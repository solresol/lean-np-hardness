import LeanNPHardness.LiteralDictionaryMachine

/-!
# Emitting a dictionary-renamed literal in unary

The postprocessor consumes the tagged unary index, original packed literal and
framed dictionary returned by preserving lookup. It pushes one output mark per
index symbol. The first literal payload bit determines polarity, with positive
polarity for an empty payload. After draining the entire input, it prepends the
polarity symbol and halts. Each input symbol costs one finite TM2 step; the
last pop, polarity push and halt share one further step.
-/

namespace LeanNPHardness

open Computability Turing StateTransition

namespace CNF.Unary

/-- A single literal uses the literal portion of the unary CNF wire format. -/
def literalEncoding : FinEncoding (CNF.Literal Nat) where
  Γ := Sym
  encode := encodeLiteral
  decode symbols :=
    match decode (symbols ++ [.endClause]) with
    | some [[literal]] => some literal
    | _ => none
  decode_encode literal := by
    rw [show encodeLiteral literal ++ [.endClause] = encode [[literal]] by
      simp [encode, encodeClause], decode_encode]
  ΓFin := inferInstance

end CNF.Unary

namespace MachineAdapters.LiteralRename

open CNF.Unary

/-- The three tags distinguish index symbols, literal bits and dictionary bits. -/
abbrev Token := Sum Bool (Sum Bool Bool)

inductive Phase
  | header
  | lowBit
  | found (negative : Bool)
  deriving DecidableEq, Fintype

private def advance (phase : Phase) : Token → Phase
  | .inr (.inl bit) =>
    match phase with
    | .header => if bit then .header else .lowBit
    | .lowBit => .found bit
    | .found sign => .found sign
  | _ => phase

private def signSymbol : Phase → Sym
  | .found true => .neg
  | _ => .pos

inductive Stack
  | input | output
  deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Token
  | .output => Sym

def program (phase : Phase) : TM2.Stmt Alphabet Phase (Option Token) :=
  .pop .input (fun _ token => token) <|
    .branch Option.isSome
      (let next := TM2.Stmt.goto (fun token => advance phase (token.getD (.inl false)))
       .branch (fun token => (token.getD (.inl false)).isLeft)
         (.push .output (fun _ => .mark) next) next)
      (.push .output (fun _ => signSymbol phase) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .header
  σ := Option Token
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Token)
  m := program

private def cfg (phase : Option Phase) (state : Option Token)
    (input : List Token) (output : List Sym) : computer.Cfg where
  l := phase
  var := state
  stk
    | .input => input
    | .output => output

private theorem step_cons (phase : Phase) (state : Option Token) (token : Token)
    (rest : List Token) (output : List Sym) :
    computer.step (cfg (some phase) state (token :: rest) output) =
      some (cfg (some (advance phase token)) (some token) rest
        (if token.isLeft then .mark :: output else output)) := by
  cases token <;> simp [computer, FinTM2.step, cfg, program, Function.update] <;>
    funext k <;> cases k <;> rfl

private theorem step_nil (phase : Phase) (state : Option Token) (output : List Sym) :
    computer.step (cfg (some phase) state [] output) =
      some (cfg none none [] (signSymbol phase :: output)) := by
  simp [computer, FinTM2.step, cfg, program]
  funext k; cases k <;> rfl

/-- Exact scan from any state and output suffix. -/
private theorem scan (input : List Token) (phase : Phase) (state : Option Token)
    (output : List Sym) :
    (fun c => c.bind computer.step)^[input.length + 1]
        (some (cfg (some phase) state input output)) =
      some (cfg none none [] (signSymbol (input.foldl advance phase) ::
        (List.replicate (input.countP Sum.isLeft) .mark ++ output))) := by
  induction input generalizing phase state output with
  | nil => simpa using step_nil phase state output
  | cons token rest ih =>
    rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some,
      step_cons, ih, List.foldl_cons, List.countP_cons]
    cases token <;> simp [List.replicate_succ', List.append_assoc]

private def literalBit (b : Bool) : Token := .inr (.inl b)

private theorem fold_fixed {α : Type} (xs : List α) (tag : α → Token) (phase : Phase)
    (fixed : ∀ a, advance phase (tag a) = phase) :
    (xs.map tag).foldl advance phase = phase := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [List.map_cons, List.foldl_cons, fixed] using ih

private theorem frame_sign (bits : List Bool) :
    signSymbol (((BinaryNatLists.frame bits).map literalBit).foldl advance .header) =
      (if bits.head?.getD false then .neg else .pos) := by
  have header (n : Nat) :
      ((List.replicate n true).map literalBit).foldl advance .header = .header := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ, List.map_cons, List.foldl_cons]
      exact ih
  simp only [BinaryNatLists.frame, List.map_append, List.foldl_append, header,
    List.map_cons, List.foldl_cons]
  cases bits with
  | nil => rfl
  | cons b bs =>
    change signSymbol ((bs.map literalBit).foldl advance (.found b)) = _
    rw [fold_fixed bs literalBit (.found b) (fun _ => rfl)]
    cases b <;> rfl

/-- The retained index supplies the new variable; the retained literal supplies its sign. -/
def assemble (input : Nat × (CNF.Literal Nat × List Nat)) : CNF.Literal Nat :=
  input.2.1.rename (fun _ => input.1)

private theorem wire_result (index : Nat) (literal : CNF.Literal Nat) (dict : List Nat) :
    let wire := LiteralDictionary.outputEncoding.encode (index, literal, dict)
    signSymbol (wire.foldl advance .header) ::
      List.replicate (wire.countP Sum.isLeft) .mark = encodeLiteral (assemble (index, literal, dict)) := by
  let bits := encodeNat literal.toNat
  let dictionaryBit : Bool → Token := fun b => .inr (.inr b)
  let wire := (unaryEncodeNat index).map (Sum.inl : Bool → Token) ++
    (BinaryNatLists.frame bits).map literalBit ++ (BinaryNatLists.encodeNatList dict).map dictionaryBit
  have hw : LiteralDictionary.outputEncoding.encode (index, literal, dict) = wire := by
    simp [LiteralDictionary.outputEncoding, LiteralDictionary.inputEncoding,
      PairEncoding.finEncoding_encode, FramedLiteral.finEncoding, FramedNatList.finEncoding,
      unaryFinEncodingNat, bits, wire, literalBit, dictionaryBit, List.map_map,
      Function.comp_def, BinaryNatLists.encodeNat, List.append_assoc]
  have unaryLength : (unaryEncodeNat index).length = index := unary_decode_encode_nat index
  have hc : wire.countP Sum.isLeft = index := by
    simp [wire, literalBit, dictionaryBit, Function.comp_def, unaryLength]
  have hs : signSymbol (wire.foldl advance .header) =
      (if MachinePrimitives.LiteralEvaluation.polarity literal then .neg else .pos) := by
    simp only [wire, List.foldl_append]
    rw [fold_fixed _ Sum.inl .header (fun _ => rfl),
      fold_fixed _ dictionaryBit _ (fun _ => rfl), frame_sign,
      MachinePrimitives.PackedLiteral.head_encode_toNat]
  dsimp only
  rw [hw, hc, hs]
  cases literal <;> rfl

/-- Canonical assembly takes exactly the retained wire length plus one step. -/
def outputsInTime (input : Nat × (CNF.Literal Nat × List Nat)) :
    TM2OutputsInTime computer (LiteralDictionary.outputEncoding.encode input)
      (some (encodeLiteral (assemble input)))
      ((LiteralDictionary.outputEncoding.encode input).length + 1) where
  steps := (LiteralDictionary.outputEncoding.encode input).length + 1
  steps_le_m := le_rfl
  evals_in_steps := by
    obtain ⟨index, literal, dict⟩ := input
    let wire := LiteralDictionary.outputEncoding.encode (index, literal, dict)
    have hi : initList computer wire = cfg (some .header) none wire [] := by
      unfold initList cfg; congr; funext k; cases k <;> rfl
    have ho (out : List Sym) : haltList computer out = cfg none none [] out := by
      unfold haltList cfg; congr; funext k; cases k <;> rfl
    change (fun c => c.bind computer.step)^[wire.length + 1] (some (initList computer wire)) =
      some (haltList computer (encodeLiteral (assemble (index, literal, dict))))
    rw [hi, ho, ← wire_result index literal dict]
    simpa only [List.append_nil] using scan wire .header none []

/-- On the actual lookup result, assembly costs at most twice the original input length plus one. -/
theorem assembly_steps_le (input : CNF.Literal Nat × List Nat) :
    (outputsInTime (LiteralDictionary.retain input)).steps ≤
      2 * (LiteralDictionary.inputEncoding.encode input).length + 1 :=
  Nat.add_le_add_right (LiteralDictionary.retain_encode_length_le input) 1

noncomputable def assembleComputableInPolyTime :
    TM2ComputableInPolyTime LiteralDictionary.outputEncoding literalEncoding assemble where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun input := by
    simpa [literalEncoding, Equiv.refl, Polynomial.eval_add, Polynomial.eval_X] using
      outputsInTime input

/-- Dictionary renaming retains polarity and uses the first occurrence or absence sentinel. -/
def rename (input : CNF.Literal Nat × List Nat) : CNF.Literal Nat :=
  input.1.rename (fun v => input.2.idxOf v)

/-- Compute the entire unary literal directly from one packed literal and its dictionary. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime LiteralDictionary.inputEncoding literalEncoding rename := by
  have composed := MachineComposition.compositionComputableInPolyTime
    LiteralDictionary.inputEncoding LiteralDictionary.outputEncoding literalEncoding
    LiteralDictionary.retain assemble LiteralDictionary.preservingComputableInPolyTime
    assembleComputableInPolyTime
  exact (show assemble ∘ LiteralDictionary.retain = rename by
    funext input; exact LiteralDictionary.retained_rename input.1 input.2) ▸ composed

/-- One polarity symbol and exactly one mark per lookup position. -/
theorem encode_length (input : CNF.Literal Nat × List Nat) :
    (literalEncoding.encode (rename input)).length = LiteralDictionary.lookup input + 1 := by
  obtain ⟨literal, dict⟩ := input
  cases literal <;> simp [literalEncoding, rename, CNF.Literal.rename,
    encodeLiteral, LiteralDictionary.lookup, CNF.Literal.var]

/-- The packed literal frame already pays for the single polarity symbol. -/
theorem encode_length_le (input : CNF.Literal Nat × List Nat) :
    (literalEncoding.encode (rename input)).length ≤
      (LiteralDictionary.inputEncoding.encode input).length := by
  rw [encode_length]
  have indexBound := List.idxOf_le_length (l := input.2) (a := input.1.var)
  have countBound := BinaryNatLists.length_le_listWireSize input.2
  have framePos := BinaryNatLists.natWireSize_pos input.1.toNat
  simp only [LiteralDictionary.inputEncoding, PairEncoding.finEncoding_encode_length]
  change input.2.idxOf input.1.var + 1 ≤
    (BinaryNatLists.encodeNat input.1.toNat).length + (BinaryNatLists.encodeNatList input.2).length
  rw [BinaryNatLists.encodeNat_length, BinaryNatLists.encodeNatList_length]
  omega

/-- Run the complete rename while carrying a separately encoded caller component. -/
noncomputable def withContextComputableInPolyTime {α : Type} (context : FinEncoding α) :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding LiteralDictionary.inputEncoding context)
      (PairEncoding.finEncoding literalEncoding context)
      (fun input => (rename input.1, input.2)) :=
  pairReductionComputableInPolyTime LiteralDictionary.inputEncoding literalEncoding context
    rename computableInPolyTime

theorem rename_dense (formula : CNF.Formula Nat) (literal : CNF.Literal Nat) :
    rename (literal, formula.variableDictionary) = literal.rename formula.denseIndex := rfl

end MachineAdapters.LiteralRename

end LeanNPHardness
