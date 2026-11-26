import LeanNPHardness.FormulaDictionaryMachine
import LeanNPHardness.OrderedFormulaRenameMachine
import LeanNPHardness.TaggedFramedListCons

/-!
# Dense renaming from a tagged dictionary and formula

The left component of the preparation wire is the framed dictionary. The right
component is the original binary formula. The tagged-pair loader can write both
directly onto the ordered renamer's stacks and use its frame workspace while
restoring their order.
-/

namespace LeanNPHardness.MachineAdapters.TaggedFormulaRename

open Computability Routines MachinePrimitives CNF.Unary

variable (c : LiteralRenameStep.Witness)

abbrev PairAlphabet (_ : Unit) := Bool ⊕ Bool
abbrev Stack := OrderedFormulaRename.Stack c ⊕ Unit
abbrev Alphabet := ExtendedAlphabet (Γ := OrderedFormulaRename.Alphabet c) PairAlphabet

instance stackDecidableEq : DecidableEq (Stack c) := by
  letI : DecidableEq (OrderedFormulaRename.Stack c) := inferInstance
  exact inferInstanceAs (DecidableEq (OrderedFormulaRename.Stack c ⊕ Unit))

def contents (pair : List (Bool ⊕ Bool)) (input dictionary : List Bool)
    (out : List Sym) : Stacks (Alphabet c) :=
  extendedStacks PairAlphabet (OrderedFormulaRename.contents c input dictionary [] out)
    (fun _ => pair)

private abbrev literalStack (k : LiteralRenameStep.Stack c) : Stack c :=
  .inl (.inl (.inl (.inl k)))

/-- The loader's left destination is the dictionary, and its right destination
is the frame mover's input. Its other Boolean stacks use the frame workspace. -/
private def address : TaggedFramedListCons.Stack → Stack c
  | .inr u => .inr u
  | .inl (.inr _) => literalStack c (.inr (.inr .dictionary))
  | .inl (.inl k) => literalStack c (.inr (.inl (match k with
    | .input => .input | .count => .count | .work => .work | .output => .output)))

private def wiring : StackMap TaggedFramedListCons.Alphabet (Alphabet c) where
  index := address c
  symbol k := by rcases k with (k | _) | _ <;> exact Equiv.refl _

def load : Routine (Alphabet c) := (wiring c).routine TaggedFramedListCons.load

private def place (out : List Sym) (S : Stacks TaggedFramedListCons.Alphabet) :
    Stacks (Alphabet c)
  | .inr u => S (.inr u)
  | .inl (.inr _) => out
  | .inl (.inl (.inl (.inl (.inr (.inr .dictionary))))) => S TaggedFramedListCons.queryStack
  | .inl (.inl (.inl (.inl (.inr (.inl k))))) => S (.inl (.inl (match k with
    | .input => .input | .count => .count | .work => .work | .output => .output)))
  | _ => []

private theorem place_contents (pair : List (Bool ⊕ Bool)) (dict input : List Bool)
    (out : List Sym) :
    place c out (TaggedFramedListCons.contents pair dict input [] [] []) =
      contents c pair input dict out := by
  funext j
  rcases j with ((((p | (f | e)) | u) | v) | w) | z <;>
    first | rfl | (cases f <;> rfl) | (cases e <;> rfl)

/-- Load arbitrary component words in source order, with an exact cost in
their combined bit length. Both words may be empty. -/
theorem load_exits (dict input : List Bool) (out : List Sym) :
    (load c).Exits (contents c (dict.map Sum.inl ++ input.map Sum.inr) [] [] out)
      (3 * (dict.length + input.length) + 3) (contents c [] input dict out) := by
  rw [← place_contents, ← place_contents]
  apply (wiring c).exits (place c out) _ _ _ (TaggedFramedListCons.load_exits dict input)
  · intro S k
    rcases k with (k | ⟨⟩) | ⟨⟩ <;> change _ = List.map id _ <;> rw [List.map_id]
    · cases k <;> rfl
    all_goals rfl
  · intro S k word
    rcases k with (f | ⟨⟩) | ⟨⟩ <;>
      funext j <;>
      rcases j with ((((p | (g | e)) | ⟨⟩) | ⟨⟩) | ⟨⟩) | ⟨⟩ <;>
      (try cases f) <;> (try cases g) <;> (try cases e) <;>
      first | rfl | (change word = word.map id; rw [List.map_id])

/-- Exact loading time for the actual output encoding of formula preparation. -/
theorem prepared_load_exits (formula : CNF.Formula Nat) (out : List Sym) :
    let pair := FormulaDictionary.outputEncoding.encode (FormulaDictionary.prepare formula)
    (load c).Exits (contents c pair [] [] out) (3 * pair.length + 3)
      (contents c [] formula.encode (BinaryNatLists.encodeNatList formula.variableDictionary) out) := by
  intro pair
  have size : pair.length =
      (BinaryNatLists.encodeNatList formula.variableDictionary).length + formula.encode.length :=
    PairEncoding.finEncoding_encode_length _ _ _
  rw [size]
  exact load_exits c _ _ out

noncomputable def routine : Routine (Alphabet c) :=
  seq (load c) (extend PairAlphabet (OrderedFormulaRename.routine c))

private theorem load_then_rename {pair : List (Bool ⊕ Bool)} {input dict : List Bool}
    {out result : List Sym} {loading traversal : Nat}
    (loaded : (load c).Exits (contents c pair [] [] out) loading (contents c [] input dict out))
    (renamed : (OrderedFormulaRename.routine c).ExitsLE
      (OrderedFormulaRename.contents c input dict [] out) traversal
      (OrderedFormulaRename.contents c [] dict [] result)) :
    (routine c).ExitsLE (contents c pair [] [] out) (loading + traversal)
      (contents c [] [] dict result) := by
  obtain ⟨steps, bound, run⟩ := renamed
  exact seq_exitsLE _ _ loaded.le
    ⟨steps, bound, extend_exits PairAlphabet _ (fun _ => []) run⟩

/-- An arbitrary supplied dictionary uses first-index lookup, including its
length sentinel on absence. Charge the loader in tagged input bits and the
output transfer in the number of emitted unary symbols. -/
theorem formula_exits (dict : List Nat) (formula : CNF.Formula Nat) (out : List Sym) :
    let pair := FormulaDictionary.outputEncoding.encode (dict, formula)
    let word := encode (formula.rename dict.idxOf)
    (routine c).ExitsLE (contents c pair [] [] out)
      (3 * pair.length + 3 +
        ((FramedFormulaRename.timePolynomial c).eval pair.length + (2 * word.length + 1)))
      (contents c [] [] (BinaryNatLists.encodeNatList dict) (word ++ out)) := by
  intro pair word
  have loadRun := load_exits c (BinaryNatLists.encodeNatList dict) formula.encode out
  have traversal := OrderedFormulaRename.formula_exits c formula dict [] out
  have size : pair.length = (BinaryNatLists.encodeNatList dict).length + formula.encode.length :=
    PairEncoding.finEncoding_encode_length _ _ _
  rw [size]
  apply load_then_rename c loadRun
  simpa only [List.append_nil, Nat.add_comm formula.encode.length] using traversal

/-- Starting at the preparation wire, load and rename in source order. The
retained dictionary and caller's output suffix are available on exit. -/
theorem dense_formula_exits (formula : CNF.Formula Nat) (out : List Sym) :
    let c := LiteralRename.computableInPolyTime
    let pair := FormulaDictionary.outputEncoding.encode (FormulaDictionary.prepare formula)
    (routine c).ExitsLE (contents c pair [] [] out)
      (12 * formula.encodedSize + 6 + (OrderedFormulaRename.timePolynomial c).eval formula.encodedSize)
      (contents c [] [] (BinaryNatLists.encodeNatList formula.variableDictionary)
        (encode formula.denseRename ++ out)) := by
  intro c pair
  have run := load_then_rename c (prepared_load_exits c formula out)
    (by simpa only [List.append_nil] using OrderedFormulaRename.dense_formula_exits formula [] out)
  apply run.mono
  apply Nat.add_le_add_right
  have size := FormulaDictionary.prepare_encode_length_le formula
  omega

end LeanNPHardness.MachineAdapters.TaggedFormulaRename
