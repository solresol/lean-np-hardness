import LeanNPHardness.DictionaryLookup

/-!
# Tagged input for dictionary lookup

Convert the tagged pair of a framed natural and a framed natural list into
the serialized lookup encoding. A five-stack finite TM2 separates the tags,
restores the dictionary, and wraps the query in a framed singleton list.
The exact cost is `3q + 2d + 8`, where `q` and `d` are the complete component
bit lengths. Cleanup and halting are included. The polynomial bound uses the
original tagged input length, and no extra copy or preloaded stack is assumed.
-/

namespace LeanNPHardness.MachineAdapters.DictionaryLookupEncoding

open Computability Turing StateTransition Routines

inductive Stack
  | input | query | dictionary | count | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | dictionary | query | header | count
  deriving Fintype

def Alphabet : Stack → Type
  | .input => Sum Bool Bool
  | _ => Bool

instance (k : Stack) : Fintype (Alphabet k) := by
  cases k <;> unfold Alphabet <;> infer_instance

abbrev State := Option (Sum Bool Bool)

private def held : State → Bool
  | some (.inl b) | some (.inr b) => b
  | none => false

private def isLeft : State → Bool
  | some (.inl _) => true
  | _ => false

def contents (input : List (Sum Bool Bool)) (query dictionary count output : List Bool) :
    Stacks Alphabet
  | .input => input
  | .query => query
  | .dictionary => dictionary
  | .count => count
  | .output => output

/-- Each loop iteration is one TM2 step. The fixed header is also one step. -/
def routine : Routine Alphabet where
  Λ := Label
  σ := State
  entry := .scan
  init := none
  program
    | .scan => .pop .input (fun _ s => s) <|
        .branch Option.isSome
          (.branch isLeft
            (.push .query held (.goto fun _ => .scan))
            (.push .dictionary held (.goto fun _ => .scan)))
          (.goto fun _ => .dictionary)
    | .dictionary => .pop .dictionary (fun _ s => s.map Sum.inl) <|
        .branch Option.isSome
          (.push .output held (.goto fun _ => .dictionary))
          (.goto fun _ => .query)
    | .query => .pop .query (fun _ s => s.map Sum.inl) <|
        .branch Option.isSome
          (.push .output held (.push .count (fun _ => true) (.goto fun _ => .query)))
          (.goto fun _ => .header)
    | .header =>
        .push .output (fun _ => true) <| .push .output (fun _ => false) <|
        .push .output (fun _ => true) <| .push .output (fun _ => false) <|
        .push .count (fun _ => true) <| .push .count (fun _ => true) <|
        .push .count (fun _ => true) (.goto fun _ => .count)
    | .count => .pop .count (fun _ s => s.map Sum.inl) <|
        .branch Option.isSome
          (.push .output (fun _ => true) (.goto fun _ => .count)) .halt

def cfg (label : Option Label) (state : State) (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) : TM2.Cfg Alphabet Label State :=
  ⟨label, state, contents input query dictionary count output⟩

private abbrev step := flip Option.bind (TM2.step routine.program)

private theorem scan_nil (state : State) (query dictionary count output : List Bool) :
    step (some (cfg (some .scan) state [] query dictionary count output)) =
      some (cfg (some .dictionary) none [] query dictionary count output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem scan_cons (a : Sum Bool Bool) (state : State)
    (input : List (Sum Bool Bool)) (query dictionary count output : List Bool) :
    step (some (cfg (some .scan) state (a :: input) query dictionary count output)) =
      some (cfg (some .scan) (some a) input
        (PairEncoding.leftSymbols [a] ++ query)
        (PairEncoding.rightSymbols [a] ++ dictionary) count output) := by
  cases a <;>
    simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet,
      held, isLeft, PairEncoding.leftSymbols, PairEncoding.rightSymbols, Function.update]
    <;> funext k <;> cases k <;> rfl

/-- Separate arbitrary tagged input, retaining every occurrence in each projection. -/
theorem scan_run (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) (state : State) :
    step^[input.length + 1] (some (cfg (some .scan) state input query dictionary count output)) =
      some (cfg (some .dictionary) none []
        ((PairEncoding.leftSymbols input).reverse ++ query)
        ((PairEncoding.rightSymbols input).reverse ++ dictionary) count output) := by
  induction input generalizing query dictionary state with
  | nil => simpa [PairEncoding.leftSymbols, PairEncoding.rightSymbols] using
      scan_nil state query dictionary count output
  | cons a input ih =>
      rw [List.length_cons, Function.iterate_succ_apply, scan_cons, ih]
      cases a <;> simp [PairEncoding.leftSymbols, PairEncoding.rightSymbols,
        List.reverse_cons, List.append_assoc]

private theorem dictionary_nil (state : State) (input : List (Sum Bool Bool))
    (query count output : List Bool) :
    step (some (cfg (some .dictionary) state input query [] count output)) =
      some (cfg (some .query) none input query [] count output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem dictionary_cons (a : Bool) (state : State) (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) :
    step (some (cfg (some .dictionary) state input query (a :: dictionary) count output)) =
      some (cfg (some .dictionary) (some (.inl a)) input query dictionary count
        (a :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet, held,
    Function.update]
  funext k; cases k <;> rfl

/-- Restore the dictionary in original order onto the output suffix. -/
theorem dictionary_run (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) (state : State) :
    step^[dictionary.length + 1]
      (some (cfg (some .dictionary) state input query dictionary count output)) =
      some (cfg (some .query) none input query [] count (dictionary.reverse ++ output)) := by
  induction dictionary generalizing output state with
  | nil => simpa using dictionary_nil state input query count output
  | cons a dictionary ih =>
      rw [List.length_cons, Function.iterate_succ_apply, dictionary_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem query_nil (state : State) (input : List (Sum Bool Bool))
    (dictionary count output : List Bool) :
    step (some (cfg (some .query) state input [] dictionary count output)) =
      some (cfg (some .header) none input [] dictionary count output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem query_cons (a : Bool) (state : State) (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) :
    step (some (cfg (some .query) state input (a :: query) dictionary count output)) =
      some (cfg (some .query) (some (.inl a)) input query dictionary
        (true :: count) (a :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet, held,
    Function.update]
  funext k; cases k <;> rfl

/-- Restore the query while counting its complete framed bit length. -/
theorem query_run (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) (state : State) :
    step^[query.length + 1]
      (some (cfg (some .query) state input query dictionary count output)) =
      some (cfg (some .header) none input [] dictionary
        (List.replicate query.length true ++ count) (query.reverse ++ output)) := by
  induction query generalizing count output state with
  | nil => simpa using query_nil state input dictionary count output
  | cons a query ih =>
      rw [List.length_cons, Function.iterate_succ_apply, query_cons, ih]
      simp [List.reverse_cons, List.replicate_succ', List.append_assoc]

private theorem header_step (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) :
    step (some (cfg (some .header) none input query dictionary count output)) =
      some (cfg (some .count) none input query dictionary
        (true :: true :: true :: count) (false :: true :: false :: true :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet, Function.update]
  funext k; cases k <;> rfl

private theorem count_nil (state : State) (input : List (Sum Bool Bool))
    (query dictionary output : List Bool) :
    step (some (cfg (some .count) state input query dictionary [] output)) =
      some (cfg none none input query dictionary [] output) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem count_cons (a : Bool) (state : State) (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) :
    step (some (cfg (some .count) state input query dictionary (a :: count) output)) =
      some (cfg (some .count) (some (.inl a)) input query dictionary count (true :: output)) := by
  simp [step, flip, routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet, Function.update]
  funext k; cases k <;> rfl

/-- Emit the outer unary length prefix and finish with reset state. -/
theorem count_run (input : List (Sum Bool Bool))
    (query dictionary count output : List Bool) (state : State) :
    step^[count.length + 1]
      (some (cfg (some .count) state input query dictionary count output)) =
      some (cfg none none input query dictionary []
        (List.replicate count.length true ++ output)) := by
  induction count generalizing output state with
  | nil => simpa using count_nil state input query dictionary output
  | cons a count ih =>
      rw [List.length_cons, Function.iterate_succ_apply, count_cons, ih]
      simp [List.replicate_succ', List.append_assoc]

/-- Exact serialization for arbitrary component words and any output suffix. -/
theorem routine_exits (query dictionary output : List Bool) :
    routine.Exits (contents (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] output)
      (3 * query.length + 2 * dictionary.length + 8)
      (contents [] [] [] []
        (BinaryNatLists.frame ([true, false, true] ++ query) ++ dictionary ++ output)) := by
  refine ⟨none, ?_⟩
  change step^[_] (some (cfg (some .scan) none _ [] [] [] output)) = _
  have hs := scan_run (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] output none
  simp only [PairEncoding.leftSymbols_append, PairEncoding.rightSymbols_append,
    PairEncoding.leftSymbols_map_inl, PairEncoding.leftSymbols_map_inr,
    PairEncoding.rightSymbols_map_inl, PairEncoding.rightSymbols_map_inr,
    List.nil_append, List.append_nil, List.length_append, List.length_map] at hs
  rw [show 3 * query.length + 2 * dictionary.length + 8 =
      (((query.length + 4) + 1) + (query.length + 1)) +
        (dictionary.length + 1) + (query.length + dictionary.length + 1) by omega,
    Function.iterate_add_apply, hs, Function.iterate_add_apply]
  have hd := dictionary_run [] query.reverse dictionary.reverse [] output none
  simp only [List.length_reverse, List.reverse_reverse] at hd
  rw [hd, Function.iterate_add_apply]
  have hq := query_run [] query.reverse [] [] (dictionary ++ output) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hq
  rw [hq, Function.iterate_add_apply, Function.iterate_one, header_step]
  have hc := count_run [] [] [] (true :: true :: true :: List.replicate query.length true)
    (false :: true :: false :: true :: (query ++ (dictionary ++ output))) none
  simpa [BinaryNatLists.frame, List.append_assoc, cfg, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hc

def computer : FinTM2 := toMachine routine .input .output

/-- Canonical conversion, with empty workspace, reset control and halt. -/
def outputsInTime (query dictionary : List Bool) :
    TM2OutputsInTime computer (query.map Sum.inl ++ dictionary.map Sum.inr)
      (some (BinaryNatLists.frame ([true, false, true] ++ query) ++ dictionary))
      (3 * query.length + 2 * dictionary.length + 8) := by
  apply toMachine_outputsInTime routine Stack.input Stack.output
  have hi : (initList computer (query.map Sum.inl ++ dictionary.map Sum.inr)).stk =
      contents (query.map Sum.inl ++ dictionary.map Sum.inr) [] [] [] [] := by
    funext k; cases k <;> rfl
  have ho : (haltList computer
      (BinaryNatLists.frame ([true, false, true] ++ query) ++ dictionary)).stk =
      contents [] [] [] [] (BinaryNatLists.frame ([true, false, true] ++ query) ++ dictionary) := by
    funext k; cases k <;> rfl
  change routine.Exits (initList computer _).stk _ (haltList computer _).stk
  rw [hi, ho]
  simpa only [List.append_nil] using routine_exits query dictionary []

theorem encode_eq (input : Nat × List Nat) :
    FramedNatLookup.encode input =
      BinaryNatLists.frame ([true, false, true] ++ BinaryNatLists.encodeNat input.1) ++
        BinaryNatLists.encodeNatList input.2 := by
  have one : BinaryNatLists.encodeNat 1 = [true, false, true] := rfl
  simp [FramedNatLookup.encode, FramedNatListQueries.encode, BinaryNatLists.encodeNatList, one]

/-- Change only the wire format, with a linear bound in the original tagged input. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      FramedNatLookup.finEncoding id where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 8
  outputsFun input := by
    have run := outputsInTime (BinaryNatLists.encodeNat input.1)
      (BinaryNatLists.encodeNatList input.2)
    have bound : 3 * (BinaryNatLists.encodeNat input.1).length +
        2 * (BinaryNatLists.encodeNatList input.2).length + 8 ≤
        3 * ((BinaryNatLists.encodeNat input.1).length +
          (BinaryNatLists.encodeNatList input.2).length) + 8 := by omega
    have result := MachinePrimitives.evalsToInTimeMono run bound
    simpa [PairEncoding.finEncoding, FramedNat.finEncoding, FramedNatList.finEncoding,
      FramedNatLookup.finEncoding, encode_eq, Equiv.refl, TM2OutputsInTime, FinTM2.step,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using result

/-- Direct lookup from independently encoded query and dictionary components. -/
noncomputable def lookupComputableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      unaryFinEncodingNat MachinePrimitives.DictionaryLookup.lookup :=
  MachineComposition.compositionComputableInPolyTime _ _ _ id
    MachinePrimitives.DictionaryLookup.lookup computableInPolyTime
    MachinePrimitives.DictionaryLookup.computableInPolyTime

/-- Retain the original tagged pair alongside the unary result, charging all copying. -/
noncomputable def preservingLookupComputableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding)
      (PairEncoding.finEncoding unaryFinEncodingNat
        (PairEncoding.finEncoding FramedNat.finEncoding FramedNatList.finEncoding))
      (fun input => (MachinePrimitives.DictionaryLookup.lookup input, input)) :=
  PairDuplication.retainInputComputableInPolyTime _ _ _ lookupComputableInPolyTime

end LeanNPHardness.MachineAdapters.DictionaryLookupEncoding
