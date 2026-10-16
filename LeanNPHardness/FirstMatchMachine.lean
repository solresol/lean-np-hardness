import LeanNPHardness.MachineRoutineBound
import LeanNPHardness.QueryMembershipComputable
import LeanNPHardness.MachineCompositionRuntime
import LeanNPHardness.CNFRenaming

/-!
# First matching dictionary position

The repeated-membership machine emits comparison bits in reverse dictionary
order. A three-stack routine restores their order and counts the initial
false bits in unary, consuming the entire stream. It takes exactly `3n + 2`
TM2 steps on `n` bits. Composition gives polynomial-time first-member lookup
under `FramedNatListQueries.finEncoding`; a singleton membership list gives
`List.idxOf`, including the dictionary-length result when absent.

This is a canonical input/output computation. Constructing the dense variable
dictionary, preserving it across lookups, and traversing CNF occurrences are
separate obligations for a complete renaming machine.
-/

namespace LeanNPHardness.MachinePrimitives.FirstMatch

open Turing StateTransition Computability Routines

inductive Stack
  | input | work | output
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Stack) := Bool
abbrev Contents := Stacks Alphabet

def contents (input work output : List Bool) : Contents
  | .input => input
  | .work => work
  | .output => output

/-- The label records whether all bits read so far were false. After the
first true bit the remaining input is consumed without changing the count. -/
def scan : Routine Alphabet where
  Λ := Bool
  σ := Option Bool
  entry := true
  init := none
  program counting :=
    .pop .work (fun _ b => b) <|
      .branch Option.isSome
        (.branch (fun b => counting && !b.getD false)
          (.push .output (fun _ => true) (.goto fun _ => true))
          (.goto fun _ => false))
        .halt

def cfg (label : Option Bool) (state : Option Bool) (input work output : List Bool) :
    TM2.Cfg Alphabet Bool (Option Bool) :=
  ⟨label, state, contents input work output⟩

theorem scan_step_cons (counting : Bool) (state : Option Bool)
    (b : Bool) (bits input output : List Bool) :
    TM2.step scan.program (cfg (some counting) state input (b :: bits) output) =
      some (cfg (some (counting && !b)) (some b) input bits
        (if counting && !b then true :: output else output)) := by
  cases counting <;> cases b <;>
    simp [scan, cfg, TM2.step, TM2.stepAux, contents, Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_step_nil (counting : Bool) (state : Option Bool)
    (input output : List Bool) :
    TM2.step scan.program (cfg (some counting) state input [] output) =
      some (cfg none none input [] output) := by
  simp [scan, cfg, TM2.step, TM2.stepAux, contents, Function.update]

/-- Exact scan cost, with arbitrary unrelated input and output suffix. -/
theorem scan_run (bits : List Bool) (counting : Bool) (state : Option Bool)
    (input output : List Bool) :
    (flip Option.bind (TM2.step scan.program))^[bits.length + 1]
      (some (cfg (some counting) state input bits output)) =
      some (cfg none none input []
        (List.replicate (if counting then bits.idxOf true else 0) true ++ output)) := by
  induction bits generalizing counting state output with
  | nil => simpa [flip] using scan_step_nil counting state input output
  | cons b bits ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
      change (flip Option.bind (TM2.step scan.program))^[bits.length + 1]
        (TM2.step scan.program (cfg (some counting) state input (b :: bits) output)) = _
      rw [scan_step_cons, ih]
      cases counting <;> cases b <;>
        simp [List.replicate_succ', List.append_assoc]

theorem scan_exits (bits input output : List Bool) :
    scan.Exits (contents input bits output) (bits.length + 1)
      (contents input [] (List.replicate (bits.idxOf true) true ++ output)) := by
  refine ⟨none, ?_⟩
  change (flip Option.bind (TM2.step scan.program))^[bits.length + 1]
    (some (cfg (some true) none input bits output)) =
    some (cfg none none input [] (List.replicate (bits.idxOf true) true ++ output))
  simpa only [Bool.true_eq, ↓reduceIte] using scan_run bits true none input output

/-- Restore comparison order before scanning. -/
def routine : Routine Alphabet := seq (moveAll .input .work id false) scan

theorem routine_exits (bits : List Bool) :
    routine.Exits (contents bits [] []) (3 * bits.length + 2)
      (contents [] [] (List.replicate (bits.reverse.idxOf true) true)) := by
  have moved := moveAll_exits (Γ := Alphabet) Stack.input Stack.work (by decide)
    id false (contents bits [] [])
  have hm : (Function.update (Function.update (contents bits [] []) Stack.input [])
      Stack.work ((((contents bits [] []) Stack.input).map id).reverse ++
        (contents bits [] []) Stack.work)) = contents [] bits.reverse [] := by
    funext k; cases k <;> simp [contents]
  rw [hm] at moved
  have h := seq_exits _ _ moved (scan_exits bits.reverse [] [])
  have hc : 2 * ((contents bits [] []) Stack.input).length + 1 +
      (bits.reverse.length + 1) = 3 * bits.length + 2 := by
    simp only [contents, List.length_reverse]; omega
  rw [hc] at h
  simpa only [routine, List.append_nil] using h

def computer : FinTM2 := toMachine routine .input .output

/-- The exact routine run includes canonical cleanup and machine halting. -/
def outputsInTime (bits : List Bool) :
    TM2OutputsInTime computer bits
      (some (List.replicate (bits.reverse.idxOf true) true)) (3 * bits.length + 2) := by
  apply toMachine_outputsInTime routine Stack.input Stack.output
  have hi : (initList computer bits).stk = contents bits [] [] := by
    funext k; cases k <;> rfl
  have ho : (haltList computer (List.replicate (bits.reverse.idxOf true) true)).stk =
      contents [] [] (List.replicate (bits.reverse.idxOf true) true) := by
    funext k; cases k <;> rfl
  change routine.Exits (initList computer bits).stk _
    (haltList computer (List.replicate (bits.reverse.idxOf true) true)).stk
  rw [hi, ho]
  exact routine_exits bits

private theorem unaryEncodeNat_eq_replicate (n : Nat) :
    unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unaryEncodeNat, List.replicate_succ, ih]

/-- The postprocessor is linear in the number of raw comparison bits. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RawBoolList.finEncoding unaryFinEncodingNat
      (fun bits => bits.reverse.idxOf true) where
  tm := computer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 2
  outputsFun bits := by
    simpa [RawBoolList.finEncoding, unaryFinEncodingNat,
      unaryEncodeNat_eq_replicate, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime bits

/-- First dictionary entry belonging to the supplied membership list;
returns the dictionary length when no entry belongs. -/
def firstMember (input : List Nat × List Nat) : Nat :=
  (input.1.map fun x => decide (x ∈ input.2)).idxOf true

theorem firstMember_le_length (input : List Nat × List Nat) :
    firstMember input ≤ input.1.length := by
  simpa only [firstMember, List.length_map] using
    (List.idxOf_le_length (l := input.1.map fun x => decide (x ∈ input.2)) (a := true))

theorem firstMember_singleton (dictionary : List Nat) (query : Nat) :
    firstMember (dictionary, [query]) = dictionary.idxOf query := by
  induction dictionary with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x = query
      · subst x; simp [firstMember]
      · simpa [firstMember, List.idxOf_cons, h] using congrArg Nat.succ ih

/-- Absence is represented by the out-of-range dictionary-length sentinel. -/
theorem firstMember_singleton_eq_length (dictionary : List Nat) (query : Nat) :
    firstMember (dictionary, [query]) = dictionary.length ↔ query ∉ dictionary := by
  rw [firstMember_singleton, List.idxOf_eq_length_iff]

/-- Polynomial-time lookup under the complete serialized pair encoding.
The generic composition theorem supplies the composed polynomial bound. -/
noncomputable def firstMemberComputableInPolyTime :
    TM2ComputableInPolyTime FramedNatListQueries.finEncoding unaryFinEncodingNat
      firstMember := by
  have h := MachineComposition.compositionComputableInPolyTime
    FramedNatListQueries.finEncoding RawBoolList.finEncoding unaryFinEncodingNat
    CanonicalQueryMembership.membershipResults (fun bits => bits.reverse.idxOf true)
    CanonicalQueryMembership.computableInPolyTime computableInPolyTime
  change TM2ComputableInPolyTime FramedNatListQueries.finEncoding unaryFinEncodingNat
    (fun input => (input.1.map fun x => decide (x ∈ input.2)).idxOf true)
  simpa only [Function.comp_def, CanonicalQueryMembership.membershipResults,
    List.reverse_reverse] using h

/-- The dictionary lookup used by dense renaming, once the dictionary and
singleton query have been supplied in the serialized input encoding. -/
theorem firstMember_denseIndex (F : CNF.Formula Nat) (query : Nat) :
    firstMember (F.variableDictionary, [query]) = F.denseIndex query :=
  firstMember_singleton _ _

end LeanNPHardness.MachinePrimitives.FirstMatch
