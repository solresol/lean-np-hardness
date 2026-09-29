import LeanNPHardness.BinaryNatLists
import LeanNPHardness.MachineRun

/-!
# Ordered Boolean copying with source restoration

This finite three-stack TM2 kernel reverses a separately supplied source word
onto empty scratch, then pushes each scratch bit onto both source and target.
It restores the source exactly, prepends an ordered copy to the target suffix,
and empties scratch in exactly `2 * source.length + 2` steps. Both exhaustion
transitions are counted; execution ends at a live `done` continuation before
its halt. Finite control is reset there.

The certificate interface copies the complete framed natural-list encoding,
including its count header and repeated entries. The certificate must already
occupy its own source stack. Loading that stack and connecting the copy to
repeated membership queries remain separate obligations. This kernel retains
the source, so its endpoint is not mathlib's canonical `haltList` contract.
-/

namespace LeanNPHardness.MachinePrimitives.BooleanCopy

open Computability Turing

inductive Stack
  | source | scratch | target
  deriving DecidableEq, Fintype

inductive Label
  | reverse | restore | done
  deriving DecidableEq, Fintype

abbrev State := Option Bool

def Alphabet (_ : Stack) : Type := Bool

/-- Each pop, presence test, and its pushes share a single TM2 step. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .reverse =>
      .pop .source (fun _ bit => bit) <|
        .branch Option.isSome
          (.push .scratch (fun bit => bit.getD false) <|
            .goto fun _ => .reverse)
          (.goto fun _ => .restore)
  | .restore =>
      .pop .scratch (fun _ bit => bit) <|
        .branch Option.isSome
          (.push .source (fun bit => bit.getD false) <|
            .push .target (fun bit => bit.getD false) <|
              .goto fun _ => .restore)
          (.load (fun _ => none) (.goto fun _ => .done))
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .target
  Γ := Alphabet
  Λ := Label
  main := .reverse
  σ := State
  initialState := none
  Γk₀Fin := Bool.fintype
  m := program

def stackContents (source scratch target : List Bool) :
    (index : Stack) → List (Alphabet index)
  | .source => source
  | .scratch => scratch
  | .target => target

def cfg (label : Option Label) (state : State)
    (source scratch target : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := stackContents source scratch target

private theorem reverse_step_nil (state : State) (scratch target : List Bool) :
    computer.step (cfg (some .reverse) state [] scratch target) =
      some (cfg (some .restore) none [] scratch target) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]

private theorem reverse_step_cons (state : State) (bit : Bool)
    (source scratch target : List Bool) :
    computer.step (cfg (some .reverse) state (bit :: source) scratch target) =
      some (cfg (some .reverse) (some bit) source (bit :: scratch) target) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]
  funext index
  cases index <;> rfl

/-- Reverse all source bits onto scratch, preserving both supplied suffixes. -/
theorem reverse_run (source scratch target : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[source.length + 1]
      (some (cfg (some .reverse) state source scratch target)) =
      some (cfg (some .restore) none [] (source.reverse ++ scratch) target) := by
  induction source generalizing scratch state with
  | nil =>
      simpa only [List.length_nil, List.reverse_nil, List.nil_append,
        Nat.zero_add, Function.iterate_one, Option.bind_some] using
        reverse_step_nil state scratch target
  | cons bit source ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, reverse_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: scratch) (some bit)

private theorem restore_step_nil (state : State) (source target : List Bool) :
    computer.step (cfg (some .restore) state source [] target) =
      some (cfg (some .done) none source [] target) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]

private theorem restore_step_cons (state : State) (bit : Bool)
    (source scratch target : List Bool) :
    computer.step (cfg (some .restore) state source (bit :: scratch) target) =
      some (cfg (some .restore) (some bit) (bit :: source) scratch (bit :: target)) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]
  funext index
  cases index <;> rfl

/-- Restore scratch in reverse order onto both independently supplied suffixes. -/
theorem restore_run (source scratch target : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[scratch.length + 1]
      (some (cfg (some .restore) state source scratch target)) =
      some (cfg (some .done) none (scratch.reverse ++ source) []
        (scratch.reverse ++ target)) := by
  induction scratch generalizing source target state with
  | nil =>
      simpa only [List.length_nil, List.reverse_nil, List.nil_append,
        Nat.zero_add, Function.iterate_one, Option.bind_some] using
        restore_step_nil state source target
  | cons bit scratch ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, restore_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: source) (bit :: target) (some bit)

/-- Copy an arbitrary word in order, restore its source, and empty scratch. -/
theorem whole_word (bits target : List Bool) :
    (fun c => c.bind computer.step)^[2 * bits.length + 2]
      (some (cfg (some .reverse) none bits [] target)) =
      some (cfg (some .done) none bits [] (bits ++ target)) := by
  rw [show 2 * bits.length + 2 = (bits.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply, reverse_run]
  simpa only [List.append_nil, List.length_reverse, List.reverse_reverse] using
    restore_run [] bits.reverse target none

/-- Linear time in source bits, independently of the retained target suffix. -/
def evalsToInTime (bits target : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .reverse) none bits [] target)
      (some (cfg (some .done) none bits [] (bits ++ target)))
      (2 * bits.length + 2) where
  steps := 2 * bits.length + 2
  evals_in_steps := whole_word bits target
  steps_le_m := le_rfl

/-- Copy a complete certificate, retaining its header, order, and repetitions. -/
theorem certificate_run (xs : List Nat) (target : List Bool) :
    (fun c => c.bind computer.step)^[2 * (BinaryNatLists.encodeNatList xs).length + 2]
      (some (cfg (some .reverse) none (BinaryNatLists.encodeNatList xs) [] target)) =
      some (cfg (some .done) none (BinaryNatLists.encodeNatList xs) []
        (BinaryNatLists.encodeNatList xs ++ target)) :=
  whole_word (BinaryNatLists.encodeNatList xs) target

/-- The certificate-copy bound uses the full serialized certificate bit length. -/
def certificate_evalsToInTime (xs : List Nat) (target : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .reverse) none (BinaryNatLists.encodeNatList xs) [] target)
      (some (cfg (some .done) none (BinaryNatLists.encodeNatList xs) []
        (BinaryNatLists.encodeNatList xs ++ target)))
      (2 * (BinaryNatLists.encodeNatList xs).length + 2) :=
  evalsToInTime (BinaryNatLists.encodeNatList xs) target

end LeanNPHardness.MachinePrimitives.BooleanCopy
