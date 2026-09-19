import LeanNPHardness.BinaryArithmetic
import LeanNPHardness.CertificateCountMachine

/-!
# Ordered transfer of a certificate-count result

This finite TM2 kernel transfers `candidate` through `scratch` onto `remaining`
in original bit order. With initially empty scratch, it takes exactly `2p + 2`
steps for `p` candidate bits, including both exhaustion transitions. Arbitrary
input, query, count, output, and remaining-stack suffixes are preserved.

The predecessor-result interface bounds this transfer by `2b + 2`, where `b`
is the original count's bit length. This kernel assumes the predecessor is
already on `candidate`; connecting predecessor execution to the transfer and
the full certificate traversal remain separate obligations. Execution ends at
a live `done` continuation whose own halt is excluded.
-/

namespace LeanNPHardness.MachinePrimitives.CertificateCountTransfer

open Computability Turing

abbrev Stack := CertificateCount.Stack
abbrev Alphabet := CertificateCount.Alphabet
abbrev State := Option Bool

inductive Label
  | reverse | restore | done
  deriving DecidableEq, Fintype

/-- A pop, presence test, push, and loop jump share one TM2 step. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .reverse =>
      .pop .candidate (fun _ bit => bit) <|
        .branch Option.isSome
          (.push .scratch (fun bit => bit.getD false) <|
            .goto fun _ => .reverse)
          (.goto fun _ => .restore)
  | .restore =>
      .pop .scratch (fun _ bit => bit) <|
        .branch Option.isSome
          (.push .remaining (fun bit => bit.getD false) <|
            .goto fun _ => .restore)
          (.load (fun _ => none) (.goto fun _ => .done))
  | .done => .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .candidate
  k₁ := .remaining
  Γ := Alphabet
  Λ := Label
  main := .reverse
  σ := State
  initialState := none
  Γk₀Fin := Bool.fintype
  m := program

def cfg (label : Option Label) (state : State)
    (input query remaining candidate scratch count output : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := CertificateCount.stackContents input query remaining candidate scratch count output

private theorem reverse_step_nil (state : State)
    (input query remaining scratch count output : List Bool) :
    computer.step (cfg (some .reverse) state input query remaining [] scratch count output) =
      some (cfg (some .restore) none input query remaining [] scratch count output) := by
  simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents,
    CertificateCount.Alphabet, Function.update]

private theorem reverse_step_cons (state : State) (bit : Bool)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some .reverse) state
      input query remaining (bit :: candidate) scratch count output) =
      some (cfg (some .reverse) (some bit)
        input query remaining candidate (bit :: scratch) count output) := by
  simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents,
    CertificateCount.Alphabet, Function.update]
  funext index
  cases index <;> rfl

/-- First pass: save the reversed candidate above the supplied scratch suffix. -/
theorem reverse_run (input query remaining candidate scratch count output : List Bool)
    (state : State) :
    (fun c => c.bind computer.step)^[candidate.length + 1]
      (some (cfg (some .reverse) state input query remaining candidate scratch count output)) =
      some (cfg (some .restore) none
        input query remaining [] (candidate.reverse ++ scratch) count output) := by
  induction candidate generalizing scratch state with
  | nil =>
      simpa only [List.length_nil, List.reverse_nil, List.nil_append,
        Nat.zero_add, Function.iterate_one, Option.bind_some] using
        reverse_step_nil state input query remaining scratch count output
  | cons bit candidate ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, reverse_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: scratch) (some bit)

private theorem restore_step_nil (state : State)
    (input query remaining candidate count output : List Bool) :
    computer.step (cfg (some .restore) state input query remaining candidate [] count output) =
      some (cfg (some .done) none input query remaining candidate [] count output) := by
  simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents,
    CertificateCount.Alphabet, Function.update]

private theorem restore_step_cons (state : State) (bit : Bool)
    (input query remaining candidate scratch count output : List Bool) :
    computer.step (cfg (some .restore) state
      input query remaining candidate (bit :: scratch) count output) =
      some (cfg (some .restore) (some bit)
        input query (bit :: remaining) candidate scratch count output) := by
  simp [computer, FinTM2.step, cfg, program, CertificateCount.stackContents,
    CertificateCount.Alphabet, Function.update]
  funext index
  cases index <;> rfl

/-- Second pass: reverse scratch onto the retained remaining-count suffix. -/
theorem restore_run (input query remaining candidate scratch count output : List Bool)
    (state : State) :
    (fun c => c.bind computer.step)^[scratch.length + 1]
      (some (cfg (some .restore) state input query remaining candidate scratch count output)) =
      some (cfg (some .done) none
        input query (scratch.reverse ++ remaining) candidate [] count output) := by
  induction scratch generalizing remaining state with
  | nil =>
      simpa only [List.length_nil, List.reverse_nil, List.nil_append,
        Nat.zero_add, Function.iterate_one, Option.bind_some] using
        restore_step_nil state input query remaining candidate count output
  | cons bit scratch ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, restore_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: remaining) (some bit)

/-- Ordered transfer empties candidate and scratch, preserving all other data. -/
theorem whole_word (bits input query remaining count output : List Bool) :
    (fun c => c.bind computer.step)^[2 * bits.length + 2]
      (some (cfg (some .reverse) none input query remaining bits [] count output)) =
      some (cfg (some .done) none input query (bits ++ remaining) [] [] count output) := by
  rw [show 2 * bits.length + 2 = (bits.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply, reverse_run]
  simpa only [List.append_nil, List.length_reverse, List.reverse_reverse] using
    restore_run input query remaining [] bits.reverse count output none

/-- Exact transfer cost depends only on the moved word's bit length. -/
def evalsToInTime (bits input query remaining count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .reverse) none input query remaining bits [] count output)
      (some (cfg (some .done) none input query (bits ++ remaining) [] [] count output))
      (2 * bits.length + 2) where
  steps := 2 * bits.length + 2
  evals_in_steps := whole_word bits input query remaining count output
  steps_le_m := le_rfl

/-- Transfer an already computed predecessor, bounded by the original word size. -/
def predecessor_evalsToInTime (bits input query count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .reverse) none input query [] (binaryPredBits bits) [] count output)
      (some (cfg (some .done) none input query (binaryPredBits bits) [] [] count output))
      (2 * bits.length + 2) where
  steps := 2 * (binaryPredBits bits).length + 2
  evals_in_steps := by
    simpa only [List.append_nil] using
      whole_word (binaryPredBits bits) input query [] count output
  steps_le_m := by have := binaryPredBits_length_le bits; omega

/-- Canonical saturated predecessor, including zero and one, is restored to remaining.
This interface starts after predecessor computation, with its result on candidate. -/
def natural_predecessor_evalsToInTime (n : Nat) (input query count output : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .reverse) none input query [] (encodeNat (Nat.pred n)) [] count output)
      (some (cfg (some .done) none input query (encodeNat (Nat.pred n)) [] [] count output))
      (2 * (encodeNat n).length + 2) := by
  simpa only [binaryPredBits_encodeNat] using
    predecessor_evalsToInTime (encodeNat n) input query count output

end LeanNPHardness.MachinePrimitives.CertificateCountTransfer
