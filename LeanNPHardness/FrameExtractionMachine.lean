import LeanNPHardness.BinaryNatLists
import LeanNPHardness.MachineRun

/-!
# Ordered extraction of one binary frame

A finite TM2 kernel reads `BinaryNatLists.frame bits ++ suffix`, counts the
unary prefix on a work stack, copies exactly the payload to scratch, and
restores its original order onto the candidate stack. It preserves the query,
unconsumed input suffix, and candidate suffix, empties both work stacks, and
resets finite control in exactly `3 * bits.length + 3` steps.

The contract concerns well-formed frames, including empty payloads. Handling
the outer framed binary list length, traversing certificates, and integrating
query-preserving equality remain separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.FrameExtraction

open Computability Turing

inductive Stack
  | input
  | query
  | candidate
  | scratch
  | count
  deriving DecidableEq, Fintype

inductive Label
  | prefix
  | payload
  | restore
  deriving DecidableEq, Fintype

abbrev State := Option Bool

def Alphabet (_ : Stack) : Type := Bool

private def observe (_ : State) (symbol : Option Bool) : State := symbol

/-- Each loop body is a finite TM2 statement. Missing delimiters or payload
bits halt early; the execution theorems below assume a complete frame. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .prefix =>
      .pop .input observe <|
        .branch Option.isSome
          (.branch (fun symbol => symbol.getD false)
            (.push .count (fun _ => true) <| .goto fun _ => .prefix)
            (.goto fun _ => .payload))
          (.load (fun _ => none) .halt)
  | .payload =>
      .pop .count observe <|
        .branch Option.isSome
          (.pop .input observe <|
            .branch Option.isSome
              (.push .scratch (fun symbol => symbol.getD false) <|
                .goto fun _ => .payload)
              (.load (fun _ => none) .halt))
          (.goto fun _ => .restore)
  | .restore =>
      .pop .scratch observe <|
        .branch Option.isSome
          (.push .candidate (fun symbol => symbol.getD false) <|
            .goto fun _ => .restore)
          (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .candidate
  Γ := Alphabet
  Λ := Label
  main := .prefix
  σ := State
  initialState := none
  Γk₀Fin := Bool.fintype
  m := program

def stackContents (input query candidate scratch count : List Bool) :
    (index : Stack) → List (Alphabet index)
  | .input => input
  | .query => query
  | .candidate => candidate
  | .scratch => scratch
  | .count => count

def cfg (label : Option Label) (state : State)
    (input query candidate scratch count : List Bool) : computer.Cfg where
  l := label
  var := state
  stk := stackContents input query candidate scratch count

private theorem prefix_step_true (state : State)
    (input query candidate scratch count : List Bool) :
    computer.step (cfg (some .prefix) state (true :: input) query candidate scratch count) =
      some (cfg (some .prefix) (some true) input query candidate scratch (true :: count)) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, Function.update]
  funext index
  cases index <;> rfl

private theorem prefix_step_false (state : State)
    (input query candidate scratch count : List Bool) :
    computer.step (cfg (some .prefix) state (false :: input) query candidate scratch count) =
      some (cfg (some .payload) (some false) input query candidate scratch count) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, Function.update]
  funext index
  cases index <;> rfl

/-- Count the unary prefix, including its separator transition, without
touching the payload or any query/candidate/scratch suffix. -/
theorem prefix_run (n : Nat) (input query candidate scratch count : List Bool)
    (state : State) :
    (fun c => c.bind computer.step)^[n + 1]
        (some (cfg (some .prefix) state
          (List.replicate n true ++ false :: input) query candidate scratch count)) =
      some (cfg (some .payload) (some false) input query candidate scratch
        (List.replicate n true ++ count)) := by
  induction n generalizing count state with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, Nat.zero_add,
        Function.iterate_one, Option.bind_some] using
        prefix_step_false state input query candidate scratch count
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, prefix_step_true]
      simpa only [replicate_true_append_cons] using
        ih (true :: count) (some true)

private theorem payload_step_cons (state : State) (bit tick : Bool)
    (input query candidate scratch count : List Bool) :
    computer.step (cfg (some .payload) state (bit :: input)
        query candidate scratch (tick :: count)) =
      some (cfg (some .payload) (some bit) input query candidate (bit :: scratch) count) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, Function.update]
  funext index
  cases index <;> rfl

private theorem payload_step_nil (state : State)
    (input query candidate scratch : List Bool) :
    computer.step (cfg (some .payload) state input query candidate scratch []) =
      some (cfg (some .restore) none input query candidate scratch []) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, Function.update]

/-- Consume exactly the counted payload and save its reverse above scratch;
the arbitrary input suffix is retained, even if it begins with payload bits. -/
theorem payload_run (bits input query candidate scratch : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[bits.length + 1]
        (some (cfg (some .payload) state (bits ++ input) query candidate scratch
          (List.replicate bits.length true))) =
      some (cfg (some .restore) none input query candidate (bits.reverse ++ scratch) []) := by
  induction bits generalizing scratch state with
  | nil =>
      simpa only [List.length_nil, List.replicate_zero, List.nil_append,
        List.reverse_nil, Nat.zero_add, Function.iterate_one, Option.bind_some] using
        payload_step_nil state input query candidate scratch
  | cons bit bits ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, payload_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: scratch) (some bit)

private theorem restore_step_cons (state : State) (bit : Bool)
    (input query candidate scratch count : List Bool) :
    computer.step (cfg (some .restore) state input query candidate (bit :: scratch) count) =
      some (cfg (some .restore) (some bit) input query (bit :: candidate) scratch count) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, Function.update]
  funext index
  cases index <;> rfl

private theorem restore_step_nil (state : State)
    (input query candidate count : List Bool) :
    computer.step (cfg (some .restore) state input query candidate [] count) =
      some (cfg none none input query candidate [] count) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, Function.update]

/-- Reverse scratch onto the candidate, preserving both input and query. -/
theorem restore_run (input query candidate scratch count : List Bool) (state : State) :
    (fun c => c.bind computer.step)^[scratch.length + 1]
        (some (cfg (some .restore) state input query candidate scratch count)) =
      some (cfg none none input query (scratch.reverse ++ candidate) [] count) := by
  induction scratch generalizing candidate state with
  | nil =>
      simpa only [List.length_nil, List.reverse_nil, List.nil_append,
        Nat.zero_add, Function.iterate_one, Option.bind_some] using
        restore_step_nil state input query candidate count
  | cons bit scratch ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, restore_step_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: candidate) (some bit)

/-- Extract one complete frame in original bit order, including the empty
frame, with exact runtime independent of the untouched suffixes. -/
theorem whole_frame (bits input query candidate : List Bool) :
    (fun c => c.bind computer.step)^[3 * bits.length + 3]
        (some (cfg (some .prefix) none (BinaryNatLists.frame bits ++ input)
          query candidate [] [])) =
      some (cfg none none input query (bits ++ candidate) [] []) := by
  rw [show 3 * bits.length + 3 =
      (2 * bits.length + 2) + (bits.length + 1) by omega,
    Function.iterate_add_apply]
  simp only [BinaryNatLists.frame, List.append_assoc, List.cons_append]
  rw [prefix_run]
  simp only [List.append_nil]
  rw [show 2 * bits.length + 2 = (bits.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply]
  rw [payload_run]
  simpa only [List.append_nil, List.length_reverse, List.reverse_reverse] using
    restore_run input query candidate bits.reverse [] none

/-- Linear in the consumed frame's actual bit length. -/
def evalsToInTime (bits input query candidate : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .prefix) none (BinaryNatLists.frame bits ++ input) query candidate [] [])
      (some (cfg none none input query (bits ++ candidate) [] []))
      (2 * (BinaryNatLists.frame bits).length + 1) where
  steps := 3 * bits.length + 3
  evals_in_steps := whole_frame bits input query candidate
  steps_le_m := by rw [BinaryNatLists.frame_length]; omega

/-- The natural interface loads the canonical unframed encoding expected by
the separate-stack binary equality kernels. -/
theorem natural_run (n : Nat) (input query candidate : List Bool) :
    (fun c => c.bind computer.step)^[3 * (Computability.encodeNat n).length + 3]
        (some (cfg (some .prefix) none (BinaryNatLists.encodeNat n ++ input)
          query candidate [] [])) =
      some (cfg none none input query (Computability.encodeNat n ++ candidate) [] []) :=
  whole_frame (Computability.encodeNat n) input query candidate

/-- A framed natural is extracted in time linear in its encoded bits. -/
def natural_evalsToInTime (n : Nat) (input query candidate : List Bool) :
    EvalsToInTime computer.step
      (cfg (some .prefix) none (BinaryNatLists.encodeNat n ++ input) query candidate [] [])
      (some (cfg none none input query (Computability.encodeNat n ++ candidate) [] []))
      (2 * BinaryNatLists.natWireSize n + 1) := by
  simpa only [BinaryNatLists.encodeNat, BinaryNatLists.natWireSize,
    BinaryNatLists.frame_length] using
    evalsToInTime (Computability.encodeNat n) input query candidate

end LeanNPHardness.MachinePrimitives.FrameExtraction
