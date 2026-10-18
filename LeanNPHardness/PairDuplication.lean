import LeanNPHardness.MachineRoutine
import LeanNPHardness.PairReductionComputable

/-!
# Duplicating an encoded input

A four-stack finite TM2 copies an arbitrary word to two reverse stacks, then
emits the right-tagged and left-tagged copies in canonical pair order. The
exact cost is `6n + 3` steps, including exhaustion and halting. Symbols are
carried by finite labels, so even an empty input alphabet needs no default.

Composition with the checked pair-left adapter retains the original input
alongside any polynomial-time function result. All time bounds use the full
encoded input length.
-/

namespace LeanNPHardness.MachineAdapters.PairDuplication

open Turing StateTransition Computability Routines

inductive Stack
  | input | left | right | output
  deriving DecidableEq, Fintype

inductive Label (Γ : Type)
  | scan | copy (symbol : Γ) | rightScan | rightPush (symbol : Γ)
  | leftScan | leftPush (symbol : Γ)
  deriving Fintype

def Alphabet (Γ : Type) : Stack → Type
  | .output => Sum Γ Γ
  | _ => Γ

variable {Γ : Type} [Fintype Γ]

instance (k : Stack) : Fintype (Alphabet Γ k) := by
  cases k <;> unfold Alphabet <;> infer_instance

def contents (input left right : List Γ) (output : List (Sum Γ Γ)) :
    Stacks (Alphabet Γ)
  | .input => input
  | .left => left
  | .right => right
  | .output => output

/-- Empty scans and symbol pushes each take one counted TM2 step. -/
def routine : Routine (Alphabet Γ) where
  Λ := Label Γ
  σ := Option Γ
  entry := .scan
  init := none
  program
    | .scan => .pop .input (fun _ s => s) (.goto fun s => s.elim .rightScan .copy)
    | .copy a => .push .left (fun _ => a)
        (.push .right (fun _ => a) (.goto fun _ => .scan))
    | .rightScan => .pop .right (fun _ s => s) (.goto fun s => s.elim .leftScan .rightPush)
    | .rightPush a => .push .output (fun _ => Sum.inr a) (.goto fun _ => .rightScan)
    | .leftScan => .pop .left (fun _ s => s)
        (.branch Option.isSome (.goto fun s => s.elim .leftScan .leftPush) .halt)
    | .leftPush a => .push .output (fun _ => Sum.inl a) (.goto fun _ => .leftScan)

def cfg (label : Option (Label Γ)) (state : Option Γ)
    (input left right : List Γ) (output : List (Sum Γ Γ)) :
    TM2.Cfg (Alphabet Γ) (Label Γ) (Option Γ) :=
  ⟨label, state, contents input left right output⟩

private theorem copy_nil (state : Option Γ) (left right : List Γ)
    (output : List (Sum Γ Γ)) :
    TM2.step routine.program (cfg (some .scan) state [] left right output) =
      some (cfg (some .rightScan) none [] left right output) := by
  simp [routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem copy_cons (a : Γ) (state : Option Γ) (input left right : List Γ)
    (output : List (Sum Γ Γ)) :
    (flip Option.bind (TM2.step routine.program))^[2]
      (some (cfg (some .scan) state (a :: input) left right output)) =
      some (cfg (some .scan) (some a) input (a :: left) (a :: right) output) := by
  simp [Function.iterate_succ_apply, flip, routine, cfg, TM2.step, TM2.stepAux,
    contents, Alphabet, Function.update]
  funext k; cases k <;> rfl

/-- Reverse both copies, preserving arbitrary work-stack and output suffixes. -/
theorem copy_run (input left right : List Γ) (output : List (Sum Γ Γ)) (state : Option Γ) :
    (flip Option.bind (TM2.step routine.program))^[2 * input.length + 1]
      (some (cfg (some .scan) state input left right output)) =
      some (cfg (some .rightScan) none [] (input.reverse ++ left)
        (input.reverse ++ right) output) := by
  induction input generalizing left right state with
  | nil => simpa [flip] using copy_nil state left right output
  | cons a input ih =>
      rw [show 2 * (a :: input).length + 1 = (2 * input.length + 1) + 2 by simp; omega,
        Function.iterate_add_apply, copy_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem right_nil (state : Option Γ) (input left : List Γ)
    (output : List (Sum Γ Γ)) :
    TM2.step routine.program (cfg (some .rightScan) state input left [] output) =
      some (cfg (some .leftScan) none input left [] output) := by
  simp [routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem right_cons (a : Γ) (state : Option Γ) (input left right : List Γ)
    (output : List (Sum Γ Γ)) :
    (flip Option.bind (TM2.step routine.program))^[2]
      (some (cfg (some .rightScan) state input left (a :: right) output)) =
      some (cfg (some .rightScan) (some a) input left right (Sum.inr a :: output)) := by
  simp [Function.iterate_succ_apply, flip, routine, cfg, TM2.step, TM2.stepAux,
    contents, Alphabet, Function.update]
  funext k; cases k <;> rfl

/-- Emit the right-tagged copy in original order. -/
theorem right_run (input left right : List Γ) (output : List (Sum Γ Γ)) (state : Option Γ) :
    (flip Option.bind (TM2.step routine.program))^[2 * right.length + 1]
      (some (cfg (some .rightScan) state input left right output)) =
      some (cfg (some .leftScan) none input left [] (right.reverse.map Sum.inr ++ output)) := by
  induction right generalizing output state with
  | nil => simpa [flip] using right_nil state input left output
  | cons a right ih =>
      rw [show 2 * (a :: right).length + 1 = (2 * right.length + 1) + 2 by simp; omega,
        Function.iterate_add_apply, right_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem left_nil (state : Option Γ) (input right : List Γ)
    (output : List (Sum Γ Γ)) :
    TM2.step routine.program (cfg (some .leftScan) state input [] right output) =
      some (cfg none none input [] right output) := by
  simp [routine, cfg, TM2.step, TM2.stepAux, contents, Alphabet]

private theorem left_cons (a : Γ) (state : Option Γ) (input left right : List Γ)
    (output : List (Sum Γ Γ)) :
    (flip Option.bind (TM2.step routine.program))^[2]
      (some (cfg (some .leftScan) state input (a :: left) right output)) =
      some (cfg (some .leftScan) (some a) input left right (Sum.inl a :: output)) := by
  simp [Function.iterate_succ_apply, flip, routine, cfg, TM2.step, TM2.stepAux,
    contents, Alphabet, Function.update]
  funext k; cases k <;> rfl

/-- Prepend the left-tagged copy in original order and exit. -/
theorem left_run (input left right : List Γ) (output : List (Sum Γ Γ)) (state : Option Γ) :
    (flip Option.bind (TM2.step routine.program))^[2 * left.length + 1]
      (some (cfg (some .leftScan) state input left right output)) =
      some (cfg none none input [] right (left.reverse.map Sum.inl ++ output)) := by
  induction left generalizing output state with
  | nil => simpa [flip] using left_nil state input right output
  | cons a left ih =>
      rw [show 2 * (a :: left).length + 1 = (2 * left.length + 1) + 2 by simp; omega,
        Function.iterate_add_apply, left_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Exact complete run, retaining any supplied output suffix. -/
theorem routine_exits (input : List Γ) (output : List (Sum Γ Γ)) :
    routine.Exits (contents input [] [] output) (6 * input.length + 3)
      (contents [] [] [] (input.map Sum.inl ++ input.map Sum.inr ++ output)) := by
  refine ⟨none, ?_⟩
  change (flip Option.bind (TM2.step routine.program))^[6 * input.length + 3]
    (some (cfg (some .scan) none input [] [] output)) = _
  rw [show 6 * input.length + 3 =
      ((2 * input.length + 1) + (2 * input.length + 1)) + (2 * input.length + 1) by omega,
    Function.iterate_add_apply, copy_run, Function.iterate_add_apply]
  simp only [List.append_nil]
  have hr := right_run [] input.reverse input.reverse output none
  simp only [List.length_reverse, List.reverse_reverse] at hr
  rw [hr]
  simpa only [List.length_reverse, List.reverse_reverse, List.append_assoc, cfg] using
    left_run [] input.reverse [] (input.map Sum.inr ++ output) none

def computer (Γ : Type) [Fintype Γ] : FinTM2 := toMachine (routine (Γ := Γ)) .input .output

/-- Canonical machine output, including workspace cleanup, reset, and halt. -/
def outputsInTime (input : List Γ) :
    TM2OutputsInTime (computer Γ) input
      (some (input.map Sum.inl ++ input.map Sum.inr)) (6 * input.length + 3) := by
  apply toMachine_outputsInTime routine Stack.input Stack.output
  have hi : (initList (computer Γ) input).stk = contents input [] [] [] := by
    funext k; cases k <;> rfl
  have ho : (haltList (computer Γ) (input.map Sum.inl ++ input.map Sum.inr)).stk =
      contents [] [] [] (input.map Sum.inl ++ input.map Sum.inr) := by
    funext k; cases k <;> rfl
  change routine.Exits (initList (computer Γ) input).stk _
    (haltList (computer Γ) (input.map Sum.inl ++ input.map Sum.inr)).stk
  rw [hi, ho]
  simpa only [List.append_nil] using routine_exits input []

/-- Duplication is linear for every finite encoding, including empty alphabets. -/
noncomputable def computableInPolyTime {α : Type} (encoding : FinEncoding α) :
    TM2ComputableInPolyTime encoding (PairEncoding.finEncoding encoding encoding)
      (fun a => (a, a)) where
  tm := computer encoding.Γ
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 3
  outputsFun a := by
    simpa [PairEncoding.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      outputsInTime (encoding.encode a)

/-- Preserve the complete original input alongside a polynomial-time result. -/
noncomputable def retainInputComputableInPolyTime {α β : Type}
    (source : FinEncoding α) (target : FinEncoding β) (f : α → β)
    (machine : TM2ComputableInPolyTime source target f) :
    TM2ComputableInPolyTime source (PairEncoding.finEncoding target source)
      (fun a => (f a, a)) := by
  exact MachineComposition.compositionComputableInPolyTime source
    (PairEncoding.finEncoding source source) (PairEncoding.finEncoding target source)
    (fun a => (a, a)) (fun pair => (f pair.1, pair.2))
    (computableInPolyTime source)
    (pairReductionComputableInPolyTime source target source f machine)

end LeanNPHardness.MachineAdapters.PairDuplication
