import Mathlib.Computability.TMComputable
import Mathlib.Data.Fintype.Lattice

namespace LeanNPHardness.MachineRuntime

open Computability Turing

private theorem transported_list_length {K : Type} (Γ : K → Type)
    {i j : K} (h : i = j) (values : List (Γ j)) :
    (Eq.mpr (congrArg (fun k => List (Γ k)) h) values).length =
      values.length := by
  cases h
  rfl

/-- An execution-path upper bound on the number of stack pushes performed
inside one `TM2.stepAux` call. A branch contributes the larger bound of its
two alternatives because only one alternative executes. -/
def stmtPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ next => stmtPushBound next + 1
  | .peek _ _ next => stmtPushBound next
  | .pop _ _ next => stmtPushBound next
  | .load _ next => stmtPushBound next
  | .branch _ left right => max (stmtPushBound left) (stmtPushBound right)
  | .goto _ => 0
  | .halt => 0

@[simp]
theorem stmtPushBound_push {K : Type} {Γ : K → Type} {Λ σ : Type}
    (k : K) (write : σ → Γ k) (next : TM2.Stmt Γ Λ σ) :
    stmtPushBound (.push k write next) = stmtPushBound next + 1 :=
  rfl

/-- In one counted TM2 step, each stack grows by at most the statement's
push bound. Pops can only shorten a stack, and a branch executes only one of
its two alternatives. -/
theorem stepAux_stack_length_le {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K] (stmt : TM2.Stmt Γ Λ σ) (state : σ)
    (contents : ∀ k, List (Γ k)) (target : K) :
    ((TM2.stepAux stmt state contents).stk target).length ≤
      (contents target).length + stmtPushBound stmt := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [TM2.stepAux, stmtPushBound]
      refine (ih state (Function.update contents k (write state :: contents k))).trans ?_
      by_cases h : target = k
      · subst target
        rw [Function.update_self]
        simp only [List.length_cons]
        omega
      · rw [Function.update_of_ne h]
        omega
  | peek k read next ih =>
      simpa only [TM2.stepAux, stmtPushBound] using
        ih (read state (contents k).head?) contents
  | pop k read next ih =>
      simp only [TM2.stepAux, stmtPushBound]
      refine (ih (read state (contents k).head?)
        (Function.update contents k (contents k).tail)).trans ?_
      by_cases h : target = k
      · subst target
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne h]
  | load update next ih =>
      simpa only [TM2.stepAux, stmtPushBound] using ih (update state) contents
  | branch test left right leftIH rightIH =>
      simp only [TM2.stepAux, stmtPushBound]
      by_cases h : test state
      · simp only [h, cond_true]
        exact (leftIH state contents).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
      · simp only [h, cond_false]
        exact (rightIH state contents).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | goto label => simp [stmtPushBound]
  | halt => simp [stmtPushBound]

/-- The largest push bound among the finitely many statements of a bundled
machine. This is a machine constant, independent of the input. -/
def machinePushBound (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup fun label => stmtPushBound (tm.m label)

/-- Every machine statement is bounded by the machine-wide push constant. -/
theorem stmtPushBound_le_machinePushBound (tm : FinTM2) (label : tm.Λ) :
    stmtPushBound (tm.m label) ≤ machinePushBound tm := by
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun current => stmtPushBound (tm.m current))
    (Finset.mem_univ label)

/-- A live step of a bundled machine grows any chosen stack by at most the
machine-wide push constant. -/
theorem step_stack_length_le (tm : FinTM2) (cfg next : tm.Cfg)
    (target : tm.K) (hstep : tm.step cfg = some next) :
    (next.stk target).length ≤
      (cfg.stk target).length + machinePushBound tm := by
  cases cfg with
  | mk label state contents =>
      cases label with
      | none => simp [FinTM2.step, TM2.step] at hstep
      | some label =>
          simp only [FinTM2.step, TM2.step] at hstep
          injection hstep with hnext
          subst next
          exact (stepAux_stack_length_le (tm.m label) state contents target).trans
            (Nat.add_le_add_left
              (stmtPushBound_le_machinePushBound tm label) _)

/-- Iterating an option-valued transition from `none` cannot later produce a
configuration. -/
private theorem iterate_bind_none {α : Type} (step : α → Option α)
    (steps : ℕ) :
    (flip Option.bind step)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih

/-- Along an exact finite run, any chosen stack grows at most linearly in the
number of counted machine steps, with coefficient `machinePushBound`. -/
theorem run_stack_length_le (tm : FinTM2) (steps : ℕ)
    (cfg finalCfg : tm.Cfg) (target : tm.K)
    (hrun :
      (flip Option.bind tm.step)^[steps] (some cfg) = some finalCfg) :
    (finalCfg.stk target).length ≤
      (cfg.stk target).length + steps * machinePushBound tm := by
  induction steps generalizing cfg with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
      subst finalCfg
      simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun
      change
        (flip Option.bind tm.step)^[steps] (tm.step cfg) = some finalCfg at hrun
      cases hstep : tm.step cfg with
      | none =>
          rw [hstep, iterate_bind_none] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          calc
            (finalCfg.stk target).length
                ≤ (next.stk target).length +
                    steps * machinePushBound tm := ih next hrun
            _ ≤ ((cfg.stk target).length + machinePushBound tm) +
                    steps * machinePushBound tm :=
              Nat.add_le_add_right
                (step_stack_length_le tm cfg next target hstep) _
            _ = (cfg.stk target).length +
                    (Nat.succ steps) * machinePushBound tm := by
              rw [Nat.succ_mul]
              omega

/-- The stack-growth bound expressed directly through mathlib's exact
execution-witness structure. -/
theorem evalsTo_stack_length_le (tm : FinTM2) (cfg finalCfg : tm.Cfg)
    (target : tm.K) (run : EvalsTo tm.step cfg (some finalCfg)) :
    (finalCfg.stk target).length ≤
      (cfg.stk target).length + run.steps * machinePushBound tm :=
  run_stack_length_le tm run.steps cfg finalCfg target run.evals_in_steps

/-- A time-bounded execution grows any selected stack by at most the declared
time bound multiplied by the machine-wide push constant. -/
theorem evalsToInTime_stack_length_le (tm : FinTM2) (cfg finalCfg : tm.Cfg)
    (target : tm.K) (time : ℕ)
    (run : EvalsToInTime tm.step cfg (some finalCfg) time) :
    (finalCfg.stk target).length ≤
      (cfg.stk target).length + time * machinePushBound tm := by
  exact (evalsTo_stack_length_le tm cfg finalCfg target run.toEvalsTo).trans
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right (machinePushBound tm) run.steps_le_m) _)

/-- A canonical TM2 output list has length at most the input length plus the
declared time bound times the machine's fixed per-step push bound. This also
covers machines whose input and output stacks coincide. -/
theorem outputsInTime_output_length_le (tm : FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ)
    (run : TM2OutputsInTime tm input (some output) time) :
    output.length ≤ input.length + time * machinePushBound tm := by
  have boundedRun := evalsToInTime_stack_length_le tm
    (initList tm input) (haltList tm output) tm.k₁ time (by
      simpa [TM2OutputsInTime] using run)
  have initialOutputLength :
      (((initList tm input).stk tm.k₁).length) ≤ input.length := by
    unfold initList
    by_cases h : tm.k₁ = tm.k₀
    · simpa only [h, dif_pos] using
        Nat.le_of_eq (transported_list_length tm.Γ h input)
    · simp [h]
  have relaxedBound :
      ((initList tm input).stk tm.k₁).length +
          time * machinePushBound tm ≤
        input.length + time * machinePushBound tm :=
    Nat.add_le_add_right initialOutputLength _
  simpa [haltList] using boundedRun.trans relaxedBound

/-- Polynomial-time computation in mathlib's TM2 model entails an explicit
encoded-result-size bound. The multiplier is a constant determined solely by
the finite machine program. -/
theorem computableInPolyTime_output_length_le {α β : Type}
    (sourceEncoding : FinEncoding α) (targetEncoding : FinEncoding β)
    (f : α → β)
    (computer : TM2ComputableInPolyTime sourceEncoding targetEncoding f)
    (input : α) :
    (targetEncoding.encode (f input)).length ≤
      (sourceEncoding.encode input).length +
        computer.time.eval (sourceEncoding.encode input).length *
          machinePushBound computer.tm := by
  simpa using outputsInTime_output_length_le computer.tm
    (List.map computer.inputAlphabet.invFun (sourceEncoding.encode input))
    (List.map computer.outputAlphabet.invFun (targetEncoding.encode (f input)))
    (computer.time.eval (sourceEncoding.encode input).length)
    (computer.outputsFun input)

end LeanNPHardness.MachineRuntime
