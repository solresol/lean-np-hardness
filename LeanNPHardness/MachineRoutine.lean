import Mathlib.Computability.TMComputable

/-!
# Structured routines over shared stacks

A routine is a program fragment over a fixed family of stacks whose `halt`
statement means "exit". Routines compose sequentially (`seq`) and iterate
while a chosen stack is nonempty (`loop`); `toMachine` packages a routine
as a bundled machine. The run relation `Exits S n S'` records the exact
number of counted steps from entry to exit and the stack contents at exit,
with the internal state at exit left unconstrained. `lift_run` is the single
simulation lemma behind all compositions: a routine run lifts to any program
that agrees with the lifted statements, with the exit statement supplied by
the context.
-/

namespace LeanNPHardness.Routines

open Turing

variable {K : Type} [DecidableEq K] {Γ : K → Type}

/-- A program fragment over shared stacks; `halt` means exit. -/
structure Routine (Γ : K → Type) where
  Λ : Type
  σ : Type
  [ΛFin : Fintype Λ]
  [σFin : Fintype σ]
  entry : Λ
  init : σ
  program : Λ → TM2.Stmt Γ Λ σ

attribute [instance] Routine.ΛFin Routine.σFin

/-- Stack contents. -/
abbrev Stacks (Γ : K → Type) := ∀ k, List (Γ k)

/-- Started at its entry in its initial state with stacks `S`, the routine
exits after exactly `n` steps with stacks `S'`. -/
def Routine.Exits (r : Routine Γ) (S : Stacks Γ) (n : ℕ) (S' : Stacks Γ) : Prop :=
  ∃ v', (flip Option.bind (TM2.step r.program))^[n]
    (some ⟨some r.entry, r.init, S⟩) = some ⟨none, v', S'⟩

/-! ### Lifting -/

section Lift

variable {Λ₁ σ₁ Λ σ : Type}

/-- Lift a statement into larger label and state types, replacing `halt` by
a context-supplied exit statement. -/
def liftStmt (lab : Λ₁ → Λ) (st : σ₁ → σ) (proj : σ → σ₁)
    (onHalt : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ₁ σ₁ → TM2.Stmt Γ Λ σ
  | .push k f q => .push k (fun v => f (proj v)) (liftStmt lab st proj onHalt q)
  | .peek k f q => .peek k (fun v s => st (f (proj v) s)) (liftStmt lab st proj onHalt q)
  | .pop k f q => .pop k (fun v s => st (f (proj v) s)) (liftStmt lab st proj onHalt q)
  | .load f q => .load (fun v => st (f (proj v))) (liftStmt lab st proj onHalt q)
  | .branch t a b =>
      .branch (fun v => t (proj v)) (liftStmt lab st proj onHalt a) (liftStmt lab st proj onHalt b)
  | .goto f => .goto (fun v => lab (f (proj v)))
  | .halt => onHalt

/-- The lifted image of a configuration: running configurations are
relabelled, halted ones execute the exit statement. -/
def embedCfg (lab : Λ₁ → Λ) (st : σ₁ → σ) (onHalt : TM2.Stmt Γ Λ σ) :
    TM2.Cfg Γ Λ₁ σ₁ → TM2.Cfg Γ Λ σ
  | ⟨some l, v, S⟩ => ⟨some (lab l), st v, S⟩
  | ⟨none, v, S⟩ => TM2.stepAux onHalt (st v) S

theorem liftStmt_stepAux (lab : Λ₁ → Λ) (st : σ₁ → σ) (proj : σ → σ₁)
    (hproj : ∀ v, proj (st v) = v) (onHalt : TM2.Stmt Γ Λ σ)
    (stmt : TM2.Stmt Γ Λ₁ σ₁) (v : σ₁) (S : Stacks Γ) :
    TM2.stepAux (liftStmt lab st proj onHalt stmt) (st v) S =
      embedCfg lab st onHalt (TM2.stepAux stmt v S) := by
  induction stmt generalizing v S with
  | push k f q ih => simp only [liftStmt, TM2.stepAux, hproj]; exact ih _ _
  | peek k f q ih => simp only [liftStmt, TM2.stepAux, hproj]; exact ih _ _
  | pop k f q ih => simp only [liftStmt, TM2.stepAux, hproj]; exact ih _ _
  | load f q ih => simp only [liftStmt, TM2.stepAux, hproj]; exact ih _ _
  | branch t a b iha ihb =>
      simp only [liftStmt, TM2.stepAux, hproj]
      cases t v
      · simp only [cond_false]; exact ihb _ _
      · simp only [cond_true]; exact iha _ _
  | goto f => simp [liftStmt, TM2.stepAux, hproj, embedCfg]
  | halt => rfl

private theorem iterate_bind_none {α : Type} (step : α → Option α) (n : ℕ) :
    (flip Option.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- A run of a program from a running configuration to its first halt lifts
to a run of any program agreeing with the lifted statements on lifted
labels; the halt becomes the context's exit statement. -/
theorem lift_run (lab : Λ₁ → Λ) (st : σ₁ → σ) (proj : σ → σ₁)
    (hproj : ∀ v, proj (st v) = v) (onHalt : TM2.Stmt Γ Λ σ)
    (prog : Λ₁ → TM2.Stmt Γ Λ₁ σ₁) (P : Λ → TM2.Stmt Γ Λ σ)
    (hP : ∀ l, P (lab l) = liftStmt lab st proj onHalt (prog l)) :
    ∀ (n : ℕ) (l : Λ₁) (v : σ₁) (S : Stacks Γ) (v' : σ₁) (S' : Stacks Γ),
      (flip Option.bind (TM2.step prog))^[n] (some ⟨some l, v, S⟩) = some ⟨none, v', S'⟩ →
      (flip Option.bind (TM2.step P))^[n] (some ⟨some (lab l), st v, S⟩) =
        some (TM2.stepAux onHalt (st v') S') := by
  intro n
  induction n with
  | zero =>
      intro l v S v' S' h
      simp at h
  | succ n ih =>
      intro l v S v' S' h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (TM2.step prog))^[n] (TM2.step prog ⟨some l, v, S⟩) = _ at h
      change (flip Option.bind (TM2.step P))^[n] (TM2.step P ⟨some (lab l), st v, S⟩) = _
      simp only [TM2.step, hP, liftStmt_stepAux lab st proj hproj] at h ⊢
      rcases hc : TM2.stepAux (prog l) v S with ⟨l₁, v₁, S₁⟩
      rw [hc] at h
      cases l₁ with
      | none =>
          cases n with
          | zero =>
              simp only [Function.iterate_zero, id_eq, Option.some.injEq, TM2.Cfg.mk.injEq,
                true_and] at h
              obtain ⟨rfl, rfl⟩ := h
              rfl
          | succ n =>
              rw [Function.iterate_succ_apply] at h
              change (flip Option.bind (TM2.step prog))^[n] (TM2.step prog ⟨none, v₁, S₁⟩) = _ at h
              simp only [TM2.step, iterate_bind_none] at h
              cases h
      | some l₁ =>
          exact ih l₁ v₁ S₁ v' S' h

end Lift

/-! ### Sequential composition -/

/-- Project a sum state onto its left component, with a default. -/
def projLeft {σ₁ σ₂ : Type} (d : σ₁) : σ₁ ⊕ σ₂ → σ₁
  | Sum.inl v => v
  | Sum.inr _ => d

/-- Project a sum state onto its right component, with a default. -/
def projRight {σ₁ σ₂ : Type} (d : σ₂) : σ₁ ⊕ σ₂ → σ₂
  | Sum.inl _ => d
  | Sum.inr v => v

@[simp] theorem projLeft_inl {σ₁ σ₂ : Type} (d : σ₁) (v : σ₁) :
    projLeft (σ₂ := σ₂) d (Sum.inl v) = v := rfl

@[simp] theorem projRight_inr {σ₁ σ₂ : Type} (d : σ₂) (v : σ₂) :
    projRight (σ₁ := σ₁) d (Sum.inr v) = v := rfl

/-- Run the first routine, then the second from its initial state. -/
def seq (r₁ r₂ : Routine Γ) : Routine Γ where
  Λ := r₁.Λ ⊕ r₂.Λ
  σ := r₁.σ ⊕ r₂.σ
  entry := Sum.inl r₁.entry
  init := Sum.inl r₁.init
  program
    | Sum.inl l =>
        liftStmt Sum.inl Sum.inl (projLeft r₁.init)
          (.load (fun _ => Sum.inr r₂.init) (.goto fun _ => Sum.inr r₂.entry)) (r₁.program l)
    | Sum.inr l => liftStmt Sum.inr Sum.inr (projRight r₂.init) .halt (r₂.program l)

/-- Steps add up under sequential composition. -/
theorem seq_exits (r₁ r₂ : Routine Γ) {S S₁ S₂ : Stacks Γ} {n₁ n₂ : ℕ}
    (h₁ : r₁.Exits S n₁ S₁) (h₂ : r₂.Exits S₁ n₂ S₂) :
    (seq r₁ r₂).Exits S (n₁ + n₂) S₂ := by
  obtain ⟨v₁, h₁⟩ := h₁
  obtain ⟨v₂, h₂⟩ := h₂
  have run₁ := lift_run Sum.inl Sum.inl (projLeft r₁.init) (fun _ => rfl)
    (.load (fun _ => Sum.inr r₂.init) (.goto fun _ => Sum.inr r₂.entry))
    r₁.program (seq r₁ r₂).program (fun _ => rfl) n₁ _ _ _ _ _ h₁
  have run₂ := lift_run Sum.inr Sum.inr (projRight r₂.init) (fun _ => rfl) .halt
    r₂.program (seq r₁ r₂).program (fun _ => rfl) n₂ _ _ _ _ _ h₂
  refine ⟨Sum.inr v₂, ?_⟩
  rw [Nat.add_comm, Function.iterate_add_apply]
  change (flip Option.bind (TM2.step (seq r₁ r₂).program))^[n₂]
    ((flip Option.bind (TM2.step (seq r₁ r₂).program))^[n₁]
      (some ⟨some (Sum.inl r₁.entry), Sum.inl r₁.init, S⟩)) = _
  rw [run₁]
  simp only [TM2.stepAux]
  exact run₂

/-! ### Loops -/

/-- The loop test state: whether the loop stack was nonempty. -/
def loopTest {σ : Type} : Bool ⊕ σ → Bool
  | Sum.inl b => b
  | Sum.inr _ => false

/-- Run the body while stack `k` is nonempty. Each test costs one step. -/
def loop (k : K) (body : Routine Γ) : Routine Γ where
  Λ := Option body.Λ
  σ := Bool ⊕ body.σ
  entry := none
  init := Sum.inl false
  program
    | none =>
        .peek k (fun _ s => Sum.inl s.isSome)
          (.branch loopTest
            (.load (fun _ => Sum.inr body.init) (.goto fun _ => some body.entry))
            .halt)
    | some l => liftStmt some Sum.inr (projRight body.init) (.goto fun _ => none) (body.program l)

/-- Total steps of `m` iterations with the given body costs, including the
`m + 1` tests. -/
def loopSteps (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => c 0 + 1 + loopSteps (fun i => c (i + 1)) m

theorem loopSteps_eq_sum (c : ℕ → ℕ) (m : ℕ) :
    loopSteps c m = ((List.range m).map fun i => c i + 1).sum + 1 := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
      rw [loopSteps, ih, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
      simp only [Function.comp_def, Nat.succ_eq_add_one]
      omega

private theorem loop_run (k : K) (body : Routine Γ) (m : ℕ) :
    ∀ (S : ℕ → Stacks Γ) (c : ℕ → ℕ),
      (∀ i < m, body.Exits (S i) (c i) (S (i + 1))) →
      (∀ i < m, S i k ≠ []) → S m k = [] → ∀ (v₀ : Bool ⊕ body.σ),
      (flip Option.bind (TM2.step (loop k body).program))^[loopSteps c m]
        (some ⟨some none, v₀, S 0⟩) = some ⟨none, Sum.inl false, S m⟩ := by
  induction m with
  | zero =>
      intro S c _ _ hempty v₀
      simp only [loopSteps, Function.iterate_one]
      change TM2.step (loop k body).program ⟨some none, v₀, S 0⟩ = _
      simp [TM2.step, loop, TM2.stepAux, hempty, loopTest]
  | succ m ih =>
      intro S c hbody hne hempty v₀
      obtain ⟨v₁, hrun⟩ := hbody 0 (by omega)
      have lifted := lift_run some Sum.inr (projRight body.init) (fun _ => rfl)
        (.goto fun _ => none) body.program (loop k body).program (fun _ => rfl)
        (c 0) _ _ _ _ _ hrun
      have test : TM2.step (loop k body).program ⟨some none, v₀, S 0⟩ =
          some ⟨some (some body.entry), Sum.inr body.init, S 0⟩ := by
        have : (S 0 k).head?.isSome = true := by
          cases h : S 0 k with
          | nil => exact (hne 0 (by omega) h).elim
          | cons _ _ => simp
        simp [TM2.step, loop, TM2.stepAux, this, loopTest]
      rw [loopSteps, show c 0 + 1 + loopSteps (fun i => c (i + 1)) m =
        loopSteps (fun i => c (i + 1)) m + (c 0 + 1) by omega, Function.iterate_add_apply,
        Function.iterate_succ_apply]
      change (flip Option.bind (TM2.step (loop k body).program))^[loopSteps (fun i => c (i + 1)) m]
        ((flip Option.bind (TM2.step (loop k body).program))^[c 0]
          (TM2.step (loop k body).program ⟨some none, v₀, S 0⟩)) = _
      rw [test, lifted]
      simp only [TM2.stepAux]
      exact ih (fun i => S (i + 1)) (fun i => c (i + 1)) (fun i hi => hbody (i + 1) (by omega))
        (fun i hi => hne (i + 1) (by omega)) hempty (Sum.inr v₁)

/-- A loop whose body runs `m` times along a given sequence of stack
contents exits with the final contents. -/
theorem loop_exits (k : K) (body : Routine Γ) (m : ℕ) (S : ℕ → Stacks Γ) (c : ℕ → ℕ)
    (hbody : ∀ i < m, body.Exits (S i) (c i) (S (i + 1)))
    (hne : ∀ i < m, S i k ≠ []) (hempty : S m k = []) :
    (loop k body).Exits (S 0) (loopSteps c m) (S m) :=
  ⟨Sum.inl false, loop_run k body m S c hbody hne hempty (Sum.inl false)⟩

/-! ### Doing nothing -/

/-- Exit immediately, in one step. -/
def skip : Routine Γ where
  Λ := Unit
  σ := Unit
  entry := ()
  init := ()
  program _ := .halt

theorem skip_exits (S : Stacks Γ) : (skip : Routine Γ).Exits S 1 S :=
  ⟨(), rfl⟩

/-! ### Dispatch on a popped symbol -/

section Dispatch

variable (k : K) [Fintype (Γ k)] [DecidableEq (Γ k)] (handlers : Γ k → Routine Γ)

/-- Project a dispatch state onto the state of the handler for `s`. -/
def dispatchProj (s : Γ k) :
    Option (Γ k) ⊕ (Σ s : Γ k, (handlers s).σ) → (handlers s).σ
  | Sum.inr ⟨s', v⟩ => if h : s' = s then h ▸ v else (handlers s).init
  | Sum.inl _ => (handlers s).init

theorem dispatchProj_inr (s : Γ k) (v : (handlers s).σ) :
    dispatchProj k handlers s (Sum.inr ⟨s, v⟩) = v := by
  simp [dispatchProj]

/-- Pop one symbol from `k` and run the handler selected by it. The pop
costs one step. An empty stack is not handled; `dispatch_exits` assumes a
symbol is present. -/
def dispatch : Routine Γ where
  Λ := Option (Σ s : Γ k, (handlers s).Λ)
  σ := Option (Γ k) ⊕ (Σ s : Γ k, (handlers s).σ)
  entry := none
  init := Sum.inl none
  program
    | none =>
        .pop k (fun _ s => Sum.inl s)
          (.load (fun v => match v with
              | Sum.inl (some s) => Sum.inr ⟨s, (handlers s).init⟩
              | v => v)
            (.goto fun v => match v with
              | Sum.inr ⟨s, _⟩ => some ⟨s, (handlers s).entry⟩
              | _ => none))
    | some ⟨s, l⟩ =>
        liftStmt (fun l' => some ⟨s, l'⟩) (fun v => Sum.inr ⟨s, v⟩) (dispatchProj k handlers s)
          .halt ((handlers s).program l)

theorem dispatch_exits (S : Stacks Γ) (s : Γ k) (rest : List (Γ k)) (hk : S k = s :: rest)
    {n : ℕ} {S' : Stacks Γ} (h : (handlers s).Exits (Function.update S k rest) n S') :
    (dispatch k handlers).Exits S (n + 1) S' := by
  obtain ⟨v', hrun⟩ := h
  have lifted := lift_run (fun l' => some ⟨s, l'⟩) (fun v => Sum.inr ⟨s, v⟩)
    (dispatchProj k handlers s) (dispatchProj_inr k handlers s) .halt (handlers s).program
    (dispatch k handlers).program (fun _ => rfl) n _ _ _ _ _ hrun
  refine ⟨Sum.inr ⟨s, v'⟩, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one]
  have first : TM2.step (dispatch k handlers).program ⟨some none, Sum.inl none, S⟩ =
      some ⟨some (some ⟨s, (handlers s).entry⟩), Sum.inr ⟨s, (handlers s).init⟩,
        Function.update S k rest⟩ := by
    simp [TM2.step, dispatch, TM2.stepAux, hk]
  change (flip Option.bind (TM2.step (dispatch k handlers).program))^[n]
    (TM2.step (dispatch k handlers).program ⟨some none, Sum.inl none, S⟩) = _
  rw [first, lifted]
  rfl

end Dispatch

/-! ### Bundled machines -/

/-- The bundled machine of a routine: exiting resets the state and halts. -/
def toMachine [Fintype K] (r : Routine Γ) (k₀ k₁ : K) [Fintype (Γ k₀)] : FinTM2 where
  K := K
  k₀ := k₀
  k₁ := k₁
  Γ := Γ
  Λ := r.Λ
  main := r.entry
  σ := r.σ
  initialState := r.init
  m l := liftStmt id id id (.load (fun _ => r.init) .halt) (r.program l)

/-- A routine run from the machine's initial stacks to the canonical halting
stacks is a time-bounded machine output. -/
def toMachine_outputsInTime [Fintype K] (r : Routine Γ) (k₀ k₁ : K) [Fintype (Γ k₀)]
    (input : List (Γ k₀)) (output : List (Γ k₁)) (n : ℕ)
    (h : r.Exits (initList (toMachine r k₀ k₁) input).stk n (haltList (toMachine r k₀ k₁) output).stk) :
    TM2OutputsInTime (toMachine r k₀ k₁) input (some output) n where
  steps := n
  evals_in_steps := by
    obtain ⟨v', hrun⟩ := h
    have lifted := lift_run id id id (fun _ => rfl) (.load (fun _ => r.init) .halt)
      r.program (toMachine r k₀ k₁).m (fun _ => rfl) n _ _ _ _ _ hrun
    simp only [Option.map_some]
    change (flip Option.bind (TM2.step (toMachine r k₀ k₁).m))^[n]
      (some (initList (toMachine r k₀ k₁) input)) = some (haltList (toMachine r k₀ k₁) output)
    have hinit : initList (toMachine r k₀ k₁) input =
        ⟨some (id r.entry), id r.init, (initList (toMachine r k₀ k₁) input).stk⟩ := rfl
    rw [hinit, lifted]
    rfl
  steps_le_m := le_rfl

end LeanNPHardness.Routines
