import LeanNPHardness.MachineRoutinePrimitives

/-!
# Routine runs with step bounds

`Routine.ExitsLE r S n S'` says `r` exits from `S` to `S'` within `n`
steps. The combinators of `Routine.Exits` (sequencing, loops, dispatch) lift
to bounds, which spares exact step accounting where only a polynomial bound
is needed, and `toMachine_outputsInTime_le` packages a bounded run as a
machine output in time.
-/

namespace LeanNPHardness.Routines

open Turing

variable {K : Type} [DecidableEq K] {Γ : K → Type}

/-- `r` exits from `S` to `S'` in at most `n` steps. -/
def Routine.ExitsLE (r : Routine Γ) (S : Stacks Γ) (n : ℕ) (S' : Stacks Γ) : Prop :=
  ∃ k, k ≤ n ∧ r.Exits S k S'

theorem Routine.Exits.le {r : Routine Γ} {S S' : Stacks Γ} {n : ℕ} (h : r.Exits S n S') :
    r.ExitsLE S n S' :=
  ⟨n, le_rfl, h⟩

theorem Routine.ExitsLE.mono {r : Routine Γ} {S S' : Stacks Γ} {n m : ℕ} (h : r.ExitsLE S n S')
    (hnm : n ≤ m) : r.ExitsLE S m S' := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk.trans hnm, h⟩

theorem seq_exitsLE (r₁ r₂ : Routine Γ) {S S₁ S₂ : Stacks Γ} {n₁ n₂ : ℕ}
    (h₁ : r₁.ExitsLE S n₁ S₁) (h₂ : r₂.ExitsLE S₁ n₂ S₂) :
    (seq r₁ r₂).ExitsLE S (n₁ + n₂) S₂ := by
  obtain ⟨k₁, hk₁, h₁⟩ := h₁
  obtain ⟨k₂, hk₂, h₂⟩ := h₂
  exact ⟨k₁ + k₂, Nat.add_le_add hk₁ hk₂, seq_exits r₁ r₂ h₁ h₂⟩

theorem loopSteps_le (c : ℕ → ℕ) (b : ℕ) (m : ℕ) (hc : ∀ i < m, c i ≤ b) :
    loopSteps c m ≤ m * (b + 1) + 1 := by
  rw [loopSteps_eq_sum]
  have : ((List.range m).map fun i => c i + 1).sum ≤ ((List.range m).map fun _ => b + 1).sum := by
    apply List.sum_le_sum
    intro i hi
    have := hc i (List.mem_range.mp hi)
    omega
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul] at this
  omega

/-- A loop whose every iteration is bounded by `c` runs within `m * (c + 1) + 1` steps. -/
theorem loop_exitsLE (k : K) (body : Routine Γ) (m : ℕ) (S : ℕ → Stacks Γ) (c : ℕ)
    (hbody : ∀ i < m, body.ExitsLE (S i) c (S (i + 1)))
    (hne : ∀ i < m, S i k ≠ []) (hempty : S m k = []) :
    (loop k body).ExitsLE (S 0) (m * (c + 1) + 1) (S m) := by
  choose steps hsteps using fun i (hi : i < m) => hbody i hi
  let cost : ℕ → ℕ := fun i => if hi : i < m then steps i hi else 0
  have run := loop_exits k body m S cost (fun i hi => by
    simp only [cost, dif_pos hi]
    exact (hsteps i hi).2) hne hempty
  refine ⟨_, ?_, run⟩
  exact loopSteps_le cost c m fun i hi => by
    simp only [cost, dif_pos hi]
    exact (hsteps i hi).1

theorem dispatch_exitsLE (k : K) [Fintype (Γ k)] [DecidableEq (Γ k)] (handlers : Γ k → Routine Γ)
    (S : Stacks Γ) (s : Γ k) (rest : List (Γ k)) (hk : S k = s :: rest)
    {n : ℕ} {S' : Stacks Γ} (h : (handlers s).ExitsLE (Function.update S k rest) n S') :
    (dispatch k handlers).ExitsLE S (n + 1) S' := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m + 1, by omega, dispatch_exits k handlers S s rest hk h⟩

/-- A bounded run from the initial stacks to the halting stacks is a
machine output in time. -/
noncomputable def toMachine_outputsInTime_le [Fintype K] (r : Routine Γ) (k₀ k₁ : K)
    [Fintype (Γ k₀)] (input : List (Γ k₀)) (output : List (Γ k₁)) (n : ℕ)
    (h : r.ExitsLE (initList (toMachine r k₀ k₁) input).stk n (haltList (toMachine r k₀ k₁) output).stk) :
    TM2OutputsInTime (toMachine r k₀ k₁) input (some output) n :=
  let k := Classical.choose h
  have hk := Classical.choose_spec h
  { (toMachine_outputsInTime r k₀ k₁ input output k hk.2) with steps_le_m := hk.1 }

/-! ### Unfolding loops one iteration at a time -/

theorem loop_exits_nil (k : K) (body : Routine Γ) (S : Stacks Γ) (hk : S k = []) :
    (loop k body).Exits S 1 S := by
  have := loop_exits k body 0 (fun _ => S) (fun _ => 0) (by simp) (by simp) hk
  simpa [loopSteps] using this

theorem loop_step_indep (k : K) (body : Routine Γ) (v : Bool ⊕ body.σ) (S : Stacks Γ) :
    TM2.step (loop k body).program ⟨some none, v, S⟩ =
      TM2.step (loop k body).program ⟨some none, Sum.inl false, S⟩ := by
  simp [TM2.step, loop, TM2.stepAux]

theorem loop_exits_cons (k : K) (body : Routine Γ) {S S' S'' : Stacks Γ} {c n : ℕ}
    (hk : S k ≠ []) (hb : body.Exits S c S') (hl : (loop k body).Exits S' n S'') :
    (loop k body).Exits S (c + 1 + n) S'' := by
  obtain ⟨v₁, hrun⟩ := hb
  obtain ⟨v₂, hl⟩ := hl
  have lifted := lift_run some Sum.inr (projRight body.init) (fun _ => rfl)
    (.goto fun _ => none) body.program (loop k body).program (fun _ => rfl) c _ _ _ _ _ hrun
  have test : TM2.step (loop k body).program ⟨some none, Sum.inl false, S⟩ =
      some ⟨some (some body.entry), Sum.inr body.init, S⟩ := by
    have : (S k).head?.isSome = true := by
      cases h : S k with
      | nil => exact (hk h).elim
      | cons _ _ => simp
    simp [TM2.step, loop, TM2.stepAux, this, loopTest]
  cases n with
  | zero => simp at hl
  | succ n =>
      refine ⟨v₂, ?_⟩
      rw [show c + 1 + (n + 1) = (n + 1) + (c + 1) by omega, Function.iterate_add_apply,
        Function.iterate_succ_apply]
      change (flip Option.bind (TM2.step (loop k body).program))^[n + 1]
        ((flip Option.bind (TM2.step (loop k body).program))^[c]
          (TM2.step (loop k body).program ⟨some none, Sum.inl false, S⟩)) = _
      rw [test, lifted]
      simp only [TM2.stepAux]
      rw [Function.iterate_succ_apply] at hl ⊢
      change (flip Option.bind (TM2.step (loop k body).program))^[n]
        (TM2.step (loop k body).program ⟨some none, Sum.inr v₁, S'⟩) = _
      rw [loop_step_indep]
      exact hl

theorem loop_exitsLE_nil (k : K) (body : Routine Γ) (S : Stacks Γ) (hk : S k = []) (n : ℕ) :
    (loop k body).ExitsLE S (n + 1) S :=
  (loop_exits_nil k body S hk).le.mono (by omega)

theorem loop_exitsLE_cons (k : K) (body : Routine Γ) {S S' S'' : Stacks Γ} {c n : ℕ}
    (hk : S k ≠ []) (hb : body.ExitsLE S c S') (hl : (loop k body).ExitsLE S' n S'') :
    (loop k body).ExitsLE S (c + 1 + n) S'' := by
  obtain ⟨c', hc', hb⟩ := hb
  obtain ⟨n', hn', hl⟩ := hl
  exact ⟨c' + 1 + n', by omega, loop_exits_cons k body hk hb hl⟩

theorem pushList_exitsLE (k : K) (as : List (Γ k)) (S : Stacks Γ) (n : ℕ) :
    (pushList k as).ExitsLE S (n + 1) (Function.update S k (as ++ S k)) :=
  (pushList_exits k as S).le.mono (by omega)

theorem popOne_exitsLE (k : K) (S : Stacks Γ) (n : ℕ) :
    (popOne k).ExitsLE S (n + 1) (Function.update S k (S k).tail) :=
  (popOne_exits k S).le.mono (by omega)

theorem skip_exitsLE (S : Stacks Γ) (n : ℕ) : (skip : Routine Γ).ExitsLE S (n + 1) S :=
  (skip_exits S).le.mono (by omega)

theorem Routine.ExitsLE.congr {r : Routine Γ} {S S' T : Stacks Γ} {n : ℕ}
    (h : r.ExitsLE S n S') (e : S' = T) : r.ExitsLE S n T := e ▸ h

end LeanNPHardness.Routines
