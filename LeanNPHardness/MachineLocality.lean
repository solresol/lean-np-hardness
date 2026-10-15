import LeanNPHardness.MachineRuntimeBounds

/-!
# Locality of one TM2 step

One `TM2.stepAux` call accesses each stack at most `depth` times along any
execution path, so the stack contents below that prefix are carried along
unchanged (`stepAux_append`). Every symbol pushed by a statement comes from
the finite list `pushable`, so the symbols that can ever appear on a stack of
a bundled machine form the explicit finite list `symbols`. These are the
finiteness and locality facts behind the Cook--Levin tableau; no runtime
claim is made here.
-/

namespace LeanNPHardness.MachineLocality

open Turing StateTransition

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- The largest number of stack accesses along one execution path. -/
def depth : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => depth q + 1
  | .peek _ _ q => depth q + 1
  | .pop _ _ q => depth q + 1
  | .load _ q => depth q
  | .branch _ q₁ q₂ => max (depth q₁) (depth q₂)
  | .goto _ => 0
  | .halt => 0

theorem stmtPushBound_le_depth (q : TM2.Stmt Γ Λ σ) :
    MachineRuntime.stmtPushBound q ≤ depth q := by
  induction q with
  | push k f q ih => simp only [MachineRuntime.stmtPushBound, depth]; omega
  | peek k f q ih => simp only [MachineRuntime.stmtPushBound, depth]; omega
  | pop k f q ih => simp only [MachineRuntime.stmtPushBound, depth]; omega
  | load f q ih => simpa [MachineRuntime.stmtPushBound, depth] using ih
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [MachineRuntime.stmtPushBound, depth]
      omega
  | goto f => simp [MachineRuntime.stmtPushBound, depth]
  | halt => simp [MachineRuntime.stmtPushBound, depth]

section Append

variable [DecidableEq K]

theorem update_append (P R : ∀ k, List (Γ k)) (k : K) (L : List (Γ k)) :
    Function.update (fun k => P k ++ R k) k (L ++ R k) =
      fun k' => Function.update P k L k' ++ R k' := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [DecidableEq K] in
/-- The depth hypothesis is inherited by statements of smaller depth. -/
private theorem hyp_mono {q q' : TM2.Stmt Γ Λ σ} (hq : depth q' ≤ depth q)
    (P R : ∀ k, List (Γ k)) (h : ∀ k, depth q ≤ (P k).length ∨ R k = []) :
    ∀ k, depth q' ≤ (P k).length ∨ R k = [] :=
  fun k => (h k).imp_left (le_trans hq)

/-- Stack contents below the depth-bounded prefix are inert during one
statement: the statement acts on the prefixes and the suffixes are
re-attached unchanged. -/
theorem stepAux_append (q : TM2.Stmt Γ Λ σ) (v : σ) (P R : ∀ k, List (Γ k))
    (h : ∀ k, depth q ≤ (P k).length ∨ R k = []) :
    TM2.stepAux q v (fun k => P k ++ R k) =
      ⟨(TM2.stepAux q v P).l, (TM2.stepAux q v P).var,
        fun k => (TM2.stepAux q v P).stk k ++ R k⟩ := by
  induction q generalizing v P with
  | push k f q ih =>
      simp only [TM2.stepAux]
      have hupd : Function.update (fun k' => P k' ++ R k') k (f v :: (P k ++ R k)) =
          fun k' => Function.update P k (f v :: P k) k' ++ R k' := by
        rw [← List.cons_append]
        exact update_append P R k (f v :: P k)
      rw [hupd]
      apply ih
      intro k'
      by_cases hk : k' = k
      · subst hk
        rcases h k' with h' | h'
        · left; simp only [Function.update_self, List.length_cons, depth] at h' ⊢; omega
        · right; exact h'
      · rw [Function.update_of_ne hk]
        rcases h k' with h' | h'
        · left; simp only [depth] at h'; omega
        · right; exact h'
  | peek k f q ih =>
      simp only [TM2.stepAux]
      have hhead : (P k ++ R k).head? = (P k).head? := by
        rcases h k with h' | h'
        · simp only [depth] at h'
          cases hP : P k with
          | nil => simp [hP] at h'
          | cons x xs => simp
        · simp [h']
      rw [hhead]
      exact ih _ _ (hyp_mono (by simp [depth]) P R h)
  | pop k f q ih =>
      simp only [TM2.stepAux]
      have hhead : (P k ++ R k).head? = (P k).head? := by
        rcases h k with h' | h'
        · simp only [depth] at h'
          cases hP : P k with
          | nil => simp [hP] at h'
          | cons x xs => simp
        · simp [h']
      have htail : (P k ++ R k).tail = (P k).tail ++ R k := by
        rcases h k with h' | h'
        · simp only [depth] at h'
          cases hP : P k with
          | nil => simp [hP] at h'
          | cons x xs => simp
        · simp [h']
      rw [hhead, htail, update_append P R k (P k).tail]
      apply ih
      intro k'
      by_cases hk : k' = k
      · subst hk
        rcases h k' with h' | h'
        · left; simp only [Function.update_self, List.length_tail, depth] at h' ⊢; omega
        · right; exact h'
      · rw [Function.update_of_ne hk]
        rcases h k' with h' | h'
        · left; simp only [depth] at h'; omega
        · right; exact h'
  | load f q ih =>
      simp only [TM2.stepAux]
      exact ih _ _ (hyp_mono (by simp [depth]) P R h)
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux]
      cases f v
      · simp only [cond_false]
        exact ih₂ _ _ (hyp_mono (by simp [depth]) P R h)
      · simp only [cond_true]
        exact ih₁ _ _ (hyp_mono (by simp [depth]) P R h)
  | goto f => rfl
  | halt => rfl

end Append

section Symbols

variable [DecidableEq K] [Fintype σ]

/-- Every symbol a statement can push onto stack `k`, over all states. -/
noncomputable def pushable (k : K) : TM2.Stmt Γ Λ σ → List (Γ k)
  | .push k' f q =>
      (if h : k' = k then (Finset.univ.toList.map fun v => h ▸ f v) else []) ++ pushable k q
  | .peek _ _ q => pushable k q
  | .pop _ _ q => pushable k q
  | .load _ q => pushable k q
  | .branch _ q₁ q₂ => pushable k q₁ ++ pushable k q₂
  | .goto _ => []
  | .halt => []

/-- Every symbol on a stack after one statement was there before or is
pushable by the statement. -/
theorem stepAux_stk_mem (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (k : K) (s : Γ k) (hs : s ∈ (TM2.stepAux q v S).stk k) :
    s ∈ S k ∨ s ∈ pushable k q := by
  induction q generalizing v S with
  | push k' f q ih =>
      simp only [TM2.stepAux] at hs
      rcases ih _ _ hs with h | h
      · by_cases hk : k' = k
        · subst hk
          simp only [Function.update_self, List.mem_cons] at h
          rcases h with rfl | h
          · right
            simp only [pushable, dif_pos, List.mem_append, List.mem_map]
            exact Or.inl ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), rfl⟩
          · left; exact h
        · rw [Function.update_of_ne (fun e => hk e.symm)] at h
          left; exact h
      · right
        simp [pushable, h]
  | peek k' f q ih =>
      simp only [TM2.stepAux] at hs
      exact ih _ _ hs
  | pop k' f q ih =>
      simp only [TM2.stepAux] at hs
      rcases ih _ _ hs with h | h
      · by_cases hk : k' = k
        · subst hk
          simp only [Function.update_self] at h
          left; exact List.mem_of_mem_tail h
        · rw [Function.update_of_ne (fun e => hk e.symm)] at h
          left; exact h
      · right; exact h
  | load f q ih =>
      simp only [TM2.stepAux] at hs
      exact ih _ _ hs
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux] at hs
      cases hfv : f v
      · simp only [hfv, cond_false] at hs
        rcases ih₂ _ _ hs with h | h
        · left; exact h
        · right; simp [pushable, h]
      · simp only [hfv, cond_true] at hs
        rcases ih₁ _ _ hs with h | h
        · left; exact h
        · right; simp [pushable, h]
  | goto f => left; simpa using hs
  | halt => left; simpa using hs

end Symbols

section Machine

variable (tm : FinTM2)

/-- The depth bound over all statements of a bundled machine. -/
def machineDepth : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup fun label => depth (tm.m label)

theorem depth_le_machineDepth (label : tm.Λ) :
    depth (tm.m label) ≤ machineDepth tm := by
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun current => depth (tm.m current)) (Finset.mem_univ label)

theorem machinePushBound_le_machineDepth :
    MachineRuntime.machinePushBound tm ≤ machineDepth tm := by
  letI := tm.ΛFin
  apply Finset.sup_le
  intro label _
  exact (stmtPushBound_le_depth _).trans (depth_le_machineDepth tm label)

/-- All labels of a bundled machine as a list. -/
noncomputable def labels : List tm.Λ :=
  letI := tm.ΛFin
  Finset.univ.toList

theorem mem_labels (label : tm.Λ) : label ∈ labels tm := by
  letI := tm.ΛFin
  exact Finset.mem_toList.mpr (Finset.mem_univ label)

/-- All internal states of a bundled machine as a list. -/
noncomputable def states : List tm.σ :=
  letI := tm.σFin
  Finset.univ.toList

theorem mem_states (state : tm.σ) : state ∈ states tm := by
  letI := tm.σFin
  exact Finset.mem_toList.mpr (Finset.mem_univ state)

/-- All stack indices of a bundled machine as a list. -/
noncomputable def stackList : List tm.K :=
  letI := tm.kFin
  Finset.univ.toList

theorem mem_stackList (k : tm.K) : k ∈ stackList tm := by
  letI := tm.kFin
  exact Finset.mem_toList.mpr (Finset.mem_univ k)

theorem stackList_nodup : (stackList tm).Nodup := by
  letI := tm.kFin
  exact Finset.nodup_toList _

/-- The whole input alphabet, available on the input stack only. -/
noncomputable def inputSymbols (k : tm.K) : List (tm.Γ k) :=
  if h : k = tm.k₀ then
    h ▸ (letI := tm.Γk₀Fin; (Finset.univ : Finset (tm.Γ tm.k₀)).toList)
  else []

theorem mem_inputSymbols (s : tm.Γ tm.k₀) : s ∈ inputSymbols tm tm.k₀ := by
  letI := tm.Γk₀Fin
  simp [inputSymbols]

/-- Extra symbols placed on the output stack only. -/
def outputSymbols (extra : List (tm.Γ tm.k₁)) (k : tm.K) : List (tm.Γ k) :=
  if h : k = tm.k₁ then h ▸ extra else []

theorem mem_outputSymbols (extra : List (tm.Γ tm.k₁)) (s : tm.Γ tm.k₁) (hs : s ∈ extra) :
    s ∈ outputSymbols tm extra tm.k₁ := by
  simp [outputSymbols, hs]

/-- Every symbol that can appear on stack `k`: pushable symbols of the
program, the input alphabet on the input stack, and the chosen extra output
symbols on the output stack. -/
noncomputable def symbols (extra : List (tm.Γ tm.k₁)) (k : tm.K) : List (tm.Γ k) :=
  letI := tm.σFin
  ((labels tm).flatMap fun label => pushable k (tm.m label)) ++
    inputSymbols tm k ++ outputSymbols tm extra k

theorem mem_symbols_of_pushable (extra : List (tm.Γ tm.k₁)) (label : tm.Λ) (k : tm.K)
    (s : tm.Γ k) (hs : letI := tm.σFin; s ∈ pushable k (tm.m label)) :
    s ∈ symbols tm extra k := by
  simp only [symbols, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl ⟨label, mem_labels tm label, hs⟩)

theorem mem_symbols_of_input (extra : List (tm.Γ tm.k₁)) (s : tm.Γ tm.k₀) :
    s ∈ symbols tm extra tm.k₀ := by
  simp only [symbols, List.mem_append]
  exact Or.inl (Or.inr (mem_inputSymbols tm s))

theorem mem_symbols_of_output (extra : List (tm.Γ tm.k₁)) (s : tm.Γ tm.k₁) (hs : s ∈ extra) :
    s ∈ symbols tm extra tm.k₁ := by
  simp only [symbols, List.mem_append]
  exact Or.inr (mem_outputSymbols tm extra s hs)

/-- A live machine step keeps every stack within the finite symbol lists. -/
theorem step_stk_mem (extra : List (tm.Γ tm.k₁)) (cfg next : tm.Cfg)
    (hstep : tm.step cfg = some next)
    (hcfg : ∀ k, ∀ s ∈ cfg.stk k, s ∈ symbols tm extra k) :
    ∀ k, ∀ s ∈ next.stk k, s ∈ symbols tm extra k := by
  letI := tm.σFin
  cases cfg with
  | mk label state contents =>
      cases label with
      | none => simp [FinTM2.step, TM2.step] at hstep
      | some label =>
          simp only [FinTM2.step, TM2.step, Option.some.injEq] at hstep
          subst hstep
          intro k s hs
          rcases stepAux_stk_mem (tm.m label) state contents k s hs with h | h
          · exact hcfg k s h
          · exact mem_symbols_of_pushable tm extra label k s h

end Machine

end LeanNPHardness.MachineLocality
