import LeanNPHardness.CNFNormalization
import LeanNPHardness.CNFCertificate

/-!
# Splitting long clauses into three-literal clauses

Original variables are renamed to even numbers, leaving the odd numbers for
fresh variables. A clause `l₁ ∨ l₂ ∨ l₃ ∨ l₄ ∨ …` becomes
`(l₁ ∨ l₂ ∨ y) ∧ split (¬y ∨ l₃ ∨ l₄ ∨ …)` with a fresh `y`; clauses of width
at most three are kept. `satisfiable_split` proves that satisfiability is
preserved, and `atMostWidth_split` that every output clause has width at most
three, so `Clause.normalizeThree` then yields exact width three.
`satToExactThree` packages the semantic reduction. Output-size and runtime
claims are separate.
-/

namespace LeanNPHardness.CNF

namespace Literal

@[simp]
theorem eval_positive (a : Assignment ℕ) (v : ℕ) : (Literal.positive v).eval a = a v := rfl

@[simp]
theorem eval_negative (a : Assignment ℕ) (v : ℕ) : (Literal.negative v).eval a = !(a v) := rfl

/-- Rename variable `v` to `2 * v`, reserving odd numbers for fresh variables. -/
def double : Literal ℕ → Literal ℕ
  | .positive v => .positive (2 * v)
  | .negative v => .negative (2 * v)

@[simp]
theorem var_double (l : Literal ℕ) : l.double.var = 2 * l.var := by
  cases l <;> rfl

theorem eval_double (a : Assignment ℕ) (l : Literal ℕ) :
    l.double.eval a = l.eval fun v => a (2 * v) := by
  cases l <;> rfl

theorem eval_double_halve (a : Assignment ℕ) (l : Literal ℕ) :
    l.double.eval (fun v => a (v / 2)) = l.eval a := by
  cases l <;> simp [double, eval]

end Literal

namespace Clause

/-- Rename every variable to its double. -/
def double (clause : Clause ℕ) : Clause ℕ := clause.map Literal.double

theorem eval_double (a : Assignment ℕ) (clause : Clause ℕ) :
    clause.double.eval a = clause.eval fun v => a (2 * v) := by
  induction clause with
  | nil => rfl
  | cons l rest ih => simp [double, eval_cons, Literal.eval_double, ih] at ih ⊢

theorem eval_double_halve (a : Assignment ℕ) (clause : Clause ℕ) :
    clause.double.eval (fun v => a (v / 2)) = clause.eval a := by
  induction clause with
  | nil => rfl
  | cons l rest ih => simp [double, eval_cons, Literal.eval_double_halve, ih] at ih ⊢

theorem var_even_of_mem_double (clause : Clause ℕ) (l : Literal ℕ) (hl : l ∈ clause.double) :
    l.var % 2 = 0 := by
  obtain ⟨l', _, rfl⟩ := List.mem_map.mp hl
  simp

end Clause

namespace Formula

/-- Rename every variable to its double. -/
def double (formula : Formula ℕ) : Formula ℕ := formula.map Clause.double

theorem eval_double (a : Assignment ℕ) (formula : Formula ℕ) :
    formula.double.eval a = formula.eval fun v => a (2 * v) := by
  induction formula with
  | nil => rfl
  | cons c rest ih => simp [double, eval_cons, Clause.eval_double, ih] at ih ⊢

theorem eval_double_halve (a : Assignment ℕ) (formula : Formula ℕ) :
    formula.double.eval (fun v => a (v / 2)) = formula.eval a := by
  induction formula with
  | nil => rfl
  | cons c rest ih => simp [double, eval_cons, Clause.eval_double_halve, ih] at ih ⊢

end Formula

/-- The `f`-th fresh variable. -/
def freshVar (f : ℕ) : ℕ := 2 * f + 1

theorem freshVar_mono {f g : ℕ} (h : f ≤ g) : freshVar f ≤ freshVar g := by
  simp only [freshVar]; omega

theorem freshVar_odd (f : ℕ) : freshVar f % 2 = 1 := by
  simp only [freshVar]; omega

/-- Split one clause using fresh variables from index `fresh`; returns the
clauses and the next unused fresh index. -/
def splitClause (fresh : ℕ) : Clause ℕ → Formula ℕ × ℕ
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
      let result := splitClause (fresh + 1) (.negative (freshVar fresh) :: l₃ :: l₄ :: rest)
      ([l₁, l₂, .positive (freshVar fresh)] :: result.1, result.2)
  | [] => ([[]], fresh)
  | [l₁] => ([[l₁]], fresh)
  | [l₁, l₂] => ([[l₁, l₂]], fresh)
  | [l₁, l₂, l₃] => ([[l₁, l₂, l₃]], fresh)
termination_by clause => clause.length
decreasing_by simp_wf

theorem splitClause_fresh_le (fresh : ℕ) (clause : Clause ℕ) :
    fresh ≤ (splitClause fresh clause).2 := by
  induction fresh, clause using splitClause.induct with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih => rw [splitClause]; simp only; omega
  | case2 => simp [splitClause]
  | case3 => simp [splitClause]
  | case4 => simp [splitClause]
  | case5 => simp [splitClause]

theorem splitClause_fresh_le_length (fresh : ℕ) (clause : Clause ℕ) :
    (splitClause fresh clause).2 ≤ fresh + clause.length := by
  induction fresh, clause using splitClause.induct with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih => rw [splitClause]; simp only [List.length_cons] at ih ⊢; omega
  | case2 => simp [splitClause]
  | case3 => simp [splitClause]
  | case4 => simp [splitClause]
  | case5 => simp [splitClause]

/-- Every output clause has width at most three. -/
theorem splitClause_width (fresh : ℕ) (clause : Clause ℕ) :
    ∀ c ∈ (splitClause fresh clause).1, c.length ≤ 3 := by
  induction fresh, clause using splitClause.induct with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih =>
      rw [splitClause]
      simp only [List.mem_cons]
      rintro c (rfl | hc)
      · simp
      · exact ih c hc
  | case2 => simp [splitClause]
  | case3 => simp [splitClause]
  | case4 => simp [splitClause]
  | case5 => simp [splitClause]

theorem splitClause_length (fresh : ℕ) (clause : Clause ℕ) :
    (splitClause fresh clause).1.length ≤ clause.length + 1 := by
  induction fresh, clause using splitClause.induct with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih => rw [splitClause]; simp only [List.length_cons] at ih ⊢; omega
  | case2 => simp [splitClause]
  | case3 => simp [splitClause]
  | case4 => simp [splitClause]
  | case5 => simp [splitClause]

/-- Variables are even or below a bound: the invariant for fresh-variable
allocation. -/
def VarsBelow (bound : ℕ) (clause : Clause ℕ) : Prop :=
  ∀ l ∈ clause, l.var < bound ∨ l.var % 2 = 0

theorem VarsBelow.mono {bound bound' : ℕ} (h : bound ≤ bound') {clause : Clause ℕ}
    (hc : VarsBelow bound clause) : VarsBelow bound' clause :=
  fun l hl => (hc l hl).imp_left fun h' => lt_of_lt_of_le h' h

/-- Output variables are even or below the next fresh variable. -/
theorem splitClause_varsBelow (fresh : ℕ) (clause : Clause ℕ)
    (hc : VarsBelow (freshVar fresh) clause) :
    ∀ c ∈ (splitClause fresh clause).1, VarsBelow (freshVar (splitClause fresh clause).2) c := by
  induction fresh, clause using splitClause.induct with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih =>
      rw [splitClause]
      simp only [List.mem_cons]
      have hnext := splitClause_fresh_le (fresh + 1)
        (.negative (freshVar fresh) :: l₃ :: l₄ :: rest)
      have hmono := freshVar_mono (show fresh + 1 ≤ _ from hnext)
      have hc' : VarsBelow (freshVar (fresh + 1)) (.negative (freshVar fresh) :: l₃ :: l₄ :: rest) := by
        intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl | hl | hl
        · left; simp only [Literal.var, freshVar]; omega
        · exact (hc l (by simp [hl])).imp_left fun h => lt_of_lt_of_le h (freshVar_mono (by omega))
        · exact (hc l (by simp [hl])).imp_left fun h => lt_of_lt_of_le h (freshVar_mono (by omega))
        · exact (hc l (by simp [hl])).imp_left fun h => lt_of_lt_of_le h (freshVar_mono (by omega))
      rintro c (rfl | hcmem)
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact (hc l (by simp)).imp_left fun h => lt_of_lt_of_le h
            ((freshVar_mono (by omega : fresh ≤ fresh + 1)).trans hmono)
        · exact (hc l (by simp)).imp_left fun h => lt_of_lt_of_le h
            ((freshVar_mono (by omega : fresh ≤ fresh + 1)).trans hmono)
        · left
          simp only [Literal.var]
          exact lt_of_lt_of_le (by simp only [freshVar]; omega) hmono
      · exact ih hc' c hcmem
  | case2 => simpa [splitClause] using hc
  | case3 => simpa [splitClause] using hc
  | case4 => simpa [splitClause] using hc
  | case5 => simpa [splitClause] using hc

/-- Any assignment satisfying the split satisfies the clause. -/
theorem splitClause_sound (fresh : ℕ) (clause : Clause ℕ) (a : Assignment ℕ)
    (h : Formula.eval a (splitClause fresh clause).1 = true) : clause.eval a = true := by
  induction fresh, clause using splitClause.induct with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih =>
      rw [splitClause] at h
      simp only [Formula.eval_cons, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      have := ih htail
      simp only [Clause.eval_cons, Bool.or_eq_true, Literal.eval_positive, Literal.eval_negative,
        Clause.eval_nil, Bool.false_eq_true, or_false, Bool.not_eq_eq_eq_not, Bool.not_true] at hhead this ⊢
      cases hy : a (freshVar fresh)
      · simp only [hy, Bool.false_eq_true] at hhead; tauto
      · simp only [hy, Bool.true_eq_false, false_or] at this; tauto
  | case2 => simp [splitClause] at h
  | case3 => simpa [splitClause] using h
  | case4 => simpa [splitClause] using h
  | case5 => simpa [splitClause] using h

/-- Agreement of two assignments outside the fresh-variable window. -/
def AgreeOutside (lo hi : ℕ) (a a' : Assignment ℕ) : Prop :=
  ∀ v, v < lo ∨ hi ≤ v ∨ v % 2 = 0 → a' v = a v

theorem Clause.eval_of_agreeOutside {lo hi : ℕ} {a a' : Assignment ℕ}
    (hagree : AgreeOutside lo hi a a') (clause : Clause ℕ) (hc : VarsBelow lo clause) :
    clause.eval a' = clause.eval a := by
  apply Clause.eval_congr
  intro v hv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
  exact hagree _ ((hc l hl).imp_right id |>.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr h)))

theorem Formula.eval_of_agreeOutside {lo hi : ℕ} {a a' : Assignment ℕ}
    (hagree : AgreeOutside lo hi a a') (formula : Formula ℕ)
    (hf : ∀ c ∈ formula, VarsBelow lo c) :
    formula.eval a' = formula.eval a := by
  induction formula with
  | nil => rfl
  | cons c rest ih =>
      simp only [Formula.eval_cons]
      rw [Clause.eval_of_agreeOutside hagree c (hf c (by simp)), ih (fun c' hc' => hf c' (by simp [hc']))]

/-- A satisfying assignment extends to the split by choosing fresh values. -/
theorem splitClause_complete (fresh : ℕ) (clause : Clause ℕ)
    (hc : VarsBelow (freshVar fresh) clause) (a : Assignment ℕ) (ha : clause.eval a = true) :
    ∃ a', AgreeOutside (freshVar fresh) (freshVar (splitClause fresh clause).2) a a' ∧
      Formula.eval a' (splitClause fresh clause).1 = true := by
  induction fresh, clause using splitClause.induct generalizing a with
  | case1 fresh l₁ l₂ l₃ l₄ rest ih =>
      rw [splitClause]
      simp only
      set y := freshVar fresh with hy
      have hyodd : y % 2 = 1 := freshVar_odd fresh
      -- the fresh variable records that neither of the first two literals holds
      let a₁ : Assignment ℕ := Function.update a y (!(l₁.eval a || l₂.eval a))
      have hl₁ : l₁.eval a₁ = l₁.eval a := by
        apply Literal.eval_congr
        rcases hc l₁ (by simp) with h | h
        · exact Function.update_of_ne (by omega) _ _
        · exact Function.update_of_ne (by omega) _ _
      have hl₂ : l₂.eval a₁ = l₂.eval a := by
        apply Literal.eval_congr
        rcases hc l₂ (by simp) with h | h
        · exact Function.update_of_ne (by omega) _ _
        · exact Function.update_of_ne (by omega) _ _
      have htail : Clause.eval a₁ (l₃ :: l₄ :: rest) = Clause.eval a (l₃ :: l₄ :: rest) := by
        apply Clause.eval_congr
        intro v hv
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        rcases hc l (by simp [hl]) with h | h
        · exact Function.update_of_ne (by omega) _ _
        · exact Function.update_of_ne (by omega) _ _
      have hc' : VarsBelow (freshVar (fresh + 1)) (.negative y :: l₃ :: l₄ :: rest) := by
        intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl | hl | hl
        · left; simp only [Literal.var, hy, freshVar]; omega
        · exact (hc l (by simp [hl])).imp_left fun h => lt_of_lt_of_le h (freshVar_mono (by omega))
        · exact (hc l (by simp [hl])).imp_left fun h => lt_of_lt_of_le h (freshVar_mono (by omega))
        · exact (hc l (by simp [hl])).imp_left fun h => lt_of_lt_of_le h (freshVar_mono (by omega))
      have ha₁ : Clause.eval a₁ (.negative y :: l₃ :: l₄ :: rest) = true := by
        rw [Clause.eval_cons, htail, Literal.eval_negative]
        simp only [a₁, Function.update_self, Bool.not_not, Bool.or_assoc]
        rw [Clause.eval_cons, Clause.eval_cons] at ha
        exact ha
      obtain ⟨a', hagree, heval⟩ := ih hc' a₁ ha₁
      refine ⟨a', ?_, ?_⟩
      · intro v hv
        have hnext := splitClause_fresh_le (fresh + 1) (.negative y :: l₃ :: l₄ :: rest)
        have hvy : v ≠ y := by
          have h1 := freshVar_mono hnext
          simp only [hy, freshVar] at hv h1 ⊢
          omega
        rw [hagree v (by
          rcases hv with hv | hv | hv
          · left; exact lt_of_lt_of_le hv (freshVar_mono (by omega))
          · right; left; exact hv
          · right; right; exact hv)]
        exact Function.update_of_ne hvy _ _
      · simp only [Formula.eval_cons, heval, Bool.and_true]
        have hl₁' : l₁.eval a' = l₁.eval a := by
          rw [← hl₁]
          apply Literal.eval_congr
          rcases hc l₁ (by simp) with h | h
          · exact hagree _ (Or.inl (lt_of_lt_of_le h (freshVar_mono (by omega))))
          · exact hagree _ (Or.inr (Or.inr h))
        have hl₂' : l₂.eval a' = l₂.eval a := by
          rw [← hl₂]
          apply Literal.eval_congr
          rcases hc l₂ (by simp) with h | h
          · exact hagree _ (Or.inl (lt_of_lt_of_le h (freshVar_mono (by omega))))
          · exact hagree _ (Or.inr (Or.inr h))
        have hy' : a' y = !(l₁.eval a || l₂.eval a) := by
          rw [hagree y (Or.inl (by simp only [hy, freshVar]; omega))]
          simp [a₁]
        simp only [Clause.eval_cons, Literal.eval_positive, hl₁', hl₂', hy', Clause.eval_nil]
        cases l₁.eval a <;> cases l₂.eval a <;> simp
  | case2 fresh =>
      exact ⟨a, fun v _ => rfl, by simp at ha⟩
  | case3 fresh l₁ =>
      exact ⟨a, fun v _ => rfl, by simpa [splitClause] using ha⟩
  | case4 fresh l₁ l₂ =>
      exact ⟨a, fun v _ => rfl, by simpa [splitClause] using ha⟩
  | case5 fresh l₁ l₂ l₃ =>
      exact ⟨a, fun v _ => rfl, by simpa [splitClause] using ha⟩

/-- Split every clause, threading the fresh index through the formula. -/
def splitFormula (fresh : ℕ) : Formula ℕ → Formula ℕ × ℕ
  | [] => ([], fresh)
  | c :: rest =>
      let first := splitClause fresh c
      let more := splitFormula first.2 rest
      (first.1 ++ more.1, more.2)

theorem splitFormula_fresh_le (fresh : ℕ) (formula : Formula ℕ) :
    fresh ≤ (splitFormula fresh formula).2 := by
  induction formula generalizing fresh with
  | nil => simp [splitFormula]
  | cons c rest ih =>
      simp only [splitFormula]
      exact (splitClause_fresh_le fresh c).trans (ih _)

theorem splitFormula_width (fresh : ℕ) (formula : Formula ℕ) :
    ∀ c ∈ (splitFormula fresh formula).1, c.length ≤ 3 := by
  induction formula generalizing fresh with
  | nil => simp [splitFormula]
  | cons c rest ih =>
      simp only [splitFormula, List.mem_append]
      rintro c' (h | h)
      · exact splitClause_width fresh c c' h
      · exact ih _ c' h

theorem splitFormula_sound (fresh : ℕ) (formula : Formula ℕ) (a : Assignment ℕ)
    (h : Formula.eval a (splitFormula fresh formula).1 = true) : formula.eval a = true := by
  induction formula generalizing fresh with
  | nil => rfl
  | cons c rest ih =>
      simp only [splitFormula, Formula.eval_append, Bool.and_eq_true] at h
      simp only [Formula.eval_cons, Bool.and_eq_true]
      exact ⟨splitClause_sound fresh c a h.1, ih _ h.2⟩

theorem splitFormula_complete (fresh : ℕ) (formula : Formula ℕ)
    (hf : ∀ c ∈ formula, VarsBelow (freshVar fresh) c) (a : Assignment ℕ)
    (ha : formula.eval a = true) :
    ∃ a', AgreeOutside (freshVar fresh) (freshVar (splitFormula fresh formula).2) a a' ∧
      Formula.eval a' (splitFormula fresh formula).1 = true := by
  induction formula generalizing fresh a with
  | nil => exact ⟨a, fun v _ => rfl, rfl⟩
  | cons c rest ih =>
      simp only [splitFormula, Formula.eval_append]
      simp only [Formula.eval_cons, Bool.and_eq_true] at ha
      obtain ⟨a₁, hagree₁, heval₁⟩ := splitClause_complete fresh c (hf c (by simp)) a ha.1
      have hfresh₁ := splitClause_fresh_le fresh c
      have hrest : ∀ c' ∈ rest, VarsBelow (freshVar (splitClause fresh c).2) c' :=
        fun c' hc' => (hf c' (by simp [hc'])).mono (freshVar_mono hfresh₁)
      have ha₁ : Formula.eval a₁ rest = true := by
        rw [Formula.eval_of_agreeOutside hagree₁ rest (fun c' hc' => hf c' (by simp [hc']))]
        exact ha.2
      obtain ⟨a', hagree', heval'⟩ := ih _ hrest a₁ ha₁
      have hfresh₂ := splitFormula_fresh_le (splitClause fresh c).2 rest
      refine ⟨a', ?_, ?_⟩
      · intro v hv
        rw [hagree' v (by
          rcases hv with hv | hv | hv
          · left; exact lt_of_lt_of_le hv (freshVar_mono hfresh₁)
          · right; left; exact hv
          · right; right; exact hv)]
        exact hagree₁ v (by
          rcases hv with hv | hv | hv
          · left; exact hv
          · right; left; exact le_trans (freshVar_mono hfresh₂) hv
          · right; right; exact hv)
      · rw [Bool.and_eq_true]
        refine ⟨?_, heval'⟩
        rw [Formula.eval_of_agreeOutside hagree' (splitClause fresh c).1
          (splitClause_varsBelow fresh c (hf c (by simp)))]
        exact heval₁

/-- The complete splitting transformation: rename variables to even numbers
and split every clause. -/
def Formula.split (formula : Formula ℕ) : Formula ℕ :=
  (splitFormula 0 formula.double).1

theorem Formula.atMostWidth_split (formula : Formula ℕ) : formula.split.AtMostWidth 3 :=
  fun c hc => splitFormula_width 0 formula.double c hc

/-- Splitting preserves satisfiability. -/
theorem Formula.satisfiable_split (formula : Formula ℕ) :
    formula.split.Satisfiable ↔ formula.Satisfiable := by
  simp only [Formula.satisfiable_iff_exists_eval]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun v => a (2 * v), ?_⟩
    rw [← Formula.eval_double]
    exact splitFormula_sound 0 formula.double a ha
  · rintro ⟨a, ha⟩
    have hdouble : ∀ c ∈ formula.double, VarsBelow (freshVar 0) c := by
      intro c hc l hl
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hc
      exact Or.inr (Clause.var_even_of_mem_double c' l hl)
    obtain ⟨a', _, heval⟩ := splitFormula_complete 0 formula.double hdouble
      (fun v => a (v / 2)) (by rw [Formula.eval_double_halve]; exact ha)
    exact ⟨a', heval⟩

/-- Split then pad: every clause has exactly three literal occurrences. -/
def Formula.toExactThree (formula : Formula ℕ) : Formula ℕ :=
  formula.split.normalizeThree

theorem Formula.exactWidth_toExactThree (formula : Formula ℕ) :
    formula.toExactThree.ExactWidth 3 :=
  (Formula.exactWidth_normalizeThree _).mpr formula.atMostWidth_split

theorem Formula.satisfiable_toExactThree (formula : Formula ℕ) :
    formula.toExactThree.Satisfiable ↔ formula.Satisfiable := by
  rw [Formula.toExactThree, Formula.satisfiable_normalizeThree, Formula.satisfiable_split]

/-- Correctness of the SAT to exact 3-SAT transformation. -/
theorem sat_iff_exactThreeSAT_toExactThree (formula : Formula ℕ) :
    SAT formula ↔ ExactThreeSAT formula.toExactThree := by
  simp only [SAT, ExactThreeSAT, ExactKSAT, Formula.exactWidth_toExactThree,
    Formula.satisfiable_toExactThree, true_and, Nat.zero_lt_succ]

/-- Semantic many-one reduction from SAT to exact 3-SAT; the polynomial-time
implementation remains separate. -/
def satToExactThree : ManyOneReduction SAT ExactThreeSAT where
  map := Formula.toExactThree
  correct := sat_iff_exactThreeSAT_toExactThree

end LeanNPHardness.CNF
