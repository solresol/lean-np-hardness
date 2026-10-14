import LeanNPHardness.CNFCertificate

/-!
# Finite Boolean relations as CNF constraints

A relation on the values of a finite list of variables is written in
conjunctive normal form by forbidding each rejected assignment with one
clause. `eval_relationCNF` identifies the formula's Boolean value with the
relation applied to the variables' values. Variable lists may repeat
variables; the construction then constrains the repeated value consistently.
These are semantic results with explicit clause and width counts. No
machine-runtime claim is made.
-/

namespace LeanNPHardness.CNF.Constraint

/-- All Boolean lists of the given length, listed once each. -/
def allAssignments : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allAssignments n).flatMap fun α => [false :: α, true :: α]

@[simp]
theorem mem_allAssignments (n : ℕ) (α : List Bool) :
    α ∈ allAssignments n ↔ α.length = n := by
  induction n generalizing α with
  | zero =>
      simp [allAssignments, List.length_eq_zero_iff]
  | succ n ih =>
      cases α with
      | nil => simp [allAssignments]
      | cons b bs =>
          simp only [allAssignments, List.mem_flatMap, List.mem_cons,
            List.not_mem_nil, or_false, List.cons.injEq,
            List.length_cons, Nat.add_right_cancel_iff, ih]
          constructor
          · rintro ⟨β, hβ, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> exact hβ
          · intro h
            exact ⟨bs, h, by cases b <;> simp⟩

@[simp]
theorem length_allAssignments (n : ℕ) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [allAssignments, List.length_flatMap, ih, Nat.pow_succ]

/-- The clause that is false exactly when each listed variable takes the
corresponding listed value. Surplus entries on either side are ignored. -/
def forbidClause : List ℕ → List Bool → Clause ℕ
  | [], _ => []
  | _, [] => []
  | v :: vars, b :: bs =>
      (if b then Literal.negative v else Literal.positive v) :: forbidClause vars bs

@[simp]
theorem forbidClause_length (vars : List ℕ) (α : List Bool) :
    (forbidClause vars α).length = min vars.length α.length := by
  induction vars generalizing α with
  | nil => simp [forbidClause]
  | cons v vars ih =>
      cases α with
      | nil => simp [forbidClause]
      | cons b bs => simp [forbidClause, ih]

theorem forbidClause_var_mem (vars : List ℕ) (α : List Bool)
    (literal : Literal ℕ) (h : literal ∈ forbidClause vars α) :
    literal.var ∈ vars := by
  induction vars generalizing α with
  | nil => simp [forbidClause] at h
  | cons v vars ih =>
      cases α with
      | nil => simp [forbidClause] at h
      | cons b bs =>
          simp only [forbidClause, List.mem_cons] at h
          rcases h with rfl | h
          · cases b <;> simp [Literal.var]
          · exact List.mem_cons_of_mem _ (ih bs h)

/-- The forbidding clause is satisfied precisely when the variables do not
take the forbidden values. -/
theorem eval_forbidClause_eq_true_iff (a : Assignment ℕ) :
    ∀ (vars : List ℕ) (α : List Bool), α.length = vars.length →
      ((forbidClause vars α).eval a = true ↔ vars.map a ≠ α)
  | [], [], _ => by simp [forbidClause, Clause.eval]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | v :: vars, b :: bs, h => by
      have ih := eval_forbidClause_eq_true_iff a vars bs (by simpa using h)
      simp only [forbidClause, Clause.eval_cons, List.map_cons, Bool.or_eq_true, ih]
      cases b <;> cases hv : a v <;> simp [Literal.eval, hv]

/-- The conjunction forbidding every assignment rejected by the relation. -/
def relationCNF (vars : List ℕ) (R : List Bool → Bool) : Formula ℕ :=
  ((allAssignments vars.length).filter fun α => !R α).map (forbidClause vars)

/-- The relation formula evaluates to the relation at the variables' values. -/
theorem eval_relationCNF_eq_true_iff (a : Assignment ℕ) (vars : List ℕ)
    (R : List Bool → Bool) :
    (relationCNF vars R).eval a = true ↔ R (vars.map a) = true := by
  simp only [relationCNF, Formula.eval, List.all_eq_true, List.mem_map,
    List.mem_filter, mem_allAssignments, Bool.not_eq_eq_eq_not, Bool.not_true,
    forall_exists_index, and_imp]
  constructor
  · intro h
    by_contra hR
    have hR' : R (vars.map a) = false := by
      cases hRv : R (vars.map a)
      · rfl
      · exact (hR hRv).elim
    have := h (forbidClause vars (vars.map a)) (vars.map a) (by simp) hR' rfl
    rw [eval_forbidClause_eq_true_iff a vars (vars.map a) (by simp)] at this
    exact this rfl
  · rintro h clause α hα hR rfl
    rw [eval_forbidClause_eq_true_iff a vars α hα]
    rintro rfl
    rw [h] at hR
    cases hR

@[simp]
theorem eval_relationCNF (a : Assignment ℕ) (vars : List ℕ)
    (R : List Bool → Bool) :
    (relationCNF vars R).eval a = R (vars.map a) := by
  cases h : R (vars.map a)
  · cases h' : (relationCNF vars R).eval a
    · rfl
    · rw [eval_relationCNF_eq_true_iff] at h'
      rw [h] at h'
      cases h'
  · exact (eval_relationCNF_eq_true_iff a vars R).2 h

theorem relationCNF_length_le (vars : List ℕ) (R : List Bool → Bool) :
    (relationCNF vars R).length ≤ 2 ^ vars.length := by
  simp only [relationCNF, List.length_map]
  exact (List.length_filter_le _ _).trans (le_of_eq (length_allAssignments _))

theorem relationCNF_clause_length (vars : List ℕ) (R : List Bool → Bool)
    (clause : Clause ℕ) (h : clause ∈ relationCNF vars R) :
    clause.length = vars.length := by
  simp only [relationCNF, List.mem_map, List.mem_filter, mem_allAssignments] at h
  obtain ⟨α, ⟨hα, _⟩, rfl⟩ := h
  simp [hα]

theorem relationCNF_var_mem (vars : List ℕ) (R : List Bool → Bool)
    (clause : Clause ℕ) (h : clause ∈ relationCNF vars R)
    (literal : Literal ℕ) (hl : literal ∈ clause) :
    literal.var ∈ vars := by
  simp only [relationCNF, List.mem_map, List.mem_filter, mem_allAssignments] at h
  obtain ⟨α, _, rfl⟩ := h
  exact forbidClause_var_mem vars α literal hl

/-- Concatenating constraint formulas conjoins them. -/
theorem eval_append_eq_true_iff (a : Assignment ℕ) (left right : Formula ℕ) :
    (left ++ right).eval a = true ↔ left.eval a = true ∧ right.eval a = true := by
  simp [Formula.eval_append]

theorem eval_flatMap_eq_true_iff {ι : Type*} (a : Assignment ℕ) (items : List ι)
    (f : ι → Formula ℕ) :
    Formula.eval a (items.flatMap f) = true ↔
      ∀ i ∈ items, Formula.eval a (f i) = true := by
  induction items with
  | nil => simp
  | cons i items ih =>
      rw [List.flatMap_cons, Formula.eval_append]
      simp [ih]

end LeanNPHardness.CNF.Constraint
