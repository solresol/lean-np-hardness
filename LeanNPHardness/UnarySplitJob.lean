import LeanNPHardness.TableauJobs
import LeanNPHardness.CNFSplitting
import Mathlib.Tactic.Ring

/-!
# The splitting job

`Formula.toExactThree` (rename to even variables, split every clause with
fresh odd variables, pad short clauses) is expressed as a job for the
tableau interpreter: original literals become their sign and twice their
marks, and fresh variables are read from the `base` register, which starts
at `1` and advances by two (`advance2`, using the `w` register holding
`1`) after each use. `render_splitJob` proves the job renders to the unary
encoding of `toExactThree`.
-/

namespace LeanNPHardness.SplitJob

open CNF CNF.Unary TableauJobs

/-- The sign of a literal. -/
def litSign : Literal ℕ → Bool
  | .positive _ => true
  | .negative _ => false

/-- The job of one original literal: its sign and twice its marks. -/
def litJobD (l : Literal ℕ) : List Instr :=
  .lit (litSign l) :: List.replicate (2 * l.var) .mark

/-- A positive fresh literal, read from `base`. -/
def freshPos : List Instr := [.lit true, .reg .base]

/-- A negative fresh literal, read from `base`. -/
def freshNeg : List Instr := [.lit false, .reg .base]

/-- Advance `base` by two (`w` holds one). -/
def advance2 : List Instr := [.addTo .base .w, .addTo .base .w]

/-- Between two consecutive split clauses: close with the fresh positive
literal and open with its negation, then advance. -/
def extras : List Instr := freshPos ++ [.endClause] ++ freshNeg ++ advance2

/-- The job of splitting a clause whose first literal's job is `head`. -/
def splitJobAux (head : List Instr) : List (Literal ℕ) → List Instr
  | l₂ :: l₃ :: l₄ :: more =>
      head ++ litJobD l₂ ++ freshPos ++ [.endClause] ++
        splitJobAux (freshNeg ++ advance2) (l₃ :: l₄ :: more)
  | [l₂, l₃] => head ++ litJobD l₂ ++ litJobD l₃ ++ [.endClause]
  | [l₂] => head ++ litJobD l₂ ++ head ++ [.endClause]
  | [] => head ++ head ++ head ++ [.endClause]

/-- The job of the padded empty clause. -/
def emptyClauseJob : List Instr :=
  [.lit true, .lit true, .lit true, .endClause, .lit false, .lit false, .lit false, .endClause]

/-- The job of one clause. -/
def clauseJob : Clause ℕ → List Instr
  | [] => emptyClauseJob
  | l₁ :: rest => splitJobAux (litJobD l₁) rest

/-- The job of a formula. -/
def splitJob (F : Formula ℕ) : List Instr := F.flatMap clauseJob

/-! ### Rendering -/

theorem render_litJobD (R : Regs) (l : Literal ℕ) :
    render R (litJobD l) = (encodeLiteral l.double, R) := by
  cases l with
  | positive v =>
      simp only [litJobD, litSign, Literal.var, render, renderInstr, render_marks, Literal.double,
        encodeLiteral, List.singleton_append]
  | negative v =>
      simp only [litJobD, litSign, Literal.var, render, renderInstr, render_marks, Literal.double,
        encodeLiteral, List.singleton_append]

theorem render_freshPos (R : Regs) :
    render R freshPos = (encodeLiteral (.positive (R .base)), R) := by
  simp [freshPos, render, renderInstr, encodeLiteral]

theorem render_freshNeg (R : Regs) :
    render R freshNeg = (encodeLiteral (.negative (R .base)), R) := by
  simp [freshNeg, render, renderInstr, encodeLiteral]

theorem render_advance2 (R : Regs) (hw : R .w = 1) :
    render R advance2 = ([], Function.update R .base (R .base + 2)) := by
  simp only [advance2, render, renderInstr, List.nil_append]
  congr 1
  rw [Function.update_idem, Function.update_self, Function.update_of_ne (by decide), hw]

theorem render_endClause (R : Regs) : render R [.endClause] = ([.endClause], R) := by
  simp [render, renderInstr]

theorem normalizeThree_three (a b c : Literal ℕ) : Clause.normalizeThree [a, b, c] = [[a, b, c]] := rfl

/-- Rendering the splitting job of a clause with at least two literals after
the head. -/
theorem render_splitJobAux : ∀ (H : List Instr) (rest : List (Literal ℕ)) (h : Literal ℕ) (f : ℕ)
    (R R₁ : Regs), 2 ≤ rest.length →
      render R H = (encodeLiteral h, R₁) → R₁ .base = 2 * f + 1 → R₁ .w = 1 →
      render R (splitJobAux H rest) =
        (encode ((splitClause f (h :: rest.map Literal.double)).1.flatMap Clause.normalizeThree),
          Function.update R₁ .base (2 * (splitClause f (h :: rest.map Literal.double)).2 + 1)) := by
  intro H rest
  induction H, rest using splitJobAux.induct with
  | case1 H l₂ l₃ l₄ more ih =>
      intro h f R R₁ _ hH hb hw
      have hH' : render R₁ (freshNeg ++ advance2) =
          (encodeLiteral (.negative (freshVar f)), Function.update R₁ .base (R₁ .base + 2)) := by
        rw [render_append, render_freshNeg, render_advance2 _ hw]
        simp [freshVar, hb]
      have ih' := ih (.negative (freshVar f)) (f + 1) R₁
        (Function.update R₁ .base (R₁ .base + 2)) (by simp) hH'
        (by simp only [Function.update_self, hb]; ring) (by simp [Function.update_of_ne, hw])
      simp only [splitJobAux, render_append, hH, render_litJobD, render_freshPos, render_endClause,
        ih', List.map_cons, Function.update_idem]
      rw [splitClause]
      simp only [List.flatMap_cons, normalizeThree_three, List.append_assoc, hb, freshVar]
      rw [Prod.mk.injEq]
      constructor
      · simp [encode_cons, encodeClause, List.append_assoc]
      · rfl
  | case2 H l₂ l₃ =>
      intro h f R R₁ _ hH hb hw
      simp only [splitJobAux, render_append, hH, render_litJobD, render_endClause, List.map_cons,
        List.map_nil]
      rw [splitClause]
      simp only [List.flatMap_cons, List.flatMap_nil, normalizeThree_three, encode_cons, encodeClause,
        encode_nil, List.append_nil, List.append_assoc]
      rw [← hb, Function.update_eq_self]
  | case3 H l₂ =>
      intro _ _ _ _ h
      simp at h
  | case4 H =>
      intro _ _ _ _ h
      simp at h

theorem render_clauseJob (c : Clause ℕ) (f : ℕ) (R : Regs) (hb : R .base = 2 * f + 1)
    (hw : R .w = 1) :
    render R (clauseJob c) =
      (encode ((splitClause f c.double).1.flatMap Clause.normalizeThree),
        Function.update R .base (2 * (splitClause f c.double).2 + 1)) := by
  rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, rest⟩⟩⟩
  · simp only [clauseJob, emptyClauseJob, Clause.double, List.map_nil]
    rw [splitClause]
    simp only [List.flatMap_cons, List.flatMap_nil, Clause.normalizeThree, encode_cons, encodeClause,
      encode_nil, encodeLiteral, render, renderInstr, List.append_nil, List.flatMap_cons,
      List.replicate_zero]
    rw [← hb, Function.update_eq_self]
    rfl
  · simp only [clauseJob, splitJobAux, render_append, render_litJobD, render_endClause,
      Clause.double, List.map_cons, List.map_nil]
    rw [splitClause]
    simp only [List.flatMap_cons, List.flatMap_nil, Clause.normalizeThree, encode_cons, encodeClause,
      encode_nil, List.append_nil, List.flatMap_cons, List.append_assoc]
    rw [← hb, Function.update_eq_self]
  · simp only [clauseJob, splitJobAux, render_append, render_litJobD, render_endClause,
      Clause.double, List.map_cons, List.map_nil]
    rw [splitClause]
    simp only [List.flatMap_cons, List.flatMap_nil, Clause.normalizeThree, encode_cons, encodeClause,
      encode_nil, List.append_nil, List.flatMap_cons, List.append_assoc]
    rw [← hb, Function.update_eq_self]
  · have := render_splitJobAux (litJobD l₁) (l₂ :: l₃ :: rest) l₁.double f R R (by simp)
      (render_litJobD R l₁) hb hw
    simp only [clauseJob, Clause.double, List.map_cons]
    exact this

/-- The splitting job of a formula renders to the padded split formula,
threading the fresh index through `base`. -/
theorem render_splitJob (F : Formula ℕ) : ∀ (f : ℕ) (R : Regs), R .base = 2 * f + 1 → R .w = 1 →
    render R (splitJob F) =
      (encode ((splitFormula f F.double).1.flatMap Clause.normalizeThree),
        Function.update R .base (2 * (splitFormula f F.double).2 + 1)) := by
  induction F with
  | nil =>
      intro f R hb _
      simp only [splitJob, List.flatMap_nil, render, Formula.double, List.map_nil, splitFormula,
        List.flatMap_nil, encode_nil]
      rw [← hb, Function.update_eq_self]
  | cons c F ih =>
      intro f R hb hw
      rw [splitJob, List.flatMap_cons, render_append, ← splitJob, render_clauseJob c f R hb hw,
        ih (splitClause f c.double).2 _ (by simp) (by simp [Function.update_of_ne, hw])]
      simp only [Formula.double, List.map_cons, splitFormula, List.flatMap_append, encode_append,
        Function.update_idem]

/-- The job renders to the unary encoding of `toExactThree`. -/
theorem render_splitJob_toExactThree (F : Formula ℕ) (R : Regs) (hb : R .base = 1) (hw : R .w = 1) :
    (render R (splitJob F)).1 = encode F.toExactThree := by
  rw [render_splitJob F 0 R (by omega) hw]
  rfl

/-! ### Validity of the instructions -/

theorem ok_of_mem_litJobD (l : Literal ℕ) : ∀ i ∈ litJobD l, i.ok := by
  intro i hi
  simp only [litJobD, List.mem_cons, List.mem_replicate] at hi
  rcases hi with rfl | ⟨_, rfl⟩ <;> trivial

theorem ok_of_mem_extrasParts : ∀ i ∈ freshPos ++ [Instr.endClause] ++ freshNeg ++ advance2, i.ok := by
  intro i hi
  simp only [freshPos, freshNeg, advance2, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with (((rfl | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl) <;> simp [Instr.ok]

theorem ok_of_mem_splitJobAux : ∀ (H : List Instr) (rest : List (Literal ℕ)), (∀ i ∈ H, i.ok) →
    ∀ i ∈ splitJobAux H rest, i.ok := by
  intro H rest
  induction H, rest using splitJobAux.induct with
  | case1 H l₂ l₃ l₄ more ih =>
      intro hH i hi
      simp only [splitJobAux, List.mem_append] at hi
      rcases hi with (((h | h) | h) | h) | h
      · exact hH i h
      · exact ok_of_mem_litJobD l₂ i h
      · exact ok_of_mem_extrasParts i (by simp [h])
      · exact ok_of_mem_extrasParts i (by simp only [List.mem_singleton] at h; subst h; simp)
      · exact ih (fun j hj => ok_of_mem_extrasParts j (by simp only [List.mem_append] at hj ⊢; tauto))
          i h
  | case2 H l₂ l₃ =>
      intro hH i hi
      simp only [splitJobAux, List.mem_append] at hi
      rcases hi with ((h | h) | h) | h
      · exact hH i h
      · exact ok_of_mem_litJobD l₂ i h
      · exact ok_of_mem_litJobD l₃ i h
      · simp only [List.mem_singleton] at h; subst h; trivial
  | case3 H l₂ =>
      intro hH i hi
      simp only [splitJobAux, List.mem_append] at hi
      rcases hi with ((h | h) | h) | h
      · exact hH i h
      · exact ok_of_mem_litJobD l₂ i h
      · exact hH i h
      · simp only [List.mem_singleton] at h; subst h; trivial
  | case4 H =>
      intro hH i hi
      simp only [splitJobAux, List.mem_append] at hi
      rcases hi with ((h | h) | h) | h
      · exact hH i h
      · exact hH i h
      · exact hH i h
      · simp only [List.mem_singleton] at h; subst h; trivial

theorem ok_of_mem_clauseJob (c : Clause ℕ) : ∀ i ∈ clauseJob c, i.ok := by
  rcases c with _ | ⟨l₁, rest⟩
  · intro i hi
    simp only [clauseJob, emptyClauseJob, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · exact ok_of_mem_splitJobAux _ rest (ok_of_mem_litJobD l₁)

theorem ok_of_mem_splitJob (F : Formula ℕ) : ∀ i ∈ splitJob F, i.ok := by
  intro i hi
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hi
  exact ok_of_mem_clauseJob c i hc

end LeanNPHardness.SplitJob
