import LeanNPHardness.SemanticReduction
import Mathlib.Data.List.Basic

/-!
# List-based conjunctive normal form

Literal occurrences, clause order, and repeated clauses are retained in the
syntax. Boolean evaluation is proved equivalent to propositional satisfaction.
The languages below are semantic predicates. `CNFEncoding` supplies their finite
encodings; finite assignment certificates and polynomial-time machine witnesses
remain separate future results.
-/

namespace LeanNPHardness.CNF

universe u

/-- A Boolean assignment to variables. -/
abbrev Assignment (α : Type u) := α → Bool

/-- A variable with positive or negative polarity. -/
inductive Literal (α : Type u) where
  | positive : α → Literal α
  | negative : α → Literal α
  deriving DecidableEq, Repr

/-- A disjunction retaining every literal occurrence, including repetitions. -/
abbrev Clause (α : Type u) := List (Literal α)

/-- A conjunction retaining every clause occurrence, including repetitions. -/
abbrev Formula (α : Type u) := List (Clause α)

namespace Literal

variable {α : Type u}

/-- Evaluate a literal under a supplied Boolean assignment. -/
def eval (assignment : Assignment α) : Literal α → Bool
  | .positive v => assignment v
  | .negative v => !(assignment v)

/-- Propositional satisfaction, independent of the evaluator. -/
def Satisfied (assignment : Assignment α) : Literal α → Prop
  | .positive v => assignment v = true
  | .negative v => assignment v = false

@[simp]
theorem eval_eq_true (assignment : Assignment α) (literal : Literal α) :
    literal.eval assignment = true ↔ literal.Satisfied assignment := by
  cases literal <;> simp [eval, Satisfied]

end Literal

namespace Clause

variable {α : Type u}

/-- Evaluate disjunction by inspecting the literal list. -/
def eval (assignment : Assignment α) (clause : Clause α) : Bool :=
  clause.any (Literal.eval assignment)

/-- A clause is satisfied when at least one listed literal is satisfied. -/
def Satisfied (assignment : Assignment α) (clause : Clause α) : Prop :=
  ∃ literal ∈ clause, literal.Satisfied assignment

@[simp]
theorem eval_eq_true (assignment : Assignment α) (clause : Clause α) :
    clause.eval assignment = true ↔ clause.Satisfied assignment := by
  simp [eval, Satisfied]

@[simp]
theorem eval_nil (assignment : Assignment α) :
    eval assignment ([] : Clause α) = false := rfl

@[simp]
theorem eval_cons (assignment : Assignment α) (literal : Literal α)
    (clause : Clause α) :
    eval assignment (literal :: clause) =
      (literal.eval assignment || clause.eval assignment) := rfl

theorem eval_append (assignment : Assignment α) (left right : Clause α) :
    eval assignment (left ++ right) =
      (left.eval assignment || right.eval assignment) := by
  simp [eval]

end Clause

namespace Formula

variable {α : Type u}

/-- Evaluate conjunction by inspecting the clause list. -/
def eval (assignment : Assignment α) (formula : Formula α) : Bool :=
  formula.all (Clause.eval assignment)

/-- Every listed clause must have a satisfied literal. -/
def Satisfied (assignment : Assignment α) (formula : Formula α) : Prop :=
  ∀ clause ∈ formula, clause.Satisfied assignment

/-- A formula has a satisfying Boolean assignment. -/
def Satisfiable (formula : Formula α) : Prop :=
  ∃ assignment, formula.Satisfied assignment

/-- Exact width counts literal occurrences, including repetitions. -/
def ExactWidth (k : Nat) (formula : Formula α) : Prop :=
  ∀ clause ∈ formula, clause.length = k

@[simp]
theorem eval_eq_true (assignment : Assignment α) (formula : Formula α) :
    formula.eval assignment = true ↔ formula.Satisfied assignment := by
  simp [eval, Satisfied]

/-- The executable evaluator recognizes precisely the satisfying assignments. -/
theorem satisfiable_iff_exists_eval (formula : Formula α) :
    formula.Satisfiable ↔ ∃ assignment, formula.eval assignment = true := by
  simp [Satisfiable]

@[simp]
theorem eval_nil (assignment : Assignment α) :
    eval assignment ([] : Formula α) = true := rfl

@[simp]
theorem eval_cons (assignment : Assignment α) (clause : Clause α)
    (formula : Formula α) :
    eval assignment (clause :: formula) =
      (clause.eval assignment && formula.eval assignment) := rfl

theorem eval_append (assignment : Assignment α) (left right : Formula α) :
    eval assignment (left ++ right) =
      (left.eval assignment && right.eval assignment) := by
  simp [eval]

/-- The empty conjunction is satisfiable even when the variable type is empty. -/
theorem satisfiable_nil : Satisfiable ([] : Formula α) :=
  ⟨fun _ => false, by simp [Satisfied]⟩

/-- An empty disjunction makes the entire conjunction unsatisfiable. -/
theorem not_satisfiable_of_nil_mem (formula : Formula α)
    (emptyClause : [] ∈ formula) : ¬ formula.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  simpa [Clause.Satisfied] using satisfied [] emptyClause

/-- Repeated occurrences count separately for exact width. -/
theorem exactWidth_repeated_triple (literal : Literal α) :
    ExactWidth 3 [[literal, literal, literal]] := by
  simp [ExactWidth]

end Formula

/-- Semantic CNF-SAT on natural-number variables; `encodedSAT` in `CNFEncoding`
bundles this predicate with a finite encoding. -/
def SAT : Language (Formula Nat) := Formula.Satisfiable

/-- Semantic exact `k`-SAT, retaining repetitions in the width constraint.
As in the Coq comparison development, the language requires positive `k`. -/
def ExactKSAT (k : Nat) : Language (Formula Nat) :=
  fun formula => 0 < k ∧ formula.ExactWidth k ∧ formula.Satisfiable

/-- The exact-three-literal language used by downstream reductions. -/
abbrev ExactThreeSAT : Language (Formula Nat) := ExactKSAT 3

end LeanNPHardness.CNF
