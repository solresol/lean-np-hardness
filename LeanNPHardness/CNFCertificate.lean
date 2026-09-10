import LeanNPHardness.CNFEncoding
import LeanNPHardness.RawNatEncoding

/-!
# Finite CNF assignment certificates

A certificate lists the variables assigned true; all others are false. Filter
the formula's variable occurrences to represent any total Boolean assignment
on its relevant inputs, retaining repetitions and order. The encoded-size
bound below uses formula bits, including binary variable names. These are
semantic and size results; no polynomial-time verifier machine is asserted.
-/

namespace LeanNPHardness.CNF

universe u

namespace Literal

/-- The variable mentioned by a literal, independently of its polarity. -/
def var {α : Type u} : Literal α → α
  | .positive v => v
  | .negative v => v

theorem eval_congr {α : Type u} (literal : Literal α)
    {left right : Assignment α} (agree : left literal.var = right literal.var) :
    literal.eval left = literal.eval right := by
  cases literal <;> simp_all [eval, var]

theorem var_le_toNat (literal : Literal Nat) : literal.var ≤ literal.toNat := by
  cases literal <;> simp only [var, toNat] <;> omega

end Literal

namespace Clause

/-- Variable occurrences, with the clause's order and repetitions retained. -/
def vars {α : Type u} (clause : Clause α) : List α :=
  clause.map Literal.var

theorem eval_congr {α : Type u} (clause : Clause α)
    {left right : Assignment α}
    (agree : ∀ v ∈ clause.vars, left v = right v) :
    clause.eval left = clause.eval right := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp only [eval_cons]
      rw [literal.eval_congr (agree literal.var (by simp [vars]))]
      rw [ih (fun v hv => agree v (by simp [vars] at hv ⊢; exact Or.inr hv))]

end Clause

/-- A finite list of true variables. Repeated entries have membership semantics. -/
abbrev Certificate (α : Type u) := List α

namespace Certificate

/-- Interpret a finite certificate as a total Boolean assignment. -/
def assignment {α : Type u} [DecidableEq α] (certificate : Certificate α) :
    Assignment α := fun v => decide (v ∈ certificate)

/-- Use the existing framed binary natural-list encoding for certificates. -/
def finEncoding : Computability.FinEncoding (Certificate Nat) :=
  FramedNatList.finEncoding

/-- Executable Boolean verification, with no machine-runtime claim. -/
def verify (formula : Formula Nat) (certificate : Certificate Nat) : Bool :=
  formula.eval certificate.assignment

theorem verify_sound (formula : Formula Nat) (certificate : Certificate Nat)
    (accepted : verify formula certificate = true) : formula.Satisfiable :=
  ⟨certificate.assignment, (Formula.eval_eq_true _ _).mp accepted⟩

end Certificate

namespace Formula

/-- All variable occurrences in formula order, retaining repetitions. -/
def vars {α : Type u} (formula : Formula α) : List α :=
  formula.flatMap Clause.vars

/-- Formula evaluation depends only on its occurring variables. -/
theorem eval_congr {α : Type u} (formula : Formula α)
    {left right : Assignment α}
    (agree : ∀ v ∈ formula.vars, left v = right v) :
    formula.eval left = formula.eval right := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      simp only [eval_cons]
      rw [clause.eval_congr (fun v hv => agree v (by simp [vars, hv]))]
      rw [ih (fun v hv => agree v (by simp [vars] at hv ⊢; exact Or.inr hv))]

/-- Keep each occurrence whose variable is true under the supplied assignment. -/
def trueVariables {α : Type u} (formula : Formula α) (a : Assignment α) :
    Certificate α := formula.vars.filter a

/-- The constructed certificate agrees on every occurring variable. -/
theorem assignment_trueVariables {α : Type u} [DecidableEq α]
    (formula : Formula α) (a : Assignment α) (v : α)
    (occurs : v ∈ formula.vars) :
    (formula.trueVariables a).assignment v = a v := by
  cases h : a v <;> simp [Certificate.assignment, trueVariables, occurs, h]

/-- A finite occurrence list preserves the entire Boolean evaluation. -/
theorem eval_trueVariables {α : Type u} [DecidableEq α]
    (formula : Formula α) (a : Assignment α) :
    formula.eval (formula.trueVariables a).assignment = formula.eval a :=
  formula.eval_congr (formula.assignment_trueVariables a)

/-- Dropping literal polarity cannot increase the total framed payload size. -/
theorem vars_payloadSize_le_encodedSize (formula : Formula Nat) :
    (formula.vars.map BinaryNatLists.natWireSize).sum ≤ formula.encodedSize := by
  have payload : (formula.vars.map BinaryNatLists.natWireSize).sum ≤
      (formula.map fun clause => BinaryNatLists.natWireSize clause.length +
        (clause.map fun literal => BinaryNatLists.natWireSize literal.toNat).sum).sum := by
    induction formula with
    | nil => simp [vars]
    | cons clause formula ih =>
        have hc : (clause.vars.map BinaryNatLists.natWireSize).sum ≤
            (clause.map fun literal => BinaryNatLists.natWireSize literal.toNat).sum := by
          simp only [Clause.vars, List.map_map]
          exact List.sum_le_sum fun literal _ =>
            BinaryNatLists.natWireSize_mono literal.var_le_toNat
        simp only [vars, List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons] at ih ⊢
        omega
  exact payload.trans (Nat.le_add_left _ _)

/-- Literal occurrences are bounded by the formula's actual encoded bit count. -/
theorem vars_length_le_encodedSize (formula : Formula Nat) :
    formula.vars.length ≤ formula.encodedSize := by
  have count (xs : List Nat) : xs.length ≤ (xs.map BinaryNatLists.natWireSize).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := BinaryNatLists.natWireSize_pos x
        omega
  exact (count formula.vars).trans formula.vars_payloadSize_le_encodedSize

/-- Finite certificates have a linear bound in formula bits, independent of the
largest variable index. The extra bit accounts for the empty-list length frame. -/
theorem trueVariables_encode_length_le (formula : Formula Nat) (a : Assignment Nat) :
    (Certificate.finEncoding.encode (formula.trueVariables a)).length ≤
      3 * formula.encodedSize + 1 := by
  have hlen : (formula.trueVariables a).length ≤ formula.encodedSize :=
    (List.length_filter_le a formula.vars).trans formula.vars_length_le_encodedSize
  have hsum : ((formula.trueVariables a).map BinaryNatLists.natWireSize).sum ≤
      formula.encodedSize := by
    exact ((List.filter_sublist (p := a) (l := formula.vars)).map
      BinaryNatLists.natWireSize).sum_le_sum (fun _ _ => Nat.zero_le _) |>.trans
        formula.vars_payloadSize_le_encodedSize
  have hheader := BinaryNatLists.natWireSize_le_two_mul_add_one
    (formula.trueVariables a).length
  change (BinaryNatLists.encodeNatList (formula.trueVariables a)).length ≤ _
  rw [BinaryNatLists.encodeNatList_length, BinaryNatLists.listWireSize]
  omega

/-- SAT is equivalent to existence of a linearly bounded finite certificate.
The remaining NP obligation is a polynomial-time TM2 implementation of verification. -/
theorem satisfiable_iff_exists_bounded_certificate (formula : Formula Nat) :
    formula.Satisfiable ↔ ∃ certificate : Certificate Nat,
      (Certificate.finEncoding.encode certificate).length ≤ 3 * formula.encodedSize + 1 ∧
        Certificate.verify formula certificate = true := by
  constructor
  · rintro ⟨a, satisfied⟩
    refine ⟨formula.trueVariables a, formula.trueVariables_encode_length_le a, ?_⟩
    change formula.eval (formula.trueVariables a).assignment = true
    rw [formula.eval_trueVariables]
    exact (eval_eq_true _ _).mpr satisfied
  · rintro ⟨certificate, _, accepted⟩
    exact Certificate.verify_sound formula certificate accepted

end Formula

end LeanNPHardness.CNF
