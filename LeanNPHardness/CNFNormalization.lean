import LeanNPHardness.CNFEncoding

/-!
# Padding short clauses to exact three-literal clauses

Repeat an existing literal to pad nonempty clauses of width one or two.
Replace an empty clause by two contradictory repeated triples on variable zero.
Longer clauses are retained. Every assignment has the same evaluation before
and after this transformation, and the output has exact width three precisely
when the input has width at most three. The encoded-size bound is separate
from the still-pending TM2 implementation and runtime bound.
-/

namespace LeanNPHardness.CNF

namespace Clause

/-- Bits in a clause's length frame and packed literal frames. -/
def encodedSize (clause : Clause Nat) : Nat :=
  BinaryNatLists.natWireSize clause.length +
    (clause.map fun literal => BinaryNatLists.natWireSize literal.toNat).sum

theorem encodedSize_pos (clause : Clause Nat) : 0 < clause.encodedSize :=
  (BinaryNatLists.natWireSize_pos clause.length).trans_le (Nat.le_add_right _ _)

/-- Preserve long clauses and pad nonempty short clauses using existing literals.
An empty clause becomes a fixed contradiction on variable zero. -/
def normalizeThree : Clause Nat → Formula Nat
  | [] => [[.positive 0, .positive 0, .positive 0],
      [.negative 0, .negative 0, .negative 0]]
  | [a] => [[a, a, a]]
  | [a, b] => [[a, b, a]]
  | clause => [clause]

/-- Padding preserves Boolean evaluation, including the empty-clause case. -/
theorem eval_normalizeThree (clause : Clause Nat) (assignment : Assignment Nat) :
    Formula.eval assignment clause.normalizeThree = clause.eval assignment := by
  rcases clause with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [normalizeThree, Literal.eval]
  · simp [normalizeThree, Bool.or_self]
  · simp [normalizeThree, Bool.or_comm]
  · simp [normalizeThree]

theorem exactWidth_normalizeThree (clause : Clause Nat) :
    clause.normalizeThree.ExactWidth 3 ↔ clause.length ≤ 3 := by
  rcases clause with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals simp [normalizeThree, Formula.ExactWidth]

theorem normalizeThree_length_le (clause : Clause Nat) :
    clause.normalizeThree.length ≤ 2 := by
  rcases clause with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals simp [normalizeThree]

/-- Bound the full output clause frames, including the fixed contradiction.
The factor is uniform in binary variable names and deliberately loose. -/
theorem normalizeThree_payloadSize_le (clause : Clause Nat) :
    (clause.normalizeThree.map encodedSize).sum ≤ 22 * clause.encodedSize := by
  have hzero : BinaryNatLists.natWireSize 0 = 1 := by
    simp [BinaryNatLists.natWireSize, BinaryNatLists.encodeNat_length_eq_size]
  have hone : BinaryNatLists.natWireSize 1 = 3 := by
    simp [BinaryNatLists.natWireSize, BinaryNatLists.encodeNat_length_eq_size]
  have htwo : BinaryNatLists.natWireSize 2 = 5 := by
    rw [BinaryNatLists.natWireSize, BinaryNatLists.encodeNat_length_eq_size]
    change 2 * Nat.size (Nat.bit false 1) + 1 = 5
    rw [Nat.size_bit (by decide), Nat.size_one]
  have hthree : BinaryNatLists.natWireSize 3 = 5 := by
    rw [BinaryNatLists.natWireSize, BinaryNatLists.encodeNat_length_eq_size]
    change 2 * Nat.size (Nat.bit true 1) + 1 = 5
    rw [Nat.size_bit (by decide), Nat.size_one]
  rcases clause with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals simp [normalizeThree, encodedSize, Literal.toNat,
    hzero, hone, htwo, hthree] <;> omega

end Clause

namespace Formula

/-- An upper width bound counts all occurrences, including repetitions. -/
def AtMostWidth {α : Type*} (k : Nat) (formula : Formula α) : Prop :=
  ∀ clause ∈ formula, clause.length ≤ k

/-- Apply local padding in formula order, retaining repeated clauses. -/
def normalizeThree (formula : Formula Nat) : Formula Nat :=
  formula.flatMap Clause.normalizeThree

theorem encodedSize_eq (formula : Formula Nat) :
    formula.encodedSize = BinaryNatLists.natWireSize formula.length +
      (formula.map Clause.encodedSize).sum := rfl

/-- Every total assignment has exactly the same evaluation after padding. -/
theorem eval_normalizeThree (formula : Formula Nat) (assignment : Assignment Nat) :
    formula.normalizeThree.eval assignment = formula.eval assignment := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      simp only [normalizeThree, List.flatMap_cons, eval_append, eval_cons] at ih ⊢
      rw [Clause.eval_normalizeThree, ih]

theorem satisfiable_normalizeThree (formula : Formula Nat) :
    formula.normalizeThree.Satisfiable ↔ formula.Satisfiable := by
  simp only [satisfiable_iff_exists_eval, eval_normalizeThree]

/-- Long clauses remain long; short and empty clauses become exact triples. -/
theorem exactWidth_normalizeThree (formula : Formula Nat) :
    formula.normalizeThree.ExactWidth 3 ↔ formula.AtMostWidth 3 := by
  constructor
  · intro exactWidth clause occurs
    apply (Clause.exactWidth_normalizeThree clause).mp
    intro padded member
    exact exactWidth padded (List.mem_flatMap.mpr ⟨clause, occurs, member⟩)
  · intro atMost padded member
    obtain ⟨clause, occurs, paddedOccurs⟩ := List.mem_flatMap.mp member
    exact (Clause.exactWidth_normalizeThree clause).mpr (atMost clause occurs)
      padded paddedOccurs

theorem normalizeThree_length_le (formula : Formula Nat) :
    formula.normalizeThree.length ≤ 2 * formula.length := by
  induction formula with
  | nil => simp [normalizeThree]
  | cons clause formula ih =>
      have hc := clause.normalizeThree_length_le
      simp only [normalizeThree, List.flatMap_cons, List.length_append,
        List.length_cons] at ih ⊢
      omega

theorem normalizeThree_payloadSize_le (formula : Formula Nat) :
    (formula.normalizeThree.map Clause.encodedSize).sum ≤
      22 * (formula.map Clause.encodedSize).sum := by
  induction formula with
  | nil => simp [normalizeThree]
  | cons clause formula ih =>
      have hc := clause.normalizeThree_payloadSize_le
      simp only [normalizeThree, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- A linear bound in actual encoded formula bits, including all length frames.
This is an output-size result, not a polynomial-time machine witness. -/
theorem normalizeThree_encode_length_le (formula : Formula Nat) :
    formula.normalizeThree.encode.length ≤ 26 * formula.encodedSize + 1 := by
  have count : formula.length ≤ (formula.map Clause.encodedSize).sum := by
    induction formula with
    | nil => simp
    | cons clause formula ih =>
        have hc := clause.encodedSize_pos
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  have hlen := formula.normalizeThree_length_le
  have hpayload := formula.normalizeThree_payloadSize_le
  have hheader := BinaryNatLists.natWireSize_le_two_mul_add_one
    formula.normalizeThree.length
  rw [encode_length, encodedSize_eq, encodedSize_eq]
  omega

end Formula

/-- The convention allowing clauses of width zero, one, two, or three. -/
def AtMostThreeSAT : Language (Formula Nat) :=
  fun formula => formula.AtMostWidth 3 ∧ formula.Satisfiable

/-- The at-most-three convention uses the same lossless binary formula encoding. -/
def encodedAtMostThreeSAT : EncodedLanguage (Formula Nat) where
  encoding := Formula.finEncoding
  accepts := AtMostThreeSAT

/-- Correctness of the convention change, with no runtime claim. -/
theorem atMostThreeSAT_iff_exactThreeSAT_normalize (formula : Formula Nat) :
    AtMostThreeSAT formula ↔ ExactThreeSAT formula.normalizeThree := by
  simp only [AtMostThreeSAT, ExactThreeSAT, ExactKSAT,
    Formula.exactWidth_normalizeThree, Formula.satisfiable_normalizeThree]
  simp

/-- Semantic many-one reduction; polynomial-time implementation remains separate. -/
def atMostThreeToExactThree : ManyOneReduction AtMostThreeSAT ExactThreeSAT where
  map := Formula.normalizeThree
  correct := atMostThreeSAT_iff_exactThreeSAT_normalize

end LeanNPHardness.CNF
