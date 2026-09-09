import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Interval.Finset.Nat

/-!
Bounded number-theory components extracted from phd-thesis-lean at 84be78d.
All enumeration, trial-division and prime-selection runtime bounds use the
explicit unary/padded input encodings; no binary-input polynomial bound is
asserted for these algorithms.
-/

namespace LeanNPHardness.BoundedPrime


/-- The finite interval scanned for a prime strictly above `q`.

For positive `q`, Bertrand's postulate guarantees that this set is nonempty.
Keeping the scan as an executable `Finset` separates the prime-selection
algorithm from its later bit-level running-time proof. -/
def primeCandidates (q : ℕ) : Finset ℕ :=
  (Finset.Icc (q + 1) (2 * q)).filter Nat.Prime

@[simp]
theorem mem_primeCandidates_iff (q p : ℕ) :
    p ∈ primeCandidates q ↔ p.Prime ∧ q < p ∧ p ≤ 2 * q := by
  simp [primeCandidates, Nat.lt_iff_add_one_le, and_comm]

theorem primeCandidates_nonempty {q : ℕ} (hq : q ≠ 0) :
    (primeCandidates q).Nonempty := by
  obtain ⟨p, hp, hqp, hpq⟩ :=
    Nat.exists_prime_lt_and_le_two_mul q hq
  exact ⟨p, (mem_primeCandidates_iff q p).2 ⟨hp, hqp, hpq⟩⟩

/-- The least prime strictly above the bound, with explicit zero/one conventions.

At `q = 0` the selector returns `2`. At positive `q` it scans the Bertrand
interval and returns its least prime. The separate machine module proves a
polynomial-time unary-bound implementation. Consumers must account for
producing the unary bound from their own encoded input. -/
def selectPrimeAbove (q : ℕ) : ℕ :=
  if hq : q = 0 then
    2
  else
    (primeCandidates q).min' (primeCandidates_nonempty hq)

@[simp]
theorem selectPrimeAbove_zero : selectPrimeAbove 0 = 2 := by
  simp [selectPrimeAbove]

theorem selectPrimeAbove_mem_primeCandidates {q : ℕ} (hq : q ≠ 0) :
    selectPrimeAbove q ∈ primeCandidates q := by
  rw [selectPrimeAbove, dif_neg hq]
  exact Finset.min'_mem _ _

theorem selectPrimeAbove_prime (q : ℕ) :
    (selectPrimeAbove q).Prime := by
  by_cases hq : q = 0
  · subst q
    norm_num
  · exact ((mem_primeCandidates_iff q (selectPrimeAbove q)).1
      (selectPrimeAbove_mem_primeCandidates hq)).1

theorem lt_selectPrimeAbove (q : ℕ) :
    q < selectPrimeAbove q := by
  by_cases hq : q = 0
  · subst q
    norm_num
  · exact ((mem_primeCandidates_iff q (selectPrimeAbove q)).1
      (selectPrimeAbove_mem_primeCandidates hq)).2.1

theorem selectPrimeAbove_le_two_mul {q : ℕ} (hq : q ≠ 0) :
    selectPrimeAbove q ≤ 2 * q :=
  ((mem_primeCandidates_iff q (selectPrimeAbove q)).1
    (selectPrimeAbove_mem_primeCandidates hq)).2.2

/-- For the nontrivial `q > 1` branch, the selected prime is strictly below
`2q`; equality would make it the product of two non-units. -/
theorem selectPrimeAbove_lt_two_mul {q : ℕ} (hq : 1 < q) :
    selectPrimeAbove q < 2 * q := by
  have hle := selectPrimeAbove_le_two_mul (by omega : q ≠ 0)
  have hne : selectPrimeAbove q ≠ 2 * q := by
    intro heq
    have hp := selectPrimeAbove_prime q
    rw [heq] at hp
    exact Nat.not_prime_mul (by omega) (by omega) hp
  omega

@[simp]
theorem selectPrimeAbove_one : selectPrimeAbove 1 = 2 := by
  have hgt := lt_selectPrimeAbove 1
  have hle := selectPrimeAbove_le_two_mul (by norm_num : (1 : ℕ) ≠ 0)
  omega


end LeanNPHardness.BoundedPrime
