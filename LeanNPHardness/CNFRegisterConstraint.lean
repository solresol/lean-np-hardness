import LeanNPHardness.CNFConstraint

/-!
# Register-valued constraints over Boolean variables

A register of width `w` is a block of `w` consecutive Boolean variables read
as a little-endian binary natural. A relation on register values becomes a
CNF constraint on the underlying bits through `relationCNF`.
`eval_registerCNF` identifies its value with the relation applied to the
registers read from the assignment. These are semantic results; no
machine-runtime claim is made.
-/

namespace LeanNPHardness.CNF.Constraint

/-- Little-endian bits of a natural, truncated or zero-padded to a width. -/
def natToBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, m => (m % 2 == 1) :: natToBits w (m / 2)

/-- The natural represented by little-endian bits. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- Bit `b` of a natural. -/
def natBit (m b : ℕ) : Bool := (m / 2 ^ b) % 2 == 1

@[simp]
theorem natToBits_length (w m : ℕ) : (natToBits w m).length = w := by
  induction w generalizing m with
  | zero => rfl
  | succ w ih => simp [natToBits, ih]

theorem bitsToNat_natToBits (w : ℕ) : ∀ m, m < 2 ^ w → bitsToNat (natToBits w m) = m := by
  induction w with
  | zero =>
      intro m hm
      simp only [Nat.pow_zero, Nat.lt_one_iff] at hm
      simp [natToBits, bitsToNat, hm]
  | succ w ih =>
      intro m hm
      have hdiv : m / 2 < 2 ^ w := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [Nat.pow_succ, Nat.mul_comm] using hm
      simp only [natToBits, bitsToNat, ih (m / 2) hdiv]
      have := Nat.mod_add_div m 2
      have hm2 : m % 2 < 2 := Nat.mod_lt m (by omega)
      by_cases h : m % 2 = 1
      · simp [h]; omega
      · have h0 : m % 2 = 0 := by omega
        simp [h0]; omega

theorem bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
      simp only [bitsToNat, List.length_cons, Nat.pow_succ]
      cases b <;> simp <;> omega

@[simp]
theorem natBit_zero (m : ℕ) : natBit m 0 = (m % 2 == 1) := by
  simp [natBit]

theorem natBit_succ (m b : ℕ) : natBit m (b + 1) = natBit (m / 2) b := by
  simp [natBit, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem natToBits_eq_map_natBit (w : ℕ) : ∀ m, natToBits w m = (List.range w).map (natBit m) := by
  induction w with
  | zero => intro m; rfl
  | succ w ih =>
      intro m
      rw [List.range_succ_eq_map]
      simp only [natToBits, List.map_cons, List.map_map, natBit_zero, List.cons.injEq, true_and]
      rw [ih (m / 2)]
      apply List.map_congr_left
      intro b _
      simp [Function.comp, natBit_succ]

/-- The variables holding register `g` of width `w`, least significant first. -/
def registerSlots (w g : ℕ) : List ℕ :=
  (List.range w).map fun b => g * w + b

@[simp]
theorem registerSlots_length (w g : ℕ) : (registerSlots w g).length = w := by
  simp [registerSlots]

/-- Read a register from an assignment. -/
def readRegister (w : ℕ) (a : Assignment ℕ) (g : ℕ) : ℕ :=
  bitsToNat ((registerSlots w g).map a)

theorem readRegister_lt (w : ℕ) (a : Assignment ℕ) (g : ℕ) :
    readRegister w a g < 2 ^ w := by
  have := bitsToNat_lt ((registerSlots w g).map a)
  simpa [readRegister] using this

/-- An assignment whose register `g` holds the bits of `f g` reads back `f g`
whenever that value fits the width. The bit at slot `g * w + b` is bit `b`. -/
theorem readRegister_of_natBit (w : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (a : Assignment ℕ) (ha : ∀ n, a n = natBit (f (n / w)) (n % w)) (g : ℕ)
    (hg : f g < 2 ^ w) :
    readRegister w a g = f g := by
  have hmap : (registerSlots w g).map a = natToBits w (f g) := by
    rw [natToBits_eq_map_natBit, registerSlots, List.map_map]
    apply List.map_congr_left
    intro b hb
    have hb' : b < w := List.mem_range.mp hb
    simp only [Function.comp, ha]
    have hdiv : (g * w + b) / w = g := by
      rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hb', Nat.add_zero]
    have hmod : (g * w + b) % w = b := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
    rw [hdiv, hmod]
  rw [readRegister, hmap, bitsToNat_natToBits w (f g) hg]

/-- Split a list into a fixed number of consecutive chunks of a given width. -/
def chunks (w : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | n + 1, bits => bits.take w :: chunks w n (bits.drop w)

theorem chunks_flatMap {ι : Type*} (w : ℕ) (items : List ι) (f : ι → List Bool)
    (hf : ∀ i, (f i).length = w) :
    chunks w items.length (items.flatMap f) = items.map f := by
  induction items with
  | nil => rfl
  | cons i items ih =>
      simp only [List.flatMap_cons, List.length_cons, chunks, List.map_cons]
      rw [List.take_append_of_le_length (by rw [hf]), List.take_of_length_le (by rw [hf]),
        List.drop_append_of_le_length (by rw [hf]), List.drop_of_length_le (by rw [hf]),
        List.nil_append, ih]

/-- A relation on register values as a CNF constraint on their bits. -/
def registerCNF (w : ℕ) (groups : List ℕ) (R : List ℕ → Bool) : Formula ℕ :=
  relationCNF (groups.flatMap (registerSlots w)) fun bits =>
    R ((chunks w groups.length bits).map bitsToNat)

@[simp]
theorem eval_registerCNF (w : ℕ) (a : Assignment ℕ) (groups : List ℕ)
    (R : List ℕ → Bool) :
    Formula.eval a (registerCNF w groups R) = R (groups.map (readRegister w a)) := by
  rw [registerCNF, eval_relationCNF, List.map_flatMap]
  rw [chunks_flatMap w groups (fun g => (registerSlots w g).map a) (by simp)]
  simp only [List.map_map]
  rfl

theorem eval_registerCNF_eq_true_iff (w : ℕ) (a : Assignment ℕ) (groups : List ℕ)
    (R : List ℕ → Bool) :
    Formula.eval a (registerCNF w groups R) = true ↔
      R (groups.map (readRegister w a)) = true := by
  rw [eval_registerCNF]

/-- Force one register to hold a given value. -/
def fixRegister (w g m : ℕ) : Formula ℕ :=
  registerCNF w [g] fun values => values == [m]

@[simp]
theorem eval_fixRegister_eq_true_iff (w : ℕ) (a : Assignment ℕ) (g m : ℕ) :
    Formula.eval a (fixRegister w g m) = true ↔ readRegister w a g = m := by
  simp [fixRegister]

theorem registerCNF_length_le (w : ℕ) (groups : List ℕ) (R : List ℕ → Bool) :
    (registerCNF w groups R).length ≤ 2 ^ (w * groups.length) := by
  have := relationCNF_length_le (groups.flatMap (registerSlots w)) fun bits =>
    R ((chunks w groups.length bits).map bitsToNat)
  simpa [registerCNF, List.length_flatMap, Nat.mul_comm] using this

theorem registerCNF_clause_length (w : ℕ) (groups : List ℕ) (R : List ℕ → Bool)
    (clause : Clause ℕ) (h : clause ∈ registerCNF w groups R) :
    clause.length = w * groups.length := by
  have := relationCNF_clause_length _ _ clause h
  simpa [List.length_flatMap, Nat.mul_comm] using this

theorem registerCNF_var_lt (w : ℕ) (groups : List ℕ) (R : List ℕ → Bool)
    (bound : ℕ) (hgroups : ∀ g ∈ groups, g < bound)
    (clause : Clause ℕ) (h : clause ∈ registerCNF w groups R)
    (literal : Literal ℕ) (hl : literal ∈ clause) :
    literal.var < bound * w := by
  have hmem := relationCNF_var_mem _ _ clause h literal hl
  simp only [List.mem_flatMap, registerSlots, List.mem_map, List.mem_range] at hmem
  obtain ⟨g, hg, b, hb, hvar⟩ := hmem
  have := hgroups g hg
  rw [← hvar]
  calc g * w + b < g * w + w := by omega
    _ = (g + 1) * w := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ bound * w := Nat.mul_le_mul_right w this

end LeanNPHardness.CNF.Constraint
