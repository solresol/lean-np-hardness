import LeanNPHardness.CNFSplitting
import Mathlib.Tactic.Ring

/-!
# A streaming reduction from SAT to exact 3-SAT

Original variables are doubled; fresh variables are odd. A clause
`l₁ ∨ … ∨ lⱼ` with fresh base `v` and `yₖ = v + 2k` becomes

* `¬y₀ ∨ ¬y₀ ∨ ¬y₀` and `y₀ ∨ ¬y₁ ∨ y₀` (so `y₀` and `y₁` are false),
* `lᵢ ∨ ¬yᵢ₊₁ ∨ yᵢ` for each literal (`yᵢ₊₁ → yᵢ ∨ lᵢ`),
* `yⱼ₊₁ ∨ yⱼ₊₁ ∨ yⱼ₊₁`,

and the next clause starts at `v + 2(j + 2)`. A satisfiable two-clause tail
closes the formula. Every output clause has exactly three literal
occurrences (`exactWidth_chainThree`), and satisfiability is preserved
(`satisfiable_chainThree`). Unlike `Formula.toExactThree`, every clause is
produced by the same per-literal pattern, so the transformation can be
emitted symbol by symbol from the unary encoding.
-/

namespace LeanNPHardness.CNF.Chain

open CNF

/-- The literal clauses of a chain whose previous fresh variable is `p`. -/
def chain (p : ℕ) : Clause ℕ → Formula ℕ
  | [] => []
  | l :: ls => [l.double, .negative (p + 2), .positive p] :: chain (p + 2) ls

/-- The clauses produced for one input clause with fresh base `v`. -/
def block (v : ℕ) (c : Clause ℕ) : Formula ℕ :=
  [.negative v, .negative v, .negative v] :: [.positive v, .negative (v + 2), .positive v] ::
    (chain (v + 2) c ++
      [[.positive (v + 2 * (c.length + 1)), .positive (v + 2 * (c.length + 1)),
        .positive (v + 2 * (c.length + 1))]])

/-- The closing clauses with fresh base `v`. -/
def tail (v : ℕ) : Formula ℕ :=
  [[.negative v, .negative v, .negative v], [.positive v, .negative (v + 2), .positive v]]

/-- The output from fresh base `v`. -/
def out (v : ℕ) : Formula ℕ → Formula ℕ
  | [] => tail v
  | c :: F => block v c ++ out (v + 2 * (c.length + 2)) F

/-- The streaming exact-3-SAT transformation. -/
def chainThree (F : Formula ℕ) : Formula ℕ := out 1 F

/-! ### Width -/

theorem chain_width (p : ℕ) (c : Clause ℕ) : ∀ cl ∈ chain p c, cl.length = 3 := by
  induction c generalizing p with
  | nil => simp [chain]
  | cons l ls ih =>
      intro cl hcl
      simp only [chain, List.mem_cons] at hcl
      rcases hcl with rfl | h
      · rfl
      · exact ih _ cl h

theorem out_width (v : ℕ) (F : Formula ℕ) : ∀ cl ∈ out v F, cl.length = 3 := by
  induction F generalizing v with
  | nil =>
      intro cl hcl
      simp only [out, tail, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> rfl
  | cons c F ih =>
      intro cl hcl
      simp only [out, block, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with (rfl | rfl | h | rfl) | h
      · rfl
      · rfl
      · exact chain_width _ c cl h
      · rfl
      · exact ih _ cl h

theorem exactWidth_chainThree (F : Formula ℕ) : (chainThree F).ExactWidth 3 :=
  out_width 1 F

/-! ### Soundness -/

theorem chain_false (A : Assignment ℕ) (c : Clause ℕ) : ∀ p, A p = false →
    (∀ cl ∈ chain p c, cl.eval A = true) → c.eval (fun x => A (2 * x)) = false →
    A (p + 2 * c.length) = false := by
  induction c with
  | nil => intro p hp _ _; simpa using hp
  | cons l ls ih =>
      intro p hp hcl hc
      simp only [Clause.eval_cons, Bool.or_eq_false_iff] at hc
      have h1 := hcl _ (List.mem_cons_self ..)
      simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_double, hc.1,
        Literal.eval_positive, Literal.eval_negative, hp, Bool.or_false, Bool.false_or,
        Bool.not_eq_true'] at h1
      have := ih (p + 2) h1 (fun cl h => hcl cl (List.mem_cons_of_mem _ h)) hc.2
      rw [List.length_cons]
      convert this using 2
      ring

theorem block_sound (A : Assignment ℕ) (v : ℕ) (c : Clause ℕ)
    (h : ∀ cl ∈ block v c, cl.eval A = true) : c.eval (fun x => A (2 * x)) = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  have h0 := h [.negative v, .negative v, .negative v] (by simp [block])
  have h1 := h [.positive v, .negative (v + 2), .positive v] (by simp [block])
  have hlast := h [.positive (v + 2 * (c.length + 1)), .positive (v + 2 * (c.length + 1)),
    .positive (v + 2 * (c.length + 1))] (by simp [block])
  simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_positive, Literal.eval_negative, Bool.or_false, Bool.or_self,
    Bool.not_eq_true'] at h0 h1 hlast
  rw [h0] at h1
  simp only [Bool.false_or, Bool.or_false, Bool.not_eq_true'] at h1
  have := chain_false A c (v + 2) h1 (fun cl hcl => h cl (by simp [block, hcl])) hc
  rw [show v + 2 + 2 * c.length = v + 2 * (c.length + 1) by ring] at this
  rw [this] at hlast
  exact Bool.false_ne_true hlast

theorem out_sound (A : Assignment ℕ) (F : Formula ℕ) : ∀ v, (out v F).eval A = true →
    F.eval (fun x => A (2 * x)) = true := by
  induction F with
  | nil => intro _ _; rfl
  | cons c F ih =>
      intro v h
      simp only [out, Formula.eval_append, Bool.and_eq_true] at h
      simp only [Formula.eval_cons, Bool.and_eq_true]
      refine ⟨block_sound A v c fun cl hcl => ?_, ih _ h.2⟩
      have := h.1
      simp only [Formula.eval, List.all_eq_true] at this
      exact this cl hcl

/-! ### Completeness -/

theorem chain_true (A : Assignment ℕ) (a : Assignment ℕ) (hA : ∀ x, A (2 * x) = a x)
    (c : Clause ℕ) : ∀ (p : ℕ) (b : Bool),
    (∀ i ≤ c.length, A (p + 2 * i) = (b || (c.take i).any (Literal.eval a))) →
    ∀ cl ∈ chain p c, cl.eval A = true := by
  have hd : ∀ l : Literal ℕ, l.double.eval A = l.eval a := by
    intro l
    rw [Literal.eval_double]
    simp only [hA]
  induction c with
  | nil => intro _ _ _ cl h; simp [chain] at h
  | cons l ls ih =>
      intro p b hp cl hcl
      simp only [chain, List.mem_cons] at hcl
      rcases hcl with rfl | h
      · have h0 := hp 0 (by simp)
        have h1 := hp 1 (by simp)
        simp only [Nat.mul_zero, Nat.add_zero, List.take_zero, List.any_nil, Bool.or_false] at h0
        simp only [Nat.mul_one, List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil,
          Bool.or_false] at h1
        simp only [Clause.eval_cons, Clause.eval_nil, hd, Literal.eval_positive,
          Literal.eval_negative, h0, h1, Bool.or_false]
        cases b <;> cases l.eval a <;> rfl
      · refine ih (p + 2) (b || l.eval a) (fun i hi => ?_) cl h
        have := hp (i + 1) (by simp; omega)
        rw [show p + 2 + 2 * i = p + 2 * (i + 1) by ring, this]
        simp [List.take_succ_cons, Bool.or_assoc]

/-- The fresh-variable values: a variable of a block is true when some
earlier literal of its clause is true. -/
def ext (a : Assignment ℕ) : ℕ → Formula ℕ → ℕ → Bool
  | _, [], _ => false
  | v, c :: F, u =>
      if u < v + 2 * (c.length + 2) then (c.take ((u - v) / 2 - 1)).any (Literal.eval a)
      else ext a (v + 2 * (c.length + 2)) F u

theorem out_complete (a : Assignment ℕ) (F : Formula ℕ) (hF : F.eval a = true) :
    ∀ (v : ℕ) (A : Assignment ℕ), v % 2 = 1 → (∀ x, A (2 * x) = a x) →
      (∀ u, v ≤ u → u % 2 = 1 → A u = ext a v F u) → (out v F).eval A = true := by
  induction F with
  | nil =>
      intro v A hodd _ hv
      have h0 := hv v le_rfl hodd
      have h2 := hv (v + 2) (by omega) (by omega)
      simp only [ext] at h0 h2
      simp [out, tail, Formula.eval, Clause.eval, Literal.eval_positive, Literal.eval_negative, h0, h2]
  | cons c F ih =>
      intro v A hodd hA hv
      simp only [Formula.eval_cons, Bool.and_eq_true] at hF
      have hval : ∀ k ≤ c.length + 1, A (v + 2 * k) = (c.take (k - 1)).any (Literal.eval a) := by
        intro k hk
        rw [hv _ (by omega) (by omega), ext, if_pos (by omega)]
        congr 2
        rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by norm_num)]
      have hy0 := hval 0 (by omega)
      have hy1 := hval 1 (by omega)
      have hyl := hval (c.length + 1) le_rfl
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_sub, List.take_zero, List.any_nil,
        Nat.mul_one, Nat.sub_self] at hy0 hy1
      simp only [Nat.add_sub_cancel, List.take_length] at hyl
      have hchain := chain_true A a hA c (v + 2) false (fun i hi => by
        rw [show v + 2 + 2 * i = v + 2 * (i + 1) by ring, hval (i + 1) (by omega)]
        simp)
      simp only [out, Formula.eval_append, Bool.and_eq_true]
      constructor
      · simp only [block, Formula.eval, List.all_cons, List.all_append, List.all_nil, Bool.and_true,
          Bool.and_eq_true, List.all_eq_true]
        refine ⟨?_, ?_, hchain, ?_⟩
        · simp [Clause.eval, Literal.eval_negative, hy0]
        · simp [Clause.eval, Literal.eval_positive, Literal.eval_negative, hy0, hy1]
        · simp only [Clause.eval, List.any_cons, List.any_nil, Literal.eval_positive, hyl, Bool.or_false,
            Bool.or_self]
          exact hF.1
      · refine ih hF.2 _ A (by omega) hA fun u hu hu2 => ?_
        rw [hv u (by omega) hu2, ext, if_neg (by omega)]

/-- The chain transformation preserves satisfiability. -/
theorem satisfiable_chainThree (F : Formula ℕ) : (chainThree F).Satisfiable ↔ F.Satisfiable := by
  simp only [Formula.satisfiable_iff_exists_eval, chainThree]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨_, out_sound A F 1 hA⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun u => if u % 2 = 0 then a (u / 2) else ext a 1 F u,
      out_complete a F ha 1 _ rfl (fun x => ?_) (fun u _ hu => ?_)⟩
    · simp
    · simp [show u % 2 ≠ 0 by omega]

end LeanNPHardness.CNF.Chain
