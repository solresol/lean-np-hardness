import LeanNPHardness.MaxCutSpec
import LeanNPHardness.ExactThreeVerifySpec

/-!
# The Max-Cut verifier: semantics

A certificate claims a colour bit for each endpoint occurrence, two bits
per edge (missing bits read as `false`). The verifier accepts when the
claims are consistent (no vertex is claimed with both colours) and the
number of edges whose claimed endpoint colours differ reaches the
threshold (`verifyMC`). Occurrences are encoded as literals (`occLit`), so
consistency is the `consistent` check of the exact 3-SAT verifier.
`verifyMC_sound` and `verifyMC_complete` characterize `MaxCutLang`.
-/

namespace LeanNPHardness.MaxCutVerify

open CNF MaxCut ExactThreeVerify

/-- A colour claim as a literal: negative for colour `true`. -/
def occLit (u : ℕ) (b : Bool) : Literal ℕ := if b then .negative u else .positive u

/-- The colour claims of all endpoint occurrences. -/
def occs : List Edge → List Bool → List (Literal ℕ)
  | [], _ => []
  | e :: G, w => occLit e.1 (w.getD 0 false) :: occLit e.2 (w.getD 1 false) :: occs G (w.drop 2)

/-- The number of edges whose claimed endpoint colours differ. -/
def claimedCut : List Edge → List Bool → ℕ
  | [], _ => 0
  | _ :: G, w => (if w.getD 0 false != w.getD 1 false then 1 else 0) + claimedCut G (w.drop 2)

/-- The Max-Cut verifier. -/
def verifyMC (q : (List Edge × ℕ) × List Bool) : Bool :=
  consistent (occs q.1.1 q.2) && decide (q.1.2 ≤ claimedCut q.1.1 q.2)

theorem occLit_var (u : ℕ) (b : Bool) : (occLit u b).var = u := by cases b <;> rfl
theorem occLit_isNeg (u : ℕ) (b : Bool) : isNeg (occLit u b) = b := by cases b <;> rfl

/-- The colouring read off consistent claims. -/
def colourOfClaims (L : List (Literal ℕ)) (u : ℕ) : Bool := L.any (· == .negative u)

theorem claim_eq (L : List (Literal ℕ)) (hc : consistent L = true) (u : ℕ) (b : Bool)
    (h : occLit u b ∈ L) : colourOfClaims L u = b := by
  have hcons := (consistent_iff L).mp hc
  cases b with
  | true =>
      exact List.any_eq_true.mpr ⟨_, h, by simp [occLit]⟩
  | false =>
      simp only [colourOfClaims, occLit, Bool.false_eq_true, if_false] at h ⊢
      rw [Bool.eq_false_iff]
      intro hany
      obtain ⟨l', hl', he⟩ := List.any_eq_true.mp hany
      have he' : l' = .negative u := by simpa using he
      subst he'
      have := hcons _ h _ hl'
      simp [conflict, isNeg, Literal.var] at this

theorem cut_of_claims (G : List Edge) : ∀ (w : List Bool) (L : List (Literal ℕ)),
    consistent L = true → (∀ l ∈ occs G w, l ∈ L) →
    cut (colourOfClaims L) G = claimedCut G w := by
  induction G with
  | nil => intro _ _ _ _; rfl
  | cons e G ih =>
      intro w L hc hsub
      have h1 := claim_eq L hc e.1 (w.getD 0 false) (hsub _ (by simp [occs]))
      have h2 := claim_eq L hc e.2 (w.getD 1 false) (hsub _ (by simp [occs]))
      rw [cut_cons, ih (w.drop 2) L hc (fun l hl => hsub l (by simp [occs, hl])), claimedCut, h1, h2]

theorem verifyMC_sound (p : List Edge × ℕ) (w : List Bool) (h : verifyMC (p, w) = true) :
    MaxCutLang p := by
  simp only [verifyMC, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨colourOfClaims (occs p.1 w), ?_⟩
  rw [cut_of_claims p.1 w _ h.1 (fun l hl => hl)]
  exact h.2

/-- The certificate of a colouring. -/
def witnessMC (s : ℕ → Bool) (G : List Edge) : List Bool := G.flatMap fun e => [s e.1, s e.2]

theorem occs_witness (s : ℕ → Bool) (G : List Edge) :
    ∀ l ∈ occs G (witnessMC s G), ∃ u, l = occLit u (s u) := by
  induction G with
  | nil => simp [occs]
  | cons e G ih =>
      intro l hl
      simp only [witnessMC, List.flatMap_cons, occs, List.cons_append, List.getD_cons_zero,
        List.getD_cons_succ, List.nil_append, List.drop_succ_cons, List.drop_zero,
        List.mem_cons] at hl
      rcases hl with rfl | rfl | h
      · exact ⟨e.1, rfl⟩
      · exact ⟨e.2, rfl⟩
      · exact ih l h

theorem claimedCut_witness (s : ℕ → Bool) (G : List Edge) :
    claimedCut G (witnessMC s G) = cut s G := by
  induction G with
  | nil => rfl
  | cons e G ih =>
      simp only [witnessMC, List.flatMap_cons, claimedCut, List.cons_append, List.getD_cons_zero,
        List.getD_cons_succ, List.nil_append, List.drop_succ_cons, List.drop_zero, cut_cons]
      rw [show G.flatMap (fun e => [s e.1, s e.2]) = witnessMC s G from rfl, ih]

theorem verifyMC_complete (p : List Edge × ℕ) (h : MaxCutLang p) :
    ∃ w : List Bool, w.length = 2 * p.1.length ∧ verifyMC (p, w) = true := by
  obtain ⟨s, hs⟩ := h
  refine ⟨witnessMC s p.1, ?_, ?_⟩
  · simp [witnessMC, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  · simp only [verifyMC, Bool.and_eq_true, decide_eq_true_eq, claimedCut_witness]
    refine ⟨(consistent_iff _).mpr fun l hl l' hl' => ?_, hs⟩
    obtain ⟨u, rfl⟩ := occs_witness s p.1 l hl
    obtain ⟨u', rfl⟩ := occs_witness s p.1 l' hl'
    simp only [conflict, occLit_var, occLit_isNeg, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      bne_eq_false_iff_eq]
    by_cases hu : u = u'
    · subst hu; exact Or.inr rfl
    · exact Or.inl hu

end LeanNPHardness.MaxCutVerify
