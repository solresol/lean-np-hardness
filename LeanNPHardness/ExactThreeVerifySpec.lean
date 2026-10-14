import LeanNPHardness.CNFEncoding
import LeanNPHardness.CNFCertificate

/-!
# The exact 3-SAT verifier: semantics

A certificate assigns two bits to each clause, selecting the literal to be
made true (`idx`): `true, _` selects literal 0, `false, true` literal 1 and
`false, false` literal 2; missing bits read as `false`. The verifier
accepts when every clause has exactly three literal occurrences and no two
selected literals are complementary (`verify`).

`verify_sound` and `verify_complete` prove that `verify` characterizes
`ExactThreeSAT`, with certificates of `2 * F.length` bits, at most twice the
binary input length (`witness_length_le`).
-/

namespace LeanNPHardness.ExactThreeVerify

open CNF

/-- Polarity: `true` for a negative literal. -/
def isNeg : Literal ℕ → Bool
  | .positive _ => false
  | .negative _ => true

/-- Two literals on the same variable with opposite polarities. -/
def conflict (l l' : Literal ℕ) : Bool := l.var == l'.var && isNeg l != isNeg l'

/-- The selected position. -/
def idx (b0 b1 : Bool) : ℕ := if b0 then 0 else if b1 then 1 else 2

theorem idx_lt (b0 b1 : Bool) : idx b0 b1 < 3 := by
  unfold idx; split_ifs <;> omega

/-- The selected literal of a clause. -/
def chooseLit (c : Clause ℕ) (b0 b1 : Bool) : Literal ℕ := c.getD (idx b0 b1) (.positive 0)

/-- The selected literals of all clauses, reading two bits per clause. -/
def chosen : Formula ℕ → List Bool → List (Literal ℕ)
  | [], _ => []
  | c :: F, w => chooseLit c (w.getD 0 false) (w.getD 1 false) :: chosen F (w.drop 2)

/-- Every clause has exactly three literal occurrences. -/
def widthOk (F : Formula ℕ) : Bool := F.all fun c => c.length == 3

/-- No two selected literals are complementary. -/
def consistent (L : List (Literal ℕ)) : Bool := L.all fun l => L.all fun l' => !conflict l l'

/-- The verifier. -/
def verify (p : Formula ℕ × List Bool) : Bool := widthOk p.1 && consistent (chosen p.1 p.2)

theorem widthOk_iff (F : Formula ℕ) : widthOk F = true ↔ F.ExactWidth 3 := by
  simp [widthOk, Formula.ExactWidth]

theorem chooseLit_mem (c : Clause ℕ) (hc : c.length = 3) (b0 b1 : Bool) : chooseLit c b0 b1 ∈ c := by
  unfold chooseLit
  rw [List.getD_eq_getElem _ _ (by rw [hc]; exact idx_lt b0 b1)]
  exact List.getElem_mem _

theorem chosen_spec (F : Formula ℕ) (w : List Bool) :
    ∀ c ∈ F, c.length = 3 → ∃ l ∈ chosen F w, l ∈ c := by
  induction F generalizing w with
  | nil => simp
  | cons d F ih =>
      intro c hc h3
      rcases List.mem_cons.mp hc with rfl | h
      · exact ⟨_, List.mem_cons_self .., chooseLit_mem c h3 _ _⟩
      · obtain ⟨l, hl, hlc⟩ := ih (w.drop 2) c h h3
        exact ⟨l, List.mem_cons_of_mem _ hl, hlc⟩

theorem consistent_iff (L : List (Literal ℕ)) :
    consistent L = true ↔ ∀ l ∈ L, ∀ l' ∈ L, conflict l l' = false := by
  simp [consistent]

/-- Accepted certificates witness exact 3-SAT. -/
theorem verify_sound (F : Formula ℕ) (w : List Bool) (h : verify (F, w) = true) :
    ExactThreeSAT F := by
  simp only [verify, Bool.and_eq_true] at h
  have hw := (widthOk_iff F).mp h.1
  have hcons := (consistent_iff _).mp h.2
  refine ⟨by decide, hw, ?_⟩
  refine ⟨fun v => (chosen F w).any (· == .positive v), ?_⟩
  intro c hc
  obtain ⟨l, hl, hlc⟩ := chosen_spec F w c hc (hw c hc)
  refine ⟨l, hlc, ?_⟩
  cases l with
  | positive v =>
      show (chosen F w).any (· == .positive v) = true
      exact List.any_eq_true.mpr ⟨_, hl, by simp⟩
  | negative v =>
      show (chosen F w).any (· == .positive v) = false
      rw [Bool.eq_false_iff]
      intro hany
      obtain ⟨l', hl', he⟩ := List.any_eq_true.mp hany
      have he' : l' = .positive v := by simpa using he
      subst he'
      have := hcons _ hl _ hl'
      simp [conflict, isNeg, Literal.var] at this

/-- The two certificate bits selecting the first true literal of a clause. -/
def pickBits (a : Assignment ℕ) (c : Clause ℕ) : List Bool :=
  match c with
  | [l0, l1, _] => if l0.eval a then [true, false] else if l1.eval a then [false, true] else [false, false]
  | _ => [false, false]

/-- The certificate built from a satisfying assignment. -/
def witness (a : Assignment ℕ) (F : Formula ℕ) : List Bool := F.flatMap (pickBits a)

theorem pickBits_length (a : Assignment ℕ) (c : Clause ℕ) : (pickBits a c).length = 2 := by
  unfold pickBits; split
  · split_ifs <;> rfl
  · rfl

theorem chosen_witness (a : Assignment ℕ) (F : Formula ℕ) (hw : F.ExactWidth 3)
    (hs : ∀ c ∈ F, c.Satisfied a) : ∀ l ∈ chosen F (witness a F), l.eval a = true := by
  induction F with
  | nil => simp [chosen]
  | cons c F ih =>
      intro l hl
      have hc3 := hw c (List.mem_cons_self ..)
      have hrest : chosen (c :: F) (witness a (c :: F)) =
          chooseLit c ((pickBits a c).getD 0 false) ((pickBits a c).getD 1 false) ::
            chosen F (witness a F) := by
        simp only [witness, List.flatMap_cons, chosen]
        have h2 := pickBits_length a c
        congr 1
        · congr 1
          · rw [List.getD_append _ _ _ _ (by omega)]
          · rw [List.getD_append _ _ _ _ (by omega)]
        · rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
            List.nil_append]
      rw [hrest] at hl
      rcases List.mem_cons.mp hl with rfl | h
      · obtain ⟨l', hl'c, hl'⟩ := hs c (List.mem_cons_self ..)
        rw [← Literal.eval_eq_true] at hl'
        match c, hc3, hl'c with
        | [l0, l1, l2], _, hm =>
            simp only [pickBits, chooseLit]
            by_cases h0 : l0.eval a = true
            · simp [h0, idx]
            · by_cases h1 : l1.eval a = true
              · simp [h0, h1, idx]
              · simp only [h0, h1]
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
                rcases hm with rfl | rfl | rfl
                · exact absurd hl' h0
                · exact absurd hl' h1
                · simp [idx, hl']
      · exact ih (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
          (fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')) l h

/-- Exact 3-SAT instances have accepted certificates of two bits per clause. -/
theorem verify_complete (F : Formula ℕ) (h : ExactThreeSAT F) :
    ∃ w : List Bool, w.length = 2 * F.length ∧ verify (F, w) = true := by
  obtain ⟨_, hw, a, hs⟩ := h
  refine ⟨witness a F, ?_, ?_⟩
  · simp [witness, List.length_flatMap, pickBits_length, List.sum_replicate, Nat.mul_comm]
  · have hev := chosen_witness a F hw hs
    simp only [verify, Bool.and_eq_true]
    refine ⟨(widthOk_iff F).mpr hw, (consistent_iff _).mpr fun l hl l' hl' => ?_⟩
    have e1 := hev l hl
    have e2 := hev l' hl'
    cases l <;> cases l' <;> simp_all [conflict, isNeg, Literal.var, Literal.eval] <;>
      (intro h; subst h; simp_all)

theorem witness_length_le (F : Formula ℕ) : 2 * F.length ≤ 2 * (Formula.encode F).length := by
  have := BinaryNatLists.length_le_wireSize F.toNatLists
  rw [Formula.encode_length]
  simp only [Formula.toNatLists, List.length_map] at this
  have e : F.encodedSize = BinaryNatLists.wireSize F.toNatLists := by
    simp [Formula.encodedSize, BinaryNatLists.wireSize, BinaryNatLists.listWireSize,
      Formula.toNatLists, List.map_map, Function.comp_def]
  rw [e]
  simp only [Formula.toNatLists] at this ⊢
  omega

end LeanNPHardness.ExactThreeVerify
