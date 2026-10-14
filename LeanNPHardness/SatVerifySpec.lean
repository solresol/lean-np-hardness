import LeanNPHardness.ExactThreeVerifySpec

/-!
# The CNF-SAT verifier: semantics

The certificate selects one literal per clause in unary: `false` skips a
literal and `true` selects it (`selectLit`); a clause whose literals are
all skipped is rejected. The verifier accepts when every clause selects a
literal and no two selected literals are complementary (`verifySat`).
`verifySat_sound` and `verifySat_complete` characterize `SAT`, with
certificates of at most twice the binary input length.
-/

namespace LeanNPHardness.SatVerify

open CNF ExactThreeVerify

/-- Select a literal of a clause by unary certificate bits. -/
def selectLit : Clause ℕ → List Bool → Option (Literal ℕ) × List Bool
  | [], w => (none, w)
  | l :: c, w => if w.getD 0 false then (some l, w.drop 1) else selectLit c (w.drop 1)

/-- Selected literals, remaining certificate, and whether every clause selected. -/
def satWalk : Formula ℕ → List Bool → List (Literal ℕ) × List Bool × Bool
  | [], w => ([], w, true)
  | c :: F, w =>
      match selectLit c w with
      | (some l, w') => (l :: (satWalk F w').1, (satWalk F w').2.1, (satWalk F w').2.2)
      | (none, w') => ([], w', false)

/-- The CNF-SAT verifier. -/
def verifySat (p : Formula ℕ × List Bool) : Bool :=
  (satWalk p.1 p.2).2.2 && consistent (satWalk p.1 p.2).1

theorem selectLit_mem (c : Clause ℕ) : ∀ (w : List Bool) (l : Literal ℕ) (w' : List Bool),
    selectLit c w = (some l, w') → l ∈ c := by
  induction c with
  | nil => intro w l w' h; simp [selectLit] at h
  | cons d c ih =>
      intro w l w' h
      unfold selectLit at h
      split_ifs at h with hb
      · simp only [Prod.mk.injEq, Option.some.injEq] at h
        rw [← h.1]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ l w' h)

theorem satWalk_cover (F : Formula ℕ) : ∀ w, (satWalk F w).2.2 = true →
    ∀ c ∈ F, ∃ l ∈ (satWalk F w).1, l ∈ c := by
  induction F with
  | nil => simp
  | cons c F ih =>
      intro w h d hd
      unfold satWalk at h ⊢
      match hs : selectLit c w with
      | (some l, w') =>
          simp only [hs] at h ⊢
          rcases List.mem_cons.mp hd with rfl | hd'
          · exact ⟨l, List.mem_cons_self .., selectLit_mem _ w l w' hs⟩
          · obtain ⟨l', hl', hl'd⟩ := ih w' h d hd'
            exact ⟨l', List.mem_cons_of_mem _ hl', hl'd⟩
      | (none, w') => simp [hs] at h

theorem verifySat_sound (F : Formula ℕ) (w : List Bool) (h : verifySat (F, w) = true) : SAT F := by
  simp only [verifySat, Bool.and_eq_true] at h
  have hcons := (consistent_iff _).mp h.2
  refine ⟨fun v => (satWalk F w).1.any (· == .positive v), ?_⟩
  intro c hc
  obtain ⟨l, hl, hlc⟩ := satWalk_cover F w h.1 c hc
  refine ⟨l, hlc, ?_⟩
  cases l with
  | positive v =>
      show (satWalk F w).1.any (· == .positive v) = true
      exact List.any_eq_true.mpr ⟨_, hl, by simp⟩
  | negative v =>
      show (satWalk F w).1.any (· == .positive v) = false
      rw [Bool.eq_false_iff]
      intro hany
      obtain ⟨l', hl', he⟩ := List.any_eq_true.mp hany
      have he' : l' = .positive v := by simpa using he
      subst he'
      have := hcons _ hl _ hl'
      simp [conflict, isNeg, Literal.var] at this

/-- Unary selection bits of the first true literal. -/
def selBits (a : Assignment ℕ) : Clause ℕ → List Bool
  | [] => []
  | l :: c => if l.eval a then [true] else false :: selBits a c

theorem selBits_length (a : Assignment ℕ) (c : Clause ℕ) : (selBits a c).length ≤ c.length := by
  induction c with
  | nil => simp [selBits]
  | cons l c ih => unfold selBits; split_ifs <;> simp <;> omega

theorem selectLit_selBits (a : Assignment ℕ) (c : Clause ℕ) (hc : Clause.Satisfied a c)
    (rest : List Bool) : ∃ l, l.eval a = true ∧ selectLit c (selBits a c ++ rest) = (some l, rest) := by
  induction c with
  | nil => obtain ⟨l, hl, _⟩ := hc; simp at hl
  | cons d c ih =>
      by_cases hd : d.eval a = true
      · exact ⟨d, hd, by simp [selBits, hd, selectLit]⟩
      · have hc' : Clause.Satisfied a c := by
          obtain ⟨l, hl, hsat⟩ := hc
          rcases List.mem_cons.mp hl with rfl | h
          · exact absurd ((Literal.eval_eq_true _ _).mpr hsat) hd
          · exact ⟨l, h, hsat⟩
        obtain ⟨l, hl, hs⟩ := ih hc'
        refine ⟨l, hl, ?_⟩
        simp only [selBits, hd, selectLit]
        simpa using hs

/-- The certificate built from a satisfying assignment. -/
def witnessSat (a : Assignment ℕ) (F : Formula ℕ) : List Bool := F.flatMap (selBits a)

theorem satWalk_witness (a : Assignment ℕ) (F : Formula ℕ) (hs : ∀ c ∈ F, Clause.Satisfied a c) :
    ∀ rest, (satWalk F (witnessSat a F ++ rest)).2.2 = true ∧
      ∀ l ∈ (satWalk F (witnessSat a F ++ rest)).1, l.eval a = true := by
  induction F with
  | nil => intro rest; simp [satWalk]
  | cons c F ih =>
      intro rest
      obtain ⟨l, hl, hsel⟩ := selectLit_selBits a c (hs c (List.mem_cons_self ..))
        (witnessSat a F ++ rest)
      have ih' := ih (fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')) rest
      have hw : witnessSat a (c :: F) ++ rest = selBits a c ++ (witnessSat a F ++ rest) := by
        simp [witnessSat, List.append_assoc]
      rw [hw]
      unfold satWalk
      rw [hsel]
      refine ⟨ih'.1, fun l' hl' => ?_⟩
      rcases List.mem_cons.mp hl' with rfl | h
      · exact hl
      · exact ih'.2 l' h

theorem witnessSat_length (a : Assignment ℕ) (F : Formula ℕ) :
    (witnessSat a F).length ≤ (F.map List.length).sum := by
  induction F with
  | nil => simp [witnessSat]
  | cons c F ih =>
      simp only [witnessSat, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
        at ih ⊢
      have := selBits_length a c
      omega

theorem verifySat_complete (F : Formula ℕ) (h : SAT F) :
    ∃ w : List Bool, w.length ≤ 2 * (Formula.encode F).length ∧ verifySat (F, w) = true := by
  obtain ⟨a, hs⟩ := h
  refine ⟨witnessSat a F, ?_, ?_⟩
  · have h1 := witnessSat_length a F
    have h2 := BinaryNatLists.sum_lengths_le_wireSize F.toNatLists
    have e : F.encodedSize = BinaryNatLists.wireSize F.toNatLists := by
      simp [Formula.encodedSize, BinaryNatLists.wireSize, BinaryNatLists.listWireSize,
        Formula.toNatLists, List.map_map, Function.comp_def]
    rw [Formula.encode_length, e]
    have h3 : ((F.toNatLists).map List.length).sum = (F.map List.length).sum := by
      simp [Formula.toNatLists, List.map_map, Function.comp_def]
    omega
  · have hw := satWalk_witness a F hs []
    rw [List.append_nil] at hw
    simp only [verifySat, Bool.and_eq_true]
    refine ⟨hw.1, (consistent_iff _).mpr fun l hl l' hl' => ?_⟩
    have e1 := hw.2 l hl
    have e2 := hw.2 l' hl'
    cases l <;> cases l' <;> simp_all [conflict, isNeg, Literal.var, Literal.eval] <;>
      (intro h; subst h; simp_all)

end LeanNPHardness.SatVerify
