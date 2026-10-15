import LeanNPHardness.VerifierBase

/-!
# The exact 3-SAT verifier machine: clauses

Per clause the verifier checks that the framed clause length is three
(nested dispatches against the frame `11011`); otherwise it records a
failure on `BAD` and drains the formula. For a width-three clause it reads
two certificate bits and keeps the selected literal's entry on `L`,
skipping the other two codes (`clauseOk_exits`, `clauseBad_exits`).
`clauseLoop_exits` runs this over all clauses, matching the functional
walk `walk`.
-/

namespace LeanNPHardness.ExactThreeVerify

open Routines CNF CNF.Unary
open LeanNPHardness.BinaryConvert (b2s s2b s2b_b2s marks marks_succ marks_zero marks_length
  marks_eq_nil marks_reverse bitsOf bitsOf_eq bitsOf_pos encodeNat_odd encodeNat_even)

/-! ### Entries of literals -/

/-- The entry of a literal: its variable's bits, then its polarity. -/
def entryL (l : Literal ℕ) : List Sym := bsyms (Computability.encodeNat l.var) ++ [term (isNeg l)]

theorem entryOf_code (l : Literal ℕ) : entryOf (Computability.encodeNat l.toNat) = entryL l := by
  cases l with
  | positive v =>
      by_cases hv : v = 0
      · subst hv
        show entryOf (Computability.encodeNat 0) = entryL (.positive 0)
        rw [← bitsOf_eq, BinaryConvert.bitsOf_zero]
        simp [entryOf, entryL, ← bitsOf_eq, BinaryConvert.bitsOf_zero, bsyms, isNeg, Literal.var]
      · show entryOf (Computability.encodeNat (2 * v)) = _
        rw [encodeNat_even v (by omega)]
        simp [entryOf, entryL, isNeg, Literal.var]
  | negative v =>
      show entryOf (Computability.encodeNat (2 * v + 1)) = _
      rw [encodeNat_odd v]
      simp [entryOf, entryL, isNeg, Literal.var]

/-! ### The per-clause routine -/

/-- Record a failure and drain the formula. -/
def bad : VR := seq (pushList .BAD [.mark]) (drain .F)

/-- Keep literal 0, 1 or 2 of the clause. -/
def path : ℕ → VR
  | 0 => seq readKeep (seq skipFrame skipFrame)
  | 1 => seq skipFrame (seq readKeep skipFrame)
  | _ => seq skipFrame (seq skipFrame readKeep)

/-- Second certificate bit. -/
def c2 : Sym → VR
  | .pos => path 1
  | .neg => path 2
  | _ => skip

/-- First certificate bit. -/
def c1 : Sym → VR
  | .pos => seq (popOne .C) (path 0)
  | .neg => dispatch .C c2
  | _ => skip

/-- Choose the literal by the certificate. -/
def okPath : VR := dispatch .C c1

def w5 : Sym → VR
  | .pos => okPath
  | _ => bad
def w4 : Sym → VR
  | .pos => dispatch .F w5
  | _ => bad
def w3 : Sym → VR
  | .neg => dispatch .F w4
  | _ => bad
def w2 : Sym → VR
  | .pos => dispatch .F w3
  | _ => bad
def w1 : Sym → VR
  | .pos => dispatch .F w2
  | _ => bad

/-- Process one clause. -/
def clauseV : VR := dispatch .F w1

/-- The symbols of one clause. -/
def clauseS (c : Clause ℕ) : List Sym :=
  frameS (Computability.encodeNat c.length) ++
    c.flatMap fun l => frameS (Computability.encodeNat l.toNat)

theorem bad_exits (S : VS) :
    bad.ExitsLE S (2 * (S .F).length + 2)
      (Function.update (Function.update S .BAD (.mark :: S .BAD)) .F []) := by
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.BAD [Sym.mark] S 0)
    (drain_exits (Γ := VAlpha) VStack.F _).le
  refine (this.mono (by simp; omega)).congr ?_
  funext k; cases k <;> simp

theorem path_exits (i : ℕ) (hi : i < 3) (l0 l1 l2 : Literal ℕ) (S : VS) (rest : List Sym)
    (hF : S .F = frameS (Computability.encodeNat l0.toNat) ++
      (frameS (Computability.encodeNat l1.toNat) ++ (frameS (Computability.encodeNat l2.toNat) ++ rest)))
    (hS : ReadClean S) :
    (path i).ExitsLE S (14 * ((Computability.encodeNat l0.toNat).length +
        (Computability.encodeNat l1.toNat).length + (Computability.encodeNat l2.toNat).length) + 60)
      (Function.update (Function.update S .F rest) .L
        (entryL ([l0, l1, l2].getD i (.positive 0)) ++ S .L)) := by
  set e1 := Computability.encodeNat l1.toNat
  set e2 := Computability.encodeNat l2.toNat
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · have := seq_exitsLE _ _ (readKeep_exits _ S _ hF hS)
      (seq_exitsLE _ _ (skipFrame_exits e1 _ (frameS e2 ++ rest) (by simp) (by simp [hS.G])
          (by simp [hS.K]))
        (skipFrame_exits e2 _ rest (by simp) (by simp [hS.G]) (by simp [hS.K])))
    refine (this.mono (by omega)).congr ?_
    funext k; cases k <;> simp [entryOf_code]
  · have := seq_exitsLE _ _ (skipFrame_exits _ S _ hF hS.G hS.K)
      (seq_exitsLE _ _ (readKeep_exits e1 _ (frameS e2 ++ rest) (by simp)
          ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
            by simp [hS.Z]⟩)
        (skipFrame_exits e2 _ rest (by simp) (by simp [hS.G]) (by simp [hS.K])))
    refine (this.mono (by omega)).congr ?_
    funext k; cases k <;> simp [entryOf_code, e1]
  · have := seq_exitsLE _ _ (skipFrame_exits _ S _ hF hS.G hS.K)
      (seq_exitsLE _ _ (skipFrame_exits e1 _ (frameS e2 ++ rest) (by simp) (by simp [hS.G])
          (by simp [hS.K]))
        (readKeep_exits e2 _ rest (by simp)
          ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
            by simp [hS.Z]⟩))
    refine (this.mono (by omega)).congr ?_
    funext k; cases k <;> simp [entryOf_code, e2]

/-! ### The width check -/

theorem encodeNat_three : Computability.encodeNat 3 = [true, true] := by
  rw [show (3 : ℕ) = 2 * 1 + 1 by rfl, encodeNat_odd, show (1 : ℕ) = 2 * 0 + 1 by rfl, encodeNat_odd,
    ← bitsOf_eq, BinaryConvert.bitsOf_zero]

theorem frameS_three : frameS (Computability.encodeNat 3) = [.pos, .pos, .neg, .pos, .pos] := by
  rw [encodeNat_three]; simp [frameS_eq, bsyms, b2s]

theorem update_F_idem (S : VS) (a b : List Sym) :
    Function.update (Function.update S .F a) .F b = Function.update S .F b :=
  Function.update_idem _ _ _

/-- A matching frame `11011` leads to `okPath`. -/
theorem clauseV_pass (S : VS) (R : List Sym) (hF : S .F = [.pos, .pos, .neg, .pos, .pos] ++ R)
    {n : ℕ} {S' : VS} (h : okPath.ExitsLE (Function.update S .F R) n S') :
    clauseV.ExitsLE S (n + 5) S' := by
  refine dispatch_exitsLE (Γ := VAlpha) (n := n + 4) .F w1 S .pos
    (Sym.pos :: Sym.neg :: Sym.pos :: Sym.pos :: R) (by simp [hF]) ?_
  refine dispatch_exitsLE (Γ := VAlpha) (n := n + 3) .F w2 _ .pos
    (Sym.neg :: Sym.pos :: Sym.pos :: R) (by simp) ?_
  refine dispatch_exitsLE (Γ := VAlpha) (n := n + 2) .F w3 _ .neg (Sym.pos :: Sym.pos :: R)
    (by simp) ?_
  refine dispatch_exitsLE (Γ := VAlpha) (n := n + 1) .F w4 _ .pos (Sym.pos :: R) (by simp) ?_
  refine dispatch_exitsLE (Γ := VAlpha) (n := n) .F w5 _ .pos R (by simp) ?_
  simp only [update_F_idem]
  exact h

theorem clauseOk_exits (c : Clause ℕ) (hc : c.length = 3) (S : VS) (rest : List Sym)
    (b0 b1 : Bool) (v : List Bool) (hF : S .F = clauseS c ++ rest)
    (hC : S .C = bsyms (b0 :: b1 :: v)) (hS : ReadClean S) :
    clauseV.ExitsLE S (7 * (clauseS c).length + 14)
      (Function.update (Function.update (Function.update S .F rest) .C (bsyms v)) .L
        (entryL (chooseLit c b0 b1) ++ S .L)) := by
  match c, hc with
  | [l0, l1, l2], _ =>
    have hF' : S .F = [.pos, .pos, .neg, .pos, .pos] ++
        (frameS (Computability.encodeNat l0.toNat) ++ (frameS (Computability.encodeNat l1.toNat) ++
          (frameS (Computability.encodeNat l2.toNat) ++ rest))) := by
      rw [hF, clauseS]; simp [frameS_three]
    have hlen : (clauseS [l0, l1, l2]).length = 8 + 2 * ((Computability.encodeNat l0.toNat).length +
        (Computability.encodeNat l1.toNat).length + (Computability.encodeNat l2.toNat).length) := by
      simp [clauseS, encodeNat_three, frameS_eq, bsyms]; omega
    have hS' : ReadClean (Function.update S .F
        (frameS (Computability.encodeNat l0.toNat) ++ (frameS (Computability.encodeNat l1.toNat) ++
          (frameS (Computability.encodeNat l2.toNat) ++ rest)))) :=
      ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
        by simp [hS.Z]⟩
    cases b0 with
    | true =>
        have hp := path_exits 0 (by omega) l0 l1 l2 _ rest (by simp)
          (⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
            by simp [hS.Z]⟩ : ReadClean (Function.update (Function.update (Function.update S .F
              (frameS (Computability.encodeNat l0.toNat) ++ (frameS (Computability.encodeNat l1.toNat)
                ++ (frameS (Computability.encodeNat l2.toNat) ++ rest)))) .C (bsyms (b1 :: v))) .C
              (bsyms v)))
        have := clauseV_pass S _ hF'
          (dispatch_exitsLE (Γ := VAlpha) .C c1 _ .pos (bsyms (b1 :: v)) (by simp [hC, bsyms, b2s])
            (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.C _ 0) hp))
        refine (this.mono (by rw [hlen]; omega)).congr ?_
        funext k; cases k <;> simp [chooseLit, idx, bsyms]
    | false =>
        cases b1 with
        | true =>
            have hp := path_exits 1 (by omega) l0 l1 l2 _ rest (by simp)
              (⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
                by simp [hS.Z]⟩ : ReadClean (Function.update (Function.update (Function.update S .F
                  (frameS (Computability.encodeNat l0.toNat) ++
                    (frameS (Computability.encodeNat l1.toNat) ++
                    (frameS (Computability.encodeNat l2.toNat) ++ rest)))) .C (bsyms (true :: v))) .C
                  (bsyms v)))
            have := clauseV_pass S _ hF'
              (dispatch_exitsLE (Γ := VAlpha) .C c1 _ .neg (bsyms (true :: v))
                (by simp [hC, bsyms, b2s])
                (dispatch_exitsLE (Γ := VAlpha) .C c2 _ .pos (bsyms v) (by simp [bsyms, b2s]) hp))
            refine (this.mono (by rw [hlen]; omega)).congr ?_
            funext k; cases k <;> simp [chooseLit, idx, bsyms]
        | false =>
            have hp := path_exits 2 (by omega) l0 l1 l2 _ rest (by simp)
              (⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
                by simp [hS.Z]⟩ : ReadClean (Function.update (Function.update (Function.update S .F
                  (frameS (Computability.encodeNat l0.toNat) ++
                    (frameS (Computability.encodeNat l1.toNat) ++
                    (frameS (Computability.encodeNat l2.toNat) ++ rest)))) .C (bsyms (false :: v))) .C
                  (bsyms v)))
            have := clauseV_pass S _ hF'
              (dispatch_exitsLE (Γ := VAlpha) .C c1 _ .neg (bsyms (false :: v))
                (by simp [hC, bsyms, b2s])
                (dispatch_exitsLE (Γ := VAlpha) .C c2 _ .neg (bsyms v) (by simp [bsyms, b2s]) hp))
            refine (this.mono (by rw [hlen]; omega)).congr ?_
            funext k; cases k <;> simp [chooseLit, idx, bsyms]

/-! ### Clauses of other widths -/

theorem encodeNat_long (n : ℕ) (hn : 4 ≤ n) :
    ∃ a b d t, Computability.encodeNat n = a :: b :: d :: t := by
  rw [← bitsOf_eq, bitsOf_pos n (by omega), bitsOf_pos (n / 2) (by omega),
    bitsOf_pos (n / 2 / 2) (by omega)]
  exact ⟨_, _, _, _, rfl⟩

theorem bad_after (S S₀ : VS) (R : List Sym) (hS : S = Function.update S₀ .F R) :
    bad.ExitsLE S (2 * R.length + 2)
      (Function.update (Function.update S₀ .BAD (.mark :: S₀ .BAD)) .F []) := by
  subst hS
  refine (bad_exits _).mono (by simp) |>.congr ?_
  funext k; cases k <;> simp

theorem clauseBad_exits (c : Clause ℕ) (hc : c.length ≠ 3) (S : VS) (rest : List Sym)
    (hF : S .F = clauseS c ++ rest) :
    clauseV.ExitsLE S (2 * (clauseS c ++ rest).length + 10)
      (Function.update (Function.update S .BAD (.mark :: S .BAD)) .F []) := by
  set R := (c.flatMap fun l => frameS (Computability.encodeNat l.toNat)) ++ rest with hR
  have hF' : S .F = frameS (Computability.encodeNat c.length) ++ R := by
    rw [hF, hR, clauseS, List.append_assoc]
  have hlen : (clauseS c ++ rest).length = (frameS (Computability.encodeNat c.length)).length +
      R.length := by
    rw [hR, clauseS]; simp
  rw [hlen]
  rcases (show c.length = 0 ∨ c.length = 1 ∨ c.length = 2 ∨ 4 ≤ c.length by omega)
    with h0 | h1 | h2 | h4
  · rw [h0, ← bitsOf_eq, BinaryConvert.bitsOf_zero] at hF'
    simp only [frameS_eq, List.length_nil, List.replicate_zero, bsyms, List.map_nil,
      List.nil_append, List.cons_append] at hF'
    have := dispatch_exitsLE (Γ := VAlpha) .F w1 S .neg R hF'
      (bad_after (Function.update S .F R) S R rfl)
    exact this.mono (by simp; omega)
  · have e : Computability.encodeNat 1 = [true] := by
      rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, encodeNat_odd, ← bitsOf_eq, BinaryConvert.bitsOf_zero]
    rw [h1, e] at hF'
    simp [frameS_eq, bsyms, b2s] at hF'
    have := dispatch_exitsLE (Γ := VAlpha) .F w1 S .pos (Sym.neg :: Sym.pos :: R) hF'
      (dispatch_exitsLE (Γ := VAlpha) .F w2 _ .neg (Sym.pos :: R) (by simp)
        (bad_after _ S (Sym.pos :: R) (by simp)))
    exact this.mono (by rw [h1, e]; simp [frameS_eq, bsyms]; omega)
  · have e : Computability.encodeNat 2 = [false, true] := by
      rw [show (2 : ℕ) = 2 * 1 by rfl, encodeNat_even 1 (by omega), show (1 : ℕ) = 2 * 0 + 1 by rfl,
        encodeNat_odd, ← bitsOf_eq, BinaryConvert.bitsOf_zero]
    rw [h2, e] at hF'
    simp [frameS_eq, bsyms, b2s] at hF'
    have := dispatch_exitsLE (Γ := VAlpha) .F w1 S .pos
      (Sym.pos :: Sym.neg :: Sym.neg :: Sym.pos :: R) hF'
      (dispatch_exitsLE (Γ := VAlpha) .F w2 _ .pos (Sym.neg :: Sym.neg :: Sym.pos :: R) (by simp)
        (dispatch_exitsLE (Γ := VAlpha) .F w3 _ .neg (Sym.neg :: Sym.pos :: R) (by simp)
          (dispatch_exitsLE (Γ := VAlpha) .F w4 _ .neg (Sym.pos :: R) (by simp)
            (bad_after _ S (Sym.pos :: R) (by simp)))))
    exact this.mono (by rw [h2, e]; simp [frameS_eq, bsyms]; omega)
  · obtain ⟨a, b, d, t, e⟩ := encodeNat_long c.length h4
    rw [e] at hF'
    set X := List.replicate t.length Sym.pos ++ Sym.neg :: bsyms (a :: b :: d :: t) ++ R with hX
    have hF'' : S .F = Sym.pos :: Sym.pos :: Sym.pos :: X := by
      rw [hF', hX, frameS_eq]; simp [List.replicate_succ]
    have := dispatch_exitsLE (Γ := VAlpha) .F w1 S .pos (Sym.pos :: Sym.pos :: X) hF''
      (dispatch_exitsLE (Γ := VAlpha) .F w2 _ .pos (Sym.pos :: X) (by simp)
        (dispatch_exitsLE (Γ := VAlpha) .F w3 _ .pos X (by simp)
          (bad_after _ S X (by simp))))
    exact this.mono (by rw [e, hX]; simp [frameS_eq, bsyms]; omega)

/-! ### All clauses -/

/-- The functional walk: selected literals so far, remaining certificate, and
whether every clause had width three. -/
def walk : Formula ℕ → List Bool → List (Literal ℕ) × List Bool × Bool
  | [], w => ([], w, true)
  | c :: F, w =>
      if c.length = 3 then
        ((chooseLit c (w.getD 0 false) (w.getD 1 false)) :: (walk F (w.drop 2)).1,
          (walk F (w.drop 2)).2.1, (walk F (w.drop 2)).2.2)
      else ([], w, false)

theorem clauseLoop_exits (F : Formula ℕ) : ∀ (S : VS) (v : List Bool),
    S .F = F.flatMap clauseS → S .C = bsyms v → 2 * F.length ≤ v.length → ReadClean S →
    (loop .F clauseV).ExitsLE S (30 * ((F.flatMap clauseS).length + F.length) + 1)
      (Function.update (Function.update (Function.update (Function.update S .F []) .C
        (bsyms (walk F v).2.1)) .L (((walk F v).1.reverse.flatMap entryL) ++ S .L)) .BAD
        ((if (walk F v).2.2 then [] else [.mark]) ++ S .BAD)) := by
  induction F with
  | nil =>
      intro S v hF hC _ hS
      refine (loop_exitsLE_nil _ _ S (by simpa using hF) _).congr ?_
      funext k; cases k <;> simp [walk, hF, hC]
  | cons c F ih =>
      intro S v hF hC hv hS
      have hF' : S .F = clauseS c ++ F.flatMap clauseS := by rw [hF, List.flatMap_cons]
      have hne : S .F ≠ [] := by
        rw [hF']; simp [clauseS, frameS_eq]
      by_cases hc : c.length = 3
      · obtain ⟨b0, b1, v', rfl⟩ : ∃ b0 b1 v', v = b0 :: b1 :: v' := by
          match v, hv with
          | b0 :: b1 :: v', _ => exact ⟨b0, b1, v', rfl⟩
        have h1 := clauseOk_exits c hc S _ b0 b1 v' hF' hC hS
        have h2 := ih (Function.update (Function.update (Function.update S .F
            (F.flatMap clauseS)) .C (bsyms v')) .L (entryL (chooseLit c b0 b1) ++ S .L)) v'
          (by simp) (by simp) (by simp at hv; omega)
          ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
            by simp [hS.Z]⟩
        refine ((loop_exitsLE_cons _ _ hne h1 h2).mono ?_).congr ?_
        · simp only [List.flatMap_cons, List.length_append, List.length_cons]
          omega
        · funext k; cases k <;> simp [walk, hc, List.flatMap_append]
      · have h1 := clauseBad_exits c hc S _ hF'
        have h2 := loop_exitsLE_nil (Γ := VAlpha) VStack.F clauseV
          (Function.update (Function.update S .BAD (.mark :: S .BAD)) .F []) (by simp) 0
        refine ((loop_exitsLE_cons _ _ hne h1 h2).mono ?_).congr ?_
        · simp only [List.flatMap_cons, List.length_append, List.length_cons]
          omega
        · funext k; cases k <;> simp [walk, hc, hC]

end LeanNPHardness.ExactThreeVerify
