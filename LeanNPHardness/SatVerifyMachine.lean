import LeanNPHardness.SatVerifySpec
import LeanNPHardness.VerifierMachine

/-!
# The CNF-SAT verifier machine

Per clause the machine converts the framed binary clause length to unary
on `LC` (Horner's scheme with unary doubling, `readLen_exits`), then walks
the clause's literal codes: while no literal is selected (`CH = [pos]`) it
reads a certificate bit per literal, keeping the selected literal's entry;
afterwards it skips the remaining codes. A clause without a selection
records a failure. The pairwise check, result bit and cleanup are those of
the exact 3-SAT verifier.
-/

namespace LeanNPHardness.SatVerify

open Turing Computability Routines CNF CNF.Unary Polynomial MachinePrimitives ExactThreeVerify StateTransition
open LeanNPHardness.BinaryConvert (b2s s2b s2b_b2s marks marks_succ marks_zero marks_length
  marks_eq_nil marks_reverse marks_add bitsOf bitsOf_eq bitsOf_pos)

/-! ### Binary to unary -/

/-- Little-endian value of bits. -/
def hval : List Bool → ℕ
  | [] => 0
  | b :: r => (if b then 1 else 0) + 2 * hval r

theorem hval_encodeNat (n : ℕ) : hval (Computability.encodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rw [← bitsOf_eq]
      by_cases h0 : n = 0
      · subst h0; simp [BinaryConvert.bitsOf_zero, hval]
      · rw [bitsOf_pos n h0, hval, bitsOf_eq, ih (n / 2) (by omega)]
        by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-- Horner's scheme over most-significant-first bits. -/
def hornerB : ℕ → List Bool → ℕ
  | acc, [] => acc
  | acc, b :: ms => hornerB (2 * acc + (if b then 1 else 0)) ms

theorem hornerB_append (xs : List Bool) (b : Bool) : ∀ acc,
    hornerB acc (xs ++ [b]) = 2 * hornerB acc xs + (if b then 1 else 0) := by
  induction xs with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; simp [hornerB, ih]

theorem hornerB_reverse (bits : List Bool) : hornerB 0 bits.reverse = hval bits := by
  induction bits with
  | nil => rfl
  | cons b r ih => rw [List.reverse_cons, hornerB_append, ih, hval]; omega

theorem le_hornerB (ms : List Bool) : ∀ acc, acc ≤ hornerB acc ms := by
  induction ms with
  | nil => intro acc; exact le_rfl
  | cons b ms ih => intro acc; exact le_trans (by split <;> omega) (ih _)

/-- Double the marks on `LC`. -/
def double : VR := seq (moveAll .LC .U2 id .mark) (loop .U2 (seq (popOne .U2) (pushList .LC [.mark, .mark])))

theorem doubleLoop_exits (a : ℕ) : ∀ (S : VS) (c : ℕ), S .U2 = marks a → S .LC = marks c →
    (loop .U2 (seq (popOne .U2) (pushList .LC [.mark, .mark]))).ExitsLE S (3 * a + 1)
      (Function.update (Function.update S .U2 []) .LC (marks (c + 2 * a))) := by
  induction a with
  | zero =>
      intro S c hu hl
      refine (loop_exitsLE_nil _ _ S (by simp [hu]) 0).congr ?_
      funext k; cases k <;> simp [hu, hl]
  | succ a ih =>
      intro S c hu hl
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.U2 S 0)
        (pushList_exitsLE (Γ := VAlpha) VStack.LC [Sym.mark, Sym.mark] _ 0)
      have h2 := ih (Function.update (Function.update S .U2 (S .U2).tail) .LC
          ([Sym.mark, Sym.mark] ++ (Function.update S .U2 (S .U2).tail) .LC)) (c + 2)
        (by simp [hu, marks_succ]) (by simp [hl, marks_succ])
      refine ((loop_exitsLE_cons _ _ (by simp [hu, marks_succ]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> (try simp) <;> (congr 1; omega)

theorem double_exits (a : ℕ) (S : VS) (hl : S .LC = marks a) (hu : S .U2 = []) :
    double.ExitsLE S (5 * a + 2) (Function.update S .LC (marks (2 * a))) := by
  have := seq_exitsLE _ _ (moveAll_exits (Γ := VAlpha) VStack.LC VStack.U2 (by decide) id Sym.mark S).le
    (doubleLoop_exits a _ 0 (by simp [hl, hu]) (by simp))
  refine (this.mono (by simp [hl]; omega)).congr ?_
  funext k; cases k <;> simp [hu]

/-- One Horner step. -/
def hornH : Sym → VR
  | .pos => seq double (pushList .LC [.mark])
  | .neg => double
  | _ => skip

theorem hornLoop_exits (ms : List Bool) : ∀ (S : VS) (acc : ℕ),
    S .T1 = bsyms ms → S .LC = marks acc → S .U2 = [] →
    (loop .T1 (dispatch .T1 hornH)).ExitsLE S (ms.length * (5 * hornerB acc ms + 6) + 1)
      (Function.update (Function.update S .T1 []) .LC (marks (hornerB acc ms))) := by
  induction ms with
  | nil =>
      intro S acc ht hl hu
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.T1 (dispatch VStack.T1 hornH) S
        (by simp [ht, bsyms]) 0).mono (by simp)).congr ?_
      funext k; cases k <;> simp [ht, hl, hornerB, bsyms]
  | cons b ms ih =>
      intro S acc ht hl hu
      have hacc := le_hornerB ms (2 * acc + (if b then 1 else 0))
      have hstep : (hornH (b2s b)).ExitsLE (Function.update S .T1 (bsyms ms)) (5 * acc + 3)
          (Function.update (Function.update S .T1 (bsyms ms)) .LC
            (marks (2 * acc + (if b then 1 else 0)))) := by
        cases b
        · exact ((double_exits acc _ (by simp [hl]) (by simp [hu])).mono (by omega)).congr
            (by funext k; cases k <;> simp)
        · refine ((seq_exitsLE _ _ (double_exits acc _ (by simp [hl]) (by simp [hu]))
            (pushList_exitsLE (Γ := VAlpha) VStack.LC [Sym.mark] _ 0)).mono (by omega)).congr ?_
          funext k; cases k <;> simp [marks_succ]
      have h2 := ih (Function.update (Function.update S .T1 (bsyms ms)) .LC
          (marks (2 * acc + (if b then 1 else 0)))) (2 * acc + (if b then 1 else 0)) (by simp)
          (by simp) (by simp [hu])
      refine ((loop_exitsLE_cons _ _ (by simp [ht, bsyms])
        (dispatch_exitsLE (Γ := VAlpha) .T1 hornH S (b2s b) (bsyms ms) (by simp [ht, bsyms]) hstep)
        h2).mono ?_).congr ?_
      · simp only [hornerB, List.length_cons, Nat.add_mul, Nat.one_mul]
        have : acc ≤ hornerB (2 * acc + (if b then 1 else 0)) ms := le_trans (by split <;> omega) hacc
        omega
      · funext k; cases k <;> simp [hornerB]

/-- Read a framed natural from `F` into unary on `LC`. -/
def readLen : VR :=
  seq (pushList .G [.mark]) <| seq (loop .G (dispatch .F skH)) <| seq moveLoop <|
  loop .T1 (dispatch .T1 hornH)

theorem readLen_exits (n : ℕ) (S : VS) (rest : List Sym)
    (hF : S .F = frameS (Computability.encodeNat n) ++ rest) (hS : ReadClean S) (hl : S .LC = [])
    (hu : S .U2 = []) :
    readLen.ExitsLE S ((Computability.encodeNat n).length * (5 * n + 13) + 7)
      (Function.update (Function.update S .F rest) .LC (marks n)) := by
  rw [frameS_eq] at hF
  set bits := Computability.encodeNat n with hbits
  have hv : hval bits = n := hval_encodeNat n
  have h := hornLoop_exits bits.reverse
  simp only [List.length_reverse] at h
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G [Sym.mark] S 0)
    (seq_exitsLE _ _ (countLoop_exits bits.length _ (bsyms bits ++ rest) 0
        (by simp [hF]) (by simp [hS.G]) (by simp [hS.K]))
      (seq_exitsLE _ _ (moveLoop_exits (bsyms bits) _ rest [] (by simp [bsyms]) (by simp)
          (by simp [hS.T1]))
        (h _ 0 (by simp [bsyms, List.map_reverse]) (by simp [hl]) (by simp [hu]))))
  rw [hornerB_reverse, hv] at this
  refine (this.mono ?_).congr ?_
  · simp [bsyms]
    have : bits.length * (5 * n + 6) + bits.length * 7 = bits.length * (5 * n + 13) := by ring
    omega
  · funext k; cases k <;> simp [hS.G, hS.K, hS.T1]

/-! ### Selecting a literal -/

/-- Act on a certificate bit while no literal is selected. -/
def certH : Sym → VR
  | .pos => seq (pushList .CH [.neg]) readKeep
  | .neg => seq (pushList .CH [.pos]) skipFrame
  | _ => skip

/-- Branch on whether a literal is already selected. -/
def chH : Sym → VR
  | .pos => dispatch .C certH
  | .neg => seq (pushList .CH [.neg]) skipFrame
  | _ => skip

/-- Process one literal code. -/
def litStep : VR := seq (popOne .LC) (dispatch .CH chH)

/-- The literal codes of a clause. -/
def codesS (c : Clause ℕ) : List Sym := c.flatMap fun l => frameS (Computability.encodeNat l.toNat)

theorem codesS_cons (l : Literal ℕ) (c : Clause ℕ) :
    codesS (l :: c) = frameS (Computability.encodeNat l.toNat) ++ codesS c := by
  simp [codesS]

theorem frameS_ne (bits : List Bool) : 1 ≤ (frameS bits).length := by rw [frameS_length]; omega

/-- After a selection, the remaining codes are skipped. -/
theorem skipRest_exits (ls : Clause ℕ) : ∀ (S : VS) (rest : List Sym),
    S .LC = marks ls.length → S .F = codesS ls ++ rest → S .CH = [.neg] → S .G = [] → S .K = [] →
    (loop .LC litStep).ExitsLE S (25 * (codesS ls).length + 1)
      (Function.update (Function.update S .LC []) .F rest) := by
  induction ls with
  | nil =>
      intro S rest hl hF hc hg hk
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.LC litStep S (by simp [hl]) 0).mono
        (by simp)).congr ?_
      funext k; cases k <;> simp [hl, hF, codesS]
  | cons l ls ih =>
      intro S rest hl hF hc hg hk
      have hF' : S .F = frameS (Computability.encodeNat l.toNat) ++ (codesS ls ++ rest) := by
        rw [hF, codesS_cons, List.append_assoc]
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.LC S 0)
        (dispatch_exitsLE (Γ := VAlpha) .CH chH _ .neg [] (by simp [hc])
          (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.CH [Sym.neg] _ 0)
            (skipFrame_exits (Computability.encodeNat l.toNat) _ (codesS ls ++ rest) (by simp [hF'])
              (by simp [hg]) (by simp [hk]))))
      have h2 := ih (Function.update (Function.update S .LC (marks ls.length)) .F (codesS ls ++ rest))
        rest (by simp) (by simp) (by simp [hc]) (by simp [hg]) (by simp [hk])
      have hb' := hb.congr (T := Function.update (Function.update S .LC (marks ls.length)) .F
          (codesS ls ++ rest)) (by funext k; cases k <;> simp [hl, hc, marks_succ])
      refine ((loop_exitsLE_cons _ _ (by simp [hl, marks_succ]) hb' h2).mono ?_).congr ?_
      · have := frameS_length (Computability.encodeNat l.toNat)
        simp only [codesS_cons, List.length_append]
        omega
      · funext k; cases k <;> simp

/-- The entry pushed for a selection result. -/
def selEntry : Option (Literal ℕ) → List Sym
  | some l => entryL l
  | none => []

/-- The selection marker: `neg` once a literal is selected. -/
def selMark : Option (Literal ℕ) → Sym
  | some _ => .neg
  | none => .pos

theorem select_exits (c : Clause ℕ) : ∀ (S : VS) (v : List Bool) (rest : List Sym),
    S .LC = marks c.length → S .F = codesS c ++ rest → S .CH = [.pos] → S .C = bsyms v →
    c.length ≤ v.length → ReadClean S →
    (loop .LC litStep).ExitsLE S (25 * (codesS c).length + 1)
      (Function.update (Function.update (Function.update (Function.update (Function.update S .LC [])
        .F rest) .C (bsyms (selectLit c v).2)) .CH [selMark (selectLit c v).1]) .L
        (selEntry (selectLit c v).1 ++ S .L)) := by
  induction c with
  | nil =>
      intro S v rest hl hF hc hC _ _
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.LC litStep S (by simp [hl]) 0).mono
        (by simp)).congr ?_
      funext k; cases k <;> simp [hl, hF, hc, hC, codesS, selectLit, selMark, selEntry]
  | cons l c ih =>
      intro S v rest hl hF hc hC hv hS
      obtain ⟨b, v', rfl⟩ : ∃ b v', v = b :: v' := by
        cases v with
        | nil => simp at hv
        | cons b v' => exact ⟨b, v', rfl⟩
      have hF' : S .F = frameS (Computability.encodeNat l.toNat) ++ (codesS c ++ rest) := by
        rw [hF, codesS_cons, List.append_assoc]
      have hfl := frameS_length (Computability.encodeNat l.toNat)
      cases b with
      | true =>
          have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.LC S 0)
            (dispatch_exitsLE (Γ := VAlpha) .CH chH _ .pos [] (by simp [hc])
              (dispatch_exitsLE (Γ := VAlpha) .C certH _ .pos (bsyms v') (by simp [hC, bsyms, b2s])
                (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.CH [Sym.neg] _ 0)
                  (readKeep_exits (Computability.encodeNat l.toNat) _ (codesS c ++ rest) (by simp [hF'])
                    ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2],
                      by simp [hS.T3], by simp [hS.Z]⟩))))
          have hb' := hb.congr (T := Function.update (Function.update (Function.update
              (Function.update (Function.update S .LC (marks c.length)) .F (codesS c ++ rest)) .C
              (bsyms v')) .CH [.neg]) .L (entryL l ++ S .L))
            (by funext k; cases k <;> simp [hl, marks_succ, entryOf_code])
          have h2 := skipRest_exits c (Function.update (Function.update (Function.update
              (Function.update (Function.update S .LC (marks c.length)) .F (codesS c ++ rest)) .C
              (bsyms v')) .CH [.neg]) .L (entryL l ++ S .L)) rest (by simp) (by simp) (by simp)
            (by simp [hS.G]) (by simp [hS.K])
          refine ((loop_exitsLE_cons _ _ (by simp [hl, marks_succ]) hb' h2).mono ?_).congr ?_
          · simp only [codesS_cons, List.length_append]
            omega
          · funext k; cases k <;> simp [selectLit, selMark, selEntry, bsyms]
      | false =>
          have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.LC S 0)
            (dispatch_exitsLE (Γ := VAlpha) .CH chH _ .pos [] (by simp [hc])
              (dispatch_exitsLE (Γ := VAlpha) .C certH _ .neg (bsyms v') (by simp [hC, bsyms, b2s])
                (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.CH [Sym.pos] _ 0)
                  (skipFrame_exits (Computability.encodeNat l.toNat) _ (codesS c ++ rest) (by simp [hF'])
                    (by simp [hS.G])
                    (by simp [hS.K])))))
          have hb' := hb.congr (T := Function.update (Function.update (Function.update S .LC
              (marks c.length)) .F (codesS c ++ rest)) .C (bsyms v'))
            (by funext k; cases k <;> simp [hl, hc, marks_succ])
          have h2 := ih (Function.update (Function.update (Function.update S .LC
              (marks c.length)) .F (codesS c ++ rest)) .C (bsyms v')) v' rest (by simp) (by simp)
            (by simp [hc]) (by simp) (by simp at hv; omega)
            ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
              by simp [hS.Z]⟩
          refine ((loop_exitsLE_cons _ _ (by simp [hl, marks_succ]) hb' h2).mono ?_).congr ?_
          · simp only [codesS_cons, List.length_append]
            omega
          · funext k; cases k <;> simp [selectLit]

/-! ### One clause -/

/-- Record a failure when no literal was selected. -/
def endH : Sym → VR
  | .pos => bad
  | _ => skip

/-- Process one clause. -/
def clauseSat : VR :=
  seq (seq readLen (seq (pushList .CH [.pos]) (loop .LC litStep))) (dispatch .CH endH)

theorem clauseS_eq (c : Clause ℕ) : clauseS c = frameS (Computability.encodeNat c.length) ++ codesS c :=
  rfl

theorem selectLit_rest (c : Clause ℕ) : ∀ v, v.length ≤ (selectLit c v).2.length + c.length := by
  induction c with
  | nil => intro v; simp [selectLit]
  | cons l c ih =>
      intro v
      unfold selectLit
      split_ifs
      · simp; omega
      · have := ih (v.drop 1); simp at this ⊢; omega

/-- The common prefix of a clause run: length, marker, literal loop. -/
theorem clausePre_exits (N : ℕ) (c : Clause ℕ) (hN : c.length ≤ N) (S : VS) (v : List Bool)
    (rest : List Sym) (hF : S .F = clauseS c ++ rest) (hC : S .C = bsyms v)
    (hv : c.length ≤ v.length) (hS : ReadClean S) (hLC : S .LC = []) (hCH : S .CH = [])
    (hU : S .U2 = []) :
    (seq readLen (seq (pushList .CH [.pos]) (loop .LC litStep))).ExitsLE S
      ((clauseS c).length * (5 * N + 40) + 10)
      (Function.update (Function.update (Function.update (Function.update S .F rest) .C
        (bsyms (selectLit c v).2)) .CH [selMark (selectLit c v).1]) .L
        (selEntry (selectLit c v).1 ++ S .L)) := by
  have h1 := readLen_exits c.length S (codesS c ++ rest) (by rw [hF, clauseS_eq, List.append_assoc])
    hS hLC hU
  have := seq_exitsLE _ _ h1 (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.CH [Sym.pos] _ 0)
    (select_exits c _ v rest (by simp) (by simp) (by simp [hCH]) (by simp [hC]) hv
      ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
        by simp [hS.Z]⟩))
  refine (this.mono ?_).congr ?_
  · have hk : (Computability.encodeNat c.length).length ≤ (clauseS c).length := by
      rw [clauseS_eq, List.length_append, frameS_length]; omega
    have hc : (codesS c).length ≤ (clauseS c).length := by
      rw [clauseS_eq, List.length_append]; omega
    have : (Computability.encodeNat c.length).length * (5 * c.length + 13) ≤
        (clauseS c).length * (5 * N + 13) := Nat.mul_le_mul hk (by omega)
    have e : (clauseS c).length * (5 * N + 40) =
        (clauseS c).length * (5 * N + 13) + 27 * (clauseS c).length := by ring
    simp []
    omega
  · funext k; cases k <;> simp [hLC, hCH, hU]

theorem clauseSome_exits (N : ℕ) (c : Clause ℕ) (hN : c.length ≤ N) (S : VS) (v : List Bool)
    (rest : List Sym) (l : Literal ℕ) (w' : List Bool) (hsel : selectLit c v = (some l, w'))
    (hF : S .F = clauseS c ++ rest) (hC : S .C = bsyms v)
    (hv : c.length ≤ v.length) (hS : ReadClean S) (hLC : S .LC = []) (hCH : S .CH = [])
    (hU : S .U2 = []) :
    clauseSat.ExitsLE S ((clauseS c).length * (5 * N + 40) + 12)
      (Function.update (Function.update (Function.update S .F rest) .C (bsyms w')) .L
        (entryL l ++ S .L)) := by
  have h := clausePre_exits N c hN S v rest hF hC hv hS hLC hCH hU
  rw [hsel] at h
  simp only [selMark, selEntry] at h
  have hd := dispatch_exitsLE (Γ := VAlpha) (n := 1) .CH endH _ .neg [] (by simp)
    (skip_exitsLE (Function.update (Function.update (Function.update (Function.update
      (Function.update S .F rest) .C (bsyms w')) .CH [.neg]) .L (entryL l ++ S .L)) .CH []) 0)
  have := seq_exitsLE _ _ h hd
  refine ((this.mono (by omega)).congr ?_)
  · funext k; cases k <;> simp [hCH]

theorem clauseNone_exits (N : ℕ) (c : Clause ℕ) (hN : c.length ≤ N) (S : VS) (v : List Bool)
    (rest : List Sym) (w' : List Bool) (hsel : selectLit c v = (none, w'))
    (hF : S .F = clauseS c ++ rest) (hC : S .C = bsyms v)
    (hv : c.length ≤ v.length) (hS : ReadClean S) (hLC : S .LC = []) (hCH : S .CH = [])
    (hU : S .U2 = []) :
    clauseSat.ExitsLE S ((clauseS c).length * (5 * N + 40) + 2 * rest.length + 14)
      (Function.update (Function.update (Function.update S .BAD (.mark :: S .BAD)) .F []) .C
        (bsyms w')) := by
  have h := clausePre_exits N c hN S v rest hF hC hv hS hLC hCH hU
  rw [hsel] at h
  simp only [selMark, selEntry, List.nil_append] at h
  have hd := dispatch_exitsLE (Γ := VAlpha) .CH endH _ .pos [] (by simp)
    (bad_exits (Function.update (Function.update (Function.update (Function.update
      (Function.update S .F rest) .C (bsyms w')) .CH [.pos]) .L (S .L)) .CH []))
  have := seq_exitsLE _ _ h hd
  refine ((this.mono (by simp; omega)).congr ?_)
  · funext k; cases k <;> simp [hCH]

/-! ### All clauses -/

theorem clauseLoopSat_exits (N : ℕ) (F : Formula ℕ) (hN : ∀ c ∈ F, c.length ≤ N) :
    ∀ (S : VS) (v : List Bool),
    S .F = F.flatMap clauseS → S .C = bsyms v → (F.map List.length).sum ≤ v.length →
    ReadClean S → S .LC = [] → S .CH = [] → S .U2 = [] →
    (loop .F clauseSat).ExitsLE S (((F.flatMap clauseS).length + F.length) * (5 * N + 54) + 1)
      (Function.update (Function.update (Function.update (Function.update S .F []) .C
        (bsyms (satWalk F v).2.1)) .L (((satWalk F v).1.reverse.flatMap entryL) ++ S .L)) .BAD
        ((if (satWalk F v).2.2 then [] else [.mark]) ++ S .BAD)) := by
  induction F with
  | nil =>
      intro S v hF hC _ _ _ _ _
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.F clauseSat S (by simpa using hF) 0).mono
        (by simp)).congr ?_
      funext k; cases k <;> simp [satWalk, hF, hC]
  | cons c F ih =>
      intro S v hF hC hv hS hLC hCH hU
      have hF' : S .F = clauseS c ++ F.flatMap clauseS := by rw [hF, List.flatMap_cons]
      have hne : S .F ≠ [] := by rw [hF']; simp [clauseS_eq, frameS_eq]
      have hc := hN c (List.mem_cons_self ..)
      have hvc : c.length ≤ v.length := by simp at hv; omega
      have hrest := selectLit_rest c v
      match hsel : selectLit c v with
      | (some l, w') =>
          have h1 := clauseSome_exits N c hc S v _ l w' hsel hF' hC hvc hS hLC hCH hU
          have h2 := ih (fun c' hc' => hN c' (List.mem_cons_of_mem _ hc'))
            (Function.update (Function.update (Function.update S .F (F.flatMap clauseS)) .C
              (bsyms w')) .L (entryL l ++ S .L)) w' (by simp) (by simp)
            (by rw [hsel] at hrest; simp at hv hrest; omega)
            ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
              by simp [hS.Z]⟩ (by simp [hLC]) (by simp [hCH]) (by simp [hU])
          refine ((loop_exitsLE_cons _ _ hne h1 h2).mono ?_).congr ?_
          · simp only [List.flatMap_cons, List.length_append, List.length_cons]
            nlinarith
          · funext k; cases k <;> simp [satWalk, hsel, List.flatMap_append]
      | (none, w') =>
          have h1 := clauseNone_exits N c hc S v _ w' hsel hF' hC hvc hS hLC hCH hU
          have h2 := loop_exitsLE_nil (Γ := VAlpha) VStack.F clauseSat
            (Function.update (Function.update (Function.update S .BAD (.mark :: S .BAD)) .F []) .C
              (bsyms w')) (by simp) 0
          refine ((loop_exitsLE_cons _ _ hne h1 h2).mono ?_).congr ?_
          · simp only [List.flatMap_cons, List.length_append, List.length_cons]
            nlinarith
          · funext k; cases k <;> simp [satWalk, hsel]

/-! ### Walk facts -/

/-- Certificates that read the same with `false` defaults. -/
def SameBits (v w : List Bool) : Prop := ∀ i, v.getD i false = w.getD i false

theorem SameBits.drop1 {v w : List Bool} (h : SameBits v w) : SameBits (v.drop 1) (w.drop 1) := by
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have := h (1 + i)
  simpa [List.getD_eq_getElem?_getD] using this

theorem selectLit_congr (c : Clause ℕ) : ∀ v w, SameBits v w →
    (selectLit c v).1 = (selectLit c w).1 ∧ SameBits (selectLit c v).2 (selectLit c w).2 := by
  induction c with
  | nil => intro v w h; exact ⟨rfl, h⟩
  | cons l c ih =>
      intro v w h
      simp only [selectLit, h 0]
      split_ifs
      · exact ⟨rfl, h.drop1⟩
      · exact ih _ _ h.drop1

theorem satWalk_congr (F : Formula ℕ) : ∀ v w, SameBits v w →
    (satWalk F v).1 = (satWalk F w).1 ∧ (satWalk F v).2.2 = (satWalk F w).2.2 := by
  induction F with
  | nil => intro v w _; exact ⟨rfl, rfl⟩
  | cons c F ih =>
      intro v w h
      obtain ⟨h1, h2⟩ := selectLit_congr c v w h
      unfold satWalk
      match hv : selectLit c v, hw : selectLit c w with
      | (some l, v'), (some l', w') =>
          rw [hv, hw] at h1 h2
          simp only [Option.some.injEq] at h1
          subst h1
          have := ih v' w' h2
          simp [this.1, this.2]
      | (some l, v'), (none, w') => rw [hv, hw] at h1; simp at h1
      | (none, v'), (some l', w') => rw [hv, hw] at h1; simp at h1
      | (none, v'), (none, w') => simp

theorem sameBits_pad (w : List Bool) (N : ℕ) : SameBits (w ++ List.replicate N false) w :=
  getD_pad w N

theorem satWalk_rest_le (F : Formula ℕ) : ∀ v, (satWalk F v).2.1.length ≤ v.length := by
  have hsel : ∀ (c : Clause ℕ) v, (selectLit c v).2.length ≤ v.length := by
    intro c
    induction c with
    | nil => intro v; simp [selectLit]
    | cons l c ih =>
        intro v; unfold selectLit; split_ifs
        · simp
        · exact le_trans (ih _) (by simp)
  induction F with
  | nil => intro v; simp [satWalk]
  | cons c F ih =>
      intro v
      unfold satWalk
      match hs : selectLit c v with
      | (some l, v') =>
          have := hsel c v; rw [hs] at this
          exact le_trans (ih v') this
      | (none, v') =>
          have := hsel c v; rw [hs] at this
          exact this

theorem satWalk_entries_le (F : Formula ℕ) : ∀ v,
    ((satWalk F v).1.flatMap entryL).length ≤ (F.flatMap clauseS).length := by
  induction F with
  | nil => intro v; simp [satWalk]
  | cons c F ih =>
      intro v
      unfold satWalk
      match hs : selectLit c v with
      | (some l, v') =>
          have hl := selectLit_mem c v l v' hs
          have h1 := entryL_le_frame l
          have h2 := frame_le_clauseS c l hl
          have := ih v'
          simp only [List.flatMap_cons, List.length_append]
          omega
      | (none, v') => simp

theorem sum_length_le_clauseS (F : Formula ℕ) : (F.map List.length).sum ≤ (F.flatMap clauseS).length := by
  have hc : ∀ c : Clause ℕ, c.length ≤ (codesS c).length := by
    intro c
    induction c with
    | nil => simp [codesS]
    | cons l c ih => rw [codesS_cons, List.length_append, List.length_cons]; have := frameS_ne (Computability.encodeNat l.toNat); omega
  induction F with
  | nil => simp
  | cons c F ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
      have := hc c
      rw [clauseS_eq, List.length_append] at *
      omega

/-! ### The SAT verifier -/

/-- The SAT verifier routine. -/
def vmainSat : VR :=
  seq split <| seq pad <| seq skipFrame <| seq (loop .F clauseSat) <|
  seq checkPhase <| seq result (drain .C)

theorem result_valueSat (F : Formula ℕ) (w : List Bool) (N : ℕ) :
    (if (((satWalk F (w ++ List.replicate N false)).1.reverse.map fun x =>
        (satWalk F (w ++ List.replicate N false)).1.reverse.countP (conflict x)).sum) = 0 then
      (if (if (satWalk F (w ++ List.replicate N false)).2.2 then 0 else 1) = 0 then true else false)
      else false) = verifySat (F, w) := by
  obtain ⟨h1, h2⟩ := satWalk_congr F _ _ (sameBits_pad w N)
  rw [h1, h2]
  simp only [verifySat]
  cases hok : (satWalk F w).2.2
  · simp
  · by_cases hc : consistent (satWalk F w).1 = true
    · have e1 := (countP_sum_eq_zero (satWalk F w).1.reverse).mpr (by rw [consistent_reverse]; exact hc)
      have e2 := (countP_sum_eq_zero (satWalk F w).1).mpr hc
      simp [e2, hc]
    · have : ¬ ((satWalk F w).1.reverse.map fun x => (satWalk F w).1.reverse.countP (conflict x)).sum
          = 0 := fun h => hc (by rw [← consistent_reverse]; exact (countP_sum_eq_zero _).mp h)
      simp only [this, if_false]
      simp only [Bool.not_eq_true] at hc
      rw [hc]; rfl

theorem vmainSat_exits (F : Formula ℕ) (w : List Bool) :
    vmainSat.ExitsLE (initV ((Formula.encode F).map .inl ++ w.map .inr))
      (vCost ((Formula.encode F).length + w.length)) (outV [verifySat (F, w)]) := by
  set A := Formula.encode F with hA
  set P := bsyms A with hP
  set v := w ++ List.replicate (2 * P.length) false with hv
  have hPe : P = frameS (Computability.encodeNat F.length) ++ F.flatMap clauseS := bsyms_encode F
  have hPlen : P.length = A.length := by simp [hP, bsyms]
  have hFl : F.length ≤ A.length := by
    have := witness_length_le F
    rw [← hA] at this
    omega
  have hframe : 2 * (Computability.encodeNat F.length).length + 1 + (F.flatMap clauseS).length =
      P.length := by rw [hPe, List.length_append, frameS_length]
  have hsumc := sum_length_le_clauseS F
  have hcN : ∀ c ∈ F, c.length ≤ P.length := by
    intro c hc
    have : c.length ≤ (F.map List.length).sum := by
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hc
      simp; omega
    omega
  set Ls := (satWalk F v).1.reverse with hLs
  have hΛ : (Ls.flatMap entryL).length ≤ (F.flatMap clauseS).length := by
    have := satWalk_entries_le F v
    simpa [hLs, List.length_flatMap, List.map_reverse, List.sum_reverse] using this
  have hLsl := length_le_flatMap_entryL Ls
  have hsum := countP_sum_le Ls
  have hrest := satWalk_rest_le F v
  have hvl : v.length = w.length + 2 * P.length := by simp [hv]
  have hbad : (if (satWalk F v).2.2 then [] else [Sym.mark]) ++ ([] : List Sym) =
      marks (if (satWalk F v).2.2 then 0 else 1) := by
    split <;> rfl
  have := seq_exitsLE _ _ (split_exits A w (initV _) rfl rfl rfl rfl rfl)
    (seq_exitsLE _ _ (pad_exits P (bsyms w) _ (by simp [hP]) (by simp) (by simp [initV])
        (by simp [initV]))
      (seq_exitsLE _ _ (skipFrame_exits (Computability.encodeNat F.length) _ (F.flatMap clauseS)
          (by simp; rw [← hP, hPe]) (by simp [initV]) (by simp [initV]))
        (seq_exitsLE _ _ (clauseLoopSat_exits P.length F hcN _ v (by simp) (by simp [hv, bsyms, b2s])
            (by rw [hvl]; omega)
            ⟨by simp [initV], by simp [initV], by simp [initV], by simp [initV], by simp [initV],
              by simp [initV]⟩ (by simp [initV]) (by simp [initV]) (by simp [initV]))
          (seq_exitsLE _ _ (checkPhase_exits Ls _ (by simp [hLs, initV]) (by simp [initV])
              (by simp [initV])
              ⟨by simp [initV], by simp [initV], by simp [initV], by simp [initV], by simp [initV],
                by simp [initV], by simp [initV], by simp [initV], by simp [initV]⟩)
            (seq_exitsLE _ _ (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.out [true] _ 0)
                (seq_exitsLE _ _ (falsify_BAD_exits (if (satWalk F v).2.2 then 0 else 1) _ true
                    (by simp [initV, hbad]) (by simp [initV]))
                  (falsify_CONF_exits ((Ls.map fun x => Ls.countP (conflict x)).sum) _
                    (if (if (satWalk F v).2.2 then 0 else 1) = 0 then true else false)
                    (by simp) (by simp))))
              (drain_exits (Γ := VAlpha) VStack.C _).le)))))
  refine (this.mono ?_).congr ?_
  · simp only [vCost]
    have hc := checkCost_mono (le_trans hΛ (show (F.flatMap clauseS).length ≤ A.length + w.length
      by omega))
    unfold checkCost at hc
    simp [initV, bsyms, hPlen]
    have hb1 : (if (satWalk F v).2.2 then 0 else 1) ≤ 1 := by split <;> omega
    have hs2 : (Ls.map fun x => Ls.countP (conflict x)).sum ≤ (A.length + w.length) ^ 2 := by
      have h1 : Ls.length ≤ A.length + w.length := by omega
      calc _ ≤ Ls.length * Ls.length := hsum
        _ ≤ (A.length + w.length) * (A.length + w.length) := Nat.mul_le_mul h1 h1
        _ = (A.length + w.length) ^ 2 := by ring
    have hEN : (Computability.encodeNat F.length).length ≤ A.length := by omega
    have hΛs : (List.map (fun a => (entryL a).length) Ls).sum = (Ls.flatMap entryL).length := by
      simp [List.length_flatMap]
    have hcs : (List.map (fun a => (clauseS a).length) F).sum = (F.flatMap clauseS).length := by
      simp [List.length_flatMap]
    have hb4 : (if (satWalk F v).2.2 = true then 0 else 4) ≤ 4 := by split <;> omega
    rw [hΛs, hcs]
    have hc' : checkCost (Ls.flatMap entryL).length ≤ 100 * (A.length + w.length + 1) ^ 3 := hc
    set N := A.length + w.length with hN
    have hloop : ((F.flatMap clauseS).length + F.length) * (5 * A.length + 54) ≤
        (2 * N) * (5 * N + 54) := Nat.mul_le_mul (by omega) (by omega)
    have hN2 : N ^ 2 ≤ (N + 1) ^ 3 := by
      calc N ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN3 : (2 * N) * (5 * N + 54) ≤ 118 * (N + 1) ^ 3 := by
      have : (2 * N) * (5 * N + 54) = 10 * N ^ 2 + 108 * N := by ring
      have hN1 : N + 1 ≤ (N + 1) ^ 3 := by
        calc N + 1 = (N + 1) ^ 1 := (pow_one _).symm
          _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hN1 : N + 1 ≤ (N + 1) ^ 3 := by
      calc N + 1 = (N + 1) ^ 1 := (pow_one _).symm
        _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · funext k
    cases k <;> simp [initV, outV]
    have hr := result_valueSat F w (2 * P.length)
    rw [← hv] at hr
    rw [← hLs] at hr
    rw [← hr]
    by_cases h1 : (Ls.map fun x => Ls.countP (conflict x)).sum = 0 <;>
      cases (satWalk F v).2.2 <;> simp [h1]

/-! ### Packaging -/

/-- The SAT verifier machine. -/
noncomputable def machineSat : FinTM2 := toMachine vmainSat .input .out

theorem initList_eqSat (x : List (Bool ⊕ Bool)) : (initList machineSat x).stk = initV x := by
  funext k; cases k <;> rfl

theorem haltList_eqSat (y : List Bool) : (haltList machineSat y).stk = outV y := by
  funext k; cases k <;> rfl

/-- The CNF-SAT verifier runs in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding encodedSAT.encoding EncodedLanguage.certificateEncoding)
      finEncodingBoolBool verifySat where
  tm := machineSat
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := ExactThreeVerify.timePoly
  outputsFun p := by
    rcases p with ⟨F, w⟩
    have run := toMachine_outputsInTime_le vmainSat .input .out
      ((Formula.encode F).map .inl ++ w.map .inr) [verifySat (F, w)] _
      (by
        have h1 := initList_eqSat ((Formula.encode F).map .inl ++ w.map .inr)
        have h2 := haltList_eqSat [verifySat (F, w)]
        simp only [machineSat] at h1 h2
        rw [h1, h2]
        exact vmainSat_exits F w)
    have run' := evalsToInTimeMono run
      (show vCost ((Formula.encode F).length + w.length) ≤
          ExactThreeVerify.timePoly.eval ((Formula.encode F).length + w.length) by
        simp [ExactThreeVerify.timePoly, vCost])
    simpa [Equiv.refl, PairEncoding.finEncoding_encode, finEncodingBoolBool, encodeBool,
      RawBoolList.finEncoding, encodedSAT, Formula.finEncoding] using! run'

/-- The checked polynomial-time verifier for binary CNF-SAT. -/
noncomputable def polytimeVerifier : EncodedLanguage.PolytimeVerifier encodedSAT where
  verify := verifySat
  certificateBound := 2 * X
  sound F w h := verifySat_sound F w h
  complete F h := by
    obtain ⟨w, hw, hv⟩ := verifySat_complete F h
    refine ⟨w, ?_, hv⟩
    simp only [eval_mul, eval_X, eval_ofNat]
    exact hw
  polytime := ⟨computableInPolyTime⟩

/-- Binary CNF-SAT is in NP. -/
theorem encodedSAT_inNP : encodedSAT.InNP := ⟨polytimeVerifier⟩

/-- Cook--Levin: CNF-SAT under the binary encoding is NP-complete. -/
theorem encodedSAT_NPComplete : encodedSAT.NPComplete :=
  ⟨BinaryConvert.encodedSAT_NPHard, encodedSAT_inNP⟩

end LeanNPHardness.SatVerify
