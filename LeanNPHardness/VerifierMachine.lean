import LeanNPHardness.VerifierCheck
import LeanNPHardness.BinaryConvertMachine

/-!
# Exact 3-SAT is NP-complete

The verifier machine splits its paired input, pads the certificate, skips
the formula's clause count, walks the clauses (`clauseLoop_exits`), checks
the selected literals pairwise (`checkPhase_exits`), and writes
`verify (F, w)` on its output stack (`vmain_exits`). It runs within
`2000 * (n + 1) ^ 3` steps on paired inputs of length `n`, so `verify` is a
polynomial-time verifier (`polytimeVerifier`) and binary exact 3-SAT is in
NP (`encodedExactThreeSAT_inNP`). With `BinaryConvert.encodedExactThreeSAT_NPHard`
this gives `encodedExactThreeSAT_NPComplete`.
-/

namespace LeanNPHardness.ExactThreeVerify

open Turing Computability Routines CNF CNF.Unary Polynomial MachinePrimitives
open LeanNPHardness.BinaryConvert (b2s s2b s2b_b2s marks marks_succ marks_zero marks_length
  marks_eq_nil marks_reverse marks_add)

/-! ### The walk -/

theorem walk_ok (F : Formula ℕ) : ∀ v, (walk F v).2.2 = widthOk F := by
  induction F with
  | nil => intro v; rfl
  | cons c F ih =>
      intro v
      by_cases hc : c.length = 3
      · simp [walk, hc, ih, widthOk]
      · simp [walk, hc, widthOk]

theorem walk_chosen (F : Formula ℕ) (h : widthOk F = true) : ∀ v, (walk F v).1 = chosen F v := by
  induction F with
  | nil => intro v; rfl
  | cons c F ih =>
      intro v
      have hc : c.length = 3 := by simpa [widthOk] using (List.all_eq_true.mp h c (by simp))
      have hF : widthOk F = true := by
        simp only [widthOk, List.all_cons, Bool.and_eq_true] at h ⊢; exact h.2
      simp [walk, hc, chosen, ih hF]

theorem chosen_congr (F : Formula ℕ) : ∀ v w : List Bool,
    (∀ i, v.getD i false = w.getD i false) → chosen F v = chosen F w := by
  induction F with
  | nil => intro _ _ _; rfl
  | cons c F ih =>
      intro v w h
      simp only [chosen, h 0, h 1]
      congr 1
      refine ih _ _ fun i => ?_
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
      have := h (2 + i)
      simpa [List.getD_eq_getElem?_getD] using this

theorem getD_pad (w : List Bool) (N i : ℕ) :
    (w ++ List.replicate N false).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := w) (by omega),
      List.getElem?_replicate]
    split <;> rfl

theorem chosen_pad (F : Formula ℕ) (w : List Bool) (N : ℕ) :
    chosen F (w ++ List.replicate N false) = chosen F w :=
  chosen_congr F _ _ (getD_pad w N)

/-! ### Encodings -/

theorem bsyms_encode (F : Formula ℕ) :
    bsyms (Formula.encode F) = frameS (Computability.encodeNat F.length) ++ F.flatMap clauseS := by
  simp only [Formula.encode, BinaryNatLists.encode, BinaryNatLists.encodeNatList,
    Formula.toNatLists, List.length_map, bsyms, List.map_append, List.map_flatMap, frameS,
    List.flatMap_map, BinaryNatLists.encodeNat]
  rfl

theorem frameS_length (bits : List Bool) : (frameS bits).length = 2 * bits.length + 1 := by
  simp [frameS_eq, bsyms]; omega

theorem entryOf_length (bits : List Bool) : (entryOf bits).length ≤ bits.length + 1 := by
  cases bits <;> simp [entryOf, bsyms]

theorem entryL_le_frame (l : Literal ℕ) :
    (entryL l).length ≤ (frameS (Computability.encodeNat l.toNat)).length := by
  rw [← entryOf_code, frameS_length]
  have := entryOf_length (Computability.encodeNat l.toNat)
  omega

theorem frame_le_clauseS (c : Clause ℕ) (l : Literal ℕ) (hl : l ∈ c) :
    (frameS (Computability.encodeNat l.toNat)).length ≤ (clauseS c).length := by
  rw [clauseS, List.length_append]
  have : (frameS (Computability.encodeNat l.toNat)).length ≤
      (c.flatMap fun l => frameS (Computability.encodeNat l.toNat)).length := by
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hl
    simp
    omega
  omega

theorem walk_entries_le (F : Formula ℕ) : ∀ v,
    ((walk F v).1.flatMap entryL).length ≤ (F.flatMap clauseS).length := by
  induction F with
  | nil => intro v; simp [walk]
  | cons c F ih =>
      intro v
      by_cases hc : c.length = 3
      · have h1 := entryL_le_frame (chooseLit c (v.getD 0 false) (v.getD 1 false))
        have h2 := frame_le_clauseS c (chooseLit c (v.getD 0 false) (v.getD 1 false))
          (chooseLit_mem c hc _ _)
        have := ih (v.drop 2)
        simp only [walk, hc, if_true, List.flatMap_cons,
          List.length_append] at this ⊢
        simp only [] at *
        omega
      · simp [walk, hc]

/-! ### The result bit -/

/-- Turn the output bit to `false` once per mark on `BAD`. -/
def falsify_BAD : VR := loop .BAD (seq (popOne .BAD) (seq (popOne .out) (pushList .out [false])))

theorem falsify_BAD_exits (k : ℕ) : ∀ (S : VS) (b : Bool), S .BAD = marks k → S .out = [b] →
    falsify_BAD.ExitsLE S (4 * k + 1)
      (Function.update (Function.update S .BAD []) .out [if k = 0 then b else false]) := by
  induction k with
  | zero =>
      intro S b hq ho
      refine (loop_exitsLE_nil _ _ S (by simp [hq]) 0).congr ?_
      funext k; cases k <;> simp [hq, ho]
  | succ k ih =>
      intro S b hq ho
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.BAD S 0)
        (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.out _ 0)
          (pushList_exitsLE (Γ := VAlpha) VStack.out [false] _ 0))
      have h2 := ih (Function.update (Function.update (Function.update S .BAD (S .BAD).tail) .out
          ((Function.update S .BAD (S .BAD).tail) .out).tail) .out
          ([false] ++ (Function.update (Function.update S .BAD (S .BAD).tail) .out
            ((Function.update S .BAD (S .BAD).tail) .out).tail) .out)) false
        (by simp [hq, marks_succ]) (by simp [ho])
      refine ((loop_exitsLE_cons _ _ (by simp [hq, marks_succ]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp

/-- Turn the output bit to `false` once per mark on `CONF`. -/
def falsify_CONF : VR := loop .CONF (seq (popOne .CONF) (seq (popOne .out) (pushList .out [false])))

theorem falsify_CONF_exits (k : ℕ) : ∀ (S : VS) (b : Bool), S .CONF = marks k → S .out = [b] →
    falsify_CONF.ExitsLE S (4 * k + 1)
      (Function.update (Function.update S .CONF []) .out [if k = 0 then b else false]) := by
  induction k with
  | zero =>
      intro S b hq ho
      refine (loop_exitsLE_nil _ _ S (by simp [hq]) 0).congr ?_
      funext k; cases k <;> simp [hq, ho]
  | succ k ih =>
      intro S b hq ho
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.CONF S 0)
        (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.out _ 0)
          (pushList_exitsLE (Γ := VAlpha) VStack.out [false] _ 0))
      have h2 := ih (Function.update (Function.update (Function.update S .CONF (S .CONF).tail) .out
          ((Function.update S .CONF (S .CONF).tail) .out).tail) .out
          ([false] ++ (Function.update (Function.update S .CONF (S .CONF).tail) .out
            ((Function.update S .CONF (S .CONF).tail) .out).tail) .out)) false
        (by simp [hq, marks_succ]) (by simp [ho])
      refine ((loop_exitsLE_cons _ _ (by simp [hq, marks_succ]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp

/-- Write `true` unless a width failure or a conflict was recorded. -/
def result : VR := seq (pushList .out [true]) (seq falsify_BAD falsify_CONF)

/-! ### The verifier -/

/-- The verifier routine. -/
def vmain : VR :=
  seq split <| seq pad <| seq skipFrame <| seq (loop .F clauseV) <|
  seq checkPhase <| seq result (drain .C)

/-- The initial stacks. -/
def initV (x : List (Bool ⊕ Bool)) : VS
  | .input => x
  | _ => []

/-- The final stacks. -/
def outV (y : List Bool) : VS
  | .out => y
  | _ => []

theorem walk_rest_le (F : Formula ℕ) : ∀ v, (walk F v).2.1.length ≤ v.length := by
  induction F with
  | nil => intro v; simp [walk]
  | cons c F ih =>
      intro v
      by_cases hc : c.length = 3
      · have := ih (v.drop 2); simp [walk, hc] at this ⊢; omega
      · simp [walk, hc]

theorem countP_sum_le (Ls : List (Literal ℕ)) :
    (Ls.map fun x => Ls.countP (conflict x)).sum ≤ Ls.length * Ls.length := by
  have : ∀ M : List (Literal ℕ), (M.map fun x => Ls.countP (conflict x)).sum ≤ M.length * Ls.length := by
    intro M
    induction M with
    | nil => simp
    | cons x M ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        have := List.countP_le_length (p := conflict x) (l := Ls)
        omega
  exact this Ls

theorem consistent_reverse (L : List (Literal ℕ)) : consistent L.reverse = consistent L := by
  rw [Bool.eq_iff_iff, consistent_iff, consistent_iff]
  simp

theorem result_value (F : Formula ℕ) (w : List Bool) (N : ℕ) :
    (if (((walk F (w ++ List.replicate N false)).1.reverse.map fun x =>
        (walk F (w ++ List.replicate N false)).1.reverse.countP (conflict x)).sum) = 0 then
      (if (if (walk F (w ++ List.replicate N false)).2.2 then 0 else 1) = 0 then true else false)
      else false) = verify (F, w) := by
  rw [walk_ok]
  by_cases hw : widthOk F = true
  · rw [walk_chosen F hw, chosen_pad]
    simp only [hw, if_true, verify, Bool.true_and]
    by_cases hc : consistent (chosen F w) = true
    · have := (countP_sum_eq_zero (chosen F w).reverse).mpr (by rw [consistent_reverse]; exact hc)
      have h2 := (countP_sum_eq_zero (chosen F w)).mpr hc
      simp [h2, hc]
    · have : ¬ ((chosen F w).reverse.map fun x => (chosen F w).reverse.countP (conflict x)).sum = 0 :=
        fun h => hc (by rw [← consistent_reverse]; exact (countP_sum_eq_zero _).mp h)
      simp only [this, if_false]
      simp only [Bool.not_eq_true] at hc
      rw [hc]
  · simp only [Bool.not_eq_true] at hw
    simp [hw, verify]

/-- Step bound of the verifier on paired inputs of length `n`. -/
def vCost (n : ℕ) : ℕ := 2000 * (n + 1) ^ 3

theorem checkCost_mono {a b : ℕ} (h : a ≤ b) : checkCost a ≤ checkCost b := by
  unfold checkCost
  have := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3
  omega

theorem vmain_exits (F : Formula ℕ) (w : List Bool) :
    vmain.ExitsLE (initV ((Formula.encode F).map .inl ++ w.map .inr))
      (vCost ((Formula.encode F).length + w.length)) (outV [verify (F, w)]) := by
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
  set Ls := (walk F v).1.reverse with hLs
  have hΛ : (Ls.flatMap entryL).length ≤ (F.flatMap clauseS).length := by
    have := walk_entries_le F v
    simpa [hLs, List.length_flatMap, List.map_reverse, List.sum_reverse] using this
  have hLsl := length_le_flatMap_entryL Ls
  have hsum := countP_sum_le Ls
  have hrest := walk_rest_le F v
  have hvl : v.length = w.length + 2 * P.length := by simp [hv]
  have hbad : (if (walk F v).2.2 then [] else [Sym.mark]) ++ ([] : List Sym) =
      marks (if (walk F v).2.2 then 0 else 1) := by
    split <;> rfl
  have := seq_exitsLE _ _ (split_exits A w (initV _) rfl rfl rfl rfl rfl)
    (seq_exitsLE _ _ (pad_exits P (bsyms w) _ (by simp [hP]) (by simp) (by simp [initV])
        (by simp [initV]))
      (seq_exitsLE _ _ (skipFrame_exits (Computability.encodeNat F.length) _ (F.flatMap clauseS)
          (by simp; rw [← hP, hPe]) (by simp [initV]) (by simp [initV]))
        (seq_exitsLE _ _ (clauseLoop_exits F _ v (by simp) (by simp [hv, bsyms, b2s])
            (by rw [hvl]; omega)
            ⟨by simp [initV], by simp [initV], by simp [initV], by simp [initV], by simp [initV],
              by simp [initV]⟩)
          (seq_exitsLE _ _ (checkPhase_exits Ls _ (by simp [hLs, initV]) (by simp [initV])
              (by simp [initV])
              ⟨by simp [initV], by simp [initV], by simp [initV], by simp [initV], by simp [initV],
                by simp [initV], by simp [initV], by simp [initV], by simp [initV]⟩)
            (seq_exitsLE _ _ (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.out [true] _ 0)
                (seq_exitsLE _ _ (falsify_BAD_exits (if (walk F v).2.2 then 0 else 1) _ true
                    (by simp [initV, hbad]) (by simp [initV]))
                  (falsify_CONF_exits ((Ls.map fun x => Ls.countP (conflict x)).sum) _
                    (if (if (walk F v).2.2 then 0 else 1) = 0 then true else false)
                    (by simp) (by simp))))
              (drain_exits (Γ := VAlpha) VStack.C _).le)))))
  refine (this.mono ?_).congr ?_
  · simp only [vCost]
    have hc := checkCost_mono (le_trans hΛ (show (F.flatMap clauseS).length ≤ A.length + w.length
      by omega))
    unfold checkCost at hc
    simp [initV, bsyms, hPlen]
    have hb1 : (if (walk F v).2.2 then 0 else 1) ≤ 1 := by split <;> omega
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
    have hb4 : (if (walk F v).2.2 = true then 0 else 4) ≤ 4 := by split <;> omega
    rw [hΛs, hcs]
    have hc' : checkCost (Ls.flatMap entryL).length ≤ 100 * (A.length + w.length + 1) ^ 3 := hc
    set N := A.length + w.length with hN
    have hN2 : N ^ 2 ≤ (N + 1) ^ 3 := by
      calc N ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN1 : N + 1 ≤ (N + 1) ^ 3 := by
      calc N + 1 = (N + 1) ^ 1 := (pow_one _).symm
        _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · funext k
    cases k <;> simp [initV, outV]
    have hr := result_value F w (2 * P.length)
    rw [← hv] at hr
    rw [← hLs] at hr
    rw [← hr]
    by_cases h1 : (Ls.map fun x => Ls.countP (conflict x)).sum = 0 <;>
      cases (walk F v).2.2 <;> simp [h1]

/-! ### The verifier as a machine -/

/-- The verifier machine. -/
noncomputable def machine : FinTM2 := toMachine vmain .input .out

theorem initList_eq (x : List (Bool ⊕ Bool)) : (initList machine x).stk = initV x := by
  funext k; cases k <;> rfl

theorem haltList_eq (y : List Bool) : (haltList machine y).stk = outV y := by
  funext k; cases k <;> rfl

/-- The verifier's time polynomial. -/
noncomputable def timePoly : Polynomial ℕ := C 2000 * (X + 1) ^ 3

/-- The exact 3-SAT verifier runs in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding encodedExactThreeSAT.encoding EncodedLanguage.certificateEncoding)
      finEncodingBoolBool verify where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun p := by
    rcases p with ⟨F, w⟩
    have run := toMachine_outputsInTime_le vmain .input .out
      ((Formula.encode F).map .inl ++ w.map .inr) [verify (F, w)] _
      (by
        have h1 := initList_eq ((Formula.encode F).map .inl ++ w.map .inr)
        have h2 := haltList_eq [verify (F, w)]
        simp only [machine] at h1 h2
        rw [h1, h2]
        exact vmain_exits F w)
    have run' := evalsToInTimeMono run
      (show vCost ((Formula.encode F).length + w.length) ≤
          timePoly.eval ((Formula.encode F).length + w.length) by
        simp [timePoly, vCost])
    simpa [Equiv.refl, PairEncoding.finEncoding_encode, finEncodingBoolBool, encodeBool,
      RawBoolList.finEncoding, encodedExactThreeSAT, encodedExactKSAT, Formula.finEncoding] using run'

/-- The checked polynomial-time verifier for binary exact 3-SAT. -/
noncomputable def polytimeVerifier : EncodedLanguage.PolytimeVerifier encodedExactThreeSAT where
  verify := verify
  certificateBound := 2 * X
  sound F w h := verify_sound F w h
  complete F h := by
    obtain ⟨w, hw, hv⟩ := verify_complete F h
    refine ⟨w, ?_, hv⟩
    have := witness_length_le F
    simp only [eval_mul, eval_X, eval_ofNat]
    show w.length ≤ 2 * (Formula.encode F).length
    omega
  polytime := ⟨computableInPolyTime⟩

/-- Binary exact 3-SAT is in NP. -/
theorem encodedExactThreeSAT_inNP : encodedExactThreeSAT.InNP := ⟨polytimeVerifier⟩

/-- Exact 3-SAT under the binary CNF encoding is NP-complete. -/
theorem encodedExactThreeSAT_NPComplete : encodedExactThreeSAT.NPComplete :=
  ⟨BinaryConvert.encodedExactThreeSAT_NPHard, encodedExactThreeSAT_inNP⟩

end LeanNPHardness.ExactThreeVerify
