import LeanNPHardness.MaxCutVerifySpec
import LeanNPHardness.SatVerifyMachine
import LeanNPHardness.MaxCutMachine

/-!
# The Max-Cut verifier machine

The threshold is converted from binary to unary with saturation: a budget
stack `BU` (marks above an `endClause` sentinel) limits every increment of
`LC`, so the conversion costs at most the budget per bit and yields
`min (2K) cap` for `cap = 2|E| + 1` (`readLenSat_exits`). Since any claimed
cut is at most `|E|`, the comparison with `2 * claimedCut` is exact.
Endpoint codes are read into colour-tagged entries (`readKeepC_exits`),
cut edges add two marks to `CNT`, and the shared pairwise check verifies
consistency.
-/

namespace LeanNPHardness.MaxCutVerify

open Turing Computability Routines CNF CNF.Unary Polynomial MachinePrimitives ExactThreeVerify
  MaxCut SatVerify
open LeanNPHardness.BinaryConvert (b2s s2b s2b_b2s marks marks_succ marks_zero marks_length
  marks_eq_nil marks_reverse marks_add bitsOf bitsOf_eq bitsOf_pos encodeNat_odd encodeNat_even)

/-! ### Saturating unary arithmetic -/

/-- Increment `LC` if the budget allows. -/
def satH : Sym → VR
  | .mark => pushList .LC [.mark]
  | .endClause => pushList .BU [.endClause]
  | _ => skip

/-- One saturating increment. -/
def satInc : VR := dispatch .BU satH

theorem satInc_exits (S : VS) (a r : ℕ) (hl : S .LC = marks a)
    (hb : S .BU = marks r ++ [.endClause]) :
    satInc.ExitsLE S 2
      (Function.update (Function.update S .LC (marks (a + min 1 r))) .BU
        (marks (r - min 1 r) ++ [.endClause])) := by
  cases r with
  | zero =>
      refine (dispatch_exitsLE (Γ := VAlpha) .BU satH S .endClause [] (by simp [hb])
        (pushList_exitsLE (Γ := VAlpha) VStack.BU [Sym.endClause] _ 0)).congr ?_
      funext k; cases k <;> simp [hl]
  | succ r =>
      refine (dispatch_exitsLE (Γ := VAlpha) .BU satH S .mark (marks r ++ [.endClause])
        (by simp [hb, marks_succ])
        (pushList_exitsLE (Γ := VAlpha) VStack.LC [Sym.mark] _ 0)).congr ?_
      funext k; cases k <;> simp [hl, marks_succ]

/-- Add the marks of `U2` to `LC`, saturating. -/
def satAdd : VR := loop .U2 (seq (popOne .U2) satInc)

theorem satAdd_exits (c : ℕ) : ∀ (S : VS) (a r : ℕ), S .U2 = marks c → S .LC = marks a →
    S .BU = marks r ++ [.endClause] →
    satAdd.ExitsLE S (4 * c + 1)
      (Function.update (Function.update (Function.update S .U2 []) .LC (marks (a + min c r))) .BU
        (marks (r - min c r) ++ [.endClause])) := by
  induction c with
  | zero =>
      intro S a r hu hl hb
      refine (loop_exitsLE_nil _ _ S (by simp [hu]) 0).congr ?_
      funext k; cases k <;> simp [hu, hl, hb]
  | succ c ih =>
      intro S a r hu hl hb
      have h1 := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.U2 S 0)
        (satInc_exits _ a r (by simp [hl]) (by simp [hb]))
      have h2 := ih (Function.update (Function.update (Function.update S .U2 (S .U2).tail) .LC
          (marks (a + min 1 r))) .BU (marks (r - min 1 r) ++ [.endClause])) (a + min 1 r)
        (r - min 1 r) (by simp [hu, marks_succ]) (by simp) (by simp)
      refine ((loop_exitsLE_cons _ _ (by simp [hu, marks_succ]) h1 h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp
      all_goals first | (congr 1; omega) | (congr 2; omega)

/-- Double `LC`, saturating. -/
def satDouble : VR := seq (copyAll .LC .U2 .scr id id id .mark .mark .mark) satAdd

theorem satDouble_exits (S : VS) (a r : ℕ) (hl : S .LC = marks a)
    (hb : S .BU = marks r ++ [.endClause]) (hu : S .U2 = []) (hs : S .scr = []) :
    satDouble.ExitsLE S (8 * a + 3)
      (Function.update (Function.update S .LC (marks (a + min a r))) .BU
        (marks (r - min a r) ++ [.endClause])) := by
  have := seq_exitsLE _ _ (copyAll_exits (Γ := VAlpha) VStack.LC VStack.U2 VStack.scr id id id
      Sym.mark Sym.mark Sym.mark (by decide) (by decide) (by decide) (fun _ => rfl) S hs).le
    (satAdd_exits a _ a r (by simp [hl, hu]) (by simp [hl]) (by simp [hb]))
  refine (this.mono (by simp [hl]; omega)).congr ?_
  funext k; cases k <;> simp [hu]

/-- Saturating Horner step. -/
def satStep (cap a : ℕ) (b : Bool) : ℕ := min (2 * a + (if b then 1 else 0)) cap

/-- Saturating Horner fold. -/
def satFold (cap : ℕ) : ℕ → List Bool → ℕ
  | a, [] => a
  | a, b :: ms => satFold cap (satStep cap a b) ms

theorem hornerB_mono (ms : List Bool) : ∀ {a a'}, a ≤ a' → hornerB a ms ≤ hornerB a' ms := by
  induction ms with
  | nil => intro a a' h; exact h
  | cons b ms ih => intro a a' h; exact ih (by split <;> omega)

theorem satFold_eq (cap : ℕ) (ms : List Bool) : ∀ a, a ≤ cap →
    satFold cap a ms = min (hornerB a ms) cap := by
  induction ms with
  | nil => intro a ha; simp [satFold, hornerB, ha]
  | cons b ms ih =>
      intro a ha
      simp only [satFold, hornerB]
      rw [ih _ (by unfold satStep; omega)]
      unfold satStep
      by_cases h : 2 * a + (if b then 1 else 0) ≤ cap
      · rw [Nat.min_eq_left h]
      · have hm : min (2 * a + (if b then 1 else 0)) cap = cap := Nat.min_eq_right (by omega)
        rw [hm]
        have h1 := le_hornerB ms cap
        have h2 := le_hornerB ms (2 * a + (if b then 1 else 0))
        omega

/-- One saturating Horner step on a bit symbol. -/
def hornS : Sym → VR
  | .pos => seq satDouble satInc
  | .neg => satDouble
  | _ => skip

theorem hornSLoop_exits (cap : ℕ) (ms : List Bool) : ∀ (S : VS) (a : ℕ), a ≤ cap →
    S .T1 = bsyms ms → S .LC = marks a → S .BU = marks (cap - a) ++ [.endClause] →
    S .U2 = [] → S .scr = [] →
    (loop .T1 (dispatch .T1 hornS)).ExitsLE S (ms.length * (8 * cap + 8) + 1)
      (Function.update (Function.update (Function.update S .T1 []) .LC (marks (satFold cap a ms)))
        .BU (marks (cap - satFold cap a ms) ++ [.endClause])) := by
  induction ms with
  | nil =>
      intro S a ha ht hl hb hu hs
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.T1 (dispatch VStack.T1 hornS) S
        (by simp [ht, bsyms]) 0).mono (by simp)).congr ?_
      funext k; cases k <;> simp [ht, hl, hb, satFold, bsyms]
  | cons b ms ih =>
      intro S a ha ht hl hb hu hs
      have hstep : (hornS (b2s b)).ExitsLE (Function.update S .T1 (bsyms ms)) (8 * cap + 6)
          (Function.update (Function.update (Function.update S .T1 (bsyms ms)) .LC
            (marks (satStep cap a b))) .BU (marks (cap - satStep cap a b) ++ [.endClause])) := by
        have hd := satDouble_exits (Function.update S .T1 (bsyms ms)) a (cap - a) (by simp [hl])
          (by simp [hb]) (by simp [hu]) (by simp [hs])
        have e1 : a + min a (cap - a) = min (2 * a) cap := by omega
        have e2 : cap - a - min a (cap - a) = cap - min (2 * a) cap := by omega
        rw [e1, e2] at hd
        cases b
        · refine (hd.mono (by omega)).congr ?_
          funext k; cases k <;> simp [satStep]
        · have hi := satInc_exits (Function.update (Function.update (Function.update S .T1 (bsyms ms))
              .LC (marks (min (2 * a) cap))) .BU (marks (cap - min (2 * a) cap) ++ [.endClause]))
            (min (2 * a) cap) (cap - min (2 * a) cap) (by simp) (by simp)
          refine ((seq_exitsLE _ _ hd hi).mono (by omega)).congr ?_
          funext k; cases k <;> simp [satStep]
          all_goals first | (congr 1; omega) | (congr 2; omega)
      have h2 := ih (Function.update (Function.update (Function.update S .T1 (bsyms ms)) .LC
          (marks (satStep cap a b))) .BU (marks (cap - satStep cap a b) ++ [.endClause]))
        (satStep cap a b) (by unfold satStep; omega) (by simp) (by simp) (by simp) (by simp [hu])
        (by simp [hs])
      refine ((loop_exitsLE_cons _ _ (by simp [ht, bsyms])
        (dispatch_exitsLE (Γ := VAlpha) .T1 hornS S (b2s b) (bsyms ms) (by simp [ht, bsyms]) hstep)
        h2).mono ?_).congr ?_
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · funext k; cases k <;> simp [satFold]

/-- Read a framed natural from `F` into `LC`, saturating at the budget. -/
def readLenSat : VR :=
  seq (pushList .G [.mark]) <| seq (loop .G (dispatch .F skH)) <| seq moveLoop <|
  loop .T1 (dispatch .T1 hornS)

theorem readLenSat_exits (n cap : ℕ) (S : VS) (rest : List Sym)
    (hF : S .F = frameS (Computability.encodeNat n) ++ rest) (hS : ReadClean S) (hl : S .LC = [])
    (hb : S .BU = marks cap ++ [.endClause]) (hu : S .U2 = []) (hs : S .scr = []) :
    readLenSat.ExitsLE S ((Computability.encodeNat n).length * (8 * cap + 15) + 7)
      (Function.update (Function.update (Function.update S .F rest) .LC (marks (min n cap))) .BU
        (marks (cap - min n cap) ++ [.endClause])) := by
  rw [frameS_eq] at hF
  set bits := Computability.encodeNat n with hbits
  have hv : hval bits = n := hval_encodeNat n
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G [Sym.mark] S 0)
    (seq_exitsLE _ _ (countLoop_exits bits.length _ (bsyms bits ++ rest) 0
        (by simp [hF]) (by simp [hS.G]) (by simp [hS.K]))
      (seq_exitsLE _ _ (moveLoop_exits (bsyms bits) _ rest [] (by simp [bsyms]) (by simp)
          (by simp [hS.T1]))
        (hornSLoop_exits cap bits.reverse _ 0 (Nat.zero_le _) (by simp [bsyms, List.map_reverse])
          (by simp [hl]) (by simp [hb]) (by simp [hu]) (by simp [hs]))))
  rw [satFold_eq cap _ 0 (Nat.zero_le _), hornerB_reverse, hv] at this
  refine (this.mono ?_).congr ?_
  · simp [bsyms]
    have : bits.length * (8 * cap + 8) + bits.length * 7 = bits.length * (8 * cap + 15) := by ring
    omega
  · funext k; cases k <;> simp [hS.G, hS.K, hS.T1]

/-! ### Colour-tagged entries -/

/-- Emit the polarity terminator `term b` for the first bit, keep the rest. -/
def firstHC (b : Bool) (_ : Sym) : VR :=
  seq (pushList .L [term b]) (seq (popOne .Z) (moveAll .T2 .T3 id .mark))

/-- Push the entry of the bits on `T2`, terminated by `term b`. -/
def emitEntryC (b : Bool) : VR :=
  seq (pushList .Z [.mark]) <| seq (loop .T2 (dispatch .T2 (firstHC b))) <|
  seq (loop .Z (seq (popOne .Z) (pushList .L [term b]))) (moveAll .T3 .L id .mark)

/-- The colour-tagged entry of a code. -/
def entryOfC (b : Bool) : List Bool → List Sym
  | [] => [term b]
  | _ :: r => bsyms r ++ [term b]

theorem emitEntryC_exits (b : Bool) (bits : List Bool) (S : VS) (h2 : S .T2 = bsyms bits)
    (h3 : S .T3 = []) (hZ : S .Z = []) :
    (emitEntryC b).ExitsLE S (5 * bits.length + 12)
      (Function.update (Function.update S .T2 []) .L (entryOfC b bits ++ S .L)) := by
  cases bits with
  | nil =>
      have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.Z [Sym.mark] S 0)
        (seq_exitsLE _ _ (loop_exitsLE_nil (Γ := VAlpha) VStack.T2 (dispatch .T2 (firstHC b)) _
            (by simp [h2, bsyms]) 0)
          (seq_exitsLE _ _ (loop_exitsLE_cons (Γ := VAlpha) VStack.Z
              (seq (popOne VStack.Z) (pushList VStack.L [term b])) (by simp)
              (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.Z _ 0)
                (pushList_exitsLE (Γ := VAlpha) VStack.L [term b] _ 0))
              (loop_exitsLE_nil (Γ := VAlpha) VStack.Z
                (seq (popOne VStack.Z) (pushList VStack.L [term b])) _ (by simp [hZ]) 0))
            (moveAll_exits (Γ := VAlpha) VStack.T3 VStack.L (by decide) id Sym.mark _).le))
      refine (this.mono (by simp [h3])).congr ?_
      funext k; cases k <;> simp [h2, h3, hZ, entryOfC, bsyms]
  | cons c r =>
      have hf : (firstHC b (b2s c)).ExitsLE
          (Function.update (Function.update S .Z ([Sym.mark] ++ S .Z)) .T2 (bsyms r))
          (2 * r.length + 3)
          (Function.update (Function.update (Function.update (Function.update
            (Function.update S .Z []) .T2 []) .T3 ((bsyms r).reverse)) .L
            (term b :: S .L)) .T2 []) := by
        have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.L [term b]
            (Function.update (Function.update S .Z ([Sym.mark] ++ S .Z)) .T2 (bsyms r)) 0)
          (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.Z _ 0)
            (moveAll_exits (Γ := VAlpha) VStack.T2 VStack.T3 (by decide) id Sym.mark _).le)
        refine (this.mono (by simp [bsyms]; omega)).congr ?_
        funext k; cases k <;> simp [hZ, h3, bsyms]
      have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.Z [Sym.mark] S 0)
        (seq_exitsLE _ _ (loop_exitsLE_cons (Γ := VAlpha) VStack.T2 _ (by simp [h2, bsyms])
            (dispatch_exitsLE (Γ := VAlpha) .T2 (firstHC b) _ (b2s c) (bsyms r)
              (by simp [h2, bsyms]) hf)
            (loop_exitsLE_nil (Γ := VAlpha) VStack.T2 (dispatch VStack.T2 (firstHC b)) _ (by simp) 0))
          (seq_exitsLE _ _ (loop_exitsLE_nil (Γ := VAlpha) VStack.Z
              (seq (popOne VStack.Z) (pushList VStack.L [term b])) _ (by simp) 0)
            (moveAll_exits (Γ := VAlpha) VStack.T3 VStack.L (by decide) id Sym.mark _).le))
      refine (this.mono (by simp [bsyms]; omega)).congr ?_
      funext k; cases k <;> simp [h3, hZ, entryOfC, bsyms]

/-- Read a framed code and push its colour-tagged entry. -/
def readKeepC (b : Bool) : VR := seq readBits (emitEntryC b)

theorem readKeepC_exits (b : Bool) (bits : List Bool) (S : VS) (rest : List Sym)
    (hF : S .F = frameS bits ++ rest) (hS : ReadClean S) :
    (readKeepC b).ExitsLE S (14 * bits.length + 20)
      (Function.update (Function.update S .F rest) .L (entryOfC b bits ++ S .L)) := by
  have := seq_exitsLE _ _ (readBits_exits bits S rest hF hS)
    (emitEntryC_exits b bits _ (by simp) (by simp [hS.T3]) (by simp [hS.Z]))
  refine (this.mono (by omega)).congr ?_
  funext k; cases k <;> simp [hS.T2]

theorem entryOfC_code (u : ℕ) (b : Bool) :
    entryOfC b (Computability.encodeNat (2 * u)) = entryL (occLit u b) := by
  by_cases hu : u = 0
  · subst hu
    show entryOfC b (Computability.encodeNat 0) = _
    rw [← bitsOf_eq, BinaryConvert.bitsOf_zero]
    cases b <;> simp [entryOfC, entryL, occLit, isNeg, Literal.var, ← bitsOf_eq,
      BinaryConvert.bitsOf_zero, bsyms]
  · rw [encodeNat_even u (by omega)]
    cases b <;> simp [entryOfC, entryL, occLit, isNeg, Literal.var]

/-! ### Clauses of the instance -/

/-- Record a cut edge. -/
def cut2 (s1 s2 : Sym) : VR := if s2b s1 = s2b s2 then skip else pushList .CNT [.mark, .mark]

/-- Process the codes of an edge after its colour bits. -/
def edgeH (s1 s2 : Sym) : VR :=
  seq (readKeepC (s2b s1)) <| seq (readKeepC (s2b s2)) <| seq (cut2 s1 s2) (pushList .BU [.mark, .mark])

/-- Read the two colour bits of an edge. -/
def edgeBody : VR := dispatch .C fun s1 => dispatch .C (edgeH s1)

def d5 : Sym → VR
  | .pos => edgeBody
  | _ => skip
def d4 : Sym → VR
  | .neg => dispatch .F d5
  | _ => skip
def d3 : Sym → VR
  | .neg => dispatch .F d4
  | _ => skip
def t3 : Sym → VR
  | .pos => readLenSat
  | _ => skip
def d2 : Sym → VR
  | .pos => dispatch .F d3
  | .neg => dispatch .F t3
  | _ => skip
def d1 : Sym → VR
  | .pos => dispatch .F d2
  | _ => skip

/-- Process one clause of the instance: an edge or the threshold. -/
def mcClause : VR := dispatch .F d1

/-- The clause of an edge. -/
def edgeCl (e : Edge) : Clause ℕ := [.positive e.1, .positive e.2]

theorem encodeNat_two : Computability.encodeNat 2 = [false, true] := by
  rw [show (2 : ℕ) = 2 * 1 by rfl, encodeNat_even 1 (by omega), show (1 : ℕ) = 2 * 0 + 1 by rfl,
    encodeNat_odd, ← bitsOf_eq, BinaryConvert.bitsOf_zero]

theorem encodeNat_one : Computability.encodeNat 1 = [true] := by
  rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, encodeNat_odd, ← bitsOf_eq, BinaryConvert.bitsOf_zero]

theorem cut2_exits (b1 b2 : Bool) (S : VS) :
    (cut2 (b2s b1) (b2s b2)).ExitsLE S 1
      (Function.update S .CNT (marks (if b1 != b2 then 2 else 0) ++ S .CNT)) := by
  unfold cut2
  by_cases h : b1 = b2
  · subst h
    simp only [s2b_b2s, if_true]
    exact (skip_exitsLE S 0).congr (by funext k; cases k <;> simp)
  · rw [if_neg (by simpa using h)]
    exact (pushList_exitsLE (Γ := VAlpha) VStack.CNT [Sym.mark, Sym.mark] S 0).congr
      (by funext k; cases k <;> simp [h, marks_succ])

theorem edgeClause_exits (e : Edge) (b1 b2 : Bool) (v' : List Bool) (S : VS) (rest : List Sym)
    (hF : S .F = clauseS (edgeCl e) ++ rest) (hC : S .C = bsyms (b1 :: b2 :: v'))
    (hS : ReadClean S) :
    mcClause.ExitsLE S (7 * (clauseS (edgeCl e)).length + 30)
      (Function.update (Function.update (Function.update (Function.update (Function.update S .F rest)
        .C (bsyms v')) .L (entryL (occLit e.2 b2) ++ entryL (occLit e.1 b1) ++ S .L)) .CNT
        (marks (if b1 != b2 then 2 else 0) ++ S .CNT)) .BU (.mark :: .mark :: S .BU)) := by
  set c1 := Computability.encodeNat (2 * e.1)
  set c2 := Computability.encodeNat (2 * e.2)
  have hF' : S .F = Sym.pos :: Sym.pos :: Sym.neg :: Sym.neg :: Sym.pos ::
      (frameS c1 ++ (frameS c2 ++ rest)) := by
    rw [hF, clauseS, edgeCl]
    simp [encodeNat_two, frameS_eq, bsyms, b2s, Literal.toNat, c1, c2]
  have hlen : (clauseS (edgeCl e)).length = 7 + 2 * (c1.length + c2.length) := by
    simp [clauseS, edgeCl, encodeNat_two, frameS_eq, bsyms, Literal.toNat, c1, c2]; omega
  have hk1 := readKeepC_exits b1 c1
    (Function.update (Function.update S .F (frameS c1 ++ (frameS c2 ++ rest))) .C (bsyms v'))
    (frameS c2 ++ rest) (by simp)
    ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
      by simp [hS.Z]⟩
  have hk2 := readKeepC_exits b2 c2 _ rest (by simp)
    (⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
      by simp [hS.Z]⟩ : ReadClean (Function.update (Function.update (Function.update S .F
        (frameS c1 ++ (frameS c2 ++ rest))) .C (bsyms v')) .F (frameS c2 ++ rest) |>
          fun T => Function.update T .L (entryOfC b1 c1 ++ T .L)))
  have hrun := seq_exitsLE _ _ hk1 (seq_exitsLE _ _ hk2 (seq_exitsLE _ _ (cut2_exits b1 b2 _)
    (pushList_exitsLE (Γ := VAlpha) VStack.BU [Sym.mark, Sym.mark] _ 0)))
  have he : edgeH (b2s b1) (b2s b2) = seq (readKeepC b1) (seq (readKeepC b2)
      (seq (cut2 (b2s b1) (b2s b2)) (pushList .BU [.mark, .mark]))) := by
    simp [edgeH]
  rw [← he] at hrun
  have hrun' := hrun.mono (show _ ≤ 14 * c1.length + 14 * c2.length + 42 by omega)
  refine Routine.ExitsLE.mono (n := 14 * c1.length + 14 * c2.length + 42 + 6 + 1) ?_
    (by rw [hlen]; omega)
  refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42 + 6) .F d1 S
    .pos (Sym.pos :: Sym.neg :: Sym.neg :: Sym.pos :: (frameS c1 ++ (frameS c2 ++ rest))) hF' ?_
  · refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42 + 5) .F d2 _
      .pos (Sym.neg :: Sym.neg :: Sym.pos :: (frameS c1 ++ (frameS c2 ++ rest))) (by simp) ?_
    refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42 + 4) .F d3 _
      .neg (Sym.neg :: Sym.pos :: (frameS c1 ++ (frameS c2 ++ rest))) (by simp) ?_
    refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42 + 3) .F d4 _
      .neg (Sym.pos :: (frameS c1 ++ (frameS c2 ++ rest))) (by simp) ?_
    refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42 + 2) .F d5 _
      .pos (frameS c1 ++ (frameS c2 ++ rest)) (by simp) ?_
    refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42 + 1) .C
      (fun s1 => dispatch .C (edgeH s1)) _ (b2s b1) (bsyms (b2 :: v')) (by simp [hC, bsyms]) ?_
    refine dispatch_exitsLE (Γ := VAlpha) (n := 14 * c1.length + 14 * c2.length + 42) .C
      (edgeH (b2s b1)) _ (b2s b2) (bsyms v') (by simp [bsyms]) ?_
    convert hrun' using 1
    · funext k; cases k <;> simp
    · funext k; cases k <;> simp [entryOfC_code, c1, c2, List.append_assoc]

theorem thresholdClause_exits (K cap : ℕ) (S : VS) (rest : List Sym)
    (hF : S .F = clauseS [.positive K] ++ rest) (hS : ReadClean S) (hl : S .LC = [])
    (hb : S .BU = marks cap ++ [.endClause]) (hu : S .U2 = []) (hs : S .scr = []) :
    mcClause.ExitsLE S ((Computability.encodeNat (2 * K)).length * (8 * cap + 15) + 10)
      (Function.update (Function.update (Function.update S .F rest) .LC (marks (min (2 * K) cap)))
        .BU (marks (cap - min (2 * K) cap) ++ [.endClause])) := by
  have hF' : S .F = Sym.pos :: Sym.neg :: Sym.pos ::
      (frameS (Computability.encodeNat (2 * K)) ++ rest) := by
    rw [hF, clauseS]
    simp [encodeNat_one, frameS_eq, bsyms, b2s, Literal.toNat]
  have hr := readLenSat_exits (2 * K) cap
    (Function.update S .F (frameS (Computability.encodeNat (2 * K)) ++ rest)) rest (by simp)
    ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1], by simp [hS.T2], by simp [hS.T3],
      by simp [hS.Z]⟩ (by simp [hl]) (by simp [hb]) (by simp [hu]) (by simp [hs])
  have h3 := dispatch_exitsLE (Γ := VAlpha) .F t3
    (Function.update (Function.update S .F (Sym.neg :: Sym.pos ::
      (frameS (Computability.encodeNat (2 * K)) ++ rest))) .F
      (Sym.pos :: (frameS (Computability.encodeNat (2 * K)) ++ rest))) .pos
    (frameS (Computability.encodeNat (2 * K)) ++ rest) (by simp)
    (hr.congr (T := _) rfl |>.mono le_rfl |> fun h => by simpa only [update_F_idem] using h)
  have h2 := dispatch_exitsLE (Γ := VAlpha) .F d2
    (Function.update S .F (Sym.neg :: Sym.pos :: (frameS (Computability.encodeNat (2 * K)) ++ rest)))
    .neg (Sym.pos :: (frameS (Computability.encodeNat (2 * K)) ++ rest)) (by simp) h3
  have h1 := dispatch_exitsLE (Γ := VAlpha) .F d1 S .pos
    (Sym.neg :: Sym.pos :: (frameS (Computability.encodeNat (2 * K)) ++ rest)) hF' h2
  refine (h1.mono (by omega)).congr ?_
  funext k; cases k <;> simp

/-! ### The instance's clauses -/

theorem graphLoop_exits (K : ℕ) (G : List Edge) : ∀ (S : VS) (v : List Bool) (r c : ℕ),
    S .F = G.flatMap (fun e => clauseS (edgeCl e)) ++ clauseS [.positive K] →
    S .C = bsyms v → 2 * G.length ≤ v.length → S .LC = [] →
    S .BU = marks r ++ [.endClause] → S .CNT = marks c → ReadClean S → S .U2 = [] →
    S .scr = [] →
    (loop .F mcClause).ExitsLE S
      (7 * (G.flatMap fun e => clauseS (edgeCl e)).length + 31 * G.length +
        (Computability.encodeNat (2 * K)).length * (8 * (r + 2 * G.length) + 15) + 12)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S .F []) .C (bsyms (v.drop (2 * G.length)))) .L
        ((occs G v).reverse.flatMap entryL ++ S .L)) .CNT (marks (c + 2 * claimedCut G v))) .LC
        (marks (min (2 * K) (r + 2 * G.length)))) .BU
        (marks (r + 2 * G.length - min (2 * K) (r + 2 * G.length)) ++ [.endClause])) := by
  induction G with
  | nil =>
      intro S v r c hF hC _ hl hb hc hS hu hs
      have h1 := thresholdClause_exits K r S [] (by simpa using hF) hS hl hb hu hs
      have h2 := loop_exitsLE_nil (Γ := VAlpha) VStack.F mcClause
        (Function.update (Function.update (Function.update S .F []) .LC (marks (min (2 * K) r))) .BU
          (marks (r - min (2 * K) r) ++ [.endClause])) (by simp) 0
      have hne : S .F ≠ [] := by rw [hF]; simp [clauseS, frameS_eq]
      refine ((loop_exitsLE_cons _ _ hne h1 h2).mono (by simp)).congr ?_
      funext k; cases k <;> simp [occs, claimedCut, hC, hc]
  | cons e G ih =>
      intro S v r c hF hC hv hl hb hc hS hu hs
      obtain ⟨b1, b2, v', rfl⟩ : ∃ b1 b2 v', v = b1 :: b2 :: v' := by
        match v, hv with
        | b1 :: b2 :: v', _ => exact ⟨b1, b2, v', rfl⟩
      have hF' : S .F = clauseS (edgeCl e) ++
          (G.flatMap (fun e => clauseS (edgeCl e)) ++ clauseS [.positive K]) := by
        rw [hF, List.flatMap_cons, List.append_assoc]
      have hne : S .F ≠ [] := by rw [hF']; simp [clauseS, frameS_eq]
      have h1 := edgeClause_exits e b1 b2 v' S _ hF' hC hS
      have h2 := ih (Function.update (Function.update (Function.update (Function.update
          (Function.update S .F (G.flatMap (fun e => clauseS (edgeCl e)) ++ clauseS [.positive K]))
          .C (bsyms v')) .L (entryL (occLit e.2 b2) ++ entryL (occLit e.1 b1) ++ S .L)) .CNT
          (marks (if b1 != b2 then 2 else 0) ++ S .CNT)) .BU (.mark :: .mark :: S .BU))
        v' (r + 2) (c + if b1 != b2 then 2 else 0) (by simp) (by simp)
        (by simp at hv; try omega) (by simp [hl]) (by simp [hb, marks_succ])
        (by simp [hc, ← marks_add, Nat.add_comm]) ⟨by simp [hS.G], by simp [hS.K], by simp [hS.T1],
          by simp [hS.T2], by simp [hS.T3], by simp [hS.Z]⟩ (by simp [hu]) (by simp [hs])
      refine ((loop_exitsLE_cons _ _ hne h1 h2).mono ?_).congr ?_
      · simp only [List.flatMap_cons, List.length_append, List.length_cons]
        rw [show r + 2 + 2 * G.length = r + 2 * (G.length + 1) by ring]
        omega
      · have hd : (b1 :: b2 :: v').drop (2 * (G.length + 1)) = v'.drop (2 * G.length) := by
          rw [show 2 * (G.length + 1) = 2 * G.length + 1 + 1 by ring]; rfl
        have hr2 : r + 2 + 2 * G.length = r + 2 * (G.length + 1) := by ring
        funext k; cases k <;> simp [occs, claimedCut, List.reverse_cons, List.flatMap_append,
          List.append_assoc, hd, hr2]
        all_goals first | rfl | (congr 1; omega) | (congr 2; omega) |
          (congr 1; split <;> simp_all <;> omega)

/-! ### Comparison and result -/

/-- Subtract the cut marks from the threshold marks. -/
def compare : VR := loop .CNT (seq (popOne .CNT) (popOne .LC))

theorem compare_exits (c : ℕ) : ∀ (S : VS) (a : ℕ), S .CNT = marks c → S .LC = marks a →
    compare.ExitsLE S (3 * c + 1)
      (Function.update (Function.update S .CNT []) .LC (marks (a - c))) := by
  induction c with
  | zero =>
      intro S a hc hl
      refine (loop_exitsLE_nil _ _ S (by simp [hc]) 0).congr ?_
      funext k; cases k <;> simp [hc, hl]
  | succ c ih =>
      intro S a hc hl
      have h1 := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.CNT S 0)
        (popOne_exitsLE (Γ := VAlpha) VStack.LC _ 0)
      have h2 := ih (Function.update (Function.update S .CNT (S .CNT).tail) .LC
          ((Function.update S .CNT (S .CNT).tail) .LC).tail) (a - 1)
        (by simp [hc, marks_succ]) (by simp [hl, marks])
      refine ((loop_exitsLE_cons _ _ (by simp [hc, marks_succ]) h1 h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp
      congr 1; omega

/-- Turn the output bit to `false` if marks remain on `LC`. -/
def falsify_LC : VR := loop .LC (seq (popOne .LC) (seq (popOne .out) (pushList .out [false])))

theorem falsify_LC_exits (k : ℕ) : ∀ (S : VS) (b : Bool), S .LC = marks k → S .out = [b] →
    falsify_LC.ExitsLE S (4 * k + 1)
      (Function.update (Function.update S .LC []) .out [if k = 0 then b else false]) := by
  induction k with
  | zero =>
      intro S b hq ho
      refine (loop_exitsLE_nil _ _ S (by simp [hq]) 0).congr ?_
      funext k; cases k <;> simp [hq, ho]
  | succ k ih =>
      intro S b hq ho
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.LC S 0)
        (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.out _ 0)
          (pushList_exitsLE (Γ := VAlpha) VStack.out [false] _ 0))
      have h2 := ih (Function.update (Function.update (Function.update S .LC (S .LC).tail) .out
          ((Function.update S .LC (S .LC).tail) .out).tail) .out
          ([false] ++ (Function.update (Function.update S .LC (S .LC).tail) .out
            ((Function.update S .LC (S .LC).tail) .out).tail) .out)) false
        (by simp [hq, marks_succ]) (by simp [ho])
      refine ((loop_exitsLE_cons _ _ (by simp [hq, marks_succ]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp

/-- Write `true` unless a conflict was found or the threshold exceeds the cut. -/
def resultMC : VR := seq (pushList .out [true]) (seq falsify_CONF falsify_LC)

/-! ### The verifier -/

/-- The Max-Cut verifier routine. -/
def vmainMC : VR :=
  seq split <| seq pad <| seq skipFrame <| seq (pushList .BU [.mark, .endClause]) <|
  seq (loop .F mcClause) <| seq checkPhase <| seq compare <| seq resultMC <|
  seq (drain .C) (drain .BU)

theorem occs_congr (G : List Edge) : ∀ v w : List Bool, SameBits v w →
    occs G v = occs G w ∧ claimedCut G v = claimedCut G w := by
  induction G with
  | nil => intro _ _ _; exact ⟨rfl, rfl⟩
  | cons e G ih =>
      intro v w h
      have h2 : SameBits (v.drop 2) (w.drop 2) := by
        have := h.drop1.drop1
        simpa [List.drop_drop] using this
      obtain ⟨i1, i2⟩ := ih _ _ h2
      simp only [occs, claimedCut, h 0, h 1, i1, i2]
      simp

theorem claimedCut_le (G : List Edge) : ∀ v, claimedCut G v ≤ G.length := by
  induction G with
  | nil => intro v; rfl
  | cons e G ih => intro v; have := ih (v.drop 2); simp only [claimedCut, List.length_cons]; split <;> omega

theorem entryL_occ_le (u : ℕ) (b : Bool) :
    (entryL (occLit u b)).length ≤ (frameS (Computability.encodeNat (2 * u))).length := by
  rw [← entryOfC_code, frameS_length]
  cases h : Computability.encodeNat (2 * u) <;> simp [entryOfC, bsyms] <;> omega

theorem occs_entries_le (G : List Edge) : ∀ v,
    ((occs G v).flatMap entryL).length ≤ (G.flatMap fun e => clauseS (edgeCl e)).length := by
  induction G with
  | nil => intro v; simp [occs]
  | cons e G ih =>
      intro v
      have h1 := entryL_occ_le e.1 (v.getD 0 false)
      have h2 := entryL_occ_le e.2 (v.getD 1 false)
      have := ih (v.drop 2)
      simp only [occs, List.flatMap_cons, List.length_append, clauseS, edgeCl, Literal.toNat]
        at this ⊢
      simp only [List.flatMap_nil, List.append_nil] at *
      omega

theorem edges_le (G : List Edge) : G.length ≤ (G.flatMap fun e => clauseS (edgeCl e)).length := by
  induction G with
  | nil => simp
  | cons e G ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : 1 ≤ (clauseS (edgeCl e)).length := by
        rw [clauseS, List.length_append]; have := frameS_ne (Computability.encodeNat (edgeCl e).length)
        omega
      omega

theorem bsyms_encode_graph (G : List Edge) (K : ℕ) :
    bsyms (Formula.encode (graphFormula G K)) =
      frameS (Computability.encodeNat (G.length + 1)) ++
        (G.flatMap fun e => clauseS (edgeCl e)) ++ clauseS [.positive K] := by
  rw [bsyms_encode]
  simp [graphFormula, List.flatMap_append, List.flatMap_map, edgeCl, List.append_assoc]

/-- Step bound of the Max-Cut verifier. -/
def vCostMC (n : ℕ) : ℕ := 3000 * (n + 1) ^ 3

theorem result_valueMC (G : List Edge) (K : ℕ) (w : List Bool) (N : ℕ) :
    (if min (2 * K) (1 + 2 * G.length) - (0 + 2 * claimedCut G (w ++ List.replicate N false)) = 0
      then (if (((occs G (w ++ List.replicate N false)).reverse.map fun x =>
          (occs G (w ++ List.replicate N false)).reverse.countP (conflict x)).sum) = 0
        then true else false)
      else false) = verifyMC ((G, K), w) := by
  obtain ⟨h1, h2⟩ := occs_congr G _ _ (sameBits_pad w N)
  rw [h1, h2]
  have hle := claimedCut_le G w
  simp only [verifyMC]
  have e : (min (2 * K) (1 + 2 * G.length) - (0 + 2 * claimedCut G w) = 0) ↔ K ≤ claimedCut G w := by
    omega
  by_cases hk : K ≤ claimedCut G w
  · rw [if_pos (e.mpr hk)]
    by_cases hc : consistent (occs G w) = true
    · have e1 := (countP_sum_eq_zero (occs G w).reverse).mpr (by rw [consistent_reverse]; exact hc)
      have e2 := (countP_sum_eq_zero (occs G w)).mpr hc
      simp [e2, hc, hk]
    · have : ¬ ((occs G w).reverse.map fun x => (occs G w).reverse.countP (conflict x)).sum = 0 :=
        fun h => hc (by rw [← consistent_reverse]; exact (countP_sum_eq_zero _).mp h)
      simp only [this, if_false]
      simp only [Bool.not_eq_true] at hc
      simp [hc]
  · rw [if_neg (fun h => hk (e.mp h))]
    simp [hk]

theorem vmainMC_exits (G : List Edge) (K : ℕ) (w : List Bool) :
    vmainMC.ExitsLE (initV ((Formula.encode (graphFormula G K)).map .inl ++ w.map .inr))
      (vCostMC ((Formula.encode (graphFormula G K)).length + w.length))
      (outV [verifyMC ((G, K), w)]) := by
  set A := Formula.encode (graphFormula G K) with hA
  set P := bsyms A with hP
  set v := w ++ List.replicate (2 * P.length) false with hv
  set EC := G.flatMap fun e => clauseS (edgeCl e) with hEC
  have hPe : P = frameS (Computability.encodeNat (G.length + 1)) ++ EC ++ clauseS [.positive K] :=
    bsyms_encode_graph G K
  have hPlen : P.length = A.length := by simp [hP, bsyms]
  have hparts : 2 * (Computability.encodeNat (G.length + 1)).length + 1 + EC.length +
      (clauseS [.positive K]).length = P.length := by
    rw [hPe, List.length_append, List.length_append, frameS_length]
  have hKlen : 2 * (Computability.encodeNat (2 * K)).length + 1 ≤ (clauseS [.positive K]).length := by
    simp only [clauseS, List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      frameS_length, Literal.toNat]
    omega
  have hGE : G.length ≤ EC.length := edges_le G
  set Ls := (occs G v).reverse with hLs
  have hΛ : (Ls.flatMap entryL).length ≤ EC.length := by
    have h1 : ((occs G v).flatMap entryL).length ≤ EC.length := occs_entries_le G v
    have h2 : (Ls.flatMap entryL).length = ((occs G v).flatMap entryL).length := by
      simp [hLs, List.length_flatMap, List.map_reverse, List.sum_reverse]
    omega
  have hLsl := length_le_flatMap_entryL Ls
  have hsum := countP_sum_le Ls
  have hcut := claimedCut_le G v
  have hvl : v.length = w.length + 2 * P.length := by simp [hv]
  have hdrop : (v.drop (2 * G.length)).length ≤ v.length := by simp
  have := seq_exitsLE _ _ (split_exits A w (initV _) rfl rfl rfl rfl rfl)
    (seq_exitsLE _ _ (pad_exits P (bsyms w) _ (by simp [hP]) (by simp) (by simp [initV])
        (by simp [initV]))
      (seq_exitsLE _ _ (skipFrame_exits (Computability.encodeNat (G.length + 1)) _
          (EC ++ clauseS [.positive K]) (by simp; rw [← hP, hPe, List.append_assoc]; try rfl)
          (by simp [initV]) (by simp [initV]))
        (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.BU [Sym.mark, Sym.endClause] _ 0)
          (seq_exitsLE _ _ (graphLoop_exits K G _ v 1 0 (by simp [hEC]) (by simp [hv, bsyms, b2s])
              (by rw [hvl]; omega) (by simp [initV]) (by simp [initV, marks]) (by simp [initV])
              ⟨by simp [initV], by simp [initV], by simp [initV], by simp [initV], by simp [initV],
                by simp [initV]⟩ (by simp [initV]) (by simp [initV]))
            (seq_exitsLE _ _ (checkPhase_exits Ls _ (by simp [hLs, initV]) (by simp [initV])
                (by simp [initV])
                ⟨by simp [initV], by simp [initV], by simp [initV], by simp [initV],
                  by simp [initV], by simp [initV], by simp [initV], by simp [initV],
                  by simp [initV]⟩)
              (seq_exitsLE _ _ (compare_exits (0 + 2 * claimedCut G v) _
                  (min (2 * K) (1 + 2 * G.length)) (by simp) (by simp))
                (seq_exitsLE _ _ (seq_exitsLE _ _
                    (pushList_exitsLE (Γ := VAlpha) VStack.out [true] _ 0)
                    (seq_exitsLE _ _ (falsify_CONF_exits
                        ((Ls.map fun x => Ls.countP (conflict x)).sum) _ true (by simp)
                        (by simp [initV]))
                      (falsify_LC_exits (min (2 * K) (1 + 2 * G.length) - (0 + 2 * claimedCut G v)) _
                        (if (Ls.map fun x => Ls.countP (conflict x)).sum = 0 then true else false)
                        (by simp) (by simp))))
                  (seq_exitsLE _ _ (drain_exits (Γ := VAlpha) VStack.C _).le
                    (drain_exits (Γ := VAlpha) VStack.BU _).le))))))))
  refine (this.mono ?_).congr ?_
  · simp only [vCostMC]
    have hc := checkCost_mono (le_trans hΛ (show EC.length ≤ A.length + w.length by omega))
    have hk : (v.drop (2 * G.length)).length = v.length - 2 * G.length := List.length_drop
    simp [initV, bsyms, hPlen]
    set n := A.length + w.length with hn
    have hc2 : checkCost n = 100 * (n + 1) ^ 3 := rfl
    have hΛs : (List.map (fun a => (entryL a).length) Ls).sum = (Ls.flatMap entryL).length := by
      simp [List.length_flatMap]
    have hcs : (List.map (fun a => (clauseS (edgeCl a)).length) G).sum = EC.length := by
      simp [hEC, List.length_flatMap]
    simp only [hΛs, hcs] at *
    have hs2 : (Ls.map fun x => Ls.countP (conflict x)).sum ≤ n ^ 2 := by
      have h1 : Ls.length ≤ n := by omega
      calc _ ≤ Ls.length * Ls.length := hsum
        _ ≤ n * n := Nat.mul_le_mul h1 h1
        _ = n ^ 2 := by ring
    have hK2 : (Computability.encodeNat (2 * K)).length * (8 * (1 + 2 * G.length) + 15) ≤
        n * (16 * n + 23) := Nat.mul_le_mul (by omega) (by omega)
    have hN2 : n ^ 2 ≤ (n + 1) ^ 3 := by
      calc n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN1 : n + 1 ≤ (n + 1) ^ 3 := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hq : n * (16 * n + 23) ≤ 39 * (n + 1) ^ 3 := by
      have : n * (16 * n + 23) = 16 * n ^ 2 + 23 * n := by ring
      omega
    have hmin : min (2 * K) (1 + 2 * G.length) ≤ 1 + 2 * G.length := Nat.min_le_right _ _
    omega
  · funext k
    cases k <;> simp [initV, outV]
    have hr := result_valueMC G K w (2 * P.length)
    rw [← hv] at hr
    rw [← hLs] at hr
    rw [← hr]
    by_cases h1 : (Ls.map fun x => Ls.countP (conflict x)).sum = 0 <;>
      by_cases h2 : min (2 * K) (1 + 2 * G.length) - 2 * claimedCut G v = 0 <;> simp [h1, h2]

/-! ### Packaging -/

/-- The Max-Cut verifier machine. -/
noncomputable def machineMC : FinTM2 := toMachine vmainMC .input .out

theorem initList_eqMC (x : List (Bool ⊕ Bool)) : (initList machineMC x).stk = initV x := by
  funext k; cases k <;> rfl

theorem haltList_eqMC (y : List Bool) : (haltList machineMC y).stk = outV y := by
  funext k; cases k <;> rfl

/-- The verifier's time polynomial. -/
noncomputable def timePolyMC : Polynomial ℕ := C 3000 * (X + 1) ^ 3

/-- The Max-Cut verifier runs in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (PairEncoding.finEncoding encodedMaxCut.encoding EncodedLanguage.certificateEncoding)
      finEncodingBoolBool verifyMC where
  tm := machineMC
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolyMC
  outputsFun q := by
    rcases q with ⟨⟨G, K⟩, w⟩
    have run := toMachine_outputsInTime_le vmainMC .input .out
      ((Formula.encode (graphFormula G K)).map .inl ++ w.map .inr) [verifyMC ((G, K), w)] _
      (by
        have h1 := initList_eqMC ((Formula.encode (graphFormula G K)).map .inl ++ w.map .inr)
        have h2 := haltList_eqMC [verifyMC ((G, K), w)]
        simp only [machineMC] at h1 h2
        rw [h1, h2]
        exact vmainMC_exits G K w)
    have run' := evalsToInTimeMono run
      (show vCostMC ((Formula.encode (graphFormula G K)).length + w.length) ≤
          timePolyMC.eval ((Formula.encode (graphFormula G K)).length + w.length) by
        simp [timePolyMC, vCostMC])
    simpa [Equiv.refl, PairEncoding.finEncoding_encode, finEncodingBoolBool, encodeBool,
      RawBoolList.finEncoding, encodedMaxCut, binaryEncoding] using run'

/-- The checked polynomial-time verifier for binary Max-Cut. -/
noncomputable def polytimeVerifier : EncodedLanguage.PolytimeVerifier encodedMaxCut where
  verify := verifyMC
  certificateBound := 2 * X
  sound p w h := verifyMC_sound p w h
  complete p h := by
    obtain ⟨w, hw, hv⟩ := verifyMC_complete p h
    refine ⟨w, ?_, hv⟩
    simp only [eval_mul, eval_X, eval_ofNat]
    show w.length ≤ 2 * (Formula.encode (graphFormula p.1 p.2)).length
    have h1 := edges_le p.1
    have h2 : (p.1.flatMap fun e => clauseS (edgeCl e)).length ≤
        (bsyms (Formula.encode (graphFormula p.1 p.2))).length := by
      rw [bsyms_encode_graph]; simp only [List.length_append]; omega
    simp only [bsyms, List.length_map] at h2
    omega
  polytime := ⟨computableInPolyTime⟩

/-- Binary Max-Cut is in NP. -/
theorem encodedMaxCut_inNP : encodedMaxCut.InNP := ⟨polytimeVerifier⟩

/-- Max-Cut under the binary encoding is NP-complete. -/
theorem encodedMaxCut_NPComplete : encodedMaxCut.NPComplete :=
  ⟨MaxCutMachine.encodedMaxCut_NPHard, encodedMaxCut_inNP⟩

end LeanNPHardness.MaxCutVerify
