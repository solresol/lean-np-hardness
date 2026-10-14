import LeanNPHardness.ExactThreeVerifySpec
import LeanNPHardness.BinaryConvertNat

/-!
# The exact 3-SAT verifier machine: stacks and frame parsing

The verifier runs over the stack family `VStack`: the input holds tagged
formula and certificate bits, the output a single bit, and every other
stack unary CNF symbols (bits as `pos`/`neg`). This file proves the
generic parsing pieces: splitting the input (`split_exits`), padding the
certificate with `false` bits (`pad_exits`), skipping a framed natural
(`skipFrame_exits`), and reading a framed literal code into a normalized
entry (`readKeep_exits`).
-/

namespace LeanNPHardness.ExactThreeVerify

open Routines CNF CNF.Unary
open LeanNPHardness.BinaryConvert (b2s s2b s2b_b2s marks marks_succ marks_zero marks_length
  marks_eq_nil marks_reverse bitsOf bitsOf_eq bitsOf_pos)

/-- The verifier's stacks. -/
inductive VStack
  | input | out | F | C | T1 | T2 | T3 | K | G | G2 | Z | L | LK | SC | X | X2 | XC | Y | Y2
  | BAD | CONF | scr | LC | CH | U2
  deriving DecidableEq, Fintype

/-- Alphabets: tagged bits on the input, a bit on the output, symbols elsewhere. -/
abbrev VAlpha : VStack → Type
  | .input => Bool ⊕ Bool
  | .out => Bool
  | _ => Sym

instance : ∀ k, Fintype (VAlpha k)
  | .input => inferInstanceAs (Fintype (Bool ⊕ Bool))
  | .out => inferInstanceAs (Fintype Bool)
  | .F | .C | .T1 | .T2 | .T3 | .K | .G | .G2 | .Z | .L | .LK | .SC | .X | .X2 | .XC | .Y | .Y2
  | .BAD | .CONF | .scr | .LC | .CH | .U2 => inferInstanceAs (Fintype Sym)

instance : ∀ k, DecidableEq (VAlpha k)
  | .input => inferInstanceAs (DecidableEq (Bool ⊕ Bool))
  | .out => inferInstanceAs (DecidableEq Bool)
  | .F | .C | .T1 | .T2 | .T3 | .K | .G | .G2 | .Z | .L | .LK | .SC | .X | .X2 | .XC | .Y | .Y2
  | .BAD | .CONF | .scr | .LC | .CH | .U2 => inferInstanceAs (DecidableEq Sym)

/-- Verifier routines. -/
abbrev VR := Routine VAlpha

/-- Verifier stacks. -/
abbrev VS := Stacks VAlpha

/-- Bits as symbols. -/
def bsyms (bits : List Bool) : List Sym := bits.map b2s

/-! ### Splitting the input -/

/-- Route formula bits to `T1` and certificate bits to `T2`. -/
def splitH : Bool ⊕ Bool → VR
  | .inl b => pushList .T1 [b2s b]
  | .inr b => pushList .T2 [b2s b]

theorem splitLoop_exits (x : List (Bool ⊕ Bool)) : ∀ (S : VS) (A B : List Sym),
    S .input = x → S .T1 = A → S .T2 = B →
    (loop .input (dispatch .input splitH)).ExitsLE S (3 * x.length + 1)
      (Function.update (Function.update (Function.update S .input []) .T1
        ((bsyms (x.filterMap Sum.getLeft?)).reverse ++ A)) .T2
        ((bsyms (x.filterMap Sum.getRight?)).reverse ++ B)) := by
  induction x with
  | nil =>
      intro S A B hi ha hb
      refine (loop_exitsLE_nil _ _ S hi 0).congr ?_
      funext k; cases k <;> simp [hi, ha, hb, bsyms]
  | cons s x ih =>
      intro S A B hi ha hb
      cases s with
      | inl b =>
          have hb' := dispatch_exitsLE (Γ := VAlpha) .input splitH S (.inl b) x hi
            (pushList_exitsLE (Γ := VAlpha) VStack.T1 [b2s b] (Function.update S .input x) 0)
          have h2 := ih (Function.update (Function.update S .input x) .T1
            ([b2s b] ++ (Function.update S .input x) .T1)) (b2s b :: A) B (by simp) (by simp [ha])
            (by simp [hb])
          refine ((loop_exitsLE_cons _ _ (by simp [hi]) hb' h2).mono (by simp; omega)).congr ?_
          funext k; cases k <;> simp [bsyms]
      | inr b =>
          have hb' := dispatch_exitsLE (Γ := VAlpha) .input splitH S (.inr b) x hi
            (pushList_exitsLE (Γ := VAlpha) VStack.T2 [b2s b] (Function.update S .input x) 0)
          have h2 := ih (Function.update (Function.update S .input x) .T2
            ([b2s b] ++ (Function.update S .input x) .T2)) A (b2s b :: B) (by simp) (by simp [ha])
            (by simp [hb])
          refine ((loop_exitsLE_cons _ _ (by simp [hi]) hb' h2).mono (by simp; omega)).congr ?_
          funext k; cases k <;> simp [bsyms]

/-- Split the input into the formula bits `F` and certificate bits `C`. -/
def split : VR :=
  seq (loop .input (dispatch .input splitH)) <|
  seq (moveAll .T1 .F id .mark) (moveAll .T2 .C id .mark)

theorem split_exits (a b : List Bool) (S : VS) (hi : S .input = a.map .inl ++ b.map .inr)
    (h1 : S .T1 = []) (h2 : S .T2 = []) (hF : S .F = []) (hC : S .C = []) :
    split.ExitsLE S (6 * (a.length + b.length) + 3)
      (Function.update (Function.update (Function.update S .input []) .F (bsyms a)) .C
        (bsyms b)) := by
  have hl : (a.map Sum.inl ++ b.map Sum.inr : List (Bool ⊕ Bool)).filterMap Sum.getLeft? = a := by
    simp [List.filterMap_append, List.filterMap_map, Function.comp_def]
  have hr : (a.map Sum.inl ++ b.map Sum.inr : List (Bool ⊕ Bool)).filterMap Sum.getRight? = b := by
    simp [List.filterMap_append, List.filterMap_map, Function.comp_def]
  have := seq_exitsLE _ _ (splitLoop_exits _ S [] [] hi h1 h2)
    (seq_exitsLE _ _ (moveAll_exits (Γ := VAlpha) VStack.T1 VStack.F (by decide) id Sym.mark _).le
      (moveAll_exits (Γ := VAlpha) VStack.T2 VStack.C (by decide) id Sym.mark _).le)
  rw [hl, hr] at this
  refine (this.mono ?_).congr ?_
  · simp [bsyms]; omega
  · funext k; cases k <;> simp [hF, hC, h1, h2, bsyms]

/-! ### Padding the certificate -/

/-- Keep a formula symbol and add two `false` padding bits. -/
def padH (s : Sym) : VR := seq (pushList .T2 [s]) (pushList .T1 [.neg, .neg])

theorem padLoop_exits (P : List Sym) : ∀ (S : VS) (A B : List Sym),
    S .F = P → S .T2 = A → S .T1 = B →
    (loop .F (dispatch .F padH)).ExitsLE S (4 * P.length + 1)
      (Function.update (Function.update (Function.update S .F []) .T2 (P.reverse ++ A)) .T1
        (List.replicate (2 * P.length) .neg ++ B)) := by
  induction P with
  | nil =>
      intro S A B hF ha hb
      refine (loop_exitsLE_nil _ _ S hF 0).congr ?_
      funext k; cases k <;> simp [hF, ha, hb]
  | cons s P ih =>
      intro S A B hF ha hb
      have hb' := dispatch_exitsLE (Γ := VAlpha) .F padH S s P hF
        (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.T2 [s] (Function.update S .F P) 0)
          (pushList_exitsLE (Γ := VAlpha) VStack.T1 [Sym.neg, Sym.neg] _ 0))
      have h2 := ih (Function.update (Function.update (Function.update S .F P) .T2
          ([s] ++ (Function.update S .F P) .T2)) .T1
          ([Sym.neg, Sym.neg] ++ (Function.update (Function.update S .F P) .T2
            ([s] ++ (Function.update S .F P) .T2)) .T1)) (s :: A) (.neg :: .neg :: B)
        (by simp) (by simp [ha]) (by simp [hb])
      refine ((loop_exitsLE_cons _ _ (by simp [hF]) hb' h2).mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp
      rw [show 2 * (P.length + 1) = 2 * P.length + 1 + 1 by omega, List.replicate_succ',
        List.replicate_succ']
      simp

/-- Append `2 * |F|` `false` bits to the certificate. -/
def pad : VR :=
  seq (moveAll .C .T1 id .mark) <| seq (loop .F (dispatch .F padH)) <|
  seq (moveAll .T2 .F id .mark) (moveAll .T1 .C id .mark)

theorem pad_exits (P Q : List Sym) (S : VS) (hF : S .F = P) (hC : S .C = Q) (h1 : S .T1 = [])
    (h2 : S .T2 = []) :
    pad.ExitsLE S (10 * P.length + 4 * Q.length + 4)
      (Function.update S .C (Q ++ List.replicate (2 * P.length) .neg)) := by
  have := seq_exitsLE _ _ (moveAll_exits (Γ := VAlpha) VStack.C VStack.T1 (by decide) id Sym.mark S).le
    (seq_exitsLE _ _ (padLoop_exits P _ [] (Q.reverse) (by simp [hF]) (by simp [h2])
        (by simp [hC, h1]))
      (seq_exitsLE _ _ (moveAll_exits (Γ := VAlpha) VStack.T2 VStack.F (by decide) id Sym.mark _).le
        (moveAll_exits (Γ := VAlpha) VStack.T1 VStack.C (by decide) id Sym.mark _).le))
  refine (this.mono ?_).congr ?_
  · simp [hC]; omega
  · funext k; cases k <;> simp [hF, h1, h2]

/-! ### Framed naturals -/

/-- The symbols of a framed bit string. -/
def frameS (bits : List Bool) : List Sym := bsyms (BinaryNatLists.frame bits)

theorem frameS_eq (bits : List Bool) :
    frameS bits = List.replicate bits.length .pos ++ .neg :: bsyms bits := by
  simp [frameS, BinaryNatLists.frame, bsyms, b2s]

/-- Count leading `pos` symbols of `F` onto `K`; the `neg` separator stops. -/
def skH : Sym → VR
  | .pos => pushList .K [.mark]
  | .neg => popOne .G
  | _ => skip

theorem countLoop_exits (k : ℕ) : ∀ (S : VS) (rest : List Sym) (c : ℕ),
    S .F = List.replicate k .pos ++ .neg :: rest → S .G = [.mark] → S .K = marks c →
    (loop .G (dispatch .F skH)).ExitsLE S (3 * k + 4)
      (Function.update (Function.update (Function.update S .F rest) .G []) .K
        (marks (c + k))) := by
  induction k with
  | zero =>
      intro S rest c hF hG hK
      have hb := dispatch_exitsLE (Γ := VAlpha) .F skH S .neg rest (by simpa using hF)
        (popOne_exitsLE (Γ := VAlpha) VStack.G (Function.update S .F rest) 0)
      refine ((loop_exitsLE_cons _ _ (by simp [hG]) hb
        (loop_exitsLE_nil (Γ := VAlpha) VStack.G (dispatch .F skH) _ (by simp [hG]) 0)).mono
          (by omega)).congr ?_
      funext k; cases k <;> simp [hG, hK]
  | succ k ih =>
      intro S rest c hF hG hK
      have hF' : S .F = .pos :: (List.replicate k .pos ++ .neg :: rest) := by
        rw [hF, List.replicate_succ, List.cons_append]
      have hb := dispatch_exitsLE (Γ := VAlpha) .F skH S .pos _ hF'
        (pushList_exitsLE (Γ := VAlpha) VStack.K [Sym.mark]
          (Function.update S .F (List.replicate k Sym.pos ++ Sym.neg :: rest)) 0)
      have h2 := ih (Function.update (Function.update S .F
          (List.replicate k Sym.pos ++ Sym.neg :: rest))
          .K ([Sym.mark] ++ (Function.update S .F (List.replicate k Sym.pos ++ Sym.neg :: rest)) .K))
        rest (c + 1) (by simp) (by simp [hG]) (by simp [hK, marks_succ])
      refine ((loop_exitsLE_cons _ _ (by simp [hG]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp
      congr 1; omega

/-- Pop as many symbols from `F` as there are marks on `K`. -/
def popLoop : VR := loop .K (seq (popOne .K) (popOne .F))

theorem popLoop_exits (P : List Sym) : ∀ (S : VS) (rest : List Sym),
    S .K = marks P.length → S .F = P ++ rest →
    popLoop.ExitsLE S (3 * P.length + 1)
      (Function.update (Function.update S .K []) .F rest) := by
  induction P with
  | nil =>
      intro S rest hK hF
      refine (loop_exitsLE_nil _ _ S (by simp [hK]) 0).congr ?_
      funext k; cases k <;> simp [hK, hF]
  | cons s P ih =>
      intro S rest hK hF
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.K S 0)
        (popOne_exitsLE (Γ := VAlpha) VStack.F _ 0)
      have h2 := ih (Function.update (Function.update S .K (S .K).tail) .F
          ((Function.update S .K (S .K).tail) .F).tail) rest
        (by simp [hK, marks_succ]) (by simp [hF])
      refine ((loop_exitsLE_cons _ _ (by simp [hK, marks_succ]) hb h2).mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp

/-- Skip one framed natural on `F`. -/
def skipFrame : VR := seq (pushList .G [.mark]) (seq (loop .G (dispatch .F skH)) popLoop)

theorem skipFrame_exits (bits : List Bool) (S : VS) (rest : List Sym)
    (hF : S .F = frameS bits ++ rest) (hG : S .G = []) (hK : S .K = []) :
    skipFrame.ExitsLE S (6 * bits.length + 7) (Function.update S .F rest) := by
  rw [frameS_eq] at hF
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G [Sym.mark] S 0)
    (seq_exitsLE _ _ (countLoop_exits bits.length _ (bsyms bits ++ rest) 0
        (by simp [hF]) (by simp [hG]) (by simp [hK]))
      (popLoop_exits (bsyms bits) _ rest (by simp [bsyms]) (by simp)))
  refine (this.mono (by simp [bsyms]; omega)).congr ?_
  funext k; cases k <;> simp [hG, hK]

/-! ### Reading a literal entry -/

/-- The terminator recording a polarity. -/
def term : Bool → Sym
  | false => .mark
  | true => .endClause

/-- The normalized entry of a code: variable bits, then the polarity terminator. -/
def entryOf : List Bool → List Sym
  | [] => [term false]
  | b :: r => bsyms r ++ [term b]

/-- Move a bit symbol from `F` to `T1`. -/
def mvH (s : Sym) : VR := pushList .T1 [s]

/-- Move as many symbols from `F` to `T1` as there are marks on `K`. -/
def moveLoop : VR := loop .K (seq (popOne .K) (dispatch .F mvH))

theorem moveLoop_exits (P : List Sym) : ∀ (S : VS) (rest A : List Sym),
    S .K = marks P.length → S .F = P ++ rest → S .T1 = A →
    moveLoop.ExitsLE S (4 * P.length + 1)
      (Function.update (Function.update (Function.update S .K []) .F rest) .T1 (P.reverse ++ A)) := by
  induction P with
  | nil =>
      intro S rest A hK hF hA
      refine (loop_exitsLE_nil _ _ S (by simp [hK]) 0).congr ?_
      funext k; cases k <;> simp [hK, hF, hA]
  | cons s P ih =>
      intro S rest A hK hF hA
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.K S 0)
        (dispatch_exitsLE (Γ := VAlpha) .F mvH _ s (P ++ rest) (by simp [hF])
          (pushList_exitsLE (Γ := VAlpha) VStack.T1 [s] _ 0))
      have h2 := ih (Function.update (Function.update (Function.update S .K (S .K).tail) .F
          (P ++ rest)) .T1 ([s] ++ (Function.update (Function.update S .K (S .K).tail) .F
            (P ++ rest)) .T1)) rest (s :: A) (by simp [hK, marks_succ]) (by simp) (by simp [hA])
      refine ((loop_exitsLE_cons _ _ (by simp [hK, marks_succ]) hb h2).mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp

/-- Emit the first bit as the polarity terminator and keep the rest on `T3`. -/
def firstH (s : Sym) : VR :=
  seq (pushList .L [term (s2b s)]) (seq (popOne .Z) (moveAll .T2 .T3 id .mark))

/-- Empty work stacks for reading. -/
structure ReadClean (S : VS) : Prop where
  G : S .G = []
  K : S .K = []
  T1 : S .T1 = []
  T2 : S .T2 = []
  T3 : S .T3 = []
  Z : S .Z = []

/-- Read the bits of a framed code from `F` onto `T2`, in order. -/
def readBits : VR :=
  seq (pushList .G [.mark]) <| seq (loop .G (dispatch .F skH)) <| seq moveLoop <|
  moveAll .T1 .T2 id .mark

theorem readBits_exits (bits : List Bool) (S : VS) (rest : List Sym)
    (hF : S .F = frameS bits ++ rest) (hS : ReadClean S) :
    readBits.ExitsLE S (9 * bits.length + 7)
      (Function.update (Function.update S .F rest) .T2 (bsyms bits)) := by
  rw [frameS_eq] at hF
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G [Sym.mark] S 0)
    (seq_exitsLE _ _ (countLoop_exits bits.length _ (bsyms bits ++ rest) 0
        (by simp [hF]) (by simp [hS.G]) (by simp [hS.K]))
      (seq_exitsLE _ _ (moveLoop_exits (bsyms bits) _ rest [] (by simp [bsyms]) (by simp)
          (by simp [hS.T1]))
        (moveAll_exits (Γ := VAlpha) VStack.T1 VStack.T2 (by decide) id Sym.mark _).le))
  refine (this.mono (by simp [bsyms]; omega)).congr ?_
  funext k; cases k <;> simp [hS.G, hS.K, hS.T1, hS.T2]

/-- Push the entry of the bits on `T2` onto `L`. -/
def emitEntry : VR :=
  seq (pushList .Z [.mark]) <| seq (loop .T2 (dispatch .T2 firstH)) <|
  seq (loop .Z (seq (popOne .Z) (pushList .L [term false]))) (moveAll .T3 .L id .mark)

theorem emitEntry_exits (bits : List Bool) (S : VS) (h2 : S .T2 = bsyms bits) (h3 : S .T3 = [])
    (hZ : S .Z = []) :
    emitEntry.ExitsLE S (5 * bits.length + 12)
      (Function.update (Function.update S .T2 []) .L (entryOf bits ++ S .L)) := by
  cases bits with
  | nil =>
      have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.Z [Sym.mark] S 0)
        (seq_exitsLE _ _ (loop_exitsLE_nil (Γ := VAlpha) VStack.T2 (dispatch .T2 firstH) _
            (by simp [h2, bsyms]) 0)
          (seq_exitsLE _ _ (loop_exitsLE_cons (Γ := VAlpha) VStack.Z
              (seq (popOne VStack.Z) (pushList VStack.L [term false])) (by simp)
              (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.Z _ 0)
                (pushList_exitsLE (Γ := VAlpha) VStack.L [term false] _ 0))
              (loop_exitsLE_nil (Γ := VAlpha) VStack.Z
                (seq (popOne VStack.Z) (pushList VStack.L [term false])) _ (by simp [hZ]) 0))
            (moveAll_exits (Γ := VAlpha) VStack.T3 VStack.L (by decide) id Sym.mark _).le))
      refine (this.mono (by simp [h3])).congr ?_
      funext k; cases k <;> simp [h2, h3, hZ, entryOf, bsyms]
  | cons b r =>
      have hf : (firstH (b2s b)).ExitsLE
          (Function.update (Function.update S .Z ([Sym.mark] ++ S .Z)) .T2 (bsyms r))
          (2 * r.length + 3)
          (Function.update (Function.update (Function.update (Function.update
            (Function.update S .Z []) .T2 []) .T3 ((bsyms r).reverse)) .L
            (term b :: S .L)) .T2 []) := by
        have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.L [term (s2b (b2s b))]
            (Function.update (Function.update S .Z ([Sym.mark] ++ S .Z)) .T2 (bsyms r)) 0)
          (seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.Z _ 0)
            (moveAll_exits (Γ := VAlpha) VStack.T2 VStack.T3 (by decide) id Sym.mark _).le)
        refine (this.mono (by simp [bsyms]; omega)).congr ?_
        funext k; cases k <;> simp [hZ, h3, bsyms]
      have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.Z [Sym.mark] S 0)
        (seq_exitsLE _ _ (loop_exitsLE_cons (Γ := VAlpha) VStack.T2 _ (by simp [h2, bsyms])
            (dispatch_exitsLE (Γ := VAlpha) .T2 firstH _ (b2s b) (bsyms r) (by simp [h2, bsyms]) hf)
            (loop_exitsLE_nil (Γ := VAlpha) VStack.T2 (dispatch VStack.T2 firstH) _ (by simp) 0))
          (seq_exitsLE _ _ (loop_exitsLE_nil (Γ := VAlpha) VStack.Z
              (seq (popOne VStack.Z) (pushList VStack.L [term false])) _ (by simp) 0)
            (moveAll_exits (Γ := VAlpha) VStack.T3 VStack.L (by decide) id Sym.mark _).le))
      refine (this.mono (by simp [bsyms]; omega)).congr ?_
      funext k; cases k <;> simp [h3, hZ, entryOf, bsyms]

/-- Read a framed code from `F` and push its entry onto `L`. -/
def readKeep : VR := seq readBits emitEntry

theorem readKeep_exits (bits : List Bool) (S : VS) (rest : List Sym)
    (hF : S .F = frameS bits ++ rest) (hS : ReadClean S) :
    readKeep.ExitsLE S (14 * bits.length + 20)
      (Function.update (Function.update S .F rest) .L (entryOf bits ++ S .L)) := by
  have := seq_exitsLE _ _ (readBits_exits bits S rest hF hS)
    (emitEntry_exits bits _ (by simp) (by simp [hS.T3]) (by simp [hS.Z]))
  refine (this.mono (by omega)).congr ?_
  funext k; cases k <;> simp [hS.T2]

end LeanNPHardness.ExactThreeVerify
