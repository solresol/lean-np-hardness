import LeanNPHardness.MachineRoutineBound
import LeanNPHardness.UnaryCNF
import LeanNPHardness.CNFEncoding
import Mathlib.Tactic.Linarith

/-!
# Unary to framed binary naturals on a stack machine

The converter from the unary CNF encoding to `Formula.finEncoding` works
over the stack family `CStack`: the input and work stacks hold unary CNF
symbols, and the output stack holds bits. Output bits are accumulated in
reverse on `buf` as symbols (`pos` for `true`, `neg` for `false`).

`emitNat` turns `n` marks on `cnt` into the reversed framed binary encoding
`BinaryNatLists.encodeNat n` on `buf`, by repeated halving
(`toBits_exits`), in at most `emitNatCost n` steps (`emitNat_exits`).
-/

namespace LeanNPHardness.BinaryConvert

open Routines CNF.Unary

/-- The converter's stacks. -/
inductive CStack
  | input | out | keep | buf | cl | cl2 | cnt | half | par | bitsA | bitsB | lenS | go | go2 | go3
  deriving DecidableEq, Fintype

/-- The converter's alphabets: bits on the output stack, symbols elsewhere. -/
abbrev CAlpha : CStack → Type
  | .out => Bool
  | _ => Sym

instance : ∀ k, Fintype (CAlpha k)
  | .out => inferInstanceAs (Fintype Bool)
  | .input | .keep | .buf | .cl | .cl2 | .cnt | .half | .par | .bitsA | .bitsB | .lenS | .go | .go2
  | .go3 => inferInstanceAs (Fintype Sym)

instance : ∀ k, DecidableEq (CAlpha k)
  | .out => inferInstanceAs (DecidableEq Bool)
  | .input | .keep | .buf | .cl | .cl2 | .cnt | .half | .par | .bitsA | .bitsB | .lenS | .go | .go2
  | .go3 => inferInstanceAs (DecidableEq Sym)

/-- Routines of the converter. -/
abbrev CR := Routine CAlpha

/-- Converter stacks. -/
abbrev CS := Stacks CAlpha

/-- A unary string of marks. -/
def marks (n : ℕ) : List Sym := List.replicate n .mark

@[simp] theorem marks_zero : marks 0 = [] := rfl
theorem marks_succ (n : ℕ) : marks (n + 1) = .mark :: marks n := rfl
@[simp] theorem marks_length (n : ℕ) : (marks n).length = n := List.length_replicate
@[simp] theorem marks_eq_nil (n : ℕ) : marks n = [] ↔ n = 0 := List.replicate_eq_nil_iff _
@[simp] theorem marks_reverse (n : ℕ) : (marks n).reverse = marks n := List.reverse_replicate
@[simp] theorem map_id_marks (n : ℕ) : (marks n).map id = marks n := List.map_id _
theorem marks_add (a b : ℕ) : marks (a + b) = marks a ++ marks b := by
  rw [marks, marks, marks, List.replicate_add]

/-- Bits as symbols. -/
def b2s : Bool → Sym
  | true => .pos
  | false => .neg

/-- Symbols as bits. -/
def s2b : Sym → Bool
  | .pos => true
  | _ => false

@[simp] theorem s2b_b2s (b : Bool) : s2b (b2s b) = b := by cases b <;> rfl

/-! ### Binary digits -/

/-- Little-endian binary digits, as mathlib's `encodeNat`. -/
def bitsOf (n : ℕ) : List Bool :=
  if h : n = 0 then [] else (n % 2 = 1) :: bitsOf (n / 2)
termination_by n
decreasing_by omega

theorem bitsOf_zero : bitsOf 0 = [] := by rw [bitsOf]; simp

theorem bitsOf_pos (n : ℕ) (hn : n ≠ 0) : bitsOf n = decide (n % 2 = 1) :: bitsOf (n / 2) := by
  rw [bitsOf]; simp [hn]

theorem encodeNat_odd (n : ℕ) :
    Computability.encodeNat (2 * n + 1) = true :: Computability.encodeNat n := by
  unfold Computability.encodeNat
  have : Num.ofNat' (2 * n + 1) = Num.bit1 (Num.ofNat' n) := by
    have := Num.ofNat'_bit true n
    simpa [Nat.bit] using this
  show Computability.encodeNum (Num.ofNat' (2 * n + 1)) = true :: Computability.encodeNum (Num.ofNat' n)
  rw [this]
  cases Num.ofNat' n <;> rfl

theorem encodeNat_even (n : ℕ) (hn : 0 < n) :
    Computability.encodeNat (2 * n) = false :: Computability.encodeNat n := by
  unfold Computability.encodeNat
  have : Num.ofNat' (2 * n) = Num.bit0 (Num.ofNat' n) := by
    have := Num.ofNat'_bit false n
    simpa [Nat.bit] using this
  show Computability.encodeNum (Num.ofNat' (2 * n)) = false :: Computability.encodeNum (Num.ofNat' n)
  rw [this]
  cases h : Num.ofNat' n with
  | zero =>
      have : n = 0 := by
        have := congrArg (fun m : Num => (m : ℕ)) h
        simpa [Num.ofNat'_eq] using this
      omega
  | pos p => rfl

theorem bitsOf_eq (n : ℕ) : bitsOf n = Computability.encodeNat n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      by_cases h0 : n = 0
      · subst h0
        rw [bitsOf_zero]
        show [] = Computability.encodeNum ((0 : ℕ) : Num)
        rw [Nat.cast_zero]
        rfl
      · rw [bitsOf_pos n h0, ih (n / 2) (by omega)]
        rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
        · rw [encodeNat_even m (by omega)]
          simp
        · rw [encodeNat_odd m]
          simp [show (2 * m + 1) / 2 = m by omega]

theorem bitsOf_length_le (n : ℕ) : (bitsOf n).length ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      by_cases h0 : n = 0
      · subst h0; simp [bitsOf_zero]
      · rw [bitsOf_pos n h0, List.length_cons]
        have := ih (n / 2) (by omega)
        omega

/-! ### Halving -/

/-- The parity marker: `pos` for even, `neg` for odd. -/
def parSym (p : ℕ) : Sym := if p = 0 then .pos else .neg

/-- Toggle the parity, counting completed pairs on `half`. -/
def halfH : Sym → CR
  | .pos => pushList .par [.neg]
  | .neg => seq (pushList .par [.pos]) (pushList .half [.mark])
  | _ => skip

/-- Consume one mark of `cnt`, toggling the parity. -/
def halfStep : CR := dispatch .cnt fun _ => dispatch .par halfH

theorem halfLoop_exits (m : ℕ) : ∀ (h p : ℕ) (S : CS), p < 2 → S .cnt = marks m →
    S .half = marks h → S .par = [parSym p] →
    (loop .cnt halfStep).ExitsLE S (5 * m + 1)
      (Function.update (Function.update (Function.update S .cnt []) .half
        (marks (h + (p + m) / 2))) .par [parSym ((p + m) % 2)]) := by
  induction m with
  | zero =>
      intro h p S hp hc hh hpar
      refine (loop_exitsLE_nil _ _ S hc 0).congr ?_
      funext k
      cases k <;> simp [hc, hh, hpar, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
  | succ m ih =>
      intro h p S hp hc hh hpar
      have hc' : S .cnt = .mark :: marks m := by rw [hc, marks_succ]
      rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
      · -- even: toggle to odd
        have hb : halfStep.ExitsLE S 3
            (Function.update (Function.update S .cnt (marks m)) .par [parSym 1]) := by
          refine dispatch_exitsLE (Γ := CAlpha) .cnt _ S .mark (marks m) hc' ?_
          refine dispatch_exitsLE (Γ := CAlpha) .par halfH _ .pos [] (by simp [hpar, parSym]) ?_
          refine (pushList_exitsLE (Γ := CAlpha) CStack.par [Sym.neg] _ 0).congr ?_
          funext k; cases k <;> simp [parSym]
        have := ih h 1 (Function.update (Function.update S .cnt (marks m)) .par [parSym 1])
          (by omega) (by simp) (by simp [hh]) (by simp)
        refine (loop_exitsLE_cons _ _ (by simp [hc']) hb this).mono (by omega) |>.congr ?_
        funext k
        cases k <;> simp <;> (congr 1; omega)
      · -- odd: toggle to even and count a pair
        have hb : halfStep.ExitsLE S 4
            (Function.update (Function.update (Function.update S .cnt (marks m)) .par [parSym 0])
              .half (marks (h + 1))) := by
          refine dispatch_exitsLE (Γ := CAlpha) .cnt _ S .mark (marks m) hc' ?_
          refine dispatch_exitsLE (Γ := CAlpha) .par halfH _ .neg [] (by simp [hpar, parSym]) ?_
          refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.par [Sym.pos] _ 0)
            (pushList_exitsLE (Γ := CAlpha) CStack.half [Sym.mark] _ 0)).congr ?_
          funext k; cases k <;> simp [parSym, hh, marks_succ]
        have := ih (h + 1) 0 (Function.update (Function.update (Function.update S .cnt (marks m))
          .par [parSym 0]) .half (marks (h + 1))) (by omega) (by simp) (by simp) (by simp)
        refine (loop_exitsLE_cons _ _ (by simp [hc']) hb this).mono (by omega) |>.congr ?_
        funext k
        cases k <;> simp <;> (congr 1; omega)

/-! ### Extracting the bits -/

/-- Record the low bit from the parity marker. -/
def bitH : Sym → CR
  | .pos => pushList .bitsA [.neg]
  | .neg => pushList .bitsA [.pos]
  | _ => skip

theorem bitH_exits (r : ℕ) (hr : r < 2) (S : CS) :
    (bitH (parSym r)).ExitsLE S 1
      (Function.update S .bitsA ([b2s (decide (r = 1))] ++ S .bitsA)) := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · exact pushList_exitsLE (Γ := CAlpha) CStack.bitsA [Sym.neg] S 0
  · exact pushList_exitsLE (Γ := CAlpha) CStack.bitsA [Sym.pos] S 0

/-- One halving round: halve `cnt`, record the low bit, count the bit. -/
def outerBody : CR :=
  seq (pushList .par [.pos]) <| seq (loop .cnt halfStep) <| seq (dispatch .par bitH) <|
  seq (pushList .lenS [.mark]) (moveAll .half .cnt id .mark)

theorem outerBody_exits (m l : ℕ) (A : List Sym) (S : CS) (hc : S .cnt = marks m)
    (hh : S .half = []) (hp : S .par = []) (hA : S .bitsA = A) (hl : S .lenS = marks l) :
    outerBody.ExitsLE S (6 * m + 7)
      (Function.update (Function.update (Function.update S .cnt (marks (m / 2))) .bitsA
        (b2s (decide (m % 2 = 1)) :: A)) .lenS (marks (l + 1))) := by
  have h1 : (pushList (Γ := CAlpha) CStack.par [Sym.pos]).ExitsLE S 1
      (Function.update S .par [parSym 0]) :=
    (pushList_exitsLE (Γ := CAlpha) CStack.par [Sym.pos] S 0).congr (by simp [hp, parSym])
  have h2 := halfLoop_exits m 0 0 (Function.update S .par [parSym 0]) (by omega)
    (by simp [hc]) (by simp [hh]) (by simp)
  have := seq_exitsLE _ _ h1 (seq_exitsLE _ _ h2 (seq_exitsLE _ _
    (dispatch_exitsLE (Γ := CAlpha) .par bitH _ (parSym ((0 + m) % 2)) [] (by simp)
      (bitH_exits _ (Nat.mod_lt _ (by norm_num)) _))
    (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.lenS [Sym.mark] _ 0)
      (moveAll_exits (Γ := CAlpha) CStack.half CStack.cnt (by decide) id Sym.mark _).le)))
  refine (this.mono ?_).congr ?_
  · simp
    omega
  · funext k
    cases k <;> simp [hA, hl, marks_succ, hh, hp]

/-- Repeated halving: the bits of `cnt`, least significant first. -/
def toBits : CR := loop .cnt outerBody

theorem toBits_exits (m : ℕ) : ∀ (l : ℕ) (A : List Sym) (S : CS), S .cnt = marks m →
    S .half = [] → S .par = [] → S .bitsA = A → S .lenS = marks l →
    toBits.ExitsLE S (20 * (m + 1) ^ 2)
      (Function.update (Function.update (Function.update S .cnt []) .bitsA
        (((bitsOf m).map b2s).reverse ++ A)) .lenS (marks (l + (bitsOf m).length))) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro l A S hc hh hp hA hl
      by_cases h0 : m = 0
      · subst h0
        refine (loop_exitsLE_nil _ _ S (by simp [hc]) _).congr ?_
        funext k
        cases k <;> simp [hc, hA, hl, bitsOf_zero]
      · have h1 := outerBody_exits m l A S hc hh hp hA hl
        have h2 := ih (m / 2) (by omega) (l + 1) (b2s (decide (m % 2 = 1)) :: A)
          (Function.update (Function.update (Function.update S .cnt (marks (m / 2))) .bitsA
            (b2s (decide (m % 2 = 1)) :: A)) .lenS (marks (l + 1)))
          (by simp) (by simp [hh]) (by simp [hp]) (by simp) (by simp)
        have hq : m / 2 + 1 ≤ m := by omega
        have hq2 : (m / 2 + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hq 2
        refine ((loop_exitsLE_cons _ _ (by simp [hc, h0]) h1 h2).mono ?_).congr ?_
        · nlinarith
        · funext k
          cases k <;> simp [bitsOf_pos m h0, List.reverse_cons, List.append_assoc] <;>
            (congr 1; omega)

/-! ### Framing -/

/-- Push `true` symbols counted by `lenS` onto `buf`. -/
def emitTrues : CR := loop .lenS (seq (popOne .lenS) (pushList .buf [.pos]))

theorem emitTrues_exits (K : ℕ) : ∀ S : CS, S .lenS = marks K →
    emitTrues.ExitsLE S (3 * K + 1)
      (Function.update (Function.update S .lenS []) .buf (List.replicate K .pos ++ S .buf)) := by
  induction K with
  | zero =>
      intro S hl
      refine (loop_exitsLE_nil _ _ S (by simp [hl]) 0).congr ?_
      funext k; cases k <;> simp [hl]
  | succ K ih =>
      intro S hl
      have hb := seq_exitsLE _ _ (popOne_exitsLE (Γ := CAlpha) CStack.lenS S 0)
        (pushList_exitsLE (Γ := CAlpha) CStack.buf [Sym.pos] _ 0)
      have h2 := ih (Function.update (Function.update S .lenS (S .lenS).tail) .buf
        ([.pos] ++ Function.update S .lenS (S .lenS).tail .buf)) (by simp [hl, marks_succ])
      refine ((loop_exitsLE_cons _ _ (by simp [hl, marks_succ]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp [List.replicate_succ']

/-- The framed binary encoding as symbols. -/
def frameSyms (n : ℕ) : List Sym := (BinaryNatLists.encodeNat n).map b2s

theorem frameSyms_eq (n : ℕ) :
    frameSyms n = List.replicate (bitsOf n).length .pos ++ .neg :: (bitsOf n).map b2s := by
  simp [frameSyms, BinaryNatLists.encodeNat, BinaryNatLists.frame, bitsOf_eq, b2s]

/-- Emit the framed binary encoding of the marks on `cnt`, reversed, onto `buf`. -/
def emitNat : CR :=
  seq toBits <| seq emitTrues <| seq (pushList .buf [.neg]) <|
  seq (moveAll .bitsA .bitsB id .mark) (moveAll .bitsB .buf id .mark)

/-- Step bound of `emitNat`. -/
def emitNatCost (n : ℕ) : ℕ := 20 * (n + 1) ^ 2 + 7 * n + 4

theorem emitNat_exits (n : ℕ) (S : CS) (hc : S .cnt = marks n) (hh : S .half = [])
    (hp : S .par = []) (hA : S .bitsA = []) (hB : S .bitsB = []) (hl : S .lenS = []) :
    emitNat.ExitsLE S (emitNatCost n)
      (Function.update (Function.update S .cnt []) .buf ((frameSyms n).reverse ++ S .buf)) := by
  have h1 := toBits_exits n 0 [] S hc hh hp hA (by simp [hl])
  have hK := bitsOf_length_le n
  have := seq_exitsLE _ _ h1 (seq_exitsLE _ _ (emitTrues_exits (bitsOf n).length _ (by simp))
    (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.buf [Sym.neg] _ 0)
      (seq_exitsLE _ _
        (moveAll_exits (Γ := CAlpha) CStack.bitsA CStack.bitsB (by decide) id Sym.mark _).le
        (moveAll_exits (Γ := CAlpha) CStack.bitsB CStack.buf (by decide) id Sym.mark _).le)))
  refine (this.mono ?_).congr ?_
  · simp [emitNatCost, hB]
    omega
  · funext k
    cases k <;> simp [hh, hp, hA, hB, hl, frameSyms_eq, List.reverse_append, List.append_assoc]

end LeanNPHardness.BinaryConvert
