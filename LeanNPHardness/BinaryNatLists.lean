import Mathlib.Computability.Encoding

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness

open Computability

namespace BinaryNatLists

/-- A self-delimiting binary frame: unary payload length, a zero separator,
then the payload bits. -/
def frame (bits : List Bool) : List Bool :=
  List.replicate bits.length true ++ false :: bits

/-- A self-delimiting form of mathlib's standard binary natural encoding. -/
def encodeNat (n : ℕ) : List Bool :=
  frame (Computability.encodeNat n)

/-- Read a unary count terminated by `false`. -/
def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readUnary rest
      pure (n + 1, tail)

/-- Read exactly `count` bits, returning the unconsumed suffix. -/
def readBits : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, input => some ([], input)
  | _ + 1, [] => none
  | count + 1, bit :: input => do
      let (bits, rest) ← readBits count input
      pure (bit :: bits, rest)

/-- Decode one framed natural and return the unconsumed suffix. -/
def decodeNatPrefix (input : List Bool) : Option (ℕ × List Bool) := do
  let (count, payload) ← readUnary input
  let (bits, rest) ← readBits count payload
  pure (Computability.decodeNat bits, rest)

@[simp]
theorem readUnary_replicate (count : ℕ) (rest : List Bool) :
    readUnary (List.replicate count true ++ false :: rest) =
      some (count, rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, readUnary, ih]

@[simp]
theorem readBits_append (bits rest : List Bool) :
    readBits bits.length (bits ++ rest) = some (bits, rest) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp [readBits, ih]

@[simp]
theorem decodeNatPrefix_encodeNat_append (n : ℕ) (rest : List Bool) :
    decodeNatPrefix (encodeNat n ++ rest) = some (n, rest) := by
  simp [decodeNatPrefix, encodeNat, frame, List.append_assoc]

/-- Decode exactly `count` framed naturals. -/
def decodeNats : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (n, rest) ← decodeNatPrefix input
      let (ns, tail) ← decodeNats count rest
      pure (n :: ns, tail)

/-- Encode a list of naturals as its binary length and framed elements. -/
def encodeNatList (xs : List ℕ) : List Bool :=
  encodeNat xs.length ++ xs.flatMap encodeNat

/-- Decode a length-prefixed list of naturals. -/
def decodeNatListPrefix (input : List Bool) :
    Option (List ℕ × List Bool) := do
  let (count, rest) ← decodeNatPrefix input
  decodeNats count rest

@[simp]
theorem decodeNats_flatMap_append (xs : List ℕ) (rest : List Bool) :
    decodeNats xs.length (xs.flatMap encodeNat ++ rest) =
      some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [decodeNats, List.append_assoc, ih]

@[simp]
theorem decodeNatListPrefix_encode_append
    (xs : List ℕ) (rest : List Bool) :
    decodeNatListPrefix (encodeNatList xs ++ rest) = some (xs, rest) := by
  simp [decodeNatListPrefix, encodeNatList, List.append_assoc]

/-- Decode exactly `count` binary natural-number lists. -/
def decodeLists : ℕ → List Bool → Option (List (List ℕ) × List Bool)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (xs, rest) ← decodeNatListPrefix input
      let (xss, tail) ← decodeLists count rest
      pure (xs :: xss, tail)

/-- Encode nested natural-number lists using binary length prefixes. -/
def encode (xss : List (List ℕ)) : List Bool :=
  encodeNat xss.length ++ xss.flatMap encodeNatList

/-- Decode a complete nested-list binary string, rejecting trailing bits. -/
def decode (input : List Bool) : Option (List (List ℕ)) := do
  let (count, rest) ← decodeNatPrefix input
  let (xss, tail) ← decodeLists count rest
  if tail = [] then some xss else none

@[simp]
theorem decodeLists_flatMap_append
    (xss : List (List ℕ)) (rest : List Bool) :
    decodeLists xss.length (xss.flatMap encodeNatList ++ rest) =
      some (xss, rest) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
      simp [decodeLists, List.append_assoc, ih]

@[simp]
theorem decode_encode (xss : List (List ℕ)) :
    decode (encode xss) = some xss := by
  have hdecode :
      decodeLists xss.length (xss.flatMap encodeNatList) =
        some (xss, []) := by
    simpa using decodeLists_flatMap_append xss []
  simp [decode, encode, hdecode]

/-- A checked binary `FinEncoding` for nested natural-number lists. -/
def finEncoding : FinEncoding (List (List ℕ)) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

/-- Number of bits used by one framed natural. -/
def natWireSize (n : ℕ) : ℕ :=
  2 * (Computability.encodeNat n).length + 1

/-- Number of bits used by one length-prefixed natural-number list. -/
def listWireSize (xs : List ℕ) : ℕ :=
  natWireSize xs.length + (xs.map natWireSize).sum

/-- Number of bits used by one length-prefixed nested list. -/
def wireSize (xss : List (List ℕ)) : ℕ :=
  natWireSize xss.length + (xss.map listWireSize).sum

@[simp]
theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  simp [frame]
  omega

@[simp]
theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = natWireSize n := by
  simp [encodeNat, natWireSize]

@[simp]
theorem encodeNatList_length (xs : List ℕ) :
    (encodeNatList xs).length = listWireSize xs := by
  simp [encodeNatList, listWireSize, Nat.add_comm]

@[simp]
theorem encode_length (xss : List (List ℕ)) :
    (encode xss).length = wireSize xss := by
  simp [encode, wireSize, Nat.add_comm]

theorem natWireSize_pos (n : ℕ) : 0 < natWireSize n := by
  simp [natWireSize]

/-- The standard natural encoding has exactly its binary digit count. -/
theorem encodeNat_length_eq_size (n : ℕ) :
    (Computability.encodeNat n).length = n.size := by
  have hpos (p : PosNum) :
      (Computability.encodePosNum p).length = p.natSize := by
    induction p <;> simp_all [Computability.encodePosNum, PosNum.natSize]
  have hnum (m : Num) : (Computability.encodeNum m).length = m.natSize := by
    cases m <;> simp [Computability.encodeNum, Num.natSize, hpos]
  simpa [Computability.encodeNat] using
    (hnum (n : Num)).trans (Num.natSize_to_nat (n : Num))

/-- Framed binary size is monotone in the represented natural. -/
theorem natWireSize_mono : Monotone natWireSize := by
  intro m n h
  simp only [natWireSize, encodeNat_length_eq_size]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.size_le_size h)) 1

private theorem encodePosNum_length_le (n : PosNum) :
    (Computability.encodePosNum n).length ≤ (n : ℕ) := by
  induction n with
  | one => simp [Computability.encodePosNum]
  | bit1 n ih =>
      simp only [Computability.encodePosNum, List.length_cons]
      simp only [PosNum.cast_bit1]
      omega
  | bit0 n ih =>
      simp only [Computability.encodePosNum, List.length_cons]
      simp only [PosNum.cast_bit0]
      have hn : 0 < (n : ℕ) := PosNum.cast_pos n
      omega

/-- The standard binary representation of a natural has at most `n` bits.
This deliberately coarse linear estimate is enough for the polynomial output
bound below. -/
theorem encodeNat_length_le (n : ℕ) :
    (Computability.encodeNat n).length ≤ n := by
  rw [Computability.encodeNat]
  cases h : (n : Num) with
  | zero => simp [Computability.encodeNum]
  | pos p =>
      rw [Computability.encodeNum]
      have hp := encodePosNum_length_le p
      have hn : n = (p : ℕ) := by
        have h' := congrArg (fun m : Num => (m : ℕ)) h
        simpa using h'
      simpa [hn] using hp

theorem natWireSize_le_two_mul_add_one (n : ℕ) :
    natWireSize n ≤ 2 * n + 1 := by
  rw [natWireSize]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (encodeNat_length_le n)) 1

theorem sum_natWireSize_le (xs : List ℕ) (bound : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ bound) :
    (xs.map natWireSize).sum ≤ xs.length * (2 * bound + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      calc
        ((x :: xs).map natWireSize).sum =
            natWireSize x + (xs.map natWireSize).sum := by simp
        _ ≤ (2 * bound + 1) + xs.length * (2 * bound + 1) :=
          Nat.add_le_add
            ((natWireSize_le_two_mul_add_one x).trans
              (Nat.add_le_add_right
                (Nat.mul_le_mul_left 2 (hxs x (by simp))) 1))
            (ih fun y hy => hxs y (by simp [hy]))
        _ = (x :: xs).length * (2 * bound + 1) := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem listWireSize_le (xs : List ℕ) (bound : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ bound) :
    listWireSize xs ≤
      (2 * xs.length + 1) + xs.length * (2 * bound + 1) := by
  exact Nat.add_le_add (natWireSize_le_two_mul_add_one xs.length)
    (sum_natWireSize_le xs bound hxs)

/-- A code containing at most four naturals bounded by `bound` has this
uniform framed size bound. -/
theorem listWireSize_le_sixteen (xs : List ℕ) (bound : ℕ)
    (hlength : xs.length ≤ 4) (hxs : ∀ x ∈ xs, x ≤ bound) :
    listWireSize xs ≤ 16 * (bound + 1) := by
  have h := listWireSize_le xs bound hxs
  have hmul : xs.length * (2 * bound + 1) ≤ 4 * (2 * bound + 1) :=
    Nat.mul_le_mul_right (2 * bound + 1) hlength
  omega

theorem sum_listWireSize_le (xss : List (List ℕ)) (bound : ℕ)
    (hlength : ∀ xs ∈ xss, xs.length ≤ 4)
    (hxs : ∀ xs ∈ xss, ∀ x ∈ xs, x ≤ bound) :
    (xss.map listWireSize).sum ≤
      xss.length * (16 * (bound + 1)) := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
      calc
        (((xs :: xss).map listWireSize).sum) =
            listWireSize xs + (xss.map listWireSize).sum := by simp
        _ ≤ (16 * (bound + 1)) +
            xss.length * (16 * (bound + 1)) :=
          Nat.add_le_add
            (listWireSize_le_sixteen xs bound
              (hlength xs (by simp)) (hxs xs (by simp)))
            (ih (fun ys hys => hlength ys (by simp [hys]))
              (fun ys hys => hxs ys (by simp [hys])))
        _ = (xs :: xss).length * (16 * (bound + 1)) := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- A nested code with four-field inner rows and uniformly bounded numeric
fields has a linear-in-row-count wire-size bound. -/
theorem wireSize_le (xss : List (List ℕ)) (bound : ℕ)
    (hlength : ∀ xs ∈ xss, xs.length ≤ 4)
    (hxs : ∀ xs ∈ xss, ∀ x ∈ xs, x ≤ bound) :
    wireSize xss ≤
      (2 * xss.length + 1) +
        xss.length * (16 * (bound + 1)) := by
  exact Nat.add_le_add (natWireSize_le_two_mul_add_one xss.length)
    (sum_listWireSize_le xss bound hlength hxs)

theorem length_le_listWireSize (xs : List ℕ) :
    xs.length ≤ listWireSize xs := by
  have hsum : xs.length ≤ (xs.map natWireSize).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have hx := natWireSize_pos x
        omega
  exact hsum.trans (Nat.le_add_left _ _)

theorem length_le_wireSize (xss : List (List ℕ)) :
    xss.length ≤ wireSize xss := by
  have hsum : xss.length ≤ (xss.map listWireSize).sum := by
    induction xss with
    | nil => simp
    | cons xs xss ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have hxs : 0 < listWireSize xs :=
          (natWireSize_pos xs.length).trans_le (Nat.le_add_right _ _)
        omega
  exact hsum.trans (Nat.le_add_left _ _)

theorem sum_lengths_le_wireSize (xss : List (List ℕ)) :
    (xss.map List.length).sum ≤ wireSize xss := by
  have hsum :
      (xss.map List.length).sum ≤ (xss.map listWireSize).sum := by
    induction xss with
    | nil => simp
    | cons xs xss ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (length_le_listWireSize xs) ih
  exact hsum.trans (Nat.le_add_left _ _)

end BinaryNatLists

end LeanNPHardness
