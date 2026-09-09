import LeanNPHardness.IntervalMachines

/-!
Bounded number-theory components extracted from phd-thesis-lean at 84be78d.
All enumeration, trial-division and prime-selection runtime bounds use the
explicit unary/padded input encodings; no binary-input polynomial bound is
asserted for these algorithms.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition LeanNPHardness.BoundedPrime

/-! ## Unary-padded divisibility

The eventual prime scan works under the full-input invariant `q ≤ s`, where
`s` is the bit length of the explicit CSP.  Consequently every candidate and
trial divisor is at most linear in `s`.  The following paired unary interface
records that padding explicitly.  It is deliberately not a polynomial-time
claim for standalone binary inputs.
-/

namespace UnaryNatPair

/-- Two unary naturals separated by a single false delimiter. -/
def encode (pair : ℕ × ℕ) : List Bool :=
  List.replicate pair.1 true ++ false :: List.replicate pair.2 true

/-- Decoder for the canonical delimiter-separated unary pair syntax. -/
def decodeAux : List Bool → ℕ × ℕ
  | [] => (0, 0)
  | false :: bits => (0, bits.length)
  | true :: bits =>
      let decoded := decodeAux bits
      (decoded.1 + 1, decoded.2)

def decode (input : List Bool) : Option (ℕ × ℕ) :=
  some (decodeAux input)

private theorem decodeAux_replicate (left right : ℕ) :
    decodeAux
        (List.replicate left true ++ false :: List.replicate right true) =
      (left, right) := by
  induction left with
  | zero => simp [decodeAux]
  | succ left ih =>
      simp [List.replicate_succ, decodeAux, ih]

@[simp]
theorem decode_encode (pair : ℕ × ℕ) :
    decode (encode pair) = some pair := by
  rcases pair with ⟨left, right⟩
  simp [decode, encode, decodeAux_replicate]

/-- Checked finite encoding of a unary-padded pair of naturals. -/
def finEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

@[simp]
theorem encode_length (pair : ℕ × ℕ) :
    (encode pair).length = pair.1 + pair.2 + 1 := by
  simp [encode]
  omega

end UnaryNatPair

/-! ## Deterministic trial-division specification

The existing divisibility machine supplies the Boolean test needed for each
pair below.  This section fixes the exact finite computation that the next
machine pass must realize: test every divisor in `[2, n)`, retain exactly the
prime Bertrand candidates, and take the first survivor.  The specification is
executable, but no polynomial-time claim is made merely from these list
definitions.  The unary-pair and aggregate-size bounds expose the padding that
the finite-machine proof will use.
-/

/-- Every possible nontrivial proper divisor of `n`, in increasing order. -/
def trialDivisors (n : ℕ) : List ℕ :=
  List.range' 2 (n - 2)

@[simp]
theorem trialDivisors_length (n : ℕ) :
    (trialDivisors n).length = n - 2 := by
  simp [trialDivisors]

@[simp]
theorem mem_trialDivisors_iff (n d : ℕ) :
    d ∈ trialDivisors n ↔ 2 ≤ d ∧ d < n := by
  simp [trialDivisors]
  omega

/-- Bounded trial division as an executable Boolean predicate. -/
def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (trialDivisors n).all fun d => decide (¬ d ∣ n)

/-- Testing all and only the divisors in `[2, n)` decides natural primality. -/
theorem trialPrime_eq_true_iff (n : ℕ) :
    trialPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_lt']
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro ⟨hn, htrial⟩
    exact ⟨hn, fun d hd2 hdn =>
      htrial d ((mem_trialDivisors_iff n d).2 ⟨hd2, hdn⟩)⟩
  · rintro ⟨hn, hprime⟩
    exact ⟨hn, fun d hd => hprime d
      ((mem_trialDivisors_iff n d).1 hd).1
      ((mem_trialDivisors_iff n d).1 hd).2⟩

/-- The exact sequence of padded divisibility inputs used to test `n`. -/
def trialDivisionPairs (n : ℕ) : List (ℕ × ℕ) :=
  (trialDivisors n).map fun d => (n, d)

@[simp]
theorem trialDivisionPairs_length (n : ℕ) :
    (trialDivisionPairs n).length = n - 2 := by
  simp [trialDivisionPairs]

theorem mem_trialDivisionPairs_iff (n : ℕ) (pair : ℕ × ℕ) :
    pair ∈ trialDivisionPairs n ↔
      pair.1 = n ∧ 2 ≤ pair.2 ∧ pair.2 < n := by
  constructor
  · intro hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact ⟨rfl, (mem_trialDivisors_iff n d).mp hd⟩
  · rintro ⟨hfirst, hd2, hdlt⟩
    exact List.mem_map.mpr ⟨pair.2,
      (mem_trialDivisors_iff n pair.2).mpr ⟨hd2, hdlt⟩,
      Prod.ext hfirst.symm rfl⟩

/-- Each trial pair has unary length at most twice its candidate. -/
theorem unaryPair_length_le_two_mul_of_mem_trialDivisionPairs
    {n : ℕ} {pair : ℕ × ℕ} (hp : pair ∈ trialDivisionPairs n) :
    (UnaryNatPair.encode pair).length ≤ 2 * n := by
  rw [UnaryNatPair.encode_length]
  have h := (mem_trialDivisionPairs_iff n pair).mp hp
  omega

/-- Total unary cells in the complete list of trial pairs for one candidate. -/
def trialDivisionInputSize (n : ℕ) : ℕ :=
  ((trialDivisionPairs n).map fun pair =>
    (UnaryNatPair.encode pair).length).sum

/-- The complete padded trial-division input for one candidate is quadratic. -/
theorem trialDivisionInputSize_le (n : ℕ) :
    trialDivisionInputSize n ≤ 2 * n * (n - 2) := by
  have hsum := List.sum_le_card_nsmul
    ((trialDivisionPairs n).map fun pair =>
      (UnaryNatPair.encode pair).length) (2 * n) (by
        intro length hlength
        obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hlength
        exact unaryPair_length_le_two_mul_of_mem_trialDivisionPairs hpair)
  simpa [trialDivisionInputSize, trialDivisionPairs_length,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- The checked Bertrand interval after deterministic trial-division
filtering. -/
def bertrandPrimeCandidates (q : ℕ) : List ℕ :=
  (bertrandCandidates q).filter trialPrime

theorem pairwise_lt_intervalFrom (count current : ℕ) :
    (intervalFrom count current).Pairwise (· < ·) := by
  induction count generalizing current with
  | zero => simp [intervalFrom]
  | succ count ih =>
      rw [intervalFrom, List.pairwise_cons]
      constructor
      · intro value hvalue
        have hbounds :=
          (mem_intervalFrom_iff value count (current + 1)).mp hvalue
        omega
      · exact ih (current + 1)

theorem pairwise_lt_bertrandPrimeCandidates (q : ℕ) :
    (bertrandPrimeCandidates q).Pairwise (· < ·) := by
  exact (pairwise_lt_intervalFrom q q).filter trialPrime

@[simp]
theorem mem_bertrandPrimeCandidates_iff (q value : ℕ) :
    value ∈ bertrandPrimeCandidates q ↔
      value.Prime ∧ q < value ∧ value ≤ 2 * q := by
  rw [bertrandPrimeCandidates, List.mem_filter]
  rw [trialPrime_eq_true_iff, mem_bertrandCandidates_iff]
  tauto

theorem selectPrimeAbove_mem_bertrandPrimeCandidates
    {q : ℕ} (hq : q ≠ 0) :
    selectPrimeAbove q ∈ bertrandPrimeCandidates q := by
  rw [mem_bertrandPrimeCandidates_iff]
  exact (mem_primeCandidates_iff q (selectPrimeAbove q)).mp
    (selectPrimeAbove_mem_primeCandidates hq)

theorem bertrandPrimeCandidates_ne_nil {q : ℕ} (hq : q ≠ 0) :
    bertrandPrimeCandidates q ≠ [] := by
  intro hempty
  have hmem := selectPrimeAbove_mem_bertrandPrimeCandidates hq
  rw [hempty] at hmem
  simp at hmem

/-- Select the first candidate surviving bounded trial division, with the
same explicit `q = 0` convention as the semantic compiler. -/
def firstBertrandPrime (q : ℕ) : ℕ :=
  if hq : q = 0 then 2
  else (bertrandPrimeCandidates q).head (bertrandPrimeCandidates_ne_nil hq)

@[simp]
theorem firstBertrandPrime_zero : firstBertrandPrime 0 = 2 := by
  simp [firstBertrandPrime]

theorem firstBertrandPrime_mem {q : ℕ} (hq : q ≠ 0) :
    firstBertrandPrime q ∈ bertrandPrimeCandidates q := by
  rw [firstBertrandPrime, dif_neg hq]
  exact List.head_mem _

private theorem head_le_of_pairwise_lt {xs : List ℕ} (hne : xs ≠ [])
    (hsorted : xs.Pairwise (· < ·)) {value : ℕ} (hvalue : value ∈ xs) :
    xs.head hne ≤ value := by
  cases xs with
  | nil => simp at hne
  | cons first rest =>
      rw [List.pairwise_cons] at hsorted
      rcases List.mem_cons.mp hvalue with hfirst | hrest
      · subst value
        exact le_rfl
      · exact (hsorted.1 value hrest).le

/-- The executable first-survivor scan returns exactly the least prime used by
the already checked semantic compiler. -/
theorem firstBertrandPrime_eq_selectPrimeAbove (q : ℕ) :
    firstBertrandPrime q = selectPrimeAbove q := by
  by_cases hq : q = 0
  · subst q
    simp
  · apply Nat.le_antisymm
    · rw [firstBertrandPrime, dif_neg hq]
      exact head_le_of_pairwise_lt (bertrandPrimeCandidates_ne_nil hq)
        (pairwise_lt_bertrandPrimeCandidates q)
        (selectPrimeAbove_mem_bertrandPrimeCandidates hq)
    · rw [selectPrimeAbove, dif_neg hq]
      exact Finset.min'_le (primeCandidates q) (firstBertrandPrime q)
        ((mem_bertrandPrimeCandidates_iff q (firstBertrandPrime q)).mp
          (firstBertrandPrime_mem hq) |>
            (mem_primeCandidates_iff q (firstBertrandPrime q)).mpr)

theorem firstBertrandPrime_prime (q : ℕ) :
    (firstBertrandPrime q).Prime := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_prime q

theorem lt_firstBertrandPrime (q : ℕ) :
    q < firstBertrandPrime q := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact lt_selectPrimeAbove q

theorem firstBertrandPrime_le_two_mul {q : ℕ} (hq : q ≠ 0) :
    firstBertrandPrime q ≤ 2 * q := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_le_two_mul hq

theorem firstBertrandPrime_lt_two_mul {q : ℕ} (hq : 1 < q) :
    firstBertrandPrime q < 2 * q := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_lt_two_mul hq

@[simp]
theorem firstBertrandPrime_one : firstBertrandPrime 1 = 2 := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_one

/-! ## Stack-oriented trial-pair lists

The finite prime filter feeds the existing divisibility checker one unary pair
at a time.  This encoding keeps every complete `UnaryNatPair` payload intact,
reverses both the list of pairs and each payload for stack consumption, and
separates payloads by a symbol outside the Boolean input alphabet.
-/

namespace RawUnaryPairList

/-- Stack-oriented encoding of a list of unary-padded natural pairs. -/
def encode (pairs : List (ℕ × ℕ)) : List (Option Bool) :=
  (pairs.map UnaryNatPair.encode).reverse.flatMap RawNatList.segment

private theorem parseAux_some_append
    (bits : List Bool) (input : List (Option Bool))
    (current : List Bool) (fields : List (List Bool)) :
    RawNatList.parseAux (bits.map some ++ input) current fields =
      RawNatList.parseAux input (bits.reverse ++ current) fields := by
  induction bits generalizing current with
  | nil => simp
  | cons bit bits ih =>
      simp [RawNatList.parseAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseAux_segments
    (segments : List (List Bool)) (fields : List (List Bool)) :
    RawNatList.parseAux
        (segments.flatMap RawNatList.segment) [] fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [RawNatList.parseAux]
  | cons bits segments ih =>
      rw [List.flatMap_cons]
      simp only [RawNatList.segment, List.append_assoc]
      rw [parseAux_some_append]
      simp only [List.reverse_reverse]
      simp only [List.singleton_append, RawNatList.parseAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (pairs : List (ℕ × ℕ)) :
    RawNatList.parse (encode pairs) =
      some (pairs.map UnaryNatPair.encode) := by
  rw [RawNatList.parse, encode, parseAux_segments]
  simp

/-- Decode every complete pair payload in a parsed field list. -/
def decodeFields : List (List Bool) → Option (List (ℕ × ℕ))
  | [] => some []
  | field :: fields => do
      let pair ← UnaryNatPair.decode field
      let pairs ← decodeFields fields
      some (pair :: pairs)

@[simp]
theorem decodeFields_map_encode (pairs : List (ℕ × ℕ)) :
    decodeFields (pairs.map UnaryNatPair.encode) = some pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => simp [decodeFields, ih]

/-- Decode a complete stack-oriented list of unary pairs. -/
def decode (input : List (Option Bool)) : Option (List (ℕ × ℕ)) := do
  let fields ← RawNatList.parse input
  decodeFields fields

@[simp]
theorem decode_encode (pairs : List (ℕ × ℕ)) :
    decode (encode pairs) = some pairs := by
  simp [decode]

/-- Checked finite encoding for a stack-oriented list of padded trial pairs. -/
def finEncoding : FinEncoding (List (ℕ × ℕ)) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end RawUnaryPairList

/-- Input, the unary dividend, the unconsumed and consumed parts of the
divisor, and the Boolean output. -/
inductive DvdStack
  | input
  | dividend
  | remaining
  | used
  | output
  deriving DecidableEq, Fintype

/-- Parsing, cyclic divisor consumption, restoration, decision, and cleanup
phases of the unary divisibility checker. -/
inductive DvdLabel
  | scanDividend
  | scanDivisor
  | start
  | consume
  | restore
  | check
  | finish
  | clearDividend
  | clearRemaining
  | clearUsed
  deriving DecidableEq, Fintype

/-- Finite control stores the most recently observed marker and the decision
bit once it is known. -/
structure DvdState where
  marker : Option Bool
  result : Bool
  deriving DecidableEq, Fintype

def dvdInitialState : DvdState :=
  ⟨none, false⟩

private def dvdObserved
    (state : DvdState) (marker : Option Bool) : DvdState :=
  { state with marker := marker }

private def dvdSetResult (result : Bool) (_state : DvdState) : DvdState :=
  ⟨none, result⟩

private def dvdMarkerPresent : DvdState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def dvdMarkerTrue : DvdState → Bool
  | ⟨some true, _⟩ => true
  | _ => false

private def dvdResult (state : DvdState) : Bool :=
  state.result

def DvdAlphabet (_index : DvdStack) : Type :=
  Bool

/-- A cyclic unary divisibility program.  For a positive divisor, the
`remaining` and `used` stacks partition one divisor-length cycle. -/
def unaryDvdProgram :
    DvdLabel → TM2.Stmt DvdAlphabet DvdLabel DvdState
  | .scanDividend =>
      .pop .input dvdObserved <|
        .branch dvdMarkerPresent
          (.branch dvdMarkerTrue
            (.push .dividend (fun _ => true) <|
              .goto (fun _ => .scanDividend))
            (.goto (fun _ => .scanDivisor)))
          (.goto (fun _ => .scanDivisor))
  | .scanDivisor =>
      .pop .input dvdObserved <|
        .branch dvdMarkerPresent
          (.push .remaining (fun _ => true) <|
            .goto (fun _ => .scanDivisor))
          (.goto (fun _ => .start))
  | .start =>
      .peek .dividend dvdObserved <|
        .branch dvdMarkerPresent
          (.peek .remaining dvdObserved <|
            .branch dvdMarkerPresent
              (.goto (fun _ => .consume))
              (.load (dvdSetResult false) <|
                .goto (fun _ => .finish)))
          (.load (dvdSetResult true) <|
            .goto (fun _ => .finish))
  | .consume =>
      .peek .dividend dvdObserved <|
        .branch dvdMarkerPresent
          (.peek .remaining dvdObserved <|
            .branch dvdMarkerPresent
              (.pop .dividend dvdObserved <|
                .pop .remaining dvdObserved <|
                  .push .used (fun _ => true) <|
                    .goto (fun _ => .consume))
              (.goto (fun _ => .restore)))
          (.goto (fun _ => .check))
  | .restore =>
      .pop .used dvdObserved <|
        .branch dvdMarkerPresent
          (.push .remaining (fun _ => true) <|
            .goto (fun _ => .restore))
          (.goto (fun _ => .consume))
  | .check =>
      .peek .remaining dvdObserved <|
        .branch dvdMarkerPresent
          (.load (dvdSetResult false) <|
            .goto (fun _ => .finish))
          (.load (dvdSetResult true) <|
            .goto (fun _ => .finish))
  | .finish =>
      .push .output dvdResult <|
        .goto (fun _ => .clearDividend)
  | .clearDividend =>
      .pop .dividend dvdObserved <|
        .branch dvdMarkerPresent
          (.goto (fun _ => .clearDividend))
          (.goto (fun _ => .clearRemaining))
  | .clearRemaining =>
      .pop .remaining dvdObserved <|
        .branch dvdMarkerPresent
          (.goto (fun _ => .clearRemaining))
          (.goto (fun _ => .clearUsed))
  | .clearUsed =>
      .pop .used dvdObserved <|
        .branch dvdMarkerPresent
          (.goto (fun _ => .clearUsed))
          (.load (fun _ => dvdInitialState) .halt)

/-- Concrete finite machine deciding divisibility on unary-padded inputs. -/
def unaryDvdComputer : FinTM2 where
  K := DvdStack
  k₀ := .input
  k₁ := .output
  Γ := DvdAlphabet
  Λ := DvdLabel
  main := .scanDividend
  σ := DvdState
  initialState := dvdInitialState
  Γk₀Fin := Bool.fintype
  m := unaryDvdProgram

def dvdStackContents
    (input dividend remaining used output : List Bool) :
    (index : DvdStack) → List (DvdAlphabet index)
  | .input => input
  | .dividend => dividend
  | .remaining => remaining
  | .used => used
  | .output => output

def dvdCfg (label : Option DvdLabel) (state : DvdState)
    (input dividend remaining used output : List Bool) :
    unaryDvdComputer.Cfg where
  l := label
  var := state
  stk := dvdStackContents input dividend remaining used output

private def dvdEvalsToInTimeOne
    {start finish : unaryDvdComputer.Cfg}
    (hstep : unaryDvdComputer.step start = some finish) :
    EvalsToInTime unaryDvdComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem dvd_step_scanDividend_true
    (input dividend remaining used output : List Bool)
    (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDividend) state (true :: input)
          dividend remaining used output) =
      some (dvdCfg (some .scanDividend)
        (dvdObserved state (some true)) input (true :: dividend)
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdMarkerTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_scanDividend_false
    (input dividend remaining used output : List Bool)
    (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDividend) state (false :: input)
          dividend remaining used output) =
      some (dvdCfg (some .scanDivisor)
        (dvdObserved state (some false)) input dividend
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdMarkerTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_scanDivisor_true
    (input dividend remaining used output : List Bool)
    (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDivisor) state (true :: input)
          dividend remaining used output) =
      some (dvdCfg (some .scanDivisor)
        (dvdObserved state (some true)) input dividend
        (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_scanDivisor_nil
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDivisor) state [] dividend remaining used output) =
      some (dvdCfg (some .start) (dvdObserved state none) []
        dividend remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]

private theorem dvd_step_start_zero
    (remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .start) state [] [] remaining used output) =
      some (dvdCfg (some .finish) (dvdSetResult true state) [] []
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_start_positive_zero
    (dividend : List Bool) (used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .start) state [] (true :: dividend) [] used output) =
      some (dvdCfg (some .finish) (dvdSetResult false state) []
        (true :: dividend) [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_start_positive_positive
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .start) state [] (true :: dividend)
          (true :: remaining) used output) =
      some (dvdCfg (some .consume)
        (dvdObserved (dvdObserved state (some true)) (some true)) []
        (true :: dividend) (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_consume_both
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .consume) state [] (true :: dividend)
          (true :: remaining) used output) =
      some (dvdCfg (some .consume)
        (dvdObserved (dvdObserved (dvdObserved
          (dvdObserved state (some true)) (some true)) (some true))
          (some true)) [] dividend remaining (true :: used) output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_consume_dividend_nil
    (remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .consume) state [] [] remaining used output) =
      some (dvdCfg (some .check) (dvdObserved state none) [] []
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_consume_remaining_nil
    (dividend used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .consume) state [] (true :: dividend) [] used output) =
      some (dvdCfg (some .restore)
        (dvdObserved (dvdObserved state (some true)) none) []
        (true :: dividend) [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_restore_cons
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .restore) state [] dividend remaining
          (true :: used) output) =
      some (dvdCfg (some .restore) (dvdObserved state (some true)) []
        dividend (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_restore_nil
    (dividend remaining output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .restore) state [] dividend remaining [] output) =
      some (dvdCfg (some .consume) (dvdObserved state none) []
        dividend remaining [] output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]

private theorem dvd_step_check_cons
    (remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .check) state [] [] (true :: remaining) used output) =
      some (dvdCfg (some .finish) (dvdSetResult false state) [] []
        (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_check_nil
    (used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .check) state [] [] [] used output) =
      some (dvdCfg (some .finish) (dvdSetResult true state) [] [] []
        used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_finish
    (input dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .finish) state input dividend remaining used output) =
      some (dvdCfg (some .clearDividend) state input dividend remaining used
        (state.result :: output)) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdResult]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearDividend_cons
    (input dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearDividend) state input (true :: dividend)
          remaining used output) =
      some (dvdCfg (some .clearDividend) (dvdObserved state (some true))
        input dividend remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearDividend_nil
    (input remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearDividend) state input [] remaining used output) =
      some (dvdCfg (some .clearRemaining) (dvdObserved state none)
        input [] remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_clearRemaining_cons
    (input remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearRemaining) state input []
          (true :: remaining) used output) =
      some (dvdCfg (some .clearRemaining) (dvdObserved state (some true))
        input [] remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearRemaining_nil
    (input used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearRemaining) state input [] [] used output) =
      some (dvdCfg (some .clearUsed) (dvdObserved state none)
        input [] [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_clearUsed_cons
    (input used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearUsed) state input [] [] (true :: used) output) =
      some (dvdCfg (some .clearUsed) (dvdObserved state (some true))
        input [] [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearUsed_nil
    (output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearUsed) state [] [] [] [] output) =
      some (dvdCfg none dvdInitialState [] [] [] [] output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdInitialState]

private def dvd_scanDividend_evals
    (left : ℕ) (input dividend remaining used output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) state
        (List.replicate left true ++ false :: input)
        dividend remaining used output)
      (some (dvdCfg (some .scanDivisor)
        (dvdObserved state (some false)) input
        (List.replicate left true ++ dividend) remaining used output))
      (left + 1) := by
  induction left generalizing state dividend with
  | zero =>
      simpa using dvdEvalsToInTimeOne
        (dvd_step_scanDividend_false input dividend remaining used output state)
  | succ left ih =>
      let nextState := dvdObserved state (some true)
      let middle := dvdCfg (some .scanDividend) nextState
        (List.replicate left true ++ false :: input)
        (true :: dividend) remaining used output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .scanDividend) state
            (List.replicate (left + 1) true ++ false :: input)
            dividend remaining used output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, List.replicate_succ] using
            dvd_step_scanDividend_true
              (List.replicate left true ++ false :: input)
              dividend remaining used output state)
      have hrest := ih (true :: dividend) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (left + 1)
        (dvdCfg (some .scanDividend) state
          (List.replicate (left + 1) true ++ false :: input)
          dividend remaining used output)
        middle
        (some (dvdCfg (some .scanDivisor)
          (dvdObserved state (some false)) input
          (List.replicate (left + 1) true ++ dividend)
          remaining used output))
        hone
        (by
          simpa [middle, nextState, dvdObserved, List.replicate_succ,
            replicate_true_append_cons]
            using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_scanDivisor_evals
    (right : ℕ) (dividend remaining used output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDivisor) state (List.replicate right true)
        dividend remaining used output)
      (some (dvdCfg (some .start) (dvdObserved state none) [] dividend
        (List.replicate right true ++ remaining) used output))
      (right + 1) := by
  induction right generalizing state remaining with
  | zero =>
      simpa using dvdEvalsToInTimeOne
        (dvd_step_scanDivisor_nil dividend remaining used output state)
  | succ right ih =>
      let nextState := dvdObserved state (some true)
      let middle := dvdCfg (some .scanDivisor) nextState
        (List.replicate right true) dividend (true :: remaining) used output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .scanDivisor) state
            (List.replicate (right + 1) true)
            dividend remaining used output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, List.replicate_succ] using
            dvd_step_scanDivisor_true (List.replicate right true)
              dividend remaining used output state)
      have hrest := ih (true :: remaining) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (right + 1)
        (dvdCfg (some .scanDivisor) state
          (List.replicate (right + 1) true)
          dividend remaining used output)
        middle
        (some (dvdCfg (some .start) (dvdObserved state none) [] dividend
          (List.replicate (right + 1) true ++ remaining) used output))
        hone
        (by
          simpa [middle, nextState, dvdObserved, List.replicate_succ,
            replicate_true_append_cons]
            using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvdAfterConsume (state : DvdState) : DvdState :=
  dvdObserved (dvdObserved (dvdObserved
    (dvdObserved state (some true)) (some true)) (some true)) (some true)

private def dvdConsumeState : DvdState → ℕ → DvdState
  | state, 0 => state
  | state, count + 1 => dvdConsumeState (dvdAfterConsume state) count

private def dvd_consume_prefix_evals
    (count : ℕ) (dividend remaining used output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .consume) state []
        (List.replicate count true ++ dividend)
        (List.replicate count true ++ remaining) used output)
      (some (dvdCfg (some .consume) (dvdConsumeState state count) []
        dividend remaining (List.replicate count true ++ used) output))
      count := by
  induction count generalizing state used with
  | zero =>
      simpa [dvdConsumeState] using EvalsToInTime.refl
        unaryDvdComputer.step
        (dvdCfg (some .consume) state [] dividend remaining used output)
  | succ count ih =>
      let nextState := dvdAfterConsume state
      let middle := dvdCfg (some .consume) nextState []
        (List.replicate count true ++ dividend)
        (List.replicate count true ++ remaining) (true :: used) output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .consume) state []
            (List.replicate (count + 1) true ++ dividend)
            (List.replicate (count + 1) true ++ remaining) used output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, dvdAfterConsume,
            List.replicate_succ] using
              dvd_step_consume_both
                (List.replicate count true ++ dividend)
                (List.replicate count true ++ remaining) used output state)
      have hrest := ih (true :: used) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 count
        (dvdCfg (some .consume) state []
          (List.replicate (count + 1) true ++ dividend)
          (List.replicate (count + 1) true ++ remaining) used output)
        middle
        (some (dvdCfg (some .consume)
          (dvdConsumeState state (count + 1)) [] dividend remaining
          (List.replicate (count + 1) true ++ used) output))
        hone
        (by
          simpa [middle, nextState, dvdConsumeState, dvdAfterConsume,
            List.replicate_succ, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvdRestoreState : DvdState → ℕ → DvdState
  | state, 0 => dvdObserved state none
  | state, count + 1 => dvdRestoreState (dvdObserved state (some true)) count

private def dvd_restore_evals
    (count : ℕ) (dividend remaining output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .restore) state [] dividend remaining
        (List.replicate count true) output)
      (some (dvdCfg (some .consume) (dvdRestoreState state count) []
        dividend (List.replicate count true ++ remaining) [] output))
      (count + 1) := by
  induction count generalizing state remaining with
  | zero =>
      simpa [dvdRestoreState] using dvdEvalsToInTimeOne
        (dvd_step_restore_nil dividend remaining output state)
  | succ count ih =>
      let nextState := dvdObserved state (some true)
      let middle := dvdCfg (some .restore) nextState [] dividend
        (true :: remaining) (List.replicate count true) output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .restore) state [] dividend remaining
            (List.replicate (count + 1) true) output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, List.replicate_succ] using
            dvd_step_restore_cons dividend remaining
              (List.replicate count true) output state)
      have hrest := ih (true :: remaining) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (count + 1)
        (dvdCfg (some .restore) state [] dividend remaining
          (List.replicate (count + 1) true) output)
        middle
        (some (dvdCfg (some .consume) (dvdRestoreState state (count + 1)) []
          dividend (List.replicate (count + 1) true ++ remaining) [] output))
        hone
        (by
          simpa [middle, nextState, dvdRestoreState, dvdObserved,
            List.replicate_succ, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_clearUsed_evals
    (used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .clearUsed) state [] [] [] used output)
      (some (dvdCfg none dvdInitialState [] [] [] [] output))
      (used.length + 1) := by
  induction used generalizing state with
  | nil =>
      simpa using dvdEvalsToInTimeOne
        (dvd_step_clearUsed_nil output state)
  | cons marker used ih =>
      cases marker
      · simp only [List.length_cons]
        have hstep : unaryDvdComputer.step
            (dvdCfg (some .clearUsed) state [] [] [] (false :: used) output) =
          some (dvdCfg (some .clearUsed) (dvdObserved state (some false))
            [] [] [] used output) := by
          rcases state with ⟨held, result⟩
          simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
            dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
          funext index
          cases index <;> rfl
        have hone := dvdEvalsToInTimeOne hstep
        have hrest := ih (dvdObserved state (some false))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (used.length + 1)
          (dvdCfg (some .clearUsed) state [] [] [] (false :: used) output)
          (dvdCfg (some .clearUsed) (dvdObserved state (some false))
            [] [] [] used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        omega
      · have hone := dvdEvalsToInTimeOne
          (dvd_step_clearUsed_cons [] used output state)
        have hrest := ih (dvdObserved state (some true))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (used.length + 1)
          (dvdCfg (some .clearUsed) state [] [] [] (true :: used) output)
          (dvdCfg (some .clearUsed) (dvdObserved state (some true))
            [] [] [] used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_clearRemaining_evals
    (remaining used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .clearRemaining) state [] [] remaining used output)
      (some (dvdCfg none dvdInitialState [] [] [] [] output))
      (remaining.length + used.length + 2) := by
  induction remaining generalizing state with
  | nil =>
      have hone := dvdEvalsToInTimeOne
        (dvd_step_clearRemaining_nil [] used output state)
      have hrest := dvd_clearUsed_evals used output (dvdObserved state none)
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (used.length + 1)
        (dvdCfg (some .clearRemaining) state [] [] [] used output)
        (dvdCfg (some .clearUsed) (dvdObserved state none) [] [] [] used output)
        (some (dvdCfg none dvdInitialState [] [] [] [] output))
        hone hrest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
  | cons marker remaining ih =>
      cases marker
      · have hstep : unaryDvdComputer.step
            (dvdCfg (some .clearRemaining) state [] []
              (false :: remaining) used output) =
          some (dvdCfg (some .clearRemaining)
            (dvdObserved state (some false)) [] [] remaining used output) := by
          rcases state with ⟨held, result⟩
          simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
            dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
          funext index
          cases index <;> rfl
        have hone := dvdEvalsToInTimeOne hstep
        have hrest := ih (dvdObserved state (some false))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (remaining.length + used.length + 2)
          (dvdCfg (some .clearRemaining) state [] []
            (false :: remaining) used output)
          (dvdCfg (some .clearRemaining) (dvdObserved state (some false))
            [] [] remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      · have hone := dvdEvalsToInTimeOne
          (dvd_step_clearRemaining_cons [] remaining used output state)
        have hrest := ih (dvdObserved state (some true))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (remaining.length + used.length + 2)
          (dvdCfg (some .clearRemaining) state [] []
            (true :: remaining) used output)
          (dvdCfg (some .clearRemaining) (dvdObserved state (some true))
            [] [] remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_clearDividend_evals
    (dividend remaining used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .clearDividend) state [] dividend remaining used output)
      (some (dvdCfg none dvdInitialState [] [] [] [] output))
      (dividend.length + remaining.length + used.length + 3) := by
  induction dividend generalizing state with
  | nil =>
      have hone := dvdEvalsToInTimeOne
        (dvd_step_clearDividend_nil [] remaining used output state)
      have hrest := dvd_clearRemaining_evals remaining used output
        (dvdObserved state none)
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (remaining.length + used.length + 2)
        (dvdCfg (some .clearDividend) state [] [] remaining used output)
        (dvdCfg (some .clearRemaining) (dvdObserved state none)
          [] [] remaining used output)
        (some (dvdCfg none dvdInitialState [] [] [] [] output))
        hone hrest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
  | cons marker dividend ih =>
      cases marker
      · have hstep : unaryDvdComputer.step
            (dvdCfg (some .clearDividend) state [] (false :: dividend)
              remaining used output) =
          some (dvdCfg (some .clearDividend)
            (dvdObserved state (some false)) [] dividend remaining used output) := by
          rcases state with ⟨held, result⟩
          simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
            dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
          funext index
          cases index <;> rfl
        have hone := dvdEvalsToInTimeOne hstep
        have hrest := ih (dvdObserved state (some false))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (dividend.length + remaining.length + used.length + 3)
          (dvdCfg (some .clearDividend) state [] (false :: dividend)
            remaining used output)
          (dvdCfg (some .clearDividend) (dvdObserved state (some false))
            [] dividend remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      · have hone := dvdEvalsToInTimeOne
          (dvd_step_clearDividend_cons [] dividend remaining used output state)
        have hrest := ih (dvdObserved state (some true))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (dividend.length + remaining.length + used.length + 3)
          (dvdCfg (some .clearDividend) state [] (true :: dividend)
            remaining used output)
          (dvdCfg (some .clearDividend) (dvdObserved state (some true))
            [] dividend remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_finish_evals
    (dividend remaining used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .finish) state [] dividend remaining used output)
      (some (dvdCfg none dvdInitialState [] [] [] []
        (state.result :: output)))
      (dividend.length + remaining.length + used.length + 4) := by
  have hone := dvdEvalsToInTimeOne
    (dvd_step_finish [] dividend remaining used output state)
  have hrest := dvd_clearDividend_evals dividend remaining used
    (state.result :: output) state
  have htrans := EvalsToInTime.trans unaryDvdComputer.step
    1 (dividend.length + remaining.length + used.length + 3)
    (dvdCfg (some .finish) state [] dividend remaining used output)
    (dvdCfg (some .clearDividend) state [] dividend remaining used
      (state.result :: output))
    (some (dvdCfg none dvdInitialState [] [] [] []
      (state.result :: output)))
    hone hrest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private noncomputable def dvd_consume_evals
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .consume) state []
        (List.replicate n true) (List.replicate d true) [] output)
      (some (dvdCfg none dvdInitialState [] [] [] []
        (decide (d ∣ n) :: output)))
      (4 * n + d + 8) := by
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
      by_cases hle : n ≤ d
      · have hsplit :
            List.replicate d true =
              List.replicate n true ++ List.replicate (d - n) true := by
          calc
            List.replicate d true =
                List.replicate (n + (d - n)) true := by
              rw [Nat.add_sub_of_le hle]
            _ = List.replicate n true ++
                List.replicate (d - n) true :=
              List.replicate_add n (d - n) true
        have hprefix := dvd_consume_prefix_evals n []
          (List.replicate (d - n) true) [] output state
        have hprefix' : EvalsToInTime unaryDvdComputer.step
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (some (dvdCfg (some .consume) (dvdConsumeState state n) [] []
              (List.replicate (d - n) true)
              (List.replicate n true) output)) n := by
          simpa only [List.append_nil, ← hsplit] using hprefix
        have hempty := dvdEvalsToInTimeOne
          (dvd_step_consume_dividend_nil
            (List.replicate (d - n) true) (List.replicate n true)
            output (dvdConsumeState state n))
        have htoCheck := EvalsToInTime.trans unaryDvdComputer.step
          n 1
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .consume) (dvdConsumeState state n) [] []
            (List.replicate (d - n) true)
            (List.replicate n true) output)
          (some (dvdCfg (some .check)
            (dvdObserved (dvdConsumeState state n) none) [] []
            (List.replicate (d - n) true)
            (List.replicate n true) output))
          hprefix' hempty
        by_cases heq : n = d
        · subst d
          have hcheck := dvdEvalsToInTimeOne
            (dvd_step_check_nil (List.replicate n true) output
              (dvdObserved (dvdConsumeState state n) none))
          have hfinish := dvd_finish_evals [] []
            (List.replicate n true) output
            (dvdSetResult true
              (dvdObserved (dvdConsumeState state n) none))
          have hthroughCheck := EvalsToInTime.trans unaryDvdComputer.step
            (1 + n) 1
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate n true) [] output)
            (dvdCfg (some .check)
              (dvdObserved (dvdConsumeState state n) none) [] [] []
              (List.replicate n true) output)
            (some (dvdCfg (some .finish)
              (dvdSetResult true
                (dvdObserved (dvdConsumeState state n) none))
              [] [] [] (List.replicate n true) output))
            (by simpa using htoCheck)
            hcheck
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (1 + n)) (n + 4)
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate n true) [] output)
            (dvdCfg (some .finish)
              (dvdSetResult true
                (dvdObserved (dvdConsumeState state n) none))
              [] [] [] (List.replicate n true) output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (n ∣ n) :: output)))
            hthroughCheck
            (by simpa [dvdSetResult] using hfinish)
          exact evalsToInTimeMono hall (by omega)
        · have hlt : n < d := lt_of_le_of_ne hle heq
          have hsubpos : 0 < d - n := Nat.sub_pos_of_lt hlt
          let rest := (d - n).pred
          have hrest : d - n = rest + 1 := by
            exact (Nat.succ_pred_eq_of_pos hsubpos).symm
          have hcheck := dvdEvalsToInTimeOne
            (dvd_step_check_cons (List.replicate rest true)
              (List.replicate n true) output
              (dvdObserved (dvdConsumeState state n) none))
          have hfinish := dvd_finish_evals []
            (List.replicate (d - n) true)
            (List.replicate n true) output
            (dvdSetResult false
              (dvdObserved (dvdConsumeState state n) none))
          have hnot : ¬d ∣ n :=
            Nat.not_dvd_of_pos_of_lt hn hlt
          have hthroughCheck := EvalsToInTime.trans unaryDvdComputer.step
            (1 + n) 1
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (dvdCfg (some .check)
              (dvdObserved (dvdConsumeState state n) none) [] []
              (List.replicate (d - n) true)
              (List.replicate n true) output)
            (some (dvdCfg (some .finish)
              (dvdSetResult false
                (dvdObserved (dvdConsumeState state n) none))
              [] [] (List.replicate (d - n) true)
              (List.replicate n true) output))
            htoCheck
            (by simpa [hrest, List.replicate_succ] using hcheck)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (1 + n)) ((d - n) + n + 4)
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (dvdCfg (some .finish)
              (dvdSetResult false
                (dvdObserved (dvdConsumeState state n) none))
              [] [] (List.replicate (d - n) true)
              (List.replicate n true) output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (d ∣ n) :: output)))
            hthroughCheck
            (by simpa [dvdSetResult, hnot] using hfinish)
          exact evalsToInTimeMono hall (by omega)
      · have hlt : d < n := lt_of_not_ge hle
        have hdle : d ≤ n := Nat.le_of_lt hlt
        have hsplit :
            List.replicate n true =
              List.replicate d true ++ List.replicate (n - d) true := by
          calc
            List.replicate n true =
                List.replicate (d + (n - d)) true := by
              rw [Nat.add_sub_of_le hdle]
            _ = List.replicate d true ++
                List.replicate (n - d) true :=
              List.replicate_add d (n - d) true
        have hprefix := dvd_consume_prefix_evals d
          (List.replicate (n - d) true) [] [] output state
        have hprefix' : EvalsToInTime unaryDvdComputer.step
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (some (dvdCfg (some .consume) (dvdConsumeState state d) []
              (List.replicate (n - d) true) []
              (List.replicate d true) output)) d := by
          simpa only [List.append_nil, ← hsplit] using hprefix
        have hsubpos : 0 < n - d := Nat.sub_pos_of_lt hlt
        let tail := (n - d).pred
        have htail : n - d = tail + 1 := by
          exact (Nat.succ_pred_eq_of_pos hsubpos).symm
        have hboundary := dvdEvalsToInTimeOne
          (dvd_step_consume_remaining_nil (List.replicate tail true)
            (List.replicate d true) output (dvdConsumeState state d))
        have htoRestore := EvalsToInTime.trans unaryDvdComputer.step
          d 1
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .consume) (dvdConsumeState state d) []
            (List.replicate (n - d) true) []
            (List.replicate d true) output)
          (some (dvdCfg (some .restore)
            (dvdObserved (dvdObserved (dvdConsumeState state d) (some true)) none)
            [] (List.replicate (n - d) true) []
            (List.replicate d true) output))
          hprefix'
          (by simpa [htail, List.replicate_succ] using hboundary)
        have hrestore := dvd_restore_evals d
          (List.replicate (n - d) true) [] output
          (dvdObserved (dvdObserved (dvdConsumeState state d) (some true)) none)
        have hrestore' : EvalsToInTime unaryDvdComputer.step
            (dvdCfg (some .restore)
              (dvdObserved
                (dvdObserved (dvdConsumeState state d) (some true)) none)
              [] (List.replicate (n - d) true) []
              (List.replicate d true) output)
            (some (dvdCfg (some .consume)
              (dvdRestoreState
                (dvdObserved
                  (dvdObserved (dvdConsumeState state d) (some true)) none) d)
              [] (List.replicate (n - d) true)
              (List.replicate d true) [] output)) (d + 1) := by
          simpa only [List.append_nil] using hrestore
        have hcycle := EvalsToInTime.trans unaryDvdComputer.step
          (1 + d) (d + 1)
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .restore)
            (dvdObserved (dvdObserved (dvdConsumeState state d) (some true)) none)
            [] (List.replicate (n - d) true) []
            (List.replicate d true) output)
          (some (dvdCfg (some .consume)
            (dvdRestoreState
              (dvdObserved
                (dvdObserved (dvdConsumeState state d) (some true)) none) d)
            [] (List.replicate (n - d) true)
            (List.replicate d true) [] output))
          (by simpa [Nat.add_comm] using htoRestore)
          hrestore'
        have hrec := ih (n - d) (Nat.sub_lt hn hd)
          hsubpos
          (dvdRestoreState
            (dvdObserved
              (dvdObserved (dvdConsumeState state d) (some true)) none) d)
        have hdvd : d ∣ n - d ↔ d ∣ n :=
          Nat.dvd_sub_iff_left hdle (Nat.dvd_refl d)
        have hall := EvalsToInTime.trans unaryDvdComputer.step
          ((d + 1) + (1 + d)) (4 * (n - d) + d + 8)
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .consume)
            (dvdRestoreState
              (dvdObserved
                (dvdObserved (dvdConsumeState state d) (some true)) none) d)
            [] (List.replicate (n - d) true)
            (List.replicate d true) [] output)
          (some (dvdCfg none dvdInitialState [] [] [] []
            (decide (d ∣ n) :: output)))
          hcycle
          (by simpa only [hdvd] using hrec)
        exact evalsToInTimeMono hall (by omega)

private def dvd_parse_evals (n d : ℕ) (output : List Bool) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode (n, d)) [] [] [] output)
      (some (dvdCfg (some .start)
        (dvdObserved (dvdObserved dvdInitialState (some false)) none)
        [] (List.replicate n true) (List.replicate d true) [] output))
      (n + d + 2) := by
  have hleft := dvd_scanDividend_evals n
    (List.replicate d true) [] [] [] output dvdInitialState
  have hright := dvd_scanDivisor_evals d
    (List.replicate n true) [] [] output
    (dvdObserved dvdInitialState (some false))
  have hall := EvalsToInTime.trans unaryDvdComputer.step
    (n + 1) (d + 1)
    (dvdCfg (some .scanDividend) dvdInitialState
      (UnaryNatPair.encode (n, d)) [] [] [] output)
    (dvdCfg (some .scanDivisor)
      (dvdObserved dvdInitialState (some false))
      (List.replicate d true) (List.replicate n true) [] [] output)
    (some (dvdCfg (some .start)
      (dvdObserved (dvdObserved dvdInitialState (some false)) none)
      [] (List.replicate n true) (List.replicate d true) [] output))
    (by simpa [UnaryNatPair.encode] using hleft)
    (by simpa using hright)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem dvd_initList_eq_cfg (input : List Bool) :
    initList unaryDvdComputer input =
      dvdCfg (some .scanDividend) dvdInitialState input [] [] [] [] := by
  unfold initList dvdCfg
  congr
  funext index
  cases index <;> rfl

private theorem dvd_haltList_eq_cfg (output : List Bool) :
    haltList unaryDvdComputer output =
      dvdCfg none dvdInitialState [] [] [] [] output := by
  unfold haltList dvdCfg
  congr
  funext index
  cases index <;> rfl

noncomputable def unaryDvd_evals_with_output
    (pair : ℕ × ℕ) (output : List Bool) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode pair) [] [] [] output)
      (some (dvdCfg none dvdInitialState [] [] [] []
        (decide (pair.2 ∣ pair.1) :: output)))
      (6 * (UnaryNatPair.encode pair).length + 16) := by
  rcases pair with ⟨n, d⟩
  have hparse := dvd_parse_evals n d output
  cases n with
  | zero =>
      let parsedState :=
        dvdObserved (dvdObserved dvdInitialState (some false)) none
      have hstart := dvdEvalsToInTimeOne
        (dvd_step_start_zero (List.replicate d true) [] output parsedState)
      have hfinish := dvd_finish_evals [] (List.replicate d true) [] output
        (dvdSetResult true parsedState)
      have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
        (d + 2) 1
        (dvdCfg (some .scanDividend) dvdInitialState
          (UnaryNatPair.encode (0, d)) [] [] [] output)
        (dvdCfg (some .start) parsedState [] []
          (List.replicate d true) [] output)
        (some (dvdCfg (some .finish) (dvdSetResult true parsedState)
          [] [] (List.replicate d true) [] output))
        (by simpa [parsedState] using hparse)
        hstart
      have hall := EvalsToInTime.trans unaryDvdComputer.step
        (1 + (d + 2)) (d + 4)
        (dvdCfg (some .scanDividend) dvdInitialState
          (UnaryNatPair.encode (0, d)) [] [] [] output)
        (dvdCfg (some .finish) (dvdSetResult true parsedState)
          [] [] (List.replicate d true) [] output)
        (some (dvdCfg none dvdInitialState [] [] [] []
          (decide (d ∣ 0) :: output)))
        hthroughStart
        (by simpa [dvdSetResult] using hfinish)
      have hbound :
          (d + 4) + (1 + (d + 2)) ≤
            6 * (UnaryNatPair.encode (0, d)).length + 16 := by
        simp [UnaryNatPair.encode]
        omega
      exact evalsToInTimeMono hall hbound
  | succ n =>
      cases d with
      | zero =>
          let parsedState :=
            dvdObserved (dvdObserved dvdInitialState (some false)) none
          have hstart := dvdEvalsToInTimeOne
            (dvd_step_start_positive_zero (List.replicate n true) []
              output parsedState)
          have hfinish := dvd_finish_evals
            (List.replicate (n + 1) true) [] [] output
            (dvdSetResult false parsedState)
          have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
            (n + 1 + 0 + 2) 1
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, 0)) [] [] [] output)
            (dvdCfg (some .start) parsedState []
              (List.replicate (n + 1) true) [] [] output)
            (some (dvdCfg (some .finish) (dvdSetResult false parsedState)
              [] (List.replicate (n + 1) true) [] [] output))
            (by simpa [parsedState] using hparse)
            (by simpa [List.replicate_succ] using hstart)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (n + 1 + 0 + 2)) (n + 1 + 4)
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, 0)) [] [] [] output)
            (dvdCfg (some .finish) (dvdSetResult false parsedState)
              [] (List.replicate (n + 1) true) [] [] output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (0 ∣ n + 1) :: output)))
            hthroughStart
            (by simpa [dvdSetResult] using hfinish)
          have hbound :
              (n + 1 + 4) + (1 + (n + 1 + 0 + 2)) ≤
                6 * (UnaryNatPair.encode (n + 1, 0)).length + 16 := by
            simp [UnaryNatPair.encode]
            omega
          exact evalsToInTimeMono hall hbound
      | succ d =>
          let parsedState :=
            dvdObserved (dvdObserved dvdInitialState (some false)) none
          let consumeState :=
            dvdObserved (dvdObserved parsedState (some true)) (some true)
          have hstart := dvdEvalsToInTimeOne
            (dvd_step_start_positive_positive
              (List.replicate n true) (List.replicate d true) [] output
              parsedState)
          have hconsume := dvd_consume_evals (n + 1) (d + 1)
            (Nat.succ_pos n) (Nat.succ_pos d) output consumeState
          have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
            (n + 1 + (d + 1) + 2) 1
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, d + 1)) [] [] [] output)
            (dvdCfg (some .start) parsedState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] output)
            (some (dvdCfg (some .consume) consumeState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] output))
            (by simpa [parsedState] using hparse)
            (by simpa [consumeState, List.replicate_succ] using hstart)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (n + 1 + (d + 1) + 2))
            (4 * (n + 1) + (d + 1) + 8)
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, d + 1)) [] [] [] output)
            (dvdCfg (some .consume) consumeState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (d + 1 ∣ n + 1) :: output)))
            hthroughStart
            (by simpa using hconsume)
          have hbound :
              (4 * (n + 1) + (d + 1) + 8) +
                  (1 + (n + 1 + (d + 1) + 2)) ≤
                6 * (UnaryNatPair.encode (n + 1, d + 1)).length + 16 := by
            simp [UnaryNatPair.encode]
            omega
          exact evalsToInTimeMono hall hbound

/-- The unary-padded checker decides natural-number divisibility in at most
`6s + 16` steps, where `s = n + d + 1` is its actual encoded input length. -/
noncomputable def unaryDvd_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime unaryDvdComputer (UnaryNatPair.encode pair)
      (some (encodeBool (decide (pair.2 ∣ pair.1))))
      (6 * (UnaryNatPair.encode pair).length + 16) := by
  have hrun := unaryDvd_evals_with_output pair []
  rw [TM2OutputsInTime, dvd_initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def]
  rw [dvd_haltList_eq_cfg]
  simpa using hrun

/-- Genuine polynomial-time divisibility on the unary-padded interface used
by the future bounded prime scan. -/
noncomputable def unaryDvdComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) Bool UnaryNatPair.finEncoding
      finEncodingBoolBool (fun pair => decide (pair.2 ∣ pair.1)) where
  tm := unaryDvdComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * Polynomial.X + 16
  outputsFun pair := by
    simpa [UnaryNatPair.finEncoding, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using unaryDvd_outputsInTime pair

/-! ## Finite-machine generation of padded trial pairs

The next machine consumes unary `n` and emits, in stack order, exactly the
inputs `(n, 2), ..., (n, n - 1)` required by bounded trial division.  Its
quadratic output is polynomial in this deliberately padded input interface.
-/

/-- Input, a preserved dividend, remaining divisor iterations, the current
divisor, copy work storage, and the raw pair-list output. -/
inductive TrialPairStack
  | input
  | dividend
  | remaining
  | divisor
  | work
  | output
  deriving DecidableEq, Fintype

/-- Counting, initial trimming, pair emission, iteration, and cleanup phases. -/
inductive TrialPairLabel
  | scan
  | trimFirst
  | trimSecond
  | loop
  | emitStart
  | copyDividend
  | restoreDividend
  | copyDivisor
  | restoreDivisor
  | cleanupDivisor
  | cleanupDividend
  deriving DecidableEq, Fintype

/-- Finite control holds the most recently popped Boolean symbol. -/
structure TrialPairState where
  marker : Option Bool
  deriving DecidableEq, Fintype

private def trialPairInitialState : TrialPairState :=
  ⟨none⟩

private def trialPairObserved
    (_state : TrialPairState) (marker : Option Bool) : TrialPairState :=
  ⟨marker⟩

private def trialPairMarkerPresent : TrialPairState → Bool
  | ⟨some _⟩ => true
  | _ => false

private def trialPairHeldBit : TrialPairState → Bool
  | ⟨some bit⟩ => bit
  | _ => false

private def trialPairHeldRawBit : TrialPairState → Option Bool
  | ⟨some bit⟩ => some bit
  | _ => none

private def TrialPairAlphabet : TrialPairStack → Type
  | .input => Bool
  | .dividend => Bool
  | .remaining => Bool
  | .divisor => Bool
  | .work => Bool
  | .output => Option Bool

/-- Generate every padded pair `(n,d)` for `2 ≤ d < n`. -/
def trialDivisionPairProgram :
    TrialPairLabel →
      TM2.Stmt TrialPairAlphabet TrialPairLabel TrialPairState
  | .scan =>
      .pop .input trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .dividend trialPairHeldBit <|
            .push .remaining trialPairHeldBit <|
              .goto (fun _ => .scan))
          (.goto (fun _ => .trimFirst))
  | .trimFirst =>
      .pop .remaining trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .trimSecond))
          (.goto (fun _ => .cleanupDivisor))
  | .trimSecond =>
      .pop .remaining trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .divisor (fun _ => true) <|
            .push .divisor (fun _ => true) <|
              .goto (fun _ => .loop))
          (.goto (fun _ => .cleanupDivisor))
  | .loop =>
      .pop .remaining trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .emitStart))
          (.goto (fun _ => .cleanupDivisor))
  | .emitStart =>
      .push .output (fun _ => none) <|
        .goto (fun _ => .copyDividend)
  | .copyDividend =>
      .pop .dividend trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .work trialPairHeldBit <|
            .push .output trialPairHeldRawBit <|
              .goto (fun _ => .copyDividend))
          (.goto (fun _ => .restoreDividend))
  | .restoreDividend =>
      .pop .work trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .dividend trialPairHeldBit <|
            .goto (fun _ => .restoreDividend))
          (.push .output (fun _ => some false) <|
            .goto (fun _ => .copyDivisor))
  | .copyDivisor =>
      .pop .divisor trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .work trialPairHeldBit <|
            .push .output trialPairHeldRawBit <|
              .goto (fun _ => .copyDivisor))
          (.goto (fun _ => .restoreDivisor))
  | .restoreDivisor =>
      .pop .work trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .divisor trialPairHeldBit <|
            .goto (fun _ => .restoreDivisor))
          (.push .divisor (fun _ => true) <|
            .goto (fun _ => .loop))
  | .cleanupDivisor =>
      .pop .divisor trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .cleanupDivisor))
          (.goto (fun _ => .cleanupDividend))
  | .cleanupDividend =>
      .pop .dividend trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .cleanupDividend))
          (.load (fun _ => trialPairInitialState) .halt)

/-- Concrete finite machine producing `RawUnaryPairList.finEncoding`. -/
def trialDivisionPairComputer : FinTM2 where
  K := TrialPairStack
  k₀ := .input
  k₁ := .output
  Γ := TrialPairAlphabet
  Λ := TrialPairLabel
  main := .scan
  σ := TrialPairState
  initialState := trialPairInitialState
  Γk₀Fin := Bool.fintype
  m := trialDivisionPairProgram

def trialPairStackContents
    (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) :
    (index : TrialPairStack) → List (TrialPairAlphabet index)
  | .input => input
  | .dividend => dividend
  | .remaining => remaining
  | .divisor => divisor
  | .work => work
  | .output => output

def trialPairCfg (label : Option TrialPairLabel)
    (state : TrialPairState)
    (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) : trialDivisionPairComputer.Cfg where
  l := label
  var := state
  stk := trialPairStackContents input dividend remaining divisor work output

private def trialPairEvalsToInTimeOne
    {start finish : trialDivisionPairComputer.Cfg}
    (hstep : trialDivisionPairComputer.step start = some finish) :
    EvalsToInTime trialDivisionPairComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem trialPair_step_scan_cons
    (bit : Bool) (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .scan) state (bit :: input) dividend remaining
          divisor work output) =
      some (trialPairCfg (some .scan) ⟨some bit⟩ input
        (bit :: dividend) (bit :: remaining) divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_scan_nil
    (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .scan) state [] dividend remaining divisor work
          output) =
      some (trialPairCfg (some .trimFirst) ⟨none⟩ [] dividend remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_trimFirst_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimFirst) state [] dividend
          (bit :: remaining) divisor work output) =
      some (trialPairCfg (some .trimSecond) ⟨some bit⟩ [] dividend remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_trimFirst_nil
    (dividend divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimFirst) state [] dividend [] divisor work
          output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_trimSecond_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimSecond) state [] dividend
          (bit :: remaining) divisor work output) =
      some (trialPairCfg (some .loop) ⟨some bit⟩ [] dividend remaining
        (true :: true :: divisor) work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_trimSecond_nil
    (dividend divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimSecond) state [] dividend [] divisor work
          output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, Function.update]

private theorem trialPair_step_loop_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .loop) state [] dividend (bit :: remaining)
          divisor work output) =
      some (trialPairCfg (some .emitStart) ⟨some bit⟩ [] dividend remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_loop_nil
    (dividend divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .loop) state [] dividend [] divisor work output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_emitStart
    (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .emitStart) state [] dividend remaining divisor
          work output) =
      some (trialPairCfg (some .copyDividend) state [] dividend remaining
        divisor work (none :: output)) := by
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDividend_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDividend) state [] (bit :: dividend)
          remaining divisor work output) =
      some (trialPairCfg (some .copyDividend) ⟨some bit⟩ [] dividend
        remaining divisor (bit :: work) (some bit :: output)) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    trialPairHeldRawBit, Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDividend_nil
    (remaining divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDividend) state [] [] remaining divisor work
          output) =
      some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_restoreDividend_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDividend) state [] dividend remaining
          divisor (bit :: work) output) =
      some (trialPairCfg (some .restoreDividend) ⟨some bit⟩ []
        (bit :: dividend) remaining divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_restoreDividend_nil
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDividend) state [] dividend remaining
          divisor [] output) =
      some (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining
        divisor [] (some false :: output)) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDivisor_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDivisor) state [] dividend remaining
          (bit :: divisor) work output) =
      some (trialPairCfg (some .copyDivisor) ⟨some bit⟩ [] dividend
        remaining divisor (bit :: work) (some bit :: output)) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    trialPairHeldRawBit, Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDivisor_nil
    (dividend remaining work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDivisor) state [] dividend remaining [] work
          output) =
      some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining
        [] work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_restoreDivisor_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDivisor) state [] dividend remaining
          divisor (bit :: work) output) =
      some (trialPairCfg (some .restoreDivisor) ⟨some bit⟩ [] dividend
        remaining (bit :: divisor) work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_restoreDivisor_nil
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDivisor) state [] dividend remaining
          divisor [] output) =
      some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: divisor) [] output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_cleanupDivisor_cons
    (bit : Bool) (dividend divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDivisor) state [] dividend []
          (bit :: divisor) work output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨some bit⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_cleanupDivisor_nil
    (dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDivisor) state [] dividend [] [] work
          output) =
      some (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] []
        work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_cleanupDividend_cons
    (bit : Bool) (dividend work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDividend) state [] (bit :: dividend) []
          [] work output) =
      some (trialPairCfg (some .cleanupDividend) ⟨some bit⟩ [] dividend []
        [] work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_cleanupDividend_nil
    (work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDividend) state [] [] [] [] work output) =
      some (trialPairCfg none trialPairInitialState [] [] [] [] work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairInitialState]

private def trialPair_scan_evals
    (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .scan) state input dividend remaining divisor work
        output)
      (some (trialPairCfg (some .trimFirst) ⟨none⟩ []
        (input.reverse ++ dividend) (input.reverse ++ remaining)
        divisor work output))
      (input.length + 1) := by
  induction input generalizing dividend remaining state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_scan_nil dividend remaining divisor work output state)
  | cons bit input ih =>
      let middle := trialPairCfg (some .scan) ⟨some bit⟩ input
        (bit :: dividend) (bit :: remaining) divisor work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .scan) state (bit :: input) dividend remaining
            divisor work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_scan_cons bit input dividend
            remaining divisor work output state)
      have hrest := ih (bit :: dividend) (bit :: remaining) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (input.length + 1)
        (trialPairCfg (some .scan) state (bit :: input) dividend remaining
          divisor work output)
        middle
        (some (trialPairCfg (some .trimFirst) ⟨none⟩ []
          ((bit :: input).reverse ++ dividend)
          ((bit :: input).reverse ++ remaining) divisor work output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_copyDividend_evals
    (bits remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .copyDividend) state [] bits remaining divisor work
        output)
      (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
        divisor (bits.reverse ++ work) (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_copyDividend_nil remaining divisor work output state)
  | cons bit bits ih =>
      let middle := trialPairCfg (some .copyDividend) ⟨some bit⟩ [] bits
        remaining divisor (bit :: work) (some bit :: output)
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .copyDividend) state [] (bit :: bits)
            remaining divisor work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_copyDividend_cons bit bits
            remaining divisor work output state)
      have hrest := ih (bit :: work) (some bit :: output) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (bits.length + 1)
        (trialPairCfg (some .copyDividend) state [] (bit :: bits)
          remaining divisor work output)
        middle
        (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
          divisor ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse.map some ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_restoreDividend_evals
    (work dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .restoreDividend) state [] dividend remaining
        divisor work output)
      (some (trialPairCfg (some .copyDivisor) ⟨none⟩ []
        (work.reverse ++ dividend) remaining divisor []
        (some false :: output)))
      (work.length + 1) := by
  induction work generalizing dividend state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_restoreDividend_nil dividend remaining divisor output
          state)
  | cons bit work ih =>
      let middle := trialPairCfg (some .restoreDividend) ⟨some bit⟩ []
        (bit :: dividend) remaining divisor work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .restoreDividend) state [] dividend remaining
            divisor (bit :: work) output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_restoreDividend_cons bit
            dividend remaining divisor work output state)
      have hrest := ih (bit :: dividend) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (work.length + 1)
        (trialPairCfg (some .restoreDividend) state [] dividend remaining
          divisor (bit :: work) output)
        middle
        (some (trialPairCfg (some .copyDivisor) ⟨none⟩ []
          ((bit :: work).reverse ++ dividend) remaining divisor []
          (some false :: output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_copyDivisor_evals
    (bits dividend remaining work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .copyDivisor) state [] dividend remaining bits work
        output)
      (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend
        remaining [] (bits.reverse ++ work)
        (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_copyDivisor_nil dividend remaining work output state)
  | cons bit bits ih =>
      let middle := trialPairCfg (some .copyDivisor) ⟨some bit⟩ [] dividend
        remaining bits (bit :: work) (some bit :: output)
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .copyDivisor) state [] dividend remaining
            (bit :: bits) work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_copyDivisor_cons bit dividend
            remaining bits work output state)
      have hrest := ih (bit :: work) (some bit :: output) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (bits.length + 1)
        (trialPairCfg (some .copyDivisor) state [] dividend remaining
          (bit :: bits) work output)
        middle
        (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend
          remaining [] ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse.map some ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_restoreDivisor_evals
    (work dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .restoreDivisor) state [] dividend remaining divisor
        work output)
      (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: work.reverse ++ divisor) [] output))
      (work.length + 1) := by
  induction work generalizing divisor state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_restoreDivisor_nil dividend remaining divisor output
          state)
  | cons bit work ih =>
      let middle := trialPairCfg (some .restoreDivisor) ⟨some bit⟩ []
        dividend remaining (bit :: divisor) work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .restoreDivisor) state [] dividend remaining
            divisor (bit :: work) output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_restoreDivisor_cons bit dividend
            remaining divisor work output state)
      have hrest := ih (bit :: divisor) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (work.length + 1)
        (trialPairCfg (some .restoreDivisor) state [] dividend remaining
          divisor (bit :: work) output)
        middle
        (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
          (true :: (bit :: work).reverse ++ divisor) [] output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPairEmitTime (dividend divisor : List Bool) : ℕ :=
  2 * dividend.length + 2 * divisor.length + 5

private theorem trialPair_segment_append
    (dividend divisor : List Bool) (output : List (Option Bool)) :
    divisor.reverse.map some ++ some false ::
        dividend.reverse.map some ++ none :: output =
      RawNatList.segment (dividend ++ false :: divisor) ++ output := by
  simp [RawNatList.segment, List.reverse_append, List.map_append,
    List.append_assoc]

private def trialPair_emit_copyDividend_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
        divisor dividend.reverse
        (dividend.reverse.map some ++ none :: output)))
      (dividend.length + 2) := by
  let afterStart := trialPairCfg (some .copyDividend) state [] dividend
    remaining divisor [] (none :: output)
  have hstart : EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some afterStart) 1 :=
    trialPairEvalsToInTimeOne (by
      simpa [afterStart] using trialPair_step_emitStart dividend remaining
        divisor [] output state)
  have hcopy := trialPair_copyDividend_evals dividend remaining divisor []
    (none :: output) state
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    1 (dividend.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    afterStart
    (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
      divisor dividend.reverse
      (dividend.reverse.map some ++ none :: output)))
    hstart
    (by simpa [afterStart] using hcopy)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_restoreDividend_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining
        divisor [] (some false :: dividend.reverse.map some ++ none :: output)))
      (2 * dividend.length + 3) := by
  have hfirst := trialPair_emit_copyDividend_evals dividend remaining divisor
    output state
  have hrestore := trialPair_restoreDividend_evals dividend.reverse []
    remaining divisor (dividend.reverse.map some ++ none :: output) ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (dividend.length + 2) (dividend.reverse.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining divisor
      dividend.reverse (dividend.reverse.map some ++ none :: output))
    (some (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining
      divisor [] (some false :: dividend.reverse.map some ++ none :: output)))
    hfirst
    (by simpa using hrestore)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_copyDivisor_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining
        [] divisor.reverse
        (divisor.reverse.map some ++ some false ::
          dividend.reverse.map some ++ none :: output)))
      (2 * dividend.length + divisor.length + 4) := by
  have hfirst := trialPair_emit_restoreDividend_evals dividend remaining divisor
    output state
  have hcopy := trialPair_copyDivisor_evals divisor dividend remaining []
    (some false :: dividend.reverse.map some ++ none :: output) ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (2 * dividend.length + 3) (divisor.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining divisor []
      (some false :: dividend.reverse.map some ++ none :: output))
    (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining
      [] divisor.reverse
      (divisor.reverse.map some ++ some false ::
        dividend.reverse.map some ++ none :: output)))
    hfirst
    (by simpa [List.append_assoc] using hcopy)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_restoreDivisor_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: divisor) []
        (RawNatList.segment (dividend ++ false :: divisor) ++ output)))
      (2 * dividend.length + 2 * divisor.length + 5) := by
  have hfirst := trialPair_emit_copyDivisor_evals dividend remaining divisor
    output state
  have hrestore := trialPair_restoreDivisor_evals divisor.reverse dividend
    remaining []
    (divisor.reverse.map some ++ some false ::
      dividend.reverse.map some ++ none :: output) ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (2 * dividend.length + divisor.length + 4)
    (divisor.reverse.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining []
      divisor.reverse
      (divisor.reverse.map some ++ some false ::
        dividend.reverse.map some ++ none :: output))
    (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
      (true :: divisor) []
      (RawNatList.segment (dividend ++ false :: divisor) ++ output)))
    hfirst
    (by
      rw [← trialPair_segment_append dividend divisor output]
      simpa using hrestore)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: divisor) []
        (RawNatList.segment (dividend ++ false :: divisor) ++ output)))
      (trialPairEmitTime dividend divisor) := by
  simpa [trialPairEmitTime] using
    trialPair_emit_restoreDivisor_evals dividend remaining divisor output state

private def trialPair_cleanupDivisor_evals
    (divisor dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .cleanupDivisor) state [] dividend [] divisor work
        output)
      (some (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] []
        work output))
      (divisor.length + 1) := by
  induction divisor generalizing state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_cleanupDivisor_nil dividend work output state)
  | cons bit divisor ih =>
      let middle := trialPairCfg (some .cleanupDivisor) ⟨some bit⟩ []
        dividend [] divisor work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .cleanupDivisor) state [] dividend []
            (bit :: divisor) work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_cleanupDivisor_cons bit dividend
            divisor work output state)
      have hrest := ih ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (divisor.length + 1)
        (trialPairCfg (some .cleanupDivisor) state [] dividend []
          (bit :: divisor) work output)
        middle
        (some (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] []
          work output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_cleanupDividend_evals
    (dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .cleanupDividend) state [] dividend [] [] work
        output)
      (some (trialPairCfg none trialPairInitialState [] [] [] [] work output))
      (dividend.length + 1) := by
  induction dividend generalizing state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_cleanupDividend_nil work output state)
  | cons bit dividend ih =>
      let middle := trialPairCfg (some .cleanupDividend) ⟨some bit⟩ []
        dividend [] [] work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .cleanupDividend) state [] (bit :: dividend) []
            [] work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_cleanupDividend_cons bit
            dividend work output state)
      have hrest := ih ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (dividend.length + 1)
        (trialPairCfg (some .cleanupDividend) state [] (bit :: dividend) []
          [] work output)
        middle
        (some (trialPairCfg none trialPairInitialState [] [] [] [] work
          output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

/-- The consecutive pair suffix beginning at divisor `first`. -/
def trialPairsFrom : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _n, _first => []
  | count + 1, n, first =>
      (n, first) :: trialPairsFrom count n (first + 1)

theorem trialPairsFrom_eq_range (count n first : ℕ) :
    trialPairsFrom count n first =
      (List.range' first count).map fun divisor => (n, divisor) := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      simp [trialPairsFrom, List.range'_succ, ih]

@[simp]
theorem trialPairsFrom_sub_two (n : ℕ) :
    trialPairsFrom (n - 2) n 2 = trialDivisionPairs n := by
  rw [trialPairsFrom_eq_range]
  rfl

private def encodedTrialPairSuffix (count n first : ℕ) :
    List (Option Bool) :=
  RawUnaryPairList.encode (trialPairsFrom count n first)

private theorem encodedTrialPairSuffix_succ (count n first : ℕ) :
    encodedTrialPairSuffix (count + 1) n first =
      encodedTrialPairSuffix count n (first + 1) ++
        RawNatList.segment (UnaryNatPair.encode (n, first)) := by
  simp [encodedTrialPairSuffix, trialPairsFrom, RawUnaryPairList.encode,
    List.reverse_cons, List.flatMap_append]

private def trialPairLoopTime : ℕ → ℕ → ℕ → ℕ
  | 0, n, first => n + first + 3
  | count + 1, n, first =>
      1 + trialPairEmitTime (unaryEncodeNat n) (unaryEncodeNat first) +
        trialPairLoopTime count n (first + 1)

private theorem unaryEncodeNat_eq_replicate (n : ℕ) :
    unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unaryEncodeNat, List.replicate_succ, ih]

private def trialPair_loop_evals
    (count n first : ℕ) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat first) [] output)
      (some (trialPairCfg none trialPairInitialState [] [] [] [] []
        (encodedTrialPairSuffix count n first ++ output)))
      (trialPairLoopTime count n first) := by
  induction count generalizing first output state with
  | zero =>
      let afterLoop := trialPairCfg (some .cleanupDivisor) ⟨none⟩ []
        (unaryEncodeNat n) [] (unaryEncodeNat first) [] output
      have hloop : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .loop) state [] (unaryEncodeNat n) []
            (unaryEncodeNat first) [] output)
          (some afterLoop) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [afterLoop] using trialPair_step_loop_nil
            (unaryEncodeNat n) (unaryEncodeNat first) [] output state)
      have hcleanupDivisor := trialPair_cleanupDivisor_evals
        (unaryEncodeNat first) (unaryEncodeNat n) [] output ⟨none⟩
      let afterDivisor := trialPairCfg (some .cleanupDividend) ⟨none⟩ []
        (unaryEncodeNat n) [] [] [] output
      have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step
        1 ((unaryEncodeNat first).length + 1)
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n) []
          (unaryEncodeNat first) [] output)
        afterLoop
        (some afterDivisor)
        hloop
        (by simpa [afterLoop, afterDivisor] using hcleanupDivisor)
      have hcleanupDividend := trialPair_cleanupDividend_evals
        (unaryEncodeNat n) [] output ⟨none⟩
      have hall := EvalsToInTime.trans trialDivisionPairComputer.step
        (1 + ((unaryEncodeNat first).length + 1))
        ((unaryEncodeNat n).length + 1)
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n) []
          (unaryEncodeNat first) [] output)
        afterDivisor
        (some (trialPairCfg none trialPairInitialState [] [] [] [] []
          output))
        (by simpa [Nat.add_comm] using hfirst)
        (by simpa [afterDivisor] using hcleanupDividend)
      simpa [trialPairLoopTime, encodedTrialPairSuffix,
        trialPairInitialState, unaryEncodeNat_length, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall
  | succ count ih =>
      let afterLoop := trialPairCfg (some .emitStart) ⟨some true⟩ []
        (unaryEncodeNat n) (unaryEncodeNat count)
        (unaryEncodeNat first) [] output
      have hloop : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
            (unaryEncodeNat (count + 1)) (unaryEncodeNat first) [] output)
          (some afterLoop) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [afterLoop, unaryEncodeNat] using trialPair_step_loop_cons true
            (unaryEncodeNat n) (unaryEncodeNat count)
            (unaryEncodeNat first) [] output state)
      have hemit := trialPair_emit_evals (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat first) output ⟨some true⟩
      let afterEmit := trialPairCfg (some .loop) ⟨none⟩ []
        (unaryEncodeNat n) (unaryEncodeNat count)
        (unaryEncodeNat (first + 1)) []
        (RawNatList.segment (UnaryNatPair.encode (n, first)) ++ output)
      have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (trialPairEmitTime (unaryEncodeNat n) (unaryEncodeNat first))
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
          (unaryEncodeNat (count + 1)) (unaryEncodeNat first) [] output)
        afterLoop
        (some afterEmit)
        hloop
        (by
          simpa [afterLoop, afterEmit, UnaryNatPair.encode,
            unaryEncodeNat_eq_replicate]
            using hemit)
      have hrest := ih (first + 1)
        (RawNatList.segment (UnaryNatPair.encode (n, first)) ++ output)
        ⟨none⟩
      have hall := EvalsToInTime.trans trialDivisionPairComputer.step
        (1 + trialPairEmitTime (unaryEncodeNat n) (unaryEncodeNat first))
        (trialPairLoopTime count n (first + 1))
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
          (unaryEncodeNat (count + 1)) (unaryEncodeNat first) [] output)
        afterEmit
        (some (trialPairCfg none trialPairInitialState [] [] [] [] []
          (encodedTrialPairSuffix (count + 1) n first ++ output)))
        (by simpa [Nat.add_comm] using hfirst)
        (by
          rw [encodedTrialPairSuffix_succ]
          simpa [afterEmit, List.append_assoc] using hrest)
      simpa [trialPairLoopTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

private theorem trialPairLoopTime_le (count n first : ℕ) :
    trialPairLoopTime count n first ≤
      count * (2 * n + 2 * (first + count) + 6) +
        n + (first + count) + 3 := by
  induction count generalizing first with
  | zero => simp [trialPairLoopTime]
  | succ count ih =>
      have hrest := ih (first + 1)
      simp only [trialPairLoopTime, trialPairEmitTime,
        unaryEncodeNat_length]
      nlinarith

private def trialPair_prepare_evals
    (count n : ℕ) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .trimFirst) state [] (unaryEncodeNat n)
        (unaryEncodeNat (count + 2)) [] [] output)
      (some (trialPairCfg (some .loop) ⟨some true⟩ [] (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat 2) [] output))
      2 := by
  let middle := trialPairCfg (some .trimSecond) ⟨some true⟩ []
    (unaryEncodeNat n) (unaryEncodeNat (count + 1)) [] [] output
  have hfirst : EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .trimFirst) state [] (unaryEncodeNat n)
        (unaryEncodeNat (count + 2)) [] [] output)
      (some middle) 1 :=
    trialPairEvalsToInTimeOne (by
      simpa [middle, unaryEncodeNat] using trialPair_step_trimFirst_cons true
        (unaryEncodeNat n) (unaryEncodeNat (count + 1)) [] [] output state)
  have hsecond : EvalsToInTime trialDivisionPairComputer.step
      middle
      (some (trialPairCfg (some .loop) ⟨some true⟩ [] (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat 2) [] output)) 1 :=
    trialPairEvalsToInTimeOne (by
      simpa [middle, unaryEncodeNat] using trialPair_step_trimSecond_cons true
        (unaryEncodeNat n) (unaryEncodeNat count) [] [] output ⟨some true⟩)
  simpa using EvalsToInTime.trans trialDivisionPairComputer.step 1 1
    (trialPairCfg (some .trimFirst) state [] (unaryEncodeNat n)
      (unaryEncodeNat (count + 2)) [] [] output)
    middle
    (some (trialPairCfg (some .loop) ⟨some true⟩ [] (unaryEncodeNat n)
      (unaryEncodeNat count) (unaryEncodeNat 2) [] output))
    hfirst hsecond

private def trialPair_cleanup_evals
    (divisor dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .cleanupDivisor) state [] dividend [] divisor work
        output)
      (some (trialPairCfg none trialPairInitialState [] [] [] [] work output))
      (divisor.length + dividend.length + 2) := by
  have hdivisor := trialPair_cleanupDivisor_evals divisor dividend work output
    state
  have hdividend := trialPair_cleanupDividend_evals dividend work output ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (divisor.length + 1) (dividend.length + 1)
    (trialPairCfg (some .cleanupDivisor) state [] dividend [] divisor work
      output)
    (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] [] work
      output)
    (some (trialPairCfg none trialPairInitialState [] [] [] [] work output))
    hdivisor hdividend
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem unaryEncodeNat_reverse (n : ℕ) :
    (unaryEncodeNat n).reverse = unaryEncodeNat n := by
  rw [unaryEncodeNat_eq_replicate, List.reverse_replicate]

theorem trialPair_initList_eq_cfg (input : List Bool) :
    initList trialDivisionPairComputer input =
      trialPairCfg (some .scan) trialPairInitialState input [] [] [] [] [] := by
  unfold initList trialPairCfg
  congr
  funext index
  cases index <;> rfl

theorem trialPair_haltList_eq_cfg (output : List (Option Bool)) :
    haltList trialDivisionPairComputer output =
      trialPairCfg none trialPairInitialState [] [] [] [] [] output := by
  unfold haltList trialPairCfg
  congr
  funext index
  cases index <;> rfl

/-- The concrete generator emits every padded trial pair in at most
`8(n+1)^2` steps from unary input `n`. -/
def trialDivisionPairs_outputsInTime (n : ℕ) :
    TM2OutputsInTime trialDivisionPairComputer (unaryEncodeNat n)
      (some (RawUnaryPairList.encode (trialDivisionPairs n)))
      (8 * (n + 1) ^ 2) := by
  cases n with
  | zero =>
      have hscan := trialPair_scan_evals [] [] [] [] [] []
        trialPairInitialState
      let afterScan := trialPairCfg (some .trimFirst) ⟨none⟩ [] [] [] [] [] []
      have htrim : EvalsToInTime trialDivisionPairComputer.step afterScan
          (some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] [] [] [] []
            [])) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [afterScan] using trialPair_step_trimFirst_nil [] [] [] []
            ⟨none⟩)
      have hcleanup := trialPair_cleanup_evals [] [] [] [] ⟨none⟩
      have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step 1 1
        (trialPairCfg (some .scan) trialPairInitialState [] [] [] [] [] [])
        afterScan
        (some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] [] [] [] []
          []))
        (by simpa [afterScan] using hscan)
        htrim
      have hall := EvalsToInTime.trans trialDivisionPairComputer.step 2 2
        (trialPairCfg (some .scan) trialPairInitialState [] [] [] [] [] [])
        (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] [] [] [] [] [])
        (some (trialPairCfg none trialPairInitialState [] [] [] [] [] []))
        (by simpa using hfirst)
        (by simpa using hcleanup)
      have hmono := evalsToInTimeMono hall (by norm_num : 4 ≤ 8 * (0 + 1) ^ 2)
      rw [TM2OutputsInTime, trialPair_initList_eq_cfg]
      simp only [Option.map_some]
      rw [trialPair_haltList_eq_cfg]
      simpa [trialDivisionPairs, trialDivisors, RawUnaryPairList.encode] using
        hmono
  | succ n =>
      cases n with
      | zero =>
          have hscan := trialPair_scan_evals (unaryEncodeNat 1) [] [] [] [] []
            trialPairInitialState
          let afterScan := trialPairCfg (some .trimFirst) ⟨none⟩ []
            (unaryEncodeNat 1) (unaryEncodeNat 1) [] [] []
          let afterFirst := trialPairCfg (some .trimSecond) ⟨some true⟩ []
            (unaryEncodeNat 1) [] [] [] []
          let afterSecond := trialPairCfg (some .cleanupDivisor) ⟨none⟩ []
            (unaryEncodeNat 1) [] [] [] []
          have hfirstTrim : EvalsToInTime trialDivisionPairComputer.step
              afterScan (some afterFirst) 1 :=
            trialPairEvalsToInTimeOne (by
              simpa [afterScan, afterFirst, unaryEncodeNat] using
                trialPair_step_trimFirst_cons true (unaryEncodeNat 1) [] []
                  [] [] ⟨none⟩)
          have hsecondTrim : EvalsToInTime trialDivisionPairComputer.step
              afterFirst (some afterSecond) 1 :=
            trialPairEvalsToInTimeOne (by
              simpa [afterFirst, afterSecond] using
                trialPair_step_trimSecond_nil (unaryEncodeNat 1) [] [] []
                  ⟨some true⟩)
          have hcleanup := trialPair_cleanup_evals [] (unaryEncodeNat 1) [] []
            ⟨none⟩
          have hthroughFirst := EvalsToInTime.trans
            trialDivisionPairComputer.step 2 1
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat 1) [] [] [] [] [])
            afterScan
            (some afterFirst)
            (by
              simpa [afterScan, unaryEncodeNat_reverse] using hscan)
            hfirstTrim
          have hthroughSecond := EvalsToInTime.trans
            trialDivisionPairComputer.step 3 1
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat 1) [] [] [] [] [])
            afterFirst
            (some afterSecond)
            (by simpa using hthroughFirst)
            hsecondTrim
          have hall := EvalsToInTime.trans trialDivisionPairComputer.step 4 3
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat 1) [] [] [] [] [])
            afterSecond
            (some (trialPairCfg none trialPairInitialState [] [] [] [] [] []))
            (by simpa using hthroughSecond)
            (by simpa [afterSecond, unaryEncodeNat_length] using hcleanup)
          have hmono := evalsToInTimeMono hall
            (by norm_num : 7 ≤ 8 * (1 + 1) ^ 2)
          rw [TM2OutputsInTime, trialPair_initList_eq_cfg]
          simp only [Option.map_some]
          rw [trialPair_haltList_eq_cfg]
          simpa [trialDivisionPairs, trialDivisors, RawUnaryPairList.encode]
            using hmono
      | succ count =>
          let value := count + 2
          have hscan := trialPair_scan_evals (unaryEncodeNat value) [] [] []
            [] [] trialPairInitialState
          let afterScan := trialPairCfg (some .trimFirst) ⟨none⟩ []
            (unaryEncodeNat value) (unaryEncodeNat value) [] [] []
          have hprepare := trialPair_prepare_evals count value [] ⟨none⟩
          let afterPrepare := trialPairCfg (some .loop) ⟨some true⟩ []
            (unaryEncodeNat value) (unaryEncodeNat count)
            (unaryEncodeNat 2) [] []
          have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step
            ((unaryEncodeNat value).length + 1) 2
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat value) [] [] [] [] [])
            afterScan
            (some afterPrepare)
            (by
              simpa [afterScan, unaryEncodeNat_reverse] using hscan)
            (by simpa [afterScan, afterPrepare, value] using hprepare)
          have hloop := trialPair_loop_evals count value 2 [] ⟨some true⟩
          have hpairs :
              trialPairsFrom count value 2 = trialDivisionPairs value := by
            simpa [value] using trialPairsFrom_sub_two value
          have hall := EvalsToInTime.trans trialDivisionPairComputer.step
            (((unaryEncodeNat value).length + 1) + 2)
            (trialPairLoopTime count value 2)
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat value) [] [] [] [] [])
            afterPrepare
            (some (trialPairCfg none trialPairInitialState [] [] [] [] []
              (RawUnaryPairList.encode (trialDivisionPairs value))))
            (by simpa [Nat.add_comm] using hfirst)
            (by
              simpa [afterPrepare, encodedTrialPairSuffix, hpairs]
                using hloop)
          have hloopBound := trialPairLoopTime_le count value 2
          have hbound :
              ((unaryEncodeNat value).length + 1 + 2) +
                  trialPairLoopTime count value 2 ≤
                8 * (value + 1) ^ 2 := by
            simp only [unaryEncodeNat_length, value] at hloopBound ⊢
            nlinarith
          have hmono := evalsToInTimeMono
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hall)
            hbound
          rw [TM2OutputsInTime, trialPair_initList_eq_cfg]
          simp only [Option.map_some]
          rw [trialPair_haltList_eq_cfg]
          simpa [value] using hmono

/-- Genuine polynomial-time production of all unary-padded inputs needed to
test one candidate by bounded trial division. -/
noncomputable def trialDivisionPairsComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ (List (ℕ × ℕ)) unaryFinEncodingNat
      RawUnaryPairList.finEncoding trialDivisionPairs where
  tm := trialDivisionPairComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 8 * (Polynomial.X + 1) ^ 2
  outputsFun n := by
    simpa [unaryFinEncodingNat, RawUnaryPairList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        trialDivisionPairs_outputsInTime n


end LeanNPHardness.MachinePrimitives
