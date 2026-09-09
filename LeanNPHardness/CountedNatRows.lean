import LeanNPHardness.RawNatEncoding

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness

open Computability

namespace CountedNatRows

/-- Count-prefixed source fields for every domain row. -/
def rowFields (domains : List (List ℕ)) : List ℕ :=
  domains.flatMap fun domain => domain.length :: domain

/-- Complete domain-section fields: domain count followed by counted rows. -/
def inputFields (domains : List (List ℕ)) : List ℕ :=
  domains.length :: rowFields domains

/-- Source-order raw encoding of the complete counted domain section. -/
def inputEncode (domains : List (List ℕ)) : List (Option Bool) :=
  SourceOrderRawFields.encode (inputFields domains)

/-- The local field encoding is exactly the checked source-order encoding of
the nested domain list, rather than a bespoke unit-cell representation. -/
theorem inputEncode_eq_sourceOrderRawNatLists
    (domains : List (List ℕ)) :
    inputEncode domains = SourceOrderRawNatLists.encode domains := by
  rw [inputEncode, SourceOrderRawNatLists.encode_eq_payloads]
  simp only [SourceOrderRawFields.encode, inputFields, rowFields,
    RawNatLists.payloads, List.flatMap_cons]
  congr 1
  induction domains with
  | nil => rfl
  | cons domain domains ih =>
      simp [ih, List.flatMap_map]

/-- Parse exactly the declared number of count-prefixed domain rows. -/
def parseRows : ℕ → List ℕ → Option (List (List ℕ))
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | count + 1, rowCount :: fields => do
      if rowCount ≤ fields.length then
        let row := fields.take rowCount
        let rest := fields.drop rowCount
        pure (row :: (← parseRows count rest))
      else
        none

@[simp]
theorem parseRows_rowFields (domains : List (List ℕ)) :
    parseRows domains.length (rowFields domains) = some domains := by
  induction domains with
  | nil => rfl
  | cons domain domains ih =>
      change parseRows (Nat.succ domains.length)
        (domain.length :: domain ++ rowFields domains) =
          some (domain :: domains)
      simp [parseRows, ih]

/-- Decode the complete domain section and check its outer and row counts. -/
def inputDecode (input : List (Option Bool)) : Option (List (List ℕ)) := do
  match ← SourceOrderRawFields.decode input with
  | count :: fields => parseRows count fields
  | [] => none

@[simp]
theorem inputDecode_encode (domains : List (List ℕ)) :
    inputDecode (inputEncode domains) = some domains := by
  simp [inputDecode, inputEncode, inputFields]

/-- Checked source-order encoding for a complete domain section. -/
def inputFinEncoding : FinEncoding (List (List ℕ)) where
  Γ := Option Bool
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

/-- Source-order raw encoding after the redundant outer domain count has been
removed.  Each remaining row still begins with its checked value count. -/
def rowPayloadEncode (domains : List (List ℕ)) : List (Option Bool) :=
  SourceOrderRawFields.encode (rowFields domains)

/-- Parse count-prefixed rows until the payload is exhausted.  Unlike
`parseRows`, this parser needs no supplied outer count: each recursive call
removes the current row-count field even when that row is empty. -/
def parseRowPayload : (fields : List ℕ) → Option (List (List ℕ))
  | [] => some []
  | rowCount :: fields => do
      if rowCount ≤ fields.length then
        let row := fields.take rowCount
        let rest := fields.drop rowCount
        pure (row :: (← parseRowPayload rest))
      else
        none
termination_by fields => fields.length
decreasing_by
  simp_wf
  omega

@[simp]
theorem parseRowPayload_rowFields (domains : List (List ℕ)) :
    parseRowPayload (rowFields domains) = some domains := by
  induction domains with
  | nil => simp [rowFields, parseRowPayload]
  | cons domain domains ih =>
      change parseRowPayload
        (domain.length :: domain ++ rowFields domains) =
          some (domain :: domains)
      rw [parseRowPayload.eq_def]
      simp [ih]

/-- Count-prefixed row payloads determine all domain boundaries uniquely,
even though the redundant outer domain count is absent. -/
theorem rowFields_injective : Function.Injective rowFields := by
  intro left right heq
  have hdecoded := congrArg parseRowPayload heq
  simpa using hdecoded

/-- Decode the exhaustion-delimited row payload and recheck every row count.
Malformed counts and trailing partial rows are rejected. -/
def rowPayloadDecode (input : List (Option Bool)) :
    Option (List (List ℕ)) := do
  parseRowPayload (← SourceOrderRawFields.decode input)

@[simp]
theorem rowPayloadDecode_encode (domains : List (List ℕ)) :
    rowPayloadDecode (rowPayloadEncode domains) = some domains := by
  simp [rowPayloadDecode, rowPayloadEncode]

theorem rowPayloadEncode_injective : Function.Injective rowPayloadEncode := by
  intro left right heq
  have hdecoded := congrArg rowPayloadDecode heq
  simpa using hdecoded

/-- Checked structured encoding of the domain-row payload.  The semantic type
retains the domain boundaries needed by the indexed-row driver even though the
wire format contains no outer count. -/
def rowPayloadFinEncoding : FinEncoding (List (List ℕ)) where
  Γ := Option Bool
  encode := rowPayloadEncode
  decode := rowPayloadDecode
  decode_encode := rowPayloadDecode_encode
  ΓFin := inferInstance

/-- Removing the outer count never increases the exact raw bit-cell length. -/
theorem rowPayloadEncode_length_le_inputEncode_length
    (domains : List (List ℕ)) :
    (rowPayloadEncode domains).length ≤ (inputEncode domains).length := by
  simp only [rowPayloadEncode, inputEncode, inputFields,
    SourceOrderRawFields.encode, List.flatMap_cons, List.length_append,
    List.length_cons, List.length_map]
  omega

end CountedNatRows

end LeanNPHardness
