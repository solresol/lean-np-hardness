import LeanNPHardness.DictionaryLookup

/-!
# Conditional insertion and ordered dictionary construction

Insert a query only when absent, leaving the existing dictionary unchanged
otherwise. A right fold processes the tail first and therefore keeps the
rightmost occurrence of each input value, exactly as `List.dedup` does.

Only this auxiliary dictionary is deduplicated; no literal or clause of a
formula is removed. These executable definitions, semantic contracts and
framed output-size bounds do not supply a TM2 implementation or runtime bound.
-/

namespace LeanNPHardness

namespace DictionaryConstruction

/-- Keep every existing entry, prepending the query only when absent. -/
def insert (query : Nat) (dictionary : List Nat) : List Nat :=
  if query ∈ dictionary then dictionary else query :: dictionary

@[simp]
theorem insert_of_mem {query : Nat} {dictionary : List Nat}
    (h : query ∈ dictionary) : insert query dictionary = dictionary := by
  simp [insert, h]

@[simp]
theorem insert_of_not_mem {query : Nat} {dictionary : List Nat}
    (h : query ∉ dictionary) : insert query dictionary = query :: dictionary := by
  simp [insert, h]

/-- The checked lookup's dictionary-length sentinel selects the cons branch.
This is a semantic interface, not a runtime claim for testing that sentinel. -/
theorem insert_eq_lookup (query : Nat) (dictionary : List Nat) :
    insert query dictionary =
      if MachinePrimitives.DictionaryLookup.lookup (query, dictionary) = dictionary.length
      then query :: dictionary else dictionary := by
  have sentinel := MachinePrimitives.DictionaryLookup.lookup_eq_length_iff (query, dictionary)
  by_cases h : query ∈ dictionary
  · have index_ne : MachinePrimitives.DictionaryLookup.lookup (query, dictionary) ≠
        dictionary.length := fun equal => (sentinel.mp equal) h
    simp [insert, h, index_ne]
  · simp [insert, h, sentinel.mpr h]

@[simp]
theorem mem_insert (query value : Nat) (dictionary : List Nat) :
    value ∈ insert query dictionary ↔ value = query ∨ value ∈ dictionary := by
  by_cases h : query ∈ dictionary
  · simp only [insert_of_mem h]
    constructor
    · exact Or.inr
    · rintro (rfl | hv) <;> assumption
  · simp [insert_of_not_mem h]

theorem nodup_insert (query : Nat) {dictionary : List Nat}
    (h : dictionary.Nodup) : (insert query dictionary).Nodup := by
  by_cases hq : query ∈ dictionary <;> simp [insert, hq, h]

theorem insert_sublist (query : Nat) (dictionary : List Nat) :
    (insert query dictionary).Sublist (query :: dictionary) := by
  by_cases h : query ∈ dictionary
  · simp [h]
  · simp [h]

/-- Tail-first insertion into an existing dictionary. The seed is retained
verbatim, even when it already contains repetitions. -/
def extend (values dictionary : List Nat) : List Nat :=
  values.foldr insert dictionary

@[simp]
theorem extend_nil (dictionary : List Nat) : extend [] dictionary = dictionary := rfl

@[simp]
theorem extend_cons (query : Nat) (values dictionary : List Nat) :
    extend (query :: values) dictionary = insert query (extend values dictionary) := rfl

@[simp]
theorem mem_extend (value : Nat) (values dictionary : List Nat) :
    value ∈ extend values dictionary ↔ value ∈ values ∨ value ∈ dictionary := by
  induction values with
  | nil => simp
  | cons query values ih => simp [ih, or_assoc]

/-- Existing entries remain an unchanged suffix, including their repetitions. -/
theorem suffix_extend (values dictionary : List Nat) :
    dictionary.IsSuffix (extend values dictionary) := by
  induction values with
  | nil => simp
  | cons query values ih =>
      rw [extend_cons]
      by_cases h : query ∈ extend values dictionary
      · simpa [h] using ih
      · rw [insert_of_not_mem h]
        exact ih.trans (List.suffix_cons _ _)

theorem extend_sublist (values dictionary : List Nat) :
    (extend values dictionary).Sublist (values ++ dictionary) := by
  induction values with
  | nil => simp
  | cons query values ih =>
      exact (insert_sublist query _).trans (ih.cons_cons query)

/-- A duplicate-free seed gives precisely deduplication of the concatenation,
with the seed's occurrences taking precedence over those in `values`. -/
theorem extend_eq_dedup_append (values dictionary : List Nat)
    (h : dictionary.Nodup) :
    extend values dictionary = (values ++ dictionary).dedup := by
  induction values with
  | nil => simpa using h.dedup.symm
  | cons query values ih =>
      simp only [extend_cons, ih, List.cons_append, List.dedup_cons', insert]

theorem nodup_extend (values : List Nat) {dictionary : List Nat}
    (h : dictionary.Nodup) : (extend values dictionary).Nodup := by
  rw [extend_eq_dedup_append values dictionary h]
  exact List.nodup_dedup _

/-- Construct the auxiliary dictionary with rightmost-occurrence order. -/
def build (values : List Nat) : List Nat := extend values []

theorem build_eq_dedup (values : List Nat) : build values = values.dedup := by
  simpa [build] using extend_eq_dedup_append values [] (by simp)

theorem build_sublist (values : List Nat) : (build values).Sublist values := by
  simpa [build] using extend_sublist values []

theorem nodup_build (values : List Nat) : (build values).Nodup := by
  rw [build_eq_dedup]
  exact List.nodup_dedup _

/-- Full framed output size, including the updated binary count header. -/
theorem extend_encode_length_le (values dictionary : List Nat) :
    (BinaryNatLists.encodeNatList (extend values dictionary)).length ≤
      (BinaryNatLists.encodeNatList (values ++ dictionary)).length :=
  BinaryNatLists.encodeNatList_length_le_of_sublist (extend_sublist values dictionary)

theorem build_encode_length_le (values : List Nat) :
    (BinaryNatLists.encodeNatList (build values)).length ≤
      (BinaryNatLists.encodeNatList values).length :=
  BinaryNatLists.encodeNatList_length_le_of_sublist (build_sublist values)

/-- The construction produces the dictionary already used by dense renaming. -/
theorem build_vars (formula : CNF.Formula Nat) :
    build formula.vars = formula.variableDictionary :=
  build_eq_dedup formula.vars

end DictionaryConstruction

namespace CNF.Formula

/-- The complete variable-occurrence list is linear in the original formula
bits. Polarity is dropped, but no occurrence is removed. -/
theorem vars_encode_length_le (formula : Formula Nat) :
    (BinaryNatLists.encodeNatList formula.vars).length ≤ 3 * formula.encodedSize + 1 := by
  have hlen := formula.vars_length_le_encodedSize
  have hsum := formula.vars_payloadSize_le_encodedSize
  have hheader := BinaryNatLists.natWireSize_le_two_mul_add_one formula.vars.length
  rw [BinaryNatLists.encodeNatList_length, BinaryNatLists.listWireSize]
  omega

/-- Deduplicating only the auxiliary dictionary cannot increase that bound.
This is an output-size theorem, independent of construction runtime. -/
theorem variableDictionary_encode_length_le (formula : Formula Nat) :
    (BinaryNatLists.encodeNatList formula.variableDictionary).length ≤
      3 * formula.encodedSize + 1 := by
  rw [← DictionaryConstruction.build_vars]
  exact (DictionaryConstruction.build_encode_length_le formula.vars).trans
    formula.vars_encode_length_le

end CNF.Formula

end LeanNPHardness
