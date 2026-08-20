import Mathlib.Computability.Encoding

namespace LeanNPHardness

open Computability

namespace PairEncoding

/-- Project the symbols belonging to the left component of a tagged alphabet. -/
def leftSymbols {Γ Δ : Type} : List (Sum Γ Δ) → List Γ
  | [] => []
  | Sum.inl symbol :: symbols => symbol :: leftSymbols symbols
  | Sum.inr _ :: symbols => leftSymbols symbols

/-- Project the symbols belonging to the right component of a tagged alphabet. -/
def rightSymbols {Γ Δ : Type} : List (Sum Γ Δ) → List Δ
  | [] => []
  | Sum.inl _ :: symbols => rightSymbols symbols
  | Sum.inr symbol :: symbols => symbol :: rightSymbols symbols

@[simp]
theorem leftSymbols_append {Γ Δ : Type} (first second : List (Sum Γ Δ)) :
    leftSymbols (first ++ second) = leftSymbols first ++ leftSymbols second := by
  induction first with
  | nil => rfl
  | cons symbol symbols ih =>
      cases symbol <;> simp [leftSymbols, ih]

@[simp]
theorem rightSymbols_append {Γ Δ : Type} (first second : List (Sum Γ Δ)) :
    rightSymbols (first ++ second) = rightSymbols first ++ rightSymbols second := by
  induction first with
  | nil => rfl
  | cons symbol symbols ih =>
      cases symbol <;> simp [rightSymbols, ih]

@[simp]
theorem leftSymbols_map_inl {Γ Δ : Type} (symbols : List Γ) :
    leftSymbols (symbols.map (Sum.inl : Γ → Sum Γ Δ)) = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih => simp [leftSymbols, ih]

@[simp]
theorem leftSymbols_map_inr {Γ Δ : Type} (symbols : List Δ) :
    leftSymbols (symbols.map (Sum.inr : Δ → Sum Γ Δ)) = [] := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih => simp [leftSymbols, ih]

@[simp]
theorem rightSymbols_map_inl {Γ Δ : Type} (symbols : List Γ) :
    rightSymbols (symbols.map (Sum.inl : Γ → Sum Γ Δ)) = [] := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih => simp [rightSymbols, ih]

@[simp]
theorem rightSymbols_map_inr {Γ Δ : Type} (symbols : List Δ) :
    rightSymbols (symbols.map (Sum.inr : Δ → Sum Γ Δ)) = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih => simp [rightSymbols, ih]

/-- A finite encoding of pairs using disjoint tagged copies of the component
alphabets. The tags make concatenation unambiguous even when either component
has an empty encoding. -/
def finEncoding {α β : Type} (left : FinEncoding α) (right : FinEncoding β) :
    FinEncoding (α × β) where
  Γ := Sum left.Γ right.Γ
  encode pair :=
    (left.encode pair.1).map Sum.inl ++ (right.encode pair.2).map Sum.inr
  decode symbols :=
    match left.decode (leftSymbols symbols), right.decode (rightSymbols symbols) with
    | some first, some second => some (first, second)
    | _, _ => none
  decode_encode pair := by
    simp [left.decode_encode, right.decode_encode]
  ΓFin := inferInstance

@[simp]
theorem finEncoding_encode {α β : Type} (left : FinEncoding α)
    (right : FinEncoding β) (pair : α × β) :
    (finEncoding left right).encode pair =
      (left.encode pair.1).map Sum.inl ++ (right.encode pair.2).map Sum.inr :=
  rfl

/-- The tagged pair encoding has exactly the sum of the two component lengths. -/
@[simp]
theorem finEncoding_encode_length {α β : Type} (left : FinEncoding α)
    (right : FinEncoding β) (pair : α × β) :
    ((finEncoding left right).encode pair).length =
      (left.encode pair.1).length + (right.encode pair.2).length := by
  simp [finEncoding]

end PairEncoding

end LeanNPHardness
