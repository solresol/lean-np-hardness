import Mathlib.Computability.TuringMachine.Computable

/-!
# Bundled finite encodings

mathlib (May 2026) unbundled the alphabet from `Computability.Encoding` and
changed `Turing.TM2ComputableInPolyTime` to take bare encoding functions. This
library, and the downstream thesis formalisation, reason throughout about an
encoding together with its finite alphabet, so this module restores the bundled
`FinEncoding` interface on top of the current mathlib API.

`TM2ComputableInPolyTime ea eb f` is *definitionally* mathlib's
`Turing.TM2ComputableInPolyTime ea.encode eb.encode f`, so no machine model or
runtime measure changes: the input size is still the length of `ea.encode x`.
-/

universe u

namespace LeanNPHardness

open Computability

/-- An encoding of `α` over a finite alphabet `Γ`, bundled with that alphabet.
The fields match the pre-2026 mathlib `Computability.FinEncoding`. -/
structure FinEncoding (α : Type u) where
  /-- The alphabet. -/
  Γ : Type
  /-- The encoding function. -/
  encode : α → List Γ
  /-- The decoding function. -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x
  /-- The alphabet is finite. -/
  ΓFin : Fintype Γ

attribute [instance] FinEncoding.ΓFin
attribute [simp] FinEncoding.decode_encode

namespace FinEncoding

/-- Bundle an unbundled mathlib encoding over a finite alphabet. -/
@[reducible]
def ofEncoding {α : Type u} {Γ : Type} [Fintype Γ] (e : Encoding α Γ) :
    FinEncoding α where
  Γ := Γ
  encode := e.encode
  decode := e.decode
  decode_encode := e.decode_encode
  ΓFin := inferInstance

/-- The underlying unbundled mathlib encoding. -/
def toEncoding {α : Type u} (e : FinEncoding α) : Encoding α e.Γ where
  encode := e.encode
  decode := e.decode
  decode_encode := e.decode_encode

theorem encode_injective {α : Type u} (e : FinEncoding α) :
    Function.Injective e.encode :=
  e.toEncoding.encode_injective

end FinEncoding

/-! The unbundled mathlib encodings are plain definitions, so their fields no
longer reduce under `simp`. These lemmas restore the reductions that the old
structure-literal definitions provided. -/

@[simp] theorem encodingNatBool_encode : encodingNatBool.encode = encodeNat := rfl
@[simp] theorem encodingNatBool_decode (l : List Bool) :
    encodingNatBool.decode l = some (decodeNat l) := rfl
@[simp] theorem encodingNatΓ'_encode :
    encodingNatΓ'.encode = fun n => (encodeNat n).map inclusionBoolΓ' := rfl
@[simp] theorem unaryEncodingNat_encode : unaryEncodingNat.encode = unaryEncodeNat := rfl
@[simp] theorem unaryEncodingNat_decode (l : List Bool) :
    unaryEncodingNat.decode l = some (unaryDecodeNat l) := rfl
@[simp] theorem encodingBoolBool_encode : encodingBoolBool.encode = encodeBool := rfl
@[simp] theorem encodingBoolBool_decode (l : List Bool) :
    encodingBoolBool.decode l = some (decodeBool l) := rfl
@[simp] theorem encodeBool_apply (b : Bool) : encodeBool b = [b] := rfl

/-- Binary encoding of natural numbers over `Bool`. -/
@[reducible]
def finEncodingNatBool : FinEncoding ℕ :=
  FinEncoding.ofEncoding encodingNatBool

/-- Binary encoding of natural numbers over mathlib's `Γ'`. -/
@[reducible]
def finEncodingNatΓ' : FinEncoding ℕ :=
  FinEncoding.ofEncoding encodingNatΓ'

/-- Unary encoding of natural numbers over `Bool`. -/
@[reducible]
def unaryFinEncodingNat : FinEncoding ℕ :=
  FinEncoding.ofEncoding unaryEncodingNat

/-- Encoding of a Boolean as a single symbol. -/
@[reducible]
def finEncodingBoolBool : FinEncoding Bool :=
  FinEncoding.ofEncoding encodingBoolBool

/-- A function computed by a finite two-stack Turing machine, with the bundled
alphabets supplied to mathlib's `Turing.TM2Computable`. -/
abbrev TM2Computable {α β : Type} (ea : FinEncoding α)
    (eb : FinEncoding β) (f : α → β) : Type 1 :=
  Turing.TM2Computable (αΓ := ea.Γ) (βΓ := eb.Γ) ea.encode eb.encode f

/-- A function computed by a finite two-stack Turing machine within an explicit
time function, with the bundled alphabets supplied to mathlib's
`Turing.TM2ComputableInTime`. -/
abbrev TM2ComputableInTime {α β : Type} (ea : FinEncoding α)
    (eb : FinEncoding β) (f : α → β) : Type 1 :=
  Turing.TM2ComputableInTime (αΓ := ea.Γ) (βΓ := eb.Γ) ea.encode eb.encode f

/-- A function computed by a finite two-stack Turing machine in polynomial time,
measured in the length of the bundled source encoding. This is mathlib's
`Turing.TM2ComputableInPolyTime` with the bundled alphabets supplied. -/
abbrev TM2ComputableInPolyTime {α β : Type} (ea : FinEncoding α)
    (eb : FinEncoding β) (f : α → β) : Type 1 :=
  Turing.TM2ComputableInPolyTime (αΓ := ea.Γ) (βΓ := eb.Γ) ea.encode eb.encode f

/-- The identity is computable in polynomial time for any bundled encoding. -/
noncomputable def idComputableInPolyTime {α : Type} (ea : FinEncoding α) :
    TM2ComputableInPolyTime ea ea id :=
  Turing.idComputableInPolyTime ea.encode

end LeanNPHardness
