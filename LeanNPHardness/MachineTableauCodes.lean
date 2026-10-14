import LeanNPHardness.CNFRegisterConstraint
import Mathlib.Data.Nat.Size

/-!
# Codes and list helpers for the machine tableau

Elements of finite lists are coded by their index; optional values are
coded with `0` for absence. `takeSome` extracts the longest prefix of present
values. These are the bookkeeping lemmas used to represent a TM2
configuration by bounded registers.
-/

namespace LeanNPHardness.MachineTableau

/-- The code of a list element: its first index, classically. -/
noncomputable def codeIn {α : Type} (L : List α) (x : α) : ℕ := by
  classical exact L.idxOf x

/-- Decode a code by indexing. -/
def decodeIn {α : Type} (L : List α) (i : ℕ) : Option α := L[i]?

theorem codeIn_lt {α : Type} (L : List α) (x : α) (h : x ∈ L) : codeIn L x < L.length := by
  classical
  simp only [codeIn]
  exact List.idxOf_lt_length_iff.mpr h

@[simp]
theorem decodeIn_codeIn {α : Type} (L : List α) (x : α) (h : x ∈ L) :
    decodeIn L (codeIn L x) = some x := by
  classical
  simp only [codeIn, decodeIn]
  exact List.getElem?_idxOf h

/-- In a duplicate-free list, the code of the element at `m` is `m`. -/
theorem codeIn_getElem {α : Type} (L : List α) (hL : L.Nodup) (m : ℕ) (hm : m < L.length) :
    codeIn L (L[m]'hm) = m := by
  have h := decodeIn_codeIn L (L[m]'hm) (List.getElem_mem hm)
  simp only [decodeIn] at h
  obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.mp h
  exact (hL.getElem_inj_iff.mp hval)

theorem codeIn_injective {α : Type} (L : List α) (x y : α) (hx : x ∈ L) (hy : y ∈ L)
    (h : codeIn L x = codeIn L y) : x = y := by
  have := decodeIn_codeIn L x hx
  rw [h, decodeIn_codeIn L y hy] at this
  exact (Option.some.inj this).symm

/-- Code an optional value, reserving `0` for absence. -/
noncomputable def optionCode {α : Type} (L : List α) : Option α → ℕ
  | none => 0
  | some x => codeIn L x + 1

/-- Decode an optional value. -/
def optionDecode {α : Type} (L : List α) : ℕ → Option α
  | 0 => none
  | i + 1 => decodeIn L i

@[simp]
theorem optionCode_none {α : Type} (L : List α) : optionCode L (none : Option α) = 0 := rfl

@[simp]
theorem optionCode_some {α : Type} (L : List α) (x : α) :
    optionCode L (some x) = codeIn L x + 1 := rfl

@[simp]
theorem optionDecode_zero {α : Type} (L : List α) : optionDecode L 0 = (none : Option α) := rfl

theorem optionDecode_optionCode {α : Type} (L : List α) (o : Option α)
    (h : ∀ x ∈ o, x ∈ L) : optionDecode L (optionCode L o) = o := by
  cases o with
  | none => rfl
  | some x => simp [optionCode, optionDecode, decodeIn_codeIn L x (h x rfl)]

theorem optionCode_le {α : Type} (L : List α) (o : Option α) (h : ∀ x ∈ o, x ∈ L) :
    optionCode L o ≤ L.length := by
  cases o with
  | none => simp
  | some x => simpa [optionCode] using codeIn_lt L x (h x rfl)

theorem optionCode_eq_zero_iff {α : Type} (L : List α) (o : Option α) :
    optionCode L o = 0 ↔ o = none := by
  cases o <;> simp

theorem optionCode_injective {α : Type} (L : List α) (o o' : Option α)
    (h : ∀ x ∈ o, x ∈ L) (h' : ∀ x ∈ o', x ∈ L)
    (heq : optionCode L o = optionCode L o') : o = o' := by
  rw [← optionDecode_optionCode L o h, ← optionDecode_optionCode L o' h', heq]

/-- The longest prefix of present values. -/
def takeSome {α : Type} : List (Option α) → List α
  | [] => []
  | none :: _ => []
  | some x :: rest => x :: takeSome rest

theorem takeSome_length_le {α : Type} (l : List (Option α)) : (takeSome l).length ≤ l.length := by
  induction l with
  | nil => simp [takeSome]
  | cons o rest ih =>
      cases o with
      | none => simp [takeSome]
      | some x => simp [takeSome]; omega

/-- Entries inside the extracted prefix are present and agree with it. -/
theorem takeSome_getElem? {α : Type} (l : List (Option α)) (i : ℕ) (hi : i < (takeSome l).length) :
    l[i]? = some (some ((takeSome l)[i]'hi)) := by
  induction l generalizing i with
  | nil => simp [takeSome] at hi
  | cons o rest ih =>
      cases o with
      | none => simp [takeSome] at hi
      | some x =>
          cases i with
          | zero => simp [takeSome]
          | succ i =>
              simp only [takeSome, List.length_cons, Nat.add_lt_add_iff_right] at hi
              simp only [List.getElem?_cons_succ, takeSome, List.getElem_cons_succ]
              exact ih i hi

/-- The entry just after the extracted prefix is absent, when it exists. -/
theorem takeSome_getElem?_length {α : Type} (l : List (Option α))
    (h : (takeSome l).length < l.length) : l[(takeSome l).length]? = some none := by
  induction l with
  | nil => simp at h
  | cons o rest ih =>
      cases o with
      | none => simp [takeSome]
      | some x =>
          simp only [takeSome, List.length_cons, Nat.add_lt_add_iff_right] at h
          simp only [takeSome, List.length_cons, List.getElem?_cons_succ]
          exact ih h

/-- Extracting the present prefix of a list's own optional entries gives a
prefix of the list. -/
theorem takeSome_map_getElem? {α : Type} (l : List α) (D : ℕ) :
    takeSome ((List.range D).map fun i => l[i]?) = l.take D := by
  induction D generalizing l with
  | zero => simp [takeSome]
  | succ D ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      cases l with
      | nil => simp [takeSome]
      | cons x xs =>
          simp only [List.getElem?_cons_zero, takeSome, List.take_succ_cons, List.cons.injEq, true_and]
          rw [← ih xs]
          rfl

/-- Indexing into a flat map whose pieces have uniform length. -/
theorem getElem?_flatMap_uniform {α β : Type} (L : List α) (f : α → List β) (D : ℕ)
    (hf : ∀ x, (f x).length = D) (m i : ℕ) (hm : m < L.length) (hi : i < D) :
    (L.flatMap f)[m * D + i]? = (f (L[m]'hm))[i]? := by
  induction L generalizing m with
  | nil => simp at hm
  | cons x xs ih =>
      cases m with
      | zero =>
          simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
          rw [List.getElem?_append_left (by rw [hf]; exact hi)]
      | succ m =>
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem?_append_right (by rw [hf]; rw [Nat.succ_mul]; omega)]
          rw [hf, show (m + 1) * D + i - D = m * D + i by rw [Nat.succ_mul]; omega]
          exact ih m (by simpa using hm)

theorem le_foldr_max (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldr_cons]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

end LeanNPHardness.MachineTableau
