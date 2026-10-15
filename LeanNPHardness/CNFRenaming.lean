import LeanNPHardness.CNFCertificate
import LeanNPHardness.UnaryCNF

/-!
# Dense renaming of CNF variables

Only the auxiliary variable dictionary is deduplicated. The formula retains
every literal and clause occurrence, in order. Dictionary indices give small
variable names even when the original names have large binary values.

The executable construction, assignment transport, and output-size bounds
are separate from a polynomial-time TM2 implementation, which is not supplied
by this module.
-/

namespace LeanNPHardness.CNF

universe u v

namespace Literal

/-- Change the variable name while retaining polarity. -/
def rename {α : Type u} {β : Type v} (f : α → β) : Literal α → Literal β
  | .positive x => .positive (f x)
  | .negative x => .negative (f x)

@[simp]
theorem var_rename {α : Type u} {β : Type v} (f : α → β) (l : Literal α) :
    (l.rename f).var = f l.var := by
  cases l <;> rfl

@[simp]
theorem eval_rename {α : Type u} {β : Type v} (f : α → β)
    (a : Assignment β) (l : Literal α) :
    (l.rename f).eval a = l.eval (a ∘ f) := by
  cases l <;> rfl

end Literal

namespace Formula

/-- Rename without changing the nested-list shape or any multiplicities. -/
def rename {α : Type u} {β : Type v} (f : α → β) (F : Formula α) : Formula β :=
  F.map (List.map (Literal.rename f))

@[simp]
theorem rename_length {α : Type u} {β : Type v} (f : α → β) (F : Formula α) :
    (F.rename f).length = F.length := by
  simp [rename]

theorem rename_clause_lengths {α : Type u} {β : Type v}
    (f : α → β) (F : Formula α) :
    (F.rename f).map List.length = F.map List.length := by
  simp [rename, List.map_map, Function.comp_def]

@[simp]
theorem exactWidth_rename {α : Type u} {β : Type v}
    (f : α → β) (F : Formula α) (k : Nat) :
    (F.rename f).ExactWidth k ↔ F.ExactWidth k := by
  simp [ExactWidth, rename]

@[simp]
theorem vars_rename {α : Type u} {β : Type v} (f : α → β) (F : Formula α) :
    (F.rename f).vars = F.vars.map f := by
  simp [rename, vars, Clause.vars, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

@[simp]
theorem eval_rename {α : Type u} {β : Type v} (f : α → β)
    (a : Assignment β) (F : Formula α) :
    (F.rename f).eval a = F.eval (a ∘ f) := by
  simp [rename, eval, Clause.eval, List.all_map, List.any_map, Function.comp_def]
  rfl

/-- The dictionary contains each occurring variable once. `List.dedup` keeps
the rightmost occurrence; no formula occurrence is removed. -/
def variableDictionary (F : Formula Nat) : List Nat := F.vars.dedup

@[simp]
theorem mem_variableDictionary (F : Formula Nat) (x : Nat) :
    x ∈ F.variableDictionary ↔ x ∈ F.vars := by
  simp [variableDictionary]

theorem variableDictionary_length_le (F : Formula Nat) :
    F.variableDictionary.length ≤ F.vars.length :=
  F.vars.dedup_sublist.length_le

/-- The index of an occurring variable in the finite dictionary. Off the
formula's support this returns the dictionary length. -/
def denseIndex (F : Formula Nat) (x : Nat) : Nat := F.variableDictionary.idxOf x

theorem denseIndex_lt (F : Formula Nat) (x : Nat) (hx : x ∈ F.vars) :
    F.denseIndex x < F.variableDictionary.length :=
  List.idxOf_lt_length_of_mem ((F.mem_variableDictionary x).2 hx)

theorem denseIndex_inj (F : Formula Nat) (x y : Nat) (hx : x ∈ F.vars) :
    F.denseIndex x = F.denseIndex y ↔ x = y :=
  List.idxOf_inj ((F.mem_variableDictionary x).2 hx)

/-- Rename the formula to indices of its variable dictionary. -/
def denseRename (F : Formula Nat) : Formula Nat := F.rename F.denseIndex

/-- Extend an original assignment to all dense indices; unused indices are
false. -/
def denseAssignment (F : Formula Nat) (a : Assignment Nat) : Assignment Nat :=
  fun i => (F.variableDictionary[i]?).elim false a

theorem denseAssignment_denseIndex (F : Formula Nat) (a : Assignment Nat)
    (x : Nat) (hx : x ∈ F.vars) :
    F.denseAssignment a (F.denseIndex x) = a x := by
  simp [denseAssignment, denseIndex,
    List.getElem?_idxOf ((F.mem_variableDictionary x).2 hx)]

/-- Pulling back any assignment gives exactly the same Boolean evaluation. -/
theorem eval_denseRename (F : Formula Nat) (a : Assignment Nat) :
    F.denseRename.eval a = F.eval (a ∘ F.denseIndex) :=
  F.eval_rename F.denseIndex a

/-- Every original assignment has an evaluation-preserving dense assignment. -/
theorem eval_denseRename_denseAssignment (F : Formula Nat) (a : Assignment Nat) :
    F.denseRename.eval (F.denseAssignment a) = F.eval a := by
  rw [eval_denseRename]
  exact F.eval_congr (F.denseAssignment_denseIndex a)

theorem satisfiable_denseRename (F : Formula Nat) :
    F.denseRename.Satisfiable ↔ F.Satisfiable := by
  rw [satisfiable_iff_exists_eval, satisfiable_iff_exists_eval]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a ∘ F.denseIndex, (F.eval_denseRename a) ▸ ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨F.denseAssignment a, (F.eval_denseRename_denseAssignment a).trans ha⟩

theorem denseRename_clause_lengths (F : Formula Nat) :
    F.denseRename.map List.length = F.map List.length :=
  F.rename_clause_lengths F.denseIndex

theorem exactWidth_denseRename (F : Formula Nat) (k : Nat) :
    F.denseRename.ExactWidth k ↔ F.ExactWidth k :=
  F.exactWidth_rename F.denseIndex k

/-- Every variable in the renamed formula is strictly below the dictionary
size, hence below the number of original variable occurrences. -/
theorem denseRename_var_lt (F : Formula Nat) (x : Nat)
    (hx : x ∈ F.denseRename.vars) : x < F.variableDictionary.length := by
  rw [denseRename, vars_rename, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact F.denseIndex_lt y hy

/-- The renamed support is precisely the initial interval of dictionary
indices: there are no gaps, even when occurrences repeat. -/
theorem mem_vars_denseRename (F : Formula Nat) (x : Nat) :
    x ∈ F.denseRename.vars ↔ x < F.variableDictionary.length := by
  refine ⟨F.denseRename_var_lt x, fun hx => ?_⟩
  rw [denseRename, vars_rename, List.mem_map]
  refine ⟨F.variableDictionary[x],
    (F.mem_variableDictionary _).1 (List.getElem_mem hx), ?_⟩
  exact (List.nodup_dedup F.vars).idxOf_getElem x hx

theorem denseRename_var_lt_encodedSize (F : Formula Nat) (x : Nat)
    (hx : x ∈ F.denseRename.vars) : x < F.encodedSize :=
  (F.denseRename_var_lt x hx).trans_le
    (F.variableDictionary_length_le.trans F.vars_length_le_encodedSize)

end Formula

namespace Unary

/-- With all variable indices below `bound`, each literal occupies at most
`bound` unary symbols. Every clause contributes one extra end marker. -/
theorem encode_length_le_of_vars_lt (F : Formula Nat) (bound : Nat)
    (h : ∀ x ∈ F.vars, x < bound) :
    (encode F).length ≤ F.vars.length * bound + F.length := by
  have clause_bound (c : Clause Nat) (hc : ∀ l ∈ c, l.var < bound) :
      (encodeClause c).length ≤ c.length * bound + 1 := by
    have lits_bound : (c.flatMap encodeLiteral).length ≤ c.length * bound := by
      induction c with
      | nil => simp
      | cons l c ih =>
          have hl : (encodeLiteral l).length ≤ bound := by
            have hv := hc l (by simp)
            cases l <;> simpa [encodeLiteral, Literal.var] using Nat.succ_le_of_lt hv
          have ht := ih (fun l hl => hc l (by simp [hl]))
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          calc
            _ ≤ bound + c.length * bound := Nat.add_le_add hl ht
            _ = _ := by simp [Nat.add_mul, Nat.add_comm]
    simpa [encodeClause] using Nat.add_le_add_right lits_bound 1
  induction F with
  | nil => simp [Formula.vars]
  | cons c F ih =>
      have hc := clause_bound c (fun l hl => h l.var (by
        simp only [Formula.vars, List.flatMap_cons, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨l, hl, rfl⟩)))
      have ht := ih (fun x hx => h x (by simp [Formula.vars] at hx ⊢; exact Or.inr hx))
      rw [encode_cons, List.length_append]
      calc
        _ ≤ c.length * bound + 1 + ((Formula.vars F).length * bound + F.length) :=
          Nat.add_le_add hc ht
        _ = _ := by simp [Formula.vars, Clause.vars, Nat.add_mul]; omega

end Unary

namespace Formula

/-- A unary representation of the renamed formula is quadratic in the
original binary input length. This bounds output size, not runtime. -/
theorem denseRename_unary_length_le (F : Formula Nat) :
    (Unary.encode F.denseRename).length ≤ F.encodedSize * (F.encodedSize + 1) := by
  have h := Unary.encode_length_le_of_vars_lt F.denseRename F.variableDictionary.length
    (F.denseRename_var_lt)
  have hd := F.variableDictionary_length_le.trans F.vars_length_le_encodedSize
  have hv := F.vars_length_le_encodedSize
  have hc : F.length ≤ F.encodedSize := by
    have := BinaryNatLists.length_le_wireSize F.toNatLists
    simpa [toNatLists, encodedSize, BinaryNatLists.wireSize,
      BinaryNatLists.listWireSize, List.map_map, Function.comp_def] using this
  simp only [denseRename, vars_rename, List.length_map, rename_length] at h
  calc
    _ ≤ F.vars.length * F.variableDictionary.length + F.length := h
    _ ≤ F.encodedSize * F.encodedSize + F.encodedSize :=
      Nat.add_le_add (Nat.mul_le_mul hv hd) hc
    _ = _ := by simp [Nat.mul_add]

end Formula

/-- Exact k-SAT membership is preserved, including its positive-width guard. -/
theorem exactKSAT_denseRename (k : Nat) (F : Formula Nat) :
    ExactKSAT k F.denseRename ↔ ExactKSAT k F := by
  simp only [ExactKSAT, Formula.exactWidth_denseRename, Formula.satisfiable_denseRename]

end LeanNPHardness.CNF
