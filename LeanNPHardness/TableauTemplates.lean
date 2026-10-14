import LeanNPHardness.TableauSkeleton

/-!
# Constant templates of the skeleton

Every cell descriptor of the skeleton is one of finitely many constants:
phantom cells, the `2D` special real cells, the generic real cell, zero
fixes, symbol fixes, certificate chains, and the output fix. The
decompositions `range_P_map_cellTrans`, `range_P_map_initCellDesc`, and
`range_P_map_finalCellDesc` write each stack's cell descriptors as
concatenations of replicated constants (and the input's symbols), which is
exactly what the emitter machine produces with loops over unary counters.
-/

namespace LeanNPHardness.MachineTableau

open CNF CNF.Unary CNF.Constraint TableauJobs Tableau MachineLocality

theorem map_range_getElem? {α β : Type} (l : List α) (f : α → β) (d : β) :
    (List.range l.length).map (fun i => (l[i]?.map f).getD d) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons]
      simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some, List.cons.injEq,
        true_and]
      rw [← ih]
      rfl

theorem map_range_eq_replicate {β : Type} (n : ℕ) (f : ℕ → β) (b : β) (h : ∀ i < n, f i = b) :
    (List.range n).map f = List.replicate n b := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, ?_⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i (List.mem_range.mp hi)

namespace Instance

variable (I : Instance)

/-! ### Transition templates -/

/-- The relation of a phantom cell: its next value is zero. -/
def phantomRel (vs : List ℕ) : Bool := vs.getLast? == some 0

noncomputable def phantomDesc : FormulaDesc := registerDesc I.width [I.nextSelfRef] phantomRel

/-- The update of a real cell at real index `i` from the dependency values. -/
noncomputable def realUpdateAt (k : I.tm.K) (i : ℕ) (vs : List ℕ) : ℕ :=
  I.realUpdate k (I.D + i) vs

noncomputable def realRel (k : I.tm.K) (i : ℕ) (vs : List ℕ) : Bool :=
  vs.getLast? == some (I.realUpdateAt k i vs.dropLast)

noncomputable def cellRealDesc (k : I.tm.K) (i : ℕ) : FormulaDesc :=
  registerDesc I.width (I.headRefs ++ I.windowRefs ++ [I.nextSelfRef]) (I.realRel k i)

theorem transitionRelation_cellGroup_real (k : I.tm.K) (j : ℕ) (hj : j < I.P) (hreal : I.IsReal j) :
    I.toParams.localSystem.transitionRelation (I.cellGroup k j) = I.realRel k (j - I.D) := by
  funext vs
  simp only [LocalSystem.transitionRelation, Params.localSystem, Params.update_cellGroup' _ k j hj,
    if_pos hreal, realRel, realUpdateAt, Nat.add_sub_cancel' hreal.1]

theorem transitionRelation_cellGroup_phantom (k : I.tm.K) (j : ℕ) (hj : j < I.P)
    (hreal : ¬ I.IsReal j) :
    I.toParams.localSystem.transitionRelation (I.cellGroup k j) = phantomRel := by
  funext vs
  simp only [LocalSystem.transitionRelation, Params.localSystem, Params.update_cellGroup' _ k j hj,
    if_neg hreal, phantomRel]

theorem cellTrans_eq (k : I.tm.K) (j : ℕ) (hj : j < I.P) :
    I.cellTrans k j = if I.IsReal j then I.cellRealDesc k (j - I.D) else I.phantomDesc := by
  by_cases hreal : I.IsReal j
  · rw [cellTrans, if_pos hreal, if_pos hreal, cellRealDesc,
      I.transitionRelation_cellGroup_real k j hj hreal]
  · rw [cellTrans, if_neg hreal, if_neg hreal, phantomDesc,
      I.transitionRelation_cellGroup_phantom k j hj hreal]

/-- The decoded tops have at most `D` symbols. -/
theorem decodeHead_tops_length_le (vs : List ℕ) (k : I.tm.K) :
    ((I.decodeHead vs).tops k).length ≤ I.D := by
  simp only [Params.decodeHead]
  exact (takeSome_length_le _).trans (by simp)

/-- The new top region of any head has at most `2D` symbols. -/
theorem headStep_stk_length_le (h : Params.Head I.tm) (hh : ∀ k, (h.tops k).length ≤ I.D)
    (k : I.tm.K) : ((I.headStep h).stk k).length ≤ 2 * I.D := by
  cases hl : h.label with
  | none =>
      rw [Params.headStep_none _ h hl]
      exact (hh k).trans (by omega)
  | some l =>
      rw [Params.headStep_some _ h l hl]
      have h1 := MachineRuntime.stepAux_stack_length_le (I.tm.m l) h.state h.tops k
      have h2 := (stmtPushBound_le_depth (I.tm.m l)).trans (depth_le_machineDepth I.tm l)
      have h3 := hh k
      simp only [Params.D] at *
      omega

theorem realUpdateAt_of_ge (k : I.tm.K) (i : ℕ) (hi : 2 * I.D ≤ i) (vs : List ℕ) :
    I.realUpdateAt k i vs = I.realUpdateAt k (2 * I.D) vs := by
  simp only [realUpdateAt, Params.realUpdate, Nat.add_sub_cancel_left]
  cases hl : (I.decodeHead vs).label with
  | none => rfl
  | some l =>
      simp only [Params.cellUpdate]
      have hlen := I.headStep_stk_length_le (I.decodeHead vs) (I.decodeHead_tops_length_le vs) k
      rw [if_neg (by omega), if_neg (by omega)]

theorem cellRealDesc_of_ge (k : I.tm.K) (i : ℕ) (hi : 2 * I.D ≤ i) :
    I.cellRealDesc k i = I.cellRealDesc k (2 * I.D) := by
  simp only [cellRealDesc]
  congr 1
  funext vs
  simp only [realRel, I.realUpdateAt_of_ge k i hi]

/-- A stack's transition cell descriptors: bottom phantoms, the special real
cells, the generic real cells, and the top phantoms. -/
theorem range_P_map_cellTrans (k : I.tm.K) :
    (List.range I.P).map (I.cellTrans k) =
      List.replicate I.D I.phantomDesc ++ (List.range (2 * I.D)).map (I.cellRealDesc k) ++
        List.replicate I.G (I.cellRealDesc k (2 * I.D)) ++ List.replicate I.D I.phantomDesc := by
  have hP : I.P = I.D + 2 * I.D + I.G + I.D := by rw [I.P_eq]; omega
  rw [hP, range_add', range_add', range_add', List.map_append, List.map_append, List.map_append,
    List.map_map, List.map_map, List.map_map]
  have hPsplit : I.D + 2 * I.D + I.G + I.D = I.P := hP.symm
  congr 1
  congr 1
  congr 1
  · apply map_range_eq_replicate
    intro j hj
    rw [I.cellTrans_eq k j (by omega), if_neg]
    simp only [Params.IsReal]; omega
  · apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_def]
    rw [I.cellTrans_eq k (i + I.D) (by omega), if_pos (by simp only [Params.IsReal]; omega),
      Nat.add_sub_cancel]
  · apply map_range_eq_replicate
    intro i hi
    simp only [Function.comp_def]
    rw [I.cellTrans_eq k (i + (I.D + 2 * I.D)) (by omega),
      if_pos (by simp only [Params.IsReal]; omega), I.cellRealDesc_of_ge k _ (by omega)]
  · apply map_range_eq_replicate
    intro i hi
    simp only [Function.comp_def]
    rw [I.cellTrans_eq k (i + (I.D + 2 * I.D + I.G)) (by omega), if_neg]
    simp only [Params.IsReal]; omega

/-! ### Initial-row templates -/

noncomputable def zeroDesc : FormulaDesc := fixDesc I.width I.selfRef 0

noncomputable def symDesc (s : I.tm.Γ I.tm.k₀) : FormulaDesc :=
  fixDesc I.width I.selfRef (optionCode (symbols I.tm I.extra I.tm.k₀) (some s))

noncomputable def chainDesc : FormulaDesc :=
  registerDesc I.width [I.selfRef, I.winRef (I.D + 1)] I.certRel

/-- Cells of stacks other than the input stack are never certificate cells. -/
theorem certIndex?_of_ne (k : I.tm.K) (hk : k ≠ I.tm.k₀) (j : ℕ) (hj : j < I.P) :
    I.certIndex? (I.cellGroup k j) = none := by
  rw [certIndex?_eq_none_iff, mem_certGroups]
  rintro ⟨i, hi, heq⟩
  have h1 := I.cellOf_cellGroup k j hj
  have h2 := I.cellOf_cellGroup I.tm.k₀ (I.D + I.inputLength + i)
    (I.certCell_lt_P i hi.le)
  simp only [certGroup] at heq
  rw [heq, h2] at h1
  exact hk (Prod.mk.inj (Option.some.inj h1)).1.symm

/-- Input-stack cells outside the certificate range are not certificate cells. -/
theorem certIndex?_input_of_lt (j : ℕ) (hj : j < I.D + I.inputLength) :
    I.certIndex? (I.cellGroup I.tm.k₀ j) = none := by
  rw [certIndex?_eq_none_iff, mem_certGroups]
  rintro ⟨i, _, heq⟩
  simp only [certGroup, Params.cellGroup] at heq
  omega

theorem certIndex?_input_of_ge (j : ℕ) (hj : I.D + I.inputLength + I.certBound ≤ j) :
    I.certIndex? (I.cellGroup I.tm.k₀ j) = none := by
  rw [certIndex?_eq_none_iff, mem_certGroups]
  rintro ⟨i, hi, heq⟩
  simp only [certGroup, Params.cellGroup] at heq
  omega

theorem initCellDesc_of_ne (k : I.tm.K) (hk : k ≠ I.tm.k₀) (j : ℕ) (hj : j < I.P) :
    I.initCellDesc k j = I.zeroDesc := by
  simp only [initCellDesc, I.certIndex?_of_ne k hk j hj, zeroDesc]
  congr 2
  rw [I.value_cellGroup _ k j hj]
  by_cases hDj : I.D ≤ j
  · rw [Params.cellValue_of_le _ _ _ _ hDj, initCfg_stk_of_ne _ _ k hk]
    simp
  · exact Params.cellValue_of_lt _ _ k j (Nat.not_le.mp hDj)

theorem range_P_map_initCellDesc_of_ne (k : I.tm.K) (hk : k ≠ I.tm.k₀) :
    (List.range I.P).map (I.initCellDesc k) = List.replicate I.P I.zeroDesc :=
  map_range_eq_replicate _ _ _ fun j hj => I.initCellDesc_of_ne k hk j hj

/-- The input stack's initial cell descriptors: bottom phantoms, one symbol
fix per input symbol, the certificate chains, and zeros. -/
theorem range_P_map_initCellDesc :
    (List.range I.P).map (I.initCellDesc I.tm.k₀) =
      List.replicate I.D I.zeroDesc ++ I.input.map I.symDesc ++
        List.replicate I.certBound I.chainDesc ++
        List.replicate (I.horizon * I.pb + 2 + 3 * I.D) I.zeroDesc := by
  have hP : I.P = I.D + I.inputLength + I.certBound + (I.horizon * I.pb + 2 + 3 * I.D) := by
    rw [I.P_eq, Params.G]; omega
  rw [hP, range_add', range_add', range_add', List.map_append, List.map_append, List.map_append,
    List.map_map, List.map_map, List.map_map]
  congr 1
  congr 1
  congr 1
  · apply map_range_eq_replicate
    intro j hj
    simp only [initCellDesc, I.certIndex?_input_of_lt j (by omega), zeroDesc]
    congr 2
    rw [I.value_cellGroup _ _ j (by omega), Params.cellValue_of_lt _ _ _ j hj]
  · rw [← I.input_length, ← map_range_getElem? I.input I.symDesc []]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_def]
    rw [initCellDesc]
    have hlen := I.input_length
    simp only [I.certIndex?_input_of_lt (i + I.D) (by omega)]
    rw [I.value_cellGroup _ _ (i + I.D) (by omega),
      Params.cellValue_of_le _ _ _ _ (by omega), Nat.add_sub_cancel, initCfg_stk_self,
      List.map_nil, List.append_nil, List.getElem?_eq_getElem hi']
    simp [symDesc]
  · apply map_range_eq_replicate
    intro i hi
    simp only [Function.comp_def]
    rw [initCellDesc]
    have hc := I.certIndex?_certGroup i hi
    simp only [certGroup] at hc
    rw [show i + (I.D + I.inputLength) = I.D + I.inputLength + i by omega, hc]
    rfl
  · apply map_range_eq_replicate
    intro i hi
    simp only [Function.comp_def]
    rw [initCellDesc]
    simp only [I.certIndex?_input_of_ge (i + (I.D + I.inputLength + I.certBound)) (by omega),
      zeroDesc]
    congr 2
    rw [I.value_cellGroup _ _ _ (by omega), Params.cellValue_of_le _ _ _ _ (by omega),
      initCfg_stk_self, List.map_nil, List.append_nil, List.getElem?_eq_none (by
        rw [I.input_length]; omega)]
    rfl

/-! ### Final-row templates -/

noncomputable def outDesc : FormulaDesc :=
  fixDesc I.width I.selfRef (optionCode (symbols I.tm I.extra I.tm.k₁) I.output[0]?)

theorem finalCellDesc_of_ne (k : I.tm.K) (hk : k ≠ I.tm.k₁) (j : ℕ) (hj : j < I.P) :
    I.finalCellDesc k j = I.zeroDesc := by
  simp only [finalCellDesc, zeroDesc]
  congr 2
  rw [I.value_cellGroup _ k j hj]
  by_cases hDj : I.D ≤ j
  · rw [Params.cellValue_of_le _ _ _ _ hDj, finalCfg, haltList_stk_of_ne _ _ k hk]
    simp
  · exact Params.cellValue_of_lt _ _ k j (Nat.not_le.mp hDj)

theorem range_P_map_finalCellDesc_of_ne (k : I.tm.K) (hk : k ≠ I.tm.k₁) :
    (List.range I.P).map (I.finalCellDesc k) = List.replicate I.P I.zeroDesc :=
  map_range_eq_replicate _ _ _ fun j hj => I.finalCellDesc_of_ne k hk j hj

/-- The output stack's final cell descriptors: bottom phantoms, the output
fix, and zeros. -/
theorem range_P_map_finalCellDesc :
    (List.range I.P).map (I.finalCellDesc I.tm.k₁) =
      List.replicate I.D I.zeroDesc ++ [I.outDesc] ++
        List.replicate (I.G + 3 * I.D - 1) I.zeroDesc := by
  have hG := I.G_ge_two
  have hP : I.P = I.D + 1 + (I.G + 3 * I.D - 1) := by rw [I.P_eq]; omega
  rw [hP, range_add', range_add', List.map_append, List.map_append, List.map_map, List.map_map]
  congr 1
  congr 1
  · apply map_range_eq_replicate
    intro j hj
    simp only [finalCellDesc, zeroDesc]
    congr 2
    rw [I.value_cellGroup _ _ j (by omega), Params.cellValue_of_lt _ _ _ j hj]
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      Function.comp_def, Nat.zero_add, finalCellDesc, outDesc]
    congr 2
    rw [I.value_cellGroup _ _ _ (by omega), Params.cellValue_of_le _ _ _ _ le_rfl,
      Nat.sub_self, finalCfg, haltList_stk_self]
  · apply map_range_eq_replicate
    intro i hi
    simp only [Function.comp_def, finalCellDesc, zeroDesc]
    congr 2
    rw [I.value_cellGroup _ _ _ (by omega), Params.cellValue_of_le _ _ _ _ (by omega), finalCfg,
      haltList_stk_self, List.getElem?_eq_none (by have := I.output_short; omega)]
    rfl

end Instance

end LeanNPHardness.MachineTableau
