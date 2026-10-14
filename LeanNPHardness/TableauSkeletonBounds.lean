import LeanNPHardness.TableauTemplateInstance

/-!
# Size bounds for the skeleton

Every descriptor that the skeleton of an instance uses is one of finitely
many descriptors of its template; `chunkBound` is the largest job length
among them, so the skeleton has at most `roundBound` instructions per
round and `(horizon + 2) * roundBound` instructions in total.
-/

namespace LeanNPHardness.MachineTableau.Instance

open CNF.Unary TableauJobs MachineLocality

/-- An element is at most the maximum of a list. -/
theorem le_foldr_max {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.foldr max 0
  | b :: l, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (le_foldr_max h).trans (Nat.le_max_right _ _)

theorem sum_map_le_length_mul {α : Type} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ a ∈ l, f a ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      have := h a (List.mem_cons_self ..)
      omega

variable (I : Instance)

/-- The descriptors a skeleton can use, up to the template. -/
noncomputable def descList : List FormulaDesc :=
  letI := I.tm.Γk₀Fin
  [I.labelTrans, I.varTrans, I.phantomDesc, I.zeroDesc, I.chainDesc, I.outDesc] ++
    (List.range (I.D + 2)).map I.dummyTrans ++ (List.range (I.D + 2)).map I.initDesc ++
    (List.range (I.D + 2)).map I.finalDesc ++
    ((stackList I.tm).flatMap fun k => (List.range (2 * I.D + 1)).map (I.cellRealDesc k)) ++
    (Finset.univ : Finset (I.tm.Γ I.tm.k₀)).toList.map I.symDesc

/-- The largest job length among the usable descriptors. -/
noncomputable def chunkBound : ℕ := (I.descList.map fun d => (formulaJob d).length).foldr max 0

theorem formulaJob_length_le_chunkBound (d : FormulaDesc) (hd : d ∈ I.descList) :
    (formulaJob d).length ≤ I.chunkBound :=
  le_foldr_max (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-! ### Membership of the instance's descriptors in the template's list -/

theorem labelTrans_mem : I.labelTrans ∈ I.template.descList := by
  rw [← template_labelTrans]; simp [descList]

theorem varTrans_mem : I.varTrans ∈ I.template.descList := by
  rw [← template_varTrans]; simp [descList]

theorem phantomDesc_mem : I.phantomDesc ∈ I.template.descList := by
  rw [← template_phantomDesc]; simp [descList]

theorem zeroDesc_mem : I.zeroDesc ∈ I.template.descList := by
  rw [← template_zeroDesc]; simp [descList]

theorem chainDesc_mem : I.chainDesc ∈ I.template.descList := by
  rw [← template_chainDesc]; simp [descList]

theorem outDesc_mem : I.outDesc ∈ I.template.descList := by
  rw [← template_outDesc]; simp [descList]

theorem dummyTrans_mem (g : ℕ) (hg : g < I.D + 2) : I.dummyTrans g ∈ I.template.descList := by
  rw [← template_dummyTrans I g hg]
  simp only [descList, List.mem_append, List.mem_map, List.mem_range, template_D]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))))

theorem initDesc_mem (g : ℕ) (hg : g < I.D + 2) : I.initDesc g ∈ I.template.descList := by
  rw [← template_initDesc I g hg]
  simp only [descList, List.mem_append, List.mem_map, List.mem_range, template_D]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩)))

theorem finalDesc_mem (g : ℕ) (hg : g < I.D + 2) : I.finalDesc g ∈ I.template.descList := by
  rw [← template_finalDesc I g hg]
  simp only [descList, List.mem_append, List.mem_map, List.mem_range, template_D]
  exact Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))

theorem cellRealDesc_mem (k : I.tm.K) (i : ℕ) (hi : i ≤ 2 * I.D) :
    I.cellRealDesc k i ∈ I.template.descList := by
  rw [← template_cellRealDesc]
  simp only [descList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, template_D]
  exact Or.inl (Or.inr ⟨k, mem_stackList _ k, i, by omega, rfl⟩)

theorem symDesc_mem (s : I.tm.Γ I.tm.k₀) : I.symDesc s ∈ I.template.descList := by
  letI := I.tm.Γk₀Fin
  rw [← template_symDesc]
  simp only [descList, List.mem_append, List.mem_map]
  exact Or.inr ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), rfl⟩

/-! ### Job lengths -/

theorem cellsJob_length_le (ds : List FormulaDesc) (c : ℕ)
    (h : ∀ d ∈ ds, (formulaJob d).length ≤ c) :
    (TableauJobs.cellsJob ds).length ≤ ds.length * (c + 1) := by
  induction ds with
  | nil => simp [TableauJobs.cellsJob]
  | cons d ds ih =>
      rw [TableauJobs.cellsJob, List.flatMap_cons, ← TableauJobs.cellsJob, List.length_append,
        List.length_append, List.length_cons, Nat.succ_mul]
      have h1 := ih fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
      have h2 := h d (List.mem_cons_self ..)
      simp only [TableauJobs.cellStep, List.length_singleton]
      omega

theorem headJob_length_le (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) (c : ℕ)
    (h0 : (formulaJob d0).length ≤ c) (h1 : (formulaJob d1).length ≤ c)
    (hdd : ∀ i < I.D, (formulaJob (dd (i + 2))).length ≤ c) :
    (I.headJob d0 d1 dd).length ≤ (2 + I.D) * c := by
  simp only [Instance.headJob, List.length_append, List.length_flatMap]
  have := sum_map_le_length_mul (List.range I.D) (fun i => (formulaJob (dd (i + 2))).length) c
    fun i hi => hdd i (List.mem_range.mp hi)
  simp only [List.length_range] at this
  rw [Nat.add_mul]
  omega

/-- Instructions per round. -/
noncomputable def roundBound : ℕ :=
  6 + I.D + (2 + I.D) * I.template.chunkBound +
    I.stackCount * I.P * (I.template.chunkBound + 1)

theorem openRound_length_le' (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc)
    (h0 : (formulaJob d0).length ≤ I.template.chunkBound)
    (h1 : (formulaJob d1).length ≤ I.template.chunkBound)
    (hdd : ∀ i < I.D, (formulaJob (dd (i + 2))).length ≤ I.template.chunkBound)
    (hf : ∀ d ∈ I.cellDescs f, (formulaJob d).length ≤ I.template.chunkBound) :
    (I.openRound d0 d1 dd f).length ≤
      4 + (2 + I.D) * I.template.chunkBound + I.stackCount * I.P * (I.template.chunkBound + 1) := by
  simp only [Instance.openRound, List.length_append]
  have hh := I.headJob_length_le d0 d1 dd _ h0 h1 hdd
  have hc := cellsJob_length_le _ _ hf
  rw [cellDescs_length] at hc
  simp only [TableauJobs.roundStart, List.length_cons, List.length_nil]
  omega

theorem openRound_length_le (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc)
    (h0 : (formulaJob d0).length ≤ I.template.chunkBound)
    (h1 : (formulaJob d1).length ≤ I.template.chunkBound)
    (hdd : ∀ i < I.D, (formulaJob (dd (i + 2))).length ≤ I.template.chunkBound)
    (hf : ∀ d ∈ I.cellDescs f, (formulaJob d).length ≤ I.template.chunkBound) :
    (I.openRound d0 d1 dd f).length ≤ I.roundBound := by
  have := I.openRound_length_le' d0 d1 dd f h0 h1 hdd hf
  unfold roundBound
  omega

theorem roundJob_length_le (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc)
    (h0 : (formulaJob d0).length ≤ I.template.chunkBound)
    (h1 : (formulaJob d1).length ≤ I.template.chunkBound)
    (hdd : ∀ i < I.D, (formulaJob (dd (i + 2))).length ≤ I.template.chunkBound)
    (hf : ∀ d ∈ I.cellDescs f, (formulaJob d).length ≤ I.template.chunkBound) :
    (I.roundJob d0 d1 dd f).length ≤ I.roundBound := by
  have := I.openRound_length_le' d0 d1 dd f h0 h1 hdd hf
  simp only [Instance.roundJob, List.length_append, TableauJobs.roundEnd, List.length_cons,
    List.length_nil, List.length_replicate]
  unfold roundBound
  omega

/-! ### Descriptors of the three kinds of rounds -/

theorem mem_cellDescs {f : I.tm.K → ℕ → FormulaDesc} {d : FormulaDesc} (hd : d ∈ I.cellDescs f) :
    ∃ k, d ∈ (List.range I.P).map (f k) := by
  simp only [Instance.cellDescs, List.mem_flatMap] at hd
  obtain ⟨k, _, hk⟩ := hd
  exact ⟨k, hk⟩

theorem cellTrans_length_le : ∀ d ∈ I.cellDescs I.cellTrans,
    (formulaJob d).length ≤ I.template.chunkBound := by
  intro d hd
  obtain ⟨k, hk⟩ := I.mem_cellDescs hd
  rw [I.range_P_map_cellTrans k] at hk
  simp only [List.mem_append, List.mem_replicate, List.mem_map, List.mem_range] at hk
  apply I.template.formulaJob_length_le_chunkBound
  rcases hk with ((⟨_, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩
  · exact I.phantomDesc_mem
  · exact I.cellRealDesc_mem k i (by omega)
  · exact I.cellRealDesc_mem k _ le_rfl
  · exact I.phantomDesc_mem

theorem initCellDesc_length_le : ∀ d ∈ I.cellDescs I.initCellDesc,
    (formulaJob d).length ≤ I.template.chunkBound := by
  intro d hd
  obtain ⟨k, hk⟩ := I.mem_cellDescs hd
  apply I.template.formulaJob_length_le_chunkBound
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  by_cases hk0 : k = I.tm.k₀
  · subst hk0
    rw [I.range_P_map_initCellDesc] at hk
    simp only [List.mem_append, List.mem_replicate, List.mem_map] at hk
    rcases hk with ((⟨_, rfl⟩ | ⟨s, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact I.zeroDesc_mem
    · exact I.symDesc_mem s
    · exact I.chainDesc_mem
    · exact I.zeroDesc_mem
  · rw [I.range_P_map_initCellDesc_of_ne k hk0] at hk
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hk
    exact I.zeroDesc_mem

theorem finalCellDesc_length_le : ∀ d ∈ I.cellDescs I.finalCellDesc,
    (formulaJob d).length ≤ I.template.chunkBound := by
  intro d hd
  obtain ⟨k, hk⟩ := I.mem_cellDescs hd
  apply I.template.formulaJob_length_le_chunkBound
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  by_cases hk1 : k = I.tm.k₁
  · subst hk1
    rw [I.range_P_map_finalCellDesc] at hk
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hk
    rcases hk with (⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩
    · exact I.zeroDesc_mem
    · exact I.outDesc_mem
    · exact I.zeroDesc_mem
  · rw [I.range_P_map_finalCellDesc_of_ne k hk1] at hk
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hk
    exact I.zeroDesc_mem

theorem initRound_length_le :
    (I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc).length ≤ I.roundBound :=
  I.openRound_length_le _ _ _ _
    (I.template.formulaJob_length_le_chunkBound _ (I.initDesc_mem 0 (by omega)))
    (I.template.formulaJob_length_le_chunkBound _ (I.initDesc_mem 1 (by omega)))
    (fun i hi => I.template.formulaJob_length_le_chunkBound _ (I.initDesc_mem (i + 2) (by omega)))
    I.initCellDesc_length_le

theorem transRound_length_le :
    (I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans).length ≤ I.roundBound :=
  I.roundJob_length_le _ _ _ _
    (I.template.formulaJob_length_le_chunkBound _ I.labelTrans_mem)
    (I.template.formulaJob_length_le_chunkBound _ I.varTrans_mem)
    (fun i hi => I.template.formulaJob_length_le_chunkBound _ (I.dummyTrans_mem (i + 2) (by omega)))
    I.cellTrans_length_le

theorem finalRound_length_le :
    (I.openRound (I.finalDesc 0) (I.finalDesc 1) I.finalDesc I.finalCellDesc).length ≤
      I.roundBound :=
  I.openRound_length_le _ _ _ _
    (I.template.formulaJob_length_le_chunkBound _ (I.finalDesc_mem 0 (by omega)))
    (I.template.formulaJob_length_le_chunkBound _ (I.finalDesc_mem 1 (by omega)))
    (fun i hi => I.template.formulaJob_length_le_chunkBound _ (I.finalDesc_mem (i + 2) (by omega)))
    I.finalCellDesc_length_le

/-- The skeleton has at most `roundBound` instructions per round. -/
theorem skeleton_length_le : I.skeleton.length ≤ (I.horizon + 2) * I.roundBound := by
  simp only [Instance.skeleton, List.length_append, List.length_flatMap, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]
  have h1 := I.initRound_length_le
  have h2 := I.transRound_length_le
  have h3 := I.finalRound_length_le
  have h4 : I.horizon * (I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans).length ≤
      I.horizon * I.roundBound := Nat.mul_le_mul_left _ h2
  rw [show (I.horizon + 2) * I.roundBound = I.horizon * I.roundBound + I.roundBound + I.roundBound
    by ring]
  omega

end LeanNPHardness.MachineTableau.Instance
