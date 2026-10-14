import LeanNPHardness.TableauEmitter

/-!
# The input-independent template of a tableau instance

The emitter only uses descriptors that depend on the machine, its extra
output symbols, the certificate symbols and the output; the input, its
length, the certificate bound and the horizon never enter them. `template`
forgets exactly that input-size data, and `emitter_template` shows that the
emitter of an instance coincides with the emitter of its template. This is
what makes the generator a single machine for all inputs.

Every equation below is proved by rewriting the few input-size-sensitive
subterms; the descriptor constructors `registerDesc` and `fixDesc` are never
unfolded, because unfolding them makes definitional checks diverge.
-/

namespace LeanNPHardness.MachineTableau.Instance

open Routines CNF.Unary TableauJobs TableauStacks MachineLocality Tableau

variable (I : Instance)

/-- The instance with the same machine data and empty input. -/
noncomputable def template : Instance where
  tm := I.tm
  extra := I.extra
  inputLength := 0
  certBound := 0
  horizon := 0
  input := []
  input_length := rfl
  certSym := I.certSym
  certSym_injective := I.certSym_injective
  output := I.output
  output_mem := I.output_mem
  output_short := I.output_short

theorem template_tm : I.template.tm = I.tm := rfl
theorem template_extra : I.template.extra = I.extra := rfl
theorem template_D : I.template.D = I.D := rfl
theorem template_pb : I.template.pb = I.pb := rfl
theorem template_width : I.template.width = I.width := rfl
theorem template_stackCount : I.template.stackCount = I.stackCount := rfl
theorem template_kIndex (k : I.tm.K) : I.template.kIndex k = I.kIndex k := rfl
theorem template_output : I.template.output = I.output := rfl

/-! ### Group references -/

theorem template_varRef : I.template.varRef = I.varRef := rfl
theorem template_dummyRef (g : ℕ) : I.template.dummyRef g = I.dummyRef g := rfl
theorem template_topRef (k : I.tm.K) (i : ℕ) : I.template.topRef k i = I.topRef k i := rfl
theorem template_headRefs : I.template.headRefs = I.headRefs := rfl
theorem template_winRef (m : ℕ) : I.template.winRef m = I.winRef m := rfl
theorem template_windowRefs : I.template.windowRefs = I.windowRefs := rfl
theorem template_selfRef : I.template.selfRef = I.selfRef := rfl
theorem template_nextSelfRef : I.template.nextSelfRef = I.nextSelfRef := rfl
theorem template_nextRef (g : ℕ) : I.template.nextRef g = I.nextRef g := rfl
theorem template_headRef (g : ℕ) : I.template.headRef g = I.headRef g := rfl

/-! ### Values, updates and relations -/

theorem template_decodeHead (vs : List ℕ) : I.template.decodeHead vs = I.decodeHead vs := rfl
theorem template_headStep (h : Params.Head I.tm) : I.template.headStep h = I.headStep h := by
  rcases h with ⟨_ | l, st, tops⟩ <;> rfl
theorem template_cellUpdate (k : I.tm.K) (newTop : List (I.tm.Γ k)) (window : List ℕ) (i : ℕ) :
    I.template.cellUpdate k newTop window i = I.cellUpdate k newTop window i := rfl

theorem template_realUpdate (k : I.tm.K) (j : ℕ) (vs : List ℕ) :
    I.template.realUpdate k j vs = I.realUpdate k j vs := by
  unfold Params.realUpdate
  simp only [Params.headGroups_length, template_stackCount, template_D, template_decodeHead,
    template_headStep, template_cellUpdate]
  generalize (I.decodeHead vs).label = lab
  cases lab <;> rfl

theorem template_realRel (k : I.tm.K) (i : ℕ) : I.template.realRel k i = I.realRel k i := by
  funext vs
  simp only [realRel, realUpdateAt, template_realUpdate, template_D]

theorem template_certRel : I.template.certRel = I.certRel := rfl

/-- Head-register values of two configurations agreeing on label and state
coincide, and do not depend on the input-size data. -/
theorem template_value_head (c c' : I.tm.Cfg) (hl : c.l = c'.l) (hv : c.var = c'.var)
    (g : ℕ) (hg : g < I.D + 2) : I.template.value c g = I.value c' g := by
  rcases g with _ | _ | g
  · rw [Params.value_zero, Params.value_zero, hl]
    rfl
  · rw [Params.value_one, Params.value_one, hv]
    rfl
  · rw [Params.value_dummy I.template.toParams c (g + 1 + 1) (by omega) hg,
      Params.value_dummy I.toParams c' (g + 1 + 1) (by omega) hg]

theorem template_transitionRelation_head (g : ℕ) (hg : g < I.D + 2) :
    I.template.toParams.localSystem.transitionRelation g =
      I.toParams.localSystem.transitionRelation g := by
  funext vs
  simp only [LocalSystem.transitionRelation, Params.localSystem]
  rcases g with _ | _ | g
  · rw [Params.update_zero, Params.update_zero]
    simp only [template_decodeHead, template_headStep, template_tm]
  · rw [Params.update_one, Params.update_one]
    simp only [template_decodeHead, template_headStep, template_tm]
  · rw [Params.update_dummy I.template.toParams (g + 1 + 1) (by omega) hg,
      Params.update_dummy I.toParams (g + 1 + 1) (by omega) hg]

/-! ### Descriptors -/

theorem template_labelTrans : I.template.labelTrans = I.labelTrans := by
  unfold labelTrans
  rw [template_transitionRelation_head I 0 (by omega), template_width, template_headRefs,
    template_nextRef]

theorem template_varTrans : I.template.varTrans = I.varTrans := by
  unfold varTrans
  rw [template_transitionRelation_head I 1 (by omega), template_width, template_headRefs,
    template_nextRef]

theorem template_dummyTrans (g : ℕ) (hg : g < I.D + 2) :
    I.template.dummyTrans g = I.dummyTrans g := by
  unfold dummyTrans
  rw [template_transitionRelation_head I g hg, template_width, template_nextRef]

theorem template_initDesc (g : ℕ) (hg : g < I.D + 2) : I.template.initDesc g = I.initDesc g := by
  unfold initDesc
  rw [template_value_head I (I.template.initCfg []) (I.initCfg []) rfl rfl g hg, template_width,
    template_headRef]

theorem template_finalDesc (g : ℕ) (hg : g < I.D + 2) :
    I.template.finalDesc g = I.finalDesc g := by
  unfold finalDesc
  rw [template_value_head I I.template.finalCfg I.finalCfg rfl rfl g hg, template_width,
    template_headRef]

theorem template_cellRealDesc (k : I.tm.K) (i : ℕ) :
    I.template.cellRealDesc k i = I.cellRealDesc k i := by
  unfold cellRealDesc
  rw [template_realRel, template_width, template_headRefs, template_windowRefs,
    template_nextSelfRef]

theorem template_phantomDesc : I.template.phantomDesc = I.phantomDesc := by
  unfold phantomDesc
  rw [template_width, template_nextSelfRef]

theorem template_zeroDesc : I.template.zeroDesc = I.zeroDesc := by
  unfold zeroDesc
  rw [template_width, template_selfRef]

theorem template_chainDesc : I.template.chainDesc = I.chainDesc := by
  unfold chainDesc
  rw [template_width, template_selfRef, template_winRef, template_D, template_certRel]

theorem template_symbols (k : I.tm.K) :
    symbols I.template.tm I.template.extra k = symbols I.tm I.extra k := rfl

theorem template_outDesc : I.template.outDesc = I.outDesc := by
  unfold outDesc
  rw [template_width, template_selfRef]
  exact congrArg (fixDesc I.width I.selfRef) (congrArg₂ optionCode (template_symbols I I.tm.k₁) rfl)

theorem template_symDesc (s : I.tm.Γ I.tm.k₀) : I.template.symDesc s = I.symDesc s := by
  unfold symDesc
  rw [template_width, template_selfRef]
  exact congrArg (fixDesc I.width I.selfRef) (congrArg₂ optionCode (template_symbols I I.tm.k₀) rfl)

/-! ### Emitter components -/

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx] (conv : Γx → I.tm.Γ I.tm.k₀)

theorem template_headChunks (d0 d1 d0' d1' : FormulaDesc) (dd dd' : ℕ → FormulaDesc)
    (h0 : d0 = d0') (h1 : d1 = d1') (hdd : ∀ g < I.D + 2, dd g = dd' g) :
    I.template.headChunks d0 d1 dd = I.headChunks d0' d1' dd' := by
  unfold headChunks
  rw [h0, h1, template_D]
  congr 1
  exact List.map_congr_left fun i hi => by
    rw [hdd (i + 2) (by simp only [List.mem_range] at hi; omega)]

omit [Fintype Γx] [DecidableEq Γx] in
theorem template_transStack (k : I.tm.K) :
    I.template.transStack (Γx := Γx) k = I.transStack k := by
  unfold transStack
  simp only [template_D, template_phantomDesc, template_cellRealDesc]

omit [Fintype Γx] [DecidableEq Γx] in
theorem template_finalStack (k : I.tm.K) :
    I.template.finalStack (Γx := Γx) k = I.finalStack k := by
  unfold finalStack
  simp only [template_D, template_zeroDesc, template_outDesc, template_tm]

theorem template_initStackInput : I.template.initStackInput conv = I.initStackInput conv := by
  unfold initStackInput
  simp only [template_D, template_zeroDesc, template_symDesc, template_chainDesc]

theorem template_initStack (k : I.tm.K) :
    I.template.initStack conv k = I.initStack conv k := by
  unfold initStack
  simp only [template_D, template_zeroDesc, template_initStackInput, template_tm]

omit [Fintype Γx] [DecidableEq Γx] in
theorem template_foldStacks (f : I.template.tm.K → GRoutine Γx) (g : I.tm.K → GRoutine Γx)
    (h : ∀ k, f k = g k) :
    foldStacks (stackList I.template.tm) f = foldStacks (stackList I.tm) g := by
  have hfg : f = g := funext h
  rw [hfg]
  rfl

omit [Fintype Γx] [DecidableEq Γx] in
theorem template_transRound : I.template.transRound (Γx := Γx) = I.transRound := by
  unfold transRound
  rw [template_headChunks I _ _ _ _ _ _ (template_labelTrans I) (template_varTrans I)
    (template_dummyTrans I), template_D]
  rw [template_foldStacks I _ _ (template_transStack I)]

omit [Fintype Γx] [DecidableEq Γx] in
theorem template_transRounds : I.template.transRounds (Γx := Γx) = I.transRounds := by
  unfold transRounds
  rw [template_transRound]

omit [Fintype Γx] [DecidableEq Γx] in
theorem template_finalRound : I.template.finalRound (Γx := Γx) = I.finalRound := by
  unfold finalRound
  rw [template_headChunks I _ _ _ _ _ _ (template_finalDesc I 0 (by omega))
    (template_finalDesc I 1 (by omega)) (template_finalDesc I)]
  rw [template_foldStacks I _ _ (template_finalStack I)]

theorem template_initRound : I.template.initRound conv = I.initRound conv := by
  unfold initRound
  rw [template_headChunks I _ _ _ _ _ _ (template_initDesc I 0 (by omega))
    (template_initDesc I 1 (by omega)) (template_initDesc I)]
  rw [template_foldStacks I _ _ (template_initStack I conv)]

/-- The emitter of an instance is the emitter of its template. -/
theorem emitter_template : I.template.emitter conv = I.emitter conv := by
  unfold emitter
  rw [template_initRound, template_transRounds, template_finalRound]

end LeanNPHardness.MachineTableau.Instance
