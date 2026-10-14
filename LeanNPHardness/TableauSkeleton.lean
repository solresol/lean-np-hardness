import LeanNPHardness.TableauSkeletonRender
import LeanNPHardness.MachineTableauBoundary
import Mathlib.Tactic.Ring

/-!
# The skeleton: a job rendering the Cook--Levin tableau

Every block of the tableau is a register constraint whose registers are
described by group references: constants from the base register for the
head, and offsets from the window register for the current cell and its
window. A round resets the window register, renders the head and dummy
blocks, renders one block per cell while advancing the window register, and
(for transition rounds) moves the base register to the next round.
`render_skeleton` proves that rendering the skeleton from the initial
registers yields exactly the unary encoding of `Instance.tableau`.
-/

namespace LeanNPHardness.MachineTableau

open CNF CNF.Unary CNF.Constraint TableauJobs Tableau MachineLocality

/-! ### List enumeration helpers -/

theorem range_add' (a b : ℕ) : List.range (a + b) = List.range a ++ (List.range b).map (· + a) := by
  induction b with
  | zero => simp
  | succ b ih => rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ]; simp [Nat.add_comm]

theorem range_mul_map {α : Type} (a b : ℕ) (f : ℕ → α) :
    (List.range (a * b)).map f =
      (List.range a).flatMap fun m => (List.range b).map fun j => f (m * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.succ_mul, range_add', List.map_append, ih, List.range_succ, List.flatMap_append]
      simp [List.map_map, Function.comp_def, Nat.add_comm]

theorem flatMap_congr_mem {α β : Type} (L : List α) (g₁ g₂ : α → List β)
    (h : ∀ x ∈ L, g₁ x = g₂ x) : L.flatMap g₁ = L.flatMap g₂ := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem flatMap_congr_range {β : Type} (n : ℕ) (g₁ g₂ : ℕ → List β)
    (h : ∀ m < n, g₁ m = g₂ m) : (List.range n).flatMap g₁ = (List.range n).flatMap g₂ :=
  flatMap_congr_mem _ _ _ fun m hm => h m (List.mem_range.mp hm)

theorem render_append_fst (R : Regs) (left right : List Instr) :
    (render R (left ++ right)).1 = (render R left).1 ++ (render (render R left).2 right).1 := by
  rw [render_append]

theorem render_append_snd (R : Regs) (left right : List Instr) :
    (render R (left ++ right)).2 = (render (render R left).2 right).2 := by
  rw [render_append]

theorem flatMap_eq_range {α β : Type} (L : List α) (g : α → List β) :
    L.flatMap g = (List.range L.length).flatMap fun m => (L[m]?.map g).getD [] := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.flatMap_cons, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_map, ih]
      simp []

theorem flatMap_range_succ_const {β : Type} (n : ℕ) (J : List β) :
    (List.range (n + 1)).flatMap (fun _ => J) = J ++ (List.range n).flatMap fun _ => J := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem flatMap_range_succ_shift {β : Type} (n : ℕ) (F : ℕ → List β) :
    (List.range (n + 1)).flatMap F = F 0 ++ (List.range n).flatMap fun s => F (s + 1) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

namespace Instance

variable (I : Instance)

/-! ### Registers -/

/-- Registers at the start of a round's cells. -/
noncomputable def roundRegs (t : ℕ) : Regs
  | .base => t * I.count * I.width
  | .win => (t * I.count + 2) * I.width
  | .w => I.width
  | .pw => I.P * I.width

/-- Registers consistent with the start of round `t`. -/
def RoundGood (t : ℕ) (R : Regs) : Prop :=
  R .base = t * I.count * I.width ∧ R .w = I.width ∧ R .pw = I.P * I.width

theorem roundGood_roundRegs (t : ℕ) : I.RoundGood t (I.roundRegs t) := ⟨rfl, rfl, rfl⟩

theorem roundGood_advance (t : ℕ) (R : Regs) (hR : I.RoundGood t R) (n : ℕ) :
    I.RoundGood t (advance R n) := by
  obtain ⟨hb, hw, hpw⟩ := hR
  exact ⟨by simpa using hb, by simpa using hw, by simpa using hpw⟩

theorem count_eq : I.count = 2 + I.D + I.stackCount * I.P := rfl

theorem reg_eq (t g : ℕ) : I.reg t g = t * I.count + g := rfl

/-- The registers after resetting the window register at the start of a
round are exactly the round registers. -/
theorem roundStart_regs (t : ℕ) (R : Regs) (hR : I.RoundGood t R) :
    Function.update R .win (R .base + 2 * R .w) = I.roundRegs t := by
  obtain ⟨hb, hw, hpw⟩ := hR
  funext r
  cases r
  · simp [roundRegs, Function.update_of_ne, hb]
  · simp [roundRegs, hb, hw]; ring
  · simp [roundRegs, Function.update_of_ne, hw]
  · simp [roundRegs, Function.update_of_ne, hpw]

@[simp] theorem roundRegs_base (t : ℕ) : I.roundRegs t .base = t * I.count * I.width := rfl
@[simp] theorem roundRegs_win (t : ℕ) : I.roundRegs t .win = (t * I.count + 2) * I.width := rfl
@[simp] theorem roundRegs_w (t : ℕ) : I.roundRegs t .w = I.width := rfl
@[simp] theorem roundRegs_pw (t : ℕ) : I.roundRegs t .pw = I.P * I.width := rfl

/-! ### Group references -/

def labelRef : GroupRef := ([.base], 0)
noncomputable def varRef : GroupRef := ([.base], I.width)
noncomputable def dummyRef (g : ℕ) : GroupRef := ([.base], g * I.width)
noncomputable def topRef (k' : I.tm.K) (i : ℕ) : GroupRef :=
  (.base :: List.replicate (I.kIndex k') .pw, (2 * I.D + 2 + i) * I.width)
noncomputable def headRefs : List GroupRef :=
  [labelRef, I.varRef] ++ (stackList I.tm).flatMap fun k' => (List.range I.D).map (I.topRef k')
noncomputable def winRef (m : ℕ) : GroupRef := ([.win], m * I.width)
noncomputable def windowRefs : List GroupRef := (List.range (2 * I.D + 1)).map I.winRef
noncomputable def selfRef : GroupRef := ([.win], I.D * I.width)
noncomputable def nextSelfRef : GroupRef :=
  (.win :: List.replicate I.stackCount .pw, (2 * I.D + 2) * I.width)
noncomputable def nextRef (g : ℕ) : GroupRef :=
  (.base :: List.replicate I.stackCount .pw, (2 + I.D + g) * I.width)

/-- The reference of a head-side register: label, state, or dummy. -/
noncomputable def headRef (g : ℕ) : GroupRef :=
  if g = 0 then labelRef else if g = 1 then I.varRef else I.dummyRef g

section Eval

variable (R : Regs)

theorem eval_labelRef : GroupRef.eval R labelRef = R .base := by simp [GroupRef.eval, labelRef]
theorem eval_varRef : GroupRef.eval R I.varRef = R .base + I.width := by
  simp [GroupRef.eval, varRef]
theorem eval_dummyRef (g : ℕ) : GroupRef.eval R (I.dummyRef g) = R .base + g * I.width := by
  simp [GroupRef.eval, dummyRef]
theorem eval_topRef (k' : I.tm.K) (i : ℕ) :
    GroupRef.eval R (I.topRef k' i) =
      R .base + I.kIndex k' * R .pw + (2 * I.D + 2 + i) * I.width := by
  simp [GroupRef.eval, topRef, List.sum_replicate, Nat.add_assoc]
theorem eval_winRef (m : ℕ) : GroupRef.eval R (I.winRef m) = R .win + m * I.width := by
  simp [GroupRef.eval, winRef]
theorem eval_selfRef : GroupRef.eval R I.selfRef = R .win + I.D * I.width := by
  simp [GroupRef.eval, selfRef]
theorem eval_nextSelfRef :
    GroupRef.eval R I.nextSelfRef =
      R .win + I.stackCount * R .pw + (2 * I.D + 2) * I.width := by
  simp [GroupRef.eval, nextSelfRef, List.sum_replicate, Nat.add_assoc]
theorem eval_nextRef (g : ℕ) :
    GroupRef.eval R (I.nextRef g) =
      R .base + I.stackCount * R .pw + (2 + I.D + g) * I.width := by
  simp [GroupRef.eval, nextRef, List.sum_replicate, Nat.add_assoc]

theorem eval_headRef (g : ℕ) : GroupRef.eval R (I.headRef g) = R .base + g * I.width := by
  simp only [headRef]
  split_ifs with h0 h1
  · subst h0; simp [eval_labelRef]
  · subst h1; simp [eval_varRef]
  · exact I.eval_dummyRef R g

/-- The head references evaluate to the head registers' slot bases. -/
theorem headRefs_map_eval (t : ℕ) (hR : I.RoundGood t R) :
    I.headRefs.map (GroupRef.eval R) = (I.headGroups.map (I.reg t)).map (· * I.width) := by
  obtain ⟨hb, hw, hpw⟩ := hR
  simp only [headRefs, Params.headGroups, List.map_append, List.map_cons, List.map_nil,
    List.map_flatMap, List.map_map, eval_labelRef, eval_varRef, hb, reg_eq, Function.comp_def,
    eval_topRef, hpw, Params.cellGroup]
  congr 1
  · simp only [List.cons.injEq, and_true]
    exact ⟨by ring, by ring⟩
  · apply flatMap_congr_mem
    intro k' _
    apply List.map_congr_left
    intro i _
    ring

end Eval

/-! ### Blocks of the tableau -/

/-- The transition block of register `g` at time `t`. -/
noncomputable def transBlock (t g : ℕ) : Formula ℕ :=
  registerCNF I.width ((I.deps g).map (I.reg t) ++ [I.reg (t + 1) g])
    (I.toParams.localSystem.transitionRelation g)

theorem transitionCNF_eq :
    I.toParams.localSystem.transitionCNF =
      (List.range I.horizon).flatMap fun t =>
        (List.range I.count).flatMap fun g => I.transBlock t g :=
  rfl

/-- The final block of register `g`. -/
noncomputable def finalBlock (g : ℕ) : Formula ℕ :=
  fixRegister I.width (I.reg I.horizon g) (I.value I.finalCfg g)

theorem finalCNF_eq : I.finalCNF = (List.range I.count).flatMap I.finalBlock := rfl

theorem initCNF_eq : I.initCNF = (List.range I.count).flatMap I.initBlock := rfl

/-! ### Descriptors -/

noncomputable def labelTrans : FormulaDesc :=
  registerDesc I.width (I.headRefs ++ [I.nextRef 0])
    (I.toParams.localSystem.transitionRelation 0)
noncomputable def varTrans : FormulaDesc :=
  registerDesc I.width (I.headRefs ++ [I.nextRef 1])
    (I.toParams.localSystem.transitionRelation 1)
noncomputable def dummyTrans (g : ℕ) : FormulaDesc :=
  registerDesc I.width [I.nextRef g] (I.toParams.localSystem.transitionRelation g)
noncomputable def cellTrans (k : I.tm.K) (j : ℕ) : FormulaDesc :=
  if I.IsReal j then
    registerDesc I.width (I.headRefs ++ I.windowRefs ++ [I.nextSelfRef])
      (I.toParams.localSystem.transitionRelation (I.cellGroup k j))
  else
    registerDesc I.width [I.nextSelfRef]
      (I.toParams.localSystem.transitionRelation (I.cellGroup k j))

noncomputable def initDesc (g : ℕ) : FormulaDesc :=
  fixDesc I.width (I.headRef g) (I.value (I.initCfg []) g)
noncomputable def initCellDesc (k : I.tm.K) (j : ℕ) : FormulaDesc :=
  match I.certIndex? (I.cellGroup k j) with
  | some _ => registerDesc I.width [I.selfRef, I.winRef (I.D + 1)] I.certRel
  | none => fixDesc I.width I.selfRef (I.value (I.initCfg []) (I.cellGroup k j))

noncomputable def finalDesc (g : ℕ) : FormulaDesc :=
  fixDesc I.width (I.headRef g) (I.value I.finalCfg g)
noncomputable def finalCellDesc (k : I.tm.K) (j : ℕ) : FormulaDesc :=
  fixDesc I.width I.selfRef (I.value I.finalCfg (I.cellGroup k j))

/-! ### Per-block correctness -/

theorem formulaOf_labelTrans (t : ℕ) :
    formulaOf (I.roundRegs t) I.labelTrans = I.transBlock t 0 := by
  rw [labelTrans, transBlock, Params.deps_zero]
  apply formulaOf_registerDesc
  rw [List.map_append, List.map_append, I.headRefs_map_eval _ t (I.roundGood_roundRegs t)]
  simp only [List.map_cons, List.map_nil, eval_nextRef, roundRegs_base, roundRegs_pw, reg_eq,
    count_eq]
  congr 2
  ring

theorem formulaOf_varTrans (t : ℕ) :
    formulaOf (I.roundRegs t) I.varTrans = I.transBlock t 1 := by
  rw [varTrans, transBlock, Params.deps_one]
  apply formulaOf_registerDesc
  rw [List.map_append, List.map_append, I.headRefs_map_eval _ t (I.roundGood_roundRegs t)]
  simp only [List.map_cons, List.map_nil, eval_nextRef, roundRegs_base, roundRegs_pw, reg_eq,
    count_eq]
  congr 2
  ring

theorem formulaOf_dummyTrans (t : ℕ) (g : ℕ) (hg2 : 2 ≤ g) (hgd : g < I.D + 2) :
    formulaOf (I.roundRegs t) (I.dummyTrans g) = I.transBlock t g := by
  rw [dummyTrans, transBlock, Params.deps_dummy _ g hg2 hgd]
  apply formulaOf_registerDesc
  simp only [List.map_cons, List.map_nil, List.nil_append, eval_nextRef, roundRegs_base,
    roundRegs_pw, reg_eq, count_eq]
  congr 1
  ring

theorem formulaOf_cellTrans (t : ℕ) (k : I.tm.K) (j : ℕ) (hj : j < I.P) :
    formulaOf (advance (I.roundRegs t) (I.kIndex k * I.P + j)) (I.cellTrans k j) =
      I.transBlock t (I.cellGroup k j) := by
  have hgood := I.roundGood_advance t _ (I.roundGood_roundRegs t) (I.kIndex k * I.P + j)
  have hwin : advance (I.roundRegs t) (I.kIndex k * I.P + j) .win =
      (t * I.count + 2) * I.width + (I.kIndex k * I.P + j) * I.width := by
    simp
  rw [cellTrans, transBlock, Params.deps_cellGroup _ k j hj]
  by_cases hreal : I.IsReal j
  · obtain ⟨hDj, hjP⟩ := hreal
    rw [if_pos ⟨hDj, hjP⟩, if_pos ⟨hDj, hjP⟩]
    apply formulaOf_registerDesc
    simp only [List.map_append, I.headRefs_map_eval _ t hgood, List.map_cons, List.map_nil]
    congr 2
    · simp only [windowRefs, Params.windowGroups, List.map_map, Function.comp_def, eval_winRef,
        hwin, reg_eq, Params.cellGroup]
      apply List.map_congr_left
      intro m _
      obtain ⟨i, rfl⟩ : ∃ i, j = I.D + i := ⟨j - I.D, by omega⟩
      rw [Nat.add_sub_cancel_left]
      ring
    · simp only [eval_nextSelfRef, hwin, advance_pw, roundRegs_pw, reg_eq, count_eq,
        Params.cellGroup]
      ring
  · rw [if_neg hreal, if_neg hreal]
    apply formulaOf_registerDesc
    simp only [List.map_cons, List.map_nil, List.nil_append, eval_nextSelfRef, hwin, advance_pw,
      roundRegs_pw, reg_eq, count_eq, Params.cellGroup]
    congr 1
    ring

theorem certIndex?_head (g : ℕ) (hgd : g < I.D + 2) : I.certIndex? g = none := by
  rw [certIndex?_eq_none_iff, mem_certGroups]
  rintro ⟨i, _, rfl⟩
  have := I.cellGroup_ge I.tm.k₀ (I.D + I.inputLength + i)
  simp only [certGroup] at hgd
  omega

theorem formulaOf_initDesc (g : ℕ) (hgd : g < I.D + 2) :
    formulaOf (I.roundRegs 0) (I.initDesc g) = I.initBlock g := by
  simp only [initDesc, initBlock, I.certIndex?_head g hgd]
  apply formulaOf_fixDesc
  simp [eval_headRef, reg_eq]

theorem formulaOf_initCellDesc (k : I.tm.K) (j : ℕ) (hj : j < I.P) :
    formulaOf (advance (I.roundRegs 0) (I.kIndex k * I.P + j)) (I.initCellDesc k j) =
      I.initBlock (I.cellGroup k j) := by
  have hwin : advance (I.roundRegs 0) (I.kIndex k * I.P + j) .win =
      (0 * I.count + 2) * I.width + (I.kIndex k * I.P + j) * I.width := by simp
  cases hc : I.certIndex? (I.cellGroup k j) with
  | none =>
      simp only [initCellDesc, initBlock, hc]
      apply formulaOf_fixDesc
      simp only [eval_selfRef, hwin, reg_eq, Params.cellGroup]
      ring
  | some i =>
      obtain ⟨hi, hg⟩ := I.certIndex?_eq_some _ i hc
      simp only [initCellDesc, initBlock, hc, certChain]
      apply formulaOf_registerDesc
      have h1 : I.certGroup (i + 1) = I.certGroup i + 1 := by
        have e1 := I.certGroup_eq (i + 1)
        have e2 := I.certGroup_eq i
        omega
      simp only [List.map_cons, List.map_nil, eval_selfRef, eval_winRef, hwin, reg_eq, h1, ← hg,
        Params.cellGroup]
      congr 2 <;> ring

theorem formulaOf_finalDesc (g : ℕ) :
    formulaOf (I.roundRegs I.horizon) (I.finalDesc g) = I.finalBlock g := by
  rw [finalDesc, finalBlock]
  apply formulaOf_fixDesc
  simp only [eval_headRef, roundRegs_base, reg_eq]
  ring

theorem formulaOf_finalCellDesc (k : I.tm.K) (j : ℕ) :
    formulaOf (advance (I.roundRegs I.horizon) (I.kIndex k * I.P + j)) (I.finalCellDesc k j) =
      I.finalBlock (I.cellGroup k j) := by
  rw [finalCellDesc, finalBlock]
  apply formulaOf_fixDesc
  simp only [eval_selfRef, advance_win, roundRegs_win, roundRegs_w, reg_eq, Params.cellGroup]
  ring

/-! ### Rounds -/

/-- The head and dummy jobs of a round. -/
noncomputable def headJob (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) : List Instr :=
  formulaJob d0 ++ formulaJob d1 ++ (List.range I.D).flatMap fun i => formulaJob (dd (i + 2))

/-- The cell descriptors of a round, in register order. -/
noncomputable def cellDescs (f : I.tm.K → ℕ → FormulaDesc) : List FormulaDesc :=
  (stackList I.tm).flatMap fun k => (List.range I.P).map (f k)

/-- A round without the base update: reset the window, head, cells. -/
noncomputable def openRound (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc) : List Instr :=
  roundStart ++ I.headJob d0 d1 dd ++ cellsJob (I.cellDescs f)

/-- A transition round: an open round followed by the base update. -/
noncomputable def roundJob (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc) : List Instr :=
  I.openRound d0 d1 dd f ++ roundEnd I.D

/-- The formula of a round evaluated at the round registers. -/
noncomputable def roundFormula (R : Regs) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc) : Formula ℕ :=
  formulaOf R d0 ++ formulaOf R d1 ++ ((List.range I.D).flatMap fun i => formulaOf R (dd (i + 2))) ++
    cellsFormula R (I.cellDescs f)

theorem render_formulaJob_flatMap (R : Regs) {α : Type} (L : List α) (h : α → FormulaDesc) :
    render R (L.flatMap fun x => formulaJob (h x)) = (encode (L.flatMap fun x => formulaOf R (h x)), R) := by
  induction L with
  | nil => simp [render]
  | cons x L ih =>
      rw [List.flatMap_cons, render_append, render_formulaJob, ih]
      simp [encode_append]

theorem render_headJob (R : Regs) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) :
    render R (I.headJob d0 d1 dd) =
      (encode (formulaOf R d0 ++ formulaOf R d1 ++
        (List.range I.D).flatMap fun i => formulaOf R (dd (i + 2))), R) := by
  simp only [headJob, render_append, render_formulaJob, render_formulaJob_flatMap, encode_append]

theorem cellDescs_length (f : I.tm.K → ℕ → FormulaDesc) :
    (I.cellDescs f).length = I.stackCount * I.P := by
  simp [cellDescs, List.length_flatMap, Params.stackCount, List.map_const', List.sum_replicate]

theorem render_openRound (t : ℕ) (R : Regs) (hR : I.RoundGood t R) (d0 d1 : FormulaDesc)
    (dd : ℕ → FormulaDesc) (f : I.tm.K → ℕ → FormulaDesc) :
    render R (I.openRound d0 d1 dd f) =
      (encode (I.roundFormula (I.roundRegs t) d0 d1 dd f),
        advance (I.roundRegs t) (I.stackCount * I.P)) := by
  simp only [openRound, render_append, render_roundStart, I.roundStart_regs t R hR,
    render_headJob, render_cellsJob, cellDescs_length, roundFormula, encode_append,
    List.nil_append, List.append_assoc]

theorem render_roundJob (t : ℕ) (R : Regs) (hR : I.RoundGood t R) (d0 d1 : FormulaDesc)
    (dd : ℕ → FormulaDesc) (f : I.tm.K → ℕ → FormulaDesc) :
    (render R (I.roundJob d0 d1 dd f)).1 = encode (I.roundFormula (I.roundRegs t) d0 d1 dd f) ∧
      I.RoundGood (t + 1) (render R (I.roundJob d0 d1 dd f)).2 := by
  simp only [roundJob, render_append, I.render_openRound t R hR, render_roundEnd, List.append_nil]
  refine ⟨by first | rfl | trivial, ?_, ?_, ?_⟩
  · simp only [Function.update_self, advance_win, advance_w, roundRegs_win, roundRegs_w, count_eq]
    ring
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]

/-- The descriptor of the `i`-th cell in register order. -/
noncomputable def cellIdx (f : I.tm.K → ℕ → FormulaDesc) (i : ℕ) : FormulaDesc :=
  ((stackList I.tm)[i / I.P]?.map fun k => f k (i % I.P)).getD []

theorem cellDescs_eq (f : I.tm.K → ℕ → FormulaDesc) :
    I.cellDescs f = (List.range (I.stackCount * I.P)).map (I.cellIdx f) := by
  rw [cellDescs, flatMap_eq_range, range_mul_map]
  apply flatMap_congr_range
  intro m hm
  have hm' : m < (stackList I.tm).length := hm
  rw [List.getElem?_eq_getElem hm']
  simp only [Option.map_some, Option.getD_some]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  simp only [cellIdx]
  rw [show (m * I.P + j) / I.P = m by
      rw [Nat.mul_comm, Nat.mul_add_div I.P_pos, Nat.div_eq_of_lt hj', Nat.add_zero],
    show (m * I.P + j) % I.P = j by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj'],
    List.getElem?_eq_getElem hm']
  rfl

/-- A round formula whose blocks match a block function is the register-ordered
concatenation of those blocks. -/
theorem roundFormula_eq (R : Regs) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc) (blk : ℕ → Formula ℕ)
    (h0 : formulaOf R d0 = blk 0) (h1 : formulaOf R d1 = blk 1)
    (hd : ∀ i < I.D, formulaOf R (dd (i + 2)) = blk (i + 2))
    (hc : ∀ k j, j < I.P → formulaOf (advance R (I.kIndex k * I.P + j)) (f k j) =
      blk (I.cellGroup k j)) :
    I.roundFormula R d0 d1 dd f = (List.range I.count).flatMap blk := by
  have hd' : ((List.range I.D).flatMap fun i => formulaOf R (dd (i + 2))) =
      (List.range I.D).flatMap fun i => blk (i + 2) :=
    flatMap_congr_range _ _ _ fun i hi => hd i hi
  have hc' : cellsFormula R (I.cellDescs f) =
      (List.range (I.stackCount * I.P)).flatMap fun i => blk (i + (2 + I.D)) := by
    rw [cellDescs_eq, cellsFormula_map_range]
    apply flatMap_congr_range
    intro i hi
    have hdiv : i / I.P < (stackList I.tm).length := by
      change i / I.P < I.stackCount
      rw [Nat.div_lt_iff_lt_mul I.P_pos]; exact hi
    have hmod : i % I.P < I.P := Nat.mod_lt _ I.P_pos
    simp only [cellIdx, List.getElem?_eq_getElem hdiv, Option.map_some, Option.getD_some]
    have hk := I.kIndex_getElem (i / I.P) hdiv
    have hi' : I.kIndex ((stackList I.tm)[i / I.P]'hdiv) * I.P + i % I.P = i := by
      rw [hk, Nat.div_add_mod']
    have hcell := hc ((stackList I.tm)[i / I.P]'hdiv) (i % I.P) hmod
    rw [hi'] at hcell
    rw [hcell]
    congr 1
    simp only [Params.cellGroup, hk]
    rw [Nat.div_add_mod']
    omega
  have hsplit : List.range I.count = [0, 1] ++ (List.range I.D).map (· + 2) ++
      (List.range (I.stackCount * I.P)).map (· + (2 + I.D)) := by
    rw [count_eq, range_add', range_add']
    rfl
  rw [hsplit, List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map,
    roundFormula, h0, h1, hd', hc']
  simp [List.append_assoc]

/-! ### The skeleton -/

/-- The initial registers: widths set, base and window zero. -/
noncomputable def initRegs : Regs
  | .w => I.width
  | .pw => I.P * I.width
  | .base => 0
  | .win => 0

theorem roundGood_initRegs : I.RoundGood 0 I.initRegs := by
  refine ⟨?_, rfl, rfl⟩
  simp [initRegs]

/-- The job rendering the whole tableau. -/
noncomputable def skeleton : List Instr :=
  I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc ++
    ((List.range I.horizon).flatMap fun _ =>
      I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans) ++
    I.openRound (I.finalDesc 0) (I.finalDesc 1) I.finalDesc I.finalCellDesc

/-- The transition rounds render the transition blocks of consecutive times. -/
theorem render_transRounds (n : ℕ) : ∀ (t : ℕ) (R : Regs), I.RoundGood t R →
    (render R ((List.range n).flatMap fun _ =>
        I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)).1 =
      encode ((List.range n).flatMap fun s => (List.range I.count).flatMap fun g =>
        I.transBlock (t + s) g) ∧
    I.RoundGood (t + n) (render R ((List.range n).flatMap fun _ =>
        I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)).2 := by
  induction n with
  | zero =>
      intro t R hR
      simp only [List.range_zero, List.flatMap_nil, render, encode_nil, Nat.add_zero]
      exact ⟨trivial, hR⟩
  | succ n ih =>
      intro t R hR
      obtain ⟨hout, hgood⟩ := I.render_roundJob t R hR I.labelTrans I.varTrans I.dummyTrans
        I.cellTrans
      obtain ⟨hout', hgood'⟩ := ih (t + 1) _ hgood
      have hjob := flatMap_range_succ_const n
        (I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
      have e1 := render_append_fst R (I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
        ((List.range n).flatMap fun _ => I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
      have e2 := render_append_snd R (I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
        ((List.range n).flatMap fun _ => I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
      rw [hout, hout'] at e1
      rw [hjob]
      refine ⟨e1.trans ?_, ?_⟩
      · have hfirst : I.roundFormula (I.roundRegs t) I.labelTrans I.varTrans I.dummyTrans
            I.cellTrans = (List.range I.count).flatMap fun g => I.transBlock (t + 0) g :=
          (I.roundFormula_eq _ _ _ _ _ (I.transBlock t) (I.formulaOf_labelTrans t)
            (I.formulaOf_varTrans t)
            (fun i hi => I.formulaOf_dummyTrans t (i + 2) (by omega) (by omega))
            (fun k j hj => I.formulaOf_cellTrans t k j hj)).trans (by rw [Nat.add_zero])
        have hrest : ((List.range n).flatMap fun s =>
            (List.range I.count).flatMap fun g => I.transBlock (t + 1 + s) g) =
            (List.range n).flatMap fun s =>
              (List.range I.count).flatMap fun g => I.transBlock (t + (s + 1)) g :=
          flatMap_congr_range _ _ _ fun s _ => by rw [show t + 1 + s = t + (s + 1) by omega]
        calc encode (I.roundFormula (I.roundRegs t) I.labelTrans I.varTrans I.dummyTrans
              I.cellTrans) ++ encode ((List.range n).flatMap fun s =>
                (List.range I.count).flatMap fun g => I.transBlock (t + 1 + s) g)
            = encode ((List.range I.count).flatMap fun g => I.transBlock (t + 0) g) ++
                encode ((List.range n).flatMap fun s =>
                  (List.range I.count).flatMap fun g => I.transBlock (t + (s + 1)) g) :=
              congrArg₂ (· ++ ·) (congrArg encode hfirst) (congrArg encode hrest)
          _ = encode (((List.range I.count).flatMap fun g => I.transBlock (t + 0) g) ++
                (List.range n).flatMap fun s =>
                  (List.range I.count).flatMap fun g => I.transBlock (t + (s + 1)) g) :=
              (encode_append _ _).symm
          _ = encode ((List.range (n + 1)).flatMap fun s =>
                (List.range I.count).flatMap fun g => I.transBlock (t + s) g) :=
              congrArg encode (flatMap_range_succ_shift n fun s =>
                (List.range I.count).flatMap fun g => I.transBlock (t + s) g).symm
      · rw [show t + 1 + n = t + (n + 1) by omega] at hgood'
        rw [e2]
        exact hgood'

/-- Rendering the skeleton from the initial registers gives exactly the
unary encoding of the tableau. -/
theorem render_skeleton : (render I.initRegs I.skeleton).1 = encode I.tableau := by
  have h1 := I.render_openRound 0 _ I.roundGood_initRegs (I.initDesc 0) (I.initDesc 1)
    I.initDesc I.initCellDesc
  obtain ⟨hout, hgood⟩ := I.render_transRounds I.horizon 0 _
    (I.roundGood_advance 0 _ (I.roundGood_roundRegs 0) (I.stackCount * I.P))
  rw [Nat.zero_add] at hgood
  have h3 := I.render_openRound I.horizon _ hgood (I.finalDesc 0) (I.finalDesc 1) I.finalDesc
    I.finalCellDesc
  have hinit : I.roundFormula (I.roundRegs 0) (I.initDesc 0) (I.initDesc 1) I.initDesc
      I.initCellDesc = I.initCNF := by
    rw [initCNF_eq]
    exact I.roundFormula_eq _ _ _ _ _ I.initBlock (I.formulaOf_initDesc 0 (by omega))
      (I.formulaOf_initDesc 1 (by omega)) (fun i hi => I.formulaOf_initDesc (i + 2) (by omega))
      (fun k j hj => I.formulaOf_initCellDesc k j hj)
  have htrans : ((List.range I.horizon).flatMap fun s =>
      (List.range I.count).flatMap fun g => I.transBlock (0 + s) g) =
      I.toParams.localSystem.transitionCNF := by
    rw [transitionCNF_eq]
    apply flatMap_congr_range
    intro s _
    rw [Nat.zero_add]
  have hfinal : I.roundFormula (I.roundRegs I.horizon) (I.finalDesc 0) (I.finalDesc 1) I.finalDesc
      I.finalCellDesc = I.finalCNF := by
    rw [finalCNF_eq]
    exact I.roundFormula_eq _ _ _ _ _ I.finalBlock (I.formulaOf_finalDesc 0)
      (I.formulaOf_finalDesc 1) (fun i _ => I.formulaOf_finalDesc (i + 2))
      (fun k j _ => I.formulaOf_finalCellDesc k j)
  have e1 := render_append_fst I.initRegs
    (I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc ++
      (List.range I.horizon).flatMap fun _ =>
        I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
    (I.openRound (I.finalDesc 0) (I.finalDesc 1) I.finalDesc I.finalCellDesc)
  have e2 := render_append_fst I.initRegs
    (I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc)
    ((List.range I.horizon).flatMap fun _ =>
      I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
  have e3 := render_append_snd I.initRegs
    (I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc)
    ((List.range I.horizon).flatMap fun _ =>
      I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)
  rw [h1] at e2 e3
  dsimp only at e2 e3
  rw [hout] at e2
  rw [e3, h3] at e1
  rw [e2] at e1
  dsimp only at e1
  rw [hinit, htrans, hfinal] at e1
  rw [skeleton]
  refine e1.trans ?_
  rw [tableau, encode_append, encode_append, List.append_assoc]

end Instance

end LeanNPHardness.MachineTableau
