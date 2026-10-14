import LeanNPHardness.TableauSkeleton
import LeanNPHardness.TableauInterpreter
import Mathlib.Tactic.Linarith

/-!
# Register bounds along the skeleton

The interpreter's step count on a job depends on the register values it
meets. `PrefixLE M R J` says every prefix of `J` rendered from `R` leaves
registers at most `M`; `interpSteps_le` bounds the interpreter's steps and
`render_fst_length_le` bounds the rendered output from such a bound. The
skeleton satisfies `PrefixLE` with the bound `regBound`, which is linear in
the horizon times the register count.
-/

namespace LeanNPHardness.TableauJobs

open CNF.Unary MachineTableau

/-- Instructions that leave the registers unchanged. -/
def Instr.pure : Instr → Prop
  | .addTo _ _ => False
  | .clear _ => False
  | _ => True

theorem renderInstr_pure_snd (R : Regs) (i : Instr) (h : i.pure) : (renderInstr R i).2 = R := by
  rcases i with b | r | _ | _ | ⟨d, s⟩ | r
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl
  · exact absurd h id
  · exact absurd h id

theorem render_pure_snd (R : Regs) (J : List Instr) (h : ∀ i ∈ J, i.pure) :
    (render R J).2 = R := by
  induction J generalizing R with
  | nil => rfl
  | cons i J ih =>
      simp only [render]
      rw [ih _ fun j hj => h j (List.mem_cons_of_mem _ hj),
        renderInstr_pure_snd R i (h i (List.mem_cons_self ..))]

theorem pure_of_mem_litJob (d : LitDesc) : ∀ i ∈ litJob d, i.pure := by
  intro i hi
  simp only [litJob, List.mem_cons, List.mem_append, List.mem_map, List.mem_replicate] at hi
  rcases hi with rfl | ⟨r, _, rfl⟩ | ⟨_, rfl⟩ <;> trivial

theorem pure_of_mem_clauseJob (c : ClauseDesc) : ∀ i ∈ clauseJob c, i.pure := by
  intro i hi
  simp only [clauseJob, List.mem_append, List.mem_flatMap, List.mem_singleton] at hi
  rcases hi with ⟨d, _, hd⟩ | rfl
  · exact pure_of_mem_litJob d i hd
  · trivial

theorem pure_of_mem_formulaJob (f : FormulaDesc) : ∀ i ∈ formulaJob f, i.pure := by
  intro i hi
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hi
  exact pure_of_mem_clauseJob c i hc

theorem render_formulaJob_snd (R : Regs) (f : FormulaDesc) : (render R (formulaJob f)).2 = R :=
  render_pure_snd R _ (pure_of_mem_formulaJob f)

/-- All registers at most `M`. -/
def RegsLE (M : ℕ) (R : Regs) : Prop := ∀ r, R r ≤ M

/-- Every prefix of `J` rendered from `R` leaves registers at most `M`. -/
def PrefixLE (M : ℕ) (R : Regs) (J : List Instr) : Prop :=
  ∀ i ≤ J.length, RegsLE M (render R (J.take i)).2

theorem regsLE_update {M : ℕ} {R : Regs} (hR : RegsLE M R) (r : RegName) {v : ℕ} (hv : v ≤ M) :
    RegsLE M (Function.update R r v) := by
  intro r'
  by_cases h : r' = r
  · subst h
    simpa using hv
  · rw [Function.update_of_ne h]
    exact hR r'

theorem PrefixLE.start {M : ℕ} {R : Regs} {J : List Instr} (h : PrefixLE M R J) : RegsLE M R := by
  have := h 0 (Nat.zero_le _)
  simpa [render] using this

theorem PrefixLE.finish {M : ℕ} {R : Regs} {J : List Instr} (h : PrefixLE M R J) :
    RegsLE M (render R J).2 := by
  have := h J.length le_rfl
  simpa using this

theorem prefixLE_append {M : ℕ} {R : Regs} {A B : List Instr} (hA : PrefixLE M R A)
    (hB : PrefixLE M (render R A).2 B) : PrefixLE M R (A ++ B) := by
  intro i hi
  by_cases h : i ≤ A.length
  · rw [List.take_append_of_le_length h]
    exact hA i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = A.length + j := ⟨i - A.length, by omega⟩
    rw [List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, render_append_snd]
    simp only [List.length_append] at hi
    exact hB j (by omega)

theorem prefixLE_of_pure {M : ℕ} {R : Regs} {J : List Instr} (h : ∀ i ∈ J, i.pure)
    (hR : RegsLE M R) : PrefixLE M R J := by
  intro i _
  rw [render_pure_snd R _ fun j hj => h j (List.mem_of_mem_take hj)]
  exact hR

theorem prefixLE_cellStep {M : ℕ} {R : Regs} (hR : RegsLE M R) (h : R .win + R .w ≤ M) :
    PrefixLE M R cellStep := by
  intro i hi
  simp only [cellStep, List.length_singleton] at hi
  rcases i with _ | _ | i
  · simpa [render] using hR
  · simp only [cellStep, List.take_succ_cons, List.take_nil]
    rw [show [Instr.addTo .win .w] = cellStep from rfl, render_cellStep, advance]
    exact regsLE_update hR _ (by omega)
  · omega

theorem prefixLE_roundStart {M : ℕ} {R : Regs} (hR : RegsLE M R)
    (h : R .base + 2 * R .w ≤ M) : PrefixLE M R roundStart := by
  intro i hi
  simp only [roundStart, List.length_cons, List.length_nil] at hi
  have hb := hR .base
  rcases i with _ | _ | _ | _ | _ | i
  · simpa [render] using hR
  · simp only [roundStart, List.take_succ_cons, List.take_zero, render, renderInstr]
    exact regsLE_update hR _ (Nat.zero_le _)
  · simp only [roundStart, List.take_succ_cons, List.take_zero, render, renderInstr,
      Function.update_idem, Function.update_self, Function.update_of_ne (by decide : RegName.base ≠ .win)]
    exact regsLE_update hR _ (by omega)
  · simp only [roundStart, List.take_succ_cons, List.take_zero, render, renderInstr,
      Function.update_idem, Function.update_self, Function.update_of_ne (by decide : RegName.base ≠ .win),
      Function.update_of_ne (by decide : RegName.w ≠ .win)]
    exact regsLE_update hR _ (by omega)
  · simp only [roundStart, List.take_succ_cons, List.take_zero, render, renderInstr,
      Function.update_idem, Function.update_self, Function.update_of_ne (by decide : RegName.base ≠ .win),
      Function.update_of_ne (by decide : RegName.w ≠ .win)]
    exact regsLE_update hR _ (by omega)
  · omega

theorem prefixLE_roundEnd {M : ℕ} {R : Regs} (D : ℕ) (hR : RegsLE M R)
    (h : R .win + D * R .w ≤ M) : PrefixLE M R (roundEnd D) := by
  intro i hi
  simp only [roundEnd, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate] at hi
  have hwin := hR .win
  rcases i with _ | _ | j
  · simpa [render] using hR
  · simp only [roundEnd, List.cons_append, List.take_succ_cons, List.take_zero, render, renderInstr]
    exact regsLE_update hR _ (Nat.zero_le _)
  · have hsplit : (roundEnd D).take (j + 1 + 1) =
        [Instr.clear .base, .addTo .base .win] ++ List.replicate (min j D) (.addTo .base .w) := by
      rw [roundEnd, List.take_append, List.take_of_length_le (by simp),
        List.length_cons, List.length_cons, List.length_nil, show j + 1 + 1 - (0 + 1 + 1) = j by omega,
        List.take_replicate]
    rw [hsplit, render_append_snd, render_replicate_addTo]
    simp only [render, renderInstr, Function.update_idem, Function.update_self,
      Function.update_of_ne (by decide : RegName.win ≠ .base),
      Function.update_of_ne (by decide : RegName.w ≠ .base), Nat.zero_add]
    refine regsLE_update hR _ ?_
    calc R .win + min j D * R .w ≤ R .win + D * R .w :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.min_le_right _ _)) _
      _ ≤ M := h

theorem prefixLE_cellsJob {M : ℕ} (ds : List FormulaDesc) : ∀ (R : Regs), RegsLE M R →
    R .win + ds.length * R .w ≤ M → PrefixLE M R (cellsJob ds) := by
  induction ds with
  | nil =>
      intro R hR _ i hi
      simp only [cellsJob, List.flatMap_nil, List.length_nil, Nat.le_zero] at hi
      subst hi
      simpa [render] using hR
  | cons d ds ih =>
      intro R hR h
      have hstep : R .win + R .w ≤ M := by
        simp only [List.length_cons, Nat.succ_mul] at h
        omega
      rw [cellsJob, List.flatMap_cons, ← cellsJob]
      refine prefixLE_append (prefixLE_append (prefixLE_of_pure (pure_of_mem_formulaJob d) hR) ?_) ?_
      · rw [render_formulaJob_snd]
        exact prefixLE_cellStep hR hstep
      · rw [render_append_snd, render_formulaJob_snd, render_cellStep]
        refine ih (advance R 1) ?_ ?_
        · rw [advance]
          exact regsLE_update hR _ (by omega)
        · simp only [advance_win, advance_w, List.length_cons, Nat.succ_mul] at h ⊢
          omega

/-- Steps of one handler are bounded by the register bound. -/
theorem instrCost_le {M : ℕ} {R : Regs} (hR : RegsLE M R) (i : Instr) :
    TableauStacks.instrCost R i ≤ 4 * M + 2 := by
  rcases i with b | r | _ | _ | ⟨d, s⟩ | r <;> simp only [TableauStacks.instrCost]
  · omega
  · have := hR r; omega
  · omega
  · omega
  · have := hR s; omega
  · have := hR r; omega

theorem prefixLE_cons {M : ℕ} {R : Regs} {i : Instr} {J : List Instr}
    (h : PrefixLE M R (i :: J)) : PrefixLE M (renderInstr R i).2 J := by
  intro j hj
  have := h (j + 1) (by simp; omega)
  simpa [render] using this

/-- The interpreter's steps on a job whose rendering keeps registers at
most `M`. -/
theorem interpSteps_le {M : ℕ} (J : List Instr) : ∀ (R : Regs), PrefixLE M R J →
    TableauStacks.interpSteps R J ≤ (4 * M + 4) * J.length + 1 := by
  induction J with
  | nil => intro R _; simp [TableauStacks.interpSteps]
  | cons i J ih =>
      intro R h
      have h1 := instrCost_le h.start i
      have h2 := ih _ (prefixLE_cons h)
      simp only [TableauStacks.interpSteps, List.length_cons]
      rw [Nat.mul_succ]
      omega

theorem renderInstr_fst_length_le {M : ℕ} {R : Regs} (hR : RegsLE M R) (i : Instr) :
    (renderInstr R i).1.length ≤ M + 1 := by
  rcases i with b | r | _ | _ | ⟨d, s⟩ | r
  · cases b <;> simp [renderInstr]
  · simp only [renderInstr, List.length_replicate]
    have := hR r; omega
  · simp [renderInstr]
  · simp [renderInstr]
  · simp [renderInstr]
  · simp [renderInstr]

/-- The rendered output of a job whose rendering keeps registers at most
`M` has at most `M + 1` symbols per instruction. -/
theorem render_fst_length_le {M : ℕ} (J : List Instr) : ∀ (R : Regs), PrefixLE M R J →
    (render R J).1.length ≤ (M + 1) * J.length := by
  induction J with
  | nil => intro R _; simp [render]
  | cons i J ih =>
      intro R h
      have h1 := renderInstr_fst_length_le h.start i
      have h2 := ih _ (prefixLE_cons h)
      simp only [render, List.length_append, List.length_cons]
      rw [Nat.mul_succ]
      omega

end LeanNPHardness.TableauJobs

namespace LeanNPHardness.MachineTableau.Instance

open CNF.Unary TableauJobs MachineLocality

variable (I : Instance)

/-- The register bound along the skeleton. -/
noncomputable def regBound : ℕ := (I.horizon + 2) * I.count * I.width + I.P * I.width

theorem prefixLE_headJob {M : ℕ} {R : Regs} (hR : RegsLE M R) (d0 d1 : FormulaDesc)
    (dd : ℕ → FormulaDesc) : PrefixLE M R (I.headJob d0 d1 dd) :=
  prefixLE_of_pure (fun i hi => by
    simp only [Instance.headJob, List.mem_append, List.mem_flatMap] at hi
    rcases hi with (h | h) | ⟨g, _, h⟩
    · exact pure_of_mem_formulaJob d0 i h
    · exact pure_of_mem_formulaJob d1 i h
    · exact pure_of_mem_formulaJob (dd (g + 2)) i h) hR

theorem render_headJob_snd (R : Regs) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) :
    (render R (I.headJob d0 d1 dd)).2 = R :=
  render_pure_snd R _ fun i hi => by
    simp only [Instance.headJob, List.mem_append, List.mem_flatMap] at hi
    rcases hi with (h | h) | ⟨g, _, h⟩
    · exact pure_of_mem_formulaJob d0 i h
    · exact pure_of_mem_formulaJob d1 i h
    · exact pure_of_mem_formulaJob (dd (g + 2)) i h

/-- An open round keeps registers at most `M` when the window may advance
over all cells. -/
theorem prefixLE_openRound {M : ℕ} {R : Regs} (hR : RegsLE M R)
    (h : R .base + (2 + I.stackCount * I.P) * R .w ≤ M) (d0 d1 : FormulaDesc)
    (dd : ℕ → FormulaDesc) (f : I.tm.K → ℕ → FormulaDesc) :
    PrefixLE M R (I.openRound d0 d1 dd f) := by
  have hR1 : RegsLE M (Function.update R .win (R .base + 2 * R .w)) :=
    regsLE_update hR _ (by rw [Nat.add_mul] at h; omega)
  unfold Instance.openRound
  refine prefixLE_append (prefixLE_append ?_ ?_) ?_
  · exact prefixLE_roundStart hR (by rw [Nat.add_mul] at h; omega)
  · rw [render_roundStart]
    exact I.prefixLE_headJob hR1 d0 d1 dd
  · rw [render_append_snd, render_roundStart, render_headJob_snd]
    refine prefixLE_cellsJob _ _ hR1 ?_
    simp only [cellDescs_length, Function.update_self,
      Function.update_of_ne (by decide : RegName.w ≠ .win)]
    rw [Nat.add_mul] at h
    omega

theorem render_openRound_snd (t : ℕ) (R : Regs) (hR : I.RoundGood t R) (d0 d1 : FormulaDesc)
    (dd : ℕ → FormulaDesc) (f : I.tm.K → ℕ → FormulaDesc) :
    (render R (I.openRound d0 d1 dd f)).2 = advance (I.roundRegs t) (I.stackCount * I.P) := by
  rw [I.render_openRound t R hR]

theorem render_roundJob_snd (t : ℕ) (R : Regs) (hR : I.RoundGood t R) (d0 d1 : FormulaDesc)
    (dd : ℕ → FormulaDesc) (f : I.tm.K → ℕ → FormulaDesc) :
    (render R (I.roundJob d0 d1 dd f)).2 =
      Function.update (advance (I.roundRegs t) (I.stackCount * I.P)) .base
        ((advance (I.roundRegs t) (I.stackCount * I.P)) .win +
          I.D * (advance (I.roundRegs t) (I.stackCount * I.P)) .w) := by
  rw [Instance.roundJob, render_append_snd, I.render_openRound_snd t R hR, render_roundEnd]

/-- Registers consistent with round `t` whose window is within the bound. -/
def Good (t : ℕ) (R : Regs) : Prop :=
  I.RoundGood t R ∧ R .win ≤ (t + 1) * I.count * I.width

theorem count_pos : 0 < I.count := by
  have := I.count_ge_two
  omega

theorem regsLE_of_good {t : ℕ} {R : Regs} (hR : I.Good t R) (ht : t + 1 ≤ I.horizon + 2) :
    RegsLE I.regBound R := by
  obtain ⟨⟨hb, hw, hpw⟩, hwin⟩ := hR
  have hc := I.count_pos
  have h1 : (t + 1) * I.count * I.width ≤ (I.horizon + 2) * I.count * I.width :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ht)
  have h2 : t * I.count * I.width ≤ (t + 1) * I.count * I.width :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  have h3 : I.width ≤ (t + 1) * I.count * I.width := by
    calc I.width = 1 * I.width := (Nat.one_mul _).symm
      _ ≤ (t + 1) * I.count * I.width :=
          Nat.mul_le_mul_right _ (Nat.mul_pos (Nat.succ_pos t) hc)
  intro r
  rcases r with _ | _ | _ | _
  · rw [hb]; unfold regBound; omega
  · unfold regBound; omega
  · rw [hw]; unfold regBound; omega
  · rw [hpw]; unfold regBound; omega

theorem good_window_bound {t : ℕ} {R : Regs} (hR : I.Good t R) (ht : t + 1 ≤ I.horizon + 2) :
    R .base + (2 + I.stackCount * I.P) * R .w ≤ I.regBound := by
  obtain ⟨⟨hb, hw, _⟩, _⟩ := hR
  rw [hb, hw]
  have h1 : (2 + I.stackCount * I.P) * I.width ≤ I.count * I.width := by
    apply Nat.mul_le_mul_right
    rw [count_eq]
    omega
  have h2 : (t + 1) * I.count * I.width ≤ (I.horizon + 2) * I.count * I.width :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ht)
  unfold regBound
  rw [Nat.succ_mul, Nat.add_mul] at h2
  omega

theorem good_advance (t : ℕ) : I.Good t (advance (I.roundRegs t) (I.stackCount * I.P)) := by
  refine ⟨I.roundGood_advance t _ (I.roundGood_roundRegs t) _, ?_⟩
  simp only [advance_win, roundRegs]
  rw [count_eq, show (t + 1) * (2 + I.D + I.stackCount * I.P) * I.width =
    (t * (2 + I.D + I.stackCount * I.P) + 2) * I.width + I.stackCount * I.P * I.width +
      I.D * I.width by ring]
  omega

theorem prefixLE_roundJob {t : ℕ} {R : Regs} (hR : I.Good t R) (ht : t + 1 ≤ I.horizon + 1)
    (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) (f : I.tm.K → ℕ → FormulaDesc) :
    PrefixLE I.regBound R (I.roundJob d0 d1 dd f) ∧
      I.Good (t + 1) (render R (I.roundJob d0 d1 dd f)).2 := by
  have hle : t + 1 ≤ I.horizon + 2 := by omega
  constructor
  · unfold Instance.roundJob
    refine prefixLE_append (I.prefixLE_openRound (I.regsLE_of_good hR hle)
      (I.good_window_bound hR hle) d0 d1 dd f) ?_
    rw [I.render_openRound_snd t R hR.1]
    refine prefixLE_roundEnd I.D (I.regsLE_of_good (I.good_advance t) hle) ?_
    simp only [advance_win, advance_w, roundRegs]
    have h2 : (t + 1) * I.count * I.width ≤ (I.horizon + 2) * I.count * I.width :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
    unfold regBound
    rw [count_eq] at h2 ⊢
    have h3 : (t * (2 + I.D + I.stackCount * I.P) + 2) * I.width + I.stackCount * I.P * I.width +
        I.D * I.width = (t + 1) * (2 + I.D + I.stackCount * I.P) * I.width := by ring
    omega
  · rw [I.render_roundJob_snd t R hR.1]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp only [Function.update_self, advance_win, advance_w, roundRegs, count_eq]
        ring
      · simp [Function.update_of_ne, roundRegs]
      · simp [Function.update_of_ne, roundRegs]
    · simp only [Function.update_of_ne (by decide : RegName.win ≠ .base), advance_win, roundRegs]
      rw [count_eq, ← Nat.add_mul]
      apply Nat.mul_le_mul_right
      have h3 : (t + 1 + 1) * (2 + I.D + I.stackCount * I.P) =
          t * (2 + I.D + I.stackCount * I.P) + 2 * (2 + I.D + I.stackCount * I.P) := by ring
      omega

theorem prefixLE_transRounds (m : ℕ) : ∀ (t : ℕ) (R : Regs), I.Good t R → t + m ≤ I.horizon →
    PrefixLE I.regBound R ((List.range m).flatMap fun _ =>
      I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans) ∧
    I.Good (t + m) (render R ((List.range m).flatMap fun _ =>
      I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans)).2 := by
  induction m with
  | zero =>
      intro t R hR _
      refine ⟨?_, by simpa [render] using hR⟩
      intro i hi
      simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.le_zero] at hi
      subst hi
      simpa [render] using I.regsLE_of_good hR (by omega)
  | succ m ih =>
      intro t R hR hm
      obtain ⟨ih1, ih2⟩ := ih t R hR (by omega)
      obtain ⟨h1, h2⟩ := I.prefixLE_roundJob ih2 (by omega) I.labelTrans I.varTrans I.dummyTrans
        I.cellTrans
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine ⟨prefixLE_append ih1 h1, ?_⟩
      rw [render_append_snd]
      exact h2

theorem good_initRegs : I.Good 0 I.initRegs :=
  ⟨I.roundGood_initRegs, by simp [initRegs]⟩

/-- The skeleton keeps every register at most `regBound`. -/
theorem prefixLE_skeleton : PrefixLE I.regBound I.initRegs I.skeleton := by
  unfold Instance.skeleton
  have h0 := I.good_initRegs
  refine prefixLE_append (prefixLE_append ?_ ?_) ?_
  · exact I.prefixLE_openRound (I.regsLE_of_good h0 (by omega)) (I.good_window_bound h0 (by omega))
      _ _ _ _
  · rw [I.render_openRound_snd 0 _ h0.1]
    exact (I.prefixLE_transRounds I.horizon 0 _ (I.good_advance 0) (by omega)).1
  · rw [render_append_snd, I.render_openRound_snd 0 _ h0.1]
    have := (I.prefixLE_transRounds I.horizon 0 _ (I.good_advance 0) (by omega)).2
    rw [Nat.zero_add] at this
    exact I.prefixLE_openRound (I.regsLE_of_good this (by omega))
      (I.good_window_bound this (by omega)) _ _ _ _

theorem interpSteps_skeleton_le :
    TableauStacks.interpSteps I.initRegs I.skeleton ≤
      (4 * I.regBound + 4) * I.skeleton.length + 1 :=
  interpSteps_le _ _ I.prefixLE_skeleton

theorem encode_tableau_length_le :
    (encode I.tableau).length ≤ (I.regBound + 1) * I.skeleton.length := by
  rw [← I.render_skeleton]
  exact render_fst_length_le _ _ I.prefixLE_skeleton

theorem finalRegs_le : RegsLE I.regBound (render I.initRegs I.skeleton).2 :=
  I.prefixLE_skeleton.finish

end LeanNPHardness.MachineTableau.Instance
