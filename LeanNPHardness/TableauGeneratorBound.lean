import LeanNPHardness.TableauGenerator
import LeanNPHardness.TableauRegisterBounds
import LeanNPHardness.TableauSkeletonBounds
import Mathlib.Tactic.Linarith

/-!
# The polynomial time bound of the generator

Every component of `generatorCost` is bounded by a constant of the
template times a power of the size parameter `sizeParam bound time n`, which
is the sum of the input length, the certificate bound, the horizon, and the
two polynomial values that dominate the Horner intermediate results. The
size parameter is the value of the polynomial `sizePoly bound time` at
`n`, so `generatorCost_le` gives a polynomial time bound.
-/

namespace LeanNPHardness.TableauStacks

open Routines Polynomial

/-! ### Horner evaluation -/

theorem hornerStepCost_le (n a : ℕ) : hornerStepCost n a ≤ 15 * (n + 1) * (a + 1) := by
  simp only [hornerStepCost, loopSteps_eq_sum, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  nlinarith

theorem le_hornerFold (y : ℕ) (hy : 1 ≤ y) (cs : List ℕ) : ∀ acc, acc ≤ hornerFold y cs acc := by
  induction cs with
  | nil => intro acc; exact le_rfl
  | cons c cs ih =>
      intro acc
      refine le_trans ?_ (ih (acc * y + c))
      nlinarith

theorem hornerFold_mono (y : ℕ) (cs : List ℕ) : ∀ {a b : ℕ}, a ≤ b →
    hornerFold y cs a ≤ hornerFold y cs b := by
  induction cs with
  | nil => intro a b h; exact h
  | cons c cs ih =>
      intro a b h
      exact ih (by nlinarith)

theorem hornerFold_le_succ (x : ℕ) (cs : List ℕ) : ∀ a, hornerFold x cs a ≤ hornerFold (x + 1) cs a := by
  induction cs with
  | nil => intro a; exact le_rfl
  | cons c cs ih =>
      intro a
      exact le_trans (ih _) (hornerFold_mono _ _ (by nlinarith))

theorem evalPolyCost_le (x : ℕ) (cs : List ℕ) : ∀ a,
    evalPolyCost x cs a ≤ cs.length * (15 * (x + 1) * (hornerFold (x + 1) cs a + 1)) + 1 := by
  induction cs with
  | nil => intro a; simp [evalPolyCost]
  | cons c cs ih =>
      intro a
      have h1 := hornerStepCost_le x a
      have h2 := ih (a * x + c)
      have hM : hornerFold (x + 1) cs (a * x + c) ≤ hornerFold (x + 1) (c :: cs) a := by
        simp only [hornerFold]
        exact hornerFold_mono _ _ (by nlinarith)
      have ha : a ≤ hornerFold (x + 1) (c :: cs) a := le_hornerFold (x + 1) (by omega) _ a
      simp only [evalPolyCost, List.length_cons]
      have h3 : 15 * (x + 1) * (a + 1) ≤ 15 * (x + 1) * (hornerFold (x + 1) (c :: cs) a + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : cs.length * (15 * (x + 1) * (hornerFold (x + 1) cs (a * x + c) + 1)) ≤
          cs.length * (15 * (x + 1) * (hornerFold (x + 1) (c :: cs) a + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      rw [Nat.succ_mul]
      omega

theorem evalPolyCost_coeffList_le (p : Polynomial ℕ) (x : ℕ) :
    evalPolyCost x (coeffList p) 0 ≤
      (p.natDegree + 1) * (15 * (x + 1) * (p.eval (x + 1) + 1)) + 1 := by
  have := evalPolyCost_le x (coeffList p) 0
  rw [hornerFold_coeffList] at this
  simpa [coeffList] using this

/-! ### The size parameter -/

/-- The size parameter: input length, certificate bound, horizon, and the
values dominating the Horner intermediates, plus one. -/
noncomputable def sizeParam (bound time : Polynomial ℕ) (n : ℕ) : ℕ :=
  n + bound.eval n + time.eval (n + bound.eval n) + bound.eval (n + 1) +
    time.eval (n + bound.eval n + 1) + 1

/-- The size parameter as a polynomial. -/
noncomputable def sizePoly (bound time : Polynomial ℕ) : Polynomial ℕ :=
  X + bound + time.comp (X + bound) + bound.comp (X + 1) + time.comp (X + bound + 1) + 1

theorem sizePoly_eval (bound time : Polynomial ℕ) (n : ℕ) :
    (sizePoly bound time).eval n = sizeParam bound time n := by
  simp [sizePoly, sizeParam, eval_add, eval_comp, eval_X, eval_one]

theorem one_le_sizeParam (bound time : Polynomial ℕ) (n : ℕ) : 1 ≤ sizeParam bound time n := by
  simp only [sizeParam]; omega

theorem parameterCost_le (bound time : Polynomial ℕ) (pb D width n : ℕ) :
    parameterCost bound time pb D width n ≤
      (60 * (bound.natDegree + 1) + 60 * (time.natDegree + 1) + 42 + 10 * pb +
        width * (4 * pb + 18)) * sizeParam bound time n ^ 2 := by
  set S := sizeParam bound time n with hS
  have hS1 : 1 ≤ S := one_le_sizeParam bound time n
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have h1 : 1 ≤ S ^ 2 := le_trans hS1 hS2
  have hn : n ≤ S ^ 2 := by simp only [hS, sizeParam] at hS2 ⊢; omega
  have hq : bound.eval n ≤ S ^ 2 := by simp only [hS, sizeParam] at hS2 ⊢; omega
  have ht : time.eval (n + bound.eval n) ≤ S ^ 2 := by simp only [hS, sizeParam] at hS2 ⊢; omega
  have hpbt : pb * time.eval (n + bound.eval n) ≤ pb * S ^ 2 := Nat.mul_le_mul_left _ ht
  have hpb : pb ≤ pb * S ^ 2 := by nlinarith
  have e1 : evalPolyCost n (coeffList bound) 0 ≤ (60 * (bound.natDegree + 1) + 1) * S ^ 2 := by
    have h := evalPolyCost_coeffList_le bound n
    have hn' : n + 1 ≤ 2 * S := by simp only [hS, sizeParam]; omega
    have hq' : bound.eval (n + 1) + 1 ≤ 2 * S := by simp only [hS, sizeParam]; omega
    have : 15 * (n + 1) * (bound.eval (n + 1) + 1) ≤ 60 * S ^ 2 := by
      calc 15 * (n + 1) * (bound.eval (n + 1) + 1) ≤ 15 * (2 * S) * (2 * S) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hn') hq'
        _ = 60 * S ^ 2 := by ring
    have := Nat.mul_le_mul_left (bound.natDegree + 1) this
    nlinarith
  have e2 : evalPolyCost (n + bound.eval n) (coeffList time) 0 ≤
      (60 * (time.natDegree + 1) + 1) * S ^ 2 := by
    have h := evalPolyCost_coeffList_le time (n + bound.eval n)
    have hn' : n + bound.eval n + 1 ≤ 2 * S := by simp only [hS, sizeParam]; omega
    have ht' : time.eval (n + bound.eval n + 1) + 1 ≤ 2 * S := by simp only [hS, sizeParam]; omega
    have : 15 * (n + bound.eval n + 1) * (time.eval (n + bound.eval n + 1) + 1) ≤ 60 * S ^ 2 := by
      calc 15 * (n + bound.eval n + 1) * (time.eval (n + bound.eval n + 1) + 1) ≤
            15 * (2 * S) * (2 * S) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hn') ht'
        _ = 60 * S ^ 2 := by ring
    have := Nat.mul_le_mul_left (time.natDegree + 1) this
    nlinarith
  have hwg : width * (4 * (n + bound.eval n + pb * time.eval (n + bound.eval n) + 2) + 2) ≤
      width * ((4 * pb + 18) * S ^ 2) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  simp only [parameterCost]
  nlinarith

end LeanNPHardness.TableauStacks

namespace LeanNPHardness.MachineTableau.Instance

open CNF.Unary TableauJobs TableauStacks MachineLocality

/-! ### Constants of the template -/

variable (T : Instance)

/-- `G ≤ cG * S`. -/
noncomputable def cG : ℕ := T.pb + 2
/-- `P ≤ cP * S`. -/
noncomputable def cP : ℕ := T.pb + 2 + 4 * T.D
/-- `count ≤ cCount * S`. -/
noncomputable def cCount : ℕ := 2 + T.D + T.stackCount * T.cP
/-- `regBound ≤ cReg * S ^ 2`. -/
noncomputable def cReg : ℕ := (3 * T.cCount + T.cP) * T.width
/-- `skeleton.length ≤ cSkel * S ^ 2`. -/
noncomputable def cSkel : ℕ :=
  3 * (6 + T.D + (2 + T.D) * T.chunkBound + T.stackCount * T.cP * (T.chunkBound + 1))
/-- `interpSteps ≤ cInterp * S ^ 4`. -/
noncomputable def cInterp : ℕ := (4 * T.cReg + 4) * T.cSkel + 1
/-- `(encode tableau).length ≤ cOut * S ^ 4`. -/
noncomputable def cOut : ℕ := (T.cReg + 1) * T.cSkel
/-- `cleanupCost ≤ cClean * S ^ 2`. -/
noncomputable def cClean : ℕ := 8 * T.cReg + 4 * T.pb + 25
/-- `initRoundCost ≤ cInitR * S`. -/
noncomputable def cInitR : ℕ := 5 + T.D + T.stackCount * (4 * T.D + 7 * T.pb + 21)
/-- `transRoundsCost ≤ cTRs * S ^ 2`. -/
noncomputable def cTRs : ℕ := (6 + T.D + T.stackCount * (4 * T.D + 7 * T.pb + 19)) + 9
/-- `finalRoundCost ≤ cFin * S`. -/
noncomputable def cFin : ℕ := 5 + T.D + T.stackCount * (7 * T.pb + 4 * T.D + 22)
/-- `emitterCost ≤ cEmit * S ^ 2`. -/
noncomputable def cEmit : ℕ := T.cInitR + T.cTRs + T.cFin
/-- `parameterCost ≤ cParam * S ^ 2`. -/
noncomputable def cParam (bound time : Polynomial ℕ) : ℕ :=
  60 * (bound.natDegree + 1) + 60 * (time.natDegree + 1) + 42 + 10 * T.pb + T.width * (4 * T.pb + 18)
/-- `generatorCost ≤ K * S ^ 4`. -/
noncomputable def K (bound time : Polynomial ℕ) : ℕ :=
  T.cParam bound time + T.cEmit + (2 * T.cSkel + 1) + T.cInterp + T.cClean + (2 * T.cOut + 1)

variable {T}

/-! ### The bound -/

theorem generatorCost_le (I : Instance) (bound time : Polynomial ℕ) (n : ℕ)
    (hn : I.inputLength = n) (hq : I.certBound = bound.eval n)
    (ht : I.horizon = time.eval (n + bound.eval n)) :
    generatorCost I bound time n ≤ K I.template bound time * sizeParam bound time n ^ 4 := by
  set S := sizeParam bound time n with hS
  have hS1 : 1 ≤ S := one_le_sizeParam bound time n
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hS24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
  have h1S2 : 1 ≤ S ^ 2 := le_trans hS1 hS2
  have hnS : n ≤ S := by simp only [hS, sizeParam]; omega
  have hqS : I.certBound ≤ S := by rw [hq]; simp only [hS, sizeParam]; omega
  have htS : I.horizon ≤ S := by rw [ht]; simp only [hS, sizeParam]; omega
  have hnq2 : n + I.certBound + 2 ≤ 2 * S := by rw [hq]; simp only [hS, sizeParam]; omega
  have htpb : I.horizon * I.pb ≤ I.pb * S := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ htS
  have hDS : I.D ≤ I.D * S := Nat.le_mul_of_pos_right _ hS1
  have hsc : I.stackCount = (stackList I.tm).length := rfl
  have hpbS : I.pb ≤ I.pb * S := Nat.le_mul_of_pos_right _ hS1
  have hpbS2 : I.pb * S ≤ I.pb * S ^ 2 := Nat.mul_le_mul_left _ hS2
  -- the basic size facts
  have hG : I.G ≤ (I.pb + 2) * S := by
    simp only [Params.G, hn]
    linarith
  have hGc : I.G ≤ I.template.cG * S := by simp only [cG, template_pb]; exact hG
  have hP : I.P ≤ I.template.cP * S := by
    rw [I.P_eq]
    simp only [cP, template_pb, template_D]
    linarith
  have hcount : I.count ≤ I.template.cCount * S := by
    rw [count_eq]
    simp only [cCount, template_D, template_stackCount]
    have := Nat.mul_le_mul_left I.stackCount hP
    linarith
  have hreg : I.regBound ≤ I.template.cReg * S ^ 2 := by
    unfold regBound
    simp only [cReg, template_width]
    have h3 : I.horizon + 2 ≤ 3 * S := by omega
    have h4 : (I.horizon + 2) * I.count * I.width ≤ (3 * S) * (I.template.cCount * S) * I.width :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul h3 hcount)
    have h5 : I.P * I.width ≤ (I.template.cP * S ^ 2) * I.width :=
      Nat.mul_le_mul_right _ (le_trans hP (Nat.mul_le_mul_left _ hS2))
    calc (I.horizon + 2) * I.count * I.width + I.P * I.width
        ≤ (3 * S) * (I.template.cCount * S) * I.width + (I.template.cP * S ^ 2) * I.width :=
          Nat.add_le_add h4 h5
      _ = (3 * I.template.cCount + I.template.cP) * I.width * S ^ 2 := by ring
  have hskel : I.skeleton.length ≤ I.template.cSkel * S ^ 2 := by
    have h1 := I.skeleton_length_le
    have hround : I.roundBound ≤ (6 + I.D + (2 + I.D) * I.template.chunkBound +
        I.stackCount * I.template.cP * (I.template.chunkBound + 1)) * S := by
      unfold roundBound
      have h2 : I.stackCount * I.P * (I.template.chunkBound + 1) ≤
          I.stackCount * (I.template.cP * S) * (I.template.chunkBound + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP)
      have h6 : 6 + I.D + (2 + I.D) * I.template.chunkBound ≤
          (6 + I.D + (2 + I.D) * I.template.chunkBound) * S := Nat.le_mul_of_pos_right _ hS1
      linarith
    have h3 : I.horizon + 2 ≤ 3 * S := by omega
    calc I.skeleton.length ≤ (I.horizon + 2) * I.roundBound := h1
      _ ≤ (3 * S) * ((6 + I.D + (2 + I.D) * I.template.chunkBound +
          I.stackCount * I.template.cP * (I.template.chunkBound + 1)) * S) :=
          Nat.mul_le_mul h3 hround
      _ = I.template.cSkel * S ^ 2 := by
          simp only [cSkel, template_D, template_stackCount]; ring
  have hinterp : interpSteps I.initRegs I.skeleton ≤ I.template.cInterp * S ^ 4 := by
    have h1 := I.interpSteps_skeleton_le
    have h2 : (4 * I.regBound + 4) * I.skeleton.length ≤
        (4 * (I.template.cReg * S ^ 2) + 4 * S ^ 2) * (I.template.cSkel * S ^ 2) :=
      Nat.mul_le_mul (by omega) hskel
    have h4 : 1 ≤ S ^ 4 := le_trans h1S2 hS24
    calc interpSteps I.initRegs I.skeleton ≤ (4 * I.regBound + 4) * I.skeleton.length + 1 := h1
      _ ≤ (4 * (I.template.cReg * S ^ 2) + 4 * S ^ 2) * (I.template.cSkel * S ^ 2) + S ^ 4 :=
          Nat.add_le_add h2 h4
      _ = I.template.cInterp * S ^ 4 := by simp only [cInterp]; ring
  have hout : (encode I.tableau).length ≤ I.template.cOut * S ^ 4 := by
    have h1 := I.encode_tableau_length_le
    have h2 : (I.regBound + 1) * I.skeleton.length ≤
        (I.template.cReg * S ^ 2 + S ^ 2) * (I.template.cSkel * S ^ 2) :=
      Nat.mul_le_mul (by omega) hskel
    calc (encode I.tableau).length ≤ (I.regBound + 1) * I.skeleton.length := h1
      _ ≤ (I.template.cReg * S ^ 2 + S ^ 2) * (I.template.cSkel * S ^ 2) := h2
      _ = I.template.cOut * S ^ 4 := by simp only [cOut]; ring
  have hclean : cleanupCost I n ≤ I.template.cClean * S ^ 2 := by
    have hR := I.finalRegs_le
    have hb := le_trans (hR .base) hreg
    have hw := le_trans (hR .win) hreg
    have hww := le_trans (hR .w) hreg
    have hpw := le_trans (hR .pw) hreg
    have hn2 : n ≤ S ^ 2 := le_trans hnS hS2
    have hq2 : I.certBound ≤ S ^ 2 := le_trans hqS hS2
    have ht2 : I.horizon ≤ S ^ 2 := le_trans htS hS2
    have htpb2 : I.horizon * I.pb ≤ I.pb * S ^ 2 := le_trans htpb hpbS2
    have hG2 : I.G ≤ (I.pb + 2) * S ^ 2 := le_trans hG (Nat.mul_le_mul_left _ hS2)
    simp only [cleanupCost, cClean, template_pb]
    linarith
  have hemit : I.emitterCost n ≤ I.template.cEmit * S ^ 2 := by
    have hinit : I.initRoundCost n ≤ I.template.cInitR * S := by
      have hstack : ∀ k ∈ stackList I.tm,
          I.initStackCostAt n k ≤ (4 * I.D + 7 * I.pb + 21) * S := by
        intro k _
        unfold initStackCostAt
        split_ifs
        · simp only [initInputCost]
          linarith
        · linarith
      have hsum := sum_map_le_length_mul (stackList I.tm) (I.initStackCostAt n) _ hstack
      simp only [initRoundCost, cInitR, template_D, template_stackCount, template_pb]
      rw [hsc]
      linarith
    have htrans : I.transRoundsCost I.horizon I.G ≤ I.template.cTRs * S ^ 2 := by
      have hts : I.transStackCost I.G ≤ (4 * I.D + 7 * I.pb + 19) * S := by
        simp only [transStackCost]
        linarith
      have htr : I.transRoundCost I.G ≤
          (6 + I.D + (stackList I.tm).length * (4 * I.D + 7 * I.pb + 19)) * S := by
        simp only [transRoundCost, List.map_const', List.sum_replicate, smul_eq_mul]
        have := Nat.mul_le_mul_left (stackList I.tm).length hts
        linarith
      simp only [transRoundsCost, loopRoundsCost, Routines.loopSteps_eq_sum, List.map_const',
        List.length_range, List.sum_replicate, smul_eq_mul, cTRs, template_D, template_stackCount,
        template_pb]
      have h5 : I.horizon * (1 + I.transRoundCost I.G + 1) ≤
          S * ((6 + I.D + (stackList I.tm).length * (4 * I.D + 7 * I.pb + 19)) * S + 2 * S) :=
        Nat.mul_le_mul htS (by linarith)
      have h6 : S * ((6 + I.D + (stackList I.tm).length * (4 * I.D + 7 * I.pb + 19)) * S + 2 * S) =
          (6 + I.D + (stackList I.tm).length * (4 * I.D + 7 * I.pb + 19)) * S ^ 2 + 2 * S ^ 2 := by
        ring
      rw [h6] at h5
      rw [hsc]
      linarith
    have hfinal : I.finalRoundCost I.G ≤ I.template.cFin * S := by
      have hstack : ∀ k ∈ stackList I.tm,
          I.finalStackCost k I.G ≤ (7 * I.pb + 4 * I.D + 22) * S := by
        intro k _
        unfold finalStackCost
        have h3 : 3 * (I.G - 1) ≤ 3 * I.G := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        split_ifs <;> linarith
      have hsum := sum_map_le_length_mul (stackList I.tm) (fun k => I.finalStackCost k I.G) _ hstack
      simp only [finalRoundCost, cFin, template_D, template_stackCount, template_pb]
      rw [hsc]
      linarith
    simp only [emitterCost, cEmit]
    have := le_trans hinit (Nat.mul_le_mul_left _ hS2)
    have := le_trans hfinal (Nat.mul_le_mul_left _ hS2)
    linarith
  have hparam : parameterCost bound time I.pb I.D I.width n ≤
      I.template.cParam bound time * S ^ 2 := by
    simp only [cParam, template_pb, template_width]
    exact parameterCost_le bound time I.pb I.D I.width n
  -- combine
  simp only [generatorCost, K]
  have hA := le_trans hparam (Nat.mul_le_mul_left _ hS24)
  have hB := le_trans hemit (Nat.mul_le_mul_left _ hS24)
  have hC := le_trans hskel (Nat.mul_le_mul_left _ hS24)
  have hD := le_trans hclean (Nat.mul_le_mul_left _ hS24)
  have h4 : 1 ≤ S ^ 4 := le_trans h1S2 hS24
  linarith

end LeanNPHardness.MachineTableau.Instance
