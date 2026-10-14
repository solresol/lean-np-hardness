import LeanNPHardness.CNFRegisterConstraint

/-!
# Tableau formulas for register-local transition systems

A deterministic transition system whose configurations are described by
finitely many bounded registers, each updated from a bounded list of
registers of the previous configuration, has a CNF tableau: one register
constraint per time step and register. `satisfiable_iff` identifies
satisfiability of the tableau with the existence of an allowed initial
configuration that the padded run carries to the required final
configuration within the horizon. The initial and final constraints are
supplied together with their register characterizations. These are
semantic results; no machine-runtime claim is made.
-/

namespace LeanNPHardness.Tableau

open CNF CNF.Constraint

/-- A deterministic transition system with `count` registers of `width` bits,
each updated from a bounded list of previous registers. `Inv` is a
time-indexed invariant valid up to the `horizon`; `Bounded` configurations
are determined by their register values. -/
structure LocalSystem (C : Type) where
  step : C → C
  width : ℕ
  count : ℕ
  horizon : ℕ
  value : C → ℕ → ℕ
  deps : ℕ → List ℕ
  update : ℕ → List ℕ → ℕ
  Inv : ℕ → C → Prop
  Bounded : C → Prop
  inv_step : ∀ t c, t < horizon → Inv t c → Inv (t + 1) (step c)
  inv_bounded : ∀ t c, t ≤ horizon → Inv t c → Bounded c
  value_lt : ∀ c g, Bounded c → g < count → value c g < 2 ^ width
  deps_lt : ∀ g, g < count → ∀ d ∈ deps g, d < count
  local_step : ∀ t c, t < horizon → Inv t c → ∀ g, g < count →
    value (step c) g = update g ((deps g).map (value c))
  value_injective : ∀ c c', Bounded c → Bounded c' →
    (∀ g, g < count → value c g = value c' g) → c = c'

namespace LocalSystem

variable {C : Type} (S : LocalSystem C)

/-- The register index of register `g` at time `t`. -/
def regIndex (t g : ℕ) : ℕ := t * S.count + g

theorem regIndex_div (hcount : 0 < S.count) (t g : ℕ) (hg : g < S.count) :
    S.regIndex t g / S.count = t := by
  simp only [regIndex]
  rw [Nat.mul_comm, Nat.mul_add_div hcount, Nat.div_eq_of_lt hg, Nat.add_zero]

theorem regIndex_mod (t g : ℕ) (hg : g < S.count) :
    S.regIndex t g % S.count = g := by
  simp only [regIndex]
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hg]

/-- The value of register `g` at time `t` read from an assignment. -/
def row (a : Assignment ℕ) (t g : ℕ) : ℕ :=
  readRegister S.width a (S.regIndex t g)

/-- The last listed value is the update of the preceding dependency values. -/
def transitionRelation (g : ℕ) (values : List ℕ) : Bool :=
  values.getLast? == some (S.update g values.dropLast)

/-- One register constraint per time step and register. -/
def transitionCNF : Formula ℕ :=
  (List.range S.horizon).flatMap fun t => (List.range S.count).flatMap fun g =>
    registerCNF S.width ((S.deps g).map (S.regIndex t) ++ [S.regIndex (t + 1) g])
      (S.transitionRelation g)

theorem eval_transitionCNF_eq_true_iff (a : Assignment ℕ) :
    Formula.eval a S.transitionCNF = true ↔
      ∀ t < S.horizon, ∀ g < S.count,
        S.row a (t + 1) g = S.update g ((S.deps g).map (S.row a t)) := by
  simp only [transitionCNF, eval_flatMap_eq_true_iff, List.mem_range,
    eval_registerCNF_eq_true_iff, transitionRelation, List.map_append, List.map_map,
    List.map_cons, List.map_nil, List.getLast?_concat, List.dropLast_concat,
    beq_iff_eq, Option.some.injEq, row, Function.comp_def]
  exact Iff.rfl

theorem inv_iterate (c : C) (hc : S.Inv 0 c) :
    ∀ t, t ≤ S.horizon → S.Inv t (S.step^[t] c) := by
  intro t
  induction t with
  | zero => intro _; simpa using hc
  | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply']
      exact S.inv_step t _ (by omega) (ih (by omega))

/-- Rows satisfying the initial and transition constraints follow the run. -/
theorem row_eq_value (a : Assignment ℕ) (c : C) (hc : S.Inv 0 c)
    (hinit : ∀ g < S.count, S.row a 0 g = S.value c g)
    (htrans : ∀ t < S.horizon, ∀ g < S.count,
      S.row a (t + 1) g = S.update g ((S.deps g).map (S.row a t))) :
    ∀ t, t ≤ S.horizon → ∀ g < S.count, S.row a t g = S.value (S.step^[t] c) g := by
  intro t
  induction t with
  | zero => intro _ g hg; simpa using hinit g hg
  | succ t ih =>
      intro ht g hg
      rw [htrans t (by omega) g hg, Function.iterate_succ_apply',
        S.local_step t _ (by omega) (S.inv_iterate c hc t (by omega)) g hg]
      congr 1
      apply List.map_congr_left
      intro d hd
      exact ih (by omega) d (S.deps_lt g hg d hd)

/-- The canonical assignment writing the register values of a run. -/
noncomputable def runAssignment (c : C) : Assignment ℕ := fun n =>
  natBit (S.value (S.step^[n / S.width / S.count] c) (n / S.width % S.count))
    (n % S.width)

theorem row_runAssignment (hw : 0 < S.width) (hcount : 0 < S.count) (c : C)
    (hc : S.Inv 0 c) (t : ℕ) (ht : t ≤ S.horizon) (g : ℕ) (hg : g < S.count) :
    S.row (S.runAssignment c) t g = S.value (S.step^[t] c) g := by
  unfold row runAssignment
  have key := readRegister_of_natBit S.width hw
    (fun r => S.value (S.step^[r / S.count] c) (r % S.count)) _ (fun n => rfl)
    (S.regIndex t g) (by
      simp only [S.regIndex_div hcount t g hg, S.regIndex_mod t g hg]
      exact S.value_lt _ g (S.inv_bounded t _ ht (S.inv_iterate c hc t ht)) hg)
  rw [key]
  simp only [S.regIndex_div hcount t g hg, S.regIndex_mod t g hg]

/-- The tableau is satisfiable exactly when some allowed initial configuration
reaches the required final configuration after `horizon` padded steps. -/
theorem satisfiable_iff (hw : 0 < S.width) (hcount : 0 < S.count)
    (initial : C → Prop) (final : C) (initCNF finalCNF : Formula ℕ)
    (hinitInv : ∀ c, initial c → S.Inv 0 c)
    (hfinal : S.Bounded final)
    (hinitCNF : ∀ a, Formula.eval a initCNF = true ↔
      ∃ c, initial c ∧ ∀ g < S.count, S.row a 0 g = S.value c g)
    (hfinalCNF : ∀ a, Formula.eval a finalCNF = true ↔
      ∀ g < S.count, S.row a S.horizon g = S.value final g) :
    (initCNF ++ S.transitionCNF ++ finalCNF).Satisfiable ↔
      ∃ c, initial c ∧ S.step^[S.horizon] c = final := by
  rw [Formula.satisfiable_iff_exists_eval]
  constructor
  · rintro ⟨a, ha⟩
    rw [eval_append_eq_true_iff, eval_append_eq_true_iff] at ha
    obtain ⟨⟨hinit, htrans⟩, hfin⟩ := ha
    obtain ⟨c, hc, hrow⟩ := (hinitCNF a).1 hinit
    rw [eval_transitionCNF_eq_true_iff] at htrans
    rw [hfinalCNF] at hfin
    refine ⟨c, hc, ?_⟩
    apply S.value_injective _ _
      (S.inv_bounded _ _ le_rfl (S.inv_iterate c (hinitInv c hc) _ le_rfl)) hfinal
    intro g hg
    rw [← S.row_eq_value a c (hinitInv c hc) hrow htrans S.horizon le_rfl g hg, hfin g hg]
  · rintro ⟨c, hc, hrun⟩
    refine ⟨S.runAssignment c, ?_⟩
    rw [eval_append_eq_true_iff, eval_append_eq_true_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (hinitCNF _).2 ⟨c, hc, fun g hg => by
        simpa using S.row_runAssignment hw hcount c (hinitInv c hc) 0 (Nat.zero_le _) g hg⟩
    · rw [eval_transitionCNF_eq_true_iff]
      intro t ht g hg
      rw [S.row_runAssignment hw hcount c (hinitInv c hc) (t + 1) ht g hg,
        Function.iterate_succ_apply',
        S.local_step t _ ht (S.inv_iterate c (hinitInv c hc) t (by omega)) g hg]
      congr 1
      apply List.map_congr_left
      intro d hd
      exact (S.row_runAssignment hw hcount c (hinitInv c hc) t (by omega) d
        (S.deps_lt g hg d hd)).symm
    · rw [hfinalCNF]
      intro g hg
      rw [S.row_runAssignment hw hcount c (hinitInv c hc) S.horizon le_rfl g hg, hrun]

theorem transitionCNF_length_le (bound : ℕ) (hdeps : ∀ g < S.count, (S.deps g).length ≤ bound) :
    S.transitionCNF.length ≤ S.horizon * (S.count * 2 ^ (S.width * (bound + 1))) := by
  simp only [transitionCNF, List.length_flatMap]
  have inner : ∀ t, ((List.range S.count).map fun g =>
      (registerCNF S.width ((S.deps g).map (S.regIndex t) ++ [S.regIndex (t + 1) g])
        (S.transitionRelation g)).length).sum ≤ S.count * 2 ^ (S.width * (bound + 1)) := by
    intro t
    calc ((List.range S.count).map fun g =>
          (registerCNF S.width ((S.deps g).map (S.regIndex t) ++ [S.regIndex (t + 1) g])
            (S.transitionRelation g)).length).sum
        ≤ ((List.range S.count).map fun _ => 2 ^ (S.width * (bound + 1))).sum := by
          apply List.sum_le_sum
          intro g hg
          refine (registerCNF_length_le _ _ _).trans ?_
          apply Nat.pow_le_pow_right (by omega)
          apply Nat.mul_le_mul_left
          simp only [List.length_append, List.length_map, List.length_singleton]
          exact Nat.add_le_add_right (hdeps g (List.mem_range.mp hg)) 1
      _ = S.count * 2 ^ (S.width * (bound + 1)) := by simp
  calc ((List.range S.horizon).map fun t => ((List.range S.count).map fun g =>
        (registerCNF S.width ((S.deps g).map (S.regIndex t) ++ [S.regIndex (t + 1) g])
          (S.transitionRelation g)).length).sum).sum
      ≤ ((List.range S.horizon).map fun _ => S.count * 2 ^ (S.width * (bound + 1))).sum := by
        apply List.sum_le_sum
        intro t _
        exact inner t
    _ = S.horizon * (S.count * 2 ^ (S.width * (bound + 1))) := by simp

end LocalSystem

end LeanNPHardness.Tableau
