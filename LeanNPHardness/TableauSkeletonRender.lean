import LeanNPHardness.TableauDescriptors

/-!
# Rendering the skeleton's control instructions

The skeleton of the Cook--Levin tableau is a job: rounds that reset the
window register, render the head and cell descriptors, advancing the window
register by one register width per cell, and finally move the base register
to the next round. These lemmas compute the rendering of each control piece
and of a cells loop, in terms of `cellsFormula`, the formula obtained by
evaluating successive descriptors at successively advanced registers.
-/

namespace LeanNPHardness.TableauJobs

open CNF CNF.Unary

/-- Reset the window register to the base plus two widths. -/
def roundStart : List Instr := [.clear .win, .addTo .win .base, .addTo .win .w, .addTo .win .w]

/-- Advance the window register by one width. -/
def cellStep : List Instr := [.addTo .win .w]

/-- Move the base register to the window register plus `D` widths. -/
def roundEnd (D : ℕ) : List Instr :=
  [.clear .base, .addTo .base .win] ++ List.replicate D (.addTo .base .w)

/-- Advance the window register by `n` widths. -/
def advance (R : Regs) (n : ℕ) : Regs := Function.update R .win (R .win + n * R .w)

@[simp] theorem advance_win (R : Regs) (n : ℕ) : advance R n .win = R .win + n * R .w := by
  simp [advance]
@[simp] theorem advance_base (R : Regs) (n : ℕ) : advance R n .base = R .base := by
  simp [advance, Function.update_of_ne]
@[simp] theorem advance_w (R : Regs) (n : ℕ) : advance R n .w = R .w := by
  simp [advance, Function.update_of_ne]
@[simp] theorem advance_pw (R : Regs) (n : ℕ) : advance R n .pw = R .pw := by
  simp [advance, Function.update_of_ne]

theorem advance_zero (R : Regs) : advance R 0 = R := by
  simp [advance]

theorem advance_advance (R : Regs) (m n : ℕ) : advance (advance R m) n = advance R (m + n) := by
  funext r
  cases r <;> simp [advance, Function.update_of_ne, Nat.add_mul, Nat.add_assoc]

theorem render_roundStart (R : Regs) :
    render R roundStart = ([], Function.update R .win (R .base + 2 * R .w)) := by
  simp only [roundStart, render, renderInstr, List.nil_append]
  congr 1
  funext r
  cases r <;> simp [Function.update_of_ne]
  omega

theorem render_cellStep (R : Regs) : render R cellStep = ([], advance R 1) := by
  simp [cellStep, render, renderInstr, advance]

theorem render_replicate_addTo (R : Regs) (n : ℕ) :
    render R (List.replicate n (.addTo .base .w)) =
      ([], Function.update R .base (R .base + n * R .w)) := by
  induction n generalizing R with
  | zero => simp [render]
  | succ n ih =>
      rw [List.replicate_succ, render]
      simp only [renderInstr, ih]
      simp only [List.nil_append, Function.update_self, Function.update_idem,
        Function.update_of_ne (show RegName.w ≠ RegName.base by decide)]
      congr 2
      rw [Nat.succ_mul]
      omega

theorem render_roundEnd (R : Regs) (D : ℕ) :
    render R (roundEnd D) = ([], Function.update R .base (R .win + D * R .w)) := by
  simp only [roundEnd, render_append, render, renderInstr, render_replicate_addTo]
  simp [Function.update_of_ne]

/-- The formula of a cells loop: each descriptor is evaluated after the
previous ones have advanced the window register. -/
def cellsFormula (R : Regs) : List FormulaDesc → Formula ℕ
  | [] => []
  | d :: ds => formulaOf R d ++ cellsFormula (advance R 1) ds

theorem cellsFormula_append (R : Regs) (ds es : List FormulaDesc) :
    cellsFormula R (ds ++ es) = cellsFormula R ds ++ cellsFormula (advance R ds.length) es := by
  induction ds generalizing R with
  | nil => simp [cellsFormula, advance_zero]
  | cons d ds ih =>
      simp only [List.cons_append, cellsFormula, ih, advance_advance, List.length_cons,
        List.append_assoc, Nat.add_comm]

theorem cellsFormula_map_range (R : Regs) (f : ℕ → FormulaDesc) (n : ℕ) :
    cellsFormula R ((List.range n).map f) =
      (List.range n).flatMap fun i => formulaOf (advance R i) (f i) := by
  induction n generalizing R f with
  | zero => simp [cellsFormula]
  | succ n ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, cellsFormula, ih, List.flatMap_cons]
      simp [advance_zero, advance_advance, List.flatMap_map, Function.comp_def, Nat.add_comm]

/-- The job rendering the descriptors with a cell step after each. -/
def cellsJob (ds : List FormulaDesc) : List Instr :=
  ds.flatMap fun d => formulaJob d ++ cellStep

theorem render_cellsJob (R : Regs) (ds : List FormulaDesc) :
    render R (cellsJob ds) = (encode (cellsFormula R ds), advance R ds.length) := by
  induction ds generalizing R with
  | nil => simp [cellsJob, render, cellsFormula, advance_zero]
  | cons d ds ih =>
      simp only [cellsJob, List.flatMap_cons, render_append, render_formulaJob, render_cellStep]
      rw [← cellsJob, ih]
      simp [cellsFormula, encode_append, advance_advance, Nat.add_comm]

end LeanNPHardness.TableauJobs
