import LeanNPHardness.MachineRoutineUnary

/-!
# The job interpreter machine

A loop pops instructions from the job stack and dispatches: literal
polarities, marks, and clause ends are pushed on the buffer; register
instructions copy a register's marks onto the buffer or onto another
register, or drain a register. `interpret_exits` proves that executing a
job leaves the reversed rendering on the buffer and the updated registers
on their stacks, with an exact step count.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary TableauJobs

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx]

/-- The stack holding register `r`. -/
abbrev regStack (r : RegName) : GStack := .work (.reg r)

/-- The routine for one instruction. -/
def instrHandler : Instr → GRoutine Γx
  | .lit true => pushList (.work .buf) [.pos]
  | .lit false => pushList (.work .buf) [.neg]
  | .reg r => copyWork (.reg r) .buf .scratch
  | .mark => pushList (.work .buf) [.mark]
  | .endClause => pushList (.work .buf) [.endClause]
  | .addTo d s => copyWork (.reg s) (.reg d) .scratch
  | .clear r => drain (.work (.reg r))

/-- Execute the whole job stack. -/
def interpret : GRoutine Γx := loop .job (dispatch .job instrHandler)

/-- Steps of one handler. -/
def instrCost (R : Regs) : Instr → ℕ
  | .lit _ => 1
  | .reg r => 4 * R r + 2
  | .mark => 1
  | .endClause => 1
  | .addTo _ s => 4 * R s + 2
  | .clear r => 2 * R r + 1

/-- The stacks during interpretation: job, buffer, and registers are
explicit; every other stack is taken from `S`. -/
def interpStacks (S : Stacks (GAlphabet Γx)) (J : List Instr) (B : List Sym) (R : Regs) :
    Stacks (GAlphabet Γx)
  | .job => J
  | .work .buf => B
  | .work (.reg r) => marks (R r)
  | .input => S .input
  | .xkeep => S .xkeep
  | .xscr => S .xscr
  | .skel => S .skel
  | .work .output => S (.work .output)
  | .work .scratch => S (.work .scratch)
  | .work (.cnt c) => S (.work (.cnt c))

@[simp] theorem interpStacks_job (S : Stacks (GAlphabet Γx)) (J B R) :
    interpStacks S J B R .job = J := rfl
@[simp] theorem interpStacks_buf (S : Stacks (GAlphabet Γx)) (J B R) :
    interpStacks S J B R (.work .buf) = B := rfl
@[simp] theorem interpStacks_reg (S : Stacks (GAlphabet Γx)) (J B R) (r : RegName) :
    interpStacks S J B R (.work (.reg r)) = marks (R r) := rfl
@[simp] theorem interpStacks_scratch (S : Stacks (GAlphabet Γx)) (J B R) :
    interpStacks S J B R (.work .scratch) = S (.work .scratch) := rfl

theorem interpStacks_update_job (S : Stacks (GAlphabet Γx)) (J J' B R) :
    Function.update (interpStacks S J B R) .job J' = interpStacks S J' B R := by
  funext k
  cases k with
  | work w => cases w <;> rfl
  | _ => first | rfl | simp [interpStacks]

theorem interpStacks_update_buf (S : Stacks (GAlphabet Γx)) (J B B' R) :
    Function.update (interpStacks S J B R) (.work .buf) B' = interpStacks S J B' R := by
  funext k
  cases k with
  | work w => cases w <;> first | rfl | simp [interpStacks]
  | _ => first | rfl | simp [interpStacks]

theorem interpStacks_update_reg (S : Stacks (GAlphabet Γx)) (J B R) (r : RegName) (n : ℕ) :
    Function.update (interpStacks S J B R) (.work (.reg r)) (marks n) =
      interpStacks S J B (Function.update R r n) := by
  funext k
  cases k with
  | work w =>
      cases w with
      | reg r' =>
          by_cases h : r' = r
          · subst h; simp [interpStacks]
          · have hne : GStack.work (WorkName.reg r') ≠ GStack.work (WorkName.reg r) :=
              fun e => h (WorkName.reg.inj (GStack.work.inj e))
            rw [Function.update_of_ne hne, interpStacks_reg, interpStacks_reg,
              Function.update_of_ne h]
      | _ => first | rfl | simp [interpStacks]
  | _ => first | rfl | simp [interpStacks]

/-- One handler renders its instruction onto the buffer (reversed) and
updates the registers. -/
theorem instrHandler_exits (S : Stacks (GAlphabet Γx)) (hscr : S (.work .scratch) = [])
    (J : List Instr) (B : List Sym) (R : Regs) (i : Instr) (hi : i.ok) :
    (instrHandler (Γx := Γx) i).Exits (interpStacks S J B R) (instrCost R i)
      (interpStacks S J ((renderInstr R i).1.reverse ++ B) (renderInstr R i).2) := by
  cases i with
  | lit p =>
      cases p
      · have := pushList_exits (Γ := GAlphabet Γx) (.work .buf) [.neg] (interpStacks S J B R)
        rw [interpStacks_buf, interpStacks_update_buf] at this
        simpa [instrHandler, instrCost, renderInstr] using this
      · have := pushList_exits (Γ := GAlphabet Γx) (.work .buf) [.pos] (interpStacks S J B R)
        rw [interpStacks_buf, interpStacks_update_buf] at this
        simpa [instrHandler, instrCost, renderInstr] using this
  | reg r =>
      have := copyWork_exits (Γx := Γx) (.reg r) .buf .scratch (by simp) (by simp) (by simp)
        (interpStacks S J B R) (by simpa using hscr)
      rw [interpStacks_reg, interpStacks_buf, interpStacks_update_buf, marks_length] at this
      simpa [instrHandler, instrCost, renderInstr, marks, List.reverse_replicate] using this
  | mark =>
      have := pushList_exits (Γ := GAlphabet Γx) (.work .buf) [.mark] (interpStacks S J B R)
      rw [interpStacks_buf, interpStacks_update_buf] at this
      simpa [instrHandler, instrCost, renderInstr] using this
  | endClause =>
      have := pushList_exits (Γ := GAlphabet Γx) (.work .buf) [.endClause] (interpStacks S J B R)
      rw [interpStacks_buf, interpStacks_update_buf] at this
      simpa [instrHandler, instrCost, renderInstr] using this
  | addTo d s =>
      have hds : d ≠ s := hi
      have := copyWork_exits (Γx := Γx) (.reg s) (.reg d) .scratch (by simpa using hds.symm)
        (by simp) (by simp) (interpStacks S J B R) (by simpa using hscr)
      rw [interpStacks_reg, interpStacks_reg, marks_length, ← marks_append,
        Nat.add_comm (R s) (R d), interpStacks_update_reg] at this
      simpa [instrHandler, instrCost, renderInstr] using this
  | clear r =>
      have := drain_exits (Γ := GAlphabet Γx) (.work (.reg r)) (interpStacks S J B R)
      rw [interpStacks_reg, marks_length, show ([] : List Sym) = marks 0 from rfl,
        interpStacks_update_reg] at this
      simpa [instrHandler, instrCost, renderInstr] using this

/-- Steps of interpreting a job: one pop per instruction, one test per
iteration and the final test. -/
def interpSteps (R : Regs) : List Instr → ℕ
  | [] => 1
  | i :: J => instrCost R i + 1 + 1 + interpSteps (renderInstr R i).2 J

theorem render_take_succ (R : Regs) (J : List Instr) (i : ℕ) (hi : i < J.length) :
    render R (J.take (i + 1)) =
      ((render R (J.take i)).1 ++ (renderInstr (render R (J.take i)).2 (J[i]'hi)).1,
        (renderInstr (render R (J.take i)).2 (J[i]'hi)).2) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, render_append]
  simp [render]

private theorem loopSteps_interp (R : Regs) (J : List Instr) :
    loopSteps (fun i => instrCost (render R (J.take i)).2 (J[i]?.getD .mark) + 1) J.length =
      interpSteps R J := by
  induction J generalizing R with
  | nil => rfl
  | cons i J ih =>
      have hfun : (fun j => instrCost (render R ((i :: J).take (j + 1))).2
          ((i :: J)[j + 1]?.getD .mark) + 1) =
          fun j => instrCost (render (renderInstr R i).2 (J.take j)).2 (J[j]?.getD .mark) + 1 := by
        funext j
        simp [List.take_succ_cons, render]
      simp only [List.length_cons, loopSteps, interpSteps]
      rw [hfun, ih]
      simp [render]

/-- Interpreting a job pushes its reversed rendering on the buffer and
leaves the updated registers; the job stack ends empty. -/
theorem interpret_exits (S : Stacks (GAlphabet Γx)) (hscr : S (.work .scratch) = [])
    (J : List Instr) (hJ : ∀ i ∈ J, i.ok) (B : List Sym) (R : Regs) :
    (interpret (Γx := Γx)).Exits (interpStacks S J B R) (interpSteps R J)
      (interpStacks S [] ((render R J).1.reverse ++ B) (render R J).2) := by
  have key := loop_exits (Γ := GAlphabet Γx) .job (dispatch .job instrHandler) J.length
    (fun i => interpStacks S (J.drop i) ((render R (J.take i)).1.reverse ++ B) (render R (J.take i)).2)
    (fun i => instrCost (render R (J.take i)).2 (J[i]?.getD .mark) + 1) ?_ ?_ ?_
  · rw [loopSteps_interp] at key
    simpa using! key
  · intro i hi
    have hsplit : J.drop i = J[i] :: J.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hdrop : (interpStacks S (J.drop i) ((render R (J.take i)).1.reverse ++ B)
        (render R (J.take i)).2) .job = J[i] :: J.drop (i + 1) := by simpa using hsplit
    have handler := instrHandler_exits S hscr (J.drop (i + 1))
      ((render R (J.take i)).1.reverse ++ B) (render R (J.take i)).2 (J[i])
      (hJ _ (List.getElem_mem hi))
    rw [← interpStacks_update_job] at handler
    have := dispatch_exits (Γ := GAlphabet Γx) .job instrHandler _ _ _ hdrop handler
    rw [List.getElem?_eq_getElem hi, Option.getD_some, render_take_succ R J i hi]
    simpa [List.reverse_append, List.append_assoc] using this
  · intro i hi
    simp [List.drop_eq_nil_iff, hi]
  · simp

end LeanNPHardness.TableauStacks
