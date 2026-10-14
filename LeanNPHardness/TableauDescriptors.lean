import LeanNPHardness.TableauJobs
import LeanNPHardness.CNFRegisterConstraint

/-!
# Descriptors of relation and register constraints

A group reference names the slot base of a register as a sum of named unary
registers plus a constant. `relationDesc` and `registerDesc` describe the
clauses of `relationCNF` and `registerCNF` with variables given by such
references; `formulaOf_registerDesc` proves that evaluating the descriptor
at register values whose references hit the intended register bases yields
exactly the register constraint. `fixDesc` describes `fixRegister`.
-/

namespace LeanNPHardness.TableauJobs

open CNF CNF.Constraint

/-- A slot reference: the sum of the named registers plus a constant. -/
abbrev SlotRef := List RegName × ℕ

/-- The value of a slot reference. -/
def SlotRef.eval (R : Regs) (ref : SlotRef) : ℕ := (ref.1.map R).sum + ref.2

/-- The literal descriptor forbidding value `a` at a slot. -/
def forbidLit (ref : SlotRef) (a : Bool) : LitDesc := ⟨!a, ref.1, ref.2⟩

theorem litOf_forbidLit (R : Regs) (ref : SlotRef) (a : Bool) :
    litOf R (forbidLit ref a) =
      if a then Literal.negative (ref.eval R) else Literal.positive (ref.eval R) := by
  cases a <;> simp [litOf, forbidLit, litValue, SlotRef.eval]

/-- The clause descriptor forbidding an assignment of listed slots. -/
def forbidDesc (refs : List SlotRef) (α : List Bool) : ClauseDesc :=
  (refs.zip α).map fun p => forbidLit p.1 p.2

theorem clauseOf_forbidDesc (R : Regs) (refs : List SlotRef) (α : List Bool) :
    clauseOf R (forbidDesc refs α) = forbidClause (refs.map (SlotRef.eval R)) α := by
  induction refs generalizing α with
  | nil => simp [forbidDesc, clauseOf, forbidClause]
  | cons ref refs ih =>
      cases α with
      | nil => simp [forbidDesc, clauseOf, forbidClause]
      | cons a α =>
          simp only [forbidDesc, List.zip_cons_cons, List.map_cons, clauseOf, litOf_forbidLit,
            forbidClause]
          rw [← ih α]
          rfl

/-- The descriptor of `relationCNF` on the listed slots. -/
def relationDesc (refs : List SlotRef) (Rel : List Bool → Bool) : FormulaDesc :=
  ((allAssignments refs.length).filter fun α => !Rel α).map (forbidDesc refs)

theorem formulaOf_relationDesc (R : Regs) (refs : List SlotRef) (Rel : List Bool → Bool) :
    formulaOf R (relationDesc refs Rel) = relationCNF (refs.map (SlotRef.eval R)) Rel := by
  simp only [relationDesc, relationCNF, formulaOf, List.map_map, List.length_map]
  apply List.map_congr_left
  intro α _
  exact clauseOf_forbidDesc R refs α

/-- A group reference: the slot base of a register. -/
abbrev GroupRef := List RegName × ℕ

/-- The value of a group reference: the intended slot base. -/
def GroupRef.eval (R : Regs) (g : GroupRef) : ℕ := (g.1.map R).sum + g.2

/-- The references of the `w` bits of a group. -/
def GroupRef.bitRefs (w : ℕ) (g : GroupRef) : List SlotRef :=
  (List.range w).map fun b => (g.1, g.2 + b)

theorem GroupRef.bitRefs_map_eval (R : Regs) (w : ℕ) (g : GroupRef) :
    (g.bitRefs w).map (SlotRef.eval R) = (List.range w).map fun b => g.eval R + b := by
  simp [GroupRef.bitRefs, SlotRef.eval, GroupRef.eval, List.map_map, Function.comp_def,
    Nat.add_assoc]

/-- The descriptor of `registerCNF` on the listed groups. -/
def registerDesc (w : ℕ) (groups : List GroupRef) (Rel : List ℕ → Bool) : FormulaDesc :=
  relationDesc (groups.flatMap (GroupRef.bitRefs w)) fun bits =>
    Rel ((chunks w groups.length bits).map bitsToNat)

/-- Evaluating a register descriptor whose group references hit the slot
bases of the registers `gs` gives exactly the register constraint on `gs`. -/
theorem formulaOf_registerDesc (R : Regs) (w : ℕ) (groups : List GroupRef) (gs : List ℕ)
    (Rel : List ℕ → Bool) (h : groups.map (GroupRef.eval R) = gs.map (· * w)) :
    formulaOf R (registerDesc w groups Rel) = registerCNF w gs Rel := by
  have hlen : groups.length = gs.length := by
    have := congrArg List.length h
    simpa using this
  simp only [registerDesc, registerCNF, formulaOf_relationDesc, hlen]
  congr 1
  rw [List.map_flatMap]
  simp only [GroupRef.bitRefs_map_eval]
  have : ∀ (groups : List GroupRef) (gs : List ℕ), groups.map (GroupRef.eval R) = gs.map (· * w) →
      (groups.flatMap fun g => (List.range w).map fun b => g.eval R + b) =
        gs.flatMap (registerSlots w) := by
    intro groups gs h
    induction groups generalizing gs with
    | nil => cases gs <;> simp_all
    | cons g groups ih =>
        cases gs with
        | nil => simp at h
        | cons x gs =>
            simp only [List.map_cons, List.cons.injEq] at h
            simp only [List.flatMap_cons, ih gs h.2, registerSlots, h.1]
  exact this groups gs h

/-- The descriptor fixing one group to a value. -/
def fixDesc (w : ℕ) (g : GroupRef) (m : ℕ) : FormulaDesc :=
  registerDesc w [g] fun values => values == [m]

theorem formulaOf_fixDesc (R : Regs) (w : ℕ) (g : GroupRef) (x m : ℕ) (h : g.eval R = x * w) :
    formulaOf R (fixDesc w g m) = fixRegister w x m := by
  rw [fixDesc, fixRegister]
  exact formulaOf_registerDesc R w [g] [x] _ (by simp [h])

end LeanNPHardness.TableauJobs
