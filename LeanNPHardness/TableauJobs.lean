import LeanNPHardness.UnaryCNF

/-!
# Jobs: a straight-line language rendering unary CNF

A job is a list of instructions read by a fixed interpreter: start a literal,
append the value of a named unary register or one mark to the current
variable index, end a clause, or update a register. Literal and clause
descriptors give jobs whose rendering is exactly the unary encoding of the
described clauses (`render_formulaJob`). The Cook--Levin skeleton is a job;
the interpreter machine executes jobs with the registers held on stacks.
-/

namespace LeanNPHardness.TableauJobs

open CNF CNF.Unary

/-- Named unary registers. -/
inductive RegName
  | base
  | cur
  | w
  | pw
  deriving DecidableEq, Fintype, Repr

/-- Job instructions. -/
inductive Instr
  | lit (positive : Bool)
  | reg (r : RegName)
  | mark
  | endClause
  | addTo (dst src : RegName)
  | clear (r : RegName)
  deriving DecidableEq, Fintype, Repr

/-- Instructions the interpreter handles as specified: register additions
must use distinct registers. -/
def Instr.ok : Instr → Prop
  | .addTo d s => d ≠ s
  | _ => True

/-- Register values. -/
abbrev Regs := RegName → ℕ

/-- Symbols rendered by one instruction, and the resulting registers. -/
def renderInstr (R : Regs) : Instr → List Sym × Regs
  | .lit true => ([.pos], R)
  | .lit false => ([.neg], R)
  | .reg r => (List.replicate (R r) .mark, R)
  | .mark => ([.mark], R)
  | .endClause => ([.endClause], R)
  | .addTo d s => ([], Function.update R d (R d + R s))
  | .clear r => ([], Function.update R r 0)

/-- Render a job from given registers. -/
def render (R : Regs) : List Instr → List Sym × Regs
  | [] => ([], R)
  | i :: job =>
      let first := renderInstr R i
      let rest := render first.2 job
      (first.1 ++ rest.1, rest.2)

theorem render_append (R : Regs) (left right : List Instr) :
    render R (left ++ right) =
      ((render R left).1 ++ (render (render R left).2 right).1,
        (render (render R left).2 right).2) := by
  induction left generalizing R with
  | nil => simp [render]
  | cons i left ih =>
      simp only [List.cons_append, render, ih, List.append_assoc]

/-! ### Descriptors -/

/-- A literal whose variable is the sum of listed registers plus a constant. -/
structure LitDesc where
  positive : Bool
  regs : List RegName
  const : ℕ
  deriving DecidableEq, Repr

/-- A clause descriptor. -/
abbrev ClauseDesc := List LitDesc

/-- A formula descriptor. -/
abbrev FormulaDesc := List ClauseDesc

def litJob (d : LitDesc) : List Instr :=
  .lit d.positive :: (d.regs.map Instr.reg ++ List.replicate d.const .mark)

def clauseJob (c : ClauseDesc) : List Instr :=
  c.flatMap litJob ++ [.endClause]

def formulaJob (f : FormulaDesc) : List Instr :=
  f.flatMap clauseJob

/-- The variable described. -/
def litValue (R : Regs) (d : LitDesc) : ℕ :=
  (d.regs.map R).sum + d.const

def litOf (R : Regs) (d : LitDesc) : Literal ℕ :=
  if d.positive then .positive (litValue R d) else .negative (litValue R d)

def clauseOf (R : Regs) (c : ClauseDesc) : Clause ℕ := c.map (litOf R)

def formulaOf (R : Regs) (f : FormulaDesc) : Formula ℕ := f.map (clauseOf R)

theorem render_regs (R : Regs) (regs : List RegName) :
    render R (regs.map Instr.reg) = (List.replicate (regs.map R).sum .mark, R) := by
  induction regs with
  | nil => simp [render]
  | cons r regs ih =>
      rw [List.map_cons, render]
      simp only [renderInstr]
      rw [ih]
      simp

theorem render_marks (R : Regs) (n : ℕ) :
    render R (List.replicate n .mark) = (List.replicate n .mark, R) := by
  induction n with
  | zero => simp [render]
  | succ n ih =>
      rw [List.replicate_succ, render]
      simp only [renderInstr]
      rw [ih]
      simp [List.replicate_succ]

theorem render_litJob (R : Regs) (d : LitDesc) :
    render R (litJob d) = (encodeLiteral (litOf R d), R) := by
  rw [litJob, render, render_append, render_regs]
  simp only [render_marks]
  cases hp : d.positive <;> simp [renderInstr, litOf, litValue, encodeLiteral, hp]

theorem render_clauseJob (R : Regs) (c : ClauseDesc) :
    render R (clauseJob c) = (encodeClause (clauseOf R c), R) := by
  simp only [clauseJob, render_append]
  have hlits : ∀ c : ClauseDesc, render R (c.flatMap litJob) =
      ((clauseOf R c).flatMap encodeLiteral, R) := by
    intro c
    induction c with
    | nil => simp [render, clauseOf]
    | cons d c ih =>
        rw [List.flatMap_cons, render_append, render_litJob, ih]
        simp [clauseOf]
  rw [hlits]
  simp [render, renderInstr, encodeClause]

theorem render_formulaJob (R : Regs) (f : FormulaDesc) :
    render R (formulaJob f) = (encode (formulaOf R f), R) := by
  induction f with
  | nil => simp [formulaJob, render, formulaOf, encode]
  | cons c f ih =>
      rw [formulaJob, List.flatMap_cons, render_append, render_clauseJob, ← formulaJob, ih]
      simp [formulaOf, encode_cons]

theorem render_addTo (R : Regs) (d s : RegName) :
    render R [.addTo d s] = ([], Function.update R d (R d + R s)) := by
  simp [render, renderInstr]

theorem render_clear (R : Regs) (r : RegName) :
    render R [.clear r] = ([], Function.update R r 0) := by
  simp [render, renderInstr]

end LeanNPHardness.TableauJobs
