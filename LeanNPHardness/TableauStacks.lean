import LeanNPHardness.TableauJobs
import LeanNPHardness.MachineRoutinePrimitives

/-!
# The stack family of the Cook--Levin generator

Work stacks hold unary CNF symbols (marks for counters and registers, and
the rendered output), the job and skeleton stacks hold instructions, and
three stacks hold the problem input and its copies. All routines of the
generator are written over this family.
-/

namespace LeanNPHardness.TableauStacks

open CNF.Unary TableauJobs

/-- Counters materialized as unary strings and their loop copies. -/
inductive Counter
  | n
  | q
  | m
  | t
  | tpb
  | g
  | tmp
  | bc
  | copy1
  | copy2
  | copy3
  deriving DecidableEq, Fintype, Repr

/-- Work stacks over the unary CNF alphabet. -/
inductive WorkName
  | output
  | buf
  | scratch
  | reg (r : RegName)
  | cnt (c : Counter)
  deriving DecidableEq, Fintype, Repr

/-- All stacks of the generator. -/
inductive GStack
  | input
  | xkeep
  | xscr
  | job
  | skel
  | work (w : WorkName)
  deriving DecidableEq, Fintype, Repr

/-- The alphabet family; `Γx` is the problem's input alphabet. -/
abbrev GAlphabet (Γx : Type) : GStack → Type
  | .input => Γx
  | .xkeep => Γx
  | .xscr => Γx
  | .job => Instr
  | .skel => Instr
  | .work _ => Sym

instance (Γx : Type) [Fintype Γx] : ∀ k, Fintype (GAlphabet Γx k)
  | .input => inferInstanceAs (Fintype Γx)
  | .xkeep => inferInstanceAs (Fintype Γx)
  | .xscr => inferInstanceAs (Fintype Γx)
  | .job => inferInstanceAs (Fintype Instr)
  | .skel => inferInstanceAs (Fintype Instr)
  | .work _ => inferInstanceAs (Fintype Sym)

instance (Γx : Type) [DecidableEq Γx] : ∀ k, DecidableEq (GAlphabet Γx k)
  | .input => inferInstanceAs (DecidableEq Γx)
  | .xkeep => inferInstanceAs (DecidableEq Γx)
  | .xscr => inferInstanceAs (DecidableEq Γx)
  | .job => inferInstanceAs (DecidableEq Instr)
  | .skel => inferInstanceAs (DecidableEq Instr)
  | .work _ => inferInstanceAs (DecidableEq Sym)

/-- A unary string of marks. -/
def marks (n : ℕ) : List Sym := List.replicate n .mark

@[simp]
theorem marks_length (n : ℕ) : (marks n).length = n := by simp [marks]

@[simp]
theorem marks_zero : marks 0 = [] := rfl

theorem marks_append (m n : ℕ) : marks (m + n) = marks m ++ marks n := by
  unfold marks
  exact List.replicate_add m n _

end LeanNPHardness.TableauStacks
