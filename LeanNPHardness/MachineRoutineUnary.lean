import LeanNPHardness.TableauStacks

/-!
# Unary arithmetic on the generator's work stacks

Multiplication of two unary strings by repeated copying: for every mark of
the second factor (consumed from a copy), the first factor is copied onto an
accumulator. The exact step count is quadratic in the factors.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx]

/-- The routine type over the generator's stack family. -/
abbrev GRoutine (Γx : Type) := Routine (GAlphabet Γx)

theorem work_ne {a b : WorkName} (h : a ≠ b) : GStack.work a ≠ GStack.work b :=
  fun e => h (GStack.work.inj e)

/-- Copy a work stack onto another through an empty scratch stack. -/
def copyWork (src dst scr : WorkName) : GRoutine Γx :=
  copyAll (Γ := GAlphabet Γx) (.work src) (.work dst) (.work scr) id id id .mark .mark .mark

theorem copyWork_exits (src dst scr : WorkName) (hsd : src ≠ dst) (hss : src ≠ scr)
    (hds : dst ≠ scr) (S : Stacks (GAlphabet Γx)) (hscr : S (.work scr) = []) :
    (copyWork (Γx := Γx) src dst scr).Exits S (4 * (S (.work src)).length + 2)
      (Function.update S (.work dst) (S (.work src) ++ S (.work dst))) := by
  have := copyAll_exits (Γ := GAlphabet Γx) (.work src) (.work dst) (.work scr) id id id
    .mark .mark .mark (work_ne hsd) (work_ne hss) (work_ne hds) (fun _ => rfl) S hscr
  simpa [copyWork] using this

/-- Add `|a| × |b|` marks to `acc`, consuming a copy of `b` made on `bc`;
`a`, `b` are preserved and `scr`, `bc` end empty. -/
def mulInto (a b acc scr bc : WorkName) : GRoutine Γx :=
  seq (copyWork b bc scr)
    (loop (.work bc) (seq (popOne (.work bc)) (copyWork a acc scr)))

/-- Stacks after `i` multiplication iterations. -/
def mulStacks (a acc bc : WorkName) (S : Stacks (GAlphabet Γx)) (y : ℕ) (i : ℕ) :
    Stacks (GAlphabet Γx) :=
  Function.update (Function.update S (.work bc) (marks (y - i))) (.work acc)
    ((List.replicate i (S (.work a))).flatten ++ S (.work acc))

theorem mulInto_exits (a b acc scr bc : WorkName)
    (hab : a ≠ b) (haacc : a ≠ acc) (has : a ≠ scr) (habc : a ≠ bc)
    (hbacc : b ≠ acc) (hbs : b ≠ scr) (hbbc : b ≠ bc)
    (haccs : acc ≠ scr) (haccbc : acc ≠ bc) (hsbc : scr ≠ bc)
    (S : Stacks (GAlphabet Γx)) (y : ℕ) (hb : S (.work b) = marks y)
    (hscr : S (.work scr) = []) (hbc : S (.work bc) = []) :
    (mulInto (Γx := Γx) a b acc scr bc).Exits S
      (4 * y + 2 + loopSteps (fun _ => 4 * (S (.work a)).length + 3) y)
      (Function.update S (.work acc) ((List.replicate y (S (.work a))).flatten ++ S (.work acc))) := by
  have first := copyWork_exits (Γx := Γx) b bc scr hbbc hbs hsbc.symm S hscr
  rw [hb, hbc, List.append_nil, marks_length] at first
  set S₁ := Function.update S (.work bc) (marks y) with hS₁
  have hS₁a : S₁ (.work a) = S (.work a) := by
    rw [hS₁, Function.update_of_ne (work_ne habc)]
  have hS₁acc : S₁ (.work acc) = S (.work acc) := by
    rw [hS₁, Function.update_of_ne (work_ne haccbc)]
  have hS₁scr : S₁ (.work scr) = [] := by
    rw [hS₁, Function.update_of_ne (work_ne hsbc), hscr]
  have hS₁bc : S₁ (.work bc) = marks y := by rw [hS₁, Function.update_self]
  have hmulbc : ∀ i, mulStacks a acc bc S₁ y i (.work bc) = marks (y - i) := by
    intro i
    simp only [mulStacks]
    rw [Function.update_of_ne (work_ne haccbc.symm), Function.update_self]
  have hmula : ∀ i, mulStacks a acc bc S₁ y i (.work a) = S (.work a) := by
    intro i
    simp only [mulStacks]
    rw [Function.update_of_ne (work_ne haacc), Function.update_of_ne (work_ne habc), hS₁a]
  have hmulscr : ∀ i, mulStacks a acc bc S₁ y i (.work scr) = [] := by
    intro i
    simp only [mulStacks]
    rw [Function.update_of_ne (work_ne haccs.symm), Function.update_of_ne (work_ne hsbc), hS₁scr]
  have hmulacc : ∀ i, mulStacks a acc bc S₁ y i (.work acc) =
      (List.replicate i (S (.work a))).flatten ++ S (.work acc) := by
    intro i
    simp only [mulStacks]
    rw [Function.update_self, hS₁a, hS₁acc]
  have body : ∀ i < y, (seq (popOne (.work bc)) (copyWork a acc scr)).Exits
      (mulStacks a acc bc S₁ y i) (4 * (S (.work a)).length + 3)
      (mulStacks a acc bc S₁ y (i + 1)) := by
    intro i hi
    have pop := popOne_exits (Γ := GAlphabet Γx) (.work bc) (mulStacks a acc bc S₁ y i)
    have htail : (mulStacks a acc bc S₁ y i (.work bc)).tail = marks (y - (i + 1)) := by
      rw [hmulbc, show y - i = (y - (i + 1)) + 1 by omega, marks, List.replicate_succ,
        List.tail_cons]
      rfl
    rw [htail] at pop
    set S₂ := Function.update (mulStacks a acc bc S₁ y i) (.work bc) (marks (y - (i + 1)))
      with hS₂
    have hS₂scr : S₂ (.work scr) = [] := by
      rw [hS₂, Function.update_of_ne (work_ne hsbc), hmulscr]
    have hS₂a : S₂ (.work a) = S (.work a) := by
      rw [hS₂, Function.update_of_ne (work_ne habc), hmula]
    have hS₂acc : S₂ (.work acc) = (List.replicate i (S (.work a))).flatten ++ S (.work acc) := by
      rw [hS₂, Function.update_of_ne (work_ne haccbc), hmulacc]
    have copy := copyWork_exits (Γx := Γx) a acc scr haacc has haccs S₂ hS₂scr
    rw [hS₂a, hS₂acc] at copy
    have combined := seq_exits _ _ pop copy
    rw [show 1 + (4 * (S (.work a)).length + 2) = 4 * (S (.work a)).length + 3 by omega] at combined
    convert combined using 1
    funext k
    simp only [S₂, mulStacks, update_apply', hS₁a, hS₁acc]
    split_ifs <;> subst_vars <;> simp_all [List.replicate_succ, List.flatten_cons]
  have hloop := loop_exits (Γ := GAlphabet Γx) (.work bc) _ y (mulStacks a acc bc S₁ y)
    (fun _ => 4 * (S (.work a)).length + 3) body (fun i hi => by
      rw [hmulbc, marks, Ne, List.replicate_eq_nil_iff]
      omega) (by rw [hmulbc]; simp [marks])
  have hstart : mulStacks a acc bc S₁ y 0 = S₁ := by
    funext k
    simp only [mulStacks, update_apply']
    split_ifs <;> subst_vars <;> simp_all
  rw [hstart] at hloop
  have combined := seq_exits _ _ first hloop
  unfold mulInto
  convert combined using 1
  funext k
  simp only [mulStacks, update_apply', hS₁acc]
  split_ifs <;> subst_vars <;> simp_all [marks]

end LeanNPHardness.TableauStacks
