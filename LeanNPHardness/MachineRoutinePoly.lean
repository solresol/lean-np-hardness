import LeanNPHardness.MachineRoutineUnary
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring

/-!
# Unary polynomial evaluation by Horner's scheme

A polynomial with natural coefficients is evaluated on a unary argument by
repeating `acc := acc * x + c` over the coefficients from the highest degree
down. Each step multiplies by repeated copying, moves the product back to
the accumulator, and appends the coefficient. `evalPoly_exits` gives the
exact run; `hornerFold_coeffList` identifies the result with
`Polynomial.eval`.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx]

/-- Horner's fold: `acc := acc * x + c` over the coefficients. -/
def hornerFold (x : ℕ) : List ℕ → ℕ → ℕ
  | [], a => a
  | c :: cs, a => hornerFold x cs (a * x + c)

/-- Coefficients of a polynomial from the highest degree down. -/
noncomputable def coeffList (p : Polynomial ℕ) : List ℕ :=
  ((List.range (p.natDegree + 1)).map p.coeff).reverse

theorem hornerFold_reverse_range (x : ℕ) (c : ℕ → ℕ) (d : ℕ) :
    ∀ acc, hornerFold x (((List.range (d + 1)).map c).reverse) acc =
      acc * x ^ (d + 1) + ∑ i ∈ Finset.range (d + 1), c i * x ^ i := by
  induction d with
  | zero =>
      intro acc
      simp [hornerFold, List.range_succ]
  | succ d ih =>
      intro acc
      rw [List.range_succ, List.map_append, List.reverse_append]
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, hornerFold, ih, Finset.sum_range_succ]
      ring

theorem hornerFold_coeffList (p : Polynomial ℕ) (x : ℕ) :
    hornerFold x (coeffList p) 0 = p.eval x := by
  rw [coeffList, hornerFold_reverse_range, Polynomial.eval_eq_sum_range]
  simp

/-- One Horner step on the stacks: `acc := acc * x + c`. -/
def hornerStep (x acc tmp scr bc : WorkName) (c : ℕ) : GRoutine Γx :=
  seq (mulInto acc x tmp scr bc)
    (seq (drain (.work acc))
      (seq (moveAll (.work tmp) (.work acc) id .mark) (pushList (.work acc) (marks c))))

def hornerStepCost (n a : ℕ) : ℕ :=
  (4 * n + 2 + loopSteps (fun _ => 4 * a + 3) n) + (2 * a + 1) + (2 * (n * a) + 1) + 1

theorem flatten_replicate_marks (y a : ℕ) :
    (List.replicate y (marks a)).flatten = marks (y * a) := by
  simp [marks, List.flatten_replicate_replicate]

theorem hornerStep_exits (x acc tmp scr bc : WorkName)
    (hxa : x ≠ acc) (hxt : x ≠ tmp) (hxs : x ≠ scr) (hxb : x ≠ bc)
    (hat : acc ≠ tmp) (has : acc ≠ scr) (hab : acc ≠ bc)
    (hts : tmp ≠ scr) (htb : tmp ≠ bc) (hsb : scr ≠ bc)
    (S : Stacks (GAlphabet Γx)) (n a : ℕ) (hx : S (.work x) = marks n)
    (hacc : S (.work acc) = marks a) (htmp : S (.work tmp) = []) (hscr : S (.work scr) = [])
    (hbc : S (.work bc) = []) (c : ℕ) :
    (hornerStep (Γx := Γx) x acc tmp scr bc c).Exits S (hornerStepCost n a)
      (Function.update S (.work acc) (marks (a * n + c))) := by
  have mul := mulInto_exits (Γx := Γx) acc x tmp scr bc hxa.symm hat has hab hxt hxs hxb hts htb
    hsb S n hx hscr hbc
  rw [hacc, marks_length, htmp, List.append_nil, flatten_replicate_marks] at mul
  set S₁ := Function.update S (.work tmp) (marks (n * a)) with hS₁
  have hS₁acc : S₁ (.work acc) = marks a := by rw [hS₁, Function.update_of_ne (work_ne hat), hacc]
  have dr := drain_exits (Γ := GAlphabet Γx) (.work acc) S₁
  rw [hS₁acc, marks_length] at dr
  set S₂ := Function.update S₁ (.work acc) [] with hS₂
  have hS₂tmp : S₂ (.work tmp) = marks (n * a) := by
    rw [hS₂, Function.update_of_ne (work_ne hat.symm), hS₁, Function.update_self]
  have hS₂acc : S₂ (.work acc) = [] := by rw [hS₂, Function.update_self]
  have mv := moveAll_exits (Γ := GAlphabet Γx) (.work tmp) (.work acc) (work_ne hat.symm) id .mark S₂
  rw [hS₂tmp, hS₂acc, marks_length, List.map_id, List.append_nil] at mv
  have hrev : (marks (n * a)).reverse = marks (n * a) := by simp [marks]
  rw [hrev] at mv
  set S₃ := Function.update (Function.update S₂ (.work tmp) []) (.work acc) (marks (n * a)) with hS₃
  have pu := pushList_exits (Γ := GAlphabet Γx) (.work acc) (marks c) S₃
  have hS₃acc : S₃ (.work acc) = marks (n * a) := by rw [hS₃, Function.update_self]
  rw [hS₃acc, ← marks_append] at pu
  have combined := seq_exits _ _ mul (seq_exits _ _ dr (seq_exits _ _ mv pu))
  convert combined using 1
  · simp only [hornerStepCost]; omega
  · funext k
    simp only [S₃, S₂, S₁, update_apply']
    split_ifs <;> subst_vars <;> simp_all [marks]
    rw [Nat.mul_comm, Nat.add_comm]

/-- Evaluate the coefficient list by Horner's scheme. -/
def evalPoly (x acc tmp scr bc : WorkName) : List ℕ → GRoutine Γx
  | [] => skip
  | c :: cs => seq (hornerStep x acc tmp scr bc c) (evalPoly x acc tmp scr bc cs)

def evalPolyCost (n : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 1
  | c :: cs, a => hornerStepCost n a + evalPolyCost n cs (a * n + c)

theorem evalPoly_exits (x acc tmp scr bc : WorkName)
    (hxa : x ≠ acc) (hxt : x ≠ tmp) (hxs : x ≠ scr) (hxb : x ≠ bc)
    (hat : acc ≠ tmp) (has : acc ≠ scr) (hab : acc ≠ bc)
    (hts : tmp ≠ scr) (htb : tmp ≠ bc) (hsb : scr ≠ bc) (cs : List ℕ) :
    ∀ (S : Stacks (GAlphabet Γx)) (n a : ℕ), S (.work x) = marks n →
      S (.work acc) = marks a → S (.work tmp) = [] → S (.work scr) = [] → S (.work bc) = [] →
      (evalPoly (Γx := Γx) x acc tmp scr bc cs).Exits S (evalPolyCost n cs a)
        (Function.update S (.work acc) (marks (hornerFold n cs a))) := by
  induction cs with
  | nil =>
      intro S n a hx hacc htmp hscr hbc
      have := skip_exits (Γ := GAlphabet Γx) S
      simp only [evalPoly, evalPolyCost, hornerFold]
      rw [← hacc, Function.update_eq_self]
      exact this
  | cons c cs ih =>
      intro S n a hx hacc htmp hscr hbc
      have step := hornerStep_exits (Γx := Γx) x acc tmp scr bc hxa hxt hxs hxb hat has hab hts htb
        hsb S n a hx hacc htmp hscr hbc c
      set S₁ := Function.update S (.work acc) (marks (a * n + c)) with hS₁
      have rest := ih S₁ n (a * n + c) (by rw [hS₁, Function.update_of_ne (work_ne hxa), hx])
        (by rw [hS₁, Function.update_self]) (by rw [hS₁, Function.update_of_ne (work_ne hat.symm), htmp])
        (by rw [hS₁, Function.update_of_ne (work_ne has.symm), hscr])
        (by rw [hS₁, Function.update_of_ne (work_ne hab.symm), hbc])
      have combined := seq_exits _ _ step rest
      simp only [evalPoly, evalPolyCost, hornerFold]
      convert combined using 1
      rw [hS₁, Function.update_idem]

end LeanNPHardness.TableauStacks
