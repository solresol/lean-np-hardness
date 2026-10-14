import LeanNPHardness.MachineRoutinePoly

/-!
# The parameter stage of the generator

From the input alone, materialize as unary strings the input length `n`,
the certificate bound `q = bound.eval n`, the paired length `m = n + q`, the
horizon `T = time.eval m`, `T * pb`, the generic cell count
`G = n + q + T * pb + 2`, and the registers `w = width` and
`pw = (G + 4D) * width`, leaving the input restored in its original order.
`parameterStage_exits` gives the exact run.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx]

/-- The stacks of the parameter stage: the input, its reversed copy, the
counters, and the two width registers; everything else empty. -/
def paramStacks (x xk : List Γx) (n q m t tpb g w pw : ℕ) : Stacks (GAlphabet Γx)
  | .input => x
  | .xkeep => xk
  | .work (.cnt .n) => marks n
  | .work (.cnt .q) => marks q
  | .work (.cnt .m) => marks m
  | .work (.cnt .t) => marks t
  | .work (.cnt .tpb) => marks tpb
  | .work (.cnt .g) => marks g
  | .work (.reg .w) => marks w
  | .work (.reg .pw) => marks pw
  | _ => []

/-- Pointwise comparison of stack families over the generator's stacks:
split into every stack, simplify, and leave the remaining unary-string
equations to `marks_finish`. -/
macro "gstacks_ext" : tactic =>
  `(tactic| (funext k; rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    (try simp [paramStacks, Function.update_of_ne])))

/-- Close unary-string equations left by `gstacks_ext`. -/
macro "marks_finish" : tactic =>
  `(tactic| all_goals (simp only [marks, List.replicate_append_replicate]; congr 1; ring))

/-! ### Counting the input -/

/-- Move the input onto `xkeep` (reversing it) while counting its symbols. -/
def countInput : GRoutine Γx :=
  loop .input (dispatch .input fun s =>
    seq (pushList .xkeep [s]) (pushList (.work (.cnt .n)) [.mark]))

/-- Move `xkeep` back onto the input stack, restoring the original order. -/
def restoreInput : GRoutine Γx :=
  loop .xkeep (dispatch .xkeep fun s => pushList .input [s])

theorem countInput_exits (x : List Γx) :
    (countInput (Γx := Γx)).Exits (paramStacks x [] 0 0 0 0 0 0 0 0) (4 * x.length + 1)
      (paramStacks [] x.reverse x.length 0 0 0 0 0 0 0) := by
  have key := loop_exits (Γ := GAlphabet Γx) .input
    (dispatch .input fun s => seq (pushList .xkeep [s]) (pushList (.work (.cnt .n)) [.mark]))
    x.length (fun i => paramStacks (x.drop i) (x.take i).reverse i 0 0 0 0 0 0 0) (fun _ => 3) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 3) x.length = 4 * x.length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using key
  · intro i hi
    have hsplit : (x.drop i) = x[i] :: x.drop (i + 1) := List.drop_eq_getElem_cons hi
    have h1 := pushList_exits (Γ := GAlphabet Γx) .xkeep [x[i]]
      (Function.update (paramStacks (x.drop i) (x.take i).reverse i 0 0 0 0 0 0 0) .input
        (x.drop (i + 1)))
    have h2 := pushList_exits (Γ := GAlphabet Γx) (.work (.cnt .n)) [.mark]
      (Function.update (Function.update (paramStacks (x.drop i) (x.take i).reverse i 0 0 0 0 0 0 0)
        .input (x.drop (i + 1))) .xkeep
        ([x[i]] ++ Function.update (paramStacks (x.drop i) (x.take i).reverse i 0 0 0 0 0 0 0)
          .input (x.drop (i + 1)) .xkeep))
    have body := dispatch_exits (Γ := GAlphabet Γx) .input
      (fun s => seq (pushList .xkeep [s]) (pushList (.work (.cnt .n)) [.mark]))
      (paramStacks (x.drop i) (x.take i).reverse i 0 0 0 0 0 0 0) x[i] (x.drop (i + 1)) hsplit
      (seq_exits _ _ h1 h2)
    convert body using 1
    have htake : (x.take (i + 1)).reverse = x[i] :: (x.take i).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; simp
    dsimp only
    rw [htake]
    gstacks_ext
    all_goals simp [marks, List.replicate_succ]
  · intro i hi
    simp [paramStacks, List.drop_eq_nil_iff]; omega
  · simp [paramStacks]

theorem restoreInput_exits (x xk : List Γx) (n q m t tpb g w pw : ℕ) :
    (restoreInput (Γx := Γx)).Exits (paramStacks x xk n q m t tpb g w pw) (3 * xk.length + 1)
      (paramStacks (xk.reverse ++ x) [] n q m t tpb g w pw) := by
  have key := loop_exits (Γ := GAlphabet Γx) .xkeep (dispatch .xkeep fun s => pushList .input [s])
    xk.length (fun i => paramStacks ((xk.take i).reverse ++ x) (xk.drop i) n q m t tpb g w pw)
    (fun _ => 2) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 2) xk.length = 3 * xk.length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using key
  · intro i hi
    have hsplit : (xk.drop i) = xk[i] :: xk.drop (i + 1) := List.drop_eq_getElem_cons hi
    have h1 := pushList_exits (Γ := GAlphabet Γx) .input [xk[i]]
      (Function.update (paramStacks ((xk.take i).reverse ++ x) (xk.drop i) n q m t tpb g w pw) .xkeep
        (xk.drop (i + 1)))
    have body := dispatch_exits (Γ := GAlphabet Γx) .xkeep (fun s => pushList .input [s])
      (paramStacks ((xk.take i).reverse ++ x) (xk.drop i) n q m t tpb g w pw) xk[i] (xk.drop (i + 1))
      hsplit h1
    convert body using 1
    have htake : (xk.take (i + 1)).reverse = xk[i] :: (xk.take i).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; simp
    dsimp only
    rw [htake]
    gstacks_ext
  · intro i hi
    simp [paramStacks, List.drop_eq_nil_iff]; omega
  · simp [paramStacks]

/-! ### Repetition -/

/-- Run a routine `n` times. -/
def repeatSeq (n : ℕ) (r : GRoutine Γx) : GRoutine Γx :=
  match n with
  | 0 => skip
  | n + 1 => seq r (repeatSeq n r)

omit [Fintype Γx] [DecidableEq Γx] in
theorem repeatSeq_exits (n : ℕ) (r : GRoutine Γx) (c : ℕ) :
    ∀ (S : ℕ → Stacks (GAlphabet Γx)), (∀ i < n, r.Exits (S i) c (S (i + 1))) →
      (repeatSeq n r).Exits (S 0) (n * c + 1) (S n) := by
  induction n with
  | zero => intro S _; simpa [repeatSeq] using skip_exits (S 0)
  | succ n ih =>
      intro S h
      have first := h 0 (by omega)
      have rest := ih (fun i => S (i + 1)) fun i hi => h (i + 1) (by omega)
      have := seq_exits _ _ first rest
      simp only [repeatSeq]
      convert this using 1
      rw [Nat.succ_mul]; omega

/-! ### The stage -/

/-- Materialize all counters and registers from the input. -/
noncomputable def parameterStage (bound time : Polynomial ℕ) (pb D width : ℕ) : GRoutine Γx :=
  seq countInput <| seq restoreInput <|
  seq (evalPoly (.cnt .n) (.cnt .q) (.cnt .tmp) .scratch (.cnt .bc) (coeffList bound)) <|
  seq (copyWork (.cnt .n) (.cnt .m) .scratch) <| seq (copyWork (.cnt .q) (.cnt .m) .scratch) <|
  seq (evalPoly (.cnt .m) (.cnt .t) (.cnt .tmp) .scratch (.cnt .bc) (coeffList time)) <|
  seq (repeatSeq pb (copyWork (.cnt .t) (.cnt .tpb) .scratch)) <|
  seq (copyWork (.cnt .n) (.cnt .g) .scratch) <| seq (copyWork (.cnt .q) (.cnt .g) .scratch) <|
  seq (copyWork (.cnt .tpb) (.cnt .g) .scratch) <| seq (pushList (.work (.cnt .g)) (marks 2)) <|
  seq (pushList (.work (.reg .w)) (marks width)) <|
  seq (repeatSeq width (copyWork (.cnt .g) (.reg .pw) .scratch))
    (pushList (.work (.reg .pw)) (marks (4 * D * width)))

/-- Exact cost of the parameter stage. -/
noncomputable def parameterCost (bound time : Polynomial ℕ) (pb D width : ℕ) (n : ℕ) : ℕ :=
  let q := bound.eval n
  let t := time.eval (n + q)
  let g := n + q + pb * t + 2
  (4 * n + 1) + (3 * n + 1) + evalPolyCost n (coeffList bound) 0 +
    (4 * n + 2) + (4 * q + 2) + evalPolyCost (n + q) (coeffList time) 0 +
    (pb * (4 * t + 2) + 1) + (4 * n + 2) + (4 * q + 2) + (4 * (pb * t) + 2) + 1 + 1 +
    (width * (4 * g + 2) + 1) + 1

theorem parameterStage_exits (bound time : Polynomial ℕ) (pb D width : ℕ) (x : List Γx) :
    (parameterStage (Γx := Γx) bound time pb D width).Exits
      (paramStacks x [] 0 0 0 0 0 0 0 0) (parameterCost bound time pb D width x.length)
      (paramStacks x [] x.length (bound.eval x.length) (x.length + bound.eval x.length)
        (time.eval (x.length + bound.eval x.length))
        (pb * time.eval (x.length + bound.eval x.length))
        (x.length + bound.eval x.length + pb * time.eval (x.length + bound.eval x.length) + 2)
        width
        ((x.length + bound.eval x.length + pb * time.eval (x.length + bound.eval x.length) + 2 + 4 * D) *
          width)) := by
  set n := x.length with hn
  set q := bound.eval n with hq
  set t := time.eval (n + q) with ht
  set g := n + q + pb * t + 2 with hg
  have s1 := countInput_exits (Γx := Γx) x
  have s2 := restoreInput_exits (Γx := Γx) [] x.reverse n 0 0 0 0 0 0 0
  rw [List.reverse_reverse, List.append_nil] at s2
  have s3 := evalPoly_exits (Γx := Γx) (.cnt .n) (.cnt .q) (.cnt .tmp) .scratch (.cnt .bc)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (coeffList bound) (paramStacks x [] n 0 0 0 0 0 0 0) n 0 rfl rfl rfl rfl rfl
  rw [hornerFold_coeffList, ← hq] at s3
  have e3 : Function.update (paramStacks x [] n 0 0 0 0 0 0 0) (.work (.cnt .q)) (marks q) =
      paramStacks x [] n q 0 0 0 0 0 0 := by gstacks_ext
  rw [e3] at s3
  have s4 := copyWork_exits (Γx := Γx) (.cnt .n) (.cnt .m) .scratch (by decide) (by decide) (by decide)
    (paramStacks x [] n q 0 0 0 0 0 0) rfl
  have e4 : Function.update (paramStacks x [] n q 0 0 0 0 0 0) (.work (.cnt .m))
      (paramStacks x [] n q 0 0 0 0 0 0 (.work (.cnt .n)) ++
        paramStacks x [] n q 0 0 0 0 0 0 (.work (.cnt .m))) = paramStacks x [] n q n 0 0 0 0 0 := by
    gstacks_ext
  rw [e4] at s4
  have s5 := copyWork_exits (Γx := Γx) (.cnt .q) (.cnt .m) .scratch (by decide) (by decide) (by decide)
    (paramStacks x [] n q n 0 0 0 0 0) rfl
  have e5 : Function.update (paramStacks x [] n q n 0 0 0 0 0) (.work (.cnt .m))
      (paramStacks x [] n q n 0 0 0 0 0 (.work (.cnt .q)) ++
        paramStacks x [] n q n 0 0 0 0 0 (.work (.cnt .m))) = paramStacks x [] n q (n + q) 0 0 0 0 0 := by
    gstacks_ext
    marks_finish
  rw [e5] at s5
  have s6 := evalPoly_exits (Γx := Γx) (.cnt .m) (.cnt .t) (.cnt .tmp) .scratch (.cnt .bc)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (coeffList time) (paramStacks x [] n q (n + q) 0 0 0 0 0) (n + q) 0
    rfl rfl rfl rfl rfl
  rw [hornerFold_coeffList, ← ht] at s6
  have e6 : Function.update (paramStacks x [] n q (n + q) 0 0 0 0 0) (.work (.cnt .t)) (marks t) =
      paramStacks x [] n q (n + q) t 0 0 0 0 := by gstacks_ext
  rw [e6] at s6
  have s7 := repeatSeq_exits (Γx := Γx) pb (copyWork (.cnt .t) (.cnt .tpb) .scratch) (4 * t + 2)
    (fun i => paramStacks x [] n q (n + q) t (i * t) 0 0 0) (fun i _ => by
      have := copyWork_exits (Γx := Γx) (.cnt .t) (.cnt .tpb) .scratch (by decide) (by decide)
        (by decide) (paramStacks x [] n q (n + q) t (i * t) 0 0 0) rfl
      convert this using 1
      · simp [paramStacks]
      · gstacks_ext
        marks_finish)
  simp only [Nat.zero_mul] at s7
  have s8 := copyWork_exits (Γx := Γx) (.cnt .n) (.cnt .g) .scratch (by decide) (by decide) (by decide)
    (paramStacks x [] n q (n + q) t (pb * t) 0 0 0) rfl
  have e8 : Function.update (paramStacks x [] n q (n + q) t (pb * t) 0 0 0) (.work (.cnt .g))
      (paramStacks x [] n q (n + q) t (pb * t) 0 0 0 (.work (.cnt .n)) ++
        paramStacks x [] n q (n + q) t (pb * t) 0 0 0 (.work (.cnt .g))) =
      paramStacks x [] n q (n + q) t (pb * t) n 0 0 := by gstacks_ext
  rw [e8] at s8
  have s9 := copyWork_exits (Γx := Γx) (.cnt .q) (.cnt .g) .scratch (by decide) (by decide) (by decide)
    (paramStacks x [] n q (n + q) t (pb * t) n 0 0) rfl
  have e9 : Function.update (paramStacks x [] n q (n + q) t (pb * t) n 0 0) (.work (.cnt .g))
      (paramStacks x [] n q (n + q) t (pb * t) n 0 0 (.work (.cnt .q)) ++
        paramStacks x [] n q (n + q) t (pb * t) n 0 0 (.work (.cnt .g))) =
      paramStacks x [] n q (n + q) t (pb * t) (n + q) 0 0 := by
    gstacks_ext
    marks_finish
  rw [e9] at s9
  have s10 := copyWork_exits (Γx := Γx) (.cnt .tpb) (.cnt .g) .scratch (by decide) (by decide)
    (by decide) (paramStacks x [] n q (n + q) t (pb * t) (n + q) 0 0) rfl
  have e10 : Function.update (paramStacks x [] n q (n + q) t (pb * t) (n + q) 0 0) (.work (.cnt .g))
      (paramStacks x [] n q (n + q) t (pb * t) (n + q) 0 0 (.work (.cnt .tpb)) ++
        paramStacks x [] n q (n + q) t (pb * t) (n + q) 0 0 (.work (.cnt .g))) =
      paramStacks x [] n q (n + q) t (pb * t) (n + q + pb * t) 0 0 := by
    gstacks_ext
    marks_finish
  rw [e10] at s10
  have s11 := pushList_exits (Γ := GAlphabet Γx) (.work (.cnt .g)) (marks 2)
    (paramStacks x [] n q (n + q) t (pb * t) (n + q + pb * t) 0 0)
  have e11 : Function.update (paramStacks x [] n q (n + q) t (pb * t) (n + q + pb * t) 0 0)
      (.work (.cnt .g)) (marks 2 ++ paramStacks x [] n q (n + q) t (pb * t) (n + q + pb * t) 0 0
        (.work (.cnt .g))) = paramStacks x [] n q (n + q) t (pb * t) g 0 0 := by
    gstacks_ext
    marks_finish
  rw [e11] at s11
  have s12 := pushList_exits (Γ := GAlphabet Γx) (.work (.reg .w)) (marks width)
    (paramStacks x [] n q (n + q) t (pb * t) g 0 0)
  have e12 : Function.update (paramStacks x [] n q (n + q) t (pb * t) g 0 0) (.work (.reg .w))
      (marks width ++ paramStacks x [] n q (n + q) t (pb * t) g 0 0 (.work (.reg .w))) =
      paramStacks x [] n q (n + q) t (pb * t) g width 0 := by gstacks_ext
  rw [e12] at s12
  have s13 := repeatSeq_exits (Γx := Γx) width (copyWork (.cnt .g) (.reg .pw) .scratch) (4 * g + 2)
    (fun i => paramStacks x [] n q (n + q) t (pb * t) g width (i * g)) (fun i _ => by
      have := copyWork_exits (Γx := Γx) (.cnt .g) (.reg .pw) .scratch (by decide) (by decide)
        (by decide) (paramStacks x [] n q (n + q) t (pb * t) g width (i * g)) rfl
      convert this using 1
      · simp [paramStacks]
      · gstacks_ext
        marks_finish)
  simp only [Nat.zero_mul] at s13
  have s14 := pushList_exits (Γ := GAlphabet Γx) (.work (.reg .pw)) (marks (4 * D * width))
    (paramStacks x [] n q (n + q) t (pb * t) g width (width * g))
  have e14 : Function.update (paramStacks x [] n q (n + q) t (pb * t) g width (width * g))
      (.work (.reg .pw)) (marks (4 * D * width) ++
        paramStacks x [] n q (n + q) t (pb * t) g width (width * g) (.work (.reg .pw))) =
      paramStacks x [] n q (n + q) t (pb * t) g width ((g + 4 * D) * width) := by
    gstacks_ext
    marks_finish
  rw [e14] at s14
  have all := seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4
    (seq_exits _ _ s5 (seq_exits _ _ s6 (seq_exits _ _ s7 (seq_exits _ _ s8 (seq_exits _ _ s9
    (seq_exits _ _ s10 (seq_exits _ _ s11 (seq_exits _ _ s12 (seq_exits _ _ s13 s14))))))))))))
  convert all using 1
  simp only [parameterCost, paramStacks, marks_length, List.length_reverse, ← hn, ← hq, ← ht, ← hg]
  ring

end LeanNPHardness.TableauStacks
