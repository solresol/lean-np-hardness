import LeanNPHardness.MachineRoutine

/-!
# Primitive routines

Constant pushes, single pops, moving a stack onto another through a symbol
map (reversing order), copying a stack onto another through a scratch stack
(preserving order and the source), and draining a stack. Each primitive has
an exact step-count theorem in terms of the stack lengths. These are the
building blocks of the tableau generator; no polynomial claim is made here.
-/

namespace LeanNPHardness.Routines

open Turing

variable {K : Type} [DecidableEq K] {Γ : K → Type}

/-! ### Stack-update bookkeeping -/

theorem update_update_ne {k₁ k₂ : K} (h : k₁ ≠ k₂) (S : Stacks Γ) (a : List (Γ k₁)) (b : List (Γ k₂)) :
    Function.update (Function.update S k₁ a) k₂ b =
      Function.update (Function.update S k₂ b) k₁ a :=
  Function.update_comm h a b S

/-- Pointwise evaluation of a dependent stack update. -/
theorem update_apply' (S : Stacks Γ) (a : K) (v : List (Γ a)) (k : K) :
    Function.update S a v k = if h : k = a then h ▸ v else S k := by
  by_cases h : k = a
  · subst h; simp
  · simp [h]

/-! ### Constant pushes -/

/-- Push the listed symbols in order (last element first). -/
def pushStmt (k : K) : List (Γ k) → TM2.Stmt Γ Unit Unit
  | [] => .halt
  | a :: rest => .push k (fun _ => a) (pushStmt k rest)

theorem pushStmt_stepAux (k : K) (as : List (Γ k)) (S : Stacks Γ) :
    TM2.stepAux (pushStmt k as) () S = ⟨none, (), Function.update S k (as.reverse ++ S k)⟩ := by
  induction as generalizing S with
  | nil => simp [pushStmt, TM2.stepAux]
  | cons a rest ih =>
      simp only [pushStmt, TM2.stepAux, ih, Function.update_self, Function.update_idem,
        List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Push a constant list onto stack `k` in one step; the stack becomes `as ++ S k`. -/
def pushList (k : K) (as : List (Γ k)) : Routine Γ where
  Λ := Unit
  σ := Unit
  entry := ()
  init := ()
  program _ := pushStmt k as.reverse

theorem pushList_exits (k : K) (as : List (Γ k)) (S : Stacks Γ) :
    (pushList k as).Exits S 1 (Function.update S k (as ++ S k)) := by
  refine ⟨(), ?_⟩
  simp only [Function.iterate_one]
  change TM2.step (pushList k as).program ⟨some (), (), S⟩ = _
  simp [TM2.step, pushList, pushStmt_stepAux]

/-! ### Single pops -/

/-- Remove the top symbol of stack `k` in one step. -/
def popOne (k : K) : Routine Γ where
  Λ := Unit
  σ := Unit
  entry := ()
  init := ()
  program _ := .pop k (fun _ _ => ()) .halt

theorem popOne_exits (k : K) (S : Stacks Γ) :
    (popOne k).Exits S 1 (Function.update S k (S k).tail) := by
  refine ⟨(), ?_⟩
  simp only [Function.iterate_one]
  change TM2.step (popOne k).program ⟨some (), (), S⟩ = _
  simp [TM2.step, popOne, TM2.stepAux]

/-! ### Moving a stack -/

/-- Pop one symbol from `src` and push its image on `dst`, in one step. -/
def movePop (src dst : K) [Fintype (Γ src)] (f : Γ src → Γ dst) (d : Γ dst) : Routine Γ where
  Λ := Unit
  σ := Option (Γ src)
  entry := ()
  init := none
  program _ := .pop src (fun _ s => s) (.push dst (fun v => (v.map f).getD d) .halt)

theorem movePop_exits (src dst : K) [Fintype (Γ src)] (hne : src ≠ dst) (f : Γ src → Γ dst)
    (d : Γ dst) (S : Stacks Γ) (a : Γ src) (rest : List (Γ src)) (hsrc : S src = a :: rest) :
    (movePop src dst f d).Exits S 1
      (Function.update (Function.update S src rest) dst (f a :: S dst)) := by
  refine ⟨some a, ?_⟩
  simp only [Function.iterate_one]
  change TM2.step (movePop src dst f d).program ⟨some (), none, S⟩ = _
  simp only [TM2.step, movePop, TM2.stepAux, hsrc, List.head?_cons, List.tail_cons,
    Option.map_some, Option.getD_some, Function.update_of_ne hne.symm]

/-- Move all of `src` onto `dst` through `f`, reversing order. -/
def moveAll (src dst : K) [Fintype (Γ src)] (f : Γ src → Γ dst) (d : Γ dst) : Routine Γ :=
  loop src (movePop src dst f d)

/-- The stacks after moving `i` symbols. -/
def moveStacks (src dst : K) (f : Γ src → Γ dst) (S : Stacks Γ) (i : ℕ) : Stacks Γ :=
  Function.update (Function.update S src ((S src).drop i)) dst
    ((((S src).take i).map f).reverse ++ S dst)

theorem moveStacks_zero (src dst : K) (f : Γ src → Γ dst) (S : Stacks Γ) :
    moveStacks src dst f S 0 = S := by
  simp [moveStacks]

theorem moveStacks_src (src dst : K) (hne : src ≠ dst) (f : Γ src → Γ dst) (S : Stacks Γ) (i : ℕ) :
    moveStacks src dst f S i src = (S src).drop i := by
  simp [moveStacks, Function.update_of_ne hne]

theorem moveStacks_dst (src dst : K) (f : Γ src → Γ dst) (S : Stacks Γ) (i : ℕ) :
    moveStacks src dst f S i dst = (((S src).take i).map f).reverse ++ S dst := by
  simp [moveStacks]

theorem moveStacks_succ (src dst : K) (hne : src ≠ dst) (f : Γ src → Γ dst) (S : Stacks Γ)
    (i : ℕ) (hi : i < (S src).length) :
    moveStacks src dst f S (i + 1) =
      Function.update (Function.update (moveStacks src dst f S i) src ((S src).drop (i + 1))) dst
        (f ((S src)[i]'hi) :: moveStacks src dst f S i dst) := by
  have htake : (((S src).take (i + 1)).map f).reverse =
      f ((S src)[i]'hi) :: (((S src).take i).map f).reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
      List.map_cons, List.map_nil, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
  rw [moveStacks_dst]
  funext k
  simp only [moveStacks, update_apply', htake]
  split_ifs <;> subst_vars <;> simp_all

theorem moveAll_exits (src dst : K) [Fintype (Γ src)] (hne : src ≠ dst) (f : Γ src → Γ dst)
    (d : Γ dst) (S : Stacks Γ) :
    (moveAll src dst f d).Exits S (2 * (S src).length + 1)
      (Function.update (Function.update S src []) dst (((S src).map f).reverse ++ S dst)) := by
  have key := loop_exits src (movePop src dst f d) (S src).length (moveStacks src dst f S)
    (fun _ => 1) ?_ ?_ ?_
  · rw [moveStacks_zero] at key
    have hsteps : loopSteps (fun _ => 1) (S src).length = 2 * (S src).length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    convert key using 1
    simp [moveStacks]
  · intro i hi
    have hsplit : moveStacks src dst f S i src = (S src)[i] :: (S src).drop (i + 1) := by
      rw [moveStacks_src src dst hne, List.drop_eq_getElem_cons hi]
    have := movePop_exits src dst hne f d (moveStacks src dst f S i) ((S src)[i])
      ((S src).drop (i + 1)) hsplit
    rw [moveStacks_succ src dst hne f S i hi]
    exact this
  · intro i hi
    rw [moveStacks_src src dst hne, Ne, List.drop_eq_nil_iff]
    omega
  · rw [moveStacks_src src dst hne]
    simp

/-! ### Draining a stack -/

/-- Empty stack `k`. -/
def drain (k : K) : Routine Γ := loop k (popOne k)

theorem drain_exits (k : K) (S : Stacks Γ) :
    (drain k).Exits S (2 * (S k).length + 1) (Function.update S k []) := by
  have key := loop_exits k (popOne k) (S k).length (fun i => Function.update S k ((S k).drop i))
    (fun _ => 1) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 1) (S k).length = 2 * (S k).length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using key
  · intro i hi
    have := popOne_exits k (Function.update S k ((S k).drop i))
    simp only [Function.update_self, Function.update_idem] at this
    rw [List.tail_drop] at this
    exact this
  · intro i hi
    simp only [Function.update_self, Ne, List.drop_eq_nil_iff]
    omega
  · simp

/-! ### Copying a stack -/

/-- Pop one scratch symbol and push its images on `src` and `dst`, in one step. -/
def restorePop (src dst scratch : K) [Fintype (Γ scratch)] (back : Γ scratch → Γ src)
    (toD : Γ scratch → Γ dst) (dS : Γ src) (dD : Γ dst) : Routine Γ where
  Λ := Unit
  σ := Option (Γ scratch)
  entry := ()
  init := none
  program _ :=
    .pop scratch (fun _ s => s)
      (.push src (fun v => (v.map back).getD dS)
        (.push dst (fun v => (v.map toD).getD dD) .halt))

theorem restorePop_exits (src dst scratch : K) [Fintype (Γ scratch)] (back : Γ scratch → Γ src)
    (toD : Γ scratch → Γ dst) (dS : Γ src) (dD : Γ dst)
    (hsd : src ≠ dst) (hss : src ≠ scratch) (hds : dst ≠ scratch)
    (S : Stacks Γ) (a : Γ scratch) (rest : List (Γ scratch)) (hscr : S scratch = a :: rest) :
    (restorePop src dst scratch back toD dS dD).Exits S 1
      (Function.update (Function.update (Function.update S scratch rest) src (back a :: S src))
        dst (toD a :: S dst)) := by
  refine ⟨some a, ?_⟩
  simp only [Function.iterate_one]
  change TM2.step (restorePop src dst scratch back toD dS dD).program ⟨some (), none, S⟩ = _
  simp only [TM2.step, restorePop, TM2.stepAux, hscr, List.head?_cons, List.tail_cons,
    Option.map_some, Option.getD_some, Function.update_of_ne hss, Function.update_of_ne hsd.symm,
    Function.update_of_ne hds]

/-- Copy `src` onto `dst` (through `toD ∘ toS`), preserving `src`, using an
initially empty `scratch` stack. -/
def copyAll (src dst scratch : K) [Fintype (Γ src)] [Fintype (Γ scratch)]
    (toS : Γ src → Γ scratch) (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst)
    (dScr : Γ scratch) (dS : Γ src) (dD : Γ dst) : Routine Γ :=
  seq (moveAll src scratch toS dScr) (loop scratch (restorePop src dst scratch back toD dS dD))

/-- The stacks after restoring `i` symbols from the reversed scratch copy. -/
def restoreStacks (src dst scratch : K) (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst)
    (S : Stacks Γ) (i : ℕ) : Stacks Γ :=
  Function.update (Function.update (Function.update S scratch ((S scratch).drop i)) src
    ((((S scratch).take i).map back).reverse ++ S src)) dst
    ((((S scratch).take i).map toD).reverse ++ S dst)

theorem restoreStacks_scratch (src dst scratch : K) (hss : src ≠ scratch) (hds : dst ≠ scratch)
    (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst) (S : Stacks Γ) (i : ℕ) :
    restoreStacks src dst scratch back toD S i scratch = (S scratch).drop i := by
  simp [restoreStacks, Function.update_of_ne hss.symm, Function.update_of_ne hds.symm]

theorem restoreStacks_src (src dst scratch : K) (hsd : src ≠ dst)
    (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst) (S : Stacks Γ) (i : ℕ) :
    restoreStacks src dst scratch back toD S i src =
      (((S scratch).take i).map back).reverse ++ S src := by
  simp [restoreStacks, Function.update_of_ne hsd]

theorem restoreStacks_dst (src dst scratch : K)
    (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst) (S : Stacks Γ) (i : ℕ) :
    restoreStacks src dst scratch back toD S i dst =
      (((S scratch).take i).map toD).reverse ++ S dst := by
  simp [restoreStacks]

theorem restoreStacks_succ (src dst scratch : K) (hsd : src ≠ dst) (hss : src ≠ scratch)
    (hds : dst ≠ scratch) (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst) (S : Stacks Γ)
    (i : ℕ) (hi : i < (S scratch).length) :
    restoreStacks src dst scratch back toD S (i + 1) =
      Function.update (Function.update (Function.update (restoreStacks src dst scratch back toD S i)
        scratch ((S scratch).drop (i + 1))) src
        (back ((S scratch)[i]'hi) :: restoreStacks src dst scratch back toD S i src)) dst
        (toD ((S scratch)[i]'hi) :: restoreStacks src dst scratch back toD S i dst) := by
  have htake : ∀ {β : Type} (g : Γ scratch → β),
      (((S scratch).take (i + 1)).map g).reverse =
        g ((S scratch)[i]'hi) :: (((S scratch).take i).map g).reverse := by
    intro β g
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
      List.map_cons, List.map_nil, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
  rw [restoreStacks_src src dst scratch hsd, restoreStacks_dst]
  funext k
  simp only [restoreStacks, update_apply', htake]
  split_ifs <;> subst_vars <;> simp_all

theorem copyAll_exits (src dst scratch : K) [Fintype (Γ src)] [Fintype (Γ scratch)]
    (toS : Γ src → Γ scratch) (back : Γ scratch → Γ src) (toD : Γ scratch → Γ dst)
    (dScr : Γ scratch) (dS : Γ src) (dD : Γ dst)
    (hsd : src ≠ dst) (hss : src ≠ scratch) (hds : dst ≠ scratch)
    (hback : ∀ a, back (toS a) = a) (S : Stacks Γ) (hscr : S scratch = []) :
    (copyAll src dst scratch toS back toD dScr dS dD).Exits S (4 * (S src).length + 2)
      (Function.update S dst ((S src).map (toD ∘ toS) ++ S dst)) := by
  have first := moveAll_exits src scratch hss toS dScr S
  rw [hscr, List.append_nil] at first
  set S₁ := Function.update (Function.update S src []) scratch ((S src).map toS).reverse with hS₁
  have hS₁scr : S₁ scratch = ((S src).map toS).reverse := by simp [S₁]
  have hS₁src : S₁ src = [] := by simp [S₁, Function.update_of_ne hss]
  have hS₁dst : S₁ dst = S dst := by
    simp [S₁, Function.update_of_ne hsd.symm, Function.update_of_ne hds]
  have hlen : (S₁ scratch).length = (S src).length := by simp [hS₁scr]
  have second := loop_exits scratch (restorePop src dst scratch back toD dS dD)
    (S src).length (restoreStacks src dst scratch back toD S₁) (fun _ => 1) ?_ ?_ ?_
  · have hstart : restoreStacks src dst scratch back toD S₁ 0 = S₁ := by simp [restoreStacks]
    rw [hstart] at second
    have combined := seq_exits _ _ first second
    have hsteps : 2 * (S src).length + 1 + loopSteps (fun _ => 1) (S src).length =
        4 * (S src).length + 2 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at combined
    convert combined using 1
    funext k
    simp only [restoreStacks, hS₁scr, hS₁src, hS₁dst]
    rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
    simp only [List.map_reverse, List.map_map, List.reverse_reverse, List.append_nil]
    have hback' : ∀ l : List (Γ src), l.map (back ∘ toS) = l := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp [hback, ih]
    rw [hback']
    by_cases hk : k = dst
    · subst hk; simp [S₁]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases hk' : k = src
      · subst hk'; simp [S₁]
      · rw [Function.update_of_ne hk']
        by_cases hk'' : k = scratch
        · subst hk''; simp [hscr]
        · rw [Function.update_of_ne hk'']
          simp [S₁, Function.update_of_ne hk', Function.update_of_ne hk'']
  · intro i hi
    have hi' : i < (S₁ scratch).length := by rw [hlen]; exact hi
    have hsplit : restoreStacks src dst scratch back toD S₁ i scratch =
        (S₁ scratch)[i] :: (S₁ scratch).drop (i + 1) := by
      rw [restoreStacks_scratch src dst scratch hss hds, List.drop_eq_getElem_cons hi']
    have := restorePop_exits src dst scratch back toD dS dD hsd hss hds
      (restoreStacks src dst scratch back toD S₁ i) ((S₁ scratch)[i]) ((S₁ scratch).drop (i + 1)) hsplit
    rw [restoreStacks_succ src dst scratch hsd hss hds back toD S₁ i hi']
    exact this
  · intro i hi
    rw [restoreStacks_scratch src dst scratch hss hds, Ne, List.drop_eq_nil_iff]
    omega
  · rw [restoreStacks_scratch src dst scratch hss hds]
    simp [hlen]

end LeanNPHardness.Routines
