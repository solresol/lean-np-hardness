import LeanNPHardness.TableauParameters
import LeanNPHardness.TableauTemplates

/-!
# Building blocks of the skeleton emitter

The emitter pushes the skeleton chunk by chunk onto the `skel` stack,
each chunk reversed, so that the stack holds the reverse of the skeleton
emitted so far. Chunks are emitted once, a constant number of times, once
per mark of a counter copy, or once per input symbol. `foldStacks`
sequences a routine over the machine's stack list.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary TableauJobs

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx]

/-- The stacks of the emitter: the parameter stacks plus the two loop
copies and the skeleton stack. -/
def emitStacks (x xk : List Γx) (n q m t tpb g w pw : ℕ) (c1 c2 : ℕ) (sk : List Instr) :
    Stacks (GAlphabet Γx)
  | .input => x
  | .xkeep => xk
  | .skel => sk
  | .work (.cnt .n) => marks n
  | .work (.cnt .q) => marks q
  | .work (.cnt .m) => marks m
  | .work (.cnt .t) => marks t
  | .work (.cnt .tpb) => marks tpb
  | .work (.cnt .g) => marks g
  | .work (.cnt .copy1) => marks c1
  | .work (.cnt .copy2) => marks c2
  | .work (.reg .w) => marks w
  | .work (.reg .pw) => marks pw
  | _ => []

theorem paramStacks_eq_emitStacks (x xk : List Γx) (n q m t tpb g w pw : ℕ) :
    paramStacks x xk n q m t tpb g w pw = emitStacks x xk n q m t tpb g w pw 0 0 [] := by
  funext k
  rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    rfl

/-- Pointwise comparison over the emitter's stacks. -/
macro "estacks_ext" : tactic =>
  `(tactic| (funext k; rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    (try simp [emitStacks, Function.update_of_ne])))

/-- Push one chunk, reversed. -/
def emit (chunk : List Instr) : GRoutine Γx := pushList .skel chunk.reverse

theorem emit_exits (chunk : List Instr) (x xk : List Γx) (n q m t tpb g w pw c1 c2 : ℕ)
    (sk : List Instr) :
    (emit (Γx := Γx) chunk).Exits (emitStacks x xk n q m t tpb g w pw c1 c2 sk) 1
      (emitStacks x xk n q m t tpb g w pw c1 c2 (chunk.reverse ++ sk)) := by
  have := pushList_exits (Γ := GAlphabet Γx) .skel chunk.reverse
    (emitStacks x xk n q m t tpb g w pw c1 c2 sk)
  convert this using 1
  estacks_ext

/-- Emit a list of chunks in order. -/
def emitList : List (List Instr) → GRoutine Γx
  | [] => skip
  | c :: cs => seq (emit c) (emitList cs)

theorem emitList_exits (cs : List (List Instr)) :
    ∀ (x xk : List Γx) (n q m t tpb g w pw c1 c2 : ℕ) (sk : List Instr),
      (emitList (Γx := Γx) cs).Exits (emitStacks x xk n q m t tpb g w pw c1 c2 sk) (cs.length + 1)
        (emitStacks x xk n q m t tpb g w pw c1 c2 (cs.flatten.reverse ++ sk)) := by
  induction cs with
  | nil =>
      intro x xk n q m t tpb g w pw c1 c2 sk
      simpa [emitList] using skip_exits (emitStacks x xk n q m t tpb g w pw c1 c2 sk)
  | cons c cs ih =>
      intro x xk n q m t tpb g w pw c1 c2 sk
      have := seq_exits _ _ (emit_exits (Γx := Γx) c x xk n q m t tpb g w pw c1 c2 sk)
        (ih x xk n q m t tpb g w pw c1 c2 (c.reverse ++ sk))
      simp only [emitList]
      rw [show (c :: cs).length + 1 = 1 + (cs.length + 1) by simp; omega]
      convert this using 2
      simp [List.reverse_append]

/-- Emit a chunk once per mark of the second loop copy, consuming it. -/
def loopEmit2 (chunk : List Instr) : GRoutine Γx :=
  loop (.work (.cnt .copy2)) (seq (popOne (.work (.cnt .copy2))) (emit chunk))

theorem loopEmit2_exits (chunk : List Instr) (x xk : List Γx) (n q m t tpb g w pw c1 : ℕ)
    (k : ℕ) (sk : List Instr) :
    (loopEmit2 (Γx := Γx) chunk).Exits (emitStacks x xk n q m t tpb g w pw c1 k sk) (3 * k + 1)
      (emitStacks x xk n q m t tpb g w pw c1 0 ((List.replicate k chunk).flatten.reverse ++ sk)) := by
  have key := loop_exits (Γ := GAlphabet Γx) (.work (.cnt .copy2))
    (seq (popOne (.work (.cnt .copy2))) (emit chunk)) k
    (fun i => emitStacks x xk n q m t tpb g w pw c1 (k - i)
      ((List.replicate i chunk).flatten.reverse ++ sk)) (fun _ => 2) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 2) k = 3 * k + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using key
  · intro i hi
    have pop := popOne_exits (Γ := GAlphabet Γx) (.work (.cnt .copy2))
      (emitStacks x xk n q m t tpb g w pw c1 (k - i) ((List.replicate i chunk).flatten.reverse ++ sk))
    have hpop : Function.update (emitStacks x xk n q m t tpb g w pw c1 (k - i)
        ((List.replicate i chunk).flatten.reverse ++ sk)) (.work (.cnt .copy2))
        (emitStacks x xk n q m t tpb g w pw c1 (k - i)
          ((List.replicate i chunk).flatten.reverse ++ sk) (.work (.cnt .copy2))).tail =
        emitStacks x xk n q m t tpb g w pw c1 (k - (i + 1))
          ((List.replicate i chunk).flatten.reverse ++ sk) := by
      estacks_ext
      rw [show k - i = (k - (i + 1)) + 1 by omega, marks, List.replicate_succ, List.tail_cons]
      rfl
    rw [hpop] at pop
    have em := emit_exits (Γx := Γx) chunk x xk n q m t tpb g w pw c1 (k - (i + 1))
      ((List.replicate i chunk).flatten.reverse ++ sk)
    have := seq_exits _ _ pop em
    convert this using 2
    simp [List.replicate_succ', List.flatten_append, List.reverse_append]
  · intro i hi
    simp [emitStacks, marks, List.replicate_eq_nil_iff]; omega
  · simp [emitStacks]

/-- Emit a chunk once per input symbol, consuming the input. -/
def loopInput (f : Γx → List Instr) : GRoutine Γx :=
  loop .input (dispatch .input fun s => emit (f s))

theorem loopInput_exits (f : Γx → List Instr) (x xk : List Γx) (n q m t tpb g w pw c1 c2 : ℕ)
    (sk : List Instr) :
    (loopInput (Γx := Γx) f).Exits (emitStacks x xk n q m t tpb g w pw c1 c2 sk) (3 * x.length + 1)
      (emitStacks [] xk n q m t tpb g w pw c1 c2 ((x.map f).flatten.reverse ++ sk)) := by
  have key := loop_exits (Γ := GAlphabet Γx) .input (dispatch .input fun s => emit (f s)) x.length
    (fun i => emitStacks (x.drop i) xk n q m t tpb g w pw c1 c2
      (((x.take i).map f).flatten.reverse ++ sk)) (fun _ => 2) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 2) x.length = 3 * x.length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using key
  · intro i hi
    have hsplit : (x.drop i) = x[i] :: x.drop (i + 1) := List.drop_eq_getElem_cons hi
    have em := emit_exits (Γx := Γx) (f x[i]) (x.drop (i + 1)) xk n q m t tpb g w pw c1 c2
      (((x.take i).map f).flatten.reverse ++ sk)
    have hupd : Function.update (emitStacks (x.drop i) xk n q m t tpb g w pw c1 c2
        (((x.take i).map f).flatten.reverse ++ sk)) .input (x.drop (i + 1)) =
        emitStacks (x.drop (i + 1)) xk n q m t tpb g w pw c1 c2
          (((x.take i).map f).flatten.reverse ++ sk) := by estacks_ext
    rw [← hupd] at em
    have body := dispatch_exits (Γ := GAlphabet Γx) .input (fun s => emit (f s))
      (emitStacks (x.drop i) xk n q m t tpb g w pw c1 c2 (((x.take i).map f).flatten.reverse ++ sk))
      x[i] (x.drop (i + 1)) hsplit em
    convert body using 2
    dsimp only
    simp only [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
      Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.reverse_append, List.append_assoc]
  · intro i hi
    simp [emitStacks, List.drop_eq_nil_iff]; omega
  · simp [emitStacks]

/-- Copy the generic-cell counter onto the second loop copy. -/
def copyG2 : GRoutine Γx := copyWork (.cnt .g) (.cnt .copy2) .scratch

theorem copyG2_exits (x xk : List Γx) (n q m t tpb g w pw c1 : ℕ) (sk : List Instr) :
    (copyG2 (Γx := Γx)).Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk) (4 * g + 2)
      (emitStacks x xk n q m t tpb g w pw c1 g sk) := by
  have := copyWork_exits (Γx := Γx) (.cnt .g) (.cnt .copy2) .scratch (by decide) (by decide)
    (by decide) (emitStacks x xk n q m t tpb g w pw c1 0 sk) rfl
  convert this using 1
  · simp [emitStacks]
  · estacks_ext

/-- Copy a counter onto the second loop copy. -/
def copyTo2 (c : Counter) : GRoutine Γx := copyWork (.cnt c) (.cnt .copy2) .scratch

theorem copyTo2_q_exits (x xk : List Γx) (n q m t tpb g w pw c1 : ℕ) (sk : List Instr) :
    (copyTo2 (Γx := Γx) .q).Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk) (4 * q + 2)
      (emitStacks x xk n q m t tpb g w pw c1 q sk) := by
  have := copyWork_exits (Γx := Γx) (.cnt .q) (.cnt .copy2) .scratch (by decide) (by decide)
    (by decide) (emitStacks x xk n q m t tpb g w pw c1 0 sk) rfl
  convert this using 1
  · simp [emitStacks]
  · estacks_ext

theorem copyTo2_tpb_exits (x xk : List Γx) (n q m t tpb g w pw c1 : ℕ) (sk : List Instr) :
    (copyTo2 (Γx := Γx) .tpb).Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk) (4 * tpb + 2)
      (emitStacks x xk n q m t tpb g w pw c1 tpb sk) := by
  have := copyWork_exits (Γx := Γx) (.cnt .tpb) (.cnt .copy2) .scratch (by decide) (by decide)
    (by decide) (emitStacks x xk n q m t tpb g w pw c1 0 sk) rfl
  convert this using 1
  · simp [emitStacks]
  · estacks_ext

/-- Copy the horizon counter onto the first loop copy. -/
def copyT1 : GRoutine Γx := copyWork (.cnt .t) (.cnt .copy1) .scratch

theorem copyT1_exits (x xk : List Γx) (n q m t tpb g w pw c2 : ℕ) (sk : List Instr) :
    (copyT1 (Γx := Γx)).Exits (emitStacks x xk n q m t tpb g w pw 0 c2 sk) (4 * t + 2)
      (emitStacks x xk n q m t tpb g w pw t c2 sk) := by
  have := copyWork_exits (Γx := Γx) (.cnt .t) (.cnt .copy1) .scratch (by decide) (by decide)
    (by decide) (emitStacks x xk n q m t tpb g w pw 0 c2 sk) rfl
  convert this using 1
  · simp [emitStacks]
  · estacks_ext

/-- Sequence a routine over a list of stacks. -/
def foldStacks {K : Type} (L : List K) (f : K → GRoutine Γx) : GRoutine Γx :=
  L.foldr (fun k r => seq (f k) r) skip

omit [Fintype Γx] [DecidableEq Γx] in
theorem foldStacks_append {K : Type} (L₁ L₂ : List K) (f : K → GRoutine Γx) :
    foldStacks (L₁ ++ L₂) f = L₁.foldr (fun k r => seq (f k) r) (foldStacks L₂ f) := by
  simp [foldStacks, List.foldr_append]

/-- A routine that only emits chunks, with the second copy empty before and
after; the chunks and the cost may depend on the generic-cell counter. -/
def EmitsOnly (r : GRoutine Γx) (chunks : ℕ → List Instr) (cost : ℕ → ℕ) : Prop :=
  ∀ (x xk : List Γx) (n q m t tpb g w pw c1 : ℕ) (sk : List Instr),
    r.Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk) (cost g)
      (emitStacks x xk n q m t tpb g w pw c1 0 ((chunks g).reverse ++ sk))

theorem emitsOnly_seq {r₁ r₂ : GRoutine Γx} {ch₁ ch₂ : ℕ → List Instr} {c₁ c₂ : ℕ → ℕ}
    (h₁ : EmitsOnly r₁ ch₁ c₁) (h₂ : EmitsOnly r₂ ch₂ c₂) :
    EmitsOnly (seq r₁ r₂) (fun g => ch₁ g ++ ch₂ g) (fun g => c₁ g + c₂ g) := by
  intro x xk n q m t tpb g w pw c1 sk
  have := seq_exits _ _ (h₁ x xk n q m t tpb g w pw c1 sk)
    (h₂ x xk n q m t tpb g w pw c1 ((ch₁ g).reverse ++ sk))
  simpa [List.reverse_append, List.append_assoc] using this

theorem emitsOnly_skip : EmitsOnly (Γx := Γx) skip (fun _ => []) (fun _ => 1) := by
  intro x xk n q m t tpb g w pw c1 sk
  simpa using skip_exits (emitStacks x xk n q m t tpb g w pw c1 0 sk)

theorem emitsOnly_emit (chunk : List Instr) :
    EmitsOnly (Γx := Γx) (emit chunk) (fun _ => chunk) (fun _ => 1) :=
  fun x xk n q m t tpb g w pw c1 sk => emit_exits chunk x xk n q m t tpb g w pw c1 0 sk

theorem emitsOnly_emitList (cs : List (List Instr)) :
    EmitsOnly (Γx := Γx) (emitList cs) (fun _ => cs.flatten) (fun _ => cs.length + 1) :=
  fun x xk n q m t tpb g w pw c1 sk => emitList_exits cs x xk n q m t tpb g w pw c1 0 sk

/-- Emit a chunk `G` times through the second copy. -/
def emitG (chunk : List Instr) : GRoutine Γx := seq copyG2 (loopEmit2 chunk)

theorem emitsOnly_emitG (chunk : List Instr) :
    EmitsOnly (Γx := Γx) (emitG chunk) (fun g => (List.replicate g chunk).flatten)
      (fun g => 7 * g + 3) := by
  intro x xk n q m t tpb g w pw c1 sk
  have := seq_exits _ _ (copyG2_exits x xk n q m t tpb g w pw c1 sk)
    (loopEmit2_exits chunk x xk n q m t tpb g w pw c1 g sk)
  convert this using 1
  dsimp only
  omega

/-- Emit a chunk `G - 1` times through the second copy. -/
def emitGpred (chunk : List Instr) : GRoutine Γx :=
  seq copyG2 (seq (popOne (.work (.cnt .copy2))) (loopEmit2 chunk))

theorem emitsOnly_emitGpred (chunk : List Instr) :
    EmitsOnly (Γx := Γx) (emitGpred chunk) (fun g => (List.replicate (g - 1) chunk).flatten)
      (fun g => 4 * g + 2 + (1 + (3 * (g - 1) + 1))) := by
  intro x xk n q m t tpb g w pw c1 sk
  have pop := popOne_exits (Γ := GAlphabet Γx) (.work (.cnt .copy2))
    (emitStacks x xk n q m t tpb g w pw c1 g sk)
  have hpop : Function.update (emitStacks x xk n q m t tpb g w pw c1 g sk) (.work (.cnt .copy2))
      (emitStacks x xk n q m t tpb g w pw c1 g sk (.work (.cnt .copy2))).tail =
      emitStacks x xk n q m t tpb g w pw c1 (g - 1) sk := by
    estacks_ext
    cases g <;> simp [marks, List.replicate_succ]
  rw [hpop] at pop
  exact seq_exits _ _ (copyG2_exits x xk n q m t tpb g w pw c1 sk)
    (seq_exits _ _ pop (loopEmit2_exits chunk x xk n q m t tpb g w pw c1 (g - 1) sk))

theorem emitsOnly_foldStacks {K : Type} (L : List K) (f : K → GRoutine Γx)
    (chunks : K → ℕ → List Instr) (cost : K → ℕ → ℕ)
    (h : ∀ k ∈ L, EmitsOnly (f k) (chunks k) (cost k)) :
    EmitsOnly (foldStacks L f) (fun g => L.flatMap fun k => chunks k g)
      (fun g => (L.map fun k => cost k g).sum + 1) := by
  induction L with
  | nil => simpa [foldStacks] using emitsOnly_skip
  | cons k L ih =>
      have := emitsOnly_seq (h k (by simp)) (ih fun k' hk' => h k' (by simp [hk']))
      simp only [foldStacks, List.foldr_cons, List.flatMap_cons, List.map_cons, List.sum_cons]
      convert this using 1

omit [Fintype Γx] [DecidableEq Γx] in
/-- A prefix of emit-only routines before a routine with an arbitrary
effect on the input stack. -/
theorem foldr_emitsOnly_prefix {K : Type} (pre : List K) (f : K → GRoutine Γx)
    (chunks : K → ℕ → List Instr) (cost : K → ℕ → ℕ)
    (h : ∀ k ∈ pre, EmitsOnly (f k) (chunks k) (cost k)) (r₀ : GRoutine Γx)
    (x x' xk : List Γx) (n q m t tpb g w pw c1 : ℕ) (c₀ : ℕ) (ch₀ : List Instr)
    (h₀ : ∀ sk, r₀.Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk) c₀
      (emitStacks x' xk n q m t tpb g w pw c1 0 (ch₀.reverse ++ sk))) :
    ∀ sk, (pre.foldr (fun k r => seq (f k) r) r₀).Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk)
      ((pre.map fun k => cost k g).sum + c₀)
      (emitStacks x' xk n q m t tpb g w pw c1 0
        (((pre.flatMap fun k => chunks k g) ++ ch₀).reverse ++ sk)) := by
  induction pre with
  | nil => intro sk; simpa using h₀ sk
  | cons k pre ih =>
      intro sk
      have first := h k (by simp) x xk n q m t tpb g w pw c1 sk
      have rest := ih (fun k' hk' => h k' (by simp [hk'])) ((chunks k g).reverse ++ sk)
      have := seq_exits _ _ first rest
      simp only [List.foldr_cons, List.flatMap_cons, List.map_cons, List.sum_cons]
      convert this using 1
      · omega
      · simp [List.reverse_append, List.append_assoc]

/-! ### Repeating an emitter once per mark of the `t` counter -/

/-- Run `r` once per mark on the `t` counter, working on a copy of that counter. -/
def loopRounds (r : GRoutine Γx) : GRoutine Γx :=
  seq copyT1 (loop (.work (.cnt .copy1)) (seq (popOne (.work (.cnt .copy1))) r))

def loopRoundsCost (cost : ℕ → ℕ) (t g : ℕ) : ℕ :=
  4 * t + 2 + loopSteps (fun _ => 1 + cost g) t

theorem loopRounds_exits (r : GRoutine Γx) (chunks : ℕ → List Instr) (cost : ℕ → ℕ)
    (h : EmitsOnly r chunks cost) (x xk : List Γx) (n q m t tpb g w pw : ℕ) (sk : List Instr) :
    (loopRounds r).Exits (emitStacks x xk n q m t tpb g w pw 0 0 sk) (loopRoundsCost cost t g)
      (emitStacks x xk n q m t tpb g w pw 0 0
        ((List.replicate t (chunks g)).flatten.reverse ++ sk)) := by
  generalize hJ : chunks g = J
  have copy := copyT1_exits (Γx := Γx) x xk n q m t tpb g w pw 0 sk
  have body : ∀ i < t, (seq (popOne (.work (.cnt .copy1))) r).Exits
      (emitStacks x xk n q m t tpb g w pw (t - i) 0 ((List.replicate i J).flatten.reverse ++ sk))
      (1 + cost g)
      (emitStacks x xk n q m t tpb g w pw (t - (i + 1)) 0
        ((List.replicate (i + 1) J).flatten.reverse ++ sk)) := by
    intro i hi
    have pop := popOne_exits (Γ := GAlphabet Γx) (.work (.cnt .copy1))
      (emitStacks x xk n q m t tpb g w pw (t - i) 0 ((List.replicate i J).flatten.reverse ++ sk))
    have hpop : Function.update (emitStacks x xk n q m t tpb g w pw (t - i) 0
        ((List.replicate i J).flatten.reverse ++ sk)) (.work (.cnt .copy1))
        (emitStacks x xk n q m t tpb g w pw (t - i) 0
          ((List.replicate i J).flatten.reverse ++ sk) (.work (.cnt .copy1))).tail =
        emitStacks x xk n q m t tpb g w pw (t - (i + 1)) 0
          ((List.replicate i J).flatten.reverse ++ sk) := by
      estacks_ext
      rw [show t - i = (t - (i + 1)) + 1 by omega, marks, List.replicate_succ, List.tail_cons]
      rfl
    rw [hpop] at pop
    have round := h x xk n q m t tpb g w pw (t - (i + 1)) ((List.replicate i J).flatten.reverse ++ sk)
    rw [hJ] at round
    have hS : J.reverse ++ ((List.replicate i J).flatten.reverse ++ sk) =
        (List.replicate (i + 1) J).flatten.reverse ++ sk := by
      simp only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.reverse_append, List.append_assoc]
    rw [hS] at round
    exact seq_exits _ _ pop round
  have key := loop_exits (Γ := GAlphabet Γx) (.work (.cnt .copy1))
    (seq (popOne (.work (.cnt .copy1))) r) t
    (fun i => emitStacks x xk n q m t tpb g w pw (t - i) 0 ((List.replicate i J).flatten.reverse ++ sk))
    (fun _ => 1 + cost g) body
    (fun i hi => by
      show marks (t - i) ≠ []
      simp only [marks, ne_eq, List.replicate_eq_nil_iff]
      omega)
    (by show marks (t - t) = []; rw [Nat.sub_self]; rfl)
  dsimp only at key
  rw [Nat.sub_zero, Nat.sub_self, List.replicate_zero, List.flatten_nil, List.reverse_nil,
    List.nil_append] at key
  exact seq_exits _ _ copy key

end LeanNPHardness.TableauStacks
