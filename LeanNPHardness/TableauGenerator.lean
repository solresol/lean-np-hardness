import LeanNPHardness.TableauTemplateInstance
import LeanNPHardness.TableauParameters
import LeanNPHardness.TableauInterpreter

/-!
# The Cook--Levin generator

The generator is one routine over the generator stacks: it materializes the
parameters from the input, emits the reversed skeleton, moves it to the job
stack, interprets it onto the buffer, drains the counters and registers,
and moves the buffer to the output stack. `generator_exits` is its exact run
from the initial stacks of a machine input to the halting stacks holding
the unary encoding of the tableau, with an exact step count
`generatorCost`.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary TableauJobs MachineLocality MachineTableau Turing

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx]

/-! ### Every skeleton instruction is handled as specified -/

theorem ok_of_mem_litJob (d : LitDesc) : ∀ i ∈ litJob d, i.ok := by
  intro i hi
  simp only [litJob, List.mem_cons, List.mem_append, List.mem_map, List.mem_replicate] at hi
  rcases hi with rfl | ⟨r, _, rfl⟩ | ⟨_, rfl⟩ <;> trivial

theorem ok_of_mem_clauseJob (c : ClauseDesc) : ∀ i ∈ clauseJob c, i.ok := by
  intro i hi
  simp only [clauseJob, List.mem_append, List.mem_flatMap, List.mem_singleton] at hi
  rcases hi with ⟨d, _, hd⟩ | rfl
  · exact ok_of_mem_litJob d i hd
  · trivial

theorem ok_of_mem_formulaJob (f : FormulaDesc) : ∀ i ∈ formulaJob f, i.ok := by
  intro i hi
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hi
  exact ok_of_mem_clauseJob c i hc

theorem ok_of_mem_roundStart : ∀ i ∈ roundStart, i.ok := by
  intro i hi
  simp only [roundStart, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [Instr.ok]

theorem ok_of_mem_cellStep : ∀ i ∈ cellStep, i.ok := by
  intro i hi
  simp only [cellStep, List.mem_singleton] at hi
  subst hi
  simp [Instr.ok]

theorem ok_of_mem_roundEnd (D : ℕ) : ∀ i ∈ roundEnd D, i.ok := by
  intro i hi
  simp only [roundEnd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at hi
  rcases hi with (rfl | rfl) | ⟨_, rfl⟩ <;> simp [Instr.ok]

theorem ok_of_mem_cellsJob (ds : List FormulaDesc) : ∀ i ∈ cellsJob ds, i.ok := by
  intro i hi
  obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hi
  rcases List.mem_append.mp hd with h | h
  · exact ok_of_mem_formulaJob d i h
  · exact ok_of_mem_cellStep i h

theorem ok_of_mem_headJob (I : Instance) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) :
    ∀ i ∈ I.headJob d0 d1 dd, i.ok := by
  intro i hi
  simp only [Instance.headJob, List.mem_append, List.mem_flatMap] at hi
  rcases hi with (h | h) | ⟨g, _, h⟩
  · exact ok_of_mem_formulaJob d0 i h
  · exact ok_of_mem_formulaJob d1 i h
  · exact ok_of_mem_formulaJob (dd (g + 2)) i h

theorem ok_of_mem_openRound (I : Instance) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc) : ∀ i ∈ I.openRound d0 d1 dd f, i.ok := by
  intro i hi
  simp only [Instance.openRound, List.mem_append] at hi
  rcases hi with (h | h) | h
  · exact ok_of_mem_roundStart i h
  · exact ok_of_mem_headJob I d0 d1 dd i h
  · exact ok_of_mem_cellsJob _ i h

theorem ok_of_mem_roundJob (I : Instance) (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc)
    (f : I.tm.K → ℕ → FormulaDesc) : ∀ i ∈ I.roundJob d0 d1 dd f, i.ok := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact ok_of_mem_openRound I d0 d1 dd f i h
  · exact ok_of_mem_roundEnd I.D i h

/-- Every instruction of the skeleton is handled as specified: register
additions always use distinct registers. -/
theorem skeleton_ok (I : Instance) : ∀ i ∈ I.skeleton, i.ok := by
  intro i hi
  simp only [Instance.skeleton, List.mem_append, List.mem_flatMap] at hi
  rcases hi with (h | ⟨_, _, h⟩) | h
  · exact ok_of_mem_openRound I _ _ _ _ i h
  · exact ok_of_mem_roundJob I _ _ _ _ i h
  · exact ok_of_mem_openRound I _ _ _ _ i h

/-! ### Draining a list of stacks -/

/-- Drain the listed stacks in order. -/
def drainAll : List GStack → GRoutine Γx
  | [] => skip
  | k :: L => seq (drain k) (drainAll L)

/-- Steps of `drainAll`, computed on the stacks being drained. -/
def drainAllCost : List GStack → Stacks (GAlphabet Γx) → ℕ
  | [], _ => 1
  | k :: L, S => (2 * (S k).length + 1) + drainAllCost L (Function.update S k [])

omit [Fintype Γx] [DecidableEq Γx] in
theorem drainAll_exits (L : List GStack) (S : Stacks (GAlphabet Γx)) :
    (drainAll L).Exits S (drainAllCost L S) (fun k => if k ∈ L then [] else S k) := by
  induction L generalizing S with
  | nil =>
      have := skip_exits S
      simpa [drainAll, drainAllCost] using this
  | cons k L ih =>
      have h1 := drain_exits k S
      have h2 := ih (Function.update S k [])
      have := seq_exits _ _ h1 h2
      convert this using 1
      funext k'
      by_cases hk : k' = k
      · subst hk
        simp
      · simp [hk]

/-- The stacks that still hold marks after interpretation. -/
def cleanupStacks : List GStack :=
  [.work (.reg .base), .work (.reg .win), .work (.reg .w), .work (.reg .pw),
    .work (.cnt .n), .work (.cnt .q), .work (.cnt .m), .work (.cnt .t), .work (.cnt .tpb),
    .work (.cnt .g)]

/-! ### The generator -/

/-- The generator routine for a template instance `T` and an input
conversion `conv`; the polynomials and constants are the parameter stage's. -/
noncomputable def generator (bound time : Polynomial ℕ) (pb D width : ℕ) (T : Instance)
    (conv : Γx → T.tm.Γ T.tm.k₀) : GRoutine Γx :=
  seq (parameterStage bound time pb D width)
    (seq (T.emitter conv)
      (seq (moveAll .skel .job id .mark)
        (seq interpret
          (seq (drainAll cleanupStacks) (moveAll (.work .buf) (.work .output) id .mark)))))

/-- The halting stacks: only the output stack is nonempty. -/
def outputStacks (out : List Sym) : Stacks (GAlphabet Γx)
  | .work .output => out
  | _ => []

/-- Steps of the cleanup for an instance with input length `n`. -/
noncomputable def cleanupCost (I : Instance) (n : ℕ) : ℕ :=
  let R := (render I.initRegs I.skeleton).2
  (2 * R .base + 1) + ((2 * R .win + 1) + ((2 * R .w + 1) + ((2 * R .pw + 1) +
    ((2 * n + 1) + ((2 * I.certBound + 1) + ((2 * (n + I.certBound) + 1) +
      ((2 * I.horizon + 1) + ((2 * (I.horizon * I.pb) + 1) + ((2 * I.G + 1) + 1)))))))))

/-- Exact steps of the generator on an input of length `n`. -/
noncomputable def generatorCost (I : Instance) (bound time : Polynomial ℕ) (n : ℕ) : ℕ :=
  parameterCost bound time I.pb I.D I.width n +
    (I.emitterCost n + ((2 * I.skeleton.length + 1) +
      (interpSteps I.initRegs I.skeleton +
        (cleanupCost I n + (2 * (encode I.tableau).length + 1)))))

/-- The generator's exact run: from the input alone to the encoded tableau alone. -/
theorem generator_exits (I : Instance) (conv : Γx → I.tm.Γ I.tm.k₀)
    (bound time : Polynomial ℕ) (x : List Γx) (hx : I.input = x.map conv)
    (hq : I.certBound = bound.eval x.length)
    (ht : I.horizon = time.eval (x.length + bound.eval x.length)) :
    (generator bound time I.pb I.D I.width I.template conv).Exits
      (paramStacks x [] 0 0 0 0 0 0 0 0) (generatorCost I bound time x.length)
      (outputStacks (encode I.tableau)) := by
  have hn : I.inputLength = x.length := by rw [← I.input_length, hx, List.length_map]
  have hG : I.G = x.length + I.certBound + I.horizon * I.pb + 2 := by
    simp only [Params.G, hn]
  rw [paramStacks_eq_emitStacks]
  -- parameters
  have s1 := parameterStage_exits (Γx := Γx) bound time I.pb I.D I.width x
  rw [← ht, ← hq, show I.pb * I.horizon = I.horizon * I.pb from Nat.mul_comm _ _, ← hG,
    ← I.P_eq, paramStacks_eq_emitStacks, paramStacks_eq_emitStacks] at s1
  -- skeleton
  have s2 := I.emitter_exits conv x hx (x.length + I.certBound) I.width (I.P * I.width)
  rw [← I.emitter_template conv] at s2
  -- move the skeleton to the job stack
  set S₂ : Stacks (GAlphabet Γx) :=
    emitStacks [] [] x.length I.certBound (x.length + I.certBound) I.horizon (I.horizon * I.pb)
      I.G I.width (I.P * I.width) 0 0 I.skeleton.reverse with hS₂
  set S₃ : Stacks (GAlphabet Γx) :=
    emitStacks [] [] x.length I.certBound (x.length + I.certBound) I.horizon (I.horizon * I.pb)
      I.G I.width (I.P * I.width) 0 0 [] with hS₃
  have s3 := moveAll_exits (Γ := GAlphabet Γx) .skel .job (by decide) id .mark S₂
  have h3 : Function.update (Function.update S₂ .skel []) .job
      (((S₂ .skel).map id).reverse ++ S₂ .job) = interpStacks S₃ I.skeleton [] I.initRegs := by
    funext k
    rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
      (try rcases r with _ | _ | _ | _) <;>
      (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
      simp [hS₂, hS₃, emitStacks, interpStacks, Instance.initRegs, marks, Function.update_of_ne]
  have hlen3 : (S₂ .skel).length = I.skeleton.length := by
    simp [hS₂, emitStacks]
  rw [h3, hlen3] at s3
  -- interpret
  have s4 := interpret_exits S₃ rfl I.skeleton (skeleton_ok I) [] I.initRegs
  rw [I.render_skeleton, List.append_nil] at s4
  -- cleanup
  set R := (render I.initRegs I.skeleton).2 with hR
  set S₄ : Stacks (GAlphabet Γx) := interpStacks S₃ [] (encode I.tableau).reverse R with hS₄
  have s5 := drainAll_exits cleanupStacks S₄
  have hcost5 : drainAllCost cleanupStacks S₄ = cleanupCost I x.length := by
    simp [drainAllCost, cleanupStacks, cleanupCost, hS₄, interpStacks, hS₃, emitStacks, marks,
      ← hR]
  rw [hcost5] at s5
  -- output
  set S₅ : Stacks (GAlphabet Γx) := fun k => if k ∈ cleanupStacks then [] else S₄ k with hS₅
  have s6 := moveAll_exits (Γ := GAlphabet Γx) (.work .buf) (.work .output) (by decide) id .mark S₅
  have h6 : Function.update (Function.update S₅ (.work .buf) []) (.work .output)
      (((S₅ (.work .buf)).map id).reverse ++ S₅ (.work .output)) =
      outputStacks (encode I.tableau) := by
    funext k
    rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
      (try rcases r with _ | _ | _ | _) <;>
      (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
      simp [hS₅, hS₄, hS₃, cleanupStacks, emitStacks, interpStacks, outputStacks, marks,
        Function.update_of_ne]
  have hlen6 : (S₅ (.work .buf)).length = (encode I.tableau).length := by
    simp [hS₅, hS₄, cleanupStacks, interpStacks]
  rw [h6, hlen6] at s6
  exact seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4
    (seq_exits _ _ s5 s6))))

/-! ### The generator as a machine -/

/-- The machine of a generator-stack routine: input on `input`, output on
`work output`. -/
noncomputable def toGenMachine (r : GRoutine Γx) : FinTM2 := toMachine r .input (.work .output)

omit [DecidableEq Γx] in
theorem initList_toGenMachine_stk (r : GRoutine Γx) (x : List Γx) :
    (initList (toGenMachine r) x).stk = paramStacks x [] 0 0 0 0 0 0 0 0 := by
  funext k
  rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    rfl

omit [DecidableEq Γx] in
theorem haltList_toGenMachine_stk (r : GRoutine Γx) (out : List Sym) :
    (haltList (toGenMachine r) out).stk = outputStacks out := by
  funext k
  rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    rfl

/-- A generator-stack routine running from the input alone to the output
alone is a time-bounded machine output. -/
noncomputable def toGenMachine_outputsInTime (r : GRoutine Γx) (x : List Γx) (out : List Sym)
    (n : ℕ) (h : r.Exits (paramStacks x [] 0 0 0 0 0 0 0 0) n (outputStacks out)) :
    TM2OutputsInTime (toGenMachine r) x (some out) n :=
  toMachine_outputsInTime r .input (.work .output) x out n
    (by
      have h1 := initList_toGenMachine_stk r x
      have h2 := haltList_toGenMachine_stk r out
      simp only [toGenMachine] at h1 h2
      rw [h1, h2]
      exact h)

end LeanNPHardness.TableauStacks
