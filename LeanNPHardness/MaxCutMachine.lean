import LeanNPHardness.MaxCutJob
import LeanNPHardness.ChainMachine
import LeanNPHardness.BinaryConvertMachine

/-!
# Max-Cut is NP-hard

The Max-Cut machine streams the gadget job of a unary formula through the
generator's input loop and interpreter (`mcMachineR_exits`), within
`10⁶ (n + 1)²` steps (`cost_le`). Composed with the chain reduction (whose
output always has exactly three literals per clause) this is a checked
polynomial-time reduction from unary CNF-SAT to unary Max-Cut
(`satReduction`, `encodedUnaryMaxCut_NPHard`). Re-encoding instances in
binary with the CNF converter gives `encodedMaxCut_NPHard`.
-/

namespace LeanNPHardness.MaxCutMachine

open Turing Computability CNF CNF.Unary CNF.Chain TableauJobs TableauStacks Routines MaxCut StateTransition
  MaxCutJob Polynomial MachinePrimitives

/-! ### Instruction validity and register bounds -/

/-- Instructions that are pure, increment a non-`w` register by `w`, or clear `win`. -/
def TameM (i : Instr) : Prop :=
  i.pure ∨ i = .addTo .base .w ∨ i = .addTo .win .w ∨ i = .addTo .pw .w ∨ i = .clear .win

theorem ok_of_tameM {i : Instr} (h : TameM i) : i.ok := by
  rcases h with h | rfl | rfl | rfl | rfl
  · rcases i with _ | _ | _ | _ | ⟨d, s⟩ | _ <;> trivial
  all_goals simp [Instr.ok]

/-- A decidable check for `TameM`. -/
def tameB : Instr → Bool
  | .addTo d s => (s == .w) && (d == .base || d == .win || d == .pw)
  | .clear r => r == .win
  | _ => true

theorem tameM_of_tameB (i : Instr) (h : tameB i = true) : TameM i := by
  rcases i with b | r | _ | _ | ⟨d, s⟩ | r
  · exact Or.inl trivial
  · exact Or.inl trivial
  · exact Or.inl trivial
  · exact Or.inl trivial
  · cases d <;> cases s <;> simp [tameB] at h <;> simp [TameM]
  · cases r <;> simp [tameB] at h; simp [TameM]

theorem tameM_chunk (s : Sym) : ∀ i ∈ chunk s, TameM i := by
  have : (chunk s).all tameB = true := by cases s <;> decide
  intro i hi
  exact tameM_of_tameB i (List.all_eq_true.mp this i hi)

theorem tameM_job (L : List Sym) : ∀ i ∈ job L, TameM i := by
  intro i hi
  simp only [job, body, List.mem_append, List.mem_flatten, List.mem_map] at hi
  rcases hi with (h | ⟨_, ⟨s, _, rfl⟩, h⟩) | h
  · exact tameM_of_tameB i (List.all_eq_true.mp (by decide : openPend.all tameB = true) i h)
  · exact tameM_chunk s i h
  · exact tameM_of_tameB i (List.all_eq_true.mp (by decide : suffix.all tameB = true) i h)

theorem render_tameM (J : List Instr) : ∀ R : Regs, (∀ i ∈ J, TameM i) → R .w = 1 →
    (∀ r, (render R J).2 r ≤ R r + J.length) ∧ (render R J).2 .w = 1 := by
  induction J with
  | nil => intro R _ hw; simp [render, hw]
  | cons i J ih =>
      intro R hJ hw
      have hJ' : ∀ j ∈ J, TameM j := fun j hj => hJ j (List.mem_cons_of_mem _ hj)
      have step : (∀ r, (renderInstr R i).2 r ≤ R r + 1) ∧ (renderInstr R i).2 .w = 1 := by
        rcases hJ i (List.mem_cons_self ..) with hp | rfl | rfl | rfl | rfl
        · rw [renderInstr_pure_snd R i hp]; exact ⟨fun r => by omega, hw⟩
        all_goals
          refine ⟨fun r => ?_, ?_⟩ <;>
            (simp only [renderInstr, Function.update_apply]; split_ifs <;> simp_all)
      obtain ⟨h1, h2⟩ := ih (renderInstr R i).2 hJ' step.2
      refine ⟨fun r => ?_, by simpa [render] using h2⟩
      have := h1 r
      have := step.1 r
      simp only [render, List.length_cons]
      omega

theorem prefixLE_tameM (J : List Instr) (R : Regs) (hJ : ∀ i ∈ J, TameM i) (hw : R .w = 1)
    (M : ℕ) (hM : ∀ r, R r + J.length ≤ M) : PrefixLE M R J := by
  intro i hi r
  have := (render_tameM (J.take i) R (fun j hj => hJ j (List.mem_of_mem_take hj)) hw).1 r
  have hk : (J.take i).length ≤ J.length := by simp
  have := hM r
  omega

theorem chunk_length_le (s : Sym) : (chunk s).length ≤ 200 := by
  cases s <;> simp only [chunk, fixedJob, eBB, eB1, vB, openPend, posEdge, openPos, openNeg, incr,
    List.length_append, List.length_cons, List.length_replicate, List.length_nil,
    List.cons_append, List.nil_append] <;> omega

theorem job_length_le (L : List Sym) : (job L).length ≤ 200 * L.length + 30 := by
  have : (body L).length ≤ 200 * L.length := by
    induction L with
    | nil => simp [body]
    | cons s L ih =>
        have := chunk_length_le s
        simp only [body, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
        simp only [List.length_cons]
        omega
  have h1 : openPend.length = 19 := by decide
  have h2 : suffix.length = 5 := by decide
  simp only [job, List.length_append, h1, h2]
  omega

/-! ### The machine -/

/-- The register stacks drained after interpretation. -/
def regStacks : List GStack :=
  [.work (.reg .base), .work (.reg .win), .work (.reg .w), .work (.reg .pw)]

/-- The mcMachineR routine. -/
def mcMachineR : GRoutine Sym :=
  seq (emit openPend) <| seq (loopInput chunk) <| seq (emit suffix) <|
  seq (moveAll .skel .job id .mark) <| seq (pushList (.work (.reg .base)) [.mark, .mark, .mark]) <|
  seq (pushList (.work (.reg .w)) [.mark]) <| seq interpret <|
  seq (drainAll regStacks) (moveAll (.work .buf) (.work .output) id .mark)

/-- The empty generator stacks. -/
def E : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 []

/-- The registers after interpretation. -/
def finalRegs (F : Formula ℕ) : Regs := (render initRegs (job (encode F))).2

/-- Exact steps of the mcMachineR. -/
def cost (F : Formula ℕ) : ℕ :=
  1 + ((3 * (encode F).length + 1) + (1 + ((2 * (job (encode F)).length + 1) + (1 + (1 +
    (interpSteps initRegs (job (encode F)) +
      (((2 * finalRegs F .base + 1) + ((2 * finalRegs F .win + 1) + ((2 * finalRegs F .w + 1) +
        ((2 * finalRegs F .pw + 1) + 1)))) + (2 * (unaryEncoding.encode (gadget F)).length + 1))))))))

theorem mcMachineR_exits (F : Formula ℕ) :
    mcMachineR.Exits (paramStacks (encode F) [] 0 0 0 0 0 0 0 0) (cost F)
      (outputStacks (unaryEncoding.encode (gadget F))) := by
  set x := encode F with hx
  rw [paramStacks_eq_emitStacks]
  have s1 := emit_exits (Γx := Sym) openPend x [] 0 0 0 0 0 0 0 0 0 0 []
  have s2 := loopInput_exits (Γx := Sym) chunk x [] 0 0 0 0 0 0 0 0 0 0 (openPend.reverse ++ [])
  have s3 := emit_exits (Γx := Sym) suffix [] [] 0 0 0 0 0 0 0 0 0 0
    ((x.map chunk).flatten.reverse ++ (openPend.reverse ++ []))
  have hsk : suffix.reverse ++ ((x.map chunk).flatten.reverse ++ (openPend.reverse ++ [])) =
      (job x).reverse := by
    simp [job, body, List.reverse_append, List.append_assoc]
  rw [hsk] at s3
  set S₃ : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 (job x).reverse with hS₃
  have s4 := moveAll_exits (Γ := GAlphabet Sym) .skel .job (by decide) id .mark S₃
  have hlen4 : (S₃ .skel).length = (job x).length := by simp [hS₃, emitStacks]
  rw [hlen4] at s4
  have s5 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .base)) [.mark, .mark, .mark]
    (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
  have s6 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .w)) [.mark]
    (Function.update
      (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
      (.work (.reg .base))
      ([.mark, .mark, .mark] ++ Function.update (Function.update S₃ .skel []) .job
        (((S₃ .skel).map id).reverse ++ S₃ .job) (.work (.reg .base))))
  have h6 : Function.update
      (Function.update
        (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
        (.work (.reg .base))
        ([.mark, .mark, .mark] ++ Function.update (Function.update S₃ .skel []) .job
          (((S₃ .skel).map id).reverse ++ S₃ .job) (.work (.reg .base))))
      (.work (.reg .w))
      ([.mark] ++ Function.update
        (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
        (.work (.reg .base))
        ([.mark, .mark, .mark] ++ Function.update (Function.update S₃ .skel []) .job
          (((S₃ .skel).map id).reverse ++ S₃ .job) (.work (.reg .base))) (.work (.reg .w))) =
      interpStacks E (job x) [] initRegs := by
    funext k
    rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
      (try rcases r with _ | _ | _ | _) <;>
      (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
      simp [hS₃, E, emitStacks, interpStacks, initRegs, regs4, marks, Function.update_of_ne]
  rw [h6] at s6
  have s7 := interpret_exits E rfl (job x) (fun i hi => ok_of_tameM (tameM_job x i hi)) [] initRegs
  rw [hx, render_job, List.append_nil] at s7
  set S₇ := interpStacks E [] (unaryEncoding.encode (gadget F)).reverse (finalRegs F) with hS₇
  have s8 := drainAll_exits regStacks S₇
  have hcost8 : drainAllCost regStacks S₇ =
      (2 * finalRegs F .base + 1) + ((2 * finalRegs F .win + 1) + ((2 * finalRegs F .w + 1) +
        ((2 * finalRegs F .pw + 1) + 1))) := by
    simp [drainAllCost, regStacks, hS₇, interpStacks, marks]
  rw [hcost8] at s8
  set S₈ : Stacks (GAlphabet Sym) := fun k => if k ∈ regStacks then [] else S₇ k with hS₈
  have s9 := moveAll_exits (Γ := GAlphabet Sym) (.work .buf) (.work .output) (by decide) id .mark S₈
  have h9 : Function.update (Function.update S₈ (.work .buf) []) (.work .output)
      (((S₈ (.work .buf)).map id).reverse ++ S₈ (.work .output)) =
      outputStacks (unaryEncoding.encode (gadget F)) := by
    funext k
    rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
      (try rcases r with _ | _ | _ | _) <;>
      (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
      simp [hS₈, hS₇, regStacks, E, emitStacks, interpStacks, outputStacks, Function.update_of_ne]
  have hlen9 : (S₈ (.work .buf)).length = (unaryEncoding.encode (gadget F)).length := by
    simp [hS₈, hS₇, regStacks, interpStacks]
  rw [h9, hlen9] at s9
  exact seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4 (seq_exits _ _ s5
    (seq_exits _ _ s6 (seq_exits _ _ s7 (seq_exits _ _ s8 s9)))))))

/-! ### The time bound -/

theorem cost_le (F : Formula ℕ) : cost F ≤ 1000000 * ((encode F).length + 1) ^ 2 := by
  set n := (encode F).length with hn
  set L := (job (encode F)).length with hL
  have hLn : L ≤ 200 * n + 30 := job_length_le _
  have hpre : PrefixLE (L + 3) initRegs (job (encode F)) :=
    prefixLE_tameM _ _ (tameM_job _) rfl _ fun r => by
      cases r <;> simp [initRegs, regs4, hL] <;> omega
  have hint := interpSteps_le _ _ hpre
  have hout := render_fst_length_le _ _ hpre
  rw [render_job] at hout
  have hR := hpre.finish
  have hb := hR .base
  have hwin := hR .win
  have hw := hR .w
  have hpw := hR .pw
  simp only [cost, finalRegs]
  have hA : (4 * (L + 3) + 4) * L ≤ 4 * (200 * n + 34) * (200 * n + 30) := by
    have : 4 * (L + 3) + 4 ≤ 4 * (200 * n + 34) := by omega
    exact Nat.mul_le_mul this hLn
  have hB : (L + 3 + 1) * L ≤ (200 * n + 34) * (200 * n + 30) :=
    Nat.mul_le_mul (by omega) hLn
  rw [← hL] at hint hout
  nlinarith

/-- The time polynomial of the Max-Cut machine. -/
noncomputable def timePoly : Polynomial ℕ := C 1000000 * (X + 1) ^ 2

/-- The gadget is computed in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Unary.finEncoding unaryEncoding gadget where
  tm := toGenMachine mcMachineR
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun F := by
    have run := evalsToInTimeMono (toGenMachine_outputsInTime _ _ _ _ (mcMachineR_exits F))
      (show cost F ≤ timePoly.eval (encode F).length by
        simp only [timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact cost_le F)
    simpa [Equiv.refl] using! run

/-- The checked reduction from unary SAT to unary Max-Cut: the chain
reduction followed by the gadget. -/
noncomputable def satReduction : encodedUnarySAT.PolytimeReducesTo encodedUnaryMaxCut where
  map := gadget ∘ chainThree
  correct F := by
    show F.Satisfiable ↔ MaxCutLang (gadget (chainThree F))
    rw [← satisfiable_chainThree]
    exact sat_iff_maxCut_gadget _ (exactWidth_chainThree F)
  polytime := ⟨MachineComposition.compositionComputableInPolyTime CNF.Unary.finEncoding CNF.Unary.finEncoding
    unaryEncoding chainThree gadget ChainMachine.computableInPolyTime computableInPolyTime⟩

/-- Max-Cut under the unary-index encoding is NP-hard. -/
theorem encodedUnaryMaxCut_NPHard : encodedUnaryMaxCut.NPHard :=
  EncodedLanguage.NPHard.of_reduction satReduction CookLevin.encodedUnarySAT_NPHard

/-- Re-encoding Max-Cut instances in binary, in polynomial time. -/
noncomputable def binaryComputable :
    TM2ComputableInPolyTime unaryEncoding binaryEncoding id where
  tm := BinaryConvert.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := BinaryConvert.timePoly
  outputsFun p := by
    have run := toMachine_outputsInTime_le BinaryConvert.conv .input .out
      (encode (graphFormula p.1 p.2)) (Formula.encode (graphFormula p.1 p.2)) _
      (by
        have h1 := BinaryConvert.initList_eq (encode (graphFormula p.1 p.2))
        have h2 := BinaryConvert.haltList_eq (Formula.encode (graphFormula p.1 p.2))
        simp only [BinaryConvert.machine] at h1 h2
        rw [h1, h2]
        exact BinaryConvert.conv_exits _)
    have run' := evalsToInTimeMono run
      (show BinaryConvert.convBound (encode (graphFormula p.1 p.2)).length ≤
          BinaryConvert.timePoly.eval (encode (graphFormula p.1 p.2)).length by
        simp only [BinaryConvert.timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact BinaryConvert.convBound_le _)
    simpa [Equiv.refl, unaryEncoding, binaryEncoding] using! run'

/-- Unary Max-Cut reduces to binary Max-Cut by re-encoding. -/
noncomputable def binaryReduction : encodedUnaryMaxCut.PolytimeReducesTo encodedMaxCut where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨binaryComputable⟩

/-- Max-Cut under the binary CNF-style encoding is NP-hard. -/
theorem encodedMaxCut_NPHard : encodedMaxCut.NPHard :=
  EncodedLanguage.NPHard.of_reduction binaryReduction encodedUnaryMaxCut_NPHard

end LeanNPHardness.MaxCutMachine
