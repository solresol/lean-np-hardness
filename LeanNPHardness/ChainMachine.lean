import LeanNPHardness.ChainJob
import LeanNPHardness.TableauGenerator
import LeanNPHardness.CookLevinHardness

/-!
# Exact 3-SAT in the unary encoding is NP-hard

The splitter machine reads the unary encoding of a formula, emits one fixed
instruction chunk per symbol (`ChainJob.chunk`) through the generator's
input loop, interprets the job, and leaves the unary encoding of
`Chain.chainThree F` on the output stack (`splitter_exits`). It runs in at
most `10000 * (n + 1) ^ 2` steps for input length `n` (`cost_le`), so
`chainThree` is a checked polynomial-time reduction from unary CNF-SAT to
unary exact 3-SAT, and `encodedUnaryExactThreeSAT_NPHard` follows from
`CookLevin.encodedUnarySAT_NPHard`.
-/

namespace LeanNPHardness.ChainMachine

open Turing Computability CNF CNF.Unary CNF.Chain TableauJobs TableauStacks Routines ChainJob StateTransition
  Polynomial MachinePrimitives

/-- The register stacks drained after interpretation. -/
def regStacks : List GStack :=
  [.work (.reg .base), .work (.reg .win), .work (.reg .w), .work (.reg .pw)]

/-- The splitter routine. -/
def splitter : GRoutine Sym :=
  seq (emit open0) <| seq (loopInput chunk) <| seq (emit close) <|
  seq (moveAll .skel .job id .mark) <| seq (pushList (.work (.reg .base)) [.mark]) <|
  seq (pushList (.work (.reg .w)) [.mark]) <| seq interpret <|
  seq (drainAll regStacks) (moveAll (.work .buf) (.work .output) id .mark)

/-- The empty generator stacks. -/
def E : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 []

/-- The registers after interpretation. -/
def finalRegs (F : Formula ℕ) : Regs := (render initRegs (job (encode F))).2

/-- Exact steps of the splitter. -/
def cost (F : Formula ℕ) : ℕ :=
  1 + ((3 * (encode F).length + 1) + (1 + ((2 * (job (encode F)).length + 1) + (1 + (1 +
    (interpSteps initRegs (job (encode F)) +
      (((2 * finalRegs F .base + 1) + ((2 * finalRegs F .win + 1) + ((2 * finalRegs F .w + 1) +
        ((2 * finalRegs F .pw + 1) + 1)))) + (2 * (encode (chainThree F)).length + 1))))))))

theorem splitter_exits (F : Formula ℕ) :
    splitter.Exits (paramStacks (encode F) [] 0 0 0 0 0 0 0 0) (cost F)
      (outputStacks (encode (chainThree F))) := by
  set x := encode F with hx
  rw [paramStacks_eq_emitStacks]
  have s1 := emit_exits (Γx := Sym) open0 x [] 0 0 0 0 0 0 0 0 0 0 []
  have s2 := loopInput_exits (Γx := Sym) chunk x [] 0 0 0 0 0 0 0 0 0 0 (open0.reverse ++ [])
  have s3 := emit_exits (Γx := Sym) close [] [] 0 0 0 0 0 0 0 0 0 0
    ((x.map chunk).flatten.reverse ++ (open0.reverse ++ []))
  have hsk : close.reverse ++ ((x.map chunk).flatten.reverse ++ (open0.reverse ++ [])) =
      (job x).reverse := by
    simp [job, body, List.reverse_append, List.append_assoc]
  rw [hsk] at s3
  set S₃ : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 (job x).reverse with hS₃
  have s4 := moveAll_exits (Γ := GAlphabet Sym) .skel .job (by decide) id .mark S₃
  have hlen4 : (S₃ .skel).length = (job x).length := by simp [hS₃, emitStacks]
  rw [hlen4] at s4
  have s5 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .base)) [.mark]
    (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
  have s6 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .w)) [.mark]
    (Function.update
      (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
      (.work (.reg .base))
      ([.mark] ++ Function.update (Function.update S₃ .skel []) .job
        (((S₃ .skel).map id).reverse ++ S₃ .job) (.work (.reg .base))))
  have h6 : Function.update
      (Function.update
        (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
        (.work (.reg .base))
        ([.mark] ++ Function.update (Function.update S₃ .skel []) .job
          (((S₃ .skel).map id).reverse ++ S₃ .job) (.work (.reg .base))))
      (.work (.reg .w))
      ([.mark] ++ Function.update
        (Function.update (Function.update S₃ .skel []) .job (((S₃ .skel).map id).reverse ++ S₃ .job))
        (.work (.reg .base))
        ([.mark] ++ Function.update (Function.update S₃ .skel []) .job
          (((S₃ .skel).map id).reverse ++ S₃ .job) (.work (.reg .base))) (.work (.reg .w))) =
      interpStacks E (job x) [] initRegs := by
    funext k
    rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
      (try rcases r with _ | _ | _ | _) <;>
      (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
      simp [hS₃, E, emitStacks, interpStacks, initRegs, marks, Function.update_of_ne]
  rw [h6] at s6
  have s7 := interpret_exits E rfl (job x) (fun i hi => ok_of_tame (tame_job x i hi)) [] initRegs
  rw [hx, render_job, List.append_nil] at s7
  set S₇ := interpStacks E [] (encode (chainThree F)).reverse (finalRegs F) with hS₇
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
      outputStacks (encode (chainThree F)) := by
    funext k
    rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
      (try rcases r with _ | _ | _ | _) <;>
      (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
      simp [hS₈, hS₇, regStacks, E, emitStacks, interpStacks, outputStacks, Function.update_of_ne]
  have hlen9 : (S₈ (.work .buf)).length = (encode (chainThree F)).length := by
    simp [hS₈, hS₇, regStacks, interpStacks]
  rw [h9, hlen9] at s9
  exact seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4 (seq_exits _ _ s5
    (seq_exits _ _ s6 (seq_exits _ _ s7 (seq_exits _ _ s8 s9)))))))

/-! ### The time bound -/

theorem cost_le (F : Formula ℕ) : cost F ≤ 10000 * ((encode F).length + 1) ^ 2 := by
  set n := (encode F).length with hn
  set L := (job (encode F)).length with hL
  have hLn : L ≤ 27 * n + 18 := job_length_le _
  have hpre : PrefixLE (L + 1) initRegs (job (encode F)) :=
    prefixLE_tame _ _ (tame_job _) rfl _ fun r => by
      cases r <;> simp [initRegs, hL] <;> omega
  have hint := interpSteps_le _ _ hpre
  have hout := render_fst_length_le _ _ hpre
  rw [render_job] at hout
  have hR := hpre.finish
  have hb := hR .base
  have hwin := hR .win
  have hw := hR .w
  have hpw := hR .pw
  simp only [cost, finalRegs]
  have hA : (4 * (L + 1) + 4) * L ≤ 4 * (27 * n + 20) * (27 * n + 18) := by
    have : 4 * (L + 1) + 4 ≤ 4 * (27 * n + 20) := by omega
    exact Nat.mul_le_mul this hLn
  have hB : (L + 1 + 1) * L ≤ (27 * n + 20) * (27 * n + 18) :=
    Nat.mul_le_mul (by omega) hLn
  rw [← hL] at hint hout
  nlinarith

/-- The time polynomial of the splitter. -/
noncomputable def timePoly : Polynomial ℕ := C 10000 * (X + 1) ^ 2

/-- The splitter computes `chainThree` in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Unary.finEncoding CNF.Unary.finEncoding chainThree where
  tm := toGenMachine splitter
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun F := by
    have run := evalsToInTimeMono (toGenMachine_outputsInTime _ _ _ _ (splitter_exits F))
      (show cost F ≤ timePoly.eval (encode F).length by
        simp only [timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact cost_le F)
    simpa [Equiv.refl] using! run

/-- The checked polynomial-time reduction from unary SAT to unary exact 3-SAT. -/
noncomputable def reduction : encodedUnarySAT.PolytimeReducesTo encodedUnaryExactThreeSAT where
  map := chainThree
  correct F := by
    show F.Satisfiable ↔ 0 < 3 ∧ (chainThree F).ExactWidth 3 ∧ (chainThree F).Satisfiable
    rw [satisfiable_chainThree]
    exact ⟨fun h => ⟨by norm_num, exactWidth_chainThree F, h⟩, fun h => h.2.2⟩
  polytime := ⟨computableInPolyTime⟩

/-- Exact 3-SAT under the unary-index encoding is NP-hard. -/
theorem encodedUnaryExactThreeSAT_NPHard : encodedUnaryExactThreeSAT.NPHard :=
  EncodedLanguage.NPHard.of_reduction reduction CookLevin.encodedUnarySAT_NPHard

end LeanNPHardness.ChainMachine
