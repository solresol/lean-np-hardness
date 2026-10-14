import LeanNPHardness.MachineTableauBoundary
import LeanNPHardness.CNFEncoding
import LeanNPHardness.CNFSplitting

/-!
# Cook--Levin: the semantic reduction from NP to SAT

For an encoded language with a polynomial-time verifier over Boolean-string
certificates, the Cook--Levin tableau of the verifier machine on an input is
satisfiable exactly when some certificate within the polynomial bound is
accepted. `reduction` packages this as a semantic many-one reduction to
`CNF.SAT`. The polynomial-time TM2 machine computing the tableau from the
input, and hence NP-hardness of SAT in the library's definition, remain
separate obligations.
-/

namespace LeanNPHardness.CookLevin

open Turing Computability CNF MachineTableau MachinePaddedRun EncodedLanguage

variable {α : Type} {problem : EncodedLanguage α}

/-- The tableau instance of a verifier machine on an input: the horizon is
the machine's time bound at the longest allowed paired input, and the
required output is the machine's encoding of `true`. -/
noncomputable def tableauInstance (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
    (computer : TM2ComputableInPolyTime
      (PairEncoding.finEncoding problem.encoding certificateEncoding)
      finEncodingBoolBool verify) (x : α) : Instance where
  tm := computer.tm
  extra := [computer.outputAlphabet.invFun true]
  inputLength := (problem.encoding.encode x).length
  certBound := bound.eval (problem.encoding.encode x).length
  horizon := computer.time.eval
    ((problem.encoding.encode x).length + bound.eval (problem.encoding.encode x).length)
  input := (problem.encoding.encode x).map fun s => computer.inputAlphabet.invFun (Sum.inl s)
  input_length := by simp
  certSym b := computer.inputAlphabet.invFun (Sum.inr b)
  certSym_injective := fun b b' h => Sum.inr.inj (computer.inputAlphabet.symm.injective h)
  output := [computer.outputAlphabet.invFun true]
  output_mem := fun s hs => hs
  output_short := by simp

variable (verify : α × List Bool → Bool) (bound : Polynomial ℕ)
  (computer : TM2ComputableInPolyTime
    (PairEncoding.finEncoding problem.encoding certificateEncoding)
    finEncodingBoolBool verify) (x : α)

/-- The machine's input list for a paired input is the prefix followed by
the certificate symbols. -/
theorem machineInput (bits : List Bool) :
    List.map computer.inputAlphabet.invFun
        ((PairEncoding.finEncoding problem.encoding certificateEncoding).encode (x, bits)) =
      (tableauInstance verify bound computer x).input ++
        bits.map (tableauInstance verify bound computer x).certSym := by
  simp [tableauInstance, PairEncoding.finEncoding_encode,
    MachinePrimitives.RawBoolList.finEncoding, List.map_append, List.map_map, Function.comp_def]

theorem machineOutput (b : Bool) :
    List.map computer.outputAlphabet.invFun (finEncodingBoolBool.encode b) =
      [computer.outputAlphabet.invFun b] := by
  simp [finEncodingBoolBool, encodeBool]

/-- The paired input length is at most the input length plus the certificate bound. -/
theorem pairedLength_le (bits : List Bool)
    (hbits : bits.length ≤ bound.eval (problem.encoding.encode x).length) :
    ((PairEncoding.finEncoding problem.encoding certificateEncoding).encode (x, bits)).length ≤
      (problem.encoding.encode x).length + bound.eval (problem.encoding.encode x).length := by
  simp only [PairEncoding.finEncoding_encode_length, certificateEncoding,
    MachinePrimitives.RawBoolList.encode_eq]
  omega

/-- The tableau is satisfiable exactly when some certificate within the bound
is accepted by the verifier. -/
theorem tableau_satisfiable_iff :
    (tableauInstance verify bound computer x).tableau.Satisfiable ↔
      ∃ bits : List Bool, bits.length ≤ bound.eval (problem.encoding.encode x).length ∧
        verify (x, bits) = true := by
  rw [Instance.tableau_satisfiable_iff]
  constructor
  · rintro ⟨bits, hbits, hrun⟩
    refine ⟨bits, hbits, ?_⟩
    simp only [Instance.initCfg, Instance.finalCfg] at hrun
    rw [iterate_padStep_eq_haltList_iff] at hrun
    obtain ⟨s, _, hrun⟩ := hrun
    obtain ⟨⟨s', hsteps⟩, _⟩ := computer.outputsFun (x, bits)
    rw [machineInput verify bound computer x, machineOutput verify computer,
      Option.map_some] at hsteps
    have huniq := run_halt_unique computer.tm _ _ _ s s' hrun hsteps rfl rfl
    have hstk := congrArg (fun c : computer.tm.Cfg => c.stk computer.tm.k₁) huniq.2
    have hself : ∀ l : List (computer.tm.Γ computer.tm.k₁),
        (haltList computer.tm l).stk computer.tm.k₁ = l := by
      intro l; simp [haltList]
    change (haltList computer.tm [computer.outputAlphabet.invFun true]).stk computer.tm.k₁ =
      (haltList computer.tm [computer.outputAlphabet.invFun (verify (x, bits))]).stk
        computer.tm.k₁ at hstk
    rw [hself, hself] at hstk
    have hsym : computer.outputAlphabet.invFun true =
        computer.outputAlphabet.invFun (verify (x, bits)) :=
      List.singleton_inj.mp hstk
    exact (computer.outputAlphabet.symm.injective hsym).symm
  · rintro ⟨bits, hbits, hv⟩
    refine ⟨bits, hbits, ?_⟩
    simp only [Instance.initCfg, Instance.finalCfg]
    rw [iterate_padStep_eq_haltList_iff]
    obtain ⟨⟨s, hsteps⟩, hle⟩ := computer.outputsFun (x, bits)
    refine ⟨s, ?_, ?_⟩
    · exact hle.trans (MachineRuntime.polynomial_eval_mono _
        (pairedLength_le bound x bits hbits))
    · rw [machineInput verify bound computer x, machineOutput verify computer,
        Option.map_some, hv] at hsteps
      exact hsteps

/-- The Cook--Levin formula of a verifier on an input. -/
noncomputable def formula : Formula ℕ :=
  (tableauInstance verify bound computer x).tableau

theorem formula_satisfiable_iff :
    (formula verify bound computer x).Satisfiable ↔
      ∃ bits : List Bool, bits.length ≤ bound.eval (problem.encoding.encode x).length ∧
        verify (x, bits) = true :=
  tableau_satisfiable_iff verify bound computer x

/-- Correctness of the Cook--Levin reduction for a checked verifier. -/
theorem accepts_iff_sat (V : PolytimeVerifier problem)
    (computer : TM2ComputableInPolyTime
      (PairEncoding.finEncoding problem.encoding certificateEncoding)
      finEncodingBoolBool V.verify) (x : α) :
    problem.accepts x ↔ SAT (formula V.verify V.certificateBound computer x) := by
  rw [V.accepts_iff_exists_certificate x]
  exact (formula_satisfiable_iff V.verify V.certificateBound computer x).symm

/-- The semantic Cook--Levin reduction from an NP language to SAT. The
verifier machine is chosen from the verifier's polynomial-time witness. -/
noncomputable def reduction (V : PolytimeVerifier problem) :
    ManyOneReduction problem.accepts SAT where
  map x := formula V.verify V.certificateBound (Classical.choice V.polytime) x
  correct x := accepts_iff_sat V (Classical.choice V.polytime) x

/-- Every language in NP semantically reduces to SAT. -/
theorem inNP_reducesTo_sat (h : problem.InNP) :
    Nonempty (ManyOneReduction problem.accepts SAT) :=
  h.map fun V => reduction V

/-- The semantic reduction from an NP language to exact 3-SAT: the
Cook--Levin tableau followed by clause splitting and padding. -/
noncomputable def reductionToExactThree (V : PolytimeVerifier problem) :
    ManyOneReduction problem.accepts ExactThreeSAT :=
  (reduction V).comp satToExactThree

/-- Every language in NP semantically reduces to exact 3-SAT. -/
theorem inNP_reducesTo_exactThreeSAT (h : problem.InNP) :
    Nonempty (ManyOneReduction problem.accepts ExactThreeSAT) :=
  h.map fun V => reductionToExactThree V

end LeanNPHardness.CookLevin
