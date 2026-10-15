import LeanNPHardness.MaxCutVerifyMachine
import LeanNPHardness.VerifierTransport

/-!
# NP-completeness under the unary-index encoding

Each unary language re-encodes to its binary counterpart by a checked
polynomial-time machine, and NP membership pulls back along such
reductions (`EncodedLanguage.InNP.of_reduction`). With the unary hardness
results this gives NP-completeness of CNF-SAT, exact 3-SAT and Max-Cut
under the unary-index encoding, whose variable and vertex indices are
polynomial in the input size.
-/

namespace LeanNPHardness.UnaryNPComplete

open CNF CNF.Unary MaxCut

/-- Unary CNF-SAT is NP-complete. -/
theorem encodedUnarySAT_NPComplete : encodedUnarySAT.NPComplete :=
  ⟨CookLevin.encodedUnarySAT_NPHard,
    EncodedLanguage.InNP.of_reduction BinaryConvert.satReduction SatVerify.encodedSAT_inNP⟩

/-- Unary exact 3-SAT is NP-complete. -/
theorem encodedUnaryExactThreeSAT_NPComplete : encodedUnaryExactThreeSAT.NPComplete :=
  ⟨ChainMachine.encodedUnaryExactThreeSAT_NPHard,
    EncodedLanguage.InNP.of_reduction BinaryConvert.exactThreeReduction
      ExactThreeVerify.encodedExactThreeSAT_inNP⟩

/-- Unary Max-Cut is NP-complete. -/
theorem encodedUnaryMaxCut_NPComplete : encodedUnaryMaxCut.NPComplete :=
  ⟨MaxCutMachine.encodedUnaryMaxCut_NPHard,
    EncodedLanguage.InNP.of_reduction MaxCutMachine.binaryReduction MaxCutVerify.encodedMaxCut_inNP⟩

end LeanNPHardness.UnaryNPComplete
