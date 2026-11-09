import LeanNPHardness.CountHeaderMachine

/-!
# Variable extraction from a complete encoded clause

Load the clause's framed binary literal count, then consume exactly its
literal frames. Input and output suffixes survive unchanged; every occurrence
is retained in reverse order. The bound is polynomial in the complete clause
encoding, which bounds both the binary header length and its numeric count.

This is a routine contract for canonical clauses. Source-order restoration,
formula traversal, malformed-input rejection and standalone packaging remain
separate obligations.
-/

namespace LeanNPHardness.MachinePrimitives.CountedClause

open Computability Routines
open CountedLiteralBody (contents)

def routine : Routine CountedLiteralBody.Alphabet :=
  seq CountHeader.routine CountedLiteralBody.routine

/-- The header's bound plus the exact counted-body cost. -/
def runBound (literals : List (CNF.Literal Nat)) : Nat :=
  (encodeNat literals.length).length * (5 * literals.length + 8) + 3 +
    CountedLiteralBody.runSteps (literals.map (fun l => encodeNat l.toNat))

/-- Consume one full encoded clause and retain every following formula bit. -/
theorem clause_exits (literals : List (CNF.Literal Nat)) (input output : List Bool) :
    routine.ExitsLE
      (contents (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat) ++ input)
        [] [] output [])
      (runBound literals)
      (contents input [] []
        (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output) []) := by
  have load := CountHeader.natural_exits literals.length
    (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat) ++ input) output
  have body := CountedLiteralBody.literal_body_exits literals input output
  simpa only [routine, runBound, BinaryNatLists.encodeNatList, List.length_map,
    List.flatMap_map, Function.comp_def, List.append_assoc] using
    seq_exitsLE _ _ load body.le

/-- Every occurrence occupies at least one bit, even positive zero. -/
theorem count_le_body_length (literals : List (CNF.Literal Nat)) :
    literals.length ≤
      (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length := by
  induction literals with
  | nil => simp
  | cons l literals ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        BinaryNatLists.encodeNat, BinaryNatLists.frame_length] at ih ⊢
      omega

/-- Bound decoding by the complete clause size, not just the binary header size. -/
theorem runBound_le (literals : List (CNF.Literal Nat)) :
    runBound literals ≤
      let N := (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length
      N * (5 * N + 15) + 4 := by
  let N := (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length
  let B := (literals.flatMap (fun l => BinaryNatLists.encodeNat l.toNat)).length
  have hN : N = 2 * (encodeNat literals.length).length + 1 + B := by
    simp only [N, B, BinaryNatLists.encodeNatList, List.length_append, List.length_map,
      List.flatMap_map, BinaryNatLists.encodeNat, BinaryNatLists.frame_length]
  have hb : (encodeNat literals.length).length ≤ N := by omega
  have hB : B ≤ N := by omega
  have hm : literals.length ≤ N := (count_le_body_length literals).trans hB
  have hc := CountedLiteralBody.runSteps_le (literals.map (fun l => encodeNat l.toNat))
  have hbody : CountedLiteralBody.runSteps (literals.map (fun l => encodeNat l.toNat)) ≤
      7 * B + 1 := by
    simpa only [B, List.flatMap_map, Function.comp_def, BinaryNatLists.encodeNat] using hc
  have hh := Nat.mul_le_mul hb (show 5 * literals.length + 8 ≤ 5 * N + 8 by omega)
  change runBound literals ≤ N * (5 * N + 15) + 4
  unfold runBound
  nlinarith

/-- Polynomial routine bound in original clause bits, independent of both suffixes. -/
theorem clause_exitsLE (literals : List (CNF.Literal Nat)) (input output : List Bool) :
    routine.ExitsLE
      (contents (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat) ++ input)
        [] [] output [])
      (let N := (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length;
        N * (5 * N + 15) + 4)
      (contents input [] []
        (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output) []) :=
  (clause_exits literals input output).mono (runBound_le literals)

/-- Removing the count header and polarity bits cannot increase the output size. -/
theorem output_length_le (literals : List (CNF.Literal Nat)) (output : List Bool) :
    (literals.reverse.flatMap (fun l => BinaryNatLists.encodeNat l.var) ++ output).length ≤
      (BinaryNatLists.encodeNatList (literals.map CNF.Literal.toNat)).length + output.length := by
  have h := CountedLiteralBody.literal_output_length_le literals output
  simp only [BinaryNatLists.encodeNatList, List.length_map, List.flatMap_map,
    List.length_append] at h ⊢
  omega

end LeanNPHardness.MachinePrimitives.CountedClause
