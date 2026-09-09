import LeanNPHardness.MachineCompositionRuntime

/-!
Reusable encoding and machine components extracted from `phd-thesis-lean`
commit `84be78db5a287f9a40dcb549252063d6db67de73`. Runtime bounds retain
the original explicit finite-alphabet input encodings.
-/

namespace LeanNPHardness.MachinePrimitives

open Computability Turing
open LeanNPHardness.MachineComposition

def evalsToInTimeMono {configuration : Type*}
    {step : configuration → Option configuration}
    {start : configuration} {finish : Option configuration} {m n : ℕ}
    (h : EvalsToInTime step start finish m) (hmn : m ≤ n) :
    EvalsToInTime step start finish n where
  toEvalsTo := h.toEvalsTo
  steps_le_m := h.steps_le_m.trans hmn


theorem replicate_true_append_cons (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

end LeanNPHardness.MachinePrimitives
