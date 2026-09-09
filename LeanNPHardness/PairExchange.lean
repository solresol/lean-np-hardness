import LeanNPHardness.PairReductionComputable

namespace LeanNPHardness.PairExchange

open Computability Turing

inductive Stack
  | input | left | right | output
  deriving DecidableEq, Fintype

inductive Label (Γ Δ : Type)
  | scan | scanPush (symbol : Option (Sum Γ Δ))
  | left | leftPush (symbol : Option (Sum Γ Δ))
  | right | rightPush (symbol : Option (Sum Γ Δ))
  deriving DecidableEq, Fintype

private abbrev Alphabet (Γ Δ : Type) (_ : Stack) := Sum Γ Δ

/-- Carry popped symbols in finite labels, so even empty alphabets need no
chosen default symbol. Exchange component order; the output alphabet
isomorphism exchanges the tags. -/
def program {Γ Δ : Type} : Label Γ Δ →
    TM2.Stmt (Alphabet Γ Δ) (Label Γ Δ) (Option (Sum Γ Δ))
  | .scan => .pop .input (fun _ symbol => symbol) (.goto Label.scanPush)
  | .scanPush none => .goto (fun _ => .left)
  | .scanPush (some (.inl symbol)) =>
      .push .left (fun _ => .inl symbol) (.goto (fun _ => .scan))
  | .scanPush (some (.inr symbol)) =>
      .push .right (fun _ => .inr symbol) (.goto (fun _ => .scan))
  | .left => .pop .left (fun _ symbol => symbol) (.goto Label.leftPush)
  | .leftPush none => .goto (fun _ => .right)
  | .leftPush (some symbol) => .push .output (fun _ => symbol) (.goto (fun _ => .left))
  | .right => .pop .right (fun _ symbol => symbol) (.goto Label.rightPush)
  | .rightPush none => .halt
  | .rightPush (some symbol) => .push .output (fun _ => symbol) (.goto (fun _ => .right))

/-- Four finite-alphabet stacks suffice for both directions of section exchange. -/
def computer (Γ Δ : Type) [Fintype Γ] [Fintype Δ] : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Γ Δ
  Λ := Label Γ Δ
  main := .scan
  σ := Option (Sum Γ Δ)
  initialState := none
  Γk₀Fin := inferInstance
  m := program

variable {Γ Δ : Type} [Fintype Γ] [Fintype Δ]

private def stackContents (input left right output : List (Sum Γ Δ)) :
    (k : Stack) → List (Alphabet Γ Δ k)
  | .input => input | .left => left | .right => right | .output => output

private def cfg (label : Option (Label Γ Δ)) (state : Option (Sum Γ Δ))
    (input left right output : List (Sum Γ Δ)) : (computer Γ Δ).Cfg :=
  ⟨label, state, stackContents input left right output⟩

private abbrev Run (a b : (computer Γ Δ).Cfg) (time : ℕ) :=
  EvalsToInTime (computer Γ Δ).step a (some b) time

private def one {a b : (computer Γ Δ).Cfg} (h : (computer Γ Δ).step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : (computer Γ Δ).Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans (computer Γ Δ).step m n a b (some c) h h'

local macro "exchange_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (source left right output : List (Sum Γ Δ)) (state : Option (Sum Γ Δ)) :
    Run (cfg (some .scan) state source left right output)
      (cfg (some .left) none []
        ((LeanNPHardness.PairEncoding.leftSymbols source).reverse.map Sum.inl ++ left)
        ((LeanNPHardness.PairEncoding.rightSymbols source).reverse.map Sum.inr ++ right)
        output) (2 * source.length + 2) := by
  induction source generalizing left right state with
  | nil =>
      change Run (cfg (some .scan) state [] left right output)
        (cfg (some .left) none [] left right output) 2
      exact seq (b := cfg (some (.scanPush none)) none [] left right output)
        (one (by exchange_step)) (one (by exchange_step))
  | cons symbol source ih =>
      cases symbol with
      | inl symbol =>
          have h : Run (cfg (some .scan) state (.inl symbol :: source) left right output)
              (cfg (some .scan) (some (.inl symbol)) source (.inl symbol :: left) right output)
              2 := seq (one (by exchange_step)) (one (by exchange_step))
          simpa [LeanNPHardness.PairEncoding.leftSymbols,
            LeanNPHardness.PairEncoding.rightSymbols, List.reverse_cons,
            List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm, Nat.mul_add] using seq h (ih (.inl symbol :: left) right _)
      | inr symbol =>
          have h : Run (cfg (some .scan) state (.inr symbol :: source) left right output)
              (cfg (some .scan) (some (.inr symbol)) source left (.inr symbol :: right) output)
              2 := seq (one (by exchange_step)) (one (by exchange_step))
          simpa [LeanNPHardness.PairEncoding.leftSymbols,
            LeanNPHardness.PairEncoding.rightSymbols, List.reverse_cons,
            List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm, Nat.mul_add] using seq h (ih left (.inr symbol :: right) _)

private def left_run (left right output : List (Sum Γ Δ)) (state : Option (Sum Γ Δ)) :
    Run (cfg (some .left) state [] left right output)
      (cfg (some .right) none [] [] right (left.reverse ++ output))
      (2 * left.length + 2) := by
  induction left generalizing output state with
  | nil =>
      change Run (cfg (some .left) state [] [] right output)
        (cfg (some .right) none [] [] right output) 2
      exact seq (b := cfg (some (.leftPush none)) none [] [] right output)
        (one (by exchange_step)) (one (by exchange_step))
  | cons symbol left ih =>
      have h : Run (cfg (some .left) state [] (symbol :: left) right output)
          (cfg (some .left) (some symbol) [] left right (symbol :: output)) 2 :=
        seq (one (by exchange_step)) (one (by exchange_step))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using seq h (ih (symbol :: output) _)

private def right_run (right output : List (Sum Γ Δ)) (state : Option (Sum Γ Δ)) :
    Run (cfg (some .right) state [] [] right output)
      (cfg none none [] [] [] (right.reverse ++ output)) (2 * right.length + 2) := by
  induction right generalizing output state with
  | nil =>
      change Run (cfg (some .right) state [] [] [] output)
        (cfg none none [] [] [] output) 2
      exact seq (b := cfg (some (.rightPush none)) none [] [] [] output)
        (one (by exchange_step)) (one (by exchange_step))
  | cons symbol right ih =>
      have h : Run (cfg (some .right) state [] [] (symbol :: right) output)
          (cfg (some .right) (some symbol) [] [] right (symbol :: output)) 2 :=
        seq (one (by exchange_step)) (one (by exchange_step))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using seq h (ih (symbol :: output) _)

private theorem init_eq (input : List (Sum Γ Δ)) :
    initList (computer Γ Δ) input = cfg (some .scan) none input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List (Sum Γ Δ)) :
    haltList (computer Γ Δ) output = cfg none none [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

/-- Canonical component-order exchange in at most `4s+6` steps, for arbitrary
finite component alphabets, including empty alphabets and empty words. -/
def outputsInTime (left : List Γ) (right : List Δ) :
    TM2OutputsInTime (computer Γ Δ) (left.map Sum.inl ++ right.map Sum.inr)
      (some (right.map Sum.inr ++ left.map Sum.inl))
      (4 * (left.length + right.length) + 6) := by
  have hscan := scan_run (left.map Sum.inl ++ right.map Sum.inr) [] [] [] none
  simp only [PairEncoding.leftSymbols_append, PairEncoding.rightSymbols_append,
    PairEncoding.leftSymbols_map_inl, PairEncoding.leftSymbols_map_inr,
    PairEncoding.rightSymbols_map_inl, PairEncoding.rightSymbols_map_inr,
    List.nil_append, List.append_nil, List.length_append, List.length_map] at hscan
  have hleft := left_run (left.reverse.map Sum.inl) (right.reverse.map Sum.inr) [] none
  have hright := right_run (right.reverse.map Sum.inr) (left.map Sum.inl) none
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil] at hscan hleft hright
  have h := seq (seq hscan hleft) hright
  rw [TM2OutputsInTime, init_eq]
  simp only [Option.map_some]
  rw [halt_eq]
  convert h using 1
  simp only [List.length_reverse, List.length_map]
  omega

/-- Exchange any pair of finitely encoded types with a checked linear bound. -/
noncomputable def computableInPolyTime {α β : Type}
    (left : FinEncoding α) (right : FinEncoding β) :
    TM2ComputableInPolyTime (PairEncoding.finEncoding left right)
      (PairEncoding.finEncoding right left) Prod.swap where
  tm := computer left.Γ right.Γ
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.sumComm _ _
  time := 4 * Polynomial.X + 6
  outputsFun pair := by
    simpa [PairEncoding.finEncoding, Equiv.refl, Equiv.sumComm, List.map_append,
      List.map_map, Function.comp_def, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_natCast, Polynomial.eval_X] using
      outputsInTime (left.encode pair.1) (right.encode pair.2)

end LeanNPHardness.PairExchange

namespace LeanNPHardness.MachineAdapters

open Computability Turing MachineComposition

/-- Polynomial-time computation on the right component of any encoded pair,
using the checked pair exchange and the existing left-component adapter. -/
noncomputable def pairRightComputableInPolyTime {α β γ : Type}
    (preserved : FinEncoding α) (source : FinEncoding β) (target : FinEncoding γ)
    (f : β → γ) (machine : TM2ComputableInPolyTime source target f) :
    TM2ComputableInPolyTime (PairEncoding.finEncoding preserved source)
      (PairEncoding.finEncoding preserved target) (fun pair => (pair.1, f pair.2)) := by
  let lifted := pairReductionComputableInPolyTime source target preserved f machine
  let first := compositionComputableInPolyTime _ _ _ _ _
    (PairExchange.computableInPolyTime preserved source) lifted
  let composed := compositionComputableInPolyTime _ _ _ _ _ first
    (PairExchange.computableInPolyTime target preserved)
  exact { composed with
    outputsFun := fun pair => by
      simpa [Function.comp_def] using composed.outputsFun pair }

end LeanNPHardness.MachineAdapters
