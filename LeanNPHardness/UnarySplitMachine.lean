import LeanNPHardness.MachineRoutineBound
import LeanNPHardness.MachineRoutineUnary
import LeanNPHardness.UnarySplitJob

/-!
# The splitting machine, part 1: clause extraction

The splitter reads the unary encoding of a formula clause by clause. For
one clause it copies the clause's symbols (doubling every mark) onto the
reversed-clause stack while counting its literals. This file proves that
extraction and the single-literal move with linear TM2 step bounds in the
unary symbol lengths. Compiling the clause's splitting job onto the job
stack and assembling the full reduction remain separate obligations.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary TableauJobs SplitJob

/-- The reversed, doubled clause. -/
abbrev crevS : GStack := .xkeep
/-- The forward doubled clause. -/
abbrev cfwdS : GStack := .xscr
/-- The job, pushed in reverse. -/
abbrev jobRevS : GStack := .skel
/-- The literal counter and plan, with an end-of-clause sentinel at the bottom. -/
abbrev cntS : GStack := .work (.cnt .n)
/-- The loop flag. -/
abbrev goS : GStack := .work (.cnt .copy1)
/-- A temporary literal. -/
abbrev tmpS : GStack := .work (.cnt .copy2)
/-- A second temporary literal. -/
abbrev tmp2S : GStack := .work (.cnt .copy3)

/-- The splitter's stacks during compilation. -/
def sp (inp crev cfwd cnt go tmp tmp2 : List Sym) (jr : List Instr) (b w : ℕ) :
    Stacks (GAlphabet Sym)
  | .input => inp
  | .xkeep => crev
  | .xscr => cfwd
  | .skel => jr
  | .work (.cnt .n) => cnt
  | .work (.cnt .copy1) => go
  | .work (.cnt .copy2) => tmp
  | .work (.cnt .copy3) => tmp2
  | .work (.reg .base) => marks b
  | .work (.reg .w) => marks w
  | _ => []

/-- Doubling the marks of a symbol. -/
def dbl : Sym → List Sym
  | .mark => [.mark, .mark]
  | s => [s]

/-- One for a sign symbol, zero otherwise. -/
def sv : Sym → ℕ
  | .pos => 1
  | .neg => 1
  | _ => 0

/-- The number of literals (sign symbols) in a symbol list. -/
def signCount (L : List Sym) : ℕ := (L.map sv).sum

theorem signCount_append (L M : List Sym) : signCount (L ++ M) = signCount L + signCount M := by
  simp [signCount]

theorem signCount_nil : signCount [] = 0 := rfl

theorem signCount_singleton (s : Sym) : signCount [s] = sv s := by simp [signCount]

theorem marks_add (a b : ℕ) : marks (a + b) = marks a ++ marks b := by
  simp only [marks, List.replicate_add]

theorem flatMap_dbl_marks (v : ℕ) : (marks v).flatMap dbl = marks (2 * v) := by
  induction v with
  | zero => rfl
  | succ v ih =>
      simp only [marks, List.replicate_succ, List.flatMap_cons, dbl] at ih ⊢
      rw [ih, Nat.mul_succ]
      simp only [List.replicate_succ, List.cons_append, List.nil_append]

/-- Symbol doubling implements the semantic renaming of an original literal. -/
theorem flatMap_dbl_encodeLiteral (l : CNF.Literal ℕ) :
    (encodeLiteral l).flatMap dbl = encodeLiteral l.double := by
  cases l with
  | positive v =>
      change Sym.pos :: (marks v).flatMap dbl = Sym.pos :: marks (2 * v)
      rw [flatMap_dbl_marks]
  | negative v =>
      change Sym.neg :: (marks v).flatMap dbl = Sym.neg :: marks (2 * v)
      rw [flatMap_dbl_marks]

theorem signCount_encodeLiteral (l : CNF.Literal ℕ) : signCount (encodeLiteral l) = 1 := by
  cases l <;> simp [signCount, encodeLiteral, sv]

theorem endClause_not_mem_encodeLiteral (l : CNF.Literal ℕ) :
    Sym.endClause ∉ encodeLiteral l := by
  cases l <;> simp [encodeLiteral]

theorem flatMap_dbl_clause (c : CNF.Clause ℕ) :
    (c.flatMap encodeLiteral).flatMap dbl = c.double.flatMap encodeLiteral := by
  simp [CNF.Clause.double, List.flatMap_assoc, List.flatMap_map, flatMap_dbl_encodeLiteral]

/-- Count occurrences, including repeated literals. -/
theorem signCount_clause (c : CNF.Clause ℕ) :
    signCount (c.flatMap encodeLiteral) = c.length := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      simp only [List.flatMap_cons, signCount_append, signCount_encodeLiteral, ih, List.length_cons]
      omega

/-- Pointwise comparison of splitter stack families. -/
macro "sp_ext" : tactic =>
  `(tactic| (funext k; rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    simp [sp, marks, dbl, sv, signCount, crevS, cfwdS, cntS, goS, tmpS, tmp2S,
      Function.update_of_ne]))

/-! ### Extraction of one clause -/

/-- Handlers of the extraction loop: marks are doubled onto the reversed
clause, signs are copied and counted, the end of the clause clears the flag. -/
def extractHandlers : Sym → GRoutine Sym
  | .mark => pushList crevS [.mark, .mark]
  | .pos => seq (pushList crevS [.pos]) (pushList cntS [.mark])
  | .neg => seq (pushList crevS [.neg]) (pushList cntS [.mark])
  | .endClause => popOne goS

/-- Extract the clause at the top of the input. -/
def extract : GRoutine Sym := loop goS (dispatch .input extractHandlers)

theorem extractHandlers_exits (s : Sym) (hs : s ≠ .endClause) (inp crev cfwd cnt go tmp tmp2 : List Sym)
    (jr : List Instr) (b w : ℕ) :
    (extractHandlers s).ExitsLE (sp inp crev cfwd cnt go tmp tmp2 jr b w) 2
      (sp inp ((dbl s).reverse ++ crev) cfwd (marks (sv s) ++ cnt) go tmp tmp2 jr b w) := by
  cases s with
  | mark =>
      have h := pushList_exits (Γ := GAlphabet Sym) crevS [.mark, .mark]
        (sp inp crev cfwd cnt go tmp tmp2 jr b w)
      refine ⟨1, by norm_num, ?_⟩
      convert h using 1
      sp_ext
  | pos =>
      have h1 := pushList_exits (Γ := GAlphabet Sym) crevS [.pos] (sp inp crev cfwd cnt go tmp tmp2 jr b w)
      have h2 := pushList_exits (Γ := GAlphabet Sym) cntS [.mark]
        (Function.update (sp inp crev cfwd cnt go tmp tmp2 jr b w) crevS
          ([.pos] ++ sp inp crev cfwd cnt go tmp tmp2 jr b w crevS))
      have := seq_exits _ _ h1 h2
      refine ⟨1 + 1, le_rfl, ?_⟩
      convert this using 1
      sp_ext
  | neg =>
      have h1 := pushList_exits (Γ := GAlphabet Sym) crevS [.neg] (sp inp crev cfwd cnt go tmp tmp2 jr b w)
      have h2 := pushList_exits (Γ := GAlphabet Sym) cntS [.mark]
        (Function.update (sp inp crev cfwd cnt go tmp tmp2 jr b w) crevS
          ([.neg] ++ sp inp crev cfwd cnt go tmp tmp2 jr b w crevS))
      have := seq_exits _ _ h1 h2
      refine ⟨1 + 1, le_rfl, ?_⟩
      convert this using 1
      sp_ext
  | endClause => exact absurd rfl hs

/-- The stacks during the extraction of `L ++ [endClause]`. -/
def extStacks (L rest crev cfwd cnt tmp tmp2 : List Sym) (jr : List Instr) (b w : ℕ) (i : ℕ) :
    Stacks (GAlphabet Sym) :=
  if i ≤ L.length then
    sp (L.drop i ++ .endClause :: rest) (((L.take i).flatMap dbl).reverse ++ crev) cfwd
      (marks (signCount (L.take i)) ++ cnt) [.mark] tmp tmp2 jr b w
  else
    sp rest ((L.flatMap dbl).reverse ++ crev) cfwd (marks (signCount L) ++ cnt) [] tmp tmp2 jr b w

theorem extract_exits (L : List Sym) (hL : Sym.endClause ∉ L) (rest crev cfwd cnt tmp tmp2 : List Sym)
    (jr : List Instr) (b w : ℕ) :
    extract.ExitsLE (sp (L ++ .endClause :: rest) crev cfwd cnt [.mark] tmp tmp2 jr b w)
      ((L.length + 1) * 4 + 1)
      (sp rest ((L.flatMap dbl).reverse ++ crev) cfwd (marks (signCount L) ++ cnt) [] tmp tmp2 jr b w) := by
  have key := loop_exitsLE (Γ := GAlphabet Sym) goS (dispatch .input extractHandlers) (L.length + 1)
    (extStacks L rest crev cfwd cnt tmp tmp2 jr b w) 3 ?_ ?_ ?_
  · simp only [extStacks, Nat.zero_le, if_true, List.drop_zero, List.take_zero, List.flatMap_nil,
      List.reverse_nil, List.nil_append, signCount_nil, marks, List.replicate_zero,
      show ¬ (L.length + 1 ≤ L.length) by omega, if_false] at key
    exact key
  · intro i hi
    by_cases hiL : i < L.length
    · have hsym : (extStacks L rest crev cfwd cnt tmp tmp2 jr b w i) .input =
          L[i] :: (L.drop (i + 1) ++ .endClause :: rest) := by
        simp only [extStacks, if_pos (by omega : i ≤ L.length), sp]
        rw [List.drop_eq_getElem_cons hiL]
        rfl
      have hne : L[i] ≠ .endClause := fun h => hL (h ▸ List.getElem_mem hiL)
      refine dispatch_exitsLE (Γ := GAlphabet Sym) .input extractHandlers _ _ _ hsym ?_
      have h := extractHandlers_exits L[i] hne (L.drop (i + 1) ++ .endClause :: rest)
        (((L.take i).flatMap dbl).reverse ++ crev) cfwd (marks (signCount (L.take i)) ++ cnt)
        [.mark] tmp tmp2 jr b w
      have e1 : Function.update (extStacks L rest crev cfwd cnt tmp tmp2 jr b w i) .input
          (L.drop (i + 1) ++ .endClause :: rest) =
          sp (L.drop (i + 1) ++ .endClause :: rest) (((L.take i).flatMap dbl).reverse ++ crev) cfwd
            (marks (signCount (L.take i)) ++ cnt) [.mark] tmp tmp2 jr b w := by
        simp only [extStacks, if_pos (by omega : i ≤ L.length)]
        sp_ext
      have e2 : extStacks L rest crev cfwd cnt tmp tmp2 jr b w (i + 1) =
          sp (L.drop (i + 1) ++ .endClause :: rest)
            ((dbl L[i]).reverse ++ (((L.take i).flatMap dbl).reverse ++ crev)) cfwd
            (marks (sv L[i]) ++ (marks (signCount (L.take i)) ++ cnt)) [.mark] tmp tmp2 jr b w := by
        simp only [extStacks, if_pos (by omega : i + 1 ≤ L.length)]
        rw [List.take_add_one, List.getElem?_eq_getElem hiL]
        simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
          List.reverse_append, signCount_append, signCount_singleton, List.append_assoc]
        rw [Nat.add_comm (signCount (L.take i)) (sv L[i]), marks_add, List.append_assoc]
      rw [e1, e2]
      exact h
    · have hi' : i = L.length := by omega
      subst hi'
      have hsym : (extStacks L rest crev cfwd cnt tmp tmp2 jr b w L.length) .input =
          .endClause :: rest := by
        simp only [extStacks, le_rfl, if_true, sp, List.drop_length, List.nil_append]
      refine dispatch_exitsLE (Γ := GAlphabet Sym) .input extractHandlers _ _ _ hsym ?_
      have h := popOne_exits (Γ := GAlphabet Sym) goS
        (Function.update (extStacks L rest crev cfwd cnt tmp tmp2 jr b w L.length) .input rest)
      refine ⟨1, by norm_num, ?_⟩
      convert h using 1
      simp only [extStacks, le_rfl, if_true, show ¬ (L.length + 1 ≤ L.length) by omega, if_false,
        List.take_length]
      sp_ext
  · intro i hi
    simp only [extStacks, if_pos (by omega : i ≤ L.length), sp]
    simp
  · simp only [extStacks, show ¬ (L.length + 1 ≤ L.length) by omega, if_false, sp]

/-- Extract an encoded clause, rename its variables to even indices, and
count every occurrence. The delimiter is consumed and the unread suffix and
all other supplied stack contents are retained. The bound measures input
symbols, including the clause delimiter. -/
theorem extract_clause_exits (c : CNF.Clause ℕ) (rest crev cfwd cnt tmp tmp2 : List Sym)
    (jr : List Instr) (b w : ℕ) :
    extract.ExitsLE (sp (encodeClause c ++ rest) crev cfwd cnt [.mark] tmp tmp2 jr b w)
      (4 * (encodeClause c).length + 1)
      (sp rest ((c.double.flatMap encodeLiteral).reverse ++ crev) cfwd
        (marks c.length ++ cnt) [] tmp tmp2 jr b w) := by
  have hL : Sym.endClause ∉ c.flatMap encodeLiteral := by
    intro h
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
    exact endClause_not_mem_encodeLiteral l hl
  simpa only [encodeClause, List.append_assoc, List.singleton_append, List.length_append,
    List.length_singleton, flatMap_dbl_clause, signCount_clause, Nat.mul_comm] using
    extract_exits (c.flatMap encodeLiteral) hL rest crev cfwd cnt tmp tmp2 jr b w

/-! ### Moving one reversed literal forward -/

/-- Handlers moving a reversed literal (marks, then its sign) from the
reversed clause to the temporary stack; the sign clears the flag. -/
def litHandlers : Sym → GRoutine Sym
  | .mark => pushList tmpS [.mark]
  | .pos => seq (pushList tmpS [.pos]) (popOne goS)
  | .neg => seq (pushList tmpS [.neg]) (popOne goS)
  | .endClause => skip

/-- Move the top reversed literal of the reversed clause to the temporary
stack, in forward order. -/
def moveLit : GRoutine Sym := seq (pushList goS [.mark]) (loop goS (dispatch crevS litHandlers))

/-- The stacks while moving a literal: `i` marks moved. -/
def litStacks (v : ℕ) (s : Sym) (inp crevRest cfwd cnt tmp tmp2 : List Sym) (jr : List Instr)
    (b w : ℕ) (i : ℕ) : Stacks (GAlphabet Sym) :=
  if i ≤ v then
    sp inp (marks (v - i) ++ s :: crevRest) cfwd cnt [.mark] (marks i ++ tmp) tmp2 jr b w
  else
    sp inp crevRest cfwd cnt [] (s :: marks v ++ tmp) tmp2 jr b w

theorem moveLit_exits (v : ℕ) (s : Sym) (hs : s = .pos ∨ s = .neg)
    (inp crevRest cfwd cnt tmp tmp2 : List Sym) (jr : List Instr) (b w : ℕ) :
    moveLit.ExitsLE (sp inp (marks v ++ s :: crevRest) cfwd cnt [] tmp tmp2 jr b w)
      ((v + 1) * 4 + 2)
      (sp inp crevRest cfwd cnt [] (s :: marks v ++ tmp) tmp2 jr b w) := by
  have h1 := pushList_exits (Γ := GAlphabet Sym) goS [.mark]
    (sp inp (marks v ++ s :: crevRest) cfwd cnt [] tmp tmp2 jr b w)
  have h1' : Function.update (sp inp (marks v ++ s :: crevRest) cfwd cnt [] tmp tmp2 jr b w) goS
      ([.mark] ++ sp inp (marks v ++ s :: crevRest) cfwd cnt [] tmp tmp2 jr b w goS) =
      litStacks v s inp crevRest cfwd cnt tmp tmp2 jr b w 0 := by
    simp only [litStacks, Nat.zero_le, if_true, Nat.sub_zero, marks, List.replicate_zero,
      List.nil_append]
    sp_ext
  rw [h1'] at h1
  have key := loop_exitsLE (Γ := GAlphabet Sym) goS (dispatch crevS litHandlers) (v + 1)
    (litStacks v s inp crevRest cfwd cnt tmp tmp2 jr b w) 3 ?_ ?_ ?_
  · have := seq_exitsLE _ _ h1.le key
    simp only [litStacks, show ¬ (v + 1 ≤ v) by omega, if_false] at this
    exact this.mono (by omega)
  · intro i hi
    by_cases hiv : i < v
    · have hsym : (litStacks v s inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS =
          .mark :: (marks (v - (i + 1)) ++ s :: crevRest) := by
        simp only [litStacks, if_pos (by omega : i ≤ v), sp]
        rw [show v - i = (v - (i + 1)) + 1 by omega, marks, marks, List.replicate_succ]
        rfl
      refine dispatch_exitsLE (Γ := GAlphabet Sym) crevS litHandlers _ _ _ hsym ?_
      have h := pushList_exits (Γ := GAlphabet Sym) tmpS [.mark]
        (Function.update (litStacks v s inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS
          (marks (v - (i + 1)) ++ s :: crevRest))
      refine ⟨1, by norm_num, ?_⟩
      convert h using 1
      simp only [litStacks, if_pos (by omega : i ≤ v), if_pos (by omega : i + 1 ≤ v)]
      rw [show marks (i + 1) = [.mark] ++ marks i by simp [marks, List.replicate_succ]]
      sp_ext
    · have hi' : i = v := by omega
      subst hi'
      have hsym : (litStacks i s inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS = s :: crevRest := by
        simp only [litStacks, le_rfl, if_true, sp, Nat.sub_self, marks, List.replicate_zero,
          List.nil_append]
      refine dispatch_exitsLE (Γ := GAlphabet Sym) crevS litHandlers _ _ _ hsym ?_
      rcases hs with rfl | rfl
      · have h1 := pushList_exits (Γ := GAlphabet Sym) tmpS [.pos]
          (Function.update (litStacks i .pos inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS crevRest)
        have h2 := popOne_exits (Γ := GAlphabet Sym) goS
          (Function.update
            (Function.update (litStacks i .pos inp crevRest cfwd cnt tmp tmp2 jr b w i)
              crevS crevRest) tmpS
            ([.pos] ++ Function.update
              (litStacks i .pos inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS crevRest tmpS))
        have := seq_exits _ _ h1 h2
        refine ⟨1 + 1, by norm_num, ?_⟩
        convert this using 1
        simp only [litStacks, le_rfl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
        sp_ext
      · have h1 := pushList_exits (Γ := GAlphabet Sym) tmpS [.neg]
          (Function.update (litStacks i .neg inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS crevRest)
        have h2 := popOne_exits (Γ := GAlphabet Sym) goS
          (Function.update
            (Function.update (litStacks i .neg inp crevRest cfwd cnt tmp tmp2 jr b w i)
              crevS crevRest) tmpS
            ([.neg] ++ Function.update
              (litStacks i .neg inp crevRest cfwd cnt tmp tmp2 jr b w i) crevS crevRest tmpS))
        have := seq_exits _ _ h1 h2
        refine ⟨1 + 1, by norm_num, ?_⟩
        convert this using 1
        simp only [litStacks, le_rfl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
        sp_ext
  · intro i hi
    simp only [litStacks, if_pos (by omega : i ≤ v), sp]
    simp
  · simp only [litStacks, show ¬ (v + 1 ≤ v) by omega, if_false, sp]

end LeanNPHardness.TableauStacks
