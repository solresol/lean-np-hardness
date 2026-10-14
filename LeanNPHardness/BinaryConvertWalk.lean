import LeanNPHardness.BinaryConvertNat

/-!
# Walking the unary formula

The pieces of the unary-to-binary converter that read the input:
`countLoop_exits` counts the clauses (keeping a reversed copy of the
input), `extractLoop_exits` moves one clause to `cl` while counting its
literals, `collectLoop_exits` doubles a literal's marks onto `cnt`, and
`litLoop_exits` emits the binary code of every literal of a clause.
-/

namespace LeanNPHardness.BinaryConvert

open Routines CNF CNF.Unary

/-! ### Symbol counts -/

/-- One for the end-of-clause symbol. -/
def ec : Sym → ℕ
  | .endClause => 1
  | _ => 0

/-- One for a sign symbol. -/
def sv : Sym → ℕ
  | .pos => 1
  | .neg => 1
  | _ => 0

/-- Number of clause ends. -/
def ecount (L : List Sym) : ℕ := (L.map ec).sum

/-- Number of literals. -/
def signCount (L : List Sym) : ℕ := (L.map sv).sum

@[simp] theorem ecount_nil : ecount [] = 0 := rfl
@[simp] theorem ecount_cons (s : Sym) (L : List Sym) : ecount (s :: L) = ec s + ecount L := by
  simp [ecount]
@[simp] theorem ecount_append (L M : List Sym) : ecount (L ++ M) = ecount L + ecount M := by
  simp [ecount]
@[simp] theorem signCount_nil : signCount [] = 0 := rfl
@[simp] theorem signCount_cons (s : Sym) (L : List Sym) :
    signCount (s :: L) = sv s + signCount L := by simp [signCount]
@[simp] theorem signCount_append (L M : List Sym) :
    signCount (L ++ M) = signCount L + signCount M := by simp [signCount]

@[simp] theorem ecount_marks (n : ℕ) : ecount (List.replicate n .mark) = 0 := by
  induction n <;> simp_all [List.replicate_succ, ec]
@[simp] theorem signCount_marks (n : ℕ) : signCount (List.replicate n .mark) = 0 := by
  induction n <;> simp_all [List.replicate_succ, sv]

theorem ecount_encodeLiteral (l : Literal ℕ) : ecount (encodeLiteral l) = 0 := by
  cases l <;> simp [encodeLiteral, ec]

theorem signCount_encodeLiteral (l : Literal ℕ) : signCount (encodeLiteral l) = 1 := by
  cases l <;> simp [encodeLiteral, sv]

theorem ecount_lits (c : Clause ℕ) : ecount (c.flatMap encodeLiteral) = 0 := by
  induction c <;> simp_all [ecount_encodeLiteral]

theorem signCount_lits (c : Clause ℕ) : signCount (c.flatMap encodeLiteral) = c.length := by
  induction c <;> simp_all [signCount_encodeLiteral]; omega

theorem ecount_encode (F : Formula ℕ) : ecount (encode F) = F.length := by
  induction F with
  | nil => rfl
  | cons c F ih => simp [encode_cons, encodeClause, ecount_lits, ih, ec]; omega

theorem endClause_not_mem_lits (c : Clause ℕ) : ∀ s ∈ c.flatMap encodeLiteral, s ≠ .endClause := by
  intro s hs
  obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp hs
  cases l <;> simp [encodeLiteral] at hl <;> rcases hl with rfl | ⟨_, rfl⟩ <;> decide

/-! ### Counting clauses -/

/-- Keep every symbol and count the clause ends. -/
def countH : Sym → CR
  | .endClause => seq (pushList .keep [.endClause]) (pushList .cnt [.mark])
  | .mark => pushList .keep [.mark]
  | .pos => pushList .keep [.pos]
  | .neg => pushList .keep [.neg]

theorem countH_exits (s : Sym) (S : CS) :
    (countH s).ExitsLE S 2
      (Function.update (Function.update S .keep (s :: S .keep)) .cnt (marks (ec s) ++ S .cnt)) := by
  cases s with
  | endClause =>
      refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.keep [Sym.endClause] S 0)
        (pushList_exitsLE (Γ := CAlpha) CStack.cnt [Sym.mark] _ 0)).congr ?_
      funext k; cases k <;> simp [ec, marks_succ]
  | mark =>
      refine ((pushList_exitsLE (Γ := CAlpha) CStack.keep [Sym.mark] S 1)).congr ?_
      funext k; cases k <;> simp [ec]
  | pos =>
      refine ((pushList_exitsLE (Γ := CAlpha) CStack.keep [Sym.pos] S 1)).congr ?_
      funext k; cases k <;> simp [ec]
  | neg =>
      refine ((pushList_exitsLE (Γ := CAlpha) CStack.keep [Sym.neg] S 1)).congr ?_
      funext k; cases k <;> simp [ec]

theorem countLoop_exits (L : List Sym) : ∀ (S : CS) (kp : List Sym) (c : ℕ),
    S .input = L → S .keep = kp → S .cnt = marks c →
    (loop .input (dispatch .input countH)).ExitsLE S (4 * L.length + 1)
      (Function.update (Function.update (Function.update S .input []) .keep (L.reverse ++ kp))
        .cnt (marks (c + ecount L))) := by
  induction L with
  | nil =>
      intro S kp c hi hk hc
      refine (loop_exitsLE_nil _ _ S hi 0).congr ?_
      funext k; cases k <;> simp [hi, hk, hc]
  | cons s L ih =>
      intro S kp c hi hk hc
      have hb := dispatch_exitsLE (Γ := CAlpha) .input countH S s L hi
        (countH_exits s (Function.update S .input L))
      have h2 := ih (Function.update (Function.update (Function.update S .input L) .keep
          (s :: (Function.update S .input L) .keep)) .cnt
          (marks (ec s) ++ (Function.update S .input L) .cnt)) (s :: kp) (c + ec s)
        (by simp) (by simp [hk]) (by simp [hc, ← marks_add, Nat.add_comm])
      refine ((loop_exitsLE_cons _ _ (by simp [hi]) hb h2).mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp
      congr 1; omega

/-! ### Extracting a clause -/

/-- Move clause symbols to `cl`, counting literals; the clause end stops. -/
def exH : Sym → CR
  | .mark => pushList .cl [.mark]
  | .pos => seq (pushList .cl [.pos]) (pushList .cnt [.mark])
  | .neg => seq (pushList .cl [.neg]) (pushList .cnt [.mark])
  | .endClause => popOne .go

theorem exH_exits (s : Sym) (hs : s ≠ .endClause) (S : CS) :
    (exH s).ExitsLE S 2
      (Function.update (Function.update S .cl (s :: S .cl)) .cnt (marks (sv s) ++ S .cnt)) := by
  cases s with
  | endClause => exact absurd rfl hs
  | mark =>
      refine ((pushList_exitsLE (Γ := CAlpha) CStack.cl [Sym.mark] S 1)).congr ?_
      funext k; cases k <;> simp [sv]
  | pos =>
      refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.cl [Sym.pos] S 0)
        (pushList_exitsLE (Γ := CAlpha) CStack.cnt [Sym.mark] _ 0)).congr ?_
      funext k; cases k <;> simp [sv, marks_succ]
  | neg =>
      refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.cl [Sym.neg] S 0)
        (pushList_exitsLE (Γ := CAlpha) CStack.cnt [Sym.mark] _ 0)).congr ?_
      funext k; cases k <;> simp [sv, marks_succ]

theorem extractLoop_exits (L : List Sym) (hL : ∀ s ∈ L, s ≠ .endClause) :
    ∀ (S : CS) (rest clL : List Sym) (c : ℕ),
    S .input = L ++ .endClause :: rest → S .go = [.mark] → S .cl = clL → S .cnt = marks c →
    (loop .go (dispatch .input exH)).ExitsLE S (4 * L.length + 4)
      (Function.update (Function.update (Function.update (Function.update S .input rest) .go [])
        .cl (L.reverse ++ clL)) .cnt (marks (c + signCount L))) := by
  induction L with
  | nil =>
      intro S rest clL c hi hg hcl hc
      have hb := dispatch_exitsLE (Γ := CAlpha) .input exH S .endClause rest (by simpa using hi)
        (popOne_exitsLE (Γ := CAlpha) CStack.go (Function.update S .input rest) 0)
      have h2 := loop_exitsLE_nil (Γ := CAlpha) CStack.go (dispatch .input exH)
        (Function.update (Function.update S .input rest) .go
          ((Function.update S .input rest) .go).tail) (by simp [hg]) 0
      refine ((loop_exitsLE_cons _ _ (by simp [hg]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp [hcl, hc, hg]
  | cons s L ih =>
      intro S rest clL c hi hg hcl hc
      have hs := hL s (List.mem_cons_self ..)
      have hb := dispatch_exitsLE (Γ := CAlpha) .input exH S s (L ++ .endClause :: rest) hi
        (exH_exits s hs (Function.update S .input (L ++ .endClause :: rest)))
      have h2 := ih (fun t ht => hL t (List.mem_cons_of_mem _ ht))
        (Function.update (Function.update (Function.update S .input (L ++ .endClause :: rest)) .cl
          (s :: (Function.update S .input (L ++ .endClause :: rest)) .cl)) .cnt
          (marks (sv s) ++ (Function.update S .input (L ++ .endClause :: rest)) .cnt))
        rest (s :: clL) (c + sv s) (by simp) (by simp [hg]) (by simp [hcl])
        (by simp [hc, ← marks_add, Nat.add_comm])
      refine ((loop_exitsLE_cons _ _ (by simp [hg]) hb h2).mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp
      congr 1; omega

/-- Extract the clause at the top of the input. -/
def extract : CR := seq (pushList .go [.mark]) (loop .go (dispatch .input exH))

/-! ### Collecting a literal's index -/

/-- Double marks onto `cnt`; a non-mark is put back and stops the loop. -/
def colH : Sym → CR
  | .mark => pushList .cnt [.mark, .mark]
  | .pos => seq (pushList .cl2 [.pos]) (popOne .go3)
  | .neg => seq (pushList .cl2 [.neg]) (popOne .go3)
  | .endClause => seq (pushList .cl2 [.endClause]) (popOne .go3)

theorem colH_stop (s : Sym) (hs : s ≠ .mark) (S : CS) :
    (colH s).ExitsLE S 2
      (Function.update (Function.update S .cl2 (s :: S .cl2)) .go3 (S .go3).tail) := by
  cases s with
  | mark => exact absurd rfl hs
  | pos =>
      exact (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.cl2 [Sym.pos] S 0)
        (popOne_exitsLE (Γ := CAlpha) CStack.go3 _ 0)).congr (by funext k; cases k <;> simp)
  | neg =>
      exact (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.cl2 [Sym.neg] S 0)
        (popOne_exitsLE (Γ := CAlpha) CStack.go3 _ 0)).congr (by funext k; cases k <;> simp)
  | endClause =>
      exact (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.cl2 [Sym.endClause] S 0)
        (popOne_exitsLE (Γ := CAlpha) CStack.go3 _ 0)).congr (by funext k; cases k <;> simp)

theorem collectLoop_exits (v : ℕ) : ∀ (S : CS) (s : Sym) (rest : List Sym) (c : ℕ),
    s ≠ .mark → S .cl2 = marks v ++ s :: rest → S .go3 = [.mark] → S .cnt = marks c →
    (loop .go3 (dispatch .cl2 colH)).ExitsLE S (3 * v + 5)
      (Function.update (Function.update (Function.update S .cl2 (s :: rest)) .go3 [])
        .cnt (marks (c + 2 * v))) := by
  induction v with
  | zero =>
      intro S s rest c hs hcl hg hc
      have hb := dispatch_exitsLE (Γ := CAlpha) .cl2 colH S s rest (by simpa using hcl)
        (colH_stop s hs (Function.update S .cl2 rest))
      have h2 := loop_exitsLE_nil (Γ := CAlpha) CStack.go3 (dispatch .cl2 colH)
        (Function.update (Function.update (Function.update S .cl2 rest) .cl2
          (s :: (Function.update S .cl2 rest) .cl2)) .go3
          ((Function.update (Function.update S .cl2 rest) .cl2
            (s :: (Function.update S .cl2 rest) .cl2)) .go3).tail) (by simp [hg]) 0
      refine ((loop_exitsLE_cons _ _ (by simp [hg]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp [hc, hg]
  | succ v ih =>
      intro S s rest c hs hcl hg hc
      have hb := dispatch_exitsLE (Γ := CAlpha) .cl2 colH S .mark (marks v ++ s :: rest)
        (by simp [hcl, marks_succ])
        (pushList_exitsLE (Γ := CAlpha) CStack.cnt [Sym.mark, Sym.mark]
          (Function.update S .cl2 (marks v ++ s :: rest)) 0)
      have h2 := ih (Function.update (Function.update S .cl2 (marks v ++ s :: rest)) .cnt
          ([.mark, .mark] ++ (Function.update S .cl2 (marks v ++ s :: rest)) .cnt)) s rest (c + 2)
        hs (by simp) (by simp [hg]) (by simp [hc, marks_succ])
      refine ((loop_exitsLE_cons _ _ (by simp [hg]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp
      congr 1; omega

/-- Collect the marks of a literal, doubled, onto `cnt`. -/
def collect : CR := seq (pushList .go3 [.mark]) (loop .go3 (dispatch .cl2 colH))

theorem collect_exits (v : ℕ) (S : CS) (s : Sym) (rest : List Sym) (hs : s ≠ .mark)
    (hcl : S .cl2 = marks v ++ s :: rest) (hg : S .go3 = []) (hc : S .cnt = []) :
    collect.ExitsLE S (3 * v + 6)
      (Function.update (Function.update S .cl2 (s :: rest)) .cnt (marks (2 * v))) := by
  have h1 := pushList_exitsLE (Γ := CAlpha) CStack.go3 [Sym.mark] S 0
  have h2 := collectLoop_exits v (Function.update S .go3 ([Sym.mark] ++ S .go3)) s rest 0 hs
    (by simp [hcl]) (by simp [hg]) (by simp [hc])
  refine ((seq_exitsLE _ _ h1 h2).mono (by omega)).congr ?_
  funext k; cases k <;> simp [hg]

/-! ### Emitting the literals of a clause -/

/-- Handle the next literal of `cl2`; the clause end stops the loop. -/
def litH : Sym → CR
  | .pos => seq collect emitNat
  | .neg => seq collect (seq (pushList .cnt [.mark]) emitNat)
  | .endClause => popOne .go2
  | .mark => skip

theorem emitNatCost_mono {a b : ℕ} (h : a ≤ b) : emitNatCost a ≤ emitNatCost b := by
  unfold emitNatCost
  have := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2
  omega

/-- Steps of one literal with codes at most `N`. -/
def litCost (N : ℕ) : ℕ := 3 * N + 10 + emitNatCost N

/-- Empty work stacks of the clause stage. -/
structure Clean (S : CS) : Prop where
  cnt : S .cnt = []
  half : S .half = []
  par : S .par = []
  bitsA : S .bitsA = []
  bitsB : S .bitsB = []
  lenS : S .lenS = []
  go3 : S .go3 = []

theorem lit_exits (l : Literal ℕ) (N : ℕ) (hN : l.toNat ≤ N) (S : CS) (s : Sym)
    (rest : List Sym) (hs : s ≠ .mark) (hcl : S .cl2 = encodeLiteral l ++ s :: rest)
    (hS : Clean S) :
    (dispatch .cl2 litH).ExitsLE S (litCost N)
      (Function.update (Function.update S .cl2 (s :: rest)) .buf
        ((frameSyms l.toNat).reverse ++ S .buf)) := by
  cases l with
  | positive v =>
      have hcl' : S .cl2 = .pos :: (marks v ++ s :: rest) := by simpa [encodeLiteral, marks] using hcl
      have hc := collect_exits v (Function.update S .cl2 (marks v ++ s :: rest)) s rest hs
        (by simp) (by simp [hS.go3]) (by simp [hS.cnt])
      have he := emitNat_exits (2 * v) (Function.update (Function.update
        (Function.update S .cl2 (marks v ++ s :: rest)) .cl2 (s :: rest)) .cnt (marks (2 * v)))
        (by simp) (by simp [hS.half]) (by simp [hS.par])
        (by simp [hS.bitsA]) (by simp [hS.bitsB]) (by simp [hS.lenS])
      have := dispatch_exitsLE (Γ := CAlpha) .cl2 litH S .pos _ hcl' (seq_exitsLE _ _ hc he)
      have hv : 2 * v ≤ N := by simpa [Literal.toNat] using hN
      refine (this.mono ?_).congr ?_
      · have := emitNatCost_mono hv
        unfold litCost; omega
      · funext k; cases k <;> simp [Literal.toNat, hS.cnt]
  | negative v =>
      have hcl' : S .cl2 = .neg :: (marks v ++ s :: rest) := by simpa [encodeLiteral, marks] using hcl
      have hc := collect_exits v (Function.update S .cl2 (marks v ++ s :: rest)) s rest hs
        (by simp) (by simp [hS.go3]) (by simp [hS.cnt])
      have hp := pushList_exitsLE (Γ := CAlpha) CStack.cnt [Sym.mark]
        (Function.update (Function.update (Function.update S .cl2 (marks v ++ s :: rest)) .cl2
          (s :: rest)) .cnt (marks (2 * v))) 0
      have he := emitNat_exits (2 * v + 1) (Function.update (Function.update (Function.update
          (Function.update S .cl2 (marks v ++ s :: rest)) .cl2 (s :: rest)) .cnt (marks (2 * v)))
          .cnt ([Sym.mark] ++ (Function.update (Function.update
            (Function.update S .cl2 (marks v ++ s :: rest)) .cl2 (s :: rest)) .cnt
            (marks (2 * v))) .cnt))
        (by simp [marks_succ]) (by simp [hS.half])
        (by simp [hS.par]) (by simp [hS.bitsA]) (by simp [hS.bitsB]) (by simp [hS.lenS])
      have := dispatch_exitsLE (Γ := CAlpha) .cl2 litH S .neg _ hcl'
        (seq_exitsLE _ _ hc (seq_exitsLE _ _ hp he))
      have hv : 2 * v + 1 ≤ N := by simpa [Literal.toNat] using hN
      refine (this.mono ?_).congr ?_
      · have := emitNatCost_mono hv
        unfold litCost; omega
      · funext k; cases k <;> simp [Literal.toNat, hS.cnt]

theorem lits_head (ls : Clause ℕ) :
    ∃ s rest, s ≠ .mark ∧ ls.flatMap encodeLiteral ++ [.endClause] = s :: rest := by
  cases ls with
  | nil => exact ⟨.endClause, [], by decide, rfl⟩
  | cons l ls =>
      cases l with
      | positive v => exact ⟨.pos, List.replicate v .mark ++ (ls.flatMap encodeLiteral ++ [.endClause]),
          by decide, by simp [encodeLiteral]⟩
      | negative v => exact ⟨.neg, List.replicate v .mark ++ (ls.flatMap encodeLiteral ++ [.endClause]),
          by decide, by simp [encodeLiteral]⟩

theorem litLoop_exits (N : ℕ) (ls : Clause ℕ) (hN : ∀ l ∈ ls, l.toNat ≤ N) : ∀ (S : CS),
    S .cl2 = ls.flatMap encodeLiteral ++ [.endClause] → S .go2 = [.mark] → Clean S →
    (loop .go2 (dispatch .cl2 litH)).ExitsLE S (ls.length * (litCost N + 1) + 4)
      (Function.update (Function.update (Function.update S .cl2 []) .go2 []) .buf
        ((ls.flatMap fun l => frameSyms l.toNat).reverse ++ S .buf)) := by
  induction ls with
  | nil =>
      intro S hcl hg _
      have hb := dispatch_exitsLE (Γ := CAlpha) .cl2 litH S .endClause [] (by simpa using hcl)
        (popOne_exitsLE (Γ := CAlpha) CStack.go2 (Function.update S .cl2 []) 0)
      have h2 := loop_exitsLE_nil (Γ := CAlpha) CStack.go2 (dispatch .cl2 litH)
        (Function.update (Function.update S .cl2 []) .go2
          ((Function.update S .cl2 []) .go2).tail) (by simp [hg]) 0
      refine ((loop_exitsLE_cons _ _ (by simp [hg]) hb h2).mono (by omega)).congr ?_
      funext k; cases k <;> simp [hg]
  | cons l ls ih =>
      intro S hcl hg hS
      obtain ⟨s, rest, hs, hsr⟩ := lits_head ls
      have hb := lit_exits l N (hN l (List.mem_cons_self ..)) S s rest hs
        (by rw [hcl, List.flatMap_cons, List.append_assoc, hsr]) hS
      have h2 := ih (fun l' hl' => hN l' (List.mem_cons_of_mem _ hl'))
        (Function.update (Function.update S .cl2 (s :: rest)) .buf
          ((frameSyms l.toNat).reverse ++ S .buf)) (by simp [hsr]) (by simp [hg])
        ⟨by simp [hS.cnt], by simp [hS.half], by simp [hS.par], by simp [hS.bitsA],
          by simp [hS.bitsB], by simp [hS.lenS], by simp [hS.go3]⟩
      refine ((loop_exitsLE_cons _ _ (by simp [hg]) hb h2).mono ?_).congr ?_
      · simp only [List.length_cons, Nat.succ_mul]; omega
      · funext k; cases k <;> simp [List.reverse_append, List.append_assoc]

end LeanNPHardness.BinaryConvert
