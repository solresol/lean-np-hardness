import LeanNPHardness.BinaryConvertWalk
import LeanNPHardness.ChainMachine

/-!
# From the unary CNF encoding to the binary one

`conv` reads the unary encoding of a formula and writes
`CNF.Formula.encode F` (`Formula.finEncoding`): it counts the clauses,
emits the framed clause count, then per clause emits the framed literal
count and each literal's framed code `2v` or `2v + 1` (`conv_exits`). It
runs within `10000 * (n + 1) ^ 3` steps (`conv_le`), so the identity map is
a checked polynomial-time reduction from each unary language to its binary
counterpart. With unary Cook--Levin and the chain reduction this gives
`encodedSAT_NPHard` and `encodedExactThreeSAT_NPHard` for the library's
binary CNF encoding.
-/

namespace LeanNPHardness.BinaryConvert

open Turing Computability Routines CNF CNF.Unary Polynomial MachinePrimitives StateTransition

/-- Empty clause-stage stacks. -/
structure Idle (S : CS) : Prop extends Clean S where
  cl : S .cl = []
  cl2 : S .cl2 = []
  go : S .go = []
  go2 : S .go2 = []

/-- Process one clause. -/
def clauseBody : CR :=
  seq extract <| seq emitNat <| seq (pushList .cl2 [.endClause]) <|
  seq (moveAll .cl .cl2 id .mark) <| seq (pushList .go2 [.mark]) (loop .go2 (dispatch .cl2 litH))

/-- The symbols emitted for one clause. -/
def clauseSyms (c : Clause ℕ) : List Sym :=
  frameSyms c.length ++ c.flatMap fun l => frameSyms l.toNat

theorem length_le_lits (c : Clause ℕ) : c.length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      have : 1 ≤ (encodeLiteral l).length := by cases l <;> simp [encodeLiteral]
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-- Per-literal step budget with codes at most `N`. -/
def stepQ (N : ℕ) : ℕ := litCost N + 10

theorem clause_exits (N : ℕ) (c : Clause ℕ) (hlen : c.length ≤ N) (hN : ∀ l ∈ c, l.toNat ≤ N)
    (S : CS) (rest : List Sym) (hi : S .input = encodeClause c ++ rest) (hS : Idle S) :
    clauseBody.ExitsLE S (((encodeClause c).length + 3) * stepQ N)
      (Function.update (Function.update S .input rest) .buf ((clauseSyms c).reverse ++ S .buf)) := by
  have hL := endClause_not_mem_lits c
  have h1 := pushList_exitsLE (Γ := CAlpha) CStack.go [Sym.mark] S 0
  have := seq_exitsLE _ _ (seq_exitsLE _ _ h1
      (extractLoop_exits (c.flatMap encodeLiteral) hL _ rest [] 0
        (by simp [hi, encodeClause]) (by simp [hS.go]) (by simp [hS.cl]) (by simp [hS.cnt])))
    (seq_exitsLE _ _ (emitNat_exits c.length _ (by simp [signCount_lits]) (by simp [hS.half])
        (by simp [hS.par]) (by simp [hS.bitsA]) (by simp [hS.bitsB]) (by simp [hS.lenS]))
      (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.cl2 [Sym.endClause] _ 0)
        (seq_exitsLE _ _ (moveAll_exits (Γ := CAlpha) CStack.cl CStack.cl2 (by decide) id
            Sym.mark _).le
          (seq_exitsLE _ _ (pushList_exitsLE (Γ := CAlpha) CStack.go2 [Sym.mark] _ 0)
            (litLoop_exits N c hN _ (by simp [hS.cl2]) (by simp [hS.go2])
              ⟨by simp, by simp [hS.half], by simp [hS.par], by simp [hS.bitsA],
                by simp [hS.bitsB], by simp [hS.lenS], by simp [hS.go3]⟩)))))
  have hcl := length_le_lits c
  have hE : emitNatCost c.length ≤ emitNatCost N := emitNatCost_mono hlen
  refine (this.mono ?_).congr ?_
  · simp
    simp only [encodeClause, List.length_append, List.length_singleton, List.length_flatMap,
      stepQ, litCost] at hcl ⊢
    have hm : c.length * (3 * N + 10 + emitNatCost N + 1) ≤
        (c.map fun a => (encodeLiteral a).length).sum * (3 * N + 10 + emitNatCost N + 1) :=
      Nat.mul_le_mul_right _ hcl
    nlinarith
  · funext k
    cases k <;> simp [hS.cl, hS.cl2, hS.go, hS.go2, hS.cnt, clauseSyms, List.reverse_append,
      List.append_assoc]

theorem clauseLoop_exits (N : ℕ) (F : Formula ℕ)
    (hN : ∀ c ∈ F, c.length ≤ N ∧ ∀ l ∈ c, l.toNat ≤ N) : ∀ (S : CS),
    S .input = encode F → Idle S →
    (loop .input clauseBody).ExitsLE S (((encode F).length + 4 * F.length) * stepQ N + 1)
      (Function.update (Function.update S .input []) .buf
        ((F.flatMap clauseSyms).reverse ++ S .buf)) := by
  induction F with
  | nil =>
      intro S hi _
      refine (loop_exitsLE_nil _ _ S (by simpa using hi) _).congr ?_
      funext k; cases k <;> simp [hi]
  | cons c F ih =>
      intro S hi hS
      have hc := hN c (List.mem_cons_self ..)
      have h1 := clause_exits N c hc.1 hc.2 S (encode F) (by rw [hi, encode_cons]) hS
      have h2 := ih (fun c' hc' => hN c' (List.mem_cons_of_mem _ hc'))
        (Function.update (Function.update S .input (encode F)) .buf
          ((clauseSyms c).reverse ++ S .buf)) (by simp)
        { cnt := by simp [hS.cnt], half := by simp [hS.half], par := by simp [hS.par],
          bitsA := by simp [hS.bitsA], bitsB := by simp [hS.bitsB], lenS := by simp [hS.lenS],
          go3 := by simp [hS.go3], cl := by simp [hS.cl], cl2 := by simp [hS.cl2],
          go := by simp [hS.go], go2 := by simp [hS.go2] }
      have hne : S .input ≠ [] := by
        rw [hi, encode_cons]; simp [encodeClause]
      have hQ : 1 ≤ stepQ N := by unfold stepQ; omega
      refine ((loop_exitsLE_cons _ _ hne h1 h2).mono ?_).congr ?_
      · simp only [encode_cons, List.length_append, List.length_cons]
        nlinarith
      · funext k; cases k <;> simp [List.reverse_append, List.append_assoc]

/-! ### The converter -/

/-- Count the clauses, restoring the input. -/
def countPass : CR := seq (loop .input (dispatch .input countH)) (moveAll .keep .input id .mark)

/-- The converter. -/
def conv : CR :=
  seq countPass <| seq emitNat <| seq (loop .input clauseBody) (moveAll .buf .out s2b false)

/-- The initial stacks on input `x`. -/
def initS (x : List Sym) : CS
  | .input => x
  | _ => []

/-- The final stacks with output `y`. -/
def outS (y : List Bool) : CS
  | .out => y
  | _ => []

theorem formula_encode_b2s (F : Formula ℕ) :
    (CNF.Formula.encode F).map b2s = frameSyms F.length ++ F.flatMap clauseSyms := by
  simp only [CNF.Formula.encode, BinaryNatLists.encode, BinaryNatLists.encodeNatList,
    CNF.Formula.toNatLists, List.length_map, List.map_append, List.map_flatMap, frameSyms,
    List.flatMap_map]
  rfl

/-- Exact symbol bound of the binary encoding. -/
theorem encode_length_le (F : Formula ℕ) (N : ℕ)
    (hN : F.length ≤ N ∧ ∀ c ∈ F, c.length ≤ N ∧ ∀ l ∈ c, l.toNat ≤ N) :
    (CNF.Formula.encode F).length ≤ (1 + F.length + (F.map List.length).sum) * (2 * N + 1) := by
  rw [CNF.Formula.encode_length, CNF.Formula.encodedSize]
  have hF := BinaryNatLists.natWireSize_le_two_mul_add_one F.length
  have inner : ∀ G : Formula ℕ, (∀ c ∈ G, c.length ≤ N ∧ ∀ l ∈ c, l.toNat ≤ N) →
      (G.map fun clause => BinaryNatLists.natWireSize clause.length +
        (clause.map fun literal => BinaryNatLists.natWireSize literal.toNat).sum).sum ≤
      (G.length + (G.map List.length).sum) * (2 * N + 1) := by
    intro G hG
    induction G with
    | nil => simp
    | cons c G ih =>
        have hc := hG c (List.mem_cons_self ..)
        have h1 := BinaryNatLists.natWireSize_le_two_mul_add_one c.length
        have h2 := BinaryNatLists.sum_natWireSize_le (c.map Literal.toNat) N
          (by simpa using hc.2)
        have h3 := ih (fun c' hc' => hG c' (List.mem_cons_of_mem _ hc'))
        simp only [List.map_map, Function.comp_def, List.length_map] at h2
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  have := inner F hN.2
  nlinarith

theorem ecount_add_signCount_le (L : List Sym) : ecount L + signCount L ≤ L.length := by
  induction L with
  | nil => simp
  | cons s L ih => cases s <;> simp [ec, sv] <;> omega

theorem signCount_encode (F : Formula ℕ) : signCount (encode F) = (F.map List.length).sum := by
  induction F with
  | nil => rfl
  | cons c F ih => simp [encode_cons, encodeClause, signCount_lits, ih, sv]

theorem clause_length_le (F : Formula ℕ) (c : Clause ℕ) (hc : c ∈ F) :
    (encodeClause c).length ≤ (encode F).length := by
  induction F with
  | nil => simp at hc
  | cons d F ih =>
      rw [encode_cons, List.length_append]
      rcases List.mem_cons.mp hc with rfl | h
      · omega
      · have := ih h; omega

theorem literal_length_le (c : Clause ℕ) (l : Literal ℕ) (hl : l ∈ c) :
    (encodeLiteral l).length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp at hl
  | cons d c ih =>
      simp only [encodeClause, List.flatMap_cons, List.length_append] at ih ⊢
      rcases List.mem_cons.mp hl with rfl | h
      · omega
      · have := ih h; omega

theorem sizes_le (F : Formula ℕ) :
    F.length ≤ 2 * (encode F).length + 1 ∧ ∀ c ∈ F, c.length ≤ 2 * (encode F).length + 1 ∧
      ∀ l ∈ c, l.toNat ≤ 2 * (encode F).length + 1 := by
  have h := ecount_add_signCount_le (encode F)
  rw [ecount_encode] at h
  refine ⟨by omega, fun c hc => ⟨?_, fun l hl => ?_⟩⟩
  · have h1 := clause_length_le F c hc
    have h2 := length_le_lits c
    simp only [encodeClause, List.length_append] at h1
    omega
  · have h1 := clause_length_le F c hc
    have h2 := literal_length_le c l hl
    cases l <;> simp [encodeLiteral, Literal.toNat] at h2 ⊢ <;> omega

/-- Step bound of the converter on an input of length `n`. -/
def convBound (n : ℕ) : ℕ :=
  (4 * n + 1) + (2 * n + 1) + emitNatCost (2 * n + 1) + ((n + 4 * n) * stepQ (2 * n + 1) + 1) +
    (2 * ((1 + n) * (2 * (2 * n + 1) + 1)) + 1)

theorem conv_exits (F : Formula ℕ) :
    conv.ExitsLE (initS (encode F)) (convBound (encode F).length)
      (outS (CNF.Formula.encode F)) := by
  obtain ⟨hFl, hcs⟩ := sizes_le F
  set n := (encode F).length with hn
  have h1 := countLoop_exits (encode F) (initS (encode F)) [] 0 rfl rfl rfl
  have := seq_exitsLE _ _ (seq_exitsLE _ _ h1
      (moveAll_exits (Γ := CAlpha) CStack.keep CStack.input (by decide) id Sym.mark _).le)
    (seq_exitsLE _ _ (emitNat_exits F.length _ (by simp [ecount_encode])
        (by simp [initS]) (by simp [initS]) (by simp [initS]) (by simp [initS]) (by simp [initS]))
      (seq_exitsLE _ _ (clauseLoop_exits (2 * n + 1) F hcs _ (by simp)
          { cnt := by simp, half := by simp [initS], par := by simp [initS],
            bitsA := by simp [initS], bitsB := by simp [initS], lenS := by simp [initS],
            go3 := by simp [initS], cl := by simp [initS], cl2 := by simp [initS],
            go := by simp [initS], go2 := by simp [initS] })
        (moveAll_exits (Γ := CAlpha) CStack.buf CStack.out (by decide) s2b false _).le))
  have hout := encode_length_le F (2 * n + 1) ⟨hFl, hcs⟩
  have hcount : 1 + F.length + (F.map List.length).sum ≤ 1 + n := by
    have := ecount_add_signCount_le (encode F)
    rw [ecount_encode, signCount_encode] at this
    omega
  have hE := emitNatCost_mono hFl
  refine (this.mono ?_).congr ?_
  · have hbuf2 : (F.flatMap clauseSyms).length + (frameSyms F.length).length = F.encodedSize := by
      rw [← CNF.Formula.encode_length, show (CNF.Formula.encode F).length =
        ((CNF.Formula.encode F).map b2s).length by simp, formula_encode_b2s, List.length_append]
      omega
    simp only [List.length_flatMap] at hbuf2
    have henc := CNF.Formula.encode_length F
    have hout' : F.encodedSize ≤ (1 + n) * (2 * (2 * n + 1) + 1) := by
      rw [← CNF.Formula.encode_length]
      exact le_trans hout (Nat.mul_le_mul_right _ hcount)
    have hc4 : (n + 4 * F.length) * stepQ (2 * n + 1) ≤ (n + 4 * n) * stepQ (2 * n + 1) := by
      apply Nat.mul_le_mul_right
      have := ecount_add_signCount_le (encode F)
      rw [ecount_encode] at this
      omega
    simp [initS, List.length_append]
    rw [← hn]
    simp only [convBound]
    omega
  · funext k
    cases k <;> simp [initS, outS]
    rw [← List.map_append, ← formula_encode_b2s, List.map_map]
    simp [Function.comp_def]

/-! ### The machine -/

/-- The converter machine. -/
noncomputable def machine : FinTM2 := toMachine conv .input .out

theorem initList_eq (x : List Sym) : (initList machine x).stk = initS x := by
  funext k; cases k <;> rfl

theorem haltList_eq (y : List Bool) : (haltList machine y).stk = outS y := by
  funext k; cases k <;> rfl

/-- The converter's time polynomial. -/
noncomputable def timePoly : Polynomial ℕ := C 10000 * (X + 1) ^ 3

theorem convBound_le (n : ℕ) : convBound n ≤ 10000 * (n + 1) ^ 3 := by
  unfold convBound stepQ litCost emitNatCost
  nlinarith [sq_nonneg (n + 1), Nat.zero_le n]

/-- The unary-to-binary conversion in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Unary.finEncoding CNF.Formula.finEncoding id where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun F := by
    have run := toMachine_outputsInTime_le conv .input .out (encode F) (CNF.Formula.encode F) _
      (by
        have h1 := initList_eq (encode F)
        have h2 := haltList_eq (CNF.Formula.encode F)
        simp only [machine] at h1 h2
        rw [h1, h2]
        exact conv_exits F)
    have run' := evalsToInTimeMono run
      (show convBound (encode F).length ≤ timePoly.eval (encode F).length by
        simp only [timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact convBound_le _)
    simpa [Equiv.refl] using! run'

/-- Unary SAT reduces to binary SAT by re-encoding. -/
noncomputable def satReduction : encodedUnarySAT.PolytimeReducesTo encodedSAT where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨computableInPolyTime⟩

/-- Unary exact 3-SAT reduces to binary exact 3-SAT by re-encoding. -/
noncomputable def exactThreeReduction :
    encodedUnaryExactThreeSAT.PolytimeReducesTo encodedExactThreeSAT where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨computableInPolyTime⟩

/-- Cook--Levin for the binary CNF encoding: CNF-SAT is NP-hard. -/
theorem encodedSAT_NPHard : encodedSAT.NPHard :=
  EncodedLanguage.NPHard.of_reduction satReduction CookLevin.encodedUnarySAT_NPHard

/-- Exact 3-SAT under the binary CNF encoding is NP-hard. -/
theorem encodedExactThreeSAT_NPHard : encodedExactThreeSAT.NPHard :=
  EncodedLanguage.NPHard.of_reduction exactThreeReduction
    ChainMachine.encodedUnaryExactThreeSAT_NPHard

end LeanNPHardness.BinaryConvert
