import LeanNPHardness.TableauEmitterBasics

/-!
# The skeleton emitter

Rounds are emitted chunk by chunk: the head chunks, then for every stack
(unrolled over the stack list) the cell chunks, with loops over copies of
the unary counters for the data-dependent counts, and the round end for
transition rounds. `emitter_exits` proves that the emitter leaves exactly
the reverse of `Instance.skeleton` on the skeleton stack and consumes the
input.
-/

namespace LeanNPHardness.TableauStacks

open Routines CNF.Unary TableauJobs

theorem flatMap_eq_flatten_map {α β : Type} (l : List α) (f : α → List β) :
    l.flatMap f = (l.map f).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem replicate_flatMap {α β : Type} (k : ℕ) (a : α) (f : α → List β) :
    (List.replicate k a).flatMap f = (List.replicate k (f a)).flatten := by
  rw [flatMap_eq_flatten_map, List.map_replicate]

theorem flatMap_flatMap' {α β γ : Type} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap fun a => (f a).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatMap_append, ih]

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  rw [flatMap_eq_flatten_map, flatMap_eq_flatten_map, List.map_congr_left h]

theorem flatMap_const_range {β : Type} (t : ℕ) (J : List β) :
    (List.range t).flatMap (fun _ => J) = (List.replicate t J).flatten := by
  induction t with
  | zero => rfl
  | succ t ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; simp

/-- One cell's job: its descriptor then the cell step. -/
def cellChunk (d : FormulaDesc) : List Instr := formulaJob d ++ cellStep

end LeanNPHardness.TableauStacks

namespace LeanNPHardness.MachineTableau.Instance

open Routines CNF.Unary TableauJobs TableauStacks MachineLocality

variable {Γx : Type} [Fintype Γx] [DecidableEq Γx] (I : Instance) (conv : Γx → I.tm.Γ I.tm.k₀)

theorem cellsJob_eq (f : I.tm.K → ℕ → FormulaDesc) :
    cellsJob (I.cellDescs f) =
      (stackList I.tm).flatMap fun k => ((List.range I.P).map (f k)).flatMap cellChunk := by
  rw [cellsJob, Instance.cellDescs, flatMap_flatMap']
  rfl

/-- The chunks of a round's head. -/
noncomputable def headChunks (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) : List (List Instr) :=
  [roundStart, formulaJob d0, formulaJob d1] ++ (List.range I.D).map fun i => formulaJob (dd (i + 2))

theorem headChunks_flatten (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) :
    (I.headChunks d0 d1 dd).flatten = roundStart ++ I.headJob d0 d1 dd := by
  simp [headChunks, Instance.headJob, flatMap_eq_flatten_map, List.append_assoc]

theorem headChunks_length (d0 d1 : FormulaDesc) (dd : ℕ → FormulaDesc) :
    (I.headChunks d0 d1 dd).length = 3 + I.D := by
  simp [headChunks]; omega

/-! ### Transition rounds -/

noncomputable def transStack (k : I.tm.K) : GRoutine Γx :=
  seq (emitList (List.replicate I.D (cellChunk I.phantomDesc) ++
      (List.range (2 * I.D)).map fun i => cellChunk (I.cellRealDesc k i)))
    (seq (emitG (cellChunk (I.cellRealDesc k (2 * I.D))))
      (emitList (List.replicate I.D (cellChunk I.phantomDesc))))

/-- The chunks of a transition stack at generic count `g`. -/
noncomputable def transChunks (k : I.tm.K) (g : ℕ) : List Instr :=
  (List.replicate I.D (cellChunk I.phantomDesc) ++
      (List.range (2 * I.D)).map fun i => cellChunk (I.cellRealDesc k i)).flatten ++
    ((List.replicate g (cellChunk (I.cellRealDesc k (2 * I.D)))).flatten ++
      (List.replicate I.D (cellChunk I.phantomDesc)).flatten)

noncomputable def transStackCost (g : ℕ) : ℕ := (I.D + 2 * I.D + 1) + ((7 * g + 3) + (I.D + 1))

theorem transStack_emits (k : I.tm.K) :
    EmitsOnly (Γx := Γx) (I.transStack k) (I.transChunks k) I.transStackCost := by
  have := emitsOnly_seq (emitsOnly_emitList (Γx := Γx)
      (List.replicate I.D (cellChunk I.phantomDesc) ++
        (List.range (2 * I.D)).map fun i => cellChunk (I.cellRealDesc k i)))
    (emitsOnly_seq (emitsOnly_emitG (Γx := Γx) (cellChunk (I.cellRealDesc k (2 * I.D))))
      (emitsOnly_emitList (Γx := Γx) (List.replicate I.D (cellChunk I.phantomDesc))))
  unfold transStack
  convert this using 1 <;> funext g
  · simp [transChunks]
  · simp [transStackCost]

theorem transChunks_G (k : I.tm.K) :
    I.transChunks k I.G = ((List.range I.P).map (I.cellTrans k)).flatMap cellChunk := by
  rw [I.range_P_map_cellTrans k]
  simp only [transChunks, flatMap_eq_flatten_map, List.map_append, List.flatten_append,
    List.map_replicate, List.map_map, Function.comp_def, List.append_assoc]

noncomputable def transRound : GRoutine Γx :=
  seq (emitList (I.headChunks I.labelTrans I.varTrans I.dummyTrans))
    (seq (foldStacks (stackList I.tm) I.transStack) (emit (roundEnd I.D)))

noncomputable def transRoundCost (g : ℕ) : ℕ :=
  (3 + I.D + 1) + (((stackList I.tm).map fun _ => I.transStackCost g).sum + 1 + 1)

theorem transRound_emits :
    EmitsOnly (Γx := Γx) I.transRound
      (fun g => roundStart ++ I.headJob I.labelTrans I.varTrans I.dummyTrans ++
        ((stackList I.tm).flatMap fun k => I.transChunks k g) ++ roundEnd I.D)
      I.transRoundCost := by
  have := emitsOnly_seq (emitsOnly_emitList (Γx := Γx) (I.headChunks I.labelTrans I.varTrans I.dummyTrans))
    (emitsOnly_seq (emitsOnly_foldStacks (Γx := Γx) (stackList I.tm) I.transStack I.transChunks
      (fun _ g => I.transStackCost g) fun k _ => I.transStack_emits k)
      (emitsOnly_emit (Γx := Γx) (roundEnd I.D)))
  unfold transRound
  convert this using 1
  · funext g
    simp only [headChunks_flatten, List.append_assoc]
  · funext g
    simp [transRoundCost, headChunks_length]

theorem transRound_chunks_G :
    roundStart ++ I.headJob I.labelTrans I.varTrans I.dummyTrans ++
        ((stackList I.tm).flatMap fun k => I.transChunks k I.G) ++ roundEnd I.D =
      I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans := by
  simp only [Instance.roundJob, Instance.openRound, cellsJob_eq]
  congr 2
  exact flatMap_congr_mem _ _ _ fun k _ => I.transChunks_G k

/-- All transition rounds, driven by a copy of the horizon counter. -/
noncomputable def transRounds : GRoutine Γx := loopRounds I.transRound

noncomputable def transRoundsCost (t g : ℕ) : ℕ := loopRoundsCost I.transRoundCost t g

theorem transRounds_exits (x xk : List Γx) (n q m t tpb w pw : ℕ) (sk : List Instr) :
    (I.transRounds (Γx := Γx)).Exits (emitStacks x xk n q m t tpb I.G w pw 0 0 sk)
      (I.transRoundsCost t I.G)
      (emitStacks x xk n q m t tpb I.G w pw 0 0
        (((List.range t).flatMap fun _ =>
          I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans).reverse ++ sk)) := by
  have := loopRounds_exits I.transRound _ _ I.transRound_emits x xk n q m t tpb I.G w pw sk
  rw [I.transRound_chunks_G, ← flatMap_const_range] at this
  exact this

/-! ### The final round -/

noncomputable def finalStack (k : I.tm.K) : GRoutine Γx :=
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  if k = I.tm.k₁ then
    seq (emitList (List.replicate I.D (cellChunk I.zeroDesc) ++ [cellChunk I.outDesc]))
      (seq (emitGpred (cellChunk I.zeroDesc))
        (emitList (List.replicate (3 * I.D) (cellChunk I.zeroDesc))))
  else seq (emitG (cellChunk I.zeroDesc)) (emitList (List.replicate (4 * I.D) (cellChunk I.zeroDesc)))

noncomputable def finalChunks (k : I.tm.K) (g : ℕ) : List Instr :=
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  if k = I.tm.k₁ then
    (List.replicate I.D (cellChunk I.zeroDesc) ++ [cellChunk I.outDesc]).flatten ++
      ((List.replicate (g - 1) (cellChunk I.zeroDesc)).flatten ++
        (List.replicate (3 * I.D) (cellChunk I.zeroDesc)).flatten)
  else (List.replicate g (cellChunk I.zeroDesc)).flatten ++
    (List.replicate (4 * I.D) (cellChunk I.zeroDesc)).flatten

noncomputable def finalStackCost (k : I.tm.K) (g : ℕ) : ℕ :=
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  if k = I.tm.k₁ then (I.D + 1 + 1) + ((4 * g + 2 + (1 + (3 * (g - 1) + 1))) + (3 * I.D + 1))
  else (7 * g + 3) + (4 * I.D + 1)

theorem finalStack_emits (k : I.tm.K) :
    EmitsOnly (Γx := Γx) (I.finalStack k) (I.finalChunks k) (I.finalStackCost k) := by
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  by_cases hk : k = I.tm.k₁
  · have := emitsOnly_seq (emitsOnly_emitList (Γx := Γx)
        (List.replicate I.D (cellChunk I.zeroDesc) ++ [cellChunk I.outDesc]))
      (emitsOnly_seq (emitsOnly_emitGpred (Γx := Γx) (cellChunk I.zeroDesc))
        (emitsOnly_emitList (Γx := Γx) (List.replicate (3 * I.D) (cellChunk I.zeroDesc))))
    simp only [finalStack, if_pos hk]
    convert this using 1 <;> funext g
    · simp [finalChunks, hk]
    · simp [finalStackCost, hk]
  · have := emitsOnly_seq (emitsOnly_emitG (Γx := Γx) (cellChunk I.zeroDesc))
      (emitsOnly_emitList (Γx := Γx) (List.replicate (4 * I.D) (cellChunk I.zeroDesc)))
    simp only [finalStack, if_neg hk]
    convert this using 1 <;> funext g
    · simp [finalChunks, hk]
    · simp [finalStackCost, hk]

theorem finalChunks_G (k : I.tm.K) :
    I.finalChunks k I.G = ((List.range I.P).map (I.finalCellDesc k)).flatMap cellChunk := by
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  have hG := I.G_ge_two
  by_cases hk : k = I.tm.k₁
  · subst hk
    rw [I.range_P_map_finalCellDesc, finalChunks, if_pos rfl,
      show I.G + 3 * I.D - 1 = (I.G - 1) + 3 * I.D by omega]
    simp only [flatMap_eq_flatten_map, List.map_append, List.flatten_append, List.map_replicate,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.replicate_add, List.append_assoc]
  · rw [I.range_P_map_finalCellDesc_of_ne k hk, finalChunks, if_neg hk, I.P_eq,
      List.replicate_add, List.flatMap_append, replicate_flatMap, replicate_flatMap]

noncomputable def finalRound : GRoutine Γx :=
  seq (emitList (I.headChunks (I.finalDesc 0) (I.finalDesc 1) I.finalDesc))
    (foldStacks (stackList I.tm) I.finalStack)

noncomputable def finalRoundCost (g : ℕ) : ℕ :=
  (3 + I.D + 1) + (((stackList I.tm).map fun k => I.finalStackCost k g).sum + 1)

theorem finalRound_exits (x xk : List Γx) (n q m t tpb w pw : ℕ) (sk : List Instr) :
    (I.finalRound (Γx := Γx)).Exits (emitStacks x xk n q m t tpb I.G w pw 0 0 sk)
      (I.finalRoundCost I.G)
      (emitStacks x xk n q m t tpb I.G w pw 0 0
        ((I.openRound (I.finalDesc 0) (I.finalDesc 1) I.finalDesc I.finalCellDesc).reverse ++ sk)) := by
  have := emitsOnly_seq (emitsOnly_emitList (Γx := Γx) (I.headChunks (I.finalDesc 0) (I.finalDesc 1) I.finalDesc))
    (emitsOnly_foldStacks (Γx := Γx) (stackList I.tm) I.finalStack I.finalChunks I.finalStackCost
      fun k _ => I.finalStack_emits k) x xk n q m t tpb I.G w pw 0 sk
  dsimp only at this
  have hch : I.openRound (I.finalDesc 0) (I.finalDesc 1) I.finalDesc I.finalCellDesc =
      (I.headChunks (I.finalDesc 0) (I.finalDesc 1) I.finalDesc).flatten ++
        (stackList I.tm).flatMap fun k => I.finalChunks k I.G := by
    simp only [Instance.openRound, cellsJob_eq, headChunks_flatten, List.append_assoc]
    congr 2
    exact flatMap_congr_mem _ _ _ fun k _ => (I.finalChunks_G k).symm
  have hcost : I.finalRoundCost I.G =
      (I.headChunks (I.finalDesc 0) (I.finalDesc 1) I.finalDesc).length + 1 +
        (((stackList I.tm).map fun k => I.finalStackCost k I.G).sum + 1) := by
    simp [finalRoundCost, headChunks_length]
  rw [hch, hcost]
  exact this

/-! ### The initial round -/

noncomputable def initStackInput : GRoutine Γx :=
  seq (emitList (List.replicate I.D (cellChunk I.zeroDesc)))
    (seq (loopInput fun s => cellChunk (I.symDesc (conv s)))
      (seq (seq (copyTo2 .q) (loopEmit2 (cellChunk I.chainDesc)))
        (seq (seq (copyTo2 .tpb) (loopEmit2 (cellChunk I.zeroDesc)))
          (emitList (List.replicate (2 + 3 * I.D) (cellChunk I.zeroDesc))))))

/-- The chunks of the input stack's initial cells. -/
noncomputable def initInputChunks (x : List Γx) (q tpb : ℕ) : List Instr :=
  (List.replicate I.D (cellChunk I.zeroDesc)).flatten ++
    ((x.map fun s => cellChunk (I.symDesc (conv s))).flatten ++
      ((List.replicate q (cellChunk I.chainDesc)).flatten ++
        ((List.replicate tpb (cellChunk I.zeroDesc)).flatten ++
          (List.replicate (2 + 3 * I.D) (cellChunk I.zeroDesc)).flatten)))

noncomputable def initInputCost (n q tpb : ℕ) : ℕ :=
  (I.D + 1) + ((3 * n + 1) + ((4 * q + 2 + (3 * q + 1)) + ((4 * tpb + 2 + (3 * tpb + 1)) +
    (2 + 3 * I.D + 1))))

theorem initStackInput_exits (x xk : List Γx) (n q m t tpb g w pw c1 : ℕ) (sk : List Instr) :
    (I.initStackInput conv).Exits (emitStacks x xk n q m t tpb g w pw c1 0 sk)
      (I.initInputCost x.length q tpb)
      (emitStacks [] xk n q m t tpb g w pw c1 0 ((I.initInputChunks conv x q tpb).reverse ++ sk)) := by
  set sk1 := (List.replicate I.D (cellChunk I.zeroDesc)).flatten.reverse ++ sk with hsk1
  set sk2 := (x.map fun s => cellChunk (I.symDesc (conv s))).flatten.reverse ++ sk1 with hsk2
  set sk3 := (List.replicate q (cellChunk I.chainDesc)).flatten.reverse ++ sk2 with hsk3
  set sk4 := (List.replicate tpb (cellChunk I.zeroDesc)).flatten.reverse ++ sk3 with hsk4
  have s1 := emitList_exits (Γx := Γx) (List.replicate I.D (cellChunk I.zeroDesc)) x xk n q m t tpb g w pw
    c1 0 sk
  have s2 := loopInput_exits (Γx := Γx) (fun s => cellChunk (I.symDesc (conv s))) x xk n q m t tpb g w pw
    c1 0 sk1
  have s3 := seq_exits _ _ (copyTo2_q_exits (Γx := Γx) [] xk n q m t tpb g w pw c1 sk2)
    (loopEmit2_exits (Γx := Γx) (cellChunk I.chainDesc) [] xk n q m t tpb g w pw c1 q sk2)
  have s4 := seq_exits _ _ (copyTo2_tpb_exits (Γx := Γx) [] xk n q m t tpb g w pw c1 sk3)
    (loopEmit2_exits (Γx := Γx) (cellChunk I.zeroDesc) [] xk n q m t tpb g w pw c1 tpb sk3)
  have s5 := emitList_exits (Γx := Γx) (List.replicate (2 + 3 * I.D) (cellChunk I.zeroDesc)) [] xk n q m t
    tpb g w pw c1 0 sk4
  have := seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4 s5)))
  unfold initStackInput
  convert this using 1
  · simp [initInputCost]
  · simp [sk4, sk3, sk2, sk1, initInputChunks, List.reverse_append, List.append_assoc]

omit [Fintype Γx] [DecidableEq Γx] in
theorem initInputChunks_eq (x : List Γx) (hx : I.input = x.map conv) :
    I.initInputChunks conv x I.certBound (I.horizon * I.pb) =
      ((List.range I.P).map (I.initCellDesc I.tm.k₀)).flatMap cellChunk := by
  rw [I.range_P_map_initCellDesc, hx,
    show I.horizon * I.pb + 2 + 3 * I.D = I.horizon * I.pb + (2 + 3 * I.D) by omega]
  simp only [initInputChunks, flatMap_eq_flatten_map, List.map_append, List.flatten_append,
    List.map_replicate, List.map_map, Function.comp_def, List.replicate_add, List.append_assoc]

noncomputable def initStack (k : I.tm.K) : GRoutine Γx :=
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  if k = I.tm.k₀ then I.initStackInput conv
  else seq (emitG (cellChunk I.zeroDesc)) (emitList (List.replicate (4 * I.D) (cellChunk I.zeroDesc)))

noncomputable def initOtherChunks (g : ℕ) : List Instr :=
  (List.replicate g (cellChunk I.zeroDesc)).flatten ++
    (List.replicate (4 * I.D) (cellChunk I.zeroDesc)).flatten

theorem initStack_emits_of_ne (k : I.tm.K) (hk : k ≠ I.tm.k₀) :
    EmitsOnly (Γx := Γx) (I.initStack conv k) I.initOtherChunks (fun g => (7 * g + 3) + (4 * I.D + 1)) := by
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  have := emitsOnly_seq (emitsOnly_emitG (Γx := Γx) (cellChunk I.zeroDesc))
    (emitsOnly_emitList (Γx := Γx) (List.replicate (4 * I.D) (cellChunk I.zeroDesc)))
  simp only [initStack, if_neg hk]
  convert this using 1 <;> funext g
  · simp [initOtherChunks]
  · simp

theorem initOtherChunks_G (k : I.tm.K) (hk : k ≠ I.tm.k₀) :
    I.initOtherChunks I.G = ((List.range I.P).map (I.initCellDesc k)).flatMap cellChunk := by
  rw [I.range_P_map_initCellDesc_of_ne k hk, initOtherChunks, replicate_flatMap, I.P_eq,
    List.replicate_add, List.flatten_append]

noncomputable def initRound : GRoutine Γx :=
  seq (emitList (I.headChunks (I.initDesc 0) (I.initDesc 1) I.initDesc))
    (foldStacks (stackList I.tm) (I.initStack conv))

/-- The chunks of an initial-row stack at the actual parameters. -/
noncomputable def initChunksAt (x : List Γx) (k : I.tm.K) : List Instr :=
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  if k = I.tm.k₀ then I.initInputChunks conv x I.certBound (I.horizon * I.pb) else I.initOtherChunks I.G

noncomputable def initStackCostAt (n : ℕ) (k : I.tm.K) : ℕ :=
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  if k = I.tm.k₀ then I.initInputCost n I.certBound (I.horizon * I.pb) else (7 * I.G + 3) + (4 * I.D + 1)

noncomputable def initRoundCost (n : ℕ) : ℕ :=
  (3 + I.D + 1) + (((stackList I.tm).map (I.initStackCostAt n)).sum + 1)

theorem initRound_exits (x xk : List Γx) (m w pw : ℕ) (sk : List Instr) :
    (I.initRound conv).Exits
      (emitStacks x xk x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0 sk)
      (I.initRoundCost x.length)
      (emitStacks [] xk x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0
        ((roundStart ++ I.headJob (I.initDesc 0) (I.initDesc 1) I.initDesc ++
          (stackList I.tm).flatMap (I.initChunksAt conv x)).reverse ++ sk)) := by
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp (mem_stackList I.tm I.tm.k₀)
  have hnodup := stackList_nodup I.tm
  rw [hsplit] at hnodup
  have hpre : I.tm.k₀ ∉ pre := by
    intro h
    exact (List.nodup_append.mp hnodup).2.2 _ h _ (List.mem_cons_self ..) rfl
  have hpost : I.tm.k₀ ∉ post := by
    have := (List.nodup_append.mp hnodup).2.1
    exact (List.nodup_cons.mp this).1
  have hhead := emitList_exits (Γx := Γx) (I.headChunks (I.initDesc 0) (I.initDesc 1) I.initDesc) x xk
    x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0 sk
  have hpostfold := emitsOnly_foldStacks post (I.initStack conv) (fun _ => I.initOtherChunks)
    (fun _ g => (7 * g + 3) + (4 * I.D + 1)) (fun k hk => I.initStack_emits_of_ne conv k
      (fun e => hpost (by rw [← e]; exact hk)))
  have hk0 := I.initStackInput_exits conv x xk x.length I.certBound m I.horizon (I.horizon * I.pb)
    I.G w pw 0
  have hmid : ∀ sk', (seq (I.initStack conv I.tm.k₀) (foldStacks post (I.initStack conv))).Exits
      (emitStacks x xk x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0 sk')
      (I.initInputCost x.length I.certBound (I.horizon * I.pb) +
        ((post.map fun _ => (7 * I.G + 3) + (4 * I.D + 1)).sum + 1))
      (emitStacks [] xk x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0
        ((I.initInputChunks conv x I.certBound (I.horizon * I.pb) ++
          post.flatMap fun _ => I.initOtherChunks I.G).reverse ++ sk')) := by
    intro sk'
    simp only [initStack, ↓reduceIte]
    have := seq_exits _ _ (hk0 sk') (hpostfold [] xk x.length I.certBound m I.horizon (I.horizon * I.pb)
      I.G w pw 0 _)
    simpa [List.reverse_append, List.append_assoc] using this
  have hprefold := foldr_emitsOnly_prefix pre (I.initStack conv) (fun _ => I.initOtherChunks)
    (fun _ g => (7 * g + 3) + (4 * I.D + 1)) (fun k hk => I.initStack_emits_of_ne conv k
      (fun e => hpre (by rw [← e]; exact hk))) _ x [] xk x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 _ _
    hmid
  have hfold : foldStacks (stackList I.tm) (I.initStack conv) =
      pre.foldr (fun k r => seq (I.initStack conv k) r)
        (seq (I.initStack conv I.tm.k₀) (foldStacks post (I.initStack conv))) := by
    rw [hsplit, foldStacks_append]
    rfl
  have hpreCost : pre.map (I.initStackCostAt x.length) =
      pre.map fun _ => (7 * I.G + 3) + (4 * I.D + 1) :=
    List.map_congr_left fun k hk => by
      simp only [initStackCostAt]
      rw [if_neg (fun e => hpre (by rw [← e]; exact hk))]
  have hpostCost : post.map (I.initStackCostAt x.length) =
      post.map fun _ => (7 * I.G + 3) + (4 * I.D + 1) :=
    List.map_congr_left fun k hk => by
      simp only [initStackCostAt]
      rw [if_neg (fun e => hpost (by rw [← e]; exact hk))]
  have hpreCh : pre.flatMap (I.initChunksAt conv x) = pre.flatMap fun _ => I.initOtherChunks I.G :=
    flatMap_congr_mem _ _ _ fun k hk => by
      simp only [initChunksAt]
      rw [if_neg (fun e => hpre (by rw [← e]; exact hk))]
  have hpostCh : post.flatMap (I.initChunksAt conv x) = post.flatMap fun _ => I.initOtherChunks I.G :=
    flatMap_congr_mem _ _ _ fun k hk => by
      simp only [initChunksAt]
      rw [if_neg (fun e => hpost (by rw [← e]; exact hk))]
  have hk0Ch : I.initChunksAt conv x I.tm.k₀ =
      I.initInputChunks conv x I.certBound (I.horizon * I.pb) := by
    rw [initChunksAt, if_pos rfl]
  have hk0Cost : I.initStackCostAt x.length I.tm.k₀ =
      I.initInputCost x.length I.certBound (I.horizon * I.pb) := by
    rw [initStackCostAt, if_pos rfl]
  have this := seq_exits _ _ hhead (hprefold _)
  rw [initRound, hfold]
  convert this using 1
  · rw [initRoundCost, hsplit, List.map_append, List.map_cons, hpreCost, hpostCost, hk0Cost,
      List.sum_append, List.sum_cons, headChunks_length]
    omega
  · apply congrArg
    rw [hsplit, headChunks_flatten, List.flatMap_append, List.flatMap_cons, hpreCh, hpostCh, hk0Ch]
    simp only [List.reverse_append, List.append_assoc]

omit [Fintype Γx] [DecidableEq Γx] in
theorem initRound_chunks_eq (x : List Γx) (hx : I.input = x.map conv) :
    roundStart ++ I.headJob (I.initDesc 0) (I.initDesc 1) I.initDesc ++
        (stackList I.tm).flatMap (I.initChunksAt conv x) =
      I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc := by
  letI : DecidableEq I.tm.K := I.tm.decidableEqK
  simp only [Instance.openRound, cellsJob_eq]
  congr 1
  apply List.flatMap_congr
  intro k _
  by_cases hk : k = I.tm.k₀
  · subst hk
    simp only [initChunksAt, ↓reduceIte]
    exact I.initInputChunks_eq conv x hx
  · simp only [initChunksAt, if_neg hk]
    exact I.initOtherChunks_G k hk

/-! ### The emitter -/

noncomputable def emitter : GRoutine Γx := seq (I.initRound conv) (seq I.transRounds I.finalRound)

noncomputable def emitterCost (n : ℕ) : ℕ :=
  I.initRoundCost n + (I.transRoundsCost I.horizon I.G + I.finalRoundCost I.G)

/-- The emitter consumes the input and leaves the reversed skeleton. -/
theorem emitter_exits (x : List Γx) (hx : I.input = x.map conv) (m w pw : ℕ) :
    (I.emitter conv).Exits
      (emitStacks x [] x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0 [])
      (I.emitterCost x.length)
      (emitStacks [] [] x.length I.certBound m I.horizon (I.horizon * I.pb) I.G w pw 0 0
        I.skeleton.reverse) := by
  have s1 := I.initRound_exits conv x [] m w pw []
  rw [I.initRound_chunks_eq conv x hx] at s1
  have s2 := I.transRounds_exits (Γx := Γx) [] [] x.length I.certBound m I.horizon (I.horizon * I.pb)
    w pw ((I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc).reverse ++ [])
  have s3 := I.finalRound_exits (Γx := Γx) [] [] x.length I.certBound m I.horizon (I.horizon * I.pb)
    w pw (((List.range I.horizon).flatMap fun _ =>
        I.roundJob I.labelTrans I.varTrans I.dummyTrans I.cellTrans).reverse ++
      ((I.openRound (I.initDesc 0) (I.initDesc 1) I.initDesc I.initCellDesc).reverse ++ []))
  have := seq_exits _ _ s1 (seq_exits _ _ s2 s3)
  simp only [emitter, emitterCost]
  convert this using 1
  apply congrArg
  simp only [Instance.skeleton, List.reverse_append, List.append_assoc, List.append_nil]

end LeanNPHardness.MachineTableau.Instance
