import LeanNPHardness.MaxCutSpec
import LeanNPHardness.ChainJob

/-!
# The Max-Cut gadget as an interpreter job

Registers: `base` holds the current block base, `win` the offset `4i` of
the current literal position, `w` the constant `1`, and `pw` accumulates
the threshold. A sign symbol closes the open edge, emits the occurrence
edge of a positive literal, and opens the literal's variable edge, whose
second endpoint `2v` is streamed by doubling the input marks. The end of a
clause closes the last edge, emits the block's two triangles and forcing
edge, advances `base`, and opens the next block's pendant edge.
`render_job` shows the job of `encode F` renders to the unary encoding of
`gadget F`.
-/

namespace LeanNPHardness.MaxCutJob

open CNF CNF.Unary TableauJobs ChainJob MaxCut

/-- `n` increments of register `r` by `w`. -/
def incr (r : RegName) (n : ℕ) : List Instr := List.replicate n (.addTo r .w)

/-- Emit the vertex `base + c`. -/
def vB (c : ℕ) : List Instr := .reg .base :: List.replicate c .mark

/-- An edge between `base + c` and `base + d`. -/
def eBB (c d : ℕ) : List Instr := .lit true :: vB c ++ .lit true :: vB d ++ [.endClause]

/-- An edge between `base + c` and vertex `1`. -/
def eB1 (c : ℕ) : List Instr := .lit true :: vB c ++ [.lit true, .mark, .endClause]

/-- The block's fixed edges. -/
def fixedJob : List Instr :=
  eBB 0 4 ++ eBB 4 12 ++ eBB 0 12 ++ eBB 14 8 ++ eB1 8 ++ eB1 14 ++ eBB 12 14

/-- Open the pendant edge of the block at `base`. -/
def openPend : List Instr := .lit true :: vB 16 ++ [.lit true]

/-- The occurrence edge of a positive literal. -/
def posEdge : List Instr :=
  [.lit true, .reg .base, .reg .win, .lit true, .reg .base, .reg .win, .mark, .mark, .endClause]

/-- Open the variable edge of a positive literal (from `t`). -/
def openPos : List Instr := [.lit true, .reg .base, .reg .win, .mark, .mark, .lit true]

/-- Open the variable edge of a negative literal (from `o`). -/
def openNeg : List Instr := [.lit true, .reg .base, .reg .win, .lit true]

/-- The chunk of one input symbol. -/
def chunk : Sym → List Instr
  | .mark => [.mark, .mark]
  | .pos => [.endClause] ++ posEdge ++ openPos ++ incr .win 4 ++ incr .pw 2
  | .neg => [.endClause] ++ openNeg ++ incr .win 4 ++ incr .pw 1
  | .endClause =>
      [.endClause] ++ fixedJob ++ incr .pw 6 ++ [.clear .win] ++ incr .base 18 ++ openPend

/-- The job of an input symbol list. -/
def body (L : List Sym) : List Instr := (L.map chunk).flatten

/-- Close the last pendant edge and emit the threshold. -/
def suffix : List Instr := [.endClause, .addTo .pw .w, .lit true, .reg .pw, .endClause]

/-- The whole job. -/
def job (L : List Sym) : List Instr := openPend ++ body L ++ suffix

theorem body_append (L M : List Sym) : body (L ++ M) = body L ++ body M := by simp [body]

/-! ### Rendering -/

/-- The symbols of a positive literal on `u`. -/
def epos (u : ℕ) : List Sym := encodeLiteral (.positive u)

/-- The symbols of an edge. -/
def edgeSyms (e : Edge) : List Sym := epos e.1 ++ epos e.2 ++ [.endClause]

theorem encode_edges (G : List Edge) (K : ℕ) :
    encode (graphFormula G K) = G.flatMap edgeSyms ++ epos K ++ [.endClause] := by
  induction G with
  | nil => simp [graphFormula, encode, encodeClause, epos]
  | cons e G ih =>
      simp only [graphFormula, List.map_cons, List.cons_append, encode_cons] at ih ⊢
      rw [ih]
      simp [encodeClause, edgeSyms, epos, List.append_assoc]

/-- Registers with given values. -/
def regs4 (b i k : ℕ) : Regs
  | .base => b
  | .win => i
  | .w => 1
  | .pw => k

theorem render_vB (R : Regs) (c : ℕ) :
    render R (vB c) = (List.replicate (R .base + c) .mark, R) := by
  simp only [vB, render, renderInstr, render_marks, List.replicate_append_replicate]

theorem render_eBB (b i k c d : ℕ) :
    render (regs4 b i k) (eBB c d) = (edgeSyms (b + c, b + d), regs4 b i k) := by
  simp [eBB, render_append, render, renderInstr, render_vB, edgeSyms, epos, encodeLiteral,
    regs4, List.append_assoc]

theorem render_eB1 (b i k c : ℕ) :
    render (regs4 b i k) (eB1 c) = (edgeSyms (b + c, 1), regs4 b i k) := by
  simp [eB1, render_append, render, renderInstr, render_vB, edgeSyms, epos, encodeLiteral,
    regs4, List.append_assoc]

theorem render_fixedJob (b i k : ℕ) :
    render (regs4 b i k) fixedJob = ((fixedEdges b).flatMap edgeSyms, regs4 b i k) := by
  simp only [fixedJob, render_append, render_eBB, render_eB1]
  simp [fixedEdges, List.append_assoc]

theorem render_incr (R : Regs) (r : RegName) (hr : r ≠ .w) (n : ℕ) :
    render R (incr r n) = ([], Function.update R r (R r + n * R .w)) := by
  induction n generalizing R with
  | zero => simp [incr, render]
  | succ n ih =>
      rw [incr, List.replicate_succ, render]
      have ih' := ih (Function.update R r (R r + R .w))
      simp only [incr] at ih'
      simp only [renderInstr, ih', List.nil_append, Function.update_self,
        Function.update_of_ne hr.symm, Function.update_idem]
      congr 2
      rw [Nat.succ_mul]; omega

theorem render_incr_win (b i k n : ℕ) :
    render (regs4 b i k) (incr .win n) = ([], regs4 b (i + n) k) := by
  rw [render_incr _ _ (by decide)]
  congr 1
  funext r; cases r <;> simp [regs4]

theorem render_incr_pw (b i k n : ℕ) :
    render (regs4 b i k) (incr .pw n) = ([], regs4 b i (k + n)) := by
  rw [render_incr _ _ (by decide)]
  congr 1
  funext r; cases r <;> simp [regs4]

theorem render_incr_base (b i k n : ℕ) :
    render (regs4 b i k) (incr .base n) = ([], regs4 (b + n) i k) := by
  rw [render_incr _ _ (by decide)]
  congr 1
  funext r; cases r <;> simp [regs4]

theorem render_clear_win (b i k : ℕ) : render (regs4 b i k) [.clear .win] = ([], regs4 b 0 k) := by
  simp only [render, renderInstr, List.append_nil]
  congr 1
  funext r; cases r <;> simp [regs4]

theorem render_endC (R : Regs) : render R [.endClause] = ([.endClause], R) := by
  simp [render, renderInstr]

theorem render_openPend (b i k : ℕ) :
    render (regs4 b i k) openPend = (epos (b + 16) ++ [.pos], regs4 b i k) := by
  simp [openPend, render, renderInstr, render_append, render_vB, epos, encodeLiteral, regs4]

theorem render_marks2' (R : Regs) (x : ℕ) :
    render R (body (List.replicate x .mark)) = (List.replicate (2 * x) .mark, R) := by
  induction x with
  | zero => simp [body, render]
  | succ x ih =>
      have hm : render R (body [Sym.mark]) = ([Sym.mark, Sym.mark], R) := by
        simp [body, chunk, render, renderInstr]
      rw [List.replicate_succ, show Sym.mark :: List.replicate x Sym.mark =
        [Sym.mark] ++ List.replicate x Sym.mark from rfl, body_append, render_append, hm]
      simp only [ih]
      rw [show 2 * (x + 1) = 2 + 2 * x by ring, List.replicate_add]
      rfl

/-- The symbols emitted for literal `l` at offset `i`, after closing the open edge. -/
def litOut (b i : ℕ) : Literal ℕ → List Sym
  | .positive v => edgeSyms (b + i, b + i + 2) ++ epos (b + i + 2) ++ [.pos] ++
      List.replicate (2 * v) .mark
  | .negative v => epos (b + i) ++ [.pos] ++ List.replicate (2 * v) .mark

/-- Threshold increment of a literal. -/
def litK : Literal ℕ → ℕ
  | .positive _ => 2
  | .negative _ => 1

theorem render_lit (b i k : ℕ) (l : Literal ℕ) :
    render (regs4 b i k) (body (encodeLiteral l)) =
      (.endClause :: litOut b i l, regs4 b (i + 4) (k + litK l)) := by
  cases l with
  | positive v =>
      rw [encodeLiteral, show Sym.pos :: List.replicate v Sym.mark =
        [Sym.pos] ++ List.replicate v Sym.mark from rfl, body_append, render_append]
      have hc : render (regs4 b i k) (body [Sym.pos]) =
          (.endClause :: (edgeSyms (b + i, b + i + 2) ++ epos (b + i + 2) ++ [.pos]),
            regs4 b (i + 4) (k + 2)) := by
        simp only [body, chunk, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, render_append]
        simp [render, renderInstr, posEdge, openPos, regs4, edgeSyms, epos, encodeLiteral,
          List.append_assoc, List.replicate_add, -List.replicate_append_replicate, render_incr_win,
          render_incr_pw]
      rw [hc]
      simp only [render_marks2']
      simp [litOut, litK, List.append_assoc]
  | negative v =>
      rw [encodeLiteral, show Sym.neg :: List.replicate v Sym.mark =
        [Sym.neg] ++ List.replicate v Sym.mark from rfl, body_append, render_append]
      have hc : render (regs4 b i k) (body [Sym.neg]) =
          (.endClause :: (epos (b + i) ++ [.pos]), regs4 b (i + 4) (k + 1)) := by
        simp only [body, chunk, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, render_append]
        simp [render, renderInstr, openNeg, regs4, epos, encodeLiteral,
          List.append_assoc, List.replicate_add, -List.replicate_append_replicate, render_incr_win,
          render_incr_pw]
      rw [hc]
      simp only [render_marks2']
      simp [litOut, litK, List.append_assoc]

/-- The literal symbols of a clause from offset `i`. -/
def litsOut (b : ℕ) : ℕ → Clause ℕ → List Sym
  | _, [] => []
  | i, l :: c => .endClause :: litOut b i l ++ litsOut b (i + 4) c

/-- Threshold increments of a clause. -/
def litsK : Clause ℕ → ℕ
  | [] => 0
  | l :: c => litK l + litsK c

theorem render_lits (b : ℕ) (c : Clause ℕ) : ∀ i k,
    render (regs4 b i k) (body (c.flatMap encodeLiteral)) =
      (litsOut b i c, regs4 b (i + 4 * c.length) (k + litsK c)) := by
  induction c with
  | nil => intro i k; simp [body, render, litsOut, litsK]
  | cons l c ih =>
      intro i k
      rw [List.flatMap_cons, body_append, render_append, render_lit, ih]
      simp only [litsOut, litsK, List.length_cons, List.cons_append]
      congr 2 <;> ring

/-- Telescoping: the literal symbols are the literal edges, shifted by one close. -/
theorem litsOut_edges (b : ℕ) (c : Clause ℕ) : ∀ i,
    litsOut b (4 * i) c ++ [.endClause] = .endClause :: (litsEdges b i c).flatMap edgeSyms := by
  induction c with
  | nil => intro i; simp [litsOut, litsEdges]
  | cons l c ih =>
      intro i
      have := ih (i + 1)
      rw [show 4 * (i + 1) = 4 * i + 4 by ring] at this
      simp only [litsOut, litsEdges, List.cons_append, List.flatMap_append, List.append_assoc,
        this]
      cases l with
      | positive v =>
          simp [litOut, litEdges, edgeSyms, epos, encodeLiteral, List.append_assoc]
      | negative v =>
          simp [litOut, litEdges, edgeSyms, epos, encodeLiteral, List.append_assoc]

theorem litsK_eq (b : ℕ) (c : Clause ℕ) : ∀ i, litsK c = (litsEdges b i c).length := by
  induction c with
  | nil => intro i; rfl
  | cons l c ih => intro i; cases l <;> simp [litsK, litK, litsEdges, litEdges, ih (i + 1)] <;> omega

theorem gadgetEdges_length (F : Formula ℕ) : ∀ b,
    2 * F.length + 1 ≤ (gadgetEdges b F).length := by
  induction F with
  | nil => intro b; simp [gadgetEdges]
  | cons c F ih =>
      intro b
      have := ih (b + 18)
      simp [gadgetEdges, fixedEdges]
      omega

/-- The job renders to the unary encoding of the gadget. -/
theorem render_out (F : Formula ℕ) : ∀ b k,
    (render (regs4 b 0 k) (openPend ++ body (encode F) ++ suffix)).1 =
      encode (graphFormula (gadgetEdges b F) (k + (gadgetEdges b F).length - 2 * F.length)) := by
  induction F with
  | nil =>
      intro b k
      simp only [encode_nil, body, List.map_nil, List.flatten_nil, List.append_nil, render_append,
        render_openPend, suffix]
      rw [encode_edges]
      simp [render, renderInstr, regs4, gadgetEdges, edgeSyms, epos, encodeLiteral,
        List.append_assoc]
  | cons c F ih =>
      intro b k
      have hjob : openPend ++ body (encode (c :: F)) ++ suffix =
          (openPend ++ body (c.flatMap encodeLiteral) ++ [.endClause] ++ fixedJob ++ incr .pw 6 ++
            [.clear .win] ++ incr .base 18) ++ (openPend ++ body (encode F) ++ suffix) := by
        simp only [encode_cons, encodeClause, body_append]
        simp [body, chunk, List.append_assoc]
      have hfirst : render (regs4 b 0 k) (openPend ++ body (c.flatMap encodeLiteral) ++
          [.endClause] ++ fixedJob ++ incr .pw 6 ++ [.clear .win] ++ incr .base 18) =
          (((b + 16, 0) :: litsEdges b 0 c ++ fixedEdges b).flatMap edgeSyms,
            regs4 (b + 18) 0 (k + litsK c + 6)) := by
        simp only [render_append, render_openPend, render_lits]
        simp only [render_endC, render_fixedJob, render_incr_pw, render_clear_win,
          render_incr_base]
        refine Prod.ext ?_ (by simp)
        have hlo := litsOut_edges b c 0
        simp only [Nat.mul_zero] at hlo
        simp only [List.flatMap_cons, List.flatMap_append, List.append_assoc]
        rw [← List.append_assoc (litsOut b 0 c), hlo]
        simp [edgeSyms, epos, encodeLiteral, List.append_assoc]
      rw [hjob, render_append, hfirst]
      simp only
      rw [ih (b + 18) (k + litsK c + 6)]
      simp only [gadgetEdges, encode_edges, List.flatMap_append, List.append_assoc,
        List.length_append, List.length_cons]
      have hge := gadgetEdges_length F (b + 18)
      have hk := litsK_eq b c 0
      congr 4
      congr 1
      simp [fixedEdges]
      omega

/-- Registers at the start of the job. -/
def initRegs : Regs := regs4 3 0 0

theorem render_job (F : Formula ℕ) :
    (render initRegs (job (encode F))).1 = unaryEncoding.encode (gadget F) := by
  have := render_out F 3 0
  simp only [Nat.zero_add] at this
  exact this

end LeanNPHardness.MaxCutJob
