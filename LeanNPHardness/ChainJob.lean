import LeanNPHardness.CNFChain
import LeanNPHardness.TableauRegisterBounds

/-!
# The chain transformation as an interpreter job

Each input symbol of the unary encoding contributes a fixed instruction
chunk (`chunk`): marks are doubled, a sign closes the previous literal's
chain clause and opens the next literal, and the end of a clause closes the
chain, emits the final clause, advances the fresh base, and opens the next
clause. The fresh base lives in the `base` register (start `1`, step `2`
via `w = 1`). `render_job` shows the job of `encode F` renders to
`encode (chainThree F)`.
-/

namespace LeanNPHardness.ChainJob

open CNF CNF.Unary CNF.Chain TableauJobs

/-- Advance the fresh base by two. -/
def adv2 : List Instr := [.addTo .base .w, .addTo .base .w]

/-- Emit `¬y₀ ∨ ¬y₀ ∨ ¬y₀` and open the dummy literal `y₀`. -/
def open0 : List Instr :=
  [.lit false, .reg .base, .lit false, .reg .base, .lit false, .reg .base, .endClause,
    .lit true, .reg .base]

/-- Close the open literal's clause with `¬y_{next} ∨ y_{prev}` and advance. -/
def close : List Instr :=
  [.lit false, .reg .base, .mark, .mark, .lit true, .reg .base, .endClause] ++ adv2

/-- The final clause `y ∨ y ∨ y`. -/
def final : List Instr :=
  [.lit true, .reg .base, .lit true, .reg .base, .lit true, .reg .base, .endClause]

/-- The chunk of one input symbol. -/
def chunk : Sym → List Instr
  | .mark => [.mark, .mark]
  | .pos => close ++ [.lit true]
  | .neg => close ++ [.lit false]
  | .endClause => close ++ final ++ adv2 ++ open0

/-- The job of an input symbol list. -/
def body (L : List Sym) : List Instr := (L.map chunk).flatten

/-- The whole job. -/
def job (L : List Sym) : List Instr := open0 ++ body L ++ close

theorem body_append (L M : List Sym) : body (L ++ M) = body L ++ body M := by
  simp [body]

/-! ### Rendering -/

/-- Registers with the fresh base set to `b`. -/
def setBase (R : Regs) (b : ℕ) : Regs := Function.update R .base b

@[simp] theorem setBase_base (R : Regs) (b : ℕ) : setBase R b .base = b := by simp [setBase]
@[simp] theorem setBase_w (R : Regs) (b : ℕ) : setBase R b .w = R .w := by
  simp [setBase, Function.update_of_ne]
@[simp] theorem setBase_setBase (R : Regs) (b c : ℕ) : setBase (setBase R b) c = setBase R c := by
  simp [setBase]
theorem setBase_self (R : Regs) : setBase R (R .base) = R := by simp [setBase]

/-- The symbols closing a chain clause from previous variable `b`. -/
def closeSyms (b : ℕ) : List Sym :=
  encodeLiteral (.negative (b + 2)) ++ encodeLiteral (.positive b) ++ [.endClause]

theorem replicate_mark_add (a b : ℕ) :
    List.replicate a Sym.mark ++ List.replicate b Sym.mark = List.replicate (a + b) Sym.mark := by
  rw [List.replicate_add]

theorem render_adv2 (R : Regs) (hw : R .w = 1) :
    render R adv2 = ([], setBase R (R .base + 2)) := by
  simp only [adv2, render, renderInstr, List.nil_append, Function.update_self,
    Function.update_of_ne (show RegName.w ≠ .base by decide), hw, Function.update_idem]
  rfl

theorem render_open0 (R : Regs) :
    render R open0 = (encodeClause [.negative (R .base), .negative (R .base), .negative (R .base)] ++
      encodeLiteral (.positive (R .base)), R) := by
  simp [open0, render, renderInstr, encodeClause, encodeLiteral]

theorem render_final (R : Regs) :
    render R final = (encodeClause [.positive (R .base), .positive (R .base), .positive (R .base)], R) := by
  simp [final, render, renderInstr, encodeClause, encodeLiteral]

theorem render_close (R : Regs) (hw : R .w = 1) :
    render R close = (closeSyms (R .base), setBase R (R .base + 2)) := by
  rw [close, render_append, render_adv2 _ (by simp [render, renderInstr, hw])]
  simp [render, renderInstr, closeSyms, encodeLiteral, List.replicate_add]

theorem render_marks2 (R : Regs) (x : ℕ) :
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

theorem render_lit (R : Regs) (hw : R .w = 1) (l : Literal ℕ) :
    render R (body (encodeLiteral l)) =
      (closeSyms (R .base) ++ encodeLiteral l.double, setBase R (R .base + 2)) := by
  cases l with
  | positive x =>
      rw [encodeLiteral, show Sym.pos :: List.replicate x Sym.mark =
        [Sym.pos] ++ List.replicate x Sym.mark from rfl, body_append, render_append]
      simp only [body, chunk, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      rw [render_append, render_close R hw]
      have := render_marks2 (setBase R (R .base + 2)) x
      simp only [body, List.map_replicate] at this
      simp [render, renderInstr, this, Literal.double, encodeLiteral]
  | negative x =>
      rw [encodeLiteral, show Sym.neg :: List.replicate x Sym.mark =
        [Sym.neg] ++ List.replicate x Sym.mark from rfl, body_append, render_append]
      simp only [body, chunk, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      rw [render_append, render_close R hw]
      have := render_marks2 (setBase R (R .base + 2)) x
      simp only [body, List.map_replicate] at this
      simp [render, renderInstr, this, Literal.double, encodeLiteral]

/-- The symbols rendered for a literal list from previous variable `b`. -/
def litsOut (b : ℕ) : Clause ℕ → List Sym
  | [] => []
  | l :: ls => closeSyms b ++ encodeLiteral l.double ++ litsOut (b + 2) ls

theorem render_lits (c : Clause ℕ) : ∀ (R : Regs), R .w = 1 →
    render R (body (c.flatMap encodeLiteral)) =
      (litsOut (R .base) c, setBase R (R .base + 2 * c.length)) := by
  induction c with
  | nil => intro R _; simp [body, render, litsOut, setBase_self]
  | cons l ls ih =>
      intro R hw
      rw [List.flatMap_cons, body_append, render_append, render_lit R hw,
        ih _ (by simp [hw])]
      simp only [setBase_base, setBase_setBase, litsOut, List.append_assoc, List.length_cons]
      congr 2
      ring

theorem litsOut_close (c : Clause ℕ) : ∀ b,
    litsOut b c ++ closeSyms (b + 2 * c.length) = closeSyms b ++ encode (chain (b + 2) c) := by
  induction c with
  | nil => intro b; simp [litsOut, chain]
  | cons l ls ih =>
      intro b
      have := ih (b + 2)
      rw [show b + 2 + 2 * ls.length = b + 2 * (l :: ls).length by simp; ring] at this
      simp only [litsOut, chain, encode_cons, List.append_assoc, this]
      simp [encodeClause, closeSyms, List.append_assoc, encodeLiteral]

theorem encodeClause_chainHead (b : ℕ) :
    encodeClause [.positive b, .negative (b + 2), .positive b] =
      encodeLiteral (.positive b) ++ closeSyms b := by
  simp [encodeClause, closeSyms, encodeLiteral]

/-- The job of `encode F` renders to `encode (out b F)`. -/
theorem render_out (F : Formula ℕ) : ∀ (R : Regs), R .w = 1 →
    (render R (open0 ++ body (encode F) ++ close)).1 = encode (out (R .base) F) := by
  induction F with
  | nil =>
      intro R hw
      simp only [encode_nil, body, List.map_nil, List.flatten_nil, List.append_nil, render_append,
        render_open0, render_close R hw, out, tail, encode_cons, encode_nil]
      simp [encodeClause_chainHead, List.append_assoc]
  | cons c F ih =>
      intro R hw
      have hjob : open0 ++ body (encode (c :: F)) ++ close =
          (open0 ++ body (c.flatMap encodeLiteral) ++ close ++ final ++ adv2) ++
            (open0 ++ body (encode F) ++ close) := by
        simp only [encode_cons, encodeClause, body_append]
        simp [body, chunk, List.append_assoc]
      have hfirst : render R (open0 ++ body (c.flatMap encodeLiteral) ++ close ++ final ++ adv2) =
          (encode (block (R .base) c), setBase R (R .base + 2 * (c.length + 2))) := by
        rw [render_append, render_append, render_append, render_append, render_open0,
          render_lits c R hw, render_close _ (by simp [hw]), render_final,
          render_adv2 _ (by simp [hw])]
        simp only [setBase_base, setBase_setBase]
        refine Prod.ext ?_ ?_
        · simp only [block, encode_cons, encode_append, encode_nil, List.append_nil]
          rw [encodeClause_chainHead, show R .base + 2 * c.length + 2 = R .base + 2 * (c.length + 1) by
            ring]
          have hlc := litsOut_close c (R .base)
          simp only [List.append_assoc] at hlc ⊢
          rw [← List.append_assoc (litsOut _ c), hlc]
          simp only [List.append_assoc]
        · show setBase R (R .base + 2 * c.length + 2 + 2) = _
          ring_nf
      rw [hjob, render_append, hfirst]
      simp only
      rw [ih _ (by simp [hw]), setBase_base, out, encode_append]

/-- Registers at the start of the job. -/
def initRegs : Regs
  | .base => 1
  | .w => 1
  | _ => 0

theorem render_job (F : Formula ℕ) :
    (render initRegs (job (encode F))).1 = encode (chainThree F) :=
  render_out F initRegs rfl

/-! ### Validity and register bounds -/

/-- Instructions that are pure or advance the base by `w`. -/
def Tame (i : Instr) : Prop := i.pure ∨ i = .addTo .base .w

theorem tame_chunk (s : Sym) : ∀ i ∈ chunk s, Tame i := by
  cases s <;> simp [chunk, close, final, adv2, open0, Tame, Instr.pure]

theorem tame_job (L : List Sym) : ∀ i ∈ job L, Tame i := by
  intro i hi
  simp only [job, body, List.mem_append, List.mem_flatten, List.mem_map] at hi
  rcases hi with (h | ⟨_, ⟨s, _, rfl⟩, h⟩) | h
  · revert i; simp [open0, Tame, Instr.pure]
  · exact tame_chunk s i h
  · revert i; simp [close, adv2, Tame, Instr.pure]

theorem ok_of_tame {i : Instr} (h : Tame i) : i.ok := by
  rcases h with h | rfl
  · rcases i with _ | _ | _ | _ | ⟨d, s⟩ | _ <;> trivial
  · show RegName.base ≠ RegName.w
    decide

theorem render_tame (J : List Instr) : ∀ R : Regs, (∀ i ∈ J, Tame i) → R .w = 1 →
    ∃ k ≤ J.length, (render R J).2 = setBase R (R .base + k) := by
  induction J with
  | nil => intro R _ _; exact ⟨0, le_rfl, by simp [render, setBase_self]⟩
  | cons i J ih =>
      intro R hJ hw
      rcases hJ i (List.mem_cons_self ..) with hp | rfl
      · obtain ⟨k, hk, h⟩ := ih R (fun j hj => hJ j (List.mem_cons_of_mem _ hj)) hw
        refine ⟨k, by simp; omega, ?_⟩
        simp only [render]
        rw [renderInstr_pure_snd R i hp, h]
      · have hR : (renderInstr R (.addTo .base .w)).2 = setBase R (R .base + 1) := by
          simp [renderInstr, setBase, hw]
        obtain ⟨k, hk, h⟩ := ih (setBase R (R .base + 1))
          (fun j hj => hJ j (List.mem_cons_of_mem _ hj)) (by simp [hw])
        refine ⟨k + 1, by simp; omega, ?_⟩
        simp only [render]
        rw [hR, h]
        simp only [setBase_base, setBase_setBase]
        congr 1
        omega

theorem prefixLE_tame (J : List Instr) (R : Regs) (hJ : ∀ i ∈ J, Tame i) (hw : R .w = 1) (M : ℕ)
    (hM : ∀ r, R r + J.length ≤ M) : PrefixLE M R J := by
  intro i hi r
  obtain ⟨k, hk, h⟩ := render_tame (J.take i) R (fun j hj => hJ j (List.mem_of_mem_take hj)) hw
  rw [h]
  have hk' : k ≤ J.length := le_trans hk (by simp)
  by_cases hr : r = .base
  · subst hr
    have := hM .base
    simp only [setBase_base]
    omega
  · have := hM r
    simp only [setBase, Function.update_of_ne hr]
    omega

theorem chunk_length_le (s : Sym) : (chunk s).length ≤ 27 := by
  cases s <;> simp [chunk, close, final, adv2, open0]

theorem job_length_le (L : List Sym) : (job L).length ≤ 27 * L.length + 18 := by
  have : (body L).length ≤ 27 * L.length := by
    induction L with
    | nil => simp [body]
    | cons s L ih =>
        have := chunk_length_le s
        simp only [body, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
        simp only [List.length_cons]
        omega
  simp only [job, List.length_append]
  simp only [open0, close, adv2, List.length_cons, List.length_nil, List.length_append]
  omega

end LeanNPHardness.ChainJob
