import LeanNPHardness.VerifierClause
import Mathlib.Tactic.Ring

/-!
# The exact 3-SAT verifier machine: consistency check

Entries on `L` are compared pairwise. `readEntryL`/`readEntryS` pop one
entry (variable bits, then a polarity terminator); `eqLoop_exits` compares
two entries in lockstep and records a conflict mark on `CONF` exactly when
the variable bits agree and the terminators differ (`entryConflict`). The
inner and outer loops (`innerLoop_exits`, `outerLoop_exits`) leave one
mark per conflicting ordered pair, so `CONF` stays empty exactly when the
selected literals are consistent (`checkPhase_exits`).
-/

namespace LeanNPHardness.ExactThreeVerify

open Routines CNF CNF.Unary
open LeanNPHardness.BinaryConvert (b2s s2b s2b_b2s marks marks_succ marks_zero marks_length
  marks_eq_nil marks_reverse marks_add bitsOf bitsOf_eq bitsOf_pos)

theorem term_ne_bit (t b : Bool) : term t ≠ b2s b := by cases t <;> cases b <;> decide

theorem term_injective : Function.Injective term := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem b2s_injective : Function.Injective b2s := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)


/-- Pop one entry from `L` onto `X`. -/
def reH_L : Sym → VR
  | .pos => pushList .X [.pos]
  | .neg => pushList .X [.neg]
  | .mark => seq (pushList .X [.mark]) (popOne .G)
  | .endClause => seq (pushList .X [.endClause]) (popOne .G)

def readEntry_L : VR := seq (pushList .G [.mark]) (loop .G (dispatch .L reH_L))

theorem reLoop_L (u : List Bool) (t : Bool) : ∀ (S : VS) (rest D : List Sym),
    S .L = bsyms u ++ term t :: rest → S .X = D → S .G = [.mark] →
    (loop .G (dispatch .L reH_L)).ExitsLE S (3 * u.length + 5)
      (Function.update (Function.update (Function.update S .L rest) .X
        (term t :: ((bsyms u).reverse ++ D))) .G []) := by
  induction u with
  | nil =>
      intro S rest D hs hd hg
      have hh : (reH_L (term t)).ExitsLE (Function.update S .L rest) 2
          (Function.update (Function.update (Function.update S .L rest) .X (term t :: D)) .G []) := by
        cases t
        · refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.X [Sym.mark] _ 0)
            (popOne_exitsLE (Γ := VAlpha) VStack.G _ 0)).congr ?_
          funext k; cases k <;> simp [hd, hg, term]
        · refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.X [Sym.endClause] _ 0)
            (popOne_exitsLE (Γ := VAlpha) VStack.G _ 0)).congr ?_
          funext k; cases k <;> simp [hd, hg, term]
      have := loop_exitsLE_cons (Γ := VAlpha) VStack.G _ (by simp [hg])
        (dispatch_exitsLE (Γ := VAlpha) .L reH_L S (term t) rest (by simpa [bsyms] using hs) hh)
        (loop_exitsLE_nil (Γ := VAlpha) VStack.G (dispatch .L reH_L) _ (by simp) 0)
      refine (this.mono (by omega)).congr ?_
      funext k; cases k <;> simp [bsyms]
  | cons b u ih =>
      intro S rest D hs hd hg
      have hh : (reH_L (b2s b)).ExitsLE (Function.update S .L (bsyms u ++ term t :: rest)) 1
          (Function.update (Function.update S .L (bsyms u ++ term t :: rest)) .X
            (b2s b :: D)) := by
        cases b
        · exact (pushList_exitsLE (Γ := VAlpha) VStack.X [Sym.neg] _ 0).congr
            (by funext k; cases k <;> simp [hd, b2s])
        · exact (pushList_exitsLE (Γ := VAlpha) VStack.X [Sym.pos] _ 0).congr
            (by funext k; cases k <;> simp [hd, b2s])
      have h2 := ih (Function.update (Function.update S .L (bsyms u ++ term t :: rest)) .X
          (b2s b :: D)) rest (b2s b :: D) (by simp) (by simp) (by simp [hg])
      have := loop_exitsLE_cons (Γ := VAlpha) VStack.G _ (by simp [hg])
        (dispatch_exitsLE (Γ := VAlpha) .L reH_L S (b2s b) _ (by simpa [bsyms] using hs) hh) h2
      refine (this.mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp [bsyms, List.reverse_cons, List.append_assoc]

theorem readEntry_L_exits (u : List Bool) (t : Bool) (S : VS) (rest : List Sym)
    (hs : S .L = bsyms u ++ term t :: rest) (hg : S .G = []) :
    readEntry_L.ExitsLE S (3 * u.length + 6)
      (Function.update (Function.update S .L rest) .X
        (term t :: ((bsyms u).reverse ++ S .X))) := by
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G [Sym.mark] S 0)
    (reLoop_L u t _ rest (S .X) (by simp [hs]) (by simp) (by simp [hg]))
  refine (this.mono (by omega)).congr ?_
  funext k; cases k <;> simp [hg]

/-- Pop one entry from `SC` onto `Y`. -/
def reH_S : Sym → VR
  | .pos => pushList .Y [.pos]
  | .neg => pushList .Y [.neg]
  | .mark => seq (pushList .Y [.mark]) (popOne .G)
  | .endClause => seq (pushList .Y [.endClause]) (popOne .G)

def readEntry_S : VR := seq (pushList .G [.mark]) (loop .G (dispatch .SC reH_S))

theorem reLoop_S (u : List Bool) (t : Bool) : ∀ (S : VS) (rest D : List Sym),
    S .SC = bsyms u ++ term t :: rest → S .Y = D → S .G = [.mark] →
    (loop .G (dispatch .SC reH_S)).ExitsLE S (3 * u.length + 5)
      (Function.update (Function.update (Function.update S .SC rest) .Y
        (term t :: ((bsyms u).reverse ++ D))) .G []) := by
  induction u with
  | nil =>
      intro S rest D hs hd hg
      have hh : (reH_S (term t)).ExitsLE (Function.update S .SC rest) 2
          (Function.update (Function.update (Function.update S .SC rest) .Y (term t :: D)) .G []) := by
        cases t
        · refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.Y [Sym.mark] _ 0)
            (popOne_exitsLE (Γ := VAlpha) VStack.G _ 0)).congr ?_
          funext k; cases k <;> simp [hd, hg, term]
        · refine (seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.Y [Sym.endClause] _ 0)
            (popOne_exitsLE (Γ := VAlpha) VStack.G _ 0)).congr ?_
          funext k; cases k <;> simp [hd, hg, term]
      have := loop_exitsLE_cons (Γ := VAlpha) VStack.G _ (by simp [hg])
        (dispatch_exitsLE (Γ := VAlpha) .SC reH_S S (term t) rest (by simpa [bsyms] using hs) hh)
        (loop_exitsLE_nil (Γ := VAlpha) VStack.G (dispatch .SC reH_S) _ (by simp) 0)
      refine (this.mono (by omega)).congr ?_
      funext k; cases k <;> simp [bsyms]
  | cons b u ih =>
      intro S rest D hs hd hg
      have hh : (reH_S (b2s b)).ExitsLE (Function.update S .SC (bsyms u ++ term t :: rest)) 1
          (Function.update (Function.update S .SC (bsyms u ++ term t :: rest)) .Y
            (b2s b :: D)) := by
        cases b
        · exact (pushList_exitsLE (Γ := VAlpha) VStack.Y [Sym.neg] _ 0).congr
            (by funext k; cases k <;> simp [hd, b2s])
        · exact (pushList_exitsLE (Γ := VAlpha) VStack.Y [Sym.pos] _ 0).congr
            (by funext k; cases k <;> simp [hd, b2s])
      have h2 := ih (Function.update (Function.update S .SC (bsyms u ++ term t :: rest)) .Y
          (b2s b :: D)) rest (b2s b :: D) (by simp) (by simp) (by simp [hg])
      have := loop_exitsLE_cons (Γ := VAlpha) VStack.G _ (by simp [hg])
        (dispatch_exitsLE (Γ := VAlpha) .SC reH_S S (b2s b) _ (by simpa [bsyms] using hs) hh) h2
      refine (this.mono (by simp; omega)).congr ?_
      funext k; cases k <;> simp [bsyms, List.reverse_cons, List.append_assoc]

theorem readEntry_S_exits (u : List Bool) (t : Bool) (S : VS) (rest : List Sym)
    (hs : S .SC = bsyms u ++ term t :: rest) (hg : S .G = []) :
    readEntry_S.ExitsLE S (3 * u.length + 6)
      (Function.update (Function.update S .SC rest) .Y
        (term t :: ((bsyms u).reverse ++ S .Y))) := by
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G [Sym.mark] S 0)
    (reLoop_S u t _ rest (S .Y) (by simp [hs]) (by simp) (by simp [hg]))
  refine (this.mono (by omega)).congr ?_
  funext k; cases k <;> simp [hg]

/-! ### Comparing two entries -/

/-- One lockstep comparison step. -/
def eqH : Sym → Sym → VR
  | .pos, .pos => skip
  | .neg, .neg => skip
  | .pos, .neg => seq (popOne .G2) (seq (drain .XC) (drain .Y2))
  | .neg, .pos => seq (popOne .G2) (seq (drain .XC) (drain .Y2))
  | .mark, .mark => popOne .G2
  | .endClause, .endClause => popOne .G2
  | .mark, .endClause => seq (popOne .G2) (pushList .CONF [.mark])
  | .endClause, .mark => seq (popOne .G2) (pushList .CONF [.mark])
  | .pos, _ => seq (popOne .G2) (drain .XC)
  | .neg, _ => seq (popOne .G2) (drain .XC)
  | _, _ => seq (popOne .G2) (drain .Y2)

theorem eqH_same (a : Bool) : eqH (b2s a) (b2s a) = skip := by cases a <;> rfl
theorem eqH_diff (a b : Bool) (h : a ≠ b) :
    eqH (b2s a) (b2s b) = seq (popOne .G2) (seq (drain .XC) (drain .Y2)) := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl h
theorem eqH_terms_eq (t : Bool) : eqH (term t) (term t) = popOne .G2 := by cases t <;> rfl
theorem eqH_terms_ne (t1 t2 : Bool) (h : t1 ≠ t2) :
    eqH (term t1) (term t2) = seq (popOne .G2) (pushList .CONF [.mark]) := by
  cases t1 <;> cases t2 <;> first | rfl | exact absurd rfl h
theorem eqH_bit_term (a t : Bool) : eqH (b2s a) (term t) = seq (popOne .G2) (drain .XC) := by
  cases a <;> cases t <;> rfl
theorem eqH_term_bit (t b : Bool) : eqH (term t) (b2s b) = seq (popOne .G2) (drain .Y2) := by
  cases t <;> cases b <;> rfl

/-- One step: pop both entries' next symbols and compare. -/
def eqStep : VR := dispatch .XC fun x => dispatch .Y2 (eqH x)

/-- Compare the entries on `XC` and `Y2`, consuming both. -/
def eqCheck : VR := seq (pushList .G2 [.mark]) (loop .G2 eqStep)

theorem eqLoop_exits (u1 : List Bool) : ∀ (u2 : List Bool) (t1 t2 : Bool) (S : VS),
    S .XC = bsyms u1 ++ [term t1] → S .Y2 = bsyms u2 ++ [term t2] → S .G2 = [.mark] →
    (loop .G2 eqStep).ExitsLE S (4 * (u1.length + u2.length) + 10)
      (Function.update (Function.update (Function.update (Function.update S .XC []) .Y2 []) .G2 [])
        .CONF ((if u1 = u2 ∧ t1 ≠ t2 then [.mark] else []) ++ S .CONF)) := by
  induction u1 with
  | nil =>
      intro u2 t1 t2 S hx hy hg
      cases u2 with
      | nil =>
          by_cases ht : t1 = t2
          · subst ht
            have hh : (eqH (term t1) (term t1)).ExitsLE
                (Function.update (Function.update S .XC []) .Y2 []) 1
                (Function.update (Function.update (Function.update S .XC []) .Y2 []) .G2
                  ((Function.update (Function.update S .XC []) .Y2 []) .G2).tail) := by
              rw [eqH_terms_eq]; exact popOne_exitsLE (Γ := VAlpha) VStack.G2 _ 0
            have := loop_exitsLE_cons (Γ := VAlpha) VStack.G2 eqStep (by simp [hg])
              (dispatch_exitsLE (Γ := VAlpha) .XC _ S (term t1) [] (by simp [hx, bsyms])
                (dispatch_exitsLE (Γ := VAlpha) .Y2 (eqH (term t1)) (Function.update S .XC [])
                  (term t1) [] (by simp [hy, bsyms]) hh))
              (loop_exitsLE_nil (Γ := VAlpha) VStack.G2 eqStep _ (by simp [hg]) 0)
            refine (this.mono (by omega)).congr ?_
            funext k; cases k <;> simp [hg]
          · have hh := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.G2
                (Function.update (Function.update S .XC []) .Y2 []) 0)
              (pushList_exitsLE (Γ := VAlpha) VStack.CONF [Sym.mark] _ 0)
            rw [← eqH_terms_ne t1 t2 ht] at hh
            have := loop_exitsLE_cons (Γ := VAlpha) VStack.G2 eqStep (by simp [hg])
              (dispatch_exitsLE (Γ := VAlpha) .XC _ S (term t1) [] (by simp [hx, bsyms])
                (dispatch_exitsLE (Γ := VAlpha) .Y2 (eqH (term t1)) (Function.update S .XC [])
                  (term t2) [] (by simp [hy, bsyms]) hh))
              (loop_exitsLE_nil (Γ := VAlpha) VStack.G2 eqStep _ (by simp [hg]) 0)
            refine (this.mono (by omega)).congr ?_
            funext k; cases k <;> simp [ht, hg]
      | cons b r2 =>
          have hh := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.G2
              (Function.update (Function.update S .XC []) .Y2 (bsyms r2 ++ [term t2])) 0)
            (drain_exits (Γ := VAlpha) VStack.Y2 _).le
          rw [← eqH_term_bit t1 b] at hh
          have := loop_exitsLE_cons (Γ := VAlpha) VStack.G2 eqStep (by simp [hg])
            (dispatch_exitsLE (Γ := VAlpha) .XC _ S (term t1) [] (by simp [hx, bsyms])
              (dispatch_exitsLE (Γ := VAlpha) .Y2 (eqH (term t1)) (Function.update S .XC [])
                (b2s b) (bsyms r2 ++ [term t2]) (by simp [hy, bsyms]) hh))
            (loop_exitsLE_nil (Γ := VAlpha) VStack.G2 eqStep _ (by simp [hg]) 0)
          refine (this.mono (by simp [bsyms]; omega)).congr ?_
          funext k; cases k <;> simp [hg]
  | cons a r1 ih =>
      intro u2 t1 t2 S hx hy hg
      cases u2 with
      | nil =>
          have hh := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.G2
              (Function.update (Function.update S .XC (bsyms r1 ++ [term t1])) .Y2 []) 0)
            (drain_exits (Γ := VAlpha) VStack.XC _).le
          rw [← eqH_bit_term a t2] at hh
          have := loop_exitsLE_cons (Γ := VAlpha) VStack.G2 eqStep (by simp [hg])
            (dispatch_exitsLE (Γ := VAlpha) .XC _ S (b2s a) (bsyms r1 ++ [term t1])
              (by simp [hx, bsyms])
              (dispatch_exitsLE (Γ := VAlpha) .Y2 (eqH (b2s a))
                (Function.update S .XC (bsyms r1 ++ [term t1])) (term t2) []
                (by simp [hy, bsyms]) hh))
            (loop_exitsLE_nil (Γ := VAlpha) VStack.G2 eqStep _ (by simp [hg]) 0)
          refine (this.mono (by simp [bsyms]; omega)).congr ?_
          funext k; cases k <;> simp [hg]
      | cons b r2 =>
          by_cases hab : a = b
          · subst hab
            have hh := skip_exitsLE (Γ := VAlpha)
              (Function.update (Function.update S .XC (bsyms r1 ++ [term t1])) .Y2
                (bsyms r2 ++ [term t2])) 0
            rw [← eqH_same a] at hh
            have h2 := ih r2 t1 t2 (Function.update (Function.update S .XC (bsyms r1 ++ [term t1]))
              .Y2 (bsyms r2 ++ [term t2])) (by simp) (by simp) (by simp [hg])
            have := loop_exitsLE_cons (Γ := VAlpha) VStack.G2 eqStep (by simp [hg])
              (dispatch_exitsLE (Γ := VAlpha) .XC _ S (b2s a) (bsyms r1 ++ [term t1])
                (by simp [hx, bsyms])
                (dispatch_exitsLE (Γ := VAlpha) .Y2 (eqH (b2s a))
                  (Function.update S .XC (bsyms r1 ++ [term t1])) (b2s a) (bsyms r2 ++ [term t2])
                  (by simp [hy, bsyms]) hh)) h2
            refine (this.mono (by simp; omega)).congr ?_
            funext k; cases k <;> simp []
          · have hh := seq_exitsLE _ _ (popOne_exitsLE (Γ := VAlpha) VStack.G2
                (Function.update (Function.update S .XC (bsyms r1 ++ [term t1])) .Y2
                  (bsyms r2 ++ [term t2])) 0)
              (seq_exitsLE _ _ (drain_exits (Γ := VAlpha) VStack.XC _).le
                (drain_exits (Γ := VAlpha) VStack.Y2 _).le)
            rw [← eqH_diff a b hab] at hh
            have := loop_exitsLE_cons (Γ := VAlpha) VStack.G2 eqStep (by simp [hg])
              (dispatch_exitsLE (Γ := VAlpha) .XC _ S (b2s a) (bsyms r1 ++ [term t1])
                (by simp [hx, bsyms])
                (dispatch_exitsLE (Γ := VAlpha) .Y2 (eqH (b2s a))
                  (Function.update S .XC (bsyms r1 ++ [term t1])) (b2s b) (bsyms r2 ++ [term t2])
                  (by simp [hy, bsyms]) hh))
              (loop_exitsLE_nil (Γ := VAlpha) VStack.G2 eqStep _ (by simp [hg]) 0)
            refine (this.mono (by simp [bsyms]; omega)).congr ?_
            funext k; cases k <;> simp [hab, hg]

theorem eqCheck_exits (lx ly : Literal ℕ) (S : VS) (hx : S .XC = entryL lx) (hy : S .Y2 = entryL ly)
    (hg : S .G2 = []) :
    eqCheck.ExitsLE S (4 * ((entryL lx).length + (entryL ly).length) + 11)
      (Function.update (Function.update (Function.update S .XC []) .Y2 []) .CONF
        ((if conflict lx ly then [.mark] else []) ++ S .CONF)) := by
  have hc : (Computability.encodeNat lx.var = Computability.encodeNat ly.var ∧ isNeg lx ≠ isNeg ly) ↔
      conflict lx ly = true := by
    constructor
    · rintro ⟨h1, h2⟩
      have : lx.var = ly.var := by
        have := congrArg Computability.decodeNat h1
        simpa [Computability.decode_encodeNat] using this
      simp [conflict, this, h2]
    · intro h
      simp only [conflict, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      exact ⟨by rw [h.1], h.2⟩
  have := seq_exitsLE _ _ (pushList_exitsLE (Γ := VAlpha) VStack.G2 [Sym.mark] S 0)
    (eqLoop_exits (Computability.encodeNat lx.var) (Computability.encodeNat ly.var) (isNeg lx)
      (isNeg ly) _ (by simp [hx, entryL]) (by simp [hy, entryL]) (by simp [hg]))
  refine (this.mono (by simp [entryL, bsyms]; omega)).congr ?_
  funext k; cases k <;> simp [hg]
  by_cases h : conflict lx ly = true
  · simp [h, hc.mpr h]
  · have : ¬ (Computability.encodeNat lx.var = Computability.encodeNat ly.var ∧
        isNeg lx ≠ isNeg ly) := fun h' => h (hc.mp h')
    simp only [Bool.not_eq_true] at h
    simp [h, this]

/-! ### Comparing one entry against all -/

/-- Compare the current outer entry with the next entry of `SC`. -/
def innerChk : VR :=
  seq readEntry_S <| seq (moveAll .Y .Y2 id .mark) <|
  seq (copyAll .X2 .XC .scr id id id .mark .mark .mark) eqCheck

/-- Empty work stacks of the check phase. -/
structure CheckClean (S : VS) : Prop where
  G : S .G = []
  X : S .X = []
  X2 : S .X2 = []
  SC : S .SC = []
  Y : S .Y = []
  Y2 : S .Y2 = []
  XC : S .XC = []
  G2 : S .G2 = []
  scr : S .scr = []

theorem entryL_length_pos (l : Literal ℕ) : 1 ≤ (entryL l).length := by simp [entryL]

theorem innerLoop_exits (lx : Literal ℕ) (Λ : ℕ) (hlx : (entryL lx).length ≤ Λ) (Ys : List (Literal ℕ))
    (hYs : ∀ y ∈ Ys, (entryL y).length ≤ Λ) : ∀ (S : VS) (k : ℕ),
    S .SC = Ys.flatMap entryL → S .X2 = entryL lx → S .CONF = marks k → S .G = [] → S .Y = [] →
    S .Y2 = [] → S .XC = [] → S .G2 = [] → S .scr = [] →
    (loop .SC innerChk).ExitsLE S (Ys.length * (17 * Λ + 30) + 1)
      (Function.update (Function.update S .SC []) .CONF
        (marks (k + Ys.countP (conflict lx)))) := by
  induction Ys with
  | nil =>
      intro S k hsc hx2 hc hg hy hy2 hxc hg2 hscr
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.SC innerChk S (by simpa using hsc) 0).mono
        (by simp)).congr ?_
      funext k; cases k <;> simp [hsc, hc]
  | cons y Ys ih =>
      intro S k hsc hx2 hc hg hy hy2 hxc hg2 hscr
      have hyl := hYs y (List.mem_cons_self ..)
      have hsc' : S .SC = bsyms (Computability.encodeNat y.var) ++ term (isNeg y) ::
          Ys.flatMap entryL := by
        rw [hsc, List.flatMap_cons, entryL]; simp
      have h1 := seq_exitsLE _ _ (readEntry_S_exits _ _ S _ hsc' hg)
        (seq_exitsLE _ _ (moveAll_exits (Γ := VAlpha) VStack.Y VStack.Y2 (by decide) id Sym.mark _).le
          (seq_exitsLE _ _ (copyAll_exits (Γ := VAlpha) VStack.X2 VStack.XC VStack.scr id id id
              Sym.mark Sym.mark Sym.mark (by decide) (by decide) (by decide) (fun _ => rfl) _
              (by simp [hscr])).le
            (eqCheck_exits lx y _ (by simp [hx2, hxc]) (by simp [hy, hy2, entryL]) (by simp [hg2]))))
      have h1' := h1.congr (T := Function.update (Function.update S .SC (Ys.flatMap entryL)) .CONF
          ((if conflict lx y then [.mark] else []) ++ S .CONF))
        (by funext k; cases k <;> simp [hg, hy, hy2, hxc, hx2, hscr])
      have h2 := ih (fun y' hy' => hYs y' (List.mem_cons_of_mem _ hy'))
        (Function.update (Function.update S .SC (Ys.flatMap entryL)) .CONF
          ((if conflict lx y then [.mark] else []) ++ S .CONF))
        (k + if conflict lx y then 1 else 0) (by simp) (by simp [hx2]) (by
          simp [hc]; split_ifs <;> simp [marks_succ]) (by simp [hg]) (by simp [hy]) (by simp [hy2])
        (by simp [hxc]) (by simp [hg2]) (by simp [hscr])
      refine ((loop_exitsLE_cons _ _ (by simp [hsc', bsyms]) h1' h2).mono ?_).congr ?_
      · simp only [entryL, bsyms, List.length_append, List.length_map, List.length_singleton]
          at hyl hlx ⊢
        simp [hy, hy2, hx2]
        have hd : (entryL lx).length = (Computability.encodeNat lx.var).length + 1 := by
          simp [entryL, bsyms]
        have hf : (Ys.length + 1) * (17 * Λ + 30) = Ys.length * (17 * Λ + 30) + (17 * Λ + 30) :=
          Nat.succ_mul _ _
        omega
      · funext k; cases k <;> simp [hg, hy, hy2, hxc, hx2, List.countP_cons]
        congr 1
        split_ifs <;> omega

/-! ### Comparing every entry against all -/

/-- Take the next outer entry and compare it with all entries. -/
def outerChk : VR :=
  seq readEntry_L <| seq (moveAll .X .X2 id .mark) <|
  seq (copyAll .LK .SC .scr id id id .mark .mark .mark) <| seq (loop .SC innerChk) (drain .X2)

theorem outerLoop_exits (Ls : List (Literal ℕ)) (Λ : ℕ) (hLs : ∀ y ∈ Ls, (entryL y).length ≤ Λ)
    (hLK : (Ls.flatMap entryL).length ≤ Λ) (Xs : List (Literal ℕ))
    (hXs : ∀ x ∈ Xs, (entryL x).length ≤ Λ) : ∀ (S : VS) (k : ℕ),
    S .L = Xs.flatMap entryL → S .LK = Ls.flatMap entryL → S .CONF = marks k → CheckClean S →
    (loop .L outerChk).ExitsLE S (Xs.length * (Ls.length * (17 * Λ + 30) + 12 * Λ + 20) + 1)
      (Function.update (Function.update S .L []) .CONF
        (marks (k + (Xs.map fun x => Ls.countP (conflict x)).sum))) := by
  induction Xs with
  | nil =>
      intro S k hL hLK' hc hS
      refine ((loop_exitsLE_nil (Γ := VAlpha) VStack.L outerChk S (by simpa using hL) 0).mono
        (by simp)).congr ?_
      funext k; cases k <;> simp [hL, hc]
  | cons x Xs ih =>
      intro S k hL hLK' hc hS
      have hxl := hXs x (List.mem_cons_self ..)
      have hL' : S .L = bsyms (Computability.encodeNat x.var) ++ term (isNeg x) ::
          Xs.flatMap entryL := by
        rw [hL, List.flatMap_cons, entryL]; simp
      have h1 := seq_exitsLE _ _ (readEntry_L_exits _ _ S _ hL' hS.G)
        (seq_exitsLE _ _ (moveAll_exits (Γ := VAlpha) VStack.X VStack.X2 (by decide) id Sym.mark _).le
          (seq_exitsLE _ _ (copyAll_exits (Γ := VAlpha) VStack.LK VStack.SC VStack.scr id id id
              Sym.mark Sym.mark Sym.mark (by decide) (by decide) (by decide) (fun _ => rfl) _
              (by simp [hS.scr])).le
            (seq_exitsLE _ _ (innerLoop_exits x Λ hxl Ls hLs _ k (by simp [hLK', hS.SC])
                (by simp [hS.X, hS.X2, entryL]) (by simp [hc]) (by simp [hS.G]) (by simp [hS.Y])
                (by simp [hS.Y2]) (by simp [hS.XC]) (by simp [hS.G2]) (by simp [hS.scr]))
              (drain_exits (Γ := VAlpha) VStack.X2 _).le)))
      have h1' := h1.congr (T := Function.update (Function.update S .L (Xs.flatMap entryL)) .CONF
          (marks (k + Ls.countP (conflict x))))
        (by funext k; cases k <;> simp [hS.G, hS.X, hS.X2, hS.SC, hS.Y, hS.Y2, hS.XC, hS.G2,
          hS.scr])
      have h2 := ih (fun x' hx' => hXs x' (List.mem_cons_of_mem _ hx'))
        (Function.update (Function.update S .L (Xs.flatMap entryL)) .CONF
          (marks (k + Ls.countP (conflict x)))) (k + Ls.countP (conflict x)) (by simp)
        (by simp [hLK']) (by simp)
        ⟨by simp [hS.G], by simp [hS.X], by simp [hS.X2], by simp [hS.SC], by simp [hS.Y],
          by simp [hS.Y2], by simp [hS.XC], by simp [hS.G2], by simp [hS.scr]⟩
      refine ((loop_exitsLE_cons _ _ (by simp [hL', bsyms]) h1' h2).mono ?_).congr ?_
      · simp only [entryL, bsyms, List.length_append, List.length_map, List.length_singleton]
          at hxl ⊢
        simp [hS.X, hS.X2, hS.SC, hLK']
        have hf2 : (List.map (fun a => (entryL a).length) Ls).sum = (Ls.flatMap entryL).length := by
          simp [List.length_flatMap]
        have hf : (Xs.length + 1) * (Ls.length * (17 * Λ + 30) + 12 * Λ + 20) =
            Xs.length * (Ls.length * (17 * Λ + 30) + 12 * Λ + 20) +
              (Ls.length * (17 * Λ + 30) + 12 * Λ + 20) := Nat.succ_mul _ _
        omega
      · funext k; cases k <;> simp
        congr 1; omega

theorem entryL_length_le_flatMap (Ls : List (Literal ℕ)) :
    ∀ x ∈ Ls, (entryL x).length ≤ (Ls.flatMap entryL).length := by
  induction Ls with
  | nil => simp
  | cons y Ls ih =>
      intro x hx
      rw [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp hx with rfl | h
      · omega
      · have := ih x h; omega

theorem length_le_flatMap_entryL (Ls : List (Literal ℕ)) : Ls.length ≤ (Ls.flatMap entryL).length := by
  induction Ls with
  | nil => simp
  | cons y Ls ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have := entryL_length_pos y; omega

/-- The consistency check over the entries on `L`. -/
def checkPhase : VR :=
  seq (copyAll .L .LK .scr id id id .mark .mark .mark) <| seq (loop .L outerChk) (drain .LK)

/-- Step bound of the check phase for `Λ` entry symbols. -/
def checkCost (Λ : ℕ) : ℕ := 100 * (Λ + 1) ^ 3

theorem checkPhase_exits (Ls : List (Literal ℕ)) (S : VS) (hL : S .L = Ls.flatMap entryL)
    (hLK : S .LK = []) (hc : S .CONF = []) (hS : CheckClean S) :
    checkPhase.ExitsLE S (checkCost (Ls.flatMap entryL).length)
      (Function.update (Function.update S .L []) .CONF
        (marks ((Ls.map fun x => Ls.countP (conflict x)).sum))) := by
  set Λ := (Ls.flatMap entryL).length with hΛ
  have hmem := entryL_length_le_flatMap Ls
  have hlen := length_le_flatMap_entryL Ls
  have := seq_exitsLE _ _ (copyAll_exits (Γ := VAlpha) VStack.L VStack.LK VStack.scr id id id
      Sym.mark Sym.mark Sym.mark (by decide) (by decide) (by decide) (fun _ => rfl) S
      (by simp [hS.scr])).le
    (seq_exitsLE _ _ (outerLoop_exits Ls Λ hmem le_rfl Ls hmem _ 0 (by simp [hL])
        (by simp [hL, hLK]) (by simp [hc])
        ⟨by simp [hS.G], by simp [hS.X], by simp [hS.X2], by simp [hS.SC], by simp [hS.Y],
          by simp [hS.Y2], by simp [hS.XC], by simp [hS.G2], by simp [hS.scr]⟩)
      (drain_exits (Γ := VAlpha) VStack.LK _).le)
  refine (this.mono ?_).congr ?_
  · simp [hL, hLK, checkCost]
    rw [← hΛ] at *
    have h1 : Ls.length * (Ls.length * (17 * Λ + 30) + 12 * Λ + 20) ≤
        Λ * (Λ * (17 * Λ + 30) + 12 * Λ + 20) :=
      Nat.mul_le_mul hlen (by have := Nat.mul_le_mul_right (17 * Λ + 30) hlen; omega)
    have hs : (List.map (fun a => (entryL a).length) Ls).sum = Λ := by
      show _ = (Ls.flatMap entryL).length
      simp [List.length_flatMap]
    rw [hs]
    have key : 6 * Λ + 4 + Λ * (Λ * (17 * Λ + 30) + 12 * Λ + 20) ≤ 100 * (Λ + 1) ^ 3 := by
      ring_nf
      nlinarith [Nat.zero_le (Λ ^ 2), Nat.zero_le (Λ ^ 3)]
    omega
  · funext k; cases k <;> simp [hLK]

theorem countP_sum_eq_zero (Ls : List (Literal ℕ)) :
    (Ls.map fun x => Ls.countP (conflict x)).sum = 0 ↔ consistent Ls = true := by
  rw [consistent_iff]
  simp [List.sum_eq_zero_iff, List.countP_eq_zero]

end LeanNPHardness.ExactThreeVerify
