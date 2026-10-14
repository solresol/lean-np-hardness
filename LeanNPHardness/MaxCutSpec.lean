import LeanNPHardness.CNFChain
import LeanNPHardness.UnaryCNF
import LeanNPHardness.CNFEncoding

/-!
# Max-Cut: the language, encodings, and a gadget from exact 3-SAT

A Max-Cut instance is a list of edges between natural-number vertices
(repeated edges and self-loops are retained) and a threshold `K`; it is a
yes-instance when some two-colouring cuts at least `K` edges
(`MaxCutLang`). Instances are encoded as CNF formulas (`graphFormula`: one
two-literal clause per edge, then the clause `[K]`), under the unary-index
and the binary CNF encodings.

`gadget F` maps a formula to a graph: the variable `v` becomes the vertex
`2v`, vertex `1` is a reference vertex, and each clause gets a block of
fresh odd vertices: one occurrence vertex per literal linked to its
variable vertex (directly for a negative literal, through a fresh vertex
for a positive one), two triangles joined by an edge forcing a
not-all-equal split, and a pendant edge. The threshold is the edge count
minus two per clause. For formulas whose clauses have exactly three
literals, `sat_iff_maxCut_gadget` proves satisfiability is equivalent to a
cut reaching the threshold.
-/

namespace LeanNPHardness.MaxCut

open CNF

/-- An edge between two vertices. -/
abbrev Edge := ℕ × ℕ

/-- The number of edges cut by a two-colouring. -/
def cut (s : ℕ → Bool) (G : List Edge) : ℕ := (G.filter fun e => s e.1 != s e.2).length

/-- Max-Cut as a decision problem: some colouring cuts at least `K` edges. -/
def MaxCutLang : Language (List Edge × ℕ) := fun p => ∃ s : ℕ → Bool, p.2 ≤ cut s p.1

theorem cut_append (s : ℕ → Bool) (A B : List Edge) : cut s (A ++ B) = cut s A + cut s B := by
  simp [cut, List.filter_append]

theorem cut_cons (s : ℕ → Bool) (e : Edge) (G : List Edge) :
    cut s (e :: G) = (if s e.1 != s e.2 then 1 else 0) + cut s G := by
  simp only [cut, List.filter_cons]
  split <;> simp [Nat.add_comm]

theorem cut_le (s : ℕ → Bool) (G : List Edge) : cut s G ≤ G.length := List.length_filter_le _ _

theorem cut_nil (s : ℕ → Bool) : cut s [] = 0 := rfl

/-! ### Encodings -/

/-- A Max-Cut instance as a formula: one clause per edge, then the threshold. -/
def graphFormula (G : List Edge) (K : ℕ) : Formula ℕ :=
  G.map (fun e => [Literal.positive e.1, .positive e.2]) ++ [[.positive K]]

/-- Recover an instance from its formula. -/
def decodeGraph : Formula ℕ → Option (List Edge × ℕ)
  | [] => none
  | [c] => match c with
    | [.positive K] => some ([], K)
    | _ => none
  | c :: d :: F => match c with
    | [.positive u, .positive v] => (decodeGraph (d :: F)).map fun p => ((u, v) :: p.1, p.2)
    | _ => none

theorem decodeGraph_graphFormula (G : List Edge) (K : ℕ) :
    decodeGraph (graphFormula G K) = some (G, K) := by
  induction G with
  | nil => rfl
  | cons e G ih =>
      cases G with
      | nil => simp [graphFormula, decodeGraph]
      | cons e' G => simp only [graphFormula, List.map_cons, List.cons_append] at ih ⊢
                     rw [decodeGraph, ih]; rfl

/-- Max-Cut instances under the unary-index CNF encoding. -/
def unaryEncoding : Computability.FinEncoding (List Edge × ℕ) where
  Γ := CNF.Unary.Sym
  encode p := CNF.Unary.encode (graphFormula p.1 p.2)
  decode syms := (CNF.Unary.decode syms).bind decodeGraph
  decode_encode p := by simp [CNF.Unary.decode_encode, decodeGraph_graphFormula]
  ΓFin := inferInstance

/-- Max-Cut instances under the binary CNF encoding. -/
def binaryEncoding : Computability.FinEncoding (List Edge × ℕ) where
  Γ := Bool
  encode p := Formula.encode (graphFormula p.1 p.2)
  decode bits := (Formula.decode bits).bind decodeGraph
  decode_encode p := by simp [decodeGraph_graphFormula]
  ΓFin := inferInstance

/-- Max-Cut with the unary-index encoding. -/
def encodedUnaryMaxCut : EncodedLanguage (List Edge × ℕ) where
  encoding := unaryEncoding
  accepts := MaxCutLang

/-- Max-Cut with the binary encoding. -/
def encodedMaxCut : EncodedLanguage (List Edge × ℕ) where
  encoding := binaryEncoding
  accepts := MaxCutLang

/-! ### The gadget -/

/-- The edges of literal `l` at position `i` of the block starting at `b`. -/
def litEdges (b i : ℕ) : Literal ℕ → List Edge
  | .positive v => [(b + 4 * i, b + 4 * i + 2), (b + 4 * i + 2, 2 * v)]
  | .negative v => [(b + 4 * i, 2 * v)]

/-- The literal edges of a clause from position `i`. -/
def litsEdges (b : ℕ) : ℕ → Clause ℕ → List Edge
  | _, [] => []
  | i, l :: c => litEdges b i l ++ litsEdges b (i + 1) c

/-- Two triangles `(o₀, o₁, y)`, `(ȳ, o₂, Z)` and the edge `y ȳ`. -/
def fixedEdges (b : ℕ) : List Edge :=
  [(b, b + 4), (b + 4, b + 12), (b, b + 12), (b + 14, b + 8), (b + 8, 1), (b + 14, 1),
    (b + 12, b + 14)]

/-- The gadget's edges for clauses from block base `b`. -/
def gadgetEdges : ℕ → Formula ℕ → List Edge
  | b, [] => [(b + 16, 0)]
  | b, c :: F => ((b + 16, 0) :: litsEdges b 0 c ++ fixedEdges b) ++ gadgetEdges (b + 18) F

/-- The gadget instance of a formula. -/
def gadget (F : Formula ℕ) : List Edge × ℕ :=
  (gadgetEdges 3 F, (gadgetEdges 3 F).length - 2 * F.length)

/-! ### Every cut loses two edges per block -/

/-- Edges cut within one triangle. -/
theorem triangle_cut (x y z : Bool) :
    (if x != y then 1 else 0) + (if y != z then 1 else 0) + (if x != z then 1 else 0) ≤ 2 := by
  cases x <;> cases y <;> cases z <;> decide

theorem fixed_cut_le (s : ℕ → Bool) (b : ℕ) : cut s (fixedEdges b) + 2 ≤ (fixedEdges b).length := by
  simp only [fixedEdges, cut_cons, cut_nil, List.length_cons, List.length_nil]
  have h1 := triangle_cut (s b) (s (b + 4)) (s (b + 12))
  have h2 := triangle_cut (s (b + 14)) (s (b + 8)) (s 1)
  have h3 : (if s (b + 12) != s (b + 14) then 1 else 0) ≤ 1 := by split <;> omega
  omega

theorem block_cut_le (s : ℕ → Bool) (b : ℕ) (c : Clause ℕ) :
    cut s ((b + 16, 0) :: litsEdges b 0 c ++ fixedEdges b) + 2 ≤
      ((b + 16, 0) :: litsEdges b 0 c ++ fixedEdges b).length := by
  rw [List.cons_append, cut_cons, cut_append, List.length_cons, List.length_append]
  have h1 := cut_le s (litsEdges b 0 c)
  have h2 := fixed_cut_le s b
  have h3 : (if s (b + 16, 0).1 != s (b + 16, 0).2 then 1 else 0) ≤ 1 := by split <;> omega
  omega

theorem gadget_cut_le (s : ℕ → Bool) (F : Formula ℕ) : ∀ b,
    cut s (gadgetEdges b F) + 2 * F.length ≤ (gadgetEdges b F).length := by
  induction F with
  | nil => intro b; simpa [gadgetEdges] using cut_le s [(b + 16, 0)]
  | cons c F ih =>
      intro b
      have h1 := block_cut_le s b c
      have h2 := ih (b + 18)
      simp only [gadgetEdges, cut_append, List.length_append, List.length_cons] at h1 h2 ⊢
      omega

/-! ### Maximal cuts satisfy the formula -/

/-- The assignment read off a colouring: `v` is true when `2v` differs from `1`. -/
def assignOf (s : ℕ → Bool) : Assignment ℕ := fun v => s (2 * v) != s 1

/-- The colour value of a literal relative to the reference vertex. -/
theorem lit_value (s : ℕ → Bool) (b i : ℕ) (l : Literal ℕ)
    (h : cut s (litEdges b i l) = (litEdges b i l).length) :
    l.eval (assignOf s) = (s (b + 4 * i) != s 1) := by
  cases l with
  | positive v =>
      simp only [litEdges, cut_cons, cut_nil, List.length_cons, List.length_nil] at h
      have h1 : s (b + 4 * i) != s (b + 4 * i + 2) := by
        by_contra hc; simp only [Bool.not_eq_true] at hc; simp [hc] at h; split at h <;> omega
      have h2 : s (b + 4 * i + 2) != s (2 * v) := by
        by_contra hc; simp only [Bool.not_eq_true] at hc; simp [hc] at h; split at h <;> omega
      simp only [Literal.eval, assignOf]
      revert h1 h2
      cases s (b + 4 * i) <;> cases s (b + 4 * i + 2) <;> cases s (2 * v) <;> cases s 1 <;> decide
  | negative v =>
      simp only [litEdges, cut_cons, cut_nil, List.length_cons, List.length_nil] at h
      have h1 : s (b + 4 * i) != s (2 * v) := by
        by_contra hc; simp only [Bool.not_eq_true] at hc; simp [hc] at h
      simp only [Literal.eval, assignOf]
      revert h1
      cases s (b + 4 * i) <;> cases s (2 * v) <;> cases s 1 <;> decide

theorem tight_block (s : ℕ → Bool) (b : ℕ) (c : Clause ℕ) (hc : c.length = 3)
    (h : cut s ((b + 16, 0) :: litsEdges b 0 c ++ fixedEdges b) + 2 =
      ((b + 16, 0) :: litsEdges b 0 c ++ fixedEdges b).length) :
    c.eval (assignOf s) = true := by
  match c, hc with
  | [l0, l1, l2], _ =>
    simp only [litsEdges, List.append_nil, List.cons_append, cut_cons, cut_append,
      List.length_cons, List.length_append, Nat.zero_add, Nat.reduceAdd] at h
    have c0 := cut_le s (litEdges b 0 l0)
    have c1 := cut_le s (litEdges b 1 l1)
    have c2 := cut_le s (litEdges b 2 l2)
    have hf := fixed_cut_le s b
    have hp : (if s (b + 16) != s 0 then 1 else 0) ≤ 1 := by split <;> omega
    have e0 : cut s (litEdges b 0 l0) = (litEdges b 0 l0).length := by omega
    have e1 : cut s (litEdges b 1 l1) = (litEdges b 1 l1).length := by omega
    have e2 : cut s (litEdges b 2 l2) = (litEdges b 2 l2).length := by omega
    have ef : cut s (fixedEdges b) + 2 = (fixedEdges b).length := by omega
    have v0 := lit_value s b 0 l0 e0
    have v1 := lit_value s b 1 l1 e1
    have v2 := lit_value s b 2 l2 e2
    simp only [fixedEdges, cut_cons, cut_nil, List.length_cons, List.length_nil] at ef
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at v0 v1 v2
    rw [show b + 4 * 2 = b + 8 by ring] at v2
    simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false, v0, v1, v2]
    revert ef
    cases s b <;> cases s (b + 4) <;> cases s (b + 8) <;> cases s (b + 12) <;>
      cases s (b + 14) <;> cases s 1 <;> decide

theorem tight_gadget (s : ℕ → Bool) (F : Formula ℕ) (hw : F.ExactWidth 3) : ∀ b,
    (gadgetEdges b F).length ≤ cut s (gadgetEdges b F) + 2 * F.length →
    F.eval (assignOf s) = true := by
  induction F with
  | nil => intro _ _; rfl
  | cons c F ih =>
      intro b h
      have h1 := block_cut_le s b c
      have h2 := gadget_cut_le s F (b + 18)
      simp only [gadgetEdges, cut_append, List.length_append, List.length_cons] at h h1 h2
      simp only [Formula.eval_cons, Bool.and_eq_true]
      refine ⟨tight_block s b c (hw c (List.mem_cons_self ..)) (by
          simp only [List.length_append, List.length_cons, cut_append] at h1 ⊢; omega),
        ih (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) (b + 18) (by omega)⟩

/-! ### Satisfying assignments give maximal cuts -/

/-- The colouring of a satisfying assignment. -/
def colourOf (a : Assignment ℕ) (F : Formula ℕ) (u : ℕ) : Bool :=
  if u % 2 = 0 then a (u / 2)
  else if u = 1 then false
  else
    let j := (u - 3) / 18
    let r := (u - 3) % 18
    let c := F.getD j []
    let o (i : ℕ) : Bool := (c.getD i (.positive 0)).eval a
    let y : Bool := !(o 0) && !(o 1)
    if r = 12 then y
    else if r = 14 then !y
    else if r = 16 then !(a 0)
    else if r % 4 = 0 then o (r / 4)
    else !(o (r / 4))

theorem colourOf_block (a : Assignment ℕ) (F : Formula ℕ) (j r : ℕ) (hr : r < 18) (he : r % 2 = 0) :
    colourOf a F (3 + 18 * j + r) =
      (let c := F.getD j []
       let o (i : ℕ) : Bool := (c.getD i (.positive 0)).eval a
       let y : Bool := !(o 0) && !(o 1)
       if r = 12 then y
       else if r = 14 then !y
       else if r = 16 then !(a 0)
       else if r % 4 = 0 then o (r / 4)
       else !(o (r / 4))) := by
  have h1 : (3 + 18 * j + r) % 2 = 1 := by omega
  have h2 : 3 + 18 * j + r ≠ 1 := by omega
  have h3 : (3 + 18 * j + r - 3) / 18 = j := by omega
  have h4 : (3 + 18 * j + r - 3) % 18 = r := by omega
  simp only [colourOf, h1, h2, h3, h4, one_ne_zero, if_false]

theorem triangle_nae (x y z : Bool) (h : ¬ (x = y ∧ y = z)) :
    (if x != y then 1 else 0) + (if y != z then 1 else 0) + (if x != z then 1 else 0) = 2 := by
  cases x <;> cases y <;> cases z <;> simp_all

theorem full_lit (a : Assignment ℕ) (F : Formula ℕ) (j i : ℕ) (hi : i < 3) (l : Literal ℕ)
    (hl : (F.getD j []).getD i (.positive 0) = l) :
    cut (colourOf a F) (litEdges (3 + 18 * j) i l) = (litEdges (3 + 18 * j) i l).length := by
  have ho := colourOf_block a F j (4 * i) (by omega) (by omega)
  cases l with
  | positive v =>
      have ht := colourOf_block a F j (4 * i + 2) (by omega) (by omega)
      have hx : colourOf a F (2 * v) = a v := by simp [colourOf]
      simp only [litEdges, cut_cons, cut_nil, List.length_cons, List.length_nil]
      rw [show 3 + 18 * j + 4 * i + 2 = 3 + 18 * j + (4 * i + 2) by ring, ho, ht, hx]
      have n1 : 4 * i ≠ 12 := by omega
      have n2 : 4 * i ≠ 14 := by omega
      have n3 : 4 * i ≠ 16 := by omega
      have m1 : 4 * i + 2 ≠ 12 := by omega
      have m2 : 4 * i + 2 ≠ 14 := by omega
      have m3 : 4 * i + 2 ≠ 16 := by omega
      simp only [n1, n2, n3, m1, m2, m3, if_false, hl,
        show 4 * i % 4 = 0 by omega, show (4 * i + 2) % 4 ≠ 0 by omega,
        show 4 * i / 4 = i by omega, show (4 * i + 2) / 4 = i by omega, if_true, Literal.eval]
      cases a v <;> decide
  | negative v =>
      have hx : colourOf a F (2 * v) = a v := by simp [colourOf]
      simp only [litEdges, cut_cons, cut_nil, List.length_cons, List.length_nil]
      rw [ho, hx]
      have n1 : 4 * i ≠ 12 := by omega
      have n2 : 4 * i ≠ 14 := by omega
      have n3 : 4 * i ≠ 16 := by omega
      simp only [n1, n2, n3, if_false, hl, show 4 * i % 4 = 0 by omega,
        show 4 * i / 4 = i by omega, if_true, Literal.eval]
      cases a v <;> decide

theorem full_block (a : Assignment ℕ) (F : Formula ℕ) (j : ℕ) (c : Clause ℕ) (hc : c.length = 3)
    (hcj : F.getD j [] = c) (hsat : c.eval a = true) :
    cut (colourOf a F) ((3 + 18 * j + 16, 0) :: litsEdges (3 + 18 * j) 0 c ++ fixedEdges (3 + 18 * j))
      + 2 = ((3 + 18 * j + 16, 0) :: litsEdges (3 + 18 * j) 0 c ++ fixedEdges (3 + 18 * j)).length := by
  match c, hc with
  | [l0, l1, l2], _ =>
    have e0 := full_lit a F j 0 (by omega) l0 (by rw [hcj]; rfl)
    have e1 := full_lit a F j 1 (by omega) l1 (by rw [hcj]; rfl)
    have e2 := full_lit a F j 2 (by omega) l2 (by rw [hcj]; rfl)
    simp only [litsEdges, List.append_nil, List.cons_append, cut_cons, cut_append,
      List.length_cons, List.length_append, Nat.zero_add, Nat.reduceAdd, e0, e1, e2]
    have hp : colourOf a F (3 + 18 * j + 16) = !(a 0) := by
      rw [colourOf_block a F j 16 (by omega) (by omega)]; simp
    have hz : colourOf a F 0 = a 0 := by simp [colourOf]
    have hZ : colourOf a F 1 = false := by simp [colourOf]
    have k0 := colourOf_block a F j 0 (by omega) (by omega)
    have k4 := colourOf_block a F j 4 (by omega) (by omega)
    have k8 := colourOf_block a F j 8 (by omega) (by omega)
    have k12 := colourOf_block a F j 12 (by omega) (by omega)
    have k14 := colourOf_block a F j 14 (by omega) (by omega)
    simp only [hcj, Nat.add_zero] at k0 k4 k8 k12 k14
    simp only [fixedEdges, cut_cons, cut_nil, List.length_cons, List.length_nil, hp, hz, hZ,
      k0, k4, k8, k12, k14]
    simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false] at hsat
    cases h0 : Literal.eval a l0 <;> cases h1 : Literal.eval a l1 <;>
      cases h2 : Literal.eval a l2 <;> cases ha : a 0 <;> simp [h0, h1, h2] at hsat ⊢ <;> omega

theorem full_gadget (a : Assignment ℕ) (F : Formula ℕ) (hw : F.ExactWidth 3)
    (hs : F.eval a = true) : ∀ (pre : Formula ℕ) (G : Formula ℕ), F = pre ++ G →
    cut (colourOf a F) (gadgetEdges (3 + 18 * pre.length) G) + 2 * G.length =
      (gadgetEdges (3 + 18 * pre.length) G).length := by
  intro pre G hFG
  induction G generalizing pre with
  | nil =>
      simp only [gadgetEdges, cut_cons, cut_nil, List.length_cons, List.length]
      have hp : colourOf a F (3 + 18 * pre.length + 16) = !(a 0) := by
        rw [colourOf_block a F pre.length 16 (by omega) (by omega)]; simp
      have hz : colourOf a F 0 = a 0 := by simp [colourOf]
      simp only [hp, hz]; cases a 0 <;> decide
  | cons c G ih =>
      have hcj : F.getD pre.length [] = c := by rw [hFG]; simp
      have hc : c.length = 3 := hw c (by rw [hFG]; simp)
      have hsat : c.eval a = true := by
        have := hs; rw [hFG] at this
        simp only [Formula.eval, List.all_append, List.all_cons, Bool.and_eq_true] at this
        exact this.2.1
      have h1 := full_block a F pre.length c hc hcj hsat
      have h2 := ih (pre ++ [c]) (by rw [hFG]; simp)
      simp only [List.length_append, List.length_singleton] at h2
      rw [show 3 + 18 * (pre.length + 1) = 3 + 18 * pre.length + 18 by ring] at h2
      simp only [gadgetEdges, cut_append, List.length_append, List.length_cons] at h1 h2 ⊢
      omega

/-- For formulas with exactly three literals per clause, satisfiability is
equivalent to a cut reaching the gadget's threshold. -/
theorem sat_iff_maxCut_gadget (F : Formula ℕ) (hw : F.ExactWidth 3) :
    SAT F ↔ MaxCutLang (gadget F) := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (Formula.satisfiable_iff_exists_eval F).mp h
    refine ⟨colourOf a F, ?_⟩
    have := full_gadget a F hw ha [] F rfl
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at this
    simp only [gadget]
    omega
  · rintro ⟨s, hs⟩
    simp only [gadget] at hs
    have hle := gadget_cut_le s F 3
    exact (Formula.satisfiable_iff_exists_eval F).mpr ⟨assignOf s, tight_gadget s F hw 3 (by omega)⟩

end LeanNPHardness.MaxCut
