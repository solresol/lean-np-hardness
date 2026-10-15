import LeanNPHardness.MachineTableauSystem

/-!
# Initial and final constraints of the machine tableau

The initial configuration is the machine's start configuration on a fixed
input prefix followed by an unknown certificate of bounded length. Every
register of the time-zero row is fixed to the prefix-only start
configuration, except the certificate cells, which are constrained in pairs:
each is empty or a certificate symbol, and an empty cell is followed by an
empty cell. The final row is fixed to the canonical halting configuration
with a given short output. `tableau_satisfiable_iff` then specializes the
generic tableau theorem to the padded run of the machine. These are
semantic results; no runtime claim is made.
-/

namespace LeanNPHardness.MachineTableau

open Turing CNF CNF.Constraint MachineLocality MachinePaddedRun Tableau StateTransition

/-- A machine tableau instance: the shape, the fixed input prefix, the
certificate symbol map, and the required short halting output. -/
structure Instance extends Params where
  input : List (tm.Γ tm.k₀)
  input_length : input.length = inputLength
  certSym : Bool → tm.Γ tm.k₀
  certSym_injective : Function.Injective certSym
  output : List (tm.Γ tm.k₁)
  output_mem : ∀ s ∈ output, s ∈ extra
  output_short : output.length ≤ 1

namespace Instance

variable (I : Instance)

/-- The register index of register `g` at time `t`. -/
noncomputable def reg (t g : ℕ) : ℕ := t * I.count + g

theorem localSystem_regIndex (t g : ℕ) : I.toParams.localSystem.regIndex t g = I.reg t g := rfl

/-- The start configuration on the input prefix followed by a certificate. -/
noncomputable def initCfg (bits : List Bool) : I.tm.Cfg :=
  initList I.tm (I.input ++ bits.map I.certSym)

/-- Allowed initial configurations. -/
def initial (c : I.tm.Cfg) : Prop :=
  ∃ bits : List Bool, bits.length ≤ I.certBound ∧ c = I.initCfg bits

/-- The canonical halting configuration with the required output. -/
noncomputable def finalCfg : I.tm.Cfg := haltList I.tm I.output

theorem initList_stk_self (input : List (I.tm.Γ I.tm.k₀)) :
    (initList I.tm input).stk I.tm.k₀ = input := by
  simp [initList]

theorem initList_stk_of_ne (input : List (I.tm.Γ I.tm.k₀)) (k : I.tm.K) (h : k ≠ I.tm.k₀) :
    (initList I.tm input).stk k = [] := by
  simp [initList, h]

theorem haltList_stk_self (output : List (I.tm.Γ I.tm.k₁)) :
    (haltList I.tm output).stk I.tm.k₁ = output := by
  simp [haltList]

theorem haltList_stk_of_ne (output : List (I.tm.Γ I.tm.k₁)) (k : I.tm.K) (h : k ≠ I.tm.k₁) :
    (haltList I.tm output).stk k = [] := by
  simp [haltList, h]

theorem initCfg_stk_self (bits : List Bool) :
    (I.initCfg bits).stk I.tm.k₀ = I.input ++ bits.map I.certSym :=
  I.initList_stk_self _

theorem initCfg_stk_of_ne (bits : List Bool) (k : I.tm.K) (h : k ≠ I.tm.k₀) :
    (I.initCfg bits).stk k = [] :=
  I.initList_stk_of_ne _ k h

theorem initCfg_l (bits : List Bool) : (I.initCfg bits).l = some I.tm.main := rfl

theorem initCfg_var (bits : List Bool) : (I.initCfg bits).var = I.tm.initialState := rfl

theorem initial_inv (c : I.tm.Cfg) (hc : I.initial c) : I.Inv 0 c := by
  obtain ⟨bits, hbits, rfl⟩ := hc
  refine ⟨fun k => ?_, fun k s hs => ?_⟩
  · by_cases hk : k = I.tm.k₀
    · subst hk
      rw [initCfg_stk_self]
      simp only [List.length_append, List.length_map, I.input_length, Nat.zero_mul,
        Nat.add_zero]
      omega
    · rw [initCfg_stk_of_ne _ _ k hk]; simp
  · by_cases hk : k = I.tm.k₀
    · subst hk
      exact mem_symbols_of_input I.tm I.extra s
    · rw [initCfg_stk_of_ne _ _ k hk] at hs; simp at hs

theorem finalCfg_bounded : I.Bounded I.finalCfg := by
  have hB := I.B_ge_two
  refine ⟨fun k => ?_, fun k s hs => ?_⟩
  · by_cases hk : k = I.tm.k₁
    · subst hk
      rw [finalCfg, haltList_stk_self]
      have := I.output_short
      omega
    · rw [finalCfg, haltList_stk_of_ne _ _ k hk]; simp; omega
  · by_cases hk : k = I.tm.k₁
    · subst hk
      rw [finalCfg, haltList_stk_self] at hs
      exact mem_symbols_of_output I.tm I.extra s (I.output_mem s hs)
    · rw [finalCfg, haltList_stk_of_ne _ _ k hk] at hs; simp at hs

/-! ### Certificate cells -/

/-- The register of the `i`-th certificate cell. -/
noncomputable def certGroup (i : ℕ) : ℕ :=
  I.cellGroup I.tm.k₀ (I.D + I.inputLength + i)

/-- The registers of the possible certificate cells. -/
noncomputable def certGroups : List ℕ := (List.range I.certBound).map I.certGroup

theorem certCell_lt_P (i : ℕ) (hi : i ≤ I.certBound) : I.D + I.inputLength + i < I.P := by
  simp only [Params.P, Params.B]; omega

theorem certGroup_lt_count (i : ℕ) (hi : i ≤ I.certBound) : I.certGroup i < I.count :=
  I.cellGroup_lt_count _ _ (I.certCell_lt_P i hi)

theorem certGroup_injective (i i' : ℕ) (h : I.certGroup i = I.certGroup i') : i = i' := by
  simp only [certGroup, Params.cellGroup] at h
  omega

theorem mem_certGroups (g : ℕ) : g ∈ I.certGroups ↔ ∃ i < I.certBound, g = I.certGroup i := by
  simp only [certGroups, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- The code of the certificate symbol for `true`. -/
noncomputable def cT : ℕ := optionCode (symbols I.tm I.extra I.tm.k₀) (some (I.certSym true))

/-- The code of the certificate symbol for `false`. -/
noncomputable def cF : ℕ := optionCode (symbols I.tm I.extra I.tm.k₀) (some (I.certSym false))

/-- The code of a certificate bit. -/
noncomputable def certCode (b : Bool) : ℕ :=
  optionCode (symbols I.tm I.extra I.tm.k₀) (some (I.certSym b))

theorem certCode_true : I.certCode true = I.cT := rfl

theorem certCode_false : I.certCode false = I.cF := rfl

theorem certCode_ne_zero (b : Bool) : I.certCode b ≠ 0 := by simp [certCode]

theorem cT_ne_cF : I.cT ≠ I.cF := by
  intro h
  have := optionCode_injective _ _ _
    (fun x hx => by cases hx; exact mem_symbols_of_input I.tm I.extra _)
    (fun x hx => by cases hx; exact mem_symbols_of_input I.tm I.extra _) h
  have := I.certSym_injective (Option.some.inj this)
  cases this

/-- Decode a certificate cell value. -/
noncomputable def certDecode (m : ℕ) : Option Bool :=
  if m = I.cT then some true else if m = I.cF then some false else none

theorem certDecode_certCode (b : Bool) : I.certDecode (I.certCode b) = some b := by
  cases b
  · simp [certDecode, certCode_false, I.cT_ne_cF.symm]
  · simp [certDecode, certCode_true]

theorem certDecode_eq_some (m : ℕ) (b : Bool) (h : I.certDecode m = some b) : m = I.certCode b := by
  simp only [certDecode] at h
  split_ifs at h with h1 h2
  · cases h; exact h1
  · cases h; exact h2

theorem certDecode_eq_none (m : ℕ) (h : I.certDecode m = none) : m ≠ I.cT ∧ m ≠ I.cF := by
  simp only [certDecode] at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2⟩

/-- The pairwise certificate relation: the first cell is empty or holds a
certificate symbol, and an empty cell is followed by an empty cell. -/
noncomputable def certRel (vs : List ℕ) : Bool :=
  match vs with
  | [u, u'] => (u == 0 || u == I.cT || u == I.cF) && (u != 0 || u' == 0)
  | _ => false

/-- The constraint between certificate cells `i` and `i + 1`. -/
noncomputable def certChain (i : ℕ) : Formula ℕ :=
  registerCNF I.width [I.reg 0 (I.certGroup i), I.reg 0 (I.certGroup (i + 1))] I.certRel

/-- Register values of the start configuration on the prefix followed by a
certificate: non-certificate registers agree with the prefix-only start. -/
theorem value_initCfg_of_not_cert (bits : List Bool) (hbits : bits.length ≤ I.certBound)
    (g : ℕ) (hg : g < I.count) (hng : g ∉ I.certGroups) :
    I.value (I.initCfg bits) g = I.value (I.initCfg []) g := by
  rcases I.classify g hg with rfl | rfl | ⟨hg2, hgd⟩ | ⟨k, j, hj, hg'⟩
  · rfl
  · rfl
  · rw [Params.value_dummy _ _ g hg2 hgd, Params.value_dummy _ _ g hg2 hgd]
  · rw [hg', I.value_cellGroup _ k j hj, I.value_cellGroup _ k j hj]
    by_cases hDj : I.D ≤ j
    · rw [Params.cellValue_of_le _ _ _ _ hDj, Params.cellValue_of_le _ _ _ _ hDj]
      by_cases hk : k = I.tm.k₀
      · subst hk
        rw [initCfg_stk_self, initCfg_stk_self, List.map_nil, List.append_nil]
        by_cases hin : j - I.D < I.input.length
        · rw [List.getElem?_append_left hin]
        · have hin' := Nat.not_lt.mp hin
          rw [List.getElem?_append_right hin']
          by_cases hlt : j - I.D - I.input.length < I.certBound
          · exfalso
            apply hng
            rw [mem_certGroups]
            refine ⟨j - I.D - I.input.length, hlt, ?_⟩
            rw [hg', certGroup, I.input_length]
            congr 1
            rw [I.input_length] at hin'
            omega
          · have hlt' := Nat.not_lt.mp hlt
            rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none hin']
      · rw [initCfg_stk_of_ne _ _ k hk, initCfg_stk_of_ne _ _ k hk]
    · rw [Params.cellValue_of_lt _ _ _ _ (Nat.not_le.mp hDj), Params.cellValue_of_lt _ _ _ _ (Nat.not_le.mp hDj)]

/-- Register values of the certificate cells. -/
theorem value_initCfg_certGroup (bits : List Bool) (i : ℕ) (hi : i ≤ I.certBound) :
    I.value (I.initCfg bits) (I.certGroup i) =
      optionCode (symbols I.tm I.extra I.tm.k₀) ((bits.map I.certSym)[i]?) := by
  rw [certGroup, I.value_cellGroup _ _ _ (I.certCell_lt_P i hi),
    Params.cellValue_of_le _ _ _ _ (by omega), initCfg_stk_self,
    List.getElem?_append_right (by rw [I.input_length]; omega)]
  congr 2
  rw [I.input_length]
  omega

theorem value_initCfg_certGroup_eq (bits : List Bool) (i : ℕ) (hi : i ≤ I.certBound) :
    I.value (I.initCfg bits) (I.certGroup i) =
      match bits[i]? with
      | some b => I.certCode b
      | none => 0 := by
  rw [value_initCfg_certGroup _ _ _ hi, List.getElem?_map]
  cases bits[i]? <;> rfl

/-! ### The initial constraint -/

theorem certGroup_eq (i : ℕ) : I.certGroup i = I.certGroup 0 + i := by
  simp only [certGroup, Params.cellGroup]; omega

/-- The certificate index of a register, if it is a certificate cell. -/
noncomputable def certIndex? (g : ℕ) : Option ℕ :=
  if I.certGroup 0 ≤ g ∧ g < I.certGroup 0 + I.certBound then some (g - I.certGroup 0) else none

theorem certIndex?_certGroup (i : ℕ) (hi : i < I.certBound) :
    I.certIndex? (I.certGroup i) = some i := by
  have hci := I.certGroup_eq i
  rw [certIndex?, if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

theorem certIndex?_eq_some (g i : ℕ) (h : I.certIndex? g = some i) :
    i < I.certBound ∧ g = I.certGroup i := by
  simp only [certIndex?] at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  obtain ⟨h1, h2⟩ := hc
  subst h
  have hci := I.certGroup_eq (g - I.certGroup 0)
  exact ⟨by omega, by omega⟩

theorem certIndex?_eq_none_iff (g : ℕ) : I.certIndex? g = none ↔ g ∉ I.certGroups := by
  rw [mem_certGroups]
  simp only [certIndex?]
  split_ifs with hc
  · simp only [false_iff, not_not]
    have hci := I.certGroup_eq (g - I.certGroup 0)
    exact ⟨g - I.certGroup 0, by omega, by omega⟩
  · simp only [true_iff, not_exists, not_and]
    intro i hi hg
    apply hc
    have hci := I.certGroup_eq i
    omega

/-- The constraint of one first-row register: a certificate chain for a
certificate cell, otherwise fixed to the prefix-only start configuration. -/
noncomputable def initBlock (g : ℕ) : Formula ℕ :=
  match I.certIndex? g with
  | some i => I.certChain i
  | none => fixRegister I.width (I.reg 0 g) (I.value (I.initCfg []) g)

/-- The first-row constraints, register by register. -/
noncomputable def initCNF : Formula ℕ := (List.range I.count).flatMap I.initBlock

/-- The certificate cell values read from the first row. -/
noncomputable def certValue (a : Assignment ℕ) (i : ℕ) : ℕ :=
  readRegister I.width a (I.reg 0 (I.certGroup i))

theorem eval_initCNF_eq_true_iff_parts (a : Assignment ℕ) :
    Formula.eval a I.initCNF = true ↔
      (∀ g < I.count, g ∉ I.certGroups →
        readRegister I.width a (I.reg 0 g) = I.value (I.initCfg []) g) ∧
      ∀ i < I.certBound, I.certRel [I.certValue a i, I.certValue a (i + 1)] = true := by
  simp only [initCNF, eval_flatMap_eq_true_iff, List.mem_range]
  constructor
  · intro h
    refine ⟨fun g hg hng => ?_, fun i hi => ?_⟩
    · have := h g hg
      simp only [initBlock, (I.certIndex?_eq_none_iff g).2 hng] at this
      exact (eval_fixRegister_eq_true_iff _ _ _ _).1 this
    · have := h (I.certGroup i) (I.certGroup_lt_count i hi.le)
      simp only [initBlock, I.certIndex?_certGroup i hi] at this
      simpa [certChain, certValue] using this
  · rintro ⟨hfix, hchain⟩ g hg
    cases hc : I.certIndex? g with
    | none =>
        simp only [initBlock, hc]
        exact (eval_fixRegister_eq_true_iff _ _ _ _).2 (hfix g hg ((I.certIndex?_eq_none_iff g).1 hc))
    | some i =>
        obtain ⟨hi, rfl⟩ := I.certIndex?_eq_some g i hc
        simp only [initBlock, hc]
        simpa [certChain, certValue] using hchain i hi

/-- The certificate recovered from the first row. -/
noncomputable def certBits (a : Assignment ℕ) : List Bool :=
  takeSome ((List.range I.certBound).map fun i => I.certDecode (I.certValue a i))

theorem certBits_length_le (a : Assignment ℕ) : (I.certBits a).length ≤ I.certBound := by
  simpa [certBits] using takeSome_length_le ((List.range I.certBound).map fun i =>
    I.certDecode (I.certValue a i))

theorem certValue_of_lt_length (a : Assignment ℕ) (i : ℕ) (hi : i < (I.certBits a).length) :
    I.certValue a i = I.certCode ((I.certBits a)[i]'hi) := by
  have hlen := I.certBits_length_le a
  have key := takeSome_getElem? ((List.range I.certBound).map fun i =>
    I.certDecode (I.certValue a i)) i hi
  rw [List.getElem?_map, List.getElem?_range (by omega)] at key
  simp only [Option.map_some, Option.some.injEq] at key
  exact I.certDecode_eq_some _ _ key

theorem certValue_length (a : Assignment ℕ) (h : (I.certBits a).length < I.certBound) :
    I.certDecode (I.certValue a (I.certBits a).length) = none := by
  have key := takeSome_getElem?_length ((List.range I.certBound).map fun i =>
    I.certDecode (I.certValue a i)) (by simpa [certBits] using h)
  rw [List.getElem?_map, List.getElem?_range (by simpa [certBits] using h)] at key
  simpa [certBits] using key

theorem certRel_eq_true_iff (u u' : ℕ) :
    I.certRel [u, u'] = true ↔ (u = 0 ∨ u = I.cT ∨ u = I.cF) ∧ (u = 0 → u' = 0) := by
  simp only [certRel, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by tauto, fun hu => ?_⟩
    rcases h2 with h2 | h2
    · exact (h2 hu).elim
    · exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨by tauto, ?_⟩
    by_cases hu : u = 0
    · exact Or.inr (h2 hu)
    · exact Or.inl hu

/-- The certificate cells beyond the recovered certificate are empty. -/
theorem certValue_of_ge (a : Assignment ℕ)
    (hchain : ∀ i < I.certBound, I.certRel [I.certValue a i, I.certValue a (i + 1)] = true)
    (d : ℕ) (hd : (I.certBits a).length + d < I.certBound) :
    I.certValue a ((I.certBits a).length + d) = 0 := by
  induction d with
  | zero =>
      have hnone := I.certValue_length a (by omega)
      obtain ⟨h1, h2⟩ := I.certDecode_eq_none _ hnone
      have := (I.certRel_eq_true_iff _ _).1 (hchain _ (by omega))
      rcases this.1 with h | h | h
      · simpa using h
      · exact (h1 h).elim
      · exact (h2 h).elim
  | succ d ih =>
      have hprev := ih (by omega)
      have := (I.certRel_eq_true_iff _ _).1 (hchain ((I.certBits a).length + d) (by omega))
      rw [show (I.certBits a).length + (d + 1) = (I.certBits a).length + d + 1 by omega]
      exact this.2 hprev

/-- Characterization of the initial constraint. -/
theorem eval_initCNF_eq_true_iff (a : Assignment ℕ) :
    Formula.eval a I.initCNF = true ↔
      ∃ c, I.initial c ∧ ∀ g < I.count,
        I.toParams.localSystem.row a 0 g = I.value c g := by
  rw [eval_initCNF_eq_true_iff_parts]
  constructor
  · rintro ⟨hfix, hchain⟩
    refine ⟨I.initCfg (I.certBits a), ⟨I.certBits a, I.certBits_length_le a, rfl⟩, ?_⟩
    intro g hg
    change readRegister I.width a (I.reg 0 g) = _
    by_cases hcert : g ∈ I.certGroups
    · obtain ⟨i, hi, rfl⟩ := (I.mem_certGroups g).1 hcert
      rw [I.value_initCfg_certGroup_eq _ i hi.le]
      change I.certValue a i = _
      by_cases hlt : i < (I.certBits a).length
      · rw [I.certValue_of_lt_length a i hlt, List.getElem?_eq_getElem hlt]
      · have hge := Nat.not_lt.mp hlt
        rw [List.getElem?_eq_none hge]
        obtain ⟨d, rfl⟩ : ∃ d, i = (I.certBits a).length + d := ⟨i - (I.certBits a).length, by omega⟩
        exact I.certValue_of_ge a hchain d hi
    · rw [hfix g hg hcert, I.value_initCfg_of_not_cert _ (I.certBits_length_le a) g hg hcert]
  · rintro ⟨c, ⟨bits, hbits, rfl⟩, hrow⟩
    refine ⟨fun g hg hng => ?_, fun i hi => ?_⟩
    · have := hrow g hg
      change readRegister I.width a (I.reg 0 g) = _ at this
      rw [this, I.value_initCfg_of_not_cert bits hbits g hg hng]
    · have h1 := hrow (I.certGroup i) (I.certGroup_lt_count i hi.le)
      have h2 := hrow (I.certGroup (i + 1)) (I.certGroup_lt_count (i + 1) hi)
      change readRegister I.width a (I.reg 0 _) = _ at h1 h2
      change I.certValue a i = _ at h1
      change I.certValue a (i + 1) = _ at h2
      rw [I.value_initCfg_certGroup_eq _ i hi.le] at h1
      rw [I.value_initCfg_certGroup_eq _ (i + 1) hi] at h2
      rw [I.certRel_eq_true_iff, h1, h2]
      constructor
      · cases hb : bits[i]? with
        | none => simp
        | some b => cases b <;> simp [certCode_true, certCode_false]
      · intro hzero
        cases hb : bits[i]? with
        | none =>
            have : bits.length ≤ i := by
              by_contra hlt
              rw [List.getElem?_eq_getElem (Nat.not_le.mp hlt)] at hb
              cases hb
            rw [List.getElem?_eq_none (by omega)]
        | some b =>
            rw [hb] at hzero
            exact (I.certCode_ne_zero b hzero).elim

/-! ### The final constraint -/

/-- Fix every register of the last row to the halting configuration. -/
noncomputable def finalCNF : Formula ℕ :=
  (List.range I.count).flatMap fun g =>
    fixRegister I.width (I.reg I.horizon g) (I.value I.finalCfg g)

theorem eval_finalCNF_eq_true_iff (a : Assignment ℕ) :
    Formula.eval a I.finalCNF = true ↔
      ∀ g < I.count, I.toParams.localSystem.row a I.horizon g = I.value I.finalCfg g := by
  simp only [finalCNF, eval_flatMap_eq_true_iff, List.mem_range, eval_fixRegister_eq_true_iff]
  exact Iff.rfl

/-! ### The tableau -/

/-- The complete tableau formula. -/
noncomputable def tableau : Formula ℕ :=
  I.initCNF ++ I.toParams.localSystem.transitionCNF ++ I.finalCNF

/-- The tableau is satisfiable exactly when some certificate of bounded
length makes the padded run reach the required halting configuration. -/
theorem tableau_satisfiable_iff :
    I.tableau.Satisfiable ↔
      ∃ bits : List Bool, bits.length ≤ I.certBound ∧
        (padStep I.tm)^[I.horizon] (I.initCfg bits) = I.finalCfg := by
  rw [tableau, I.toParams.localSystem.satisfiable_iff I.width_pos
    (by have := I.count_ge_two; change 0 < I.count; omega)
    I.initial I.finalCfg I.initCNF I.finalCNF I.initial_inv I.finalCfg_bounded
    I.eval_initCNF_eq_true_iff I.eval_finalCNF_eq_true_iff]
  constructor
  · rintro ⟨c, ⟨bits, hbits, rfl⟩, hrun⟩
    exact ⟨bits, hbits, hrun⟩
  · rintro ⟨bits, hbits, hrun⟩
    exact ⟨I.initCfg bits, ⟨bits, hbits, rfl⟩, hrun⟩

end Instance

end LeanNPHardness.MachineTableau
