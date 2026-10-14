import LeanNPHardness.LocalTableau
import LeanNPHardness.MachineLocality
import LeanNPHardness.MachinePaddedRun
import LeanNPHardness.MachineTableauCodes

/-!
# A bundled TM2 machine as a register-local transition system

A configuration bounded in time `t` is described by registers: the label,
the internal state, and one register per padded cell of every stack. Cell
`j` of a stack holds the symbol at real index `j - D`, where `D` is the
machine's statement depth; the `D` phantom cells on each side are always
empty. Each register of the next configuration depends on the head (label,
state, top `D` cells of every stack) and, for a cell, on a window of `2D+1`
cells of its own stack. `localSystem` packages this with the time-indexed
stack-growth invariant so that `Tableau.LocalSystem.satisfiable_iff` applies.
These are semantic results; no runtime claim is made.
-/

namespace LeanNPHardness.MachineTableau

open Turing CNF CNF.Constraint MachineLocality MachinePaddedRun Tableau

/-- The shape of a machine tableau: the machine, extra output symbols, the
input length, the certificate bound, and the time horizon. -/
structure Params where
  tm : FinTM2
  extra : List (tm.Γ tm.k₁)
  inputLength : ℕ
  certBound : ℕ
  horizon : ℕ

namespace Params

variable (p : Params)

/-- Statement depth bound of the machine. -/
noncomputable def D : ℕ := machineDepth p.tm

/-- Push bound of the machine. -/
noncomputable def pb : ℕ := MachineRuntime.machinePushBound p.tm

/-- Real cells per stack: enough for the longest reachable stack plus one
empty cell, and at least two. -/
noncomputable def B : ℕ := p.inputLength + p.certBound + p.horizon * p.pb + 2

/-- Padded cells per stack. -/
noncomputable def P : ℕ := p.B + 2 * p.D

noncomputable def stackCount : ℕ := (stackList p.tm).length

/-- Registers per configuration. -/
noncomputable def count : ℕ := 2 + p.stackCount * p.P

noncomputable def maxCode : ℕ :=
  max (labels p.tm).length (max (states p.tm).length
    (((stackList p.tm).map fun k => (symbols p.tm p.extra k).length).foldr max 0))

/-- Bits per register. -/
noncomputable def width : ℕ := Nat.size p.maxCode

noncomputable def kIndex (k : p.tm.K) : ℕ := codeIn (stackList p.tm) k

/-- The register of padded cell `j` of stack `k`. -/
noncomputable def cellGroup (k : p.tm.K) (j : ℕ) : ℕ := p.kIndex k * p.P + j + 2

theorem B_ge_two : 2 ≤ p.B := by simp [B]

theorem P_pos : 0 < p.P := by have := p.B_ge_two; simp only [P]; omega

theorem B_le_P : p.B ≤ p.P := by simp [P]

theorem kIndex_lt (k : p.tm.K) : p.kIndex k < p.stackCount :=
  codeIn_lt _ k (mem_stackList p.tm k)

theorem stackList_getElem?_kIndex (k : p.tm.K) : (stackList p.tm)[p.kIndex k]? = some k :=
  decodeIn_codeIn _ k (mem_stackList p.tm k)

theorem kIndex_getElem (m : ℕ) (hm : m < (stackList p.tm).length) :
    p.kIndex ((stackList p.tm)[m]'hm) = m :=
  codeIn_getElem _ (stackList_nodup p.tm) m hm

theorem cellGroup_div (k : p.tm.K) (j : ℕ) (hj : j < p.P) :
    (p.kIndex k * p.P + j) / p.P = p.kIndex k := by
  rw [Nat.mul_comm, Nat.mul_add_div p.P_pos, Nat.div_eq_of_lt hj, Nat.add_zero]

theorem cellGroup_mod (k : p.tm.K) (j : ℕ) (hj : j < p.P) :
    (p.kIndex k * p.P + j) % p.P = j := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem cellGroup_lt_count (k : p.tm.K) (j : ℕ) (hj : j < p.P) :
    p.cellGroup k j < p.count := by
  have hk := p.kIndex_lt k
  simp only [cellGroup, count]
  have : p.kIndex k * p.P + j < (p.kIndex k + 1) * p.P := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have : (p.kIndex k + 1) * p.P ≤ p.stackCount * p.P := Nat.mul_le_mul_right _ hk
  omega

/-- Every register index at least two is a padded cell of some stack. -/
theorem exists_cellGroup (g : ℕ) (hg2 : 2 ≤ g) (hg : g < p.count) :
    ∃ k j, j < p.P ∧ g = p.cellGroup k j := by
  obtain ⟨r, rfl⟩ : ∃ r, g = r + 2 := ⟨g - 2, by omega⟩
  have hr : r < p.stackCount * p.P := by simp only [count] at hg; omega
  have hdiv : r / p.P < p.stackCount := by
    rw [Nat.div_lt_iff_lt_mul p.P_pos]; exact hr
  refine ⟨(stackList p.tm)[r / p.P]'hdiv, r % p.P, Nat.mod_lt _ p.P_pos, ?_⟩
  simp only [cellGroup, kIndex_getElem]
  rw [Nat.div_add_mod']

theorem count_ge_two : 2 ≤ p.count := by simp [count]

theorem labels_length_pos : 0 < (labels p.tm).length :=
  List.length_pos_of_mem (mem_labels p.tm p.tm.main)

theorem width_pos : 0 < p.width := by
  have := p.labels_length_pos
  simp only [width, maxCode]
  rw [Nat.pos_iff_ne_zero, Ne, Nat.size_eq_zero]
  omega

theorem lt_two_pow_width (m : ℕ) (hm : m ≤ p.maxCode) : m < 2 ^ p.width :=
  lt_of_le_of_lt hm (Nat.lt_size_self _)

theorem symbols_length_le_maxCode (k : p.tm.K) :
    (symbols p.tm p.extra k).length ≤ p.maxCode := by
  simp only [maxCode]
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_right _ _)
  exact le_foldr_max _ _ (List.mem_map.mpr ⟨k, mem_stackList p.tm k, rfl⟩)

/-! ### Register values -/

/-- Symbol validity: every stack symbol belongs to the finite symbol list. -/
def SymbolsValid (c : p.tm.Cfg) : Prop :=
  ∀ k, ∀ s ∈ c.stk k, s ∈ symbols p.tm p.extra k

/-- The value of padded cell `j` of stack `k`: the coded symbol at real index
`j - D`, with phantom cells empty. -/
noncomputable def cellValue (c : p.tm.Cfg) (k : p.tm.K) (j : ℕ) : ℕ :=
  if p.D ≤ j then optionCode (symbols p.tm p.extra k) ((c.stk k)[j - p.D]?) else 0

/-- Register values of a configuration. -/
noncomputable def value (c : p.tm.Cfg) : ℕ → ℕ
  | 0 => optionCode (labels p.tm) c.l
  | 1 => codeIn (states p.tm) c.var
  | r + 2 =>
      match (stackList p.tm)[r / p.P]? with
      | some k => p.cellValue c k (r % p.P)
      | none => 0

@[simp]
theorem value_zero (c : p.tm.Cfg) : p.value c 0 = optionCode (labels p.tm) c.l := rfl

@[simp]
theorem value_one (c : p.tm.Cfg) : p.value c 1 = codeIn (states p.tm) c.var := rfl

theorem value_cellGroup (c : p.tm.Cfg) (k : p.tm.K) (j : ℕ) (hj : j < p.P) :
    p.value c (p.cellGroup k j) = p.cellValue c k j := by
  simp only [cellGroup, value, p.cellGroup_div k j hj, p.cellGroup_mod k j hj,
    p.stackList_getElem?_kIndex k]

theorem cellValue_of_lt (c : p.tm.Cfg) (k : p.tm.K) (j : ℕ) (hj : j < p.D) :
    p.cellValue c k j = 0 := by
  simp [cellValue, Nat.not_le.mpr hj]

theorem cellValue_of_le (c : p.tm.Cfg) (k : p.tm.K) (j : ℕ) (hj : p.D ≤ j) :
    p.cellValue c k j = optionCode (symbols p.tm p.extra k) ((c.stk k)[j - p.D]?) := by
  simp [cellValue, hj]

theorem cellValue_real (c : p.tm.Cfg) (k : p.tm.K) (i : ℕ) :
    p.cellValue c k (p.D + i) = optionCode (symbols p.tm p.extra k) ((c.stk k)[i]?) := by
  rw [cellValue_of_le _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getElem?_valid (c : p.tm.Cfg) (hc : p.SymbolsValid c) (k : p.tm.K) (i : ℕ) :
    ∀ s ∈ (c.stk k)[i]?, s ∈ symbols p.tm p.extra k := by
  intro s hs
  exact hc k s (List.mem_of_getElem? hs)

theorem cellValue_le (c : p.tm.Cfg) (hc : p.SymbolsValid c) (k : p.tm.K) (j : ℕ) :
    p.cellValue c k j ≤ (symbols p.tm p.extra k).length := by
  by_cases hj : p.D ≤ j
  · rw [cellValue_of_le _ _ _ _ hj]
    exact optionCode_le _ _ (p.getElem?_valid c hc k _)
  · rw [cellValue_of_lt _ _ _ _ (Nat.not_le.mp hj)]; exact Nat.zero_le _

/-! ### Heads and dependency lists -/

/-- The data one statement reads: the label, the state, and the top `D`
symbols of every stack. -/
structure Head (tm : FinTM2) where
  label : Option tm.Λ
  state : tm.σ
  tops : ∀ k, List (tm.Γ k)

/-- The head of a configuration. -/
noncomputable def cfgHead (c : p.tm.Cfg) : Head p.tm := ⟨c.l, c.var, fun k => (c.stk k).take p.D⟩

/-- The registers holding the head: label, state, then the top `D` real cells
of every stack in stack-list order. -/
noncomputable def headGroups : List ℕ :=
  [0, 1] ++ (stackList p.tm).flatMap fun k => (List.range p.D).map fun i => p.cellGroup k (p.D + i)

theorem headGroups_length : p.headGroups.length = 2 + p.stackCount * p.D := by
  simp [headGroups, List.length_flatMap, stackCount]
  omega

theorem headGroups_getElem?_zero : p.headGroups[0]? = some 0 := by simp [headGroups]

theorem headGroups_getElem?_one : p.headGroups[1]? = some 1 := by simp [headGroups]

theorem headGroups_getElem?_cell (k : p.tm.K) (i : ℕ) (hi : i < p.D) :
    p.headGroups[2 + p.kIndex k * p.D + i]? = some (p.cellGroup k (p.D + i)) := by
  simp only [headGroups]
  rw [List.getElem?_append_right (by simp; omega)]
  have hidx : 2 + p.kIndex k * p.D + i - [0, 1].length = p.kIndex k * p.D + i := by
    simp; omega
  rw [hidx]
  rw [getElem?_flatMap_uniform _ _ p.D (fun _ => by simp) _ _ (p.kIndex_lt k) hi]
  have hk : (stackList p.tm)[p.kIndex k]'(p.kIndex_lt k) = k := by
    have := p.stackList_getElem?_kIndex k
    rw [List.getElem?_eq_getElem (p.kIndex_lt k)] at this
    exact Option.some.inj this
  rw [hk]
  simp [hi]

/-- Decode a head from the leading register values. -/
noncomputable def decodeHead (vs : List ℕ) : Head p.tm where
  label := optionDecode (labels p.tm) (vs.getD 0 0)
  state := (decodeIn (states p.tm) (vs.getD 1 0)).getD p.tm.initialState
  tops k := takeSome ((List.range p.D).map fun i =>
    optionDecode (symbols p.tm p.extra k) (vs.getD (2 + p.kIndex k * p.D + i) 0))

/-- Decoding only reads the head positions. -/
theorem decodeHead_append (vs ws : List ℕ) (hvs : p.headGroups.length ≤ vs.length) :
    p.decodeHead (vs ++ ws) = p.decodeHead vs := by
  rw [headGroups_length] at hvs
  have key : ∀ i, i < 2 + p.stackCount * p.D → (vs ++ ws).getD i 0 = vs.getD i 0 := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  simp only [decodeHead]
  congr 1
  · rw [key 0 (by omega)]
  · rw [key 1 (by omega)]
  · funext k
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    have hk := p.kIndex_lt k
    rw [key _ (by
      have : p.kIndex k * p.D + i < (p.kIndex k + 1) * p.D := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      have : (p.kIndex k + 1) * p.D ≤ p.stackCount * p.D := Nat.mul_le_mul_right _ hk
      omega)]

/-- The head registers of a valid configuration decode to its head. -/
theorem decodeHead_value (c : p.tm.Cfg) (hc : p.SymbolsValid c) :
    p.decodeHead (p.headGroups.map (p.value c)) = p.cfgHead c := by
  simp only [decodeHead, cfgHead]
  congr 1
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, p.headGroups_getElem?_zero]
    simp only [Option.map_some, Option.getD_some, value_zero]
    exact optionDecode_optionCode _ _ (fun x _ => mem_labels p.tm x)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, p.headGroups_getElem?_one]
    simp [decodeIn_codeIn _ _ (mem_states p.tm c.var)]
  · funext k
    rw [← takeSome_map_getElem? (c.stk k) p.D]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, p.headGroups_getElem?_cell k i hi']
    simp only [Option.map_some, Option.getD_some]
    rw [p.value_cellGroup c k (p.D + i) (by simp only [P]; omega), cellValue_real]
    exact optionDecode_optionCode _ _ (p.getElem?_valid c hc k i)

/-- The padded local step on a head: a halted head is unchanged, a live head
executes its statement on the top symbols. -/
noncomputable def headStep (h : Head p.tm) : p.tm.Cfg :=
  match h.label with
  | none => ⟨none, h.state, h.tops⟩
  | some l => TM2.stepAux (p.tm.m l) h.state h.tops

theorem headStep_none (h : Head p.tm) (hl : h.label = none) :
    p.headStep h = ⟨none, h.state, h.tops⟩ := by
  simp [headStep, hl]

theorem headStep_some (h : Head p.tm) (l : p.tm.Λ) (hl : h.label = some l) :
    p.headStep h = TM2.stepAux (p.tm.m l) h.state h.tops := by
  simp [headStep, hl]

/-- The registers of the `2D+1` cells around padded cell `j` of stack `k`. -/
noncomputable def windowGroups (k : p.tm.K) (j : ℕ) : List ℕ :=
  (List.range (2 * p.D + 1)).map fun i => p.cellGroup k (j - p.D + i)

theorem windowGroups_length (k : p.tm.K) (j : ℕ) : (p.windowGroups k j).length = 2 * p.D + 1 := by
  simp [windowGroups]

theorem windowGroups_map_getD (c : p.tm.Cfg) (k : p.tm.K) (j m : ℕ) (hm : m < 2 * p.D + 1) :
    ((p.windowGroups k j).map (p.value c)).getD m 0 = p.value c (p.cellGroup k (j - p.D + m)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [windowGroups, List.getElem?_range hm]

/-- Whether padded cell `j` is a real cell. -/
def IsReal (j : ℕ) : Prop := p.D ≤ j ∧ j + p.D < p.P

noncomputable instance (j : ℕ) : Decidable (p.IsReal j) := by unfold IsReal; infer_instance

/-- Dependency registers. -/
noncomputable def deps : ℕ → List ℕ
  | 0 => p.headGroups
  | 1 => p.headGroups
  | r + 2 =>
      match (stackList p.tm)[r / p.P]? with
      | some k => if p.IsReal (r % p.P) then p.headGroups ++ p.windowGroups k (r % p.P) else []
      | none => []

@[simp]
theorem deps_zero : p.deps 0 = p.headGroups := rfl

@[simp]
theorem deps_one : p.deps 1 = p.headGroups := rfl

theorem deps_cellGroup (k : p.tm.K) (j : ℕ) (hj : j < p.P) :
    p.deps (p.cellGroup k j) =
      if p.IsReal j then p.headGroups ++ p.windowGroups k j else [] := by
  simp only [cellGroup, deps, p.cellGroup_div k j hj, p.cellGroup_mod k j hj,
    p.stackList_getElem?_kIndex k]

/-- The new value of real cell `i` of stack `k`: a symbol of the new top
region, or the old cell shifted by the net change in stack height. -/
noncomputable def cellUpdate (k : p.tm.K) (newTop : List (p.tm.Γ k)) (window : List ℕ) (i : ℕ) : ℕ :=
  if i < newTop.length then optionCode (symbols p.tm p.extra k) newTop[i]?
  else window.getD (2 * p.D - newTop.length) 0

/-- The update function. -/
noncomputable def update (g : ℕ) (vs : List ℕ) : ℕ :=
  match g with
  | 0 => optionCode (labels p.tm) (p.headStep (p.decodeHead vs)).l
  | 1 => codeIn (states p.tm) (p.headStep (p.decodeHead vs)).var
  | r + 2 =>
      match (stackList p.tm)[r / p.P]? with
      | some k =>
          if p.IsReal (r % p.P) then
            match (p.decodeHead vs).label with
            | none => (vs.drop p.headGroups.length).getD p.D 0
            | some _ =>
                p.cellUpdate k ((p.headStep (p.decodeHead vs)).stk k)
                  (vs.drop p.headGroups.length) (r % p.P - p.D)
          else 0
      | none => 0

@[simp]
theorem update_zero (vs : List ℕ) :
    p.update 0 vs = optionCode (labels p.tm) (p.headStep (p.decodeHead vs)).l := rfl

@[simp]
theorem update_one (vs : List ℕ) :
    p.update 1 vs = codeIn (states p.tm) (p.headStep (p.decodeHead vs)).var := rfl

theorem update_cellGroup (k : p.tm.K) (j : ℕ) (hj : j < p.P) (vs : List ℕ) :
    p.update (p.cellGroup k j) vs =
      if p.IsReal j then
        match (p.decodeHead vs).label with
        | none => (vs.drop p.headGroups.length).getD p.D 0
        | some _ =>
            p.cellUpdate k ((p.headStep (p.decodeHead vs)).stk k)
              (vs.drop p.headGroups.length) (j - p.D)
      else 0 := by
  simp only [cellGroup, update, p.cellGroup_div k j hj, p.cellGroup_mod k j hj,
    p.stackList_getElem?_kIndex k]

/-! ### Invariants -/

/-- The time-indexed invariant: stacks grow at most `pb` per step. -/
def Inv (t : ℕ) (c : p.tm.Cfg) : Prop :=
  (∀ k, (c.stk k).length ≤ p.inputLength + p.certBound + t * p.pb) ∧ p.SymbolsValid c

/-- Configurations determined by their registers. -/
def Bounded (c : p.tm.Cfg) : Prop :=
  (∀ k, (c.stk k).length < p.B) ∧ p.SymbolsValid c

theorem inv_step (t : ℕ) (c : p.tm.Cfg) (hc : p.Inv t c) : p.Inv (t + 1) (padStep p.tm c) := by
  obtain ⟨hlen, hsym⟩ := hc
  cases hstep : p.tm.step c with
  | none =>
      rw [padStep_of_halt p.tm c ((step_eq_none_iff p.tm c).1 hstep)]
      refine ⟨fun k => ?_, hsym⟩
      have := hlen k
      rw [Nat.succ_mul]
      omega
  | some c' =>
      rw [padStep_of_step p.tm c c' hstep]
      refine ⟨fun k => ?_, step_stk_mem p.tm p.extra c c' hstep hsym⟩
      have := MachineRuntime.step_stack_length_le p.tm c c' k hstep
      have := hlen k
      rw [Nat.succ_mul]
      simp only [pb] at *
      omega

theorem inv_bounded (t : ℕ) (c : p.tm.Cfg) (ht : t ≤ p.horizon) (hc : p.Inv t c) : p.Bounded c := by
  obtain ⟨hlen, hsym⟩ := hc
  refine ⟨fun k => ?_, hsym⟩
  have := hlen k
  have : t * p.pb ≤ p.horizon * p.pb := Nat.mul_le_mul_right _ ht
  simp only [B]
  omega

theorem value_lt (c : p.tm.Cfg) (g : ℕ) (hc : p.Bounded c) (hg : g < p.count) :
    p.value c g < 2 ^ p.width := by
  apply p.lt_two_pow_width
  match g with
  | 0 =>
      simp only [value_zero, maxCode]
      exact (optionCode_le _ _ (fun x _ => mem_labels p.tm x)).trans (le_max_left _ _)
  | 1 =>
      simp only [value_one, maxCode]
      exact (codeIn_lt _ _ (mem_states p.tm c.var)).le.trans
        ((le_max_left _ _).trans (le_max_right _ _))
  | r + 2 =>
      obtain ⟨k, j, hj, hg'⟩ := p.exists_cellGroup (r + 2) (by omega) hg
      rw [hg', p.value_cellGroup c k j hj]
      exact (p.cellValue_le c hc.2 k j).trans (p.symbols_length_le_maxCode k)

theorem headGroups_lt (g : ℕ) (hg : g ∈ p.headGroups) : g < p.count := by
  simp only [headGroups, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hg
  have h2 := p.count_ge_two
  rcases hg with (rfl | rfl) | ⟨k, _, i, hi, rfl⟩
  · omega
  · omega
  · exact p.cellGroup_lt_count k (p.D + i) (by simp only [P]; omega)

theorem deps_lt (g : ℕ) (hg : g < p.count) : ∀ d ∈ p.deps g, d < p.count := by
  match g with
  | 0 => exact fun d hd => p.headGroups_lt d hd
  | 1 => exact fun d hd => p.headGroups_lt d hd
  | r + 2 =>
      obtain ⟨k, j, hj, hg'⟩ := p.exists_cellGroup (r + 2) (by omega) hg
      rw [hg', p.deps_cellGroup k j hj]
      intro d hd
      split_ifs at hd with hreal
      · simp only [List.mem_append, windowGroups, List.mem_map, List.mem_range] at hd
        rcases hd with hd | ⟨m, hm, rfl⟩
        · exact p.headGroups_lt d hd
        · obtain ⟨hDj, hjP⟩ := hreal
          exact p.cellGroup_lt_count k _ (by omega)
      · simp at hd

/-- A configuration is determined by its registers once bounded. -/
theorem value_injective (c c' : p.tm.Cfg) (hc : p.Bounded c) (hc' : p.Bounded c')
    (h : ∀ g, g < p.count → p.value c g = p.value c' g) : c = c' := by
  have h2 := p.count_ge_two
  have hl : c.l = c'.l := by
    have := h 0 (by omega)
    simp only [value_zero] at this
    exact optionCode_injective _ _ _ (fun x _ => mem_labels p.tm x) (fun x _ => mem_labels p.tm x) this
  have hv : c.var = c'.var := by
    have := h 1 (by omega)
    simp only [value_one] at this
    exact codeIn_injective _ _ _ (mem_states p.tm _) (mem_states p.tm _) this
  have hs : c.stk = c'.stk := by
    funext k
    apply List.ext_getElem?
    intro i
    by_cases hi : i < p.B
    · have hj : p.D + i < p.P := by simp only [P]; omega
      have := h (p.cellGroup k (p.D + i)) (p.cellGroup_lt_count k _ hj)
      rw [p.value_cellGroup c k _ hj, p.value_cellGroup c' k _ hj, cellValue_real, cellValue_real] at this
      exact optionCode_injective _ _ _ (p.getElem?_valid c hc.2 k i) (p.getElem?_valid c' hc'.2 k i) this
    · have h1 := hc.1 k
      have h2 := hc'.1 k
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  cases c; cases c'
  simp only at hl hv hs
  subst hl hv hs
  rfl

/-! ### Locality of the padded step -/

theorem stepAux_split (c : p.tm.Cfg) (l : p.tm.Λ) :
    TM2.stepAux (p.tm.m l) c.var c.stk =
      ⟨(TM2.stepAux (p.tm.m l) c.var fun k => (c.stk k).take p.D).l,
        (TM2.stepAux (p.tm.m l) c.var fun k => (c.stk k).take p.D).var,
        fun k => (TM2.stepAux (p.tm.m l) c.var fun k => (c.stk k).take p.D).stk k ++
          (c.stk k).drop p.D⟩ := by
  have hsplit : c.stk = fun k => (c.stk k).take p.D ++ (c.stk k).drop p.D := by
    funext k; simp
  conv_lhs => rw [hsplit]
  apply stepAux_append
  intro k
  by_cases hk : p.D ≤ (c.stk k).length
  · left
    rw [List.length_take, Nat.min_eq_left hk]
    exact depth_le_machineDepth p.tm l
  · right
    exact List.drop_of_length_le (by omega)

/-- The new top region has at most `2D` symbols. -/
theorem newTop_length_le (c : p.tm.Cfg) (l : p.tm.Λ) (k : p.tm.K) :
    ((TM2.stepAux (p.tm.m l) c.var fun k => (c.stk k).take p.D).stk k).length ≤ 2 * p.D := by
  have h1 := MachineRuntime.stepAux_stack_length_le (p.tm.m l) c.var (fun k => (c.stk k).take p.D) k
  have h2 := (stmtPushBound_le_depth (p.tm.m l)).trans (depth_le_machineDepth p.tm l)
  simp only [List.length_take] at h1
  have : min p.D (c.stk k).length ≤ p.D := Nat.min_le_left _ _
  simp only [D] at *
  omega

theorem padStep_eq_of_some (c : p.tm.Cfg) (l : p.tm.Λ) (hl : c.l = some l) :
    padStep p.tm c = TM2.stepAux (p.tm.m l) c.var c.stk := by
  apply padStep_of_step
  rcases c with ⟨label, state, contents⟩
  simp only at hl
  subst hl
  rfl

/-- Local correctness of the update function for a live, bounded step. -/
theorem local_step (t : ℕ) (c : p.tm.Cfg) (ht : t < p.horizon) (hc : p.Inv t c) (g : ℕ)
    (hg : g < p.count) :
    p.value (padStep p.tm c) g = p.update g ((p.deps g).map (p.value c)) := by
  have hnext := p.inv_step t c hc
  have hnextB := p.inv_bounded (t + 1) _ ht hnext
  have hhead : p.decodeHead (p.headGroups.map (p.value c)) = p.cfgHead c :=
    p.decodeHead_value c hc.2
  match g with
  | 0 =>
      simp only [value_zero, update_zero, deps_zero, hhead, cfgHead]
      cases hl : c.l with
      | none =>
          rw [padStep_of_halt p.tm c hl, hl, p.headStep_none _ rfl]
      | some l =>
          rw [p.padStep_eq_of_some c l hl, p.stepAux_split c l, p.headStep_some _ l rfl]
  | 1 =>
      simp only [value_one, update_one, deps_one, hhead, cfgHead]
      cases hl : c.l with
      | none =>
          rw [padStep_of_halt p.tm c hl, p.headStep_none _ rfl]
      | some l =>
          rw [p.padStep_eq_of_some c l hl, p.stepAux_split c l, p.headStep_some _ l rfl]
  | r + 2 =>
      obtain ⟨k, j, hj, hg'⟩ := p.exists_cellGroup (r + 2) (by omega) hg
      rw [hg', p.value_cellGroup _ k j hj, p.deps_cellGroup k j hj, p.update_cellGroup k j hj]
      by_cases hreal : p.IsReal j
      · obtain ⟨hDj, hjP⟩ := hreal
        rw [if_pos ⟨hDj, hjP⟩, if_pos ⟨hDj, hjP⟩, List.map_append,
          p.decodeHead_append _ _ (by simp), hhead,
          List.drop_left' (by simp)]
        simp only [cfgHead]
        cases hl : c.l with
        | none =>
            rw [padStep_of_halt p.tm c hl, p.windowGroups_map_getD c k j p.D (by omega),
              Nat.sub_add_cancel hDj, p.value_cellGroup c k j hj]
        | some l =>
            rw [p.padStep_eq_of_some c l hl, p.stepAux_split c l, p.headStep_some _ l rfl]
            simp only [cellUpdate]
            rw [cellValue_of_le _ _ _ _ hDj]
            have hS'len := p.newTop_length_le c l k
            by_cases hi : j - p.D <
                ((TM2.stepAux (p.tm.m l) c.var fun k => (c.stk k).take p.D).stk k).length
            · rw [if_pos hi, List.getElem?_append_left hi]
            · rw [if_neg hi]
              have hi' := Nat.not_lt.mp hi
              rw [List.getElem?_append_right hi', List.getElem?_drop,
                p.windowGroups_map_getD c k j _ (by omega),
                p.value_cellGroup c k _ (by omega),
                cellValue_of_le _ _ _ _ (by omega)]
              congr 2
              omega
      · rw [if_neg hreal]
        simp only [IsReal, not_and, Nat.not_lt] at hreal
        by_cases hDj : p.D ≤ j
        · have hjP := hreal hDj
          rw [cellValue_of_le _ _ _ _ hDj, List.getElem?_eq_none, optionCode_none]
          have := hnextB.1 k
          simp only [P] at hjP
          omega
        · exact p.cellValue_of_lt _ k j (Nat.not_le.mp hDj)

/-- The register-local system of a bundled machine. -/
noncomputable def localSystem : LocalSystem p.tm.Cfg where
  step := padStep p.tm
  width := p.width
  count := p.count
  horizon := p.horizon
  value := p.value
  deps := p.deps
  update := p.update
  Inv := p.Inv
  Bounded := p.Bounded
  inv_step := fun t c _ hc => p.inv_step t c hc
  inv_bounded := p.inv_bounded
  value_lt := fun c g hc hg => p.value_lt c g hc hg
  deps_lt := p.deps_lt
  local_step := p.local_step
  value_injective := p.value_injective

end Params

end LeanNPHardness.MachineTableau
