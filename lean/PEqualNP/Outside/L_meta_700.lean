import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_700_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation

/-! ## Section 1: Bowtie graph and basic circuit semantics -/

def bowtieEdges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

def bowtieAdjB (u v : Fin 5) : Bool :=
  decide ((u.val, v.val) ∈ bowtieEdges ∨ (v.val, u.val) ∈ bowtieEdges)

abbrev bowtieAdj (u v : Fin 5) : Prop := bowtieAdjB u v = true

theorem bowtieAdj_iff (u v : Fin 5) :
    bowtieAdj u v ↔ (u.val, v.val) ∈ bowtieEdges ∨ (v.val, u.val) ∈ bowtieEdges := by
  simp [bowtieAdj, bowtieAdjB]

theorem bowtieAdj_symm {u v : Fin 5} (h : bowtieAdj u v) : bowtieAdj v u := by
  rw [bowtieAdj_iff] at h ⊢; exact h.symm

theorem bowtieAdj_irrefl (u : Fin 5) : ¬ bowtieAdj u u := by
  fin_cases u <;> decide

theorem bowtie_deg2 : ∀ v : Fin 5, ∃ a b : Fin 5, a ≠ b ∧ bowtieAdj v a ∧ bowtieAdj v b := by
  decide

theorem bowtie_uniqN : ∀ u v : Fin 5, u ≠ v → ∃ w : Fin 5, bowtieAdj v w ∧ ¬ bowtieAdj u w := by
  decide

theorem bowtie_other_nbr : ∀ u v : Fin 5, u ≠ v → ∃ w : Fin 5, w ≠ v ∧ bowtieAdj u w := by
  decide

theorem bowtie_tri_mate : ∀ u v : Fin 5, bowtieAdj u v →
    ∃ w : Fin 5, w ≠ u ∧ w ≠ v ∧ bowtieAdj u w ∧ bowtieAdj v w := by
  decide

theorem bowtie_edge_avoid : ∀ v : Fin 5, ∃ a b : Fin 5, a ≠ v ∧ b ≠ v ∧ bowtieAdj a b := by
  decide

theorem bowtie_vc_ge3 (S : Finset (Fin 5))
    (hS : ∀ u v : Fin 5, bowtieAdj u v → u ∈ S ∨ v ∈ S) : 3 ≤ S.card := by
  have h12 : (1 : Fin 5) ∈ S ∨ (2 : Fin 5) ∈ S := hS 1 2 (by decide)
  have h01 : (0 : Fin 5) ∈ S ∨ (1 : Fin 5) ∈ S := hS 0 1 (by decide)
  have h02 : (0 : Fin 5) ∈ S ∨ (2 : Fin 5) ∈ S := hS 0 2 (by decide)
  have h34 : (3 : Fin 5) ∈ S ∨ (4 : Fin 5) ∈ S := hS 3 4 (by decide)
  have htri : 2 ≤ (S ∩ ({0, 1, 2} : Finset (Fin 5))).card := by
    by_cases h0 : (0 : Fin 5) ∈ S
    · rcases h12 with h1 | h2
      · exact (show ({0, 1} : Finset (Fin 5)).card = 2 by decide) ▸
          Finset.card_le_card (by intro x hx; simp at hx ⊢; rcases hx with rfl | rfl <;> simp [h0, h1])
      · exact (show ({0, 2} : Finset (Fin 5)).card = 2 by decide) ▸
          Finset.card_le_card (by intro x hx; simp at hx ⊢; rcases hx with rfl | rfl <;> simp [h0, h2])
    · have h1 : (1 : Fin 5) ∈ S := h01.resolve_left h0
      have h2 : (2 : Fin 5) ∈ S := h02.resolve_left h0
      exact (show ({1, 2} : Finset (Fin 5)).card = 2 by decide) ▸
        Finset.card_le_card (by intro x hx; simp at hx ⊢; rcases hx with rfl | rfl <;> simp [h1, h2])
  have hedge : 1 ≤ (S ∩ ({3, 4} : Finset (Fin 5))).card := by
    rcases h34 with h3 | h4
    · exact Finset.card_pos.mpr ⟨3, Finset.mem_inter.mpr ⟨h3, by decide⟩⟩
    · exact Finset.card_pos.mpr ⟨4, Finset.mem_inter.mpr ⟨h4, by decide⟩⟩
  have hdisj : Disjoint (S ∩ ({0, 1, 2} : Finset (Fin 5))) (S ∩ ({3, 4} : Finset (Fin 5))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1.2 with rfl | rfl | rfl <;> simp at hx2
  have hsub : (S ∩ ({0, 1, 2} : Finset (Fin 5))) ∪ (S ∩ ({3, 4} : Finset (Fin 5))) ⊆ S :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hc
  omega

def BowtieEval (C : Circuit) : Prop :=
  ∀ x : Fin 5 → Bool,
    (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ bowtieEdges ∧ x u = true ∧ x v = true)

theorem bowtieEval_adj {C : Circuit} (hE : BowtieEval C) (x : Fin 5 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, bowtieAdj u v ∧ x u = true ∧ x v = true := by
  rw [hE x]
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    exact ⟨u, v, (bowtieAdj_iff u v).mpr (Or.inl huv), hxu, hxv⟩
  · rintro ⟨u, v, huv, hxu, hxv⟩
    rcases (bowtieAdj_iff u v).mp huv with h | h
    · exact ⟨u, v, h, hxu, hxv⟩
    · exact ⟨v, u, h, hxv, hxu⟩

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht]; simp [hl]

theorem getD_ext (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val (C : Circuit) (x : Fin 5 → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_output (C : Circuit) (x : Fin 5 → Bool) :
    val C x C.output = C.eval (List.ofFn x) := rfl

theorem val_input (C : Circuit) (x : Fin 5 → Bool) (i : Fin 5) :
    val C x i.val = x i := by
  rw [val, getD_ext _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  fin_cases i <;> rfl

theorem val_beyond (C : Circuit) (x : Fin 5 → Bool) {i : ℕ}
    (hi : 5 + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand (C : Circuit) (x : Fin 5 → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate (C : Circuit) (x : Fin 5 → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (5 + p) = g.op.eval (g.inputs.map (operand C x (5 + p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop (p + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = 5 + p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (5 + p) i := by
    by_cases hi : i < 5 + p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact getD_ext _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (5 + p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p + 1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (5 + p) false = _
  rw [getD_ext _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

theorem val_and {C : Circuit} (x : Fin 5 → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) (hop : g.op = GateOp.and) :
    val C x (5 + p) = true ↔ ∀ i ∈ g.inputs, i < 5 + p ∧ val C x i = true := by
  rw [val_gate C x hp, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id, operand]
  constructor
  · intro h i hi
    have := h i hi
    split_ifs at this with hlt
    exact ⟨hlt, this⟩
  · intro h i hi
    obtain ⟨hlt, hv⟩ := h i hi
    simp [hlt, hv]

theorem val_or {C : Circuit} (x : Fin 5 → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) (hop : g.op = GateOp.or) :
    val C x (5 + p) = true ↔ ∃ i ∈ g.inputs, i < 5 + p ∧ val C x i = true := by
  rw [val_gate C x hp, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id, operand]
  constructor
  · rintro ⟨i, hi, hv⟩
    split_ifs at hv with hlt
    exact ⟨i, hi, hlt, hv⟩
  · rintro ⟨i, hi, hlt, hv⟩
    exact ⟨i, hi, by simp [hlt, hv]⟩

theorem mono_op {C : Circuit} (hC : Monotone2 C) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  have hm := (hC g (List.mem_of_getElem? hp)).1
  simpa using hm

theorem val_mono {C : Circuit} (hC : Monotone2 C) {x y : Fin 5 → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hlt : w < 5
    · have : w = (⟨w, hlt⟩ : Fin 5).val := rfl
      rw [this, val_input] at hwx ⊢
      exact hxy ⟨w, hlt⟩ hwx
    · by_cases hbd : w < 5 + C.gates.length
      · set p := w - 5
        have hw : w = 5 + p := by omega
        have hp_lt : p < C.gates.length := by omega
        obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
        rw [hw] at hwx ⊢
        rcases mono_op hC hg with hop | hop
        · rw [val_and y hg hop]
          rw [val_and x hg hop] at hwx
          intro i hi
          obtain ⟨hilt, hvi⟩ := hwx i hi
          exact ⟨hilt, ih i (by omega) hvi⟩
        · rw [val_or y hg hop]
          rw [val_or x hg hop] at hwx
          obtain ⟨i, hi, hilt, hvi⟩ := hwx
          exact ⟨i, hi, hilt, ih i (by omega) hvi⟩
      · rw [val_beyond C x (by omega)] at hwx
        cases hwx

def sing (u : Fin 5) : Fin 5 → Bool := fun i => decide (i = u)
def pairIn (u v : Fin 5) : Fin 5 → Bool := fun i => decide (i = u ∨ i = v)
def zeroIn : Fin 5 → Bool := fun _ => false

theorem bowtie_zero {C : Circuit} (hE : BowtieEval C) :
    val C zeroIn C.output = false := by
  rw [val_output, Bool.eq_false_iff]
  intro h
  obtain ⟨u, v, _, hxu, _⟩ := (bowtieEval_adj hE zeroIn).mp h
  simp [zeroIn] at hxu

theorem bowtie_sing {C : Circuit} (hE : BowtieEval C) (u : Fin 5) :
    val C (sing u) C.output = false := by
  rw [val_output, Bool.eq_false_iff]
  intro h
  obtain ⟨a, b, hab, ha, hb⟩ := (bowtieEval_adj hE (sing u)).mp h
  simp only [sing, decide_eq_true_eq] at ha hb
  subst ha hb
  exact bowtieAdj_irrefl _ hab

theorem bowtie_pair_iff {C : Circuit} (hE : BowtieEval C) (u v : Fin 5) :
    val C (pairIn u v) C.output = true ↔ bowtieAdj u v := by
  rw [val_output, bowtieEval_adj hE]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairIn, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (bowtieAdj_irrefl _)
    · exact hab
    · exact bowtieAdj_symm hab
    · exact absurd hab (bowtieAdj_irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairIn], by simp [pairIn]⟩

/-! ## Section 2: Liveness, fan-out budget, and branch-free chains -/

def Next (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = 5 + p ∧ a ∈ g.inputs

def Live (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next C) i C.output

def LNext (C : Circuit) (a b : ℕ) : Prop := Next C a b ∧ Live C b

theorem next_lt {C : Circuit} {a b : ℕ} (h : Next C a b) : a < b := h.1

theorem next_le {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next C) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem lnext_le {C : Circuit} {a b : ℕ} (h : ReflTransGen (LNext C) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.1.le

theorem live_le_output {C : Circuit} {a : ℕ} (h : Live C a) : a ≤ C.output :=
  next_le h

theorem live_of_lnext {C : Circuit} {a b : ℕ} (h : LNext C a b) : Live C a :=
  (ReflTransGen.single h.1).trans h.2

theorem output_bounds {C : Circuit} (hE : BowtieEval C) :
    5 ≤ C.output ∧ C.output < 5 + C.gates.length := by
  constructor
  · by_contra hlt
    push Not at hlt
    have h0 : val C (pairIn 1 2) C.output = true := (bowtie_pair_iff hE 1 2).mpr (by decide)
    have h1 : val C (pairIn 3 4) C.output = true := (bowtie_pair_iff hE 3 4).mpr (by decide)
    have heq : C.output = (⟨C.output, hlt⟩ : Fin 5).val := rfl
    rw [heq, val_input] at h0 h1
    simp only [pairIn, decide_eq_true_eq] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      have := h0.symm.trans h1 <;> simp [Fin.ext_iff] at this
  · by_contra hge
    push Not at hge
    have h0 : val C (pairIn 0 1) C.output = true := (bowtie_pair_iff hE 0 1).mpr (by decide)
    rw [val_beyond C _ hge] at h0
    cases h0

theorem eval_eq_of_no_reach {C : Circuit} {v : Fin 5} {x y : Fin 5 → Bool}
    (hag : ∀ i : Fin 5, i ≠ v → x i = y i) :
    ∀ w, ¬ ReflTransGen (Next C) v.val w → val C x w = val C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hnr
    by_cases hlt : w < 5
    · have hw : w = (⟨w, hlt⟩ : Fin 5).val := rfl
      rw [hw, val_input, val_input]
      apply hag ⟨w, hlt⟩
      intro heq
      apply hnr
      rw [show v.val = w by simpa using congrArg Fin.val heq.symm]
    · by_cases hbd : w < 5 + C.gates.length
      · set p := w - 5
        have hw : w = 5 + p := by omega
        have hp_lt : p < C.gates.length := by omega
        obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
        rw [hw, val_gate C x hg, val_gate C y hg]
        congr 1
        apply List.map_congr_left
        intro i hi
        unfold operand
        split_ifs with hilt
        · apply ih i (by omega)
          intro hr
          apply hnr
          exact hr.tail ⟨by omega, p, g, hg, hw, hi⟩
        · rfl
      · rw [val_beyond C x (by omega), val_beyond C y (by omega)]

theorem input_live {C : Circuit} (hE : BowtieEval C) (v : Fin 5) : Live C v.val := by
  by_contra hnr
  obtain ⟨a, _, _, hva, _⟩ := bowtie_deg2 v
  have heq := eval_eq_of_no_reach (C := C) (v := v) (x := sing a) (y := pairIn v a)
    (fun i hi => by
      simp only [sing, pairIn]
      by_cases hia : i = a <;> simp [hi, hia])
    C.output hnr
  have h1 : val C (sing a) C.output = false := bowtie_sing hE a
  have h2 : val C (pairIn v a) C.output = true := (bowtie_pair_iff hE v a).mpr hva
  rw [h1, h2] at heq
  cases heq

open Classical in
noncomputable def living (C : Circuit) : Finset ℕ :=
  (Finset.range (5 + C.gates.length)).filter (Live C)

open Classical in
noncomputable def liveGates (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => Live C (5 + j))

open Classical in
noncomputable def readers (C : Circuit) (a : ℕ) : Finset ℕ :=
  (living C).filter (fun j => LNext C a j)

noncomputable def outdeg (C : Circuit) (a : ℕ) : ℕ := (readers C a).card

open Classical in
noncomputable def inWires (C : Circuit) (j : ℕ) : Finset ℕ :=
  (living C).filter (fun a => LNext C a j)

noncomputable def inc (C : Circuit) (j : ℕ) : ℕ := (inWires C j).card

def Branch (C : Circuit) (a : ℕ) : Prop :=
  ∃ j₁ j₂ : ℕ, j₁ ≠ j₂ ∧ LNext C a j₁ ∧ LNext C a j₂

def isWide (C : Circuit) (w : ℕ) : Prop :=
  ∃ u v : Fin 5, u ≠ v ∧ val C (sing u) w = true ∧ val C (sing v) w = true

def isAndGate (C : Circuit) (w : ℕ) : Prop :=
  ∃ p g, C.gates[p]? = some g ∧ w = 5 + p ∧ g.op = GateOp.and

def isOrGate (C : Circuit) (w : ℕ) : Prop :=
  ∃ p g, C.gates[p]? = some g ∧ w = 5 + p ∧ g.op = GateOp.or

def isNarrowOr (C : Circuit) (w : ℕ) : Prop := isOrGate C w ∧ ¬ isWide C w

open Classical in
noncomputable def liveAnd (C : Circuit) : Finset ℕ :=
  (liveGates C).filter (fun j => isAndGate C (5 + j))

open Classical in
noncomputable def liveWideOr (C : Circuit) : Finset ℕ :=
  (liveGates C).filter (fun j => isOrGate C (5 + j) ∧ isWide C (5 + j))

open Classical in
noncomputable def liveNarrowOr (C : Circuit) : Finset ℕ :=
  (liveGates C).filter (fun j => isNarrowOr C (5 + j))


theorem mem_liveGates {C : Circuit} {j : ℕ} :
    j ∈ liveGates C ↔ j < C.gates.length ∧ Live C (5 + j) := by
  simp only [liveGates, Finset.mem_filter, Finset.mem_range]

theorem mem_liveAnd {C : Circuit} {j : ℕ} :
    j ∈ liveAnd C ↔ j ∈ liveGates C ∧ isAndGate C (5 + j) := by
  simp only [liveAnd, Finset.mem_filter]

theorem mem_liveWideOr {C : Circuit} {j : ℕ} :
    j ∈ liveWideOr C ↔ j ∈ liveGates C ∧ isOrGate C (5 + j) ∧ isWide C (5 + j) := by
  simp only [liveWideOr, Finset.mem_filter]

theorem mem_liveNarrowOr {C : Circuit} {j : ℕ} :
    j ∈ liveNarrowOr C ↔ j ∈ liveGates C ∧ isNarrowOr C (5 + j) := by
  simp only [liveNarrowOr, Finset.mem_filter]

theorem mem_living {C : Circuit} (hE : BowtieEval C) {w : ℕ} :
    w ∈ living C ↔ Live C w := by
  classical
  simp only [living, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro hw
  exact (live_le_output hw).trans_lt (output_bounds hE).2

theorem mem_readers {C : Circuit} (hE : BowtieEval C) {a j : ℕ} :
    j ∈ readers C a ↔ LNext C a j := by
  classical
  simp only [readers, Finset.mem_filter, mem_living hE, and_iff_right_iff_imp]
  exact fun h => h.2

theorem mem_inWires {C : Circuit} (hE : BowtieEval C) {a j : ℕ} :
    a ∈ inWires C j ↔ LNext C a j := by
  classical
  simp only [inWires, Finset.mem_filter, mem_living hE, and_iff_right_iff_imp]
  exact fun h => live_of_lnext h

theorem branch_iff_two_le_outdeg {C : Circuit} (hE : BowtieEval C) (a : ℕ) :
    Branch C a ↔ 2 ≤ outdeg C a := by
  unfold Branch outdeg
  rw [show (2 ≤ (readers C a).card) ↔ (1 < (readers C a).card) by omega, Finset.one_lt_card_iff]
  constructor
  · rintro ⟨j₁, j₂, hne, h1, h2⟩
    exact ⟨j₁, j₂, (mem_readers hE).mpr h1, (mem_readers hE).mpr h2, hne⟩
  · rintro ⟨j₁, j₂, h1, h2, hne⟩
    exact ⟨j₁, j₂, hne, (mem_readers hE).mp h1, (mem_readers hE).mp h2⟩

theorem live_ne_output_outdeg_pos {C : Circuit} (hE : BowtieEval C) {a : ℕ}
    (ha : Live C a) (hne : a ≠ C.output) : 1 ≤ outdeg C a := by
  rcases ha.cases_head with rfl | ⟨b, hab, hbo⟩
  · exact absurd rfl hne
  · exact Finset.card_pos.mpr ⟨b, (mem_readers hE).mpr ⟨hab, hbo⟩⟩

theorem outdeg_output {C : Circuit} (hE : BowtieEval C) : outdeg C C.output = 0 := by
  rw [outdeg, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hln := (mem_readers hE).mp hj
  have h1 := hln.1.1
  have h2 := live_le_output hln.2
  omega

theorem inc_input {C : Circuit} (hE : BowtieEval C) {j : ℕ} (hj : j < 5) : inc C j = 0 := by
  rw [inc, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro a ha
  obtain ⟨⟨_, p, g, _, hjp, _⟩, _⟩ := (mem_inWires hE).mp ha
  omega

theorem inc_le_two {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) (j : ℕ) :
    inc C j ≤ 2 := by
  classical
  by_cases hj : 5 ≤ j
  · by_cases hlt : j < 5 + C.gates.length
    · set p := j - 5
      have hjp : j = 5 + p := by omega
      have hp_lt : p < C.gates.length := by omega
      obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
      have hsub : inWires C j ⊆ g.inputs.toFinset := by
        intro a ha
        obtain ⟨⟨_, p', g', hg', hjp', hain⟩, _⟩ := (mem_inWires hE).mp ha
        have hp' : p' = p := by omega
        subst hp'
        rw [hg] at hg'
        cases hg'
        exact List.mem_toFinset.mpr hain
      calc inc C j ≤ g.inputs.toFinset.card := Finset.card_le_card hsub
        _ ≤ g.inputs.length := List.toFinset_card_le g.inputs
        _ ≤ 2 := (hC g (List.mem_of_getElem? hg)).2
    · rw [inc, Finset.card_eq_zero.mpr]
      · omega
      · rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        have := live_le_output ((mem_inWires hE).mp ha).2
        have := (output_bounds hE).2
        omega
  · rw [inc_input hE (by omega)]; omega

theorem cost_ge_live {C : Circuit} (hC : Monotone2 C)
    {A B D : Finset ℕ}
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (hB : ∀ j g, C.gates[j]? = some g → g.op = GateOp.or → isWide C (5 + j) → j ∈ B)
    (hD : ∀ j g, C.gates[j]? = some g → g.op = GateOp.or → ¬ isWide C (5 + j) → j ∈ D) :
    (liveGates C).card + (liveNarrowOr C).card ≤ A.card + B.card + 2 * D.card := by
  classical
  have hsubA : liveAnd C ⊆ A := by
    intro j hj
    simp only [mem_liveAnd, mem_liveGates, isAndGate] at hj
    obtain ⟨_, p, g, hg, hjp, hop⟩ := hj
    have hp : p = j := by omega
    subst p
    exact hA j g hg hop
  have hsubB : liveWideOr C ⊆ B := by
    intro j hj
    simp only [mem_liveWideOr, mem_liveGates, isOrGate] at hj
    obtain ⟨_, ⟨p, g, hg, hjp, hop⟩, hwide⟩ := hj
    have hp : p = j := by omega
    subst p
    exact hB j g hg hop hwide
  have hsubD : liveNarrowOr C ⊆ D := by
    intro j hj
    simp only [mem_liveNarrowOr, mem_liveGates, isNarrowOr, isOrGate] at hj
    obtain ⟨_, ⟨p, g, hg, hjp, hop⟩, hnw⟩ := hj
    have hp : p = j := by omega
    subst p
    exact hD j g hg hop hnw
  have hpart : liveGates C = (liveAnd C ∪ liveWideOr C) ∪ liveNarrowOr C := by
    ext j
    simp only [Finset.mem_union, mem_liveAnd, mem_liveWideOr, mem_liveNarrowOr, mem_liveGates,
      isAndGate, isOrGate, isNarrowOr]
    constructor
    · rintro ⟨hj, hlive⟩
      obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g := ⟨C.gates[j], List.getElem?_eq_getElem hj⟩
      rcases mono_op hC hg with hop | hop
      · exact Or.inl (Or.inl ⟨⟨hj, hlive⟩, j, g, hg, rfl, hop⟩)
      · by_cases hw : isWide C (5 + j)
        · exact Or.inl (Or.inr ⟨⟨hj, hlive⟩, ⟨j, g, hg, rfl, hop⟩, hw⟩)
        · exact Or.inr ⟨⟨hj, hlive⟩, ⟨j, g, hg, rfl, hop⟩, hw⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint (liveAnd C) (liveWideOr C) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [mem_liveAnd, mem_liveWideOr, isAndGate, isOrGate] at h1 h2
    obtain ⟨p1, g1, hg1, hjp1, hop1⟩ := h1.2
    obtain ⟨p2, g2, hg2, hjp2, hop2⟩ := h2.2.1
    have : p1 = p2 := by omega
    subst this; rw [hg1] at hg2; cases hg2; rw [hop1] at hop2; cases hop2
  have hd2 : Disjoint (liveAnd C ∪ liveWideOr C) (liveNarrowOr C) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_union, mem_liveAnd, mem_liveWideOr, mem_liveNarrowOr, isAndGate, isOrGate, isNarrowOr] at h1 h2
    rcases h1 with h1 | h1
    · obtain ⟨p1, g1, hg1, hjp1, hop1⟩ := h1.2
      obtain ⟨p2, g2, hg2, hjp2, hop2⟩ := h2.2.1
      have : p1 = p2 := by omega
      subst this; rw [hg1] at hg2; cases hg2; rw [hop1] at hop2; cases hop2
    · exact h2.2.2 h1.2.2
  have hcard : (liveGates C).card = (liveAnd C).card + (liveWideOr C).card + (liveNarrowOr C).card := by
    rw [hpart, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have h1 := Finset.card_le_card hsubA
  have h2 := Finset.card_le_card hsubB
  have h3 := Finset.card_le_card hsubD
  omega

theorem live_budget_exact {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) :
    (liveGates C).card =
      4 + (∑ a ∈ (living C).erase C.output, (outdeg C a - 1)) +
          (∑ j ∈ (living C).filter (fun w => 5 ≤ w), (2 - inc C j)) := by
  classical
  set W := living C
  set GW := W.filter (fun w => 5 ≤ w)
  set IN := W.filter (fun w => w < 5)
  have hIN : IN = Finset.range 5 := by
    ext a
    simp only [IN, W, Finset.mem_filter, mem_living hE, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro ha; exact ⟨input_live hE ⟨a, ha⟩, ha⟩
  have hGW_card : GW.card = (liveGates C).card := by
    refine Finset.card_bij (fun w _ => w - 5) ?_ ?_ ?_
    · intro w hw
      simp only [GW, W, Finset.mem_filter, mem_living hE] at hw
      simp only [liveGates, Finset.mem_filter, Finset.mem_range]
      have hlt := (live_le_output hw.1).trans_lt (output_bounds hE).2
      exact ⟨by omega, by rw [show 5 + (w - 5) = w by omega]; exact hw.1⟩
    · intro w₁ hw₁ w₂ hw₂ heq
      simp only [GW, Finset.mem_filter] at hw₁ hw₂
      omega
    · intro j hj
      simp only [liveGates, Finset.mem_filter, Finset.mem_range] at hj
      refine ⟨5 + j, ?_, by omega⟩
      simp only [GW, W, Finset.mem_filter, mem_living hE]
      exact ⟨hj.2, by omega⟩
  have hW_split : W.card = 5 + GW.card := by
    have hdisj : Disjoint IN GW := by
      rw [Finset.disjoint_left]; intro a h1 h2
      simp only [IN, GW, Finset.mem_filter] at h1 h2; omega
    have hunion : IN ∪ GW = W := by
      ext a; simp only [Finset.mem_union, IN, GW, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro ha; by_cases h : a < 5
        · exact Or.inl ⟨ha, h⟩
        · exact Or.inr ⟨ha, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hIN, Finset.card_range]
  have houtW : C.output ∈ W := (mem_living hE).mpr ReflTransGen.refl
  have hW_erase : (W.erase C.output).card = 4 + GW.card := by
    rw [Finset.card_erase_of_mem houtW, hW_split]; omega
  have hsum_out : (∑ a ∈ W, outdeg C a) = (∑ a ∈ W.erase C.output, outdeg C a) := by
    rw [← Finset.add_sum_erase W (outdeg C) houtW, outdeg_output hE, zero_add]
  have hsum_delta :
      (∑ a ∈ W.erase C.output, outdeg C a) =
        (W.erase C.output).card + ∑ a ∈ W.erase C.output, (outdeg C a - 1) := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨hne, haW⟩ := Finset.mem_erase.mp ha
    have hpos := live_ne_output_outdeg_pos hE ((mem_living hE).mp haW) hne
    omega
  have hcomm : (∑ a ∈ W, outdeg C a) = ∑ j ∈ W, inc C j := by
    simp only [outdeg, inc, readers, inWires, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsum_inc : (∑ j ∈ W, inc C j) = ∑ j ∈ GW, inc C j := by
    rw [show GW = W.filter (fun w => 5 ≤ w) from rfl, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · exact inc_input hE (by omega)
  have hsum_slack :
      (∑ j ∈ GW, inc C j) + (∑ j ∈ GW, (2 - inc C j)) = 2 * GW.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ j ∈ GW, (inc C j + (2 - inc C j))
        = ∑ _j ∈ GW, 2 := Finset.sum_congr rfl fun j _ => by have := inc_le_two hC hE j; omega
      _ = 2 * GW.card := by simp [Nat.mul_comm]
  rw [← hGW_card]
  omega

/-! ## Section 2B: Branch-free chain cut and Claim 1 (`chain_sing_subset`) -/

def Trace (C : Circuit) (P : ℕ → Prop) (a b : ℕ) : Prop :=
  ReflTransGen (fun u w => P u ∧ LNext C u w) a b

theorem trace_le {C : Circuit} {P : ℕ → Prop} {a b : ℕ} (h : Trace C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem trace_lnext_unique {C : Circuit} {a b₁ b₂ : ℕ}
    (hnb : ¬ Branch C a) (h1 : LNext C a b₁) (h2 : LNext C a b₂) : b₁ = b₂ := by
  by_contra hne
  exact hnb ⟨b₁, b₂, hne, h1, h2⟩

theorem trace_det_init {C : Circuit} {a t u w : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) a t)
    (hu : Trace C (fun z => ¬ Branch C z) a u)
    (hlt : u < t) (hln : LNext C u w) :
    Trace C (fun z => ¬ Branch C z) a w ∧ w ≤ t := by
  induction ht using ReflTransGen.head_induction_on with
  | refl =>
    have := trace_le hu
    omega
  | @head x y hxy hyt ih =>
    rcases hu.cases_head with rfl | ⟨y', hxy', hy'u⟩
    · have hy : w = y := trace_lnext_unique hxy.1 hln hxy.2
      subst hy
      exact ⟨ReflTransGen.single hxy, trace_le hyt⟩
    · have hy : y' = y := trace_lnext_unique hxy.1 hxy'.2 hxy.2
      subst hy
      obtain ⟨hw, hwt⟩ := ih hy'u
      exact ⟨ReflTransGen.head hxy hw, hwt⟩

theorem trace_strict_not_branch {C : Circuit} {a t u : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) a t)
    (hu : Trace C (fun z => ¬ Branch C z) a u)
    (hlt : u < t) : ¬ Branch C u := by
  induction ht using ReflTransGen.head_induction_on with
  | refl =>
    have := trace_le hu; omega
  | @head x y hxy hyt ih =>
    rcases hu.cases_head with rfl | ⟨y', hxy', hy'u⟩
    · exact hxy.1
    · have hy : y' = y := trace_lnext_unique hxy.1 hxy'.2 hxy.2
      subst hy
      exact ih hy'u

/-- Single-wire cut along a branch-free chain from `v.val` to `t`. -/
theorem no_bypass_mono {C : Circuit} (hC : Monotone2 C)
    {v : Fin 5} {t : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) v.val t)
    {x y : Fin 5 → Bool}
    (hag : ∀ i : Fin 5, i ≠ v → x i = true → y i = true)
    (hvt : val C x t = true → val C y t = true) :
    ∀ w, Live C w → (¬ (Trace C (fun z => ¬ Branch C z) v.val w ∧ w < t)) →
      val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlive hnotP hwx
    by_cases hwt : w = t
    · subst hwt; exact hvt hwx
    · by_cases hlt : w < 5
      · have hw : w = (⟨w, hlt⟩ : Fin 5).val := rfl
        rw [hw, val_input] at hwx ⊢
        apply hag ⟨w, hlt⟩ _ hwx
        intro heq
        have hvw : v.val = w := by simpa using congrArg Fin.val heq.symm
        subst hvw
        apply hnotP
        exact ⟨ReflTransGen.refl, lt_of_le_of_ne (trace_le ht) hwt⟩
      · by_cases hbd : w < 5 + C.gates.length
        · set p := w - 5
          have hw : w = 5 + p := by omega
          have hp_lt : p < C.gates.length := by omega
          obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
          have hstep : ∀ i ∈ g.inputs, i < 5 + p → val C x i = true → val C y i = true := by
            intro i hi hilt hvi
            have hln : LNext C i w := ⟨⟨by omega, p, g, hg, hw, hi⟩, hlive⟩
            apply ih i (by omega) (live_of_lnext hln) _ hvi
            rintro ⟨hiT, hilt_t⟩
            obtain ⟨hwT, hwt_le⟩ := trace_det_init ht hiT hilt_t hln
            exact hnotP ⟨hwT, lt_of_le_of_ne hwt_le hwt⟩
          rw [hw] at hwx ⊢
          rcases mono_op hC hg with hop | hop
          · rw [val_and y hg hop]
            rw [val_and x hg hop] at hwx
            intro i hi
            obtain ⟨hilt, hvi⟩ := hwx i hi
            exact ⟨hilt, hstep i hi hilt hvi⟩
          · rw [val_or y hg hop]
            rw [val_or x hg hop] at hwx
            obtain ⟨i, hi, hilt, hvi⟩ := hwx
            exact ⟨i, hi, hilt, hstep i hi hilt hvi⟩
        · rw [val_beyond C x (by omega)] at hwx; cases hwx

theorem no_bypass_output {C : Circuit} (hC : Monotone2 C)
    {v : Fin 5} {t : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) v.val t)
    (htlive : Live C t)
    {x y : Fin 5 → Bool}
    (hag : ∀ i : Fin 5, i ≠ v → x i = true → y i = true)
    (hvt : val C x t = true → val C y t = true) :
    val C x C.output = true → val C y C.output = true := by
  apply no_bypass_mono hC ht hag hvt C.output ReflTransGen.refl
  rintro ⟨_, hlt⟩
  have := live_le_output htlive
  omega

/-- Claim 1 (Zero-Wide-OR-on-Chain): every wire on a branch-free chain from `v` has `S(t) ⊆ {v}`. -/
theorem chain_sing_subset {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {v : Fin 5} {t : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) v.val t) (htlive : Live C t)
    {u : Fin 5} (hu : val C (sing u) t = true) : u = v := by
  by_contra huv
  by_cases hadj : bowtieAdj u v
  · have htrue : val C (pairIn u v) C.output = true := (bowtie_pair_iff hE u v).mpr hadj
    have hres := no_bypass_output hC ht htlive
      (x := pairIn u v) (y := sing u)
      (fun i hi hxi => by
        simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢
        exact hxi.resolve_right hi)
      (fun _ => hu) htrue
    rw [bowtie_sing hE u] at hres
    cases hres
  · obtain ⟨k, hvk, huk⟩ := bowtie_uniqN u v huv
    have htrue : val C (pairIn v k) C.output = true := (bowtie_pair_iff hE v k).mpr hvk
    have hy_t : val C (pairIn u k) t = true :=
      val_mono hC (x := sing u) (y := pairIn u k)
        (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) t hu
    have hres := no_bypass_output hC ht htlive
      (x := pairIn v k) (y := pairIn u k)
      (fun i hi hxi => by
        simp only [pairIn, decide_eq_true_eq] at hxi ⊢
        exact Or.inr (hxi.resolve_left hi))
      (fun _ => hy_t) htrue
    exact huk ((bowtie_pair_iff hE u k).mp hres)

theorem chain_not_wide {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {v : Fin 5} {t : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) v.val t) (htlive : Live C t) :
    ¬ isWide C t := by
  rintro ⟨u₁, u₂, hne, h1, h2⟩
  exact hne ((chain_sing_subset hC hE ht htlive h1).trans
    (chain_sing_subset hC hE ht htlive h2).symm)

/-- On a branch-free chain `v → ... → u → t`, any other input `h ≠ u` of `t` is not reachable from `v`. -/
theorem chain_other_not_reach {C : Circuit}
    {v : Fin 5} {u t h : ℕ}
    (hu : Trace C (fun z => ¬ Branch C z) v.val u)
    (hunb : ¬ Branch C u)
    (hut : LNext C u t)
    (hht : LNext C h t)
    (hhu : h ≠ u) :
    ¬ ReflTransGen (Next C) v.val h := by
  intro hreach
  have hht_lt : h < t := hht.1.1
  have hhlive : Live C h := live_of_lnext hht
  have htrace_h : Trace C (fun z => ¬ Branch C z) v.val h := by
    have ht : Trace C (fun z => ¬ Branch C z) v.val t := hu.tail ⟨hunb, hut⟩
    -- Prove by induction on `hreach` that every reachable wire `< t` from `v.val` lies on `ht`.
    suffices ∀ z, ReflTransGen (Next C) v.val z → Live C z → z < t →
        Trace C (fun z => ¬ Branch C z) v.val z by
      exact this h hreach hhlive hht_lt
    intro z hrz
    induction hrz with
    | refl => intro _ _; exact ReflTransGen.refl
    | @tail a b hra hab ih =>
      intro hblive hblt
      have halive : Live C a := live_of_lnext ⟨hab, hblive⟩
      have halt : a < t := hab.1.trans hblt
      have haT := ih halive halt
      exact (trace_det_init ht haT halt ⟨hab, hblive⟩).1
  have ht : Trace C (fun z => ¬ Branch C z) v.val t := hu.tail ⟨hunb, hut⟩
  -- Since `h < t` lies on `ht`, its unique successor `w` satisfies `w ≤ t`, and if `h < u` then `w ≤ u < t`, impossible!
  by_cases hlt : h < u
  · obtain ⟨_, hle⟩ := trace_det_init hu htrace_h hlt hht
    have := hht.1.1
    have := hut.1.1
    omega
  · have hgt : u < h := by omega
    obtain ⟨_, hle⟩ := trace_det_init htrace_h hu hgt hut
    omega

/-! ## Section 2C: Carries-eligible vertices and vertex-cover injection (`L_meta_614`) -/

def Carries (C : Circuit) (v : Fin 5) (w : ℕ) : Prop :=
  val C (sing v) w = true ∧ val C zeroIn w = false

theorem carries_step {C : Circuit} (hC : Monotone2 C) {v : Fin 5} {w : ℕ}
    (hw : Carries C v w) (hw_ge : 5 ≤ w) (hw_live : Live C w) (hE : BowtieEval C) :
    ∃ a, LNext C a w ∧ Carries C v a := by
  have hlt := (live_le_output hw_live).trans_lt (output_bounds hE).2
  set p := w - 5
  have hwp : w = 5 + p := by omega
  have hp_lt : p < C.gates.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
  rcases mono_op hC hg with hop | hop
  · -- AND gate: all inputs true on sing v, some input false on zeroIn
    have h1 := (val_and (sing v) hg hop).mp (hwp ▸ hw.1)
    have h0 : ¬ ∀ i ∈ g.inputs, i < 5 + p ∧ val C zeroIn i = true := by
      intro hall
      have := (val_and zeroIn hg hop).mpr hall
      rw [← hwp, hw.2] at this; cases this
    push Not at h0
    obtain ⟨a, ha, hbad⟩ := h0
    obtain ⟨halt, hva⟩ := h1 a ha
    have hza : val C zeroIn a = false := by
      cases hz : val C zeroIn a
      · rfl
      · exact absurd hz (hbad halt)
    exact ⟨a, ⟨⟨by omega, p, g, hg, hwp, ha⟩, hw_live⟩, hva, hza⟩
  · -- OR gate: some input true on sing v, all inputs false on zeroIn
    obtain ⟨a, ha, halt, hva⟩ := (val_or (sing v) hg hop).mp (hwp ▸ hw.1)
    have hza : val C zeroIn a = false := by
      cases hz : val C zeroIn a
      · rfl
      · have := (val_or zeroIn hg hop).mpr ⟨a, ha, halt, hz⟩
        rw [← hwp, hw.2] at this; cases this
    exact ⟨a, ⟨⟨by omega, p, g, hg, hwp, ha⟩, hw_live⟩, hva, hza⟩

theorem carries_trace {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) {v : Fin 5} :
    ∀ w, Live C w → Carries C v w → Trace C (Carries C v) v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlive hcw
    by_cases hlt : w < 5
    · have hweq : w = (⟨w, hlt⟩ : Fin 5).val := rfl
      have hv1 := hcw.1
      rw [hweq, val_input] at hv1
      simp only [sing, decide_eq_true_eq] at hv1
      have hvw : v.val = w := by simpa using congrArg Fin.val hv1.symm
      rw [hvw]
      exact ReflTransGen.refl
    · obtain ⟨a, hln, hca⟩ := carries_step hC hcw (by omega) hlive hE
      exact (ih a hln.1.1 (live_of_lnext hln) hca).tail ⟨hca, hln⟩

def Eligible (C : Circuit) (v : Fin 5) : Prop :=
  ∃ b, Live C b ∧ Carries C v b ∧ Branch C b

/-- If `v` is NOT eligible, every Carries-wire has `¬ Branch`, so `Trace (Carries v)` implies `Trace (¬ Branch)`. -/
theorem not_eligible_not_branch {C : Circuit} {v : Fin 5} (hne : ¬ Eligible C v)
    {w : ℕ} (hlive : Live C w) (hcw : Carries C v w) : ¬ Branch C w :=
  fun hb => hne ⟨w, hlive, hcw, hb⟩

theorem trace_carries_to_not_branch {C : Circuit} {v : Fin 5} {w : ℕ}
    (ht : Trace C (Carries C v) v.val w)
    (hnb : ∀ z, z < w → Live C z → Carries C v z → ¬ Branch C z) :
    Trace C (fun z => ¬ Branch C z) v.val w := by
  induction ht with
  | refl => exact ReflTransGen.refl
  | @tail a b hta hab ih =>
    have halive := live_of_lnext hab.2
    have hba := hab.2.1.1
    exact (ih (fun z hz => hnb z (hz.trans hba))).tail ⟨hnb a hba halive hab.1, hab.2⟩

open Classical in
/-- Minimal branching wire carrying `v` when `Eligible C v`. -/
noncomputable def firstBranch (C : Circuit) (v : Fin 5) (hv : Eligible C v) : ℕ :=
  Nat.find hv

theorem firstBranch_spec {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {v : Fin 5} (hv : Eligible C v) :
    Live C (firstBranch C v hv) ∧ Carries C v (firstBranch C v hv) ∧
      Branch C (firstBranch C v hv) ∧
      Trace C (fun z => ¬ Branch C z) v.val (firstBranch C v hv) := by
  classical
  have hs := Nat.find_spec hv
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  apply trace_carries_to_not_branch (carries_trace hC hE _ hs.1 hs.2.1)
  intro z hz hzl hzc hzb
  exact Nat.find_min hv hz ⟨hzl, hzc, hzb⟩

theorem firstBranch_injective {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {u v : Fin 5} (hu : Eligible C u) (hv : Eligible C v)
    (heq : firstBranch C u hu = firstBranch C v hv) : u = v := by
  have su := firstBranch_spec hC hE hu
  have sv := firstBranch_spec hC hE hv
  rw [heq] at su
  exact chain_sing_subset hC hE sv.2.2.2 sv.1 su.2.1.1

/-- For any edge `(u, v)` of the bowtie, at least one of `u, v` is `Eligible`. -/
theorem eligible_covers_edge {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {u v : Fin 5} (huv : bowtieAdj u v) : Eligible C u ∨ Eligible C v := by
  classical
  by_contra hbad
  push Not at hbad
  obtain ⟨hnu, hnv⟩ := hbad
  -- Minimal live wire `m` with `val C (pairIn u v) m = true` and `val C (sing u) m = false` and `val C (sing v) m = false`
  have hex : ∃ m, Live C m ∧ val C (pairIn u v) m = true ∧
      val C (sing u) m = false ∧ val C (sing v) m = false :=
    ⟨C.output, ReflTransGen.refl, (bowtie_pair_iff hE u v).mpr huv,
      bowtie_sing hE u, bowtie_sing hE v⟩
  set m := Nat.find hex with hm_def
  have hm : Live C m ∧ val C (pairIn u v) m = true ∧
      val C (sing u) m = false ∧ val C (sing v) m = false := Nat.find_spec hex
  have hm_ge : 5 ≤ m := by
    by_contra hlt
    push Not at hlt
    have hmeq : m = (⟨m, hlt⟩ : Fin 5).val := rfl
    have h1 := hm.2.1
    rw [hmeq, val_input] at h1
    simp only [pairIn, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · have h2 := hm.2.2.1; rw [hmeq, val_input] at h2; simp [sing, h1] at h2
    · have h2 := hm.2.2.2; rw [hmeq, val_input] at h2; simp [sing, h1] at h2
  have hm_lt := (live_le_output hm.1).trans_lt (output_bounds hE).2
  set p := m - 5
  have hmp : m = 5 + p := by omega
  have hp_lt : p < C.gates.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
  have hAnd : g.op = GateOp.and := by
    rcases mono_op hC hg with hop | hop
    · exact hop
    · obtain ⟨a, ha, halt, hva⟩ := (val_or (pairIn u v) hg hop).mp (hmp ▸ hm.2.1)
      have hln : LNext C a m := ⟨⟨by omega, p, g, hg, hmp, ha⟩, hm.1⟩
      have hsu : val C (sing u) a = false := by
        cases h : val C (sing u) a
        · rfl
        · have := (val_or (sing u) hg hop).mpr ⟨a, ha, halt, h⟩
          rw [← hmp, hm.2.2.1] at this; cases this
      have hsv : val C (sing v) a = false := by
        cases h : val C (sing v) a
        · rfl
        · have := (val_or (sing v) hg hop).mpr ⟨a, ha, halt, h⟩
          rw [← hmp, hm.2.2.2] at this; cases this
      exact absurd ⟨live_of_lnext hln, hva, hsu, hsv⟩ (Nat.find_min hex (by omega))
  -- At AND gate `m`: all inputs are true on `pairIn u v`, some `a` is false on `sing v`, some `b` is false on `sing u`.
  have hall := (val_and (pairIn u v) hg hAnd).mp (hmp ▸ hm.2.1)
  have hna : ¬ ∀ i ∈ g.inputs, i < 5 + p ∧ val C (sing v) i = true := by
    intro h; have := (val_and (sing v) hg hAnd).mpr h; rw [← hmp, hm.2.2.2] at this; cases this
  push Not at hna
  obtain ⟨a, ha, ha_bad⟩ := hna
  obtain ⟨halt, hap⟩ := hall a ha
  have hav : val C (sing v) a = false := by
    cases h : val C (sing v) a
    · rfl
    · exact absurd h (ha_bad halt)
  have hnb : ¬ ∀ i ∈ g.inputs, i < 5 + p ∧ val C (sing u) i = true := by
    intro h; have := (val_and (sing u) hg hAnd).mpr h; rw [← hmp, hm.2.2.1] at this; cases this
  push Not at hnb
  obtain ⟨b, hb, hb_bad⟩ := hnb
  obtain ⟨hblt, hbp⟩ := hall b hb
  have hbu : val C (sing u) b = false := by
    cases h : val C (sing u) b
    · rfl
    · exact absurd h (hb_bad hblt)
  have hln_a : LNext C a m := ⟨⟨by omega, p, g, hg, hmp, ha⟩, hm.1⟩
  have hln_b : LNext C b m := ⟨⟨by omega, p, g, hg, hmp, hb⟩, hm.1⟩
  -- By minimality of `m`, `a` must be true on `sing u` and `b` must be true on `sing v`!
  have hau : val C (sing u) a = true := by
    cases h : val C (sing u) a
    · exact absurd ⟨live_of_lnext hln_a, hap, h, hav⟩ (Nat.find_min hex (by omega))
    · rfl
  have hbv : val C (sing v) b = true := by
    cases h : val C (sing v) b
    · exact absurd ⟨live_of_lnext hln_b, hbp, hbu, h⟩ (Nat.find_min hex (by omega))
    · rfl
  have haz : val C zeroIn a = false := by
    cases h : val C zeroIn a
    · rfl
    · have := val_mono hC (x := zeroIn) (y := sing v) (fun i hi => by simp [zeroIn] at hi) a h
      rw [hav] at this; cases this
  have hbz : val C zeroIn b = false := by
    cases h : val C zeroIn b
    · rfl
    · have := val_mono hC (x := zeroIn) (y := sing u) (fun i hi => by simp [zeroIn] at hi) b h
      rw [hbu] at this; cases this
  have hab_ne : a ≠ b := by intro e; subst e; rw [hau] at hbu; cases hbu
  -- Both `a` and `b` are reached by branch-free chains from `u` and `v`, ending at `m`!
  have hTa : Trace C (fun z => ¬ Branch C z) u.val a :=
    trace_carries_to_not_branch (carries_trace hC hE a (live_of_lnext hln_a) ⟨hau, haz⟩)
      (fun z _ => not_eligible_not_branch hnu)
  have hTb : Trace C (fun z => ¬ Branch C z) v.val b :=
    trace_carries_to_not_branch (carries_trace hC hE b (live_of_lnext hln_b) ⟨hbv, hbz⟩)
      (fun z _ => not_eligible_not_branch hnv)
  have hanb : ¬ Branch C a := not_eligible_not_branch hnu (live_of_lnext hln_a) ⟨hau, haz⟩
  have hbnb : ¬ Branch C b := not_eligible_not_branch hnv (live_of_lnext hln_b) ⟨hbv, hbz⟩
  have hTum : Trace C (fun z => ¬ Branch C z) u.val m := hTa.tail ⟨hanb, hln_a⟩
  have hTvm : Trace C (fun z => ¬ Branch C z) v.val m := hTb.tail ⟨hbnb, hln_b⟩
  -- Pick the triangle mate `w` of edge `(u, v)`: `bowtieAdj u w` and `bowtieAdj v w`!
  obtain ⟨w, hwu, hwv, huw, hvw⟩ := bowtie_tri_mate u v huv
  -- `b` does not depend on `u`, and `a` does not depend on `v`!
  have hb_nr : ¬ ReflTransGen (Next C) u.val b :=
    chain_other_not_reach hTa hanb hln_a hln_b hab_ne.symm
  have ha_nr : ¬ ReflTransGen (Next C) v.val a :=
    chain_other_not_reach hTb hbnb hln_b hln_a hab_ne
  -- Compare `pairIn u w` vs `sing w`: since `b` doesn't depend on `u`, `b(pairIn u w) = b(sing w)`.
  -- By Claim 1 on `b` (on `v`'s chain), since `w ≠ v`, `b(sing w) = false`!
  have hbw : val C (sing w) b = false := by
    cases h : val C (sing w) b
    · rfl
    · exact absurd (chain_sing_subset hC hE hTb (live_of_lnext hln_b) h) hwv
  have hbuw : val C (pairIn u w) b = false := by
    rw [← hbw]
    exact eval_eq_of_no_reach (v := u) (x := pairIn u w) (y := sing w)
      (fun i hi => by simp only [pairIn, sing]; by_cases hiw : i = w <;> simp [hi, hiw]) b hb_nr
  have hmuw : val C (pairIn u w) m = false := by
    rw [Bool.eq_false_iff]
    intro hmt
    have := ((val_and (pairIn u w) hg hAnd).mp (hmp ▸ hmt) b hb).2
    rw [hbuw] at this; cases this
  have hres := no_bypass_output hC hTum hm.1
    (x := pairIn u w) (y := sing w)
    (fun i hi hxi => by
      simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢
      exact hxi.resolve_left hi)
    (fun h => by rw [hmuw] at h; cases h)
    ((bowtie_pair_iff hE u w).mpr huw)
  rw [bowtie_sing hE w] at hres
  cases hres

/-! ## Section 3: `3 ≤ liveAnd.card`, `3 ≤ O_0.card`, and `8 ≤ liveGates.card` -/

def clauseVal (T : Finset (Fin 5)) (x : Fin 5 → Bool) : Bool :=
  decide (∃ i ∈ T, x i = true)

theorem clauseVal_empty (x : Fin 5 → Bool) : clauseVal ∅ x = false := by
  simp [clauseVal]

theorem clauseVal_singleton (i : Fin 5) (x : Fin 5 → Bool) :
    clauseVal {i} x = x i := by
  simp [clauseVal]

theorem clauseVal_union (T₁ T₂ : Finset (Fin 5)) (x : Fin 5 → Bool) :
    (clauseVal T₁ x || clauseVal T₂ x) = clauseVal (T₁ ∪ T₂) x := by
  by_cases h1 : ∃ i ∈ T₁, x i = true <;> by_cases h2 : ∃ i ∈ T₂, x i = true <;>
    simp [clauseVal, h1, h2, or_and_right, exists_or]

/-- No bowtie function equals an AND of two clauses `clauseVal S₁ && clauseVal S₂`. -/
theorem bowtie_ne_and_clauses (S₁ S₂ : Finset (Fin 5)) :
    ¬ (∀ x : Fin 5 → Bool,
        (clauseVal S₁ x && clauseVal S₂ x) = true ↔
          ∃ u v : Fin 5, bowtieAdj u v ∧ x u = true ∧ x v = true) := by
  intro h
  have hge : ∀ S : Finset (Fin 5), (∀ x, (∃ u v, bowtieAdj u v ∧ x u = true ∧ x v = true) → clauseVal S x = true) →
      ∀ u v, bowtieAdj u v → u ∈ S ∨ v ∈ S := by
    intro S hS u v huv
    have h1 := hS (pairIn u v) ⟨u, v, huv, by simp [pairIn], by simp [pairIn]⟩
    simp only [clauseVal, pairIn, decide_eq_true_eq] at h1
    obtain ⟨i, hi, hiuv⟩ := h1
    rcases hiuv with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  have hS1 : ∀ u v, bowtieAdj u v → u ∈ S₁ ∨ v ∈ S₁ :=
    hge S₁ (fun x hx => (Bool.and_eq_true _ _ |>.mp ((h x).mpr hx)).1)
  have hS2 : ∀ u v, bowtieAdj u v → u ∈ S₂ ∨ v ∈ S₂ :=
    hge S₂ (fun x hx => (Bool.and_eq_true _ _ |>.mp ((h x).mpr hx)).2)
  have h0 : ¬ ((clauseVal S₁ (sing 0) && clauseVal S₂ (sing 0)) = true) := by
    rw [h (sing 0)]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [sing, decide_eq_true_eq] at hu hv
    subst hu hv; exact bowtieAdj_irrefl _ huv
  have h0' : (0 : Fin 5) ∉ S₁ ∨ (0 : Fin 5) ∉ S₂ := by
    by_contra hc; push Not at hc
    exact h0 (by simp [clauseVal, sing, hc.1, hc.2])
  -- WLOG `0 ∉ S` for one of S₁, S₂
  suffices aux : ∀ A B : Finset (Fin 5),
      (∀ x, (clauseVal A x && clauseVal B x) = true ↔ ∃ u v, bowtieAdj u v ∧ x u = true ∧ x v = true) →
      (∀ u v, bowtieAdj u v → u ∈ A ∨ v ∈ A) → (0 : Fin 5) ∉ A → False by
    rcases h0' with h01 | h02
    · exact aux S₁ S₂ h hS1 h01
    · exact aux S₂ S₁ (fun x => by rw [Bool.and_comm]; exact h x) hS2 h02
  intro A B hAB hAv h0A
  have hA1 : (1 : Fin 5) ∈ A := (hAv 0 1 (by decide)).resolve_left h0A
  have hA2 : (2 : Fin 5) ∈ A := (hAv 0 2 (by decide)).resolve_left h0A
  have hA3 : (3 : Fin 5) ∈ A := (hAv 0 3 (by decide)).resolve_left h0A
  have hA4 : (4 : Fin 5) ∈ A := (hAv 0 4 (by decide)).resolve_left h0A
  have hno_pair : ∀ a b : Fin 5, ¬ bowtieAdj a b → a ∈ A → a ∉ B ∧ b ∉ B := by
    intro a b hnab haA
    have hfalse : ¬ ((clauseVal A (pairIn a b) && clauseVal B (pairIn a b)) = true) := by
      rw [hAB]
      rintro ⟨u, v, huv, hu, hv⟩
      simp only [pairIn, decide_eq_true_eq] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact bowtieAdj_irrefl _ huv
      · exact hnab huv
      · exact hnab (bowtieAdj_symm huv)
      · exact bowtieAdj_irrefl _ huv
    have hAt : clauseVal A (pairIn a b) = true := by
      simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨a, haA, Or.inl rfl⟩
    constructor
    · intro haB
      apply hfalse
      rw [Bool.and_eq_true]
      exact ⟨hAt, by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨a, haB, Or.inl rfl⟩⟩
    · intro hbB
      apply hfalse
      rw [Bool.and_eq_true]
      exact ⟨hAt, by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨b, hbB, Or.inr rfl⟩⟩
  have hb1 : (1 : Fin 5) ∉ B := (hno_pair 1 3 (by decide) hA1).1
  have hb2 : (2 : Fin 5) ∉ B := (hno_pair 2 3 (by decide) hA2).1
  have h12 : (clauseVal A (pairIn 1 2) && clauseVal B (pairIn 1 2)) = true :=
    (hAB (pairIn 1 2)).mpr ⟨1, 2, by decide, by simp [pairIn], by simp [pairIn]⟩
  have hB12 := (Bool.and_eq_true _ _ |>.mp h12).2
  simp only [clauseVal, pairIn, decide_eq_true_eq] at hB12
  obtain ⟨i, hiB, hi12⟩ := hB12
  rcases hi12 with rfl | rfl
  · exact hb1 hiB
  · exact hb2 hiB

/-- No bowtie function equals `(clauseVal S₁ && clauseVal S₂) || (clauseVal T₁ && clauseVal T₂)`
    (handles both `g₁ ∨ g₂` and `(g₁ ∨ C_T₁) ∧ (g₁ ∨ C_T₂)`!). -/
theorem bowtie_ne_or_two_and (S₁ S₂ T₁ T₂ : Finset (Fin 5)) :
    ¬ (∀ x : Fin 5 → Bool,
        ((clauseVal S₁ x && clauseVal S₂ x) || (clauseVal T₁ x && clauseVal T₂ x)) = true ↔
          ∃ u v : Fin 5, bowtieAdj u v ∧ x u = true ∧ x v = true) := by
  intro h
  -- First, `(clauseVal S₁ && clauseVal S₂)` is false on all singletons, so `S₁ ∩ S₂ = ∅`,
  -- and every `(a, b) ∈ S₁ × S₂` is an edge of the bowtie!
  have hS_edge : ∀ a ∈ S₁, ∀ b ∈ S₂, bowtieAdj a b := by
    intro a ha b hb
    have h1 : ((clauseVal S₁ (pairIn a b) && clauseVal S₂ (pairIn a b)) ||
        (clauseVal T₁ (pairIn a b) && clauseVal T₂ (pairIn a b))) = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq]
      exact Or.inl ⟨⟨a, ha, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩
    obtain ⟨u, v, huv, hu, hv⟩ := (h (pairIn a b)).mp h1
    simp only [pairIn, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd huv (bowtieAdj_irrefl _)
    · exact huv
    · exact bowtieAdj_symm huv
    · exact absurd huv (bowtieAdj_irrefl _)
  -- Since the bowtie is C4-free, `S₁.card ≤ 1 ∨ S₂.card ≤ 1`!
  have hnoC4 : ∀ a₁ a₂ b₁ b₂ : Fin 5, a₁ ≠ a₂ → b₁ ≠ b₂ →
      bowtieAdj a₁ b₁ → bowtieAdj a₁ b₂ → bowtieAdj a₂ b₁ → ¬ bowtieAdj a₂ b₂ := by
    decide
  have hstar : ∃ v : Fin 5, ∀ x, (clauseVal S₁ x && clauseVal S₂ x) = true → x v = true := by
    by_cases h1 : S₁.card ≤ 1
    · by_cases he : S₁.Nonempty
      · obtain ⟨v, hv⟩ := he
        refine ⟨v, fun x hx => ?_⟩
        have h1' := (Bool.and_eq_true _ _ |>.mp hx).1
        simp only [clauseVal, decide_eq_true_eq] at h1'
        obtain ⟨a, ha, hxa⟩ := h1'
        have hav : a = v := Finset.card_le_one.mp h1 a ha v hv
        rwa [← hav]
      · refine ⟨0, fun x hx => ?_⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp he, clauseVal_empty] at hx
        simp at hx
    · push Not at h1
      obtain ⟨a₁, ha₁, a₂, ha₂, ha12⟩ := Finset.one_lt_card.mp h1
      have h2 : S₂.card ≤ 1 := by
        by_contra h2; push Not at h2
        obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.one_lt_card.mp h2
        exact hnoC4 a₁ a₂ b₁ b₂ ha12 hb12
          (hS_edge a₁ ha₁ b₁ hb₁) (hS_edge a₁ ha₁ b₂ hb₂)
          (hS_edge a₂ ha₂ b₁ hb₁) (hS_edge a₂ ha₂ b₂ hb₂)
      by_cases he : S₂.Nonempty
      · obtain ⟨v, hv⟩ := he
        refine ⟨v, fun x hx => ?_⟩
        have h2' := (Bool.and_eq_true _ _ |>.mp hx).2
        simp only [clauseVal, decide_eq_true_eq] at h2'
        obtain ⟨b, hb, hxb⟩ := h2'
        have hbv : b = v := Finset.card_le_one.mp h2 b hb v hv
        rwa [← hbv]
      · refine ⟨0, fun x hx => ?_⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp he, clauseVal_empty] at hx
        simp at hx
  obtain ⟨v, hv⟩ := hstar
  -- Restrict to inputs with `x v = false`: `(clauseVal T₁ && clauseVal T₂)` must equal `G - v`!
  have hT_edge : ∀ a b : Fin 5, a ≠ v → b ≠ v →
      ((clauseVal T₁ (pairIn a b) && clauseVal T₂ (pairIn a b)) = true ↔ bowtieAdj a b) := by
    intro a b hav hbv
    have hS0 : (clauseVal S₁ (pairIn a b) && clauseVal S₂ (pairIn a b)) = false := by
      cases hs : (clauseVal S₁ (pairIn a b) && clauseVal S₂ (pairIn a b))
      · rfl
      · have := hv (pairIn a b) hs
        simp only [pairIn, decide_eq_true_eq] at this
        rcases this with rfl | rfl
        · exact absurd rfl hav
        · exact absurd rfl hbv
    have hiff := h (pairIn a b)
    rw [hS0, Bool.false_or] at hiff
    rw [hiff]
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      simp only [pairIn, decide_eq_true_eq] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd hxy (bowtieAdj_irrefl _)
      · exact hxy
      · exact bowtieAdj_symm hxy
      · exact absurd hxy (bowtieAdj_irrefl _)
    · intro hab; exact ⟨a, b, hab, by simp [pairIn], by simp [pairIn]⟩
  have hT_sing : ∀ a : Fin 5, a ≠ v →
      (clauseVal T₁ (sing a) && clauseVal T₂ (sing a)) = false := by
    intro a _
    rw [Bool.eq_false_iff]
    intro ht
    have := (h (sing a)).mp (by simp [ht])
    obtain ⟨x, y, hxy, hx, hy⟩ := this
    simp only [sing, decide_eq_true_eq] at hx hy
    subst hx hy; exact bowtieAdj_irrefl _ hxy
  -- Case split on `v : Fin 5`:
  -- If `v = 0`: G - 0 = {12, 34} (2K2) is not complete bipartite!
  -- If `v ∈ {1,2,3,4}`: G - v contains a triangle ({0,3,4} or {0,1,2}), not bipartite!
  have no_tri : ∀ a b c : Fin 5, a ≠ v → b ≠ v → c ≠ v →
      bowtieAdj a b → bowtieAdj a c → bowtieAdj b c → False := by
    intro a b c hav hbv hcv hab hac hbc
    have h1 := (hT_edge a b hav hbv).mpr hab
    have h2 := (hT_edge a c hav hcv).mpr hac
    have h3 := (hT_edge b c hbv hcv).mpr hbc
    have hsA := hT_sing a hav
    have hsB := hT_sing b hbv
    have hsC := hT_sing c hcv
    -- Each of a, b, c can belong to AT MOST one of T₁, T₂, yet every pair hits BOTH T₁ and T₂!
    have hna : ¬ (a ∈ T₁ ∧ a ∈ T₂) := fun ⟨h1, h2⟩ => by
      have : (clauseVal T₁ (sing a) && clauseVal T₂ (sing a)) = true := by
        simp [clauseVal, sing, h1, h2]
      rw [hsA] at this; cases this
    have hnb : ¬ (b ∈ T₁ ∧ b ∈ T₂) := fun ⟨h1, h2⟩ => by
      have : (clauseVal T₁ (sing b) && clauseVal T₂ (sing b)) = true := by
        simp [clauseVal, sing, h1, h2]
      rw [hsB] at this; cases this
    have hnc : ¬ (c ∈ T₁ ∧ c ∈ T₂) := fun ⟨h1, h2⟩ => by
      have : (clauseVal T₁ (sing c) && clauseVal T₂ (sing c)) = true := by
        simp [clauseVal, sing, h1, h2]
      rw [hsC] at this; cases this
    have ext_pair : ∀ x y : Fin 5,
        (clauseVal T₁ (pairIn x y) && clauseVal T₂ (pairIn x y)) = true →
        (x ∈ T₁ ∨ y ∈ T₁) ∧ (x ∈ T₂ ∨ y ∈ T₂) := by
      intro x y hxy
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hxy
      simp only [clauseVal, pairIn, decide_eq_true_eq] at h1 h2
      obtain ⟨i, hi1, hixy⟩ := h1
      obtain ⟨j, hj2, hjxy⟩ := h2
      exact ⟨hixy.elim (fun e => Or.inl (e ▸ hi1)) (fun e => Or.inr (e ▸ hi1)), hjxy.elim (fun e => Or.inl (e ▸ hj2)) (fun e => Or.inr (e ▸ hj2))⟩
    obtain ⟨hab1, hab2⟩ := ext_pair a b h1
    obtain ⟨hac1, hac2⟩ := ext_pair a c h2
    obtain ⟨hbc1, hbc2⟩ := ext_pair b c h3
    by_cases ha1 : a ∈ T₁ <;> by_cases hb1 : b ∈ T₁ <;> by_cases hc1 : c ∈ T₁
    · exact hna ⟨ha1, hab2.elim id (fun hb2 => absurd ⟨hb1, hb2⟩ hnb)⟩
    · have ha2 : a ∉ T₂ := fun h => hna ⟨ha1, h⟩
      have hb2 : b ∉ T₂ := fun h => hnb ⟨hb1, h⟩
      exact hab2.elim ha2 hb2
    · have ha2 : a ∉ T₂ := fun h => hna ⟨ha1, h⟩
      have hc2 : c ∉ T₂ := fun h => hnc ⟨hc1, h⟩
      exact hac2.elim ha2 hc2
    · exact hbc1.elim hb1 hc1
    · have hb2 : b ∉ T₂ := fun h => hnb ⟨hb1, h⟩
      have hc2 : c ∉ T₂ := fun h => hnc ⟨hc1, h⟩
      exact hbc2.elim hb2 hc2
    · exact hac1.elim ha1 hc1
    · exact hab1.elim ha1 hb1
    · exact hab1.elim ha1 hb1
  fin_cases v
  · -- v = 0: G - 0 has edges 12, 34 and non-edges 13, 14, 23, 24
    have e12 := (hT_edge 1 2 (by decide) (by decide)).mpr (by decide)
    have e34 := (hT_edge 3 4 (by decide) (by decide)).mpr (by decide)
    have ext_pair : ∀ x y : Fin 5,
        (clauseVal T₁ (pairIn x y) && clauseVal T₂ (pairIn x y)) = true →
        (x ∈ T₁ ∨ y ∈ T₁) ∧ (x ∈ T₂ ∨ y ∈ T₂) := by
      intro x y hxy
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hxy
      simp only [clauseVal, pairIn, decide_eq_true_eq] at h1 h2
      obtain ⟨i, hi1, hixy⟩ := h1
      obtain ⟨j, hj2, hjxy⟩ := h2
      exact ⟨hixy.elim (fun e => Or.inl (e ▸ hi1)) (fun e => Or.inr (e ▸ hi1)), hjxy.elim (fun e => Or.inl (e ▸ hj2)) (fun e => Or.inr (e ▸ hj2))⟩
    obtain ⟨h12_1, _⟩ := ext_pair 1 2 e12
    obtain ⟨_, h34_2⟩ := ext_pair 3 4 e34
    rcases h12_1 with h1 | h2 <;> rcases h34_2 with h3 | h4
    · have : (clauseVal T₁ (pairIn 1 3) && clauseVal T₂ (pairIn 1 3)) = true := by
        simp only [Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq]
        exact ⟨⟨1, h1, Or.inl rfl⟩, ⟨3, h3, Or.inr rfl⟩⟩
      exact absurd ((hT_edge 1 3 (by decide) (by decide)).mp this) (by decide)
    · have : (clauseVal T₁ (pairIn 1 4) && clauseVal T₂ (pairIn 1 4)) = true := by
        simp only [Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq]
        exact ⟨⟨1, h1, Or.inl rfl⟩, ⟨4, h4, Or.inr rfl⟩⟩
      exact absurd ((hT_edge 1 4 (by decide) (by decide)).mp this) (by decide)
    · have : (clauseVal T₁ (pairIn 2 3) && clauseVal T₂ (pairIn 2 3)) = true := by
        simp only [Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq]
        exact ⟨⟨2, h2, Or.inl rfl⟩, ⟨3, h3, Or.inr rfl⟩⟩
      exact absurd ((hT_edge 2 3 (by decide) (by decide)).mp this) (by decide)
    · have : (clauseVal T₁ (pairIn 2 4) && clauseVal T₂ (pairIn 2 4)) = true := by
        simp only [Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq]
        exact ⟨⟨2, h2, Or.inl rfl⟩, ⟨4, h4, Or.inr rfl⟩⟩
      exact absurd ((hT_edge 2 4 (by decide) (by decide)).mp this) (by decide)
  · exact no_tri 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact no_tri 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact no_tri 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact no_tri 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Every `Monotone2` circuit computing the bowtie has at least 3 live `AND` gates. -/
theorem three_and_gates {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) :
    3 ≤ (liveAnd C).card := by
  classical
  -- Helper: any live wire `w` with no live AND gates `< w` (or `≤ w`) has form `const true` or `clauseVal T`.
  have no_and_form : ∀ bound, (∀ j ∈ liveAnd C, bound ≤ 5 + j) →
      ∀ w, Live C w → w < bound →
        (∀ x, val C x w = true) ∨ ∃ T : Finset (Fin 5), ∀ x, val C x w = clauseVal T x := by
    intro bound hbd w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hlive hwlt
      by_cases hlt : w < 5
      · right; refine ⟨{⟨w, hlt⟩}, fun x => ?_⟩
        change val C x (⟨w, hlt⟩ : Fin 5).val = _; rw [val_input, clauseVal_singleton]
      · set p := w - 5
        have hwp : w = 5 + p := by omega
        have hp_lt : p < C.gates.length := by
          have := (live_le_output hlive).trans_lt (output_bounds hE).2; omega
        obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
        have hor : g.op = GateOp.or := by
          rcases mono_op hC hg with hop | hop
          · have hp_mem : p ∈ liveAnd C := by
              simp only [mem_liveAnd, mem_liveGates, isAndGate]
              exact ⟨⟨hp_lt, hwp ▸ hlive⟩, p, g, hg, rfl, hop⟩
            have := hbd p hp_mem; omega
          · exact hop
        -- Prove for any sublist `L ⊆ g.inputs`, `L.any (operand C · w)` is either const true or `clauseVal T`!
        have hsub : ∀ L : List ℕ, (∀ i ∈ L, i ∈ g.inputs) →
            (∀ x, L.any (operand C x (5 + p)) = true) ∨
              ∃ T : Finset (Fin 5), ∀ x, L.any (operand C x (5 + p)) = clauseVal T x := by
          intro L
          induction L with
          | nil => intro _; right; exact ⟨∅, fun x => by simp [clauseVal_empty]⟩
          | cons i rest ihL =>
            intro hmem
            have hrest := ihL (fun k hk => hmem k (List.mem_cons_of_mem i hk))
            have hi_form : (∀ x, operand C x (5 + p) i = true) ∨
                ∃ T : Finset (Fin 5), ∀ x, operand C x (5 + p) i = clauseVal T x := by
              by_cases hilt : i < 5 + p
              · have hln : LNext C i w := ⟨⟨by omega, p, g, hg, hwp, hmem i List.mem_cons_self⟩, hlive⟩
                rcases ih i (by omega) (live_of_lnext hln) (by omega) with ht | ⟨T, hT⟩
                · left; intro x; simp [operand, hilt, ht x]
                · right; exact ⟨T, fun x => by simp [operand, hilt, hT x]⟩
              · right; exact ⟨∅, fun x => by simp [operand, hilt, clauseVal_empty]⟩
            rcases hi_form with h1 | ⟨T₁, hT₁⟩
            · left; intro x; simp [h1 x]
            · rcases hrest with h2 | ⟨T₂, hT₂⟩
              · left; intro x; simp [h2 x]
              · right; exact ⟨T₁ ∪ T₂, fun x => by simp [hT₁ x, hT₂ x, clauseVal_union]⟩
        rcases hsub g.inputs (fun _ h => h) with ht | ⟨T, hT⟩
        · left; intro x; rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using ht x
        · right; exact ⟨T, fun x => by rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using hT x⟩
  -- Helper: given a single function `f`, any wire with no live AND gates in `[a, bound)` is in the OR-closure of `{f} ∪ clauses` (or const true).
  have or_closure_form : ∀ (f : (Fin 5 → Bool) → Bool) (a bound : ℕ),
      (∀ w, Live C w → w < a → (∀ x, val C x w = true) ∨
        ∃ T : Finset (Fin 5), (∀ x, val C x w = clauseVal T x) ∨ (∀ x, val C x w = (f x || clauseVal T x))) →
      (∀ j ∈ liveAnd C, 5 + j < a ∨ bound ≤ 5 + j) →
      ∀ w, Live C w → w < bound →
        (∀ x, val C x w = true) ∨
        ∃ T : Finset (Fin 5), (∀ x, val C x w = clauseVal T x) ∨ (∀ x, val C x w = (f x || clauseVal T x)) := by
    intro f a bound hbase hno w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hlive hwlt
      by_cases hwa : w < a
      · exact hbase w hlive hwa
      · by_cases hlt : w < 5
        · right; refine ⟨{⟨w, hlt⟩}, Or.inl fun x => ?_⟩
          change val C x (⟨w, hlt⟩ : Fin 5).val = _; rw [val_input, clauseVal_singleton]
        · set p := w - 5
          have hwp : w = 5 + p := by omega
          have hp_lt : p < C.gates.length := by
            have := (live_le_output hlive).trans_lt (output_bounds hE).2; omega
          obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
          have hor : g.op = GateOp.or := by
            rcases mono_op hC hg with hop | hop
            · have hp_mem : p ∈ liveAnd C := by
                simp only [mem_liveAnd, mem_liveGates, isAndGate]
                exact ⟨⟨hp_lt, hwp ▸ hlive⟩, p, g, hg, rfl, hop⟩
              rcases hno p hp_mem with h1 | h2 <;> omega
            · exact hop
          have hsub : ∀ L : List ℕ, (∀ i ∈ L, i ∈ g.inputs) →
              (∀ x, L.any (operand C x (5 + p)) = true) ∨
              ∃ T : Finset (Fin 5), (∀ x, L.any (operand C x (5 + p)) = clauseVal T x) ∨
                (∀ x, L.any (operand C x (5 + p)) = (f x || clauseVal T x)) := by
            intro L
            induction L with
            | nil => intro _; right; exact ⟨∅, Or.inl fun x => by simp [clauseVal_empty]⟩
            | cons i rest ihL =>
              intro hmem
              have hrest := ihL (fun k hk => hmem k (List.mem_cons_of_mem i hk))
              have hi_form : (∀ x, operand C x (5 + p) i = true) ∨
                  ∃ T : Finset (Fin 5), (∀ x, operand C x (5 + p) i = clauseVal T x) ∨
                    (∀ x, operand C x (5 + p) i = (f x || clauseVal T x)) := by
                by_cases hilt : i < 5 + p
                · have hln : LNext C i w := ⟨⟨by omega, p, g, hg, hwp, hmem i List.mem_cons_self⟩, hlive⟩
                  rcases ih i (by omega) (live_of_lnext hln) (by omega) with ht | ⟨T, hT | hT⟩
                  · left; intro x; simp [operand, hilt, ht x]
                  · right; exact ⟨T, Or.inl fun x => by simp [operand, hilt, hT x]⟩
                  · right; exact ⟨T, Or.inr fun x => by simp [operand, hilt, hT x]⟩
                · right; exact ⟨∅, Or.inl fun x => by simp [operand, hilt, clauseVal_empty]⟩
              rcases hi_form with h1 | ⟨T₁, h1 | h1⟩
              · left; intro x; simp [h1 x]
              · rcases hrest with h2 | ⟨T₂, h2 | h2⟩
                · left; intro x; simp [h2 x]
                · right; exact ⟨T₁ ∪ T₂, Or.inl fun x => by simp [h1 x, h2 x, clauseVal_union]⟩
                · right; refine ⟨T₁ ∪ T₂, Or.inr fun x => ?_⟩
                  simp only [List.any_cons, h1 x, h2 x]
                  rw [← clauseVal_union T₁ T₂ x]
                  cases f x <;> cases clauseVal T₁ x <;> cases clauseVal T₂ x <;> rfl
              · rcases hrest with h2 | ⟨T₂, h2 | h2⟩
                · left; intro x; simp [h2 x]
                · right; refine ⟨T₁ ∪ T₂, Or.inr fun x => ?_⟩
                  simp only [List.any_cons, h1 x, h2 x]
                  rw [← clauseVal_union T₁ T₂ x]
                  cases f x <;> cases clauseVal T₁ x <;> cases clauseVal T₂ x <;> rfl
                · right; refine ⟨T₁ ∪ T₂, Or.inr fun x => ?_⟩
                  simp only [List.any_cons, h1 x, h2 x]
                  rw [← clauseVal_union T₁ T₂ x]
                  cases f x <;> cases clauseVal T₁ x <;> cases clauseVal T₂ x <;> rfl
          rcases hsub g.inputs (fun _ h => h) with ht | ⟨T, hT | hT⟩
          · left; intro x; rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using ht x
          · right; exact ⟨T, Or.inl fun x => by rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using hT x⟩
          · right; exact ⟨T, Or.inr fun x => by rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using hT x⟩
  -- Helper: bowtie cannot equal `const true` or `clauseVal T`.
  have ne_true : ¬ ∀ x, val C x C.output = true := fun h => by
    have := h zeroIn; rw [bowtie_zero hE] at this; cases this
  have ne_clause : ∀ T : Finset (Fin 5), ¬ ∀ x, val C x C.output = clauseVal T x := by
    intro T hT
    by_cases he : T.Nonempty
    · obtain ⟨u, hu⟩ := he
      have := hT (sing u)
      rw [bowtie_sing hE u] at this
      have hc : clauseVal T (sing u) = true := by simp [clauseVal, sing, hu]
      rw [hc] at this; cases this
    · rw [Finset.not_nonempty_iff_eq_empty.mp he] at hT
      have := hT (pairIn 0 1)
      rw [(bowtie_pair_iff hE 0 1).mpr (by decide), clauseVal_empty] at this; cases this
  -- Helper: for any AND gate `w = 5 + j`, its value is an AND of at most 2 operands (each `< w` or `false`).
  have and_operands : ∀ j, j ∈ liveAnd C →
      (∀ x, val C x (5 + j) = true) ∨
      (∃ a, LNext C a (5 + j) ∧ ∀ x, val C x (5 + j) = val C x a) ∨
      (∃ a b, LNext C a (5 + j) ∧ LNext C b (5 + j) ∧ ∀ x, val C x (5 + j) = (val C x a && val C x b)) ∨
      (∀ x, val C x (5 + j) = false) := by
    intro j hj
    simp only [mem_liveAnd, mem_liveGates, isAndGate] at hj
    obtain ⟨⟨_, hlive⟩, p, g, hg, hjp, hop⟩ := hj
    have hp : p = j := by omega
    subst p
    have hlen : g.inputs.length ≤ 2 := (hC g (List.mem_of_getElem? hg)).2
    rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · left; intro x; rw [val_gate C x hg, hop, hgi]; rfl
    · by_cases ha : a < 5 + j
      · right; left; refine ⟨a, ⟨⟨ha, j, g, hg, rfl, by rw [hgi]; simp⟩, hlive⟩, fun x => ?_⟩
        rw [val_gate C x hg, hop, hgi]; simp [GateOp.eval, operand, ha]
      · right; right; right; intro x; rw [val_gate C x hg, hop, hgi]; simp [GateOp.eval, operand, ha]
    · by_cases ha : a < 5 + j <;> by_cases hb : b < 5 + j
      · right; right; left
        refine ⟨a, b, ⟨⟨ha, j, g, hg, rfl, by rw [hgi]; simp⟩, hlive⟩,
          ⟨⟨hb, j, g, hg, rfl, by rw [hgi]; simp⟩, hlive⟩, fun x => ?_⟩
        rw [val_gate C x hg, hop, hgi]; simp [GateOp.eval, operand, ha, hb]
      · right; right; right; intro x; rw [val_gate C x hg, hop, hgi]; simp [GateOp.eval, operand, ha, hb]
      · right; right; right; intro x; rw [val_gate C x hg, hop, hgi]; simp [GateOp.eval, operand, ha, hb]
      · right; right; right; intro x; rw [val_gate C x hg, hop, hgi]; simp [GateOp.eval, operand, ha, hb]
    · simp [hgi] at hlen
  -- Helper: if `val C · C.output = (f || clauseVal T)` then `T = ∅`!
  have or_clause_eq_empty : ∀ (f : (Fin 5 → Bool) → Bool) (T : Finset (Fin 5)),
      (∀ x, val C x C.output = (f x || clauseVal T x)) → ∀ x, val C x C.output = f x := by
    intro f T hT
    have hTe : T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      have := hT (sing u)
      rw [bowtie_sing hE u] at this
      have hc : clauseVal T (sing u) = true := by simp [clauseVal, sing, hu]
      rw [hc, Bool.or_true] at this; cases this
    intro x; rw [hT x, hTe, clauseVal_empty, Bool.or_false]
  -- Helper: given a single AND gate `f = clauseVal S₁ && clauseVal S₂`, rule out `val C · C.output` in OR-closure of `{f} ∪ clauses`.
  have rule_out_1and : ∀ (S₁ S₂ : Finset (Fin 5)),
      ¬ ((∀ x, val C x C.output = true) ∨
        ∃ T : Finset (Fin 5), (∀ x, val C x C.output = clauseVal T x) ∨
          (∀ x, val C x C.output = ((clauseVal S₁ x && clauseVal S₂ x) || clauseVal T x))) := by
    intro S₁ S₂ h
    rcases h with ht | ⟨T, hT | hT⟩
    · exact ne_true ht
    · exact ne_clause T hT
    · have hf := or_clause_eq_empty _ T hT
      exact bowtie_ne_and_clauses S₁ S₂ (fun x => by rw [← hf x, val_output, bowtieEval_adj hE])
  -- Now assume `(liveAnd C).card ≤ 2` and derive a contradiction!
  by_contra hlt
  push Not at hlt
  have hle : (liveAnd C).card ≤ 2 := by omega
  -- Helper: classify a wire `w = 5 + j` whose operands are all `const true` or `clauseVal T`.
  have and_of_clauses : ∀ j, j ∈ liveAnd C →
      (∀ a, LNext C a (5 + j) → (∀ x, val C x a = true) ∨ ∃ T, ∀ x, val C x a = clauseVal T x) →
      (∀ x, val C x (5 + j) = true) ∨
      ∃ S₁ S₂ : Finset (Fin 5), ∀ x, val C x (5 + j) = (clauseVal S₁ x && clauseVal S₂ x) := by
    intro j hj hop
    rcases and_operands j hj with ht | ⟨a, hln, ha⟩ | ⟨a, b, hlna, hlnb, hab⟩ | hf
    · exact Or.inl ht
    · rcases hop a hln with h1 | ⟨T, hT⟩
      · exact Or.inl (fun x => by rw [ha x, h1 x])
      · exact Or.inr ⟨T, T, fun x => by rw [ha x, hT x, Bool.and_self]⟩
    · rcases hop a hlna with h1 | ⟨T₁, hT₁⟩ <;> rcases hop b hlnb with h2 | ⟨T₂, hT₂⟩
      · exact Or.inl (fun x => by rw [hab x, h1 x, h2 x]; rfl)
      · exact Or.inr ⟨T₂, T₂, fun x => by rw [hab x, h1 x, hT₂ x, Bool.true_and, Bool.and_self]⟩
      · exact Or.inr ⟨T₁, T₁, fun x => by rw [hab x, hT₁ x, h2 x, Bool.and_true, Bool.and_self]⟩
      · exact Or.inr ⟨T₁, T₂, fun x => by rw [hab x, hT₁ x, hT₂ x]⟩
    · exact Or.inr ⟨∅, ∅, fun x => by rw [hf x, clauseVal_empty]; rfl⟩
  -- Split by `(liveAnd C).card ∈ {0, 1, 2}`:
  rcases Nat.le_iff_lt_or_eq.mp hle with hlt2 | hcard2
  · rcases Nat.lt_succ_iff.mp hlt2 |> Nat.le_iff_lt_or_eq.mp with hlt1 | hcard1
    · -- Card = 0
      have hemp : liveAnd C = ∅ := Finset.card_eq_zero.mp (by omega)
      rcases no_and_form (C.output + 1) (fun j hj => by rw [hemp] at hj; simp at hj)
          C.output ReflTransGen.refl (by omega) with ht | ⟨T, hT⟩
      · exact ne_true ht
      · exact ne_clause T hT
    · -- Card = 1
      obtain ⟨j₁, hj₁eq⟩ := Finset.card_eq_one.mp hcard1
      have hj₁ : j₁ ∈ liveAnd C := by rw [hj₁eq]; simp
      have hbelow := no_and_form (5 + j₁) (fun j hj => by rw [hj₁eq, Finset.mem_singleton] at hj; omega)
      have hj₁_form := and_of_clauses j₁ hj₁ (fun a hln => hbelow a (live_of_lnext hln) hln.1.1)
      rcases hj₁_form with ht | ⟨S₁, S₂, hS⟩
      · -- `5 + j₁` is `const true`, so everything is `const true` or `clauseVal T`!
        have hall := or_closure_form (fun _ => false) (5 + j₁ + 1) (C.output + 1)
          (fun w hwl hwlt => by
            by_cases heq : w = 5 + j₁
            · subst heq; exact Or.inl ht
            · rcases hbelow w hwl (by omega) with h1 | ⟨T, hT⟩
              · exact Or.inl h1
              · exact Or.inr ⟨T, Or.inl hT⟩)
          (fun j hj => by rw [hj₁eq, Finset.mem_singleton] at hj; left; omega)
          C.output ReflTransGen.refl (by omega)
        rcases hall with h1 | ⟨T, hT | hT⟩
        · exact ne_true h1
        · exact ne_clause T hT
        · exact ne_clause T (fun x => by simpa using hT x)
      · -- `5 + j₁ = clauseVal S₁ && clauseVal S₂`
        apply rule_out_1and S₁ S₂
        exact or_closure_form (fun x => clauseVal S₁ x && clauseVal S₂ x) (5 + j₁ + 1) (C.output + 1)
          (fun w hwl hwlt => by
            by_cases heq : w = 5 + j₁
            · subst heq; exact Or.inr ⟨∅, Or.inr fun x => by simp [hS x, clauseVal_empty]⟩
            · rcases hbelow w hwl (by omega) with h1 | ⟨T, hT⟩
              · exact Or.inl h1
              · exact Or.inr ⟨T, Or.inl hT⟩)
          (fun j hj => by rw [hj₁eq, Finset.mem_singleton] at hj; left; omega)
          C.output ReflTransGen.refl (by omega)
  · -- Card = 2: `liveAnd C = {j₁, j₂}` with `j₁ < j₂`
    obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hcard2
    obtain ⟨j₁, j₂, hj12, heq2⟩ : ∃ j₁ j₂, j₁ < j₂ ∧ liveAnd C = {j₁, j₂} := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, h, hpair⟩
      · exact ⟨b, a, h, by rw [hpair, Finset.pair_comm]⟩
    have hj₁ : j₁ ∈ liveAnd C := by rw [heq2]; simp
    have hj₂ : j₂ ∈ liveAnd C := by rw [heq2]; simp
    have hbelow1 := no_and_form (5 + j₁) (fun j hj => by
      rw [heq2, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> omega)
    rcases and_of_clauses j₁ hj₁ (fun a hln => hbelow1 a (live_of_lnext hln) hln.1.1) with ht1 | ⟨S₁, S₂, hS⟩
    · -- `5 + j₁` is `const true`, so everything `< 5 + j₂` is `const true` or `clauseVal T`!
      have hbelow2 : ∀ w, Live C w → w < 5 + j₂ →
          (∀ x, val C x w = true) ∨ ∃ T, ∀ x, val C x w = clauseVal T x := by
        intro w hwl hwlt
        have h := or_closure_form (fun _ => false) (5 + j₁ + 1) (5 + j₂)
          (fun u hul hult => by
            by_cases heq : u = 5 + j₁
            · subst heq; exact Or.inl ht1
            · rcases hbelow1 u hul (by omega) with h1 | ⟨T, hT⟩
              · exact Or.inl h1
              · exact Or.inr ⟨T, Or.inl hT⟩)
          (fun j hj => by
            rw [heq2, Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · left; omega
            · right; omega)
          w hwl hwlt
        rcases h with h1 | ⟨T, hT | hT⟩
        · exact Or.inl h1
        · exact Or.inr ⟨T, hT⟩
        · exact Or.inr ⟨T, fun x => by simpa using hT x⟩
      rcases and_of_clauses j₂ hj₂ (fun a hln => hbelow2 a (live_of_lnext hln) hln.1.1) with ht2 | ⟨T₁, T₂, hT⟩
      · have hall := or_closure_form (fun _ => false) (5 + j₂ + 1) (C.output + 1)
          (fun w hwl hwlt => by
            by_cases heq : w = 5 + j₂
            · subst heq; exact Or.inl ht2
            · rcases hbelow2 w hwl (by omega) with h1 | ⟨T, hT⟩
              · exact Or.inl h1
              · exact Or.inr ⟨T, Or.inl hT⟩)
          (fun j hj => by
            rw [heq2, Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl <;> left <;> omega)
          C.output ReflTransGen.refl (by omega)
        rcases hall with h1 | ⟨T, hT | hT⟩
        · exact ne_true h1
        · exact ne_clause T hT
        · exact ne_clause T (fun x => by simpa using hT x)
      · apply rule_out_1and T₁ T₂
        exact or_closure_form (fun x => clauseVal T₁ x && clauseVal T₂ x) (5 + j₂ + 1) (C.output + 1)
          (fun w hwl hwlt => by
            by_cases heq : w = 5 + j₂
            · subst heq; exact Or.inr ⟨∅, Or.inr fun x => by simp [hT x, clauseVal_empty]⟩
            · rcases hbelow2 w hwl (by omega) with h1 | ⟨T, hT⟩
              · exact Or.inl h1
              · exact Or.inr ⟨T, Or.inl hT⟩)
          (fun j hj => by
            rw [heq2, Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl <;> left <;> omega)
          C.output ReflTransGen.refl (by omega)
    · -- Main 2-AND case: `f₁ := val (5 + j₁) = clauseVal S₁ && clauseVal S₂`.
      let f₁ : (Fin 5 → Bool) → Bool := fun x => clauseVal S₁ x && clauseVal S₂ x
      have hbelow2 : ∀ w, Live C w → w < 5 + j₂ →
          (∀ x, val C x w = true) ∨
          ∃ T : Finset (Fin 5), (∀ x, val C x w = clauseVal T x) ∨ (∀ x, val C x w = (f₁ x || clauseVal T x)) :=
        or_closure_form f₁ (5 + j₁ + 1) (5 + j₂)
          (fun u hul hult => by
            by_cases heq : u = 5 + j₁
            · subst heq; exact Or.inr ⟨∅, Or.inr fun x => by simp [f₁, hS x, clauseVal_empty]⟩
            · rcases hbelow1 u hul (by omega) with h1 | ⟨T, hT⟩
              · exact Or.inl h1
              · exact Or.inr ⟨T, Or.inl hT⟩)
          (fun j hj => by
            rw [heq2, Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · left; omega
            · right; omega)
      -- Let `f₂ := val (5 + j₂)`. Every wire `≤ C.output` is in OR-closure of `{f₁, f₂} ∪ clauses`!
      -- Even simpler: every wire `w` with `Live C w` is either `const true` or
      -- `(b₁ && f₁) || (b₂ && f₂) || clauseVal T` for some `b₁ b₂ : Bool` and `T`!
      let f₂ : (Fin 5 → Bool) → Bool := fun x => val C x (5 + j₂)
      have hall : ∀ w, Live C w → w ≤ C.output →
          (∀ x, val C x w = true) ∨
          ∃ (b₁ b₂ : Bool) (T : Finset (Fin 5)),
            ∀ x, val C x w = (((b₁ && f₁ x) || (b₂ && f₂ x)) || clauseVal T x) := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwl hwle
          by_cases hlt2 : w < 5 + j₂
          · rcases hbelow2 w hwl hlt2 with ht | ⟨T, hT | hT⟩
            · exact Or.inl ht
            · exact Or.inr ⟨false, false, T, fun x => by simp [hT x]⟩
            · exact Or.inr ⟨true, false, T, fun x => by simp [hT x]⟩
          · by_cases heq2w : w = 5 + j₂
            · subst heq2w
              exact Or.inr ⟨false, true, ∅, fun x => by simp [f₂, clauseVal_empty]⟩
            · set p := w - 5
              have hwp : w = 5 + p := by omega
              have hp_lt : p < C.gates.length := by
                have := hwle.trans_lt (output_bounds hE).2; omega
              obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
              have hor : g.op = GateOp.or := by
                rcases mono_op hC hg with hop | hop
                · have hp_mem : p ∈ liveAnd C := by
                    simp only [mem_liveAnd, mem_liveGates, isAndGate]
                    exact ⟨⟨hp_lt, hwp ▸ hwl⟩, p, g, hg, rfl, hop⟩
                  rw [heq2, Finset.mem_insert, Finset.mem_singleton] at hp_mem
                  rcases hp_mem with rfl | rfl <;> omega
                · exact hop
              have hsub : ∀ L : List ℕ, (∀ i ∈ L, i ∈ g.inputs) →
                  (∀ x, L.any (operand C x (5 + p)) = true) ∨
                  ∃ (b₁ b₂ : Bool) (T : Finset (Fin 5)),
                    ∀ x, L.any (operand C x (5 + p)) = (((b₁ && f₁ x) || (b₂ && f₂ x)) || clauseVal T x) := by
                intro L
                induction L with
                | nil => intro _; right; exact ⟨false, false, ∅, fun x => by simp [clauseVal_empty]⟩
                | cons i rest ihL =>
                  intro hmem
                  have hrest := ihL (fun k hk => hmem k (List.mem_cons_of_mem i hk))
                  have hi_form : (∀ x, operand C x (5 + p) i = true) ∨
                      ∃ (b₁ b₂ : Bool) (T : Finset (Fin 5)),
                        ∀ x, operand C x (5 + p) i = (((b₁ && f₁ x) || (b₂ && f₂ x)) || clauseVal T x) := by
                    by_cases hilt : i < 5 + p
                    · have hln : LNext C i w := ⟨⟨by omega, p, g, hg, hwp, hmem i List.mem_cons_self⟩, hwl⟩
                      rcases ih i (by omega) (live_of_lnext hln) (by omega) with ht | ⟨b1, b2, T, hT⟩
                      · left; intro x; simp [operand, hilt, ht x]
                      · right; exact ⟨b1, b2, T, fun x => by simp [operand, hilt, hT x]⟩
                    · right; exact ⟨false, false, ∅, fun x => by simp [operand, hilt, clauseVal_empty]⟩
                  rcases hi_form with h1 | ⟨a1, a2, T1, h1⟩
                  · left; intro x; simp [h1 x]
                  · rcases hrest with h2 | ⟨c1, c2, T2, h2⟩
                    · left; intro x; simp [h2 x]
                    · right
                      refine ⟨a1 || c1, a2 || c2, T1 ∪ T2, fun x => ?_⟩
                      simp only [List.any_cons, h1 x, h2 x]
                      rw [← clauseVal_union T1 T2 x]
                      cases a1 <;> cases a2 <;> cases c1 <;> cases c2 <;>
                        cases f₁ x <;> cases f₂ x <;> cases clauseVal T1 x <;> cases clauseVal T2 x <;> rfl
              rcases hsub g.inputs (fun _ h => h) with ht | ⟨b1, b2, T, hT⟩
              · left; intro x; rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using ht x
              · right; exact ⟨b1, b2, T, fun x => by rw [hwp, val_gate C x hg, hor]; simpa [GateOp.eval, List.any_map] using hT x⟩
      -- Apply `hall` to `C.output`!
      rcases hall C.output ReflTransGen.refl le_rfl with ht | ⟨b₁, b₂, T, hout⟩
      · exact ne_true ht
      · have hout' := or_clause_eq_empty _ T hout
        -- Note `b₂` must be `true` (else we're in the 1-AND case!)
        cases b₂
        · cases b₁
          · have := hout' (pairIn 0 1); rw [(bowtie_pair_iff hE 0 1).mpr (by decide)] at this; simp at this
          · exact bowtie_ne_and_clauses S₁ S₂ (fun x => by
              have hx := hout' x; simp only [f₁, Bool.true_and, Bool.false_and, Bool.or_false] at hx
              rw [← hx, val_output, bowtieEval_adj hE])
        · -- Now `val C x C.output = (b₁ && f₁ x) || f₂ x`, where `f₂` is AND of ≤ 2 operands from `hbelow2`!
          -- Show `f₂` is either `const true`, `const false`, `clauseVal U && clauseVal V`,
          -- `f₁ || (clauseVal U && clauseVal V)`, or `(f₁ || clauseVal U) && clauseVal V`!
          have kill_pair : ∀ (U V : Finset (Fin 5)),
              ¬ (∀ x, val C x C.output = (f₁ x || (clauseVal U x && clauseVal V x))) :=
            fun U V h => bowtie_ne_or_two_and S₁ S₂ U V (fun x => by rw [← h x, val_output, bowtieEval_adj hE])
          have kill_mix : ∀ (U V : Finset (Fin 5)),
              ¬ (∀ x, val C x C.output = ((f₁ x || clauseVal U x) && clauseVal V x)) := by
            intro U V h
            have heval : ∀ x, ((f₁ x || clauseVal U x) && clauseVal V x) = true ↔
                ∃ u v, bowtieAdj u v ∧ x u = true ∧ x v = true :=
              fun x => by rw [← h x, val_output, bowtieEval_adj hE]
            -- Check whether `0 ∈ V`:
            by_cases h0V : (0 : Fin 5) ∈ V
            · -- `V` is a vertex cover containing 0, so `V` hits `{1,2}` and `{3,4}`!
              have hV_vc : ∀ u v, bowtieAdj u v → u ∈ V ∨ v ∈ V := by
                intro u v huv
                have h1 := (Bool.and_eq_true _ _ |>.mp ((heval (pairIn u v)).mpr ⟨u, v, huv, by simp [pairIn], by simp [pairIn]⟩)).2
                simp only [clauseVal, pairIn, decide_eq_true_eq] at h1
                obtain ⟨i, hiV, hiuv⟩ := h1
                rcases hiuv with rfl | rfl
                · exact Or.inl hiV
                · exact Or.inr hiV
              have h12 : (1 : Fin 5) ∈ V ∨ (2 : Fin 5) ∈ V := hV_vc 1 2 (by decide)
              have h34 : (3 : Fin 5) ∈ V ∨ (4 : Fin 5) ∈ V := hV_vc 3 4 (by decide)
              -- Pick `a ∈ {1,2} ∩ V`, `a'` the other, `c ∈ {3,4} ∩ V`, `c'` the other!
              -- On `sing 0`, `pairIn a c`, `pairIn a c'`, `pairIn a' c`: `V` is TRUE, while bowtie is FALSE!
              -- So `f₁ || clauseVal U` must be FALSE on ALL FOUR, forcing `U = ∅`!
              have hU0 : (0 : Fin 5) ∉ U := by
                intro h0U
                have : ((f₁ (sing 0) || clauseVal U (sing 0)) && clauseVal V (sing 0)) = true := by
                  simp [clauseVal, sing, h0U, h0V]
                obtain ⟨u, v, huv, hu, hv⟩ := (heval (sing 0)).mp this
                simp only [sing, decide_eq_true_eq] at hu hv; rw [hu, hv] at huv; exact bowtieAdj_irrefl 0 huv
              have kill_pair_U : ∀ x y : Fin 5, ¬ bowtieAdj x y → x ∈ V → x ∉ U ∧ y ∉ U := by
                intro x y hnab hxV
                have hf : ¬ (((f₁ (pairIn x y) || clauseVal U (pairIn x y)) && clauseVal V (pairIn x y)) = true) := by
                  rw [heval]
                  rintro ⟨u, v, huv, hu, hv⟩
                  simp only [pairIn, decide_eq_true_eq] at hu hv
                  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
                  · exact bowtieAdj_irrefl _ huv
                  · exact hnab huv
                  · exact hnab (bowtieAdj_symm huv)
                  · exact bowtieAdj_irrefl _ huv
                have hVt : clauseVal V (pairIn x y) = true := by
                  simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hxV, Or.inl rfl⟩
                constructor
                · intro hxU; apply hf
                  rw [Bool.and_eq_true, Bool.or_eq_true]
                  exact ⟨Or.inr (by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hxU, Or.inl rfl⟩), hVt⟩
                · intro hyU; apply hf
                  rw [Bool.and_eq_true, Bool.or_eq_true]
                  exact ⟨Or.inr (by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨y, hyU, Or.inr rfl⟩), hVt⟩
              have hU_empty : U = ∅ := by
                rw [Finset.eq_empty_iff_forall_notMem]
                intro i hiU
                rcases h12 with h1V | h2V <;> rcases h34 with h3V | h4V <;> fin_cases i
                all_goals first
                  | exact hU0 hiU
                  | exact (kill_pair_U 1 3 (by decide) h1V).1 hiU
                  | exact (kill_pair_U 1 3 (by decide) h1V).2 hiU
                  | exact (kill_pair_U 1 4 (by decide) h1V).2 hiU
                  | exact (kill_pair_U 3 2 (by decide) h3V).2 hiU
                  | exact (kill_pair_U 4 2 (by decide) h4V).2 hiU
                  | exact (kill_pair_U 2 3 (by decide) h2V).1 hiU
                  | exact (kill_pair_U 2 3 (by decide) h2V).2 hiU
                  | exact (kill_pair_U 2 4 (by decide) h2V).2 hiU
                  | exact (kill_pair_U 3 1 (by decide) h3V).2 hiU
                  | exact (kill_pair_U 4 1 (by decide) h4V).2 hiU
              -- Now `f₁ && clauseVal V = bowtie`! Since `f₁(0) = false`, one of `S₁, S₂` misses `0`, so is `{1,2,3,4}`!
              rw [hU_empty] at heval
              have hS_vc : ∀ u v, bowtieAdj u v → (u ∈ S₁ ∨ v ∈ S₁) ∧ (u ∈ S₂ ∨ v ∈ S₂) := by
                intro u v huv
                have ht := (heval (pairIn u v)).mpr ⟨u, v, huv, by simp [pairIn], by simp [pairIn]⟩
                rw [clauseVal_empty, Bool.or_false, Bool.and_eq_true] at ht
                have hf1t := ht.1
                simp only [f₁, Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq] at hf1t
                obtain ⟨⟨i, hi1, hiuv⟩, ⟨j, hj2, hjuv⟩⟩ := hf1t
                exact ⟨hiuv.elim (fun e => Or.inl (e ▸ hi1)) (fun e => Or.inr (e ▸ hi1)), hjuv.elim (fun e => Or.inl (e ▸ hj2)) (fun e => Or.inr (e ▸ hj2))⟩
              have hf1_0 : f₁ (sing 0) = false := by
                cases hf0 : f₁ (sing 0)
                · rfl
                · have : ((f₁ (sing 0) || clauseVal ∅ (sing 0)) && clauseVal V (sing 0)) = true := by
                    simp [hf0, clauseVal, sing, h0V]
                  obtain ⟨u, v, huv, hu, hv⟩ := (heval (sing 0)).mp this
                  simp only [sing, decide_eq_true_eq] at hu hv; rw [hu, hv] at huv; exact False.elim (bowtieAdj_irrefl 0 huv)
              have h0S : (0 : Fin 5) ∉ S₁ ∨ (0 : Fin 5) ∉ S₂ := by
                by_contra hc; push Not at hc
                have : f₁ (sing 0) = true := by simp [f₁, clauseVal, sing, hc.1, hc.2]
                rw [hf1_0] at this; cases this
              -- WLOG `0 ∉ A` where `f₁ = clauseVal A && clauseVal B`
              suffices aux2 : ∀ A B : Finset (Fin 5),
                  (∀ x, (clauseVal A x && clauseVal B x && clauseVal V x) = true ↔
                    ∃ u v, bowtieAdj u v ∧ x u = true ∧ x v = true) →
                  (∀ u v, bowtieAdj u v → u ∈ A ∨ v ∈ A) → (0 : Fin 5) ∉ A → False by
                rcases h0S with h01 | h02
                · exact aux2 S₁ S₂ (fun x => by simpa [f₁, clauseVal_empty] using heval x)
                    (fun u v huv => (hS_vc u v huv).1) h01
                · exact aux2 S₂ S₁ (fun x => by
                    rw [Bool.and_comm (clauseVal S₂ x) (clauseVal S₁ x)]
                    simpa [f₁, clauseVal_empty] using heval x)
                    (fun u v huv => (hS_vc u v huv).2) h02
              intro A B hABV hAv h0A
              have hA_all : ∀ k : Fin 5, k ≠ 0 → k ∈ A := by
                intro k hk; fin_cases k
                · exact absurd rfl hk
                · exact (hAv 0 1 (by decide)).resolve_left h0A
                · exact (hAv 0 2 (by decide)).resolve_left h0A
                · exact (hAv 0 3 (by decide)).resolve_left h0A
                · exact (hAv 0 4 (by decide)).resolve_left h0A
              -- Every non-edge `(x, y)` with `x ∈ V` has `x ∈ A` (since `x ≠ 0`), so `B` must miss BOTH `x` and `y`!
              have hnoB : ∀ x y : Fin 5, x ≠ 0 → ¬ bowtieAdj x y → x ∈ V → x ∉ B ∧ y ∉ B := by
                intro x y hx0 hnab hxV
                have hf : ¬ ((clauseVal A (pairIn x y) && clauseVal B (pairIn x y) && clauseVal V (pairIn x y)) = true) := by
                  rw [hABV]
                  rintro ⟨u, v, huv, hu, hv⟩
                  simp only [pairIn, decide_eq_true_eq] at hu hv
                  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
                  · exact bowtieAdj_irrefl _ huv
                  · exact hnab huv
                  · exact hnab (bowtieAdj_symm huv)
                  · exact bowtieAdj_irrefl _ huv
                have hAt : clauseVal A (pairIn x y) = true := by
                  simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hA_all x hx0, Or.inl rfl⟩
                have hVt : clauseVal V (pairIn x y) = true := by
                  simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hxV, Or.inl rfl⟩
                constructor
                · intro hxB; apply hf
                  rw [Bool.and_eq_true, Bool.and_eq_true]
                  exact ⟨⟨hAt, by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hxB, Or.inl rfl⟩⟩, hVt⟩
                · intro hyB; apply hf
                  rw [Bool.and_eq_true, Bool.and_eq_true]
                  exact ⟨⟨hAt, by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨y, hyB, Or.inr rfl⟩⟩, hVt⟩
              -- Now ALL of `{1, 2, 3, 4}` are outside `B`!
              have hB12 : (1 : Fin 5) ∉ B ∧ (2 : Fin 5) ∉ B := by
                rcases h12 with h1V | h2V <;> rcases h34 with h3V | h4V
                · exact ⟨(hnoB 1 3 (by decide) (by decide) h1V).1, (hnoB 3 2 (by decide) (by decide) h3V).2⟩
                · exact ⟨(hnoB 1 3 (by decide) (by decide) h1V).1, (hnoB 4 2 (by decide) (by decide) h4V).2⟩
                · exact ⟨(hnoB 3 1 (by decide) (by decide) h3V).2, (hnoB 2 3 (by decide) (by decide) h2V).1⟩
                · exact ⟨(hnoB 4 1 (by decide) (by decide) h4V).2, (hnoB 2 3 (by decide) (by decide) h2V).1⟩
              have ht12 := (hABV (pairIn 1 2)).mpr ⟨1, 2, by decide, by simp [pairIn], by simp [pairIn]⟩
              have hBt := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp ht12).1).2
              simp only [clauseVal, pairIn, decide_eq_true_eq] at hBt
              obtain ⟨i, hiB, hi12⟩ := hBt
              rcases hi12 with rfl | rfl
              · exact hB12.1 hiB
              · exact hB12.2 hiB
            · -- `0 ∉ V`: since `V` is a vertex cover, `1, 2, 3, 4 ∈ V`!
              -- So `V` is TRUE on all 4 non-edges `{1,3}, {1,4}, {2,3}, {2,4}`, forcing `f₁ || clauseVal U`
              -- to be FALSE on all 4, hence `U ⊆ {0}` and `f₁` false on all 4 while true on `{1,2}` and `{3,4}`!
              have hV_vc : ∀ u v, bowtieAdj u v → u ∈ V ∨ v ∈ V := by
                intro u v huv
                have h1 := (Bool.and_eq_true _ _ |>.mp ((heval (pairIn u v)).mpr ⟨u, v, huv, by simp [pairIn], by simp [pairIn]⟩)).2
                simp only [clauseVal, pairIn, decide_eq_true_eq] at h1
                obtain ⟨i, hiV, hiuv⟩ := h1
                rcases hiuv with rfl | rfl
                · exact Or.inl hiV
                · exact Or.inr hiV
              have hV_all : ∀ k : Fin 5, k ≠ 0 → k ∈ V := by
                intro k hk; fin_cases k
                · exact absurd rfl hk
                · exact (hV_vc 0 1 (by decide)).resolve_left h0V
                · exact (hV_vc 0 2 (by decide)).resolve_left h0V
                · exact (hV_vc 0 3 (by decide)).resolve_left h0V
                · exact (hV_vc 0 4 (by decide)).resolve_left h0V
              have hbad_pair : ∀ x y : Fin 5, x ≠ 0 → ¬ bowtieAdj x y →
                  f₁ (pairIn x y) = false ∧ x ∉ U ∧ y ∉ U := by
                intro x y hx0 hnab
                have hf : ¬ (((f₁ (pairIn x y) || clauseVal U (pairIn x y)) && clauseVal V (pairIn x y)) = true) := by
                  rw [heval]
                  rintro ⟨u, v, huv, hu, hv⟩
                  simp only [pairIn, decide_eq_true_eq] at hu hv
                  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
                  · exact bowtieAdj_irrefl _ huv
                  · exact hnab huv
                  · exact hnab (bowtieAdj_symm huv)
                  · exact bowtieAdj_irrefl _ huv
                have hVt : clauseVal V (pairIn x y) = true := by
                  simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hV_all x hx0, Or.inl rfl⟩
                refine ⟨?_, ?_, ?_⟩
                · cases hfx : f₁ (pairIn x y)
                  · rfl
                  · exact absurd (by simp [hfx, hVt]) hf
                · intro hxU; apply hf
                  rw [Bool.and_eq_true, Bool.or_eq_true]
                  exact ⟨Or.inr (by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨x, hxU, Or.inl rfl⟩), hVt⟩
                · intro hyU; apply hf
                  rw [Bool.and_eq_true, Bool.or_eq_true]
                  exact ⟨Or.inr (by simp only [clauseVal, pairIn, decide_eq_true_eq]; exact ⟨y, hyU, Or.inr rfl⟩), hVt⟩
              have hU1 := (hbad_pair 1 3 (by decide) (by decide)).2.1
              have hU3 := (hbad_pair 1 3 (by decide) (by decide)).2.2
              have hU2 := (hbad_pair 2 4 (by decide) (by decide)).2.1
              have hU4 := (hbad_pair 2 4 (by decide) (by decide)).2.2
              have hf12 : f₁ (pairIn 1 2) = true := by
                have ht := (Bool.and_eq_true _ _ |>.mp ((heval (pairIn 1 2)).mpr ⟨1, 2, by decide, by simp [pairIn], by simp [pairIn]⟩)).1
                have hUc : clauseVal U (pairIn 1 2) = false := by
                  rw [Bool.eq_false_iff]
                  intro h
                  simp only [clauseVal, pairIn, decide_eq_true_eq] at h
                  rcases h with ⟨i, hiU, hi⟩
                  rcases hi with rfl | rfl
                  · exact hU1 hiU
                  · exact hU2 hiU
                simpa [hUc] using ht
              have hf34 : f₁ (pairIn 3 4) = true := by
                have ht := (Bool.and_eq_true _ _ |>.mp ((heval (pairIn 3 4)).mpr ⟨3, 4, by decide, by simp [pairIn], by simp [pairIn]⟩)).1
                have hUc : clauseVal U (pairIn 3 4) = false := by
                  rw [Bool.eq_false_iff]
                  intro h
                  simp only [clauseVal, pairIn, decide_eq_true_eq] at h
                  rcases h with ⟨i, hiU, hi⟩
                  rcases hi with rfl | rfl
                  · exact hU3 hiU
                  · exact hU4 hiU
                simpa [hUc] using ht
              obtain ⟨h12_1, _⟩ := Bool.and_eq_true _ _ |>.mp hf12
              obtain ⟨_, h34_2⟩ := Bool.and_eq_true _ _ |>.mp hf34
              simp only [clauseVal, pairIn, decide_eq_true_eq] at h12_1 h34_2
              obtain ⟨a, ha1, ha12⟩ := h12_1
              obtain ⟨c, hc2, hc34⟩ := h34_2
              have hac_t : f₁ (pairIn a c) = true := by
                simp only [f₁, Bool.and_eq_true, clauseVal, pairIn, decide_eq_true_eq]
                exact ⟨⟨a, ha1, Or.inl rfl⟩, ⟨c, hc2, Or.inr rfl⟩⟩
              rcases ha12 with rfl | rfl <;> rcases hc34 with rfl | rfl
              · have := (hbad_pair 1 3 (by decide) (by decide)).1; rw [hac_t] at this; cases this
              · have := (hbad_pair 1 4 (by decide) (by decide)).1; rw [hac_t] at this; cases this
              · have := (hbad_pair 2 3 (by decide) (by decide)).1; rw [hac_t] at this; cases this
              · have := (hbad_pair 2 4 (by decide) (by decide)).1; rw [hac_t] at this; cases this
          -- Finally, expand `f₂` via `and_operands j₂ hj₂`!
          have hout2 : ∀ x, val C x C.output = ((b₁ && f₁ x) || val C x (5 + j₂)) :=
            fun x => by simpa [f₂] using hout' x
          rcases and_operands j₂ hj₂ with ht2 | ⟨a, hlna, ha⟩ | ⟨a, b, hlna, hlnb, hab⟩ | hf2
          · exact ne_true (fun x => by rw [hout2 x, ht2 x, Bool.or_true])
          · rcases hbelow2 a (live_of_lnext hlna) hlna.1.1 with ht | ⟨U, hU | hU⟩
            · exact ne_true (fun x => by rw [hout2 x, ha x, ht x, Bool.or_true])
            · cases b₁
              · exact ne_clause U (fun x => by simpa [ha x, hU x] using hout2 x)
              · exact kill_pair U U (fun x => by simpa [ha x, hU x, Bool.and_self] using hout2 x)
            · exact rule_out_1and S₁ S₂ (Or.inr ⟨U, Or.inr fun x => by
                have hx := hout2 x; rw [ha x, hU x] at hx
                rw [hx]; dsimp only [f₁]
                cases b₁ <;> cases (clauseVal S₁ x && clauseVal S₂ x) <;> cases clauseVal U x <;> rfl⟩)
          · rcases hbelow2 a (live_of_lnext hlna) hlna.1.1 with hta | ⟨U, hU | hU⟩ <;>
              rcases hbelow2 b (live_of_lnext hlnb) hlnb.1.1 with htb | ⟨V, hV | hV⟩
            · exact ne_true (fun x => by rw [hout2 x, hab x, hta x, htb x]; simp)
            · cases b₁
              · exact ne_clause V (fun x => by simpa [hab x, hta x, hV x] using hout2 x)
              · exact rule_out_1and S₁ S₂ (Or.inr ⟨V, Or.inr fun x => by simpa [f₁, hab x, hta x, hV x] using hout2 x⟩)
            · exact rule_out_1and S₁ S₂ (Or.inr ⟨V, Or.inr fun x => by
                have hx := hout2 x; rw [hab x, hta x, hV x, Bool.true_and] at hx
                rw [hx]; dsimp only [f₁]
                cases b₁ <;> cases (clauseVal S₁ x && clauseVal S₂ x) <;> cases clauseVal V x <;> rfl⟩)
            · cases b₁
              · exact ne_clause U (fun x => by simpa [hab x, hU x, htb x] using hout2 x)
              · exact rule_out_1and S₁ S₂ (Or.inr ⟨U, Or.inr fun x => by simpa [f₁, hab x, hU x, htb x] using hout2 x⟩)
            · cases b₁
              · exact bowtie_ne_and_clauses U V (fun x => by
                  have hx := hout2 x; simp only [hab x, hU x, hV x, Bool.false_and, Bool.false_or] at hx
                  rw [← hx, val_output, bowtieEval_adj hE])
              · exact kill_pair U V (fun x => by simpa [hab x, hU x, hV x] using hout2 x)
            · cases b₁
              · exact kill_mix V U (fun x => by
                  have hx := hout2 x; simp only [hab x, hU x, hV x, Bool.false_and, Bool.false_or] at hx
                  rw [hx, Bool.and_comm])
              · exact kill_pair U V (fun x => by
                  have hx := hout2 x; simp only [hab x, hU x, hV x, Bool.true_and] at hx
                  rw [hx]; cases f₁ x <;> cases clauseVal U x <;> cases clauseVal V x <;> rfl)
            · exact rule_out_1and S₁ S₂ (Or.inr ⟨U, Or.inr fun x => by
                have hx := hout2 x; rw [hab x, hU x, htb x, Bool.and_true] at hx
                rw [hx]; dsimp only [f₁]
                cases b₁ <;> cases (clauseVal S₁ x && clauseVal S₂ x) <;> cases clauseVal U x <;> rfl⟩)
            · cases b₁
              · exact kill_mix U V (fun x => by simpa [hab x, hU x, hV x] using hout2 x)
              · exact kill_pair U V (fun x => by
                  have hx := hout2 x; simp only [hab x, hU x, hV x, Bool.true_and] at hx
                  rw [hx]; cases f₁ x <;> cases clauseVal U x <;> cases clauseVal V x <;> rfl)
            · exact kill_pair U V (fun x => by
                have hx := hout2 x; rw [hab x, hU x, hV x] at hx
                rw [hx]; cases b₁ <;> cases f₁ x <;> cases clauseVal U x <;> cases clauseVal V x <;> rfl)
          · cases b₁
            · have hx := hout2 (pairIn 0 1)
              rw [hf2 (pairIn 0 1), (bowtie_pair_iff hE 0 1).mpr (by decide)] at hx; simp at hx
            · exact bowtie_ne_and_clauses S₁ S₂ (fun x => by
                have hx := hout2 x; simp only [f₁, hf2 x, Bool.true_and, Bool.or_false] at hx
                rw [← hx, val_output, bowtieEval_adj hE])

open Classical in
noncomputable def liveOrZero (C : Circuit) : Finset ℕ :=
  (liveGates C).filter (fun j => isOrGate C (5 + j) ∧ val C (sing 0) (5 + j) = false)

theorem mem_liveOrZero {C : Circuit} {j : ℕ} :
    j ∈ liveOrZero C ↔ j ∈ liveGates C ∧ isOrGate C (5 + j) ∧ val C (sing 0) (5 + j) = false := by
  simp only [liveOrZero, Finset.mem_filter]

/-- Every `Monotone2` circuit computing the bowtie has at least 3 live OR gates false on `sing 0`. -/
theorem three_or_zero_gates {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) :
    3 ≤ (liveOrZero C).card := by
  classical
  -- For any `k ≤ C.gates.length`, if a Finset `M` of live wires `< 5 + k` with `val (sing 0) = false`
  -- covers `{1, 2, 3, 4}` (every `i ∈ {1,2,3,4}` has some `w ∈ M` with `val (pairIn 0 i) w = true`),
  -- then `4 ≤ M.card + ((liveOrZero C).filter (· < k)).card`!
  have hcov : ∀ k, k ≤ C.gates.length → ∀ M : Finset ℕ,
      (∀ w ∈ M, w < 5 + k ∧ Live C w ∧ val C (sing 0) w = false) →
      (∀ i : Fin 5, i ≠ 0 → ∃ w ∈ M, val C (pairIn 0 i) w = true) →
      4 ≤ M.card + ((liveOrZero C).filter (fun j => j < k)).card := by
    intro k
    induction k with
    | zero =>
      intro _ M hM hcover
      have hinj : ({1, 2, 3, 4} : Finset (Fin 5)).card ≤ M.card := by
        refine Finset.card_le_card_of_injOn (fun i : Fin 5 => i.val) ?_ ?_
        · intro i hi
          have hi0 : i ≠ 0 := by simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> decide
          obtain ⟨w, hwM, hwi⟩ := hcover i hi0
          obtain ⟨hw5, _, hw0⟩ := hM w hwM
          have hweq : w = (⟨w, hw5⟩ : Fin 5).val := rfl
          rw [hweq, val_input] at hwi hw0
          simp only [sing, decide_eq_false_iff_not] at hw0
          simp only [pairIn, decide_eq_true_eq] at hwi
          have hwi' : (⟨w, hw5⟩ : Fin 5) = i := hwi.resolve_left hw0
          have hiw : i.val = w := congrArg Fin.val hwi'.symm
          simpa [hiw] using hwM
        · intro a _ b _ hab; exact Fin.ext hab
      have h4 : ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
      omega
    | succ k ih =>
      intro hk M hM hcover
      by_cases hmem : 5 + k ∈ M
      · obtain ⟨_, hlive_k, hzero_k⟩ := hM (5 + k) hmem
        obtain ⟨g, hg⟩ : ∃ g, C.gates[k]? = some g := ⟨C.gates[k], List.getElem?_eq_getElem (by omega)⟩
        rcases mono_op hC hg with hop | hop
        · -- Gate `k` is an AND gate false on `sing 0`, so some valid input `a < 5 + k` is false on `sing 0`!
          have hna : ¬ ∀ a ∈ g.inputs, a < 5 + k ∧ val C (sing 0) a = true := by
            intro hall; have := (val_and (sing 0) hg hop).mpr hall; rw [hzero_k] at this; cases this
          push Not at hna
          obtain ⟨a, ha_in, ha_bad⟩ := hna
          -- Case: is `a < 5 + k`? If not, `5 + k` is identically `false`, so simply erase `5 + k`!
          by_cases halt : a < 5 + k
          · have ha0 : val C (sing 0) a = false := by
              cases h : val C (sing 0) a
              · rfl
              · exact absurd h (ha_bad halt)
            have hln : LNext C a (5 + k) := ⟨⟨halt, k, g, hg, rfl, ha_in⟩, hlive_k⟩
            let M' := insert a (M.erase (5 + k))
            have hM' : ∀ w ∈ M', w < 5 + k ∧ Live C w ∧ val C (sing 0) w = false := by
              intro w hw
              rcases Finset.mem_insert.mp hw with rfl | hw'
              · exact ⟨halt, live_of_lnext hln, ha0⟩
              · obtain ⟨hne, hwM⟩ := Finset.mem_erase.mp hw'
                obtain ⟨hwlt, hwl, hw0⟩ := hM w hwM
                exact ⟨by omega, hwl, hw0⟩
            have hcov' : ∀ i : Fin 5, i ≠ 0 → ∃ w ∈ M', val C (pairIn 0 i) w = true := by
              intro i hi0
              obtain ⟨w, hwM, hwi⟩ := hcover i hi0
              by_cases hw : w = 5 + k
              · subst hw
                exact ⟨a, Finset.mem_insert_self _ _, ((val_and (pairIn 0 i) hg hop).mp hwi a ha_in).2⟩
              · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hw, hwM⟩), hwi⟩
            have hstep := ih (by omega) M' hM' hcov'
            have hcardM : M'.card ≤ M.card := by
              have h1 : M'.card ≤ (M.erase (5 + k)).card + 1 := Finset.card_insert_le a (M.erase (5 + k))
              have h2 := Finset.card_erase_of_mem hmem
              have hpos := Finset.card_pos.mpr ⟨5 + k, hmem⟩
              omega
            have hsub : (liveOrZero C).filter (fun j => j < k) ⊆ (liveOrZero C).filter (fun j => j < k + 1) := by
              intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, by omega⟩
            have hcardF := Finset.card_le_card hsub
            omega
          · -- Out-of-bounds input makes AND gate `5 + k` identically `false`!
            let M' := M.erase (5 + k)
            have hM' : ∀ w ∈ M', w < 5 + k ∧ Live C w ∧ val C (sing 0) w = false := by
              intro w hw
              obtain ⟨hne, hwM⟩ := Finset.mem_erase.mp hw
              obtain ⟨hwlt, hwl, hw0⟩ := hM w hwM
              exact ⟨by omega, hwl, hw0⟩
            have hcov' : ∀ i : Fin 5, i ≠ 0 → ∃ w ∈ M', val C (pairIn 0 i) w = true := by
              intro i hi0
              obtain ⟨w, hwM, hwi⟩ := hcover i hi0
              by_cases hw : w = 5 + k
              · subst hw
                exact absurd ((val_and (pairIn 0 i) hg hop).mp hwi a ha_in).1 halt
              · exact ⟨w, Finset.mem_erase.mpr ⟨hw, hwM⟩, hwi⟩
            have hstep := ih (by omega) M' hM' hcov'
            have hcardM : M'.card ≤ M.card := Finset.card_erase_le
            have hsub : (liveOrZero C).filter (fun j => j < k) ⊆ (liveOrZero C).filter (fun j => j < k + 1) := by
              intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, by omega⟩
            have hcardF := Finset.card_le_card hsub
            omega
        · -- Gate `k` is an OR gate false on `sing 0` (`k ∈ liveOrZero C`), replacing `5 + k` by its ≤ 2 valid inputs!
          have hk_or0 : k ∈ (liveOrZero C).filter (fun j => j < k + 1) := by
            simp only [Finset.mem_filter, mem_liveOrZero, mem_liveGates, isOrGate]
            exact ⟨⟨⟨by omega, hlive_k⟩, ⟨k, g, hg, rfl, hop⟩, hzero_k⟩, by omega⟩
          let ins := g.inputs.toFinset.filter (fun a => a < 5 + k)
          let M' := (M.erase (5 + k)) ∪ ins
          have hM' : ∀ w ∈ M', w < 5 + k ∧ Live C w ∧ val C (sing 0) w = false := by
            intro w hw
            rcases Finset.mem_union.mp hw with hw' | hw'
            · obtain ⟨hne, hwM⟩ := Finset.mem_erase.mp hw'
              obtain ⟨hwlt, hwl, hw0⟩ := hM w hwM
              exact ⟨by omega, hwl, hw0⟩
            · simp only [ins, Finset.mem_filter, List.mem_toFinset] at hw'
              have hln : LNext C w (5 + k) := ⟨⟨hw'.2, k, g, hg, rfl, hw'.1⟩, hlive_k⟩
              have hw0 : val C (sing 0) w = false := by
                cases h : val C (sing 0) w
                · rfl
                · have := (val_or (sing 0) hg hop).mpr ⟨w, hw'.1, hw'.2, h⟩
                  rw [hzero_k] at this; cases this
              exact ⟨hw'.2, live_of_lnext hln, hw0⟩
          have hcov' : ∀ i : Fin 5, i ≠ 0 → ∃ w ∈ M', val C (pairIn 0 i) w = true := by
            intro i hi0
            obtain ⟨w, hwM, hwi⟩ := hcover i hi0
            by_cases hw : w = 5 + k
            · subst hw
              obtain ⟨a, ha, halt, hva⟩ := (val_or (pairIn 0 i) hg hop).mp hwi
              exact ⟨a, Finset.mem_union_right _ (by simp [ins, ha, halt]), hva⟩
            · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hw, hwM⟩), hwi⟩
          have hstep := ih (by omega) M' hM' hcov'
          have hins_card : ins.card ≤ 2 :=
            (Finset.card_le_card (Finset.filter_subset _ _)).trans
              ((List.toFinset_card_le g.inputs).trans (hC g (List.mem_of_getElem? hg)).2)
          have hcardM : M'.card ≤ M.card + 1 := by
            have h1 : M'.card ≤ (M.erase (5 + k)).card + ins.card := Finset.card_union_le (M.erase (5 + k)) ins
            have h2 := Finset.card_erase_of_mem hmem
            have hpos := Finset.card_pos.mpr ⟨5 + k, hmem⟩
            omega
          have hcardF : ((liveOrZero C).filter (fun j => j < k)).card + 1 ≤
              ((liveOrZero C).filter (fun j => j < k + 1)).card := by
            have hsub : insert k ((liveOrZero C).filter (fun j => j < k)) ⊆
                (liveOrZero C).filter (fun j => j < k + 1) := by
              intro j hj
              rcases Finset.mem_insert.mp hj with rfl | hj'
              · exact hk_or0
              · simp only [Finset.mem_filter] at hj' ⊢; exact ⟨hj'.1, by omega⟩
            have hnot : k ∉ (liveOrZero C).filter (fun j => j < k) := by simp
            have := Finset.card_le_card hsub
            rwa [Finset.card_insert_of_notMem hnot] at this
          omega
      · -- `5 + k ∉ M`
        have hM' : ∀ w ∈ M, w < 5 + k ∧ Live C w ∧ val C (sing 0) w = false := by
          intro w hw
          obtain ⟨hwlt, hwl, hw0⟩ := hM w hw
          have hne : w ≠ 5 + k := fun e => hmem (e ▸ hw)
          exact ⟨by omega, hwl, hw0⟩
        have hstep := ih (by omega) M hM' hcover
        have hsub : (liveOrZero C).filter (fun j => j < k) ⊆ (liveOrZero C).filter (fun j => j < k + 1) := by
          intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, by omega⟩
        have hcardF := Finset.card_le_card hsub
        omega
  have hfinal := hcov C.gates.length le_rfl {C.output}
    (fun w hw => by
      rw [Finset.mem_singleton] at hw; subst hw
      exact ⟨(output_bounds hE).2, ReflTransGen.refl, bowtie_sing hE 0⟩)
    (fun i hi0 => ⟨C.output, Finset.mem_singleton_self _,
      (bowtie_pair_iff hE 0 i).mpr (by fin_cases i <;> first | exact absurd rfl hi0 | decide)⟩)
  have hsub : (liveOrZero C).filter (fun j => j < C.gates.length) ⊆ liveOrZero C :=
    Finset.filter_subset _ _
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hfinal
  omega

/-- Every `Monotone2` circuit computing the bowtie has at least 8 live gates. -/
theorem eight_live_gates {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) :
    8 ≤ (liveGates C).card := by
  classical
  by_contra hlt
  push Not at hlt
  let S : Finset (Fin 5) := Finset.univ.filter (Eligible C)
  have hS_vc : 3 ≤ S.card :=
    bowtie_vc_ge3 S (fun u v huv => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact eligible_covers_edge hC hE huv)
  let B : Finset ℕ := ((living C).erase C.output).filter (Branch C)
  have hS_le_B : S.card ≤ B.card := by
    let f (v : Fin 5) : ℕ := if h : Eligible C v then firstBranch C v h else 0
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro v hv
      have hev : Eligible C v := (Finset.mem_filter.mp hv).2
      have hsp := firstBranch_spec hC hE hev
      have hne : firstBranch C v hev ≠ C.output := by
        intro heq
        have := (branch_iff_two_le_outdeg hE _).mp hsp.2.2.1
        rw [heq, outdeg_output hE] at this; omega
      simp only [B, f, dif_pos hev, Finset.mem_coe, Finset.mem_filter, Finset.mem_erase, mem_living hE]
      exact ⟨⟨hne, hsp.1⟩, hsp.2.2.1⟩
    · intro u hu v hv heq
      have heu : Eligible C u := (Finset.mem_filter.mp hu).2
      have hev : Eligible C v := (Finset.mem_filter.mp hv).2
      simp only [f, dif_pos heu, dif_pos hev] at heq
      exact firstBranch_injective hC hE heu hev heq
  have hB_le_delta : B.card ≤ ∑ a ∈ (living C).erase C.output, (outdeg C a - 1) := by
    calc B.card = ∑ _a ∈ B, 1 := by simp
      _ ≤ ∑ a ∈ B, (outdeg C a - 1) := Finset.sum_le_sum fun a ha => by
          have hb := (branch_iff_two_le_outdeg hE a).mp (Finset.mem_filter.mp ha).2
          omega
      _ ≤ ∑ a ∈ (living C).erase C.output, (outdeg C a - 1) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hbud := live_budget_exact hC hE
  -- Force `S.card = 3`, `B.card = 3`, `(liveGates C).card = 7`, and EVERY branching wire is `firstBranch v` for some `v ∈ S`!
  have hScard : S.card = 3 := by omega
  have hBcard : B.card = 3 := by omega
  have hB_img : ∀ b ∈ B, ∃ v : Fin 5, ∃ hv : Eligible C v, firstBranch C v hv = b := by
    let f (v : Fin 5) : ℕ := if h : Eligible C v then firstBranch C v h else 0
    have hsub : S.image f ⊆ B := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      have hev : Eligible C v := (Finset.mem_filter.mp hv).2
      have hsp := firstBranch_spec hC hE hev
      have hne : firstBranch C v hev ≠ C.output := by
        intro heq; have := (branch_iff_two_le_outdeg hE _).mp hsp.2.2.1
        rw [heq, outdeg_output hE] at this; omega
      simp only [B, f, dif_pos hev, Finset.mem_coe, Finset.mem_filter, Finset.mem_erase, mem_living hE]
      exact ⟨⟨hne, hsp.1⟩, hsp.2.2.1⟩
    have hinj : Set.InjOn f (S : Set (Fin 5)) := by
      intro u hu v hv heq
      have heu : Eligible C u := (Finset.mem_filter.mp hu).2
      have hev : Eligible C v := (Finset.mem_filter.mp hv).2
      simp only [f, dif_pos heu, dif_pos hev] at heq
      exact firstBranch_injective hC hE heu hev heq
    have heq : S.image f = B :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj]; omega)
    intro b hb
    rw [← heq] at hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have hev : Eligible C v := (Finset.mem_filter.mp hv).2
    exact ⟨v, hev, by simp [f, dif_pos hev]⟩
  -- Every live branching wire has `|S(b)| = 1` (specifically `S(b) = {v}`), so NO wire with `|S(w)| ≥ 2` or `S(w) = ∅` can branch!
  have hbranch_sing : ∀ b, Live C b → Branch C b → ∃ v : Fin 5, val C (sing v) b = true ∧ ∀ u, val C (sing u) b = true → u = v := by
    intro b hbl hbb
    have hne : b ≠ C.output := by
      intro heq; have := (branch_iff_two_le_outdeg hE b).mp hbb
      rw [heq, outdeg_output hE] at this; omega
    have hbB : b ∈ B := by simp only [B, Finset.mem_filter, Finset.mem_erase, mem_living hE]; exact ⟨⟨hne, hbl⟩, hbb⟩
    obtain ⟨v, hv, hfb⟩ := hB_img b hbB
    have hsp := firstBranch_spec hC hE hv
    rw [hfb] at hsp
    exact ⟨v, hsp.2.1.1, fun u hu => chain_sing_subset hC hE hsp.2.2.2 hsp.1 hu⟩
  have hwide_not_branch : ∀ w, Live C w → isWide C w → ¬ Branch C w := by
    intro w hwl ⟨u₁, u₂, hne, h1, h2⟩ hwb
    obtain ⟨v, _, huniq⟩ := hbranch_sing w hwl hwb
    exact hne ((huniq u₁ h1).trans (huniq u₂ h2).symm)
  -- Every `v ∉ S` has a branch-free chain ALL THE WAY to `C.output`!
  have not_elig_chain : ∀ v : Fin 5, v ∉ S → Trace C (fun z => ¬ Branch C z) v.val C.output := by
    intro v hvS
    have hne : ¬ Eligible C v := by simpa [S] using hvS
    -- Show by induction along a live path starting at `v.val`: if `Trace (¬ Branch) v.val w` and `w < C.output`,
    -- then `¬ Branch w` (because if `Branch w`, by `hbranch_sing` some `u` has `val (sing u) w = true`,
    -- by Claim 1 `u = v`, and `val zeroIn w = false` since `w` reaches output or `v` carries... wait: check `val zeroIn w = false`!).
    suffices ∀ k w, w = C.output - k → Live C w → Trace C (fun z => ¬ Branch C z) v.val w →
        Trace C (fun z => ¬ Branch C z) v.val C.output by
      exact this (C.output - v.val) v.val (by have := live_le_output (input_live hE v); omega)
        (input_live hE v) ReflTransGen.refl
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro w hwk hwl htw
      by_cases hwo : w = C.output
      · exact hwo ▸ htw
      · have hnb : ¬ Branch C w := by
          intro hwb
          obtain ⟨u, hu, _⟩ := hbranch_sing w hwl hwb
          have huv : u = v := chain_sing_subset hC hE htw hwl hu
          subst huv
          have hz : val C zeroIn w = false := by
            cases h0 : val C zeroIn w
            · rfl
            · -- If `val zeroIn w = true`, then `val (sing w_nbr) w = true` for ALL `w_nbr`, contradicting Claim 1!
              obtain ⟨a, b, hab, _, _⟩ := bowtie_deg2 u
              have ha := val_mono hC (x := zeroIn) (y := sing a) (fun i hi => by simp [zeroIn] at hi) w h0
              have hb := val_mono hC (x := zeroIn) (y := sing b) (fun i hi => by simp [zeroIn] at hi) w h0
              exact absurd ((chain_sing_subset hC hE htw hwl ha).trans
                (chain_sing_subset hC hE htw hwl hb).symm) hab
          exact hne ⟨w, hwl, ⟨hu, hz⟩, hwb⟩
        rcases hwl.cases_head with rfl | ⟨w', hww', hw'o⟩
        · exact absurd rfl hwo
        · have hle := live_le_output hw'o
          have hlt := hww'.1
          exact ih (C.output - w') (by omega) w' (by omega) hw'o (htw.tail ⟨hnb, hww', hw'o⟩)
  -- Since `S` is a vertex cover of size 3, `0 ∈ S`, and there exist `u ∈ {1,2}`, `u' ∈ {1,2}` (`u' ∉ S`, `Adj u u'`, `Adj 0 u'`),
  -- and `v ∈ {3,4}`, `v' ∈ {3,4}` (`v' ∉ S`, `Adj v v'`, `Adj 0 v'`), with `u' ≠ v'`!
  have hS0 : (0 : Fin 5) ∈ S := by
    by_contra h0
    have h1 : (1 : Fin 5) ∈ S := by
      rcases eligible_covers_edge hC hE (u := 0) (v := 1) (by decide) with h | h
      · exact absurd (by simpa [S] using h) h0
      · simpa [S] using h
    have h2 : (2 : Fin 5) ∈ S := by
      rcases eligible_covers_edge hC hE (u := 0) (v := 2) (by decide) with h | h
      · exact absurd (by simpa [S] using h) h0
      · simpa [S] using h
    have h3 : (3 : Fin 5) ∈ S := by
      rcases eligible_covers_edge hC hE (u := 0) (v := 3) (by decide) with h | h
      · exact absurd (by simpa [S] using h) h0
      · simpa [S] using h
    have h4 : (4 : Fin 5) ∈ S := by
      rcases eligible_covers_edge hC hE (u := 0) (v := 4) (by decide) with h | h
      · exact absurd (by simpa [S] using h) h0
      · simpa [S] using h
    have hsub : ({1, 2, 3, 4} : Finset (Fin 5)) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    have h4c : ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
    omega
  have hmiss : ∃ u u' v v' : Fin 5, u' ∉ S ∧ v' ∉ S ∧ u' ≠ v' ∧
      bowtieAdj 0 u' ∧ bowtieAdj u u' ∧ u ≠ 0 ∧ u ≠ u' ∧
      bowtieAdj 0 v' ∧ bowtieAdj v v' ∧ v ≠ 0 ∧ v ≠ v' := by
    have h12 : (1 : Fin 5) ∉ S ∨ (2 : Fin 5) ∉ S := by
      by_contra hc; push Not at hc; obtain ⟨h1, h2⟩ := hc
      have h34 : (3 : Fin 5) ∈ S ∨ (4 : Fin 5) ∈ S := by
        simpa [S] using eligible_covers_edge hC hE (u := 3) (v := 4) (by decide)
      rcases h34 with h3 | h4
      · have hsub : ({0, 1, 2, 3} : Finset (Fin 5)) ⊆ S := by
          intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have hc1 := Finset.card_le_card hsub
        have hc2 : ({0, 1, 2, 3} : Finset (Fin 5)).card = 4 := by decide
        omega
      · have hsub : ({0, 1, 2, 4} : Finset (Fin 5)) ⊆ S := by
          intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have hc1 := Finset.card_le_card hsub
        have hc2 : ({0, 1, 2, 4} : Finset (Fin 5)).card = 4 := by decide
        omega
    have h34 : (3 : Fin 5) ∉ S ∨ (4 : Fin 5) ∉ S := by
      by_contra hc; push Not at hc; obtain ⟨h3, h4⟩ := hc
      have h12' : (1 : Fin 5) ∈ S ∨ (2 : Fin 5) ∈ S := by
        simpa [S] using eligible_covers_edge hC hE (u := 1) (v := 2) (by decide)
      rcases h12' with h1 | h2
      · have hsub : ({0, 1, 3, 4} : Finset (Fin 5)) ⊆ S := by
          intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have hc1 := Finset.card_le_card hsub
        have hc2 : ({0, 1, 3, 4} : Finset (Fin 5)).card = 4 := by decide
        omega
      · have hsub : ({0, 2, 3, 4} : Finset (Fin 5)) ⊆ S := by
          intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have hc1 := Finset.card_le_card hsub
        have hc2 : ({0, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
        omega
    rcases h12 with h1 | h2 <;> rcases h34 with h3 | h4
    · exact ⟨2, 1, 4, 3, h1, h3, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 1, 3, 4, h1, h4, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨1, 2, 4, 3, h2, h3, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨1, 2, 3, 4, h2, h4, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨u, u', v, v', hu'S, hv'S, huv'_ne, h0u', huu', hu0, huu'_ne, h0v', hvv', hv0, hvv'_ne⟩ := hmiss
  have hTu' := not_elig_chain u' hu'S
  have hTv' := not_elig_chain v' hv'S
  -- Let `m` be the FIRST common wire on `u'`'s chain and `v'`'s chain.
  have hex_m : ∃ m, Trace C (fun z => ¬ Branch C z) u'.val m ∧ Trace C (fun z => ¬ Branch C z) v'.val m :=
    ⟨C.output, hTu', hTv'⟩
  set m := Nat.find hex_m with hm_def
  have hm : Trace C (fun z => ¬ Branch C z) u'.val m ∧ Trace C (fun z => ¬ Branch C z) v'.val m :=
    Nat.find_spec hex_m
  have hm_live : Live C m := by
    -- Any wire on a branch-free chain to `C.output` is live!
    have hstep : ∀ x y, Trace C (fun z => ¬ Branch C z) x y → Live C x → Live C y := by
      intro x y hxy
      induction hxy with
      | refl => exact id
      | tail _ h _ => intro _; exact h.2.2
    exact hstep u'.val m hm.1 (input_live hE u')
  have hm_u'0 : val C (sing u') m = false := by
    cases h : val C (sing u') m
    · rfl
    · exact absurd (chain_sing_subset hC hE hm.2 hm_live h) huv'_ne
  have hm_v'0 : val C (sing v') m = false := by
    cases h : val C (sing v') m
    · rfl
    · exact absurd (chain_sing_subset hC hE hm.1 hm_live h) huv'_ne.symm
  -- Helper: given `x'` (`x' ∉ S`, chain to `m` with `val (sing x') m = false`) and neighbors `0, x`,
  -- find the first gate `a` on `x'`'s chain where `val (sing x') a = false`, prove `a < m`,
  -- and find an OR gate `w` with `0, x ∈ S(w)` and a fan-out-1 wide path `w → ... → h → a`!
  have find_wide_or : ∀ (x x' y' : Fin 5),
      Trace C (fun z => ¬ Branch C z) x'.val m →
      Trace C (fun z => ¬ Branch C z) y'.val m →
      (∀ z < m, ¬ (Trace C (fun q => ¬ Branch C q) x'.val z ∧ Trace C (fun q => ¬ Branch C q) y'.val z)) →
      x' ≠ y' → x ≠ 0 → x ≠ x' → bowtieAdj 0 x' → bowtieAdj x x' →
      val C (sing x') m = false →
      ∃ a w, a < m ∧ Trace C (fun z => ¬ Branch C z) x'.val a ∧
        Live C w ∧ isOrGate C w ∧ val C (sing 0) w = true ∧
        Trace C (fun z => isWide C z) w a := by
    intro x x' y' hTx' hTy' hm_min hxy' hx0 hxx' h0x' hxx'_adj hm0
    have hex_a : ∃ a, Trace C (fun z => ¬ Branch C z) x'.val a ∧ val C (sing x') a = false :=
      ⟨m, hTx', hm0⟩
    set a := Nat.find hex_a with ha_def
    have ha : Trace C (fun z => ¬ Branch C z) x'.val a ∧ val C (sing x') a = false :=
      Nat.find_spec hex_a
    have ha_le_m : a ≤ m := Nat.find_min' hex_a ⟨hTx', hm0⟩
    have ha_live : Live C a := by
      have hstep : ∀ q r, Trace C (fun z => ¬ Branch C z) q r → Live C q → Live C r := by
        intro q r hqr; induction hqr with | refl => exact id | tail _ h _ => intro _; exact h.2.2
      exact hstep x'.val a ha.1 (input_live hE x')
    -- `a ≠ x'.val` because `val (sing x') x'.val = true`!
    rcases ha.1.cases_tail with heq | ⟨pred, hTpred, hnb_pred, hln_pred⟩
    · have h1 := ha.2; rw [heq, val_input] at h1; simp [sing] at h1
    have hpred_t : val C (sing x') pred = true := by
      cases h : val C (sing x') pred
      · exact absurd ⟨hTpred, h⟩ (Nat.find_min hex_a hln_pred.1.1)
      · rfl
    -- So `a` is an AND gate `5 + p` with `pred ∈ g.inputs` and another input `h` false on `sing x'`!
    obtain ⟨_, p, g, hg, hap, hpred_in⟩ := hln_pred.1
    have ha_and : g.op = GateOp.and := by
      rcases mono_op hC hg with hop | hop
      · exact hop
      · have := (val_or (sing x') hg hop).mpr ⟨pred, hpred_in, by omega, hpred_t⟩
        rw [← hap, ha.2] at this; cases this
    have hna : ¬ ∀ i ∈ g.inputs, i < 5 + p ∧ val C (sing x') i = true := by
      intro hall; have := (val_and (sing x') hg ha_and).mpr hall; rw [← hap, ha.2] at this; cases this
    push Not at hna
    obtain ⟨h, hh_in, hh_bad⟩ := hna
    have hh_ne_pred : h ≠ pred := by
      intro e; subst e; exact hh_bad (by omega) hpred_t
    -- `a` must be TRUE on `pairIn 0 x'` and `pairIn x x'`!
    have ha_0x' : val C (pairIn 0 x') a = true := by
      cases h0 : val C (pairIn 0 x') a
      · have hres := no_bypass_output hC ha.1 ha_live (x := pairIn 0 x') (y := sing 0)
          (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_right hi)
          (fun ht => by rw [h0] at ht; cases ht)
          ((bowtie_pair_iff hE 0 x').mpr h0x')
        rw [bowtie_sing hE 0] at hres; cases hres
      · rfl
    have ha_xx' : val C (pairIn x x') a = true := by
      cases h0 : val C (pairIn x x') a
      · have hres := no_bypass_output hC ha.1 ha_live (x := pairIn x x') (y := sing x)
          (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_right hi)
          (fun ht => by rw [h0] at ht; cases ht)
          ((bowtie_pair_iff hE x x').mpr hxx'_adj)
        rw [bowtie_sing hE x] at hres; cases hres
      · rfl
    obtain ⟨hhlt, hh_0x'⟩ := (val_and (pairIn 0 x') hg ha_and).mp (hap ▸ ha_0x') h hh_in
    obtain ⟨_, hh_xx'⟩ := (val_and (pairIn x x') hg ha_and).mp (hap ▸ ha_xx') h hh_in
    have hln_h : LNext C h a := ⟨⟨by omega, p, g, hg, hap, hh_in⟩, ha_live⟩
    have hh_nr : ¬ ReflTransGen (Next C) x'.val h :=
      chain_other_not_reach hTpred hnb_pred hln_pred hln_h hh_ne_pred
    have hh0 : val C (sing 0) h = true := by
      rw [← hh_0x']
      exact eval_eq_of_no_reach (v := x') (x := sing 0) (y := pairIn 0 x')
        (fun i hi => by simp only [sing, pairIn]; by_cases h0i : i = 0 <;> simp [hi, h0i]) h hh_nr
    have hhx : val C (sing x) h = true := by
      rw [← hh_xx']
      exact eval_eq_of_no_reach (v := x') (x := sing x) (y := pairIn x x')
        (fun i hi => by simp only [sing, pairIn]; by_cases hxi : i = x <;> simp [hi, hxi]) h hh_nr
    have hh_wide : isWide C h := ⟨0, x, hx0.symm, hh0, hhx⟩
    -- Prove `a < m`: if `a = m`, then `y'`'s predecessor `pred_y` of `m` is an input of `m` (`≠ pred` since `m` is first common wire!).
    -- Wait: since `m` has at most 2 inputs (`pred` and `h`), `pred_y = h`!
    -- But `pred_y` lies on `y'`'s chain so `¬ isWide pred_y`, contradicting `hh_wide`!
    have ha_lt_m : a < m := by
      apply lt_of_le_of_ne ha_le_m
      intro ham
      rcases hTy'.cases_tail with hy'eq | ⟨pred_y, hTpy, _, hln_py⟩
      · have hlt5 : y'.val < 5 := y'.isLt
        omega
      obtain ⟨_, p', g', hg', hap', hpy_in⟩ := hln_py.1
      have hp' : p' = p := by omega
      subst hp'
      rw [hg] at hg'; cases hg'
      have hpy_ne_pred : pred_y ≠ pred := fun e => by
        subst e; exact hm_min pred_y (by omega) ⟨hTpred, hTpy⟩
      have hlen : g.inputs.length ≤ 2 := (hC g (List.mem_of_getElem? hg)).2
      have hpy_eq_h : pred_y = h := by
        rcases hgi : g.inputs with _ | ⟨i₁, _ | ⟨i₂, _ | _⟩⟩
        · simp [hgi] at hpred_in
        · simp [hgi] at hpred_in hh_in; exact absurd (hh_in.trans hpred_in.symm) hh_ne_pred
        · simp only [hgi, List.mem_cons, List.not_mem_nil, or_false] at hpred_in hh_in hpy_in
          rcases hpred_in with rfl | rfl <;> rcases hh_in with rfl | rfl <;>
            rcases hpy_in with rfl | rfl <;> first | rfl | exact absurd rfl hh_ne_pred | exact absurd rfl hpy_ne_pred
        · simp [hgi] at hlen
      subst hpy_eq_h
      exact chain_not_wide hC hE hTpy (live_of_lnext hln_py) hh_wide
    -- Trace backwards from `h` along `{z | val (sing 0) z = true ∧ val (sing x) z = true}` to an OR gate `w`!
    have find_w : ∀ z, Live C z → val C (sing 0) z = true → val C (sing x) z = true →
        ∃ w, Live C w ∧ isOrGate C w ∧ val C (sing 0) w = true ∧
          Trace C (fun q => isWide C q) w z := by
      intro z
      induction z using Nat.strong_induction_on with
      | ind z ihz =>
        intro hzl hz0 hzx
        have hz_ge : 5 ≤ z := by
          by_contra hlt; push Not at hlt
          have hzeq : z = (⟨z, hlt⟩ : Fin 5).val := rfl
          rw [hzeq, val_input] at hz0 hzx
          simp only [sing, decide_eq_true_eq] at hz0 hzx
          exact hx0 (hzx.symm.trans hz0)
        set q := z - 5
        have hzq : z = 5 + q := by omega
        have hq_lt : q < C.gates.length := by
          have := (live_le_output hzl).trans_lt (output_bounds hE).2; omega
        obtain ⟨gq, hgq⟩ : ∃ gq, C.gates[q]? = some gq := ⟨C.gates[q], List.getElem?_eq_getElem hq_lt⟩
        rcases mono_op hC hgq with hop | hop
        · -- AND gate: if empty inputs, then `val (sing 0) z = true` & `val (sing x) z = true`,
          -- wait: can `gq.inputs = []` (constant true)? If `gq.inputs = []`, `inc z = 0`, so `slack ≥ 2`,
          -- contradicting `(liveGates C).card = 7` and `∑ Δ ≥ 3`!
          have hne_nil : gq.inputs ≠ [] := by
            intro hnil
            have hinc0 : inc C z = 0 := by
              rw [inc, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro r hr
              obtain ⟨⟨_, q', gq', hgq', hzq', hrin⟩, _⟩ := (mem_inWires hE).mp hr
              have : q' = q := by omega
              subst this; rw [hgq] at hgq'; cases hgq'; rw [hnil] at hrin; cases hrin
            have hslack2 : 2 ≤ ∑ j ∈ (living C).filter (fun w => 5 ≤ w), (2 - inc C j) := by
              have hzm : z ∈ (living C).filter (fun w => 5 ≤ w) := by
                simp only [Finset.mem_filter, mem_living hE]; exact ⟨hzl, hz_ge⟩
              calc 2 = 2 - inc C z := by omega
                _ ≤ ∑ j ∈ (living C).filter (fun w => 5 ≤ w), (2 - inc C j) :=
                    Finset.single_le_sum (f := fun j => 2 - inc C j) (fun _ _ => Nat.zero_le _) hzm
            omega
          obtain ⟨r, rest, hri⟩ := List.exists_cons_of_ne_nil hne_nil
          have hrin : r ∈ gq.inputs := by rw [hri]; exact List.mem_cons_self
          obtain ⟨hrlt, hr0⟩ := (val_and (sing 0) hgq hop).mp (hzq ▸ hz0) r hrin
          obtain ⟨_, hrx⟩ := (val_and (sing x) hgq hop).mp (hzq ▸ hzx) r hrin
          have hln_r : LNext C r z := ⟨⟨by omega, q, gq, hgq, hzq, hrin⟩, hzl⟩
          obtain ⟨w, hwl, hwor, hw0, hTw⟩ := ihz r (by omega) (live_of_lnext hln_r) hr0 hrx
          exact ⟨w, hwl, hwor, hw0, hTw.tail ⟨⟨0, x, hx0.symm, hr0, hrx⟩, hln_r⟩⟩
        · exact ⟨z, hzl, ⟨q, gq, hgq, hzq, hop⟩, hz0, ReflTransGen.refl⟩
    obtain ⟨w, hwl, hwor, hw0, hTw⟩ := find_w h (live_of_lnext hln_h) hh0 hhx
    exact ⟨a, w, ha_lt_m, ha.1, hwl, hwor, hw0, hTw.tail ⟨hh_wide, hln_h⟩⟩
  obtain ⟨a₁, w₁, ha₁_lt, hTa₁, hw₁_live, hw₁_or, hw₁_0, hTw₁⟩ :=
    find_wide_or u u' v' hm.1 hm.2 (fun z hz => Nat.find_min hex_m hz) huv'_ne hu0 huu'_ne h0u' huu' hm_u'0
  obtain ⟨a₂, w₂, ha₂_lt, hTa₂, hw₂_live, hw₂_or, hw₂_0, hTw₂⟩ :=
    find_wide_or v v' u' hm.2 hm.1 (fun z hz h => Nat.find_min hex_m hz ⟨h.2, h.1⟩) huv'_ne.symm hv0 hvv'_ne h0v' hvv' hm_v'0
  -- Prove `w₁ ≠ w₂`! Because every wire strictly before `a₁` on `hTw₁` is wide (hence `¬ Branch`),
  -- and every wire strictly before `a₂` on `hTw₂` is wide (hence `¬ Branch`),
  -- while `a₁` and `a₂` are NOT wide (by Claim 1) and `a₁ ≠ a₂` (since both `< m` and `m` is first common wire)!
  have ha12_ne : a₁ ≠ a₂ := fun e => by
    subst e; exact Nat.find_min hex_m ha₁_lt ⟨hTa₁, hTa₂⟩
  have hw12_ne : w₁ ≠ w₂ := by
    intro heq
    subst heq
    -- Convert `Trace isWide` to `Trace (¬ Branch)`!
    have to_nb : ∀ z, Trace C (fun q => isWide C q) w₁ z → Trace C (fun q => ¬ Branch C q) w₁ z := by
      intro z hz
      induction hz with
      | refl => exact ReflTransGen.refl
      | tail _ h ih => exact ih.tail ⟨hwide_not_branch _ (live_of_lnext h.2) h.1, h.2⟩
    have h1 := to_nb a₁ hTw₁
    have h2 := to_nb a₂ hTw₂
    -- Since `a₁ ≠ a₂`, WLOG `a₁ < a₂` or `a₂ < a₁`, so the smaller one lies strictly before the larger one,
    -- which forces the smaller one to be WIDE — contradicting Claim 1!
    have head_wide : ∀ x y, Trace C (fun q => isWide C q) x y → x < y → isWide C x := by
      intro x y hxy hlt
      rcases hxy.cases_head with rfl | ⟨_, hstep, _⟩
      · omega
      · exact hstep.1
    have wide_along : ∀ {w z₁ z₂}, Trace C (fun q => isWide C q) w z₁ →
        Trace C (fun q => isWide C q) w z₂ → z₁ < z₂ → isWide C z₁ := by
      intro w z₁ z₂ hT1 hT2 hlt
      induction hT2 using ReflTransGen.head_induction_on generalizing z₁ with
      | refl => have := trace_le hT1; omega
      | @head x y hxy hyz ih =>
        rcases hT1.cases_head with rfl | ⟨y', hxy', hy'z⟩
        · exact hxy.1
        · have hy : y' = y := trace_lnext_unique (hwide_not_branch _ (live_of_lnext hxy.2) hxy.1) hxy'.2 hxy.2
          subst hy
          exact ih hy'z hlt
    have ha₁_live : Live C a₁ := by
      rcases hTw₁.cases_tail with rfl | ⟨_, _, _, hln⟩
      · exact hw₁_live
      · exact hln.2
    have ha₂_live : Live C a₂ := by
      rcases hTw₂.cases_tail with rfl | ⟨_, _, _, hln⟩
      · exact hw₂_live
      · exact hln.2
    rcases lt_or_gt_of_ne ha12_ne with hlt | hlt
    · exact chain_not_wide hC hE hTa₁ ha₁_live (wide_along hTw₁ hTw₂ hlt)
    · exact chain_not_wide hC hE hTa₂ ha₂_live (wide_along hTw₂ hTw₁ hlt)
  -- Convert `w₁, w₂` to gate indices `j₁, j₂ ∈ liveGates C` disjoint from `liveAnd C` and `liveOrZero C`!
  obtain ⟨j₁, g₁, hg₁, hw₁_eq, hop₁⟩ := hw₁_or
  obtain ⟨j₂, g₂, hg₂, hw₂_eq, hop₂⟩ := hw₂_or
  have hj12_ne : j₁ ≠ j₂ := by omega
  have hj₁_mem : j₁ ∈ liveGates C := by
    simp only [liveGates, Finset.mem_filter, Finset.mem_range]
    exact ⟨(List.getElem?_eq_some_iff.mp hg₁).1, hw₁_eq ▸ hw₁_live⟩
  have hj₂_mem : j₂ ∈ liveGates C := by
    simp only [liveGates, Finset.mem_filter, Finset.mem_range]
    exact ⟨(List.getElem?_eq_some_iff.mp hg₂).1, hw₂_eq ▸ hw₂_live⟩
  have hdisj_AO : Disjoint (liveAnd C) (liveOrZero C) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [mem_liveAnd, mem_liveOrZero, isAndGate, isOrGate] at h1 h2
    obtain ⟨p1, g1, hg1, hp1, hop1⟩ := h1.2
    obtain ⟨p2, g2, hg2, hp2, hop2⟩ := h2.2.1
    have : p1 = p2 := by omega
    subst this; rw [hg1] at hg2; cases hg2; rw [hop1] at hop2; cases hop2
  have hdisj_W : Disjoint (liveAnd C ∪ liveOrZero C) ({j₁, j₂} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    simp only [Finset.mem_union, mem_liveAnd, mem_liveOrZero, isAndGate, isOrGate] at h1
    rcases h2 with hj1 | hj2
    · subst j
      rcases h1 with h1 | h1
      · obtain ⟨p1, g', hg', hp1, hop'⟩ := h1.2
        have hp1e : p1 = j₁ := by omega
        subst hp1e; rw [hg₁] at hg'; cases hg'; rw [hop₁] at hop'; cases hop'
      · rw [← hw₁_eq, hw₁_0] at h1; exact Bool.noConfusion h1.2.2
    · subst j
      rcases h1 with h1 | h1
      · obtain ⟨p1, g', hg', hp1, hop'⟩ := h1.2
        have hp1e : p1 = j₂ := by omega
        subst hp1e; rw [hg₂] at hg'; cases hg'; rw [hop₂] at hop'; cases hop'
      · rw [← hw₂_eq, hw₂_0] at h1; exact Bool.noConfusion h1.2.2
  have hsub : (liveAnd C ∪ liveOrZero C) ∪ ({j₁, j₂} : Finset ℕ) ⊆ liveGates C := by
    refine Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) ?_
    intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl; exact hj₁_mem; exact hj₂_mem
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj_W, Finset.card_union_of_disjoint hdisj_AO,
    Finset.card_pair hj12_ne] at hcard
  have hA3 := three_and_gates hC hE
  have hO3 := three_or_zero_gates hC hE
  omega

/-! ## Section 4: Tight-cut tree machinery, 2-wide-OR lemma, and Case `|D_L| = 0` -/

def TightCut (C : Circuit) (B : Finset ℕ) : Prop :=
  B ⊆ (living C).erase C.output ∧
  (∀ b ∈ B, outdeg C b = 2) ∧
  (∀ w ∈ (living C).erase C.output, w ∉ B → outdeg C w = 1) ∧
  (∀ j ∈ (living C).filter (fun w => 5 ≤ w), inc C j = 2)

theorem tightCut_of_le {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hBsub : B ⊆ (living C).erase C.output)
    (hBbr : ∀ b ∈ B, Branch C b) (hcard : (liveGates C).card ≤ 4 + B.card) :
    TightCut C B := by
  classical
  have hbud := live_budget_exact hC hE
  set W' := (living C).erase C.output
  set GW := (living C).filter (fun w => 5 ≤ w)
  have hsplit : (∑ a ∈ W', (outdeg C a - 1)) =
      (∑ a ∈ B, (outdeg C a - 1)) + (∑ a ∈ W' \ B, (outdeg C a - 1)) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hBsub]
  have hBsum : B.card ≤ ∑ a ∈ B, (outdeg C a - 1) := by
    calc B.card = ∑ _a ∈ B, 1 := by simp
      _ ≤ ∑ a ∈ B, (outdeg C a - 1) := Finset.sum_le_sum fun a ha => by
          have := (branch_iff_two_le_outdeg hE a).mp (hBbr a ha); omega
  have hBsum_eq : (∑ a ∈ B, (outdeg C a - 1)) = B.card := by omega
  have hrest_zero : (∑ a ∈ W' \ B, (outdeg C a - 1)) = 0 := by omega
  have hslack_zero : (∑ j ∈ GW, (2 - inc C j)) = 0 := by omega
  refine ⟨hBsub, ?_, ?_, ?_⟩
  · intro b hb
    have hge2 := (branch_iff_two_le_outdeg hE b).mp (hBbr b hb)
    have hle : outdeg C b - 1 ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h1 : B.card - 1 ≤ ∑ a ∈ B.erase b, (outdeg C a - 1) := by
        calc B.card - 1 = (B.erase b).card := (Finset.card_erase_of_mem hb).symm
          _ = ∑ _a ∈ B.erase b, 1 := by simp
          _ ≤ ∑ a ∈ B.erase b, (outdeg C a - 1) := Finset.sum_le_sum fun a ha => by
              have := (branch_iff_two_le_outdeg hE a).mp (hBbr a (Finset.mem_of_mem_erase ha)); omega
      have h2 := Finset.add_sum_erase B (fun a => outdeg C a - 1) hb
      have hpos := Finset.card_pos.mpr ⟨b, hb⟩
      omega
    omega
  · intro w hw hwB
    have hw_sdiff : w ∈ W' \ B := Finset.mem_sdiff.mpr ⟨hw, hwB⟩
    have h0 : outdeg C w - 1 = 0 := (Finset.sum_eq_zero_iff.mp hrest_zero) w hw_sdiff
    obtain ⟨hne, hwl⟩ := Finset.mem_erase.mp hw
    have hpos := live_ne_output_outdeg_pos hE ((mem_living hE).mp hwl) hne
    omega
  · intro j hj
    have h0 : 2 - inc C j = 0 := (Finset.sum_eq_zero_iff.mp hslack_zero) j hj
    have hle := inc_le_two hC hE j
    omega

theorem tightCut_not_branch {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ}
    (hT : TightCut C B) {w : ℕ} (hwl : Live C w) (hwB : w ∉ B) : ¬ Branch C w := by
  intro hwb
  have h2 := (branch_iff_two_le_outdeg hE w).mp hwb
  by_cases hwo : w = C.output
  · rw [hwo, outdeg_output hE] at h2; omega
  · have h1 := hT.2.2.1 w (Finset.mem_erase.mpr ⟨hwo, (mem_living hE).mpr hwl⟩) hwB
    omega

theorem tightCut_gate_inputs {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) {B : Finset ℕ}
    (hT : TightCut C B) {w : ℕ} (hwl : Live C w) (hw5 : 5 ≤ w) :
    ∃ p g a b, C.gates[p]? = some g ∧ w = 5 + p ∧ a ≠ b ∧
      LNext C a w ∧ LNext C b w ∧ (∀ i ∈ g.inputs, i = a ∨ i = b) ∧
      a ∈ g.inputs ∧ b ∈ g.inputs := by
  have hlt := (live_le_output hwl).trans_lt (output_bounds hE).2
  set p := w - 5
  have hwp : w = 5 + p := by omega
  have hp_lt : p < C.gates.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem hp_lt⟩
  have hinc2 : inc C w = 2 := hT.2.2.2 w (by simp only [Finset.mem_filter, mem_living hE]; exact ⟨hwl, hw5⟩)
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hinc2
  have ha_ln : LNext C a w := (mem_inWires hE).mp (by rw [hpair]; simp)
  have hb_ln : LNext C b w := (mem_inWires hE).mp (by rw [hpair]; simp)
  have hin : ∀ x, LNext C x w → x ∈ g.inputs := by
    rintro x ⟨⟨_, p', g', hg', hwp', hxin⟩, _⟩
    have hp' : p' = p := by omega
    subst p'; rw [hg] at hg'; cases hg'; exact hxin
  have ha_in : a ∈ g.inputs := hin a ha_ln
  have hb_in : b ∈ g.inputs := hin b hb_ln
  have hlen : g.inputs.length ≤ 2 := (hC g (List.mem_of_getElem? hg)).2
  have hall : ∀ i ∈ g.inputs, i = a ∨ i = b := by
    rcases hgi : g.inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · simp [hgi] at ha_in
    · simp [hgi] at ha_in hb_in; exact absurd (ha_in.trans hb_in.symm) hab
    · simp only [hgi, List.mem_cons, List.not_mem_nil, or_false] at ha_in hb_in ⊢
      intro i hi
      rcases ha_in with rfl | rfl <;> rcases hb_in with rfl | rfl <;>
        rcases hi with rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hab
    · simp [hgi] at hlen
  exact ⟨p, g, a, b, hg, hwp, hab, ha_ln, hb_ln, hall, ha_in, hb_in⟩

open Classical in
noncomputable def Internal (C : Circuit) (B : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (living C).filter (fun u => u ∉ B ∧ Trace C (fun z => z ∉ B) u r)

open Classical in
noncomputable def LeafEdges (C : Circuit) (B : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (B ×ˢ Internal C B r).filter (fun p => LNext C p.1 p.2)

open Classical in
noncomputable def AllBEdges (C : Circuit) (B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (B ×ˢ living C).filter (fun p => LNext C p.1 p.2)

open Classical in
noncomputable def Leaves (C : Circuit) (B : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (LeafEdges C B r).image Prod.fst

theorem mem_Internal {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} {r u : ℕ} :
    u ∈ Internal C B r ↔ Live C u ∧ u ∉ B ∧ Trace C (fun z => z ∉ B) u r := by
  simp only [Internal, Finset.mem_filter, mem_living hE]

theorem mem_LeafEdges {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} {r : ℕ} {p : ℕ × ℕ} :
    p ∈ LeafEdges C B r ↔ p.1 ∈ B ∧ p.2 ∈ Internal C B r ∧ LNext C p.1 p.2 := by
  simp only [LeafEdges, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem mem_AllBEdges {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ AllBEdges C B ↔ p.1 ∈ B ∧ Live C p.2 ∧ LNext C p.1 p.2 := by
  simp only [AllBEdges, Finset.mem_filter, Finset.mem_product, mem_living hE, and_assoc]

theorem leafEdges_subset_allBEdges {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} {r : ℕ} :
    LeafEdges C B r ⊆ AllBEdges C B := by
  intro p hp
  rw [mem_LeafEdges hE] at hp
  rw [mem_AllBEdges hE]
  exact ⟨hp.1, ((mem_Internal hE).mp hp.2.1).1, hp.2.2⟩

theorem allBEdges_card {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B) :
    (AllBEdges C B).card = 2 * B.card := by
  classical
  have heq : AllBEdges C B = B.biUnion (fun b => (readers C b).image (fun j => (b, j))) := by
    ext ⟨b, j⟩
    simp only [mem_AllBEdges hE, Finset.mem_biUnion, Finset.mem_image, mem_readers hE]
    constructor
    · rintro ⟨hb, _, hln⟩; exact ⟨b, hb, j, hln, rfl⟩
    · rintro ⟨b', hb', j', hln, heq'⟩
      cases heq'
      exact ⟨hb', hln.2, hln⟩
  rw [heq, Finset.card_biUnion]
  · calc ∑ b ∈ B, ((readers C b).image (fun j => (b, j))).card
        = ∑ b ∈ B, (readers C b).card := Finset.sum_congr rfl fun b _ =>
            Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      _ = ∑ _b ∈ B, 2 := Finset.sum_congr rfl fun b hb => hT.2.1 b hb
      _ = 2 * B.card := by simp [Nat.mul_comm]
  · intro b₁ _ b₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨_, _, rfl⟩ := h1
    obtain ⟨_, _, h⟩ := h2
    exact hne (Prod.mk.inj h).1.symm

def fiber (S : Finset (ℕ × ℕ)) (b : ℕ) : Finset (ℕ × ℕ) :=
  S.filter (fun p => p.1 = b)

theorem mem_fiber {S : Finset (ℕ × ℕ)} {b : ℕ} {p : ℕ × ℕ} :
    p ∈ fiber S b ↔ p ∈ S ∧ p.1 = b := Finset.mem_filter

/-- For any `b ∈ B`, at most 2 edges in `AllBEdges C B` start at `b`. -/
theorem allBEdges_fiber_card {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {b : ℕ} (hb : b ∈ B) :
    (fiber (AllBEdges C B) b).card = 2 := by
  classical
  have heq : fiber (AllBEdges C B) b = (readers C b).image (fun j => (b, j)) := by
    ext ⟨a, j⟩
    simp only [fiber, Finset.mem_filter, mem_AllBEdges hE, Finset.mem_image, mem_readers hE]
    constructor
    · rintro ⟨⟨_, _, hln⟩, rfl⟩; exact ⟨j, hln, rfl⟩
    · rintro ⟨j', hln, h⟩; cases h; exact ⟨⟨hb, hln.2, hln⟩, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
  exact hT.2.1 b hb

theorem freq_le_two {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {H : Finset ℕ} (hdisj : (H : Set ℕ).PairwiseDisjoint (fun h => LeafEdges C B h))
    {b : ℕ} (hbB : b ∈ B) [DecidablePred (fun h => b ∈ Leaves C B h)] :
    (H.filter (fun h => b ∈ Leaves C B h)).card ≤ 2 := by
  set Hb := H.filter (fun h => b ∈ Leaves C B h)
  have hdisj_b : (Hb : Set ℕ).PairwiseDisjoint (fun h => fiber (LeafEdges C B h) b) := by
    intro h₁ h1 h₂ h2 hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact Finset.disjoint_left.mp
      (hdisj (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).1 (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).1 hne)
      (mem_fiber.mp hp1).1 (mem_fiber.mp hp2).1
  calc Hb.card = ∑ _h ∈ Hb, 1 := by simp
    _ ≤ ∑ h ∈ Hb, (fiber (LeafEdges C B h) b).card :=
        Finset.sum_le_sum fun h hh => Nat.succ_le_iff.mpr (Finset.card_pos.mpr (by
          have hbL : b ∈ Leaves C B h := (Finset.mem_filter.mp hh).2
          obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp hbL
          exact ⟨p, mem_fiber.mpr ⟨hp, hp1⟩⟩))
    _ = (Hb.biUnion (fun h => fiber (LeafEdges C B h) b)).card :=
        (Finset.card_biUnion hdisj_b).symm
    _ ≤ (fiber (AllBEdges C B) b).card := Finset.card_le_card (by
        intro p hp
        obtain ⟨h, _, hp'⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨hpL, hp1⟩ := mem_fiber.mp hp'
        exact mem_fiber.mpr ⟨leafEdges_subset_allBEdges hE hpL, hp1⟩)
    _ = 2 := allBEdges_fiber_card hE hT hbB

/-- Disjointness of `Internal` sets for incomparable roots outside `B`. -/
theorem internal_disjoint {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {r₁ r₂ : ℕ} (h12 : ¬ Trace C (fun z => z ∉ B) r₁ r₂)
    (h21 : ¬ Trace C (fun z => z ∉ B) r₂ r₁) :
    Disjoint (Internal C B r₁) (Internal C B r₂) := by
  classical
  rw [Finset.disjoint_left]
  intro u₀ hu1 hu2
  have hne : (Internal C B r₁ ∩ Internal C B r₂).Nonempty := ⟨u₀, Finset.mem_inter.mpr ⟨hu1, hu2⟩⟩
  obtain ⟨u, huM, hmax⟩ := Finset.exists_max_image (Internal C B r₁ ∩ Internal C B r₂) id hne
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp huM
  obtain ⟨hul, huB, huT1⟩ := (mem_Internal hE).mp h1
  obtain ⟨_, _, huT2⟩ := (mem_Internal hE).mp h2
  rcases huT1.cases_head with rfl | ⟨j₁, hstep1, hj1r1⟩
  · exact h12 huT2
  rcases huT2.cases_head with rfl | ⟨j₂, hstep2, hj2r2⟩
  · exact h21 (ReflTransGen.head hstep1 hj1r1)
  have hnb := tightCut_not_branch hE hT hul huB
  have hjeq : j₁ = j₂ := trace_lnext_unique hnb hstep1.2 hstep2.2
  subst hjeq
  -- Is `j₁ ∈ B`? If `j₁ ∈ B`, then `hj1r1` MUST be `refl` (so `j₁ = r₁`) and `hj2r2` MUST be `refl` (so `j₁ = r₂`),
  -- giving `r₁ = r₂`, contradicting `h12`!
  by_cases hjB : j₁ ∈ B
  · rcases hj1r1.cases_head with rfl | ⟨_, hbad, _⟩
    · rcases hj2r2.cases_head with rfl | ⟨_, hbad2, _⟩
      · exact h12 ReflTransGen.refl
      · exact hbad2.1 hjB
    · exact hbad.1 hjB
  · have hj_mem : j₁ ∈ Internal C B r₁ ∩ Internal C B r₂ := Finset.mem_inter.mpr
      ⟨(mem_Internal hE).mpr ⟨hstep1.2.2, hjB, hj1r1⟩, (mem_Internal hE).mpr ⟨hstep1.2.2, hjB, hj2r2⟩⟩
    have hle : j₁ ≤ u := hmax j₁ hj_mem
    have hlt := hstep1.2.1.1
    omega

theorem leafEdges_disjoint {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {r₁ r₂ : ℕ} (h12 : ¬ Trace C (fun z => z ∉ B) r₁ r₂)
    (h21 : ¬ Trace C (fun z => z ∉ B) r₂ r₁) :
    Disjoint (LeafEdges C B r₁) (LeafEdges C B r₂) := by
  rw [Finset.disjoint_left]
  intro p h1 h2
  rw [mem_LeafEdges hE] at h1 h2
  exact Finset.disjoint_left.mp (internal_disjoint hE hT h12 h21) h1.2.1 h2.2.1

/-- Monotonicity over `Leaves C B r` when `Internal C B r` contains no input wires `< 5`. -/
theorem internal_mono {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) {B : Finset ℕ}
    (hT : TightCut C B) {r : ℕ} (hnoin : ∀ u ∈ Internal C B r, 5 ≤ u)
    {x y : Fin 5 → Bool} (hxy : ∀ b ∈ Leaves C B r, val C x b = true → val C y b = true) :
    ∀ u ∈ Internal C B r, val C x u = true → val C y u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hux
    obtain ⟨hul, huB, huTr⟩ := (mem_Internal hE).mp hu
    have hu5 := hnoin u hu
    obtain ⟨p, g, a, b, hg, hup, hab, hlna, hlnb, hall, hain, hbin⟩ := tightCut_gate_inputs hC hE hT hul hu5
    have hstep : ∀ i, LNext C i u → val C x i = true → val C y i = true := by
      intro i hlni hix
      by_cases hiB : i ∈ B
      · exact hxy i (Finset.mem_image.mpr ⟨(i, u), (mem_LeafEdges hE).mpr ⟨hiB, hu, hlni⟩, rfl⟩) hix
      · have hiI : i ∈ Internal C B r :=
          (mem_Internal hE).mpr ⟨live_of_lnext hlni, hiB, ReflTransGen.head ⟨hiB, hlni⟩ huTr⟩
        exact ih i hlni.1.1 hiI hix
    rw [hup] at hux ⊢
    rcases mono_op hC hg with hop | hop
    · rw [val_and y hg hop]
      rw [val_and x hg hop] at hux
      intro i hi
      rcases hall i hi with hia | hib
      · subst i; exact ⟨by have := hlna.1.1; omega, hstep a hlna (hux a hain).2⟩
      · subst i; exact ⟨by have := hlnb.1.1; omega, hstep b hlnb (hux b hbin).2⟩
    · rw [val_or y hg hop]
      rw [val_or x hg hop] at hux
      obtain ⟨i, hi, hilt, hix⟩ := hux
      rcases hall i hi with hia | hib
      · subst i; exact ⟨a, hain, hilt, hstep a hlna hix⟩
      · subst i; exact ⟨b, hbin, hilt, hstep b hlnb hix⟩

/-- If all leaves in `Leaves C B r` evaluate to `false` on `x`, then every wire in `Internal C B r` evaluates to `false` on `x`. -/
theorem internal_false {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) {B : Finset ℕ}
    (hT : TightCut C B) {r : ℕ} (hnoin : ∀ u ∈ Internal C B r, 5 ≤ u)
    {x : Fin 5 → Bool} (hxf : ∀ b ∈ Leaves C B r, val C x b = false) :
    ∀ u ∈ Internal C B r, val C x u = false := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    obtain ⟨hul, huB, huTr⟩ := (mem_Internal hE).mp hu
    have hu5 := hnoin u hu
    obtain ⟨p, g, a, b, hg, hup, _, hlna, hlnb, hall, hain, hbin⟩ := tightCut_gate_inputs hC hE hT hul hu5
    have hstep : ∀ i, LNext C i u → val C x i = false := by
      intro i hlni
      by_cases hiB : i ∈ B
      · exact hxf i (Finset.mem_image.mpr ⟨(i, u), (mem_LeafEdges hE).mpr ⟨hiB, hu, hlni⟩, rfl⟩)
      · exact ih i hlni.1.1 ((mem_Internal hE).mpr ⟨live_of_lnext hlni, hiB, ReflTransGen.head ⟨hiB, hlni⟩ huTr⟩)
    rw [Bool.eq_false_iff]
    intro hux
    rw [hup] at hux
    rcases mono_op hC hg with hop | hop
    · have ha := ((val_and x hg hop).mp hux a hain).2
      rw [hstep a hlna] at ha; cases ha
    · obtain ⟨i, hi, _, hix⟩ := (val_or x hg hop).mp hux
      rcases hall i hi with hia | hib
      · subst i; rw [hstep a hlna] at hix; cases hix
      · subst i; rw [hstep b hlnb] at hix; cases hix

/-- If `Internal C B r` is nonempty and contains no inputs `< 5`, then `LeafEdges C B r` is nonempty. -/
theorem leafEdges_nonempty {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) {B : Finset ℕ}
    (hT : TightCut C B) {r : ℕ} (hrl : Live C r) (hrB : r ∉ B)
    (hnoin : ∀ u ∈ Internal C B r, 5 ≤ u) :
    (LeafEdges C B r).Nonempty := by
  have hrI : r ∈ Internal C B r := (mem_Internal hE).mpr ⟨hrl, hrB, ReflTransGen.refl⟩
  obtain ⟨u, huI, hmin⟩ := Finset.exists_min_image (Internal C B r) id ⟨r, hrI⟩
  obtain ⟨hul, _, huTr⟩ := (mem_Internal hE).mp huI
  obtain ⟨_, _, a, _, _, _, _, hlna, _, _, _, _⟩ := tightCut_gate_inputs hC hE hT hul (hnoin u huI)
  have haB : a ∈ B := by
    by_contra ha_notB
    have haI : a ∈ Internal C B r :=
      (mem_Internal hE).mpr ⟨live_of_lnext hlna, ha_notB, ReflTransGen.head ⟨ha_notB, hlna⟩ huTr⟩
    have hle : u ≤ a := hmin a haI
    have hlt := hlna.1.1
    omega
  exact ⟨(a, u), (mem_LeafEdges hE).mpr ⟨haB, huI, hlna⟩⟩

/-- Every `b ∈ B` on `v`'s chain with `b ≠ v.val` consumes an edge in `AllBEdges C B` that cannot
    belong to `LeafEdges C B r` for any `r` whose forward path to `C.output` avoids `B`. -/
theorem non_input_branch_uses_edge {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    (h_input_sep : ∀ w : Fin 5, ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z →
      ∀ w' : Fin 5, Trace C (fun q => q ∉ B) w'.val z → w' = w)
    {v : Fin 5} {b : ℕ} (hbB : b ∈ B) (hvb : Trace C (fun q => q ∉ B) v.val b)
    (hbne : b ≠ v.val) :
    ∃ p ∈ AllBEdges C B,
      (p.2 = b ∨ (p.2 ∉ B ∧ Trace C (fun q => q ∉ B) p.2 b)) ∧
      (∀ r, r ∉ B → Trace C (fun q => q ∉ B) r C.output → p ∉ LeafEdges C B r) ∧
      (∃ u₁ u₂, u₁ ≠ u₂ ∧ LNext C u₁ b ∧ LNext C u₂ b ∧
        Trace C (fun q => q ∉ B) v.val u₁ ∧ u₁ ∉ B ∧
        (u₂ = p.1 ∧ p.2 = b ∨ u₂ ∉ B ∧ p ∈ LeafEdges C B u₂ ∧
          ∀ q ∈ Internal C B u₂, 5 ≤ q)) := by
  have hbl : Live C b := ((mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hbB)))
  have hb5 : 5 ≤ b := by
    by_contra hlt; push Not at hlt
    have hv_eq : (⟨b, hlt⟩ : Fin 5) = v := h_input_sep v b hbB hvb ⟨b, hlt⟩ ReflTransGen.refl
    exact hbne (congrArg Fin.val hv_eq)
  rcases hvb.cases_tail with heq | ⟨u₁, hTu₁, hu₁B, hln1⟩
  · exact absurd heq hbne
  obtain ⟨_, _, a, c, _, _, hac, hlna, hlnc, _, _, _⟩ := tightCut_gate_inputs hC hE hT hbl hb5
  -- Pick `u₂ ≠ u₁` among `{a, c}`!
  have hu2_ex : ∃ u₂, u₂ ≠ u₁ ∧ LNext C u₂ b := by
    by_cases h1 : a = u₁
    · exact ⟨c, by omega, hlnc⟩
    · exact ⟨a, h1, hlna⟩
  obtain ⟨u₂, hu21, hln2⟩ := hu2_ex
  -- Helper: no edge `(x, y)` with `y = b ∨ (y ∉ B ∧ Trace (· ∉ B) y b)` lies in `LeafEdges C B r` when `Trace (· ∉ B) r C.output`.
  have not_in_leaf : ∀ p : ℕ × ℕ, (p.2 = b ∨ (p.2 ∉ B ∧ Trace C (fun q => q ∉ B) p.2 b)) →
      ∀ r, r ∉ B → Trace C (fun q => q ∉ B) r C.output → p ∉ LeafEdges C B r := by
    intro p hp r hrB hrOut hpL
    rw [mem_LeafEdges hE] at hpL
    obtain ⟨_, hpI, _⟩ := hpL
    obtain ⟨hyl, hyB, hyTr⟩ := (mem_Internal hE).mp hpI
    rcases hp with hyeq | ⟨_, hyTb⟩
    · exact hyB (hyeq ▸ hbB)
    · -- `p.2` has both `Trace (· ∉ B) p.2 b` and `Trace (· ∉ B) p.2 r`, and `Trace (· ∉ B) r C.output`!
      -- Combining gives `Trace (· ∉ B) p.2 C.output` and `Trace (· ∉ B) p.2 b`, with `b ∈ B` and `b < C.output`.
      have hyOut : Trace C (fun q => q ∉ B) p.2 C.output := hyTr.trans hrOut
      -- Since every wire `∉ B` has `¬ Branch`, `Trace (· ∉ B)` is deterministic:
      have det : ∀ {x y z}, Trace C (fun q => q ∉ B) x y → Trace C (fun q => q ∉ B) x z →
          y ≤ z → Trace C (fun q => q ∉ B) y z := by
        intro x y z hxy hxz hle
        induction hxy using ReflTransGen.head_induction_on with
        | refl => exact hxz
        | @head s t hst hty ih =>
          rcases hxz.cases_head with rfl | ⟨t', hst', ht'z⟩
          · have := trace_le hty; have := hst.2.1.1; omega
          · have hteq : t' = t := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hst.2) hst.1) hst'.2 hst.2
            subst hteq
            exact ih ht'z
      have hbOut : Trace C (fun q => q ∉ B) b C.output := det hyTb hyOut (live_le_output hbl)
      rcases hbOut.cases_head with hbo | ⟨_, hstep, _⟩
      · exact (Finset.mem_erase.mp (hT.1 hbB)).1 hbo
      · exact hstep.1 hbB
  by_cases hu2B : u₂ ∈ B
  · refine ⟨(u₂, b), (mem_AllBEdges hE).mpr ⟨hu2B, hbl, hln2⟩, Or.inl rfl,
      not_in_leaf (u₂, b) (Or.inl rfl), u₁, u₂, hu21.symm, hln1, hln2, hTu₁, hu₁B, Or.inl ⟨rfl, rfl⟩⟩
  · -- Show `∀ q ∈ Internal C B u₂, 5 ≤ q`!
    have hnoin : ∀ q ∈ Internal C B u₂, 5 ≤ q := by
      intro q hq
      obtain ⟨_, _, hqTu2⟩ := (mem_Internal hE).mp hq
      by_contra hlt; push Not at hlt
      let w' : Fin 5 := ⟨q, hlt⟩
      have hw'b : Trace C (fun z => z ∉ B) w'.val b := hqTu2.tail ⟨hu2B, hln2⟩
      have hw'v : w' = v := h_input_sep v b hbB hvb w' hw'b
      -- So `v.val` reaches BOTH `u₁` (with `LNext u₁ b`) and `u₂` (with `LNext u₂ b`) via `Trace (· ∉ B)`!
      -- Since `Trace (· ∉ B)` is deterministic (`¬ Branch` at every step), `u₁` and `u₂` cannot both precede `b`!
      have hvTu2 : Trace C (fun z => z ∉ B) v.val u₂ := by rw [← hw'v]; exact hqTu2
      have hnb_all : ∀ z, z ∉ B → Live C z → ¬ Branch C z := fun z hz hzl => tightCut_not_branch hE hT hzl hz
      have to_nb : ∀ {x y}, Trace C (fun z => z ∉ B) x y → Trace C (fun z => ¬ Branch C z) x y := by
        intro x y hxy
        induction hxy with
        | refl => exact ReflTransGen.refl
        | tail _ h ih => exact ih.tail ⟨hnb_all _ h.1 (live_of_lnext h.2), h.2⟩
      exact chain_other_not_reach (to_nb hTu₁) (hnb_all u₁ hu₁B (live_of_lnext hln1)) hln1 hln2 hu21
        (by
          have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
            intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ h ih => exact ih.tail h.2.1
          exact hstep hvTu2)
    obtain ⟨p, hp⟩ := leafEdges_nonempty hC hE hT (live_of_lnext hln2) hu2B hnoin
    have hp_all := leafEdges_subset_allBEdges hE hp
    obtain ⟨_, hpI, _⟩ := (mem_LeafEdges hE).mp hp
    obtain ⟨_, hp2B, hp2Tu2⟩ := (mem_Internal hE).mp hpI
    have hp2Tb : Trace C (fun q => q ∉ B) p.2 b := hp2Tu2.tail ⟨hu2B, hln2⟩
    refine ⟨p, hp_all, Or.inr ⟨hp2B, hp2Tb⟩, not_in_leaf p (Or.inr ⟨hp2B, hp2Tb⟩),
      u₁, u₂, hu21.symm, hln1, hln2, hTu₁, hu₁B, Or.inr ⟨hu2B, hp, hnoin⟩⟩

/-- 2-Wide-OR Lemma: the bowtie cannot be the AND of two wide wires. -/
theorem two_wide_or_ne_bowtie {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {h₁ h₂ : ℕ} (hw₁ : isWide C h₁) (hw₂ : isWide C h₂)
    (heq : ∀ x, val C x C.output = true ↔ val C x h₁ = true ∧ val C x h₂ = true) : False := by
  have h0 : val C (sing 0) h₁ = false ∨ val C (sing 0) h₂ = false := by
    by_contra hc; push Not at hc
    have h1t : val C (sing 0) h₁ = true := Bool.eq_true_of_not_eq_false hc.1
    have h2t : val C (sing 0) h₂ = true := Bool.eq_true_of_not_eq_false hc.2
    have hout := (heq (sing 0)).mpr ⟨h1t, h2t⟩
    rw [bowtie_sing hE 0] at hout; cases hout
  suffices aux : ∀ a b : ℕ, isWide C a → isWide C b →
      (∀ x, val C x C.output = true ↔ val C x a = true ∧ val C x b = true) →
      val C (sing 0) a = false → False by
    rcases h0 with h01 | h02
    · exact aux h₁ h₂ hw₁ hw₂ heq h01
    · exact aux h₂ h₁ hw₂ hw₁ (fun x => by rw [heq x, and_comm]) h02
  intro a b hwa hwb hab ha0
  -- Since `b` is wide, `b` is true on some singleton `u ≠ 0`!
  obtain ⟨u₁, u₂, hu12, hbu1, hbu2⟩ := hwb
  obtain ⟨u, hu0, hbu⟩ : ∃ u : Fin 5, u ≠ 0 ∧ val C (sing u) b = true := by
    by_cases h1 : u₁ = 0
    · exact ⟨u₂, fun h2 => hu12 (h1.trans h2.symm), hbu2⟩
    · exact ⟨u₁, h1, hbu1⟩
  -- For every `v` NOT adjacent to `u` (and `v ≠ u`), `pairIn u v` is FALSE on bowtie,
  -- while `b(pairIn u v) ≥ b(sing u) = true`, forcing `a(pairIn u v) = false`, so `a(sing u) = false` and `a(sing v) = false`!
  have ha_false_nonadj : ∀ v : Fin 5, v ≠ u → ¬ bowtieAdj u v →
      val C (sing u) a = false ∧ val C (sing v) a = false := by
    intro v hvu hnuv
    have hbuv : val C (pairIn u v) b = true :=
      val_mono hC (x := sing u) (y := pairIn u v)
        (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) b hbu
    have hauv : val C (pairIn u v) a = false := by
      cases h : val C (pairIn u v) a
      · rfl
      · exact absurd ((bowtie_pair_iff hE u v).mp ((hab (pairIn u v)).mpr ⟨h, hbuv⟩)) hnuv
    constructor
    · cases h : val C (sing u) a
      · rfl
      · have := val_mono hC (x := sing u) (y := pairIn u v)
          (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) a h
        rw [hauv] at this; cases this
    · cases h : val C (sing v) a
      · rfl
      · have := val_mono hC (x := sing v) (y := pairIn u v)
          (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) a h
        rw [hauv] at this; cases this
  -- Since `u ∈ {1, 2, 3, 4}`, `u` has TWO non-neighbors (the entire other triangle!), so 4 vertices are FALSE on `a`!
  -- Thus `a` can be true on at most 1 singleton, contradicting `isWide C a`!
  obtain ⟨x, y, hxy, hax, hay⟩ := hwa
  have huniq : ∃ w : Fin 5, ∀ z : Fin 5, val C (sing z) a = true → z = w := by
    have elim_z : ∀ (w z : Fin 5), (z ≠ w → val C (sing z) a = false) → val C (sing z) a = true → z = w := by
      intro w z hzf hzt; by_contra hne; rw [hzf hne] at hzt; cases hzt
    fin_cases u
    · exact absurd rfl hu0
    · refine ⟨2, fun z => elim_z 2 z fun hne => ?_⟩
      have h1 := (ha_false_nonadj 3 (by decide) (by decide)).1
      have h3 := (ha_false_nonadj 3 (by decide) (by decide)).2
      have h4 := (ha_false_nonadj 4 (by decide) (by decide)).2
      fin_cases z
      · exact ha0
      · exact h1
      · exact absurd rfl hne
      · exact h3
      · exact h4
    · refine ⟨1, fun z => elim_z 1 z fun hne => ?_⟩
      have h2 := (ha_false_nonadj 3 (by decide) (by decide)).1
      have h3 := (ha_false_nonadj 3 (by decide) (by decide)).2
      have h4 := (ha_false_nonadj 4 (by decide) (by decide)).2
      fin_cases z
      · exact ha0
      · exact absurd rfl hne
      · exact h2
      · exact h3
      · exact h4
    · refine ⟨4, fun z => elim_z 4 z fun hne => ?_⟩
      have h3 := (ha_false_nonadj 1 (by decide) (by decide)).1
      have h1 := (ha_false_nonadj 1 (by decide) (by decide)).2
      have h2 := (ha_false_nonadj 2 (by decide) (by decide)).2
      fin_cases z
      · exact ha0
      · exact h1
      · exact h2
      · exact h3
      · exact absurd rfl hne
    · refine ⟨3, fun z => elim_z 3 z fun hne => ?_⟩
      have h4 := (ha_false_nonadj 1 (by decide) (by decide)).1
      have h1 := (ha_false_nonadj 1 (by decide) (by decide)).2
      have h2 := (ha_false_nonadj 2 (by decide) (by decide)).2
      fin_cases z
      · exact ha0
      · exact h1
      · exact h2
      · exact absurd rfl hne
      · exact h4
  obtain ⟨w, hw⟩ := huniq
  exact hxy ((hw x hax).trans (hw y hay).symm)

/-- `AndAnc C u root`: path from `u` to `root` where every entered gate is an `AND` gate. -/
def AndStep (C : Circuit) (u w : ℕ) : Prop := LNext C u w ∧ isAndGate C w

def AndAnc (C : Circuit) (u root : ℕ) : Prop := ReflTransGen (AndStep C) u root

theorem andAnc_le {C : Circuit} {u root : ℕ} (h : AndAnc C u root) : u ≤ root := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.1.1.le

theorem andAnc_val_le {C : Circuit} {u root : ℕ} (h : AndAnc C u root) (x : Fin 5 → Bool) :
    val C x root = true → val C x u = true := by
  induction h with
  | refl => exact id
  | @tail a b _ hab ih =>
    intro hbx
    obtain ⟨⟨hlt, p, g, hg, hbp, hain⟩, _⟩ := hab.1
    obtain ⟨p', g', hg', hbp', hop⟩ := hab.2
    have hp' : p' = p := by omega
    subst p'; rw [hg] at hg'; cases hg'
    exact ih (((val_and x hg hop).mp (hbp ▸ hbx) a hain).2)

theorem andAnc_to_trace_notB {C : Circuit} {B : Finset ℕ} {u root : ℕ}
    (h : AndAnc C u root) (hnoB : ∀ z, AndAnc C z root → z ∉ B) :
    Trace C (fun w => w ∉ B) u root := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail a b hab hstep ih =>
    have haB : a ∉ B := hnoB a (ReflTransGen.single hstep)
    exact (ih (fun z hz => hnoB z (hz.tail hstep))).tail ⟨haB, hstep.1⟩

/-- Maximal `AND`-tree decomposition of a live wire `root` under `TightCut C B`. -/
theorem and_tree_decomp {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B) :
    ∀ root, Live C root → (∀ z, AndAnc C z root → z ∉ B) →
      ∃ H : Finset ℕ,
        (∀ h ∈ H, Live C h ∧ ¬ isAndGate C h ∧ h ∉ B ∧ AndAnc C h root) ∧
        (∀ h ∈ H, ∀ x, val C x root = true → val C x h = true) ∧
        (∀ x, (∀ h ∈ H, val C x h = true) → val C x root = true) ∧
        (∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ ≠ h₂ → ¬ Trace C (fun w => w ∉ B) h₁ h₂) := by
  classical
  -- First prove the decomposition without incomparability, then deduce incomparability cleanly!
  have build : ∀ root, Live C root → (∀ z, AndAnc C z root → z ∉ B) →
      ∃ H : Finset ℕ,
        (∀ h ∈ H, Live C h ∧ ¬ isAndGate C h ∧ h ∉ B ∧ AndAnc C h root) ∧
        (∀ x, (∀ h ∈ H, val C x h = true) → val C x root = true) := by
    intro root
    induction root using Nat.strong_induction_on with
    | ind root ih =>
      intro hrl hnoB
      by_cases hand : isAndGate C root
      · obtain ⟨p, g, hg, hrootp, hop⟩ := hand
        have hroot5 : 5 ≤ root := by omega
        obtain ⟨p', g', a, b, hg', hrootp', hab, hlna, hlnb, hall, hain, hbin⟩ :=
          tightCut_gate_inputs hC hE hT hrl hroot5
        have hp' : p' = p := by omega
        subst p'; rw [hg] at hg'; cases hg'
        have hand' : isAndGate C root := ⟨p, g, hg, hrootp, hop⟩
        obtain ⟨Ha, hHa_mem, hHa_eval⟩ := ih a hlna.1.1 (live_of_lnext hlna)
          (fun z hz => hnoB z (hz.tail ⟨hlna, hand'⟩))
        obtain ⟨Hb, hHb_mem, hHb_eval⟩ := ih b hlnb.1.1 (live_of_lnext hlnb)
          (fun z hz => hnoB z (hz.tail ⟨hlnb, hand'⟩))
        refine ⟨Ha ∪ Hb, ?_, ?_⟩
        · intro h hh
          rcases Finset.mem_union.mp hh with h1 | h2
          · obtain ⟨hl, hna, hnb, hanc⟩ := hHa_mem h h1
            exact ⟨hl, hna, hnb, hanc.tail ⟨hlna, hand'⟩⟩
          · obtain ⟨hl, hna, hnb, hanc⟩ := hHb_mem h h2
            exact ⟨hl, hna, hnb, hanc.tail ⟨hlnb, hand'⟩⟩
        · intro x hx
          have hax := hHa_eval x (fun h hh => hx h (Finset.mem_union_left _ hh))
          have hbx := hHb_eval x (fun h hh => hx h (Finset.mem_union_right _ hh))
          rw [hrootp, val_and x hg hop]
          intro i hi
          rcases hall i hi with rfl | rfl
          · exact ⟨by have := hlna.1.1; omega, hax⟩
          · exact ⟨by have := hlnb.1.1; omega, hbx⟩
      · refine ⟨{root}, ?_, ?_⟩
        · intro h hh; rw [Finset.mem_singleton] at hh; subst h
          exact ⟨hrl, hand, hnoB root ReflTransGen.refl, ReflTransGen.refl⟩
        · intro x hx; exact hx root (Finset.mem_singleton_self root)
  intro root hrl hnoB
  obtain ⟨H, hH_mem, hH_eval⟩ := build root hrl hnoB
  refine ⟨H, hH_mem, fun h hh x hx => andAnc_val_le (hH_mem h hh).2.2.2 x hx, hH_eval, ?_⟩
  -- Incomparability: every wire strictly between `h₁` and `root` on `h₁`'s unique `Trace (· ∉ B)` path IS an AND gate!
  intro h₁ hh₁ h₂ hh₂ hne hT12
  obtain ⟨h1l, _, h1nB, h1anc⟩ := hH_mem h₁ hh₁
  obtain ⟨_, h2notA, _, h2anc⟩ := hH_mem h₂ hh₂
  -- Induct on `h1anc`: if `AndAnc C x root` and `Trace (· ∉ B) x h₂` with `x ≠ h₂` and `h₂ ≤ root`, then `isAndGate C h₂`!
  have step_and : ∀ x, AndAnc C x root → Trace C (fun w => w ∉ B) x h₂ → x < h₂ → isAndGate C h₂ := by
    intro x hxr
    induction hxr using ReflTransGen.head_induction_on with
    | refl =>
      intro _ hlt
      have := andAnc_le h2anc
      omega
    | @head u w huw hwr ih =>
      intro huT hlt
      rcases huT.cases_head with rfl | ⟨w', huw', hw'h2⟩
      · omega
      · have huB : u ∉ B := hnoB u (ReflTransGen.head huw hwr)
        have hweq : w' = w := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext huw.1) huB) huw'.2 huw.1
        subst w'
        by_cases hwh2 : w = h₂
        · rw [hwh2] at huw; exact huw.2
        · exact ih hw'h2 (lt_of_le_of_ne (trace_le hw'h2) hwh2)
  exact h2notA (step_and h₁ h1anc hT12 (lt_of_le_of_ne (trace_le hT12) hne))

/-- Helper: if a wire `w` is reached from `v.val` by a chain containing NO live narrow OR gate,
    then every gate on the chain is an AND gate, so `val C x w = true → x v = true`. -/
theorem and_chain_le_input {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {v : Fin 5} {t : ℕ}
    (ht : Trace C (fun z => ¬ Branch C z) v.val t) (htl : Live C t)
    (hnoD : ∀ u, Trace C (fun z => ¬ Branch C z) v.val u → u ≤ t → ¬ isNarrowOr C u) :
    ∀ x, val C x t = true → x v = true := by
  induction ht with
  | refl => intro x hx; rwa [val_input] at hx
  | @tail a b hta hab ih =>
    intro x hbx
    have hal : Live C a := live_of_lnext hab.2
    have hnoD_a : ∀ u, Trace C (fun z => ¬ Branch C z) v.val u → u ≤ a → ¬ isNarrowOr C u :=
      fun u hu hle => hnoD u hu (hle.trans hab.2.1.1.le)
    obtain ⟨hlt, p, g, hg, hbp, hain⟩ := hab.2.1
    have hband : g.op = GateOp.and := by
      rcases mono_op hC hg with hop | hop
      · exact hop
      · exfalso
        apply hnoD b (hta.tail hab) le_rfl
        exact ⟨⟨p, g, hg, hbp, hop⟩, chain_not_wide hC hE (hta.tail hab) htl⟩
    exact ih hal hnoD_a x (((val_and x hg hband).mp (hbp ▸ hbx) a hain).2)

/-- Case 1: If there are NO live narrow OR gates (`liveNarrowOr.card = 0`), then `10 ≤ liveGates.card`. -/
theorem case_zero_narrow {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    (hD0 : (liveNarrowOr C).card = 0) : 10 ≤ (liveGates C).card := by
  classical
  have hnoD : ∀ w, Live C w → ¬ isNarrowOr C w := by
    intro w hwl hnw
    obtain ⟨p, g, hg, hwp, _⟩ := hnw.1
    have hp_lt : p < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
    have hp_mem : p ∈ liveNarrowOr C :=
      mem_liveNarrowOr.mpr ⟨mem_liveGates.mpr ⟨hp_lt, hwp ▸ hwl⟩, hwp ▸ hnw⟩
    have hpos := Finset.card_pos.mpr ⟨p, hp_mem⟩
    omega
  -- Every vertex `v : Fin 5` hits a branching wire `b(v)` along its branch-free chain!
  have hex_br : ∀ v : Fin 5, ∃ b, Live C b ∧ Branch C b ∧ Trace C (fun z => ¬ Branch C z) v.val b := by
    intro v
    by_contra hno
    push Not at hno
    -- If `v` never hits a branching wire, `v` has a branch-free chain all the way to `C.output`!
    suffices hreach : ∀ k w, w = C.output - k → Live C w → Trace C (fun z => ¬ Branch C z) v.val w →
        Trace C (fun z => ¬ Branch C z) v.val C.output by
      have hT := hreach (C.output - v.val) v.val (by have := live_le_output (input_live hE v); omega)
        (input_live hE v) ReflTransGen.refl
      have hle := and_chain_le_input hC hE hT ReflTransGen.refl (fun u hu _ => by
        have hul : Live C u := by
          have hs : ∀ x y, Trace C (fun z => ¬ Branch C z) x y → Live C x → Live C y := by
            intro x y hxy; induction hxy with | refl => exact id | tail _ h _ => intro _; exact h.2.2
          exact hs v.val u hu (input_live hE v)
        exact hnoD u hul)
      obtain ⟨a, b, hav, hbv, hab⟩ := bowtie_edge_avoid v
      have ht := hle (pairIn a b) ((bowtie_pair_iff hE a b).mpr hab)
      simp only [pairIn, decide_eq_true_eq] at ht
      rcases ht with rfl | rfl
      · exact hav rfl
      · exact hbv rfl
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro w hwk hwl htw
      by_cases hwo : w = C.output
      · exact hwo ▸ htw
      · have hnb : ¬ Branch C w := fun hwb => hno w hwl hwb htw
        rcases hwl.cases_head with rfl | ⟨w', hww', hw'o⟩
        · exact absurd rfl hwo
        · have hle := live_le_output hw'o
          have hlt := hww'.1
          exact ih (C.output - w') (by omega) w' (by omega) hw'o (htw.tail ⟨hnb, hww', hw'o⟩)
  let b (v : Fin 5) : ℕ := Nat.find (hex_br v)
  have hb_spec : ∀ v : Fin 5, Live C (b v) ∧ Branch C (b v) ∧ Trace C (fun z => ¬ Branch C z) v.val (b v) :=
    fun v => Nat.find_spec (hex_br v)
  have hb_le : ∀ v : Fin 5, ∀ x, val C x (b v) = true → x v = true := fun v =>
    and_chain_le_input hC hE (hb_spec v).2.2 (hb_spec v).1 (fun u hu _ => by
      have hul : Live C u := by
        have hs : ∀ q r, Trace C (fun z => ¬ Branch C z) q r → Live C q → Live C r := by
          intro q r hqr; induction hqr with | refl => exact id | tail _ h _ => intro _; exact h.2.2
        exact hs v.val u hu (input_live hE v)
      exact hnoD u hul)
  have hb_inj : Function.Injective b := by
    intro u v huv
    by_contra hne
    obtain ⟨w, hwv, huw⟩ := bowtie_other_nbr u v hne
    have hbu_false : val C (pairIn u w) (b u) = false := by
      cases h : val C (pairIn u w) (b u)
      · rfl
      · rw [huv] at h
        have hv1 := hb_le v (pairIn u w) h
        simp only [pairIn, decide_eq_true_eq] at hv1
        rcases hv1 with rfl | rfl
        · exact absurd rfl hne
        · exact absurd rfl hwv
    have hres := no_bypass_output hC (hb_spec u).2.2 (hb_spec u).1
      (x := pairIn u w) (y := sing w)
      (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_left hi)
      (fun ht => by rw [hbu_false] at ht; cases ht)
      ((bowtie_pair_iff hE u w).mpr huw)
    rw [bowtie_sing hE w] at hres; cases hres
  let B : Finset ℕ := Finset.univ.image b
  have hBcard : B.card = 5 := by
    rw [Finset.card_image_of_injective _ hb_inj, Finset.card_fin]
  have hBsub : B ⊆ (living C).erase C.output := by
    intro w hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    have hne : b v ≠ C.output := by
      intro heq; have := (branch_iff_two_le_outdeg hE _).mp (hb_spec v).2.1
      rw [heq, outdeg_output hE] at this; omega
    exact Finset.mem_erase.mpr ⟨hne, (mem_living hE).mpr (hb_spec v).1⟩
  have hBbr : ∀ w ∈ B, Branch C w := by
    intro w hw; obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw; exact (hb_spec v).2.1
  -- Assume for contradiction `(liveGates C).card ≤ 9 = 4 + B.card`, so `TightCut C B` holds!
  by_contra hlt
  push Not at hlt
  have hT : TightCut C B := tightCut_of_le hC hE hBsub hBbr (by omega)
  -- No wire in `B` can satisfy `AndAnc C z C.output` (since `val C.output ≤ b v ≤ x v`, impossible for bowtie!).
  have hnoB_out : ∀ z, AndAnc C z C.output → z ∉ B := by
    intro z hz hzB
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hzB
    obtain ⟨c, d, hcv, hdv, hcd⟩ := bowtie_edge_avoid v
    have h1 := hb_le v (pairIn c d) (andAnc_val_le hz (pairIn c d) ((bowtie_pair_iff hE c d).mpr hcd))
    simp only [pairIn, decide_eq_true_eq] at h1
    rcases h1 with rfl | rfl
    · exact hcv rfl
    · exact hdv rfl
  obtain ⟨H, hH_mem, hH_ge, hH_eval, hH_incomp⟩ := and_tree_decomp hC hE hT C.output ReflTransGen.refl hnoB_out
  -- Every `h ∈ H` is a WIDE OR gate (cannot be input `< 5` since `f_G ≰ x_v`, cannot be AND, cannot be narrow OR)!
  have hH_wide : ∀ h ∈ H, isWide C h := by
    intro h hh
    obtain ⟨hl, hnotA, _, _⟩ := hH_mem h hh
    have hge5 : 5 ≤ h := by
      by_contra hlt5; push Not at hlt5
      let v : Fin 5 := ⟨h, hlt5⟩
      obtain ⟨c, d, hcv, hdv, hcd⟩ := bowtie_edge_avoid v
      have h1 := hH_ge h hh (pairIn c d) ((bowtie_pair_iff hE c d).mpr hcd)
      change val C (pairIn c d) v.val = true at h1
      rw [val_input] at h1
      simp only [pairIn, decide_eq_true_eq] at h1
      rcases h1 with rfl | rfl
      · exact hcv rfl
      · exact hdv rfl
    have hlt_len := (live_le_output hl).trans_lt (output_bounds hE).2
    set p := h - 5
    have hhp : h = 5 + p := by omega
    obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem (by omega)⟩
    have hor : g.op = GateOp.or := by
      rcases mono_op hC hg with hop | hop
      · exact absurd ⟨p, g, hg, hhp, hop⟩ hnotA
      · exact hop
    by_contra hnw
    exact hnoD h hl ⟨⟨p, g, hg, hhp, hor⟩, hnw⟩
  -- Prove `3 ≤ H.card` using `two_wide_or_ne_bowtie`!
  have hH_ge3 : 3 ≤ H.card := by
    by_contra hlt3; push Not at hlt3
    have hle2 : H.card ≤ 2 := by omega
    rcases Nat.le_iff_lt_or_eq.mp hle2 with hlt2 | hcard2
    · rcases Nat.lt_succ_iff.mp hlt2 |> Nat.le_iff_lt_or_eq.mp with hlt1 | hcard1
      · have hemp : H = ∅ := Finset.card_eq_zero.mp (by omega)
        have h0 := hH_eval zeroIn (fun h hh => by rw [hemp] at hh; simp at hh)
        rw [bowtie_zero hE] at h0; cases h0
      · obtain ⟨h₁, hh₁eq⟩ := Finset.card_eq_one.mp hcard1
        have hh₁ : h₁ ∈ H := by rw [hh₁eq]; simp
        obtain ⟨u, _, _, hu, _⟩ := hH_wide h₁ hh₁
        have hout := hH_eval (sing u) (fun h hh => by rw [hh₁eq, Finset.mem_singleton] at hh; subst hh; exact hu)
        rw [bowtie_sing hE u] at hout; cases hout
    · obtain ⟨h₁, h₂, h12, hpair⟩ := Finset.card_eq_two.mp hcard2
      have hh₁ : h₁ ∈ H := by rw [hpair]; simp
      have hh₂ : h₂ ∈ H := by rw [hpair]; simp
      exact two_wide_or_ne_bowtie hC hE (hH_wide h₁ hh₁) (hH_wide h₂ hh₂) (fun x => by
        constructor
        · intro hx; exact ⟨hH_ge h₁ hh₁ x hx, hH_ge h₂ hh₂ x hx⟩
        · rintro ⟨h1, h2⟩; apply hH_eval x
          intro h hh; rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hh
          rcases hh with rfl | rfl
          · exact h1
          · exact h2)
  -- For each `h ∈ H`, show NO input wire `< 5` lies in `Internal C B h`!
  have hnoin_B : ∀ r, r ∉ B → Trace C (fun z => z ∉ B) r C.output → ∀ u ∈ Internal C B r, 5 ≤ u := by
    intro r hrB hrOut u hu
    obtain ⟨hul, huB, huTr⟩ := (mem_Internal hE).mp hu
    by_contra hlt5; push Not at hlt5
    let v : Fin 5 := ⟨u, hlt5⟩
    -- `v` has `Trace (· ∉ B) v.val C.output` (via `huTr.trans hrOut`), AND `Trace (¬ Branch) v.val (b v)` with `b v ∈ B`!
    -- Since every wire `∉ B` is `¬ Branch`, determinism forces `b v` to lie on `v.val → ... → C.output`, impossible!
    have hvOut : Trace C (fun z => z ∉ B) v.val C.output := huTr.trans hrOut
    have hv_to_nb : ∀ {x y}, Trace C (fun z => z ∉ B) x y → Trace C (fun z => ¬ Branch C z) x y := by
      intro x y hxy
      induction hxy with
      | refl => exact ReflTransGen.refl
      | tail _ h ih => exact ih.tail ⟨tightCut_not_branch hE hT (live_of_lnext h.2) h.1, h.2⟩
    have hvOut_nb := hv_to_nb hvOut
    have hbv_inB : b v ∈ B := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    have hbv_lt : b v < C.output :=
      lt_of_le_of_ne (live_le_output (hb_spec v).1) (Finset.mem_erase.mp (hT.1 hbv_inB)).1
    exact absurd (hb_spec v).2.1 (trace_strict_not_branch hvOut_nb (hb_spec v).2.2 hbv_lt)
  have hH_noin : ∀ h ∈ H, ∀ u ∈ Internal C B h, 5 ≤ u := fun h hh =>
    hnoin_B h (hH_mem h hh).2.2.1 (andAnc_to_trace_notB (hH_mem h hh).2.2.2 hnoB_out)
  -- For each `h ∈ H`, `V h := {v : Fin 5 | b v ∈ Leaves C B h}` is a VERTEX COVER of the bowtie!
  let V (h : ℕ) : Finset (Fin 5) := Finset.univ.filter (fun v => b v ∈ Leaves C B h)
  have hV_vc : ∀ h ∈ H, ∀ u v : Fin 5, bowtieAdj u v → u ∈ V h ∨ v ∈ V h := by
    intro h hh u v huv
    by_contra hneither
    push Not at hneither
    have hfa : ∀ w ∈ Leaves C B h, val C (pairIn u v) w = false := by
      intro w hw
      have hwB : w ∈ B := by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
        exact ((mem_LeafEdges hE).mp hp).1
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hwB
      have hzu : z ≠ u := fun e => hneither.1 (by simp [V, e ▸ hw])
      have hzv : z ≠ v := fun e => hneither.2 (by simp [V, e ▸ hw])
      cases hval : val C (pairIn u v) (b z)
      · rfl
      · have hz1 := hb_le z (pairIn u v) hval
        simp only [pairIn, decide_eq_true_eq] at hz1
        rcases hz1 with rfl | rfl
        · exact absurd rfl hzu
        · exact absurd rfl hzv
    have hf := internal_false hC hE hT (hH_noin h hh) hfa h
      ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
    have ht := hH_ge h hh (pairIn u v) ((bowtie_pair_iff hE u v).mpr huv)
    rw [hf] at ht; cases ht
  have hV_le_edges : ∀ h ∈ H, (V h).card ≤ (LeafEdges C B h).card := by
    intro h _
    calc (V h).card = ((V h).image b).card := (Finset.card_image_of_injective _ hb_inj).symm
      _ ≤ (Leaves C B h).card := Finset.card_le_card (by
          intro w hw; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw; exact (Finset.mem_filter.mp hv).2)
      _ ≤ (LeafEdges C B h).card := Finset.card_image_le
  -- Disjointness of `LeafEdges C B h` across `h ∈ H` gives `∑ h ∈ H, (LeafEdges C B h).card ≤ 10`!
  have hdisj_H : (H : Set ℕ).PairwiseDisjoint (fun h => LeafEdges C B h) := by
    intro h₁ hh₁ h₂ hh₂ hne
    exact leafEdges_disjoint hE hT (hH_incomp h₁ hh₁ h₂ hh₂ hne) (hH_incomp h₂ hh₂ h₁ hh₁ hne.symm)
  have hunion_sub : H.biUnion (fun h => LeafEdges C B h) ⊆ AllBEdges C B := by
    intro p hp
    obtain ⟨h, _, hpL⟩ := Finset.mem_biUnion.mp hp
    exact leafEdges_subset_allBEdges hE hpL
  have hsum_edges_le : (∑ h ∈ H, (LeafEdges C B h).card) ≤ 10 := by
    calc (∑ h ∈ H, (LeafEdges C B h).card)
        = (H.biUnion (fun h => LeafEdges C B h)).card := (Finset.card_biUnion hdisj_H).symm
      _ ≤ (AllBEdges C B).card := Finset.card_le_card hunion_sub
      _ = 10 := by rw [allBEdges_card hE hT, hBcard]
  -- Each vertex `v : Fin 5` belongs to AT MOST 2 sets `V h` (since `b v` has only 2 outgoing edges in `AllBEdges C B`)!
  have hfreq_le2 : ∀ v : Fin 5, (H.filter (fun h => v ∈ V h)).card ≤ 2 := by
    intro v
    have hbvB : b v ∈ B := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    have heq_f : H.filter (fun h => v ∈ V h) = H.filter (fun h => b v ∈ Leaves C B h) := by
      ext h; simp [V]
    rw [heq_f]
    exact freq_le_two hE hT hdisj_H hbvB
  -- Since `H.card ≥ 3` and `(H.filter (0 ∈ V ·)).card ≤ 2`, there is `h₁ ∈ H` with `0 ∉ V h₁` (so `(V h₁).card ≥ 4`)!
  have hex_no0 : ∃ h₁ ∈ H, (0 : Fin 5) ∉ V h₁ := by
    by_contra hall; push Not at hall
    have heq : H.filter (fun h => (0 : Fin 5) ∈ V h) = H :=
      Finset.filter_true_of_mem hall
    have hle := hfreq_le2 0
    rw [heq] at hle; omega
  obtain ⟨h₁, hh₁, h0V1⟩ := hex_no0
  have hV1_all : ∀ k : Fin 5, k ≠ 0 → k ∈ V h₁ := by
    intro k hk; fin_cases k
    · exact absurd rfl hk
    · exact (hV_vc h₁ hh₁ 0 1 (by decide)).resolve_left h0V1
    · exact (hV_vc h₁ hh₁ 0 2 (by decide)).resolve_left h0V1
    · exact (hV_vc h₁ hh₁ 0 3 (by decide)).resolve_left h0V1
    · exact (hV_vc h₁ hh₁ 0 4 (by decide)).resolve_left h0V1
  have hV1_card : 4 ≤ (V h₁).card := by
    have hsub : ({1, 2, 3, 4} : Finset (Fin 5)) ⊆ V h₁ := by
      intro k hk; apply hV1_all k; simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
    have h4 : ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
    exact h4 ▸ Finset.card_le_card hsub
  have hV_ge3 : ∀ h ∈ H, 3 ≤ (V h).card := fun h hh => bowtie_vc_ge3 (V h) (hV_vc h hh)
  -- Sum over `H`: `4 + 3 * (H.card - 1) ≤ ∑ h ∈ H, (V h).card ≤ ∑ h ∈ H, (LeafEdges C B h).card ≤ 10`,
  -- forcing `H.card = 3`, `∑ h ∈ H, (LeafEdges C B h).card = 10`, and EVERY `V h` tight!
  have hsum_V : 4 + 3 * (H.card - 1) ≤ ∑ h ∈ H, (V h).card := by
    rw [← Finset.add_sum_erase H (fun h => (V h).card) hh₁]
    have hrest : 3 * (H.erase h₁).card ≤ ∑ h ∈ H.erase h₁, (V h).card := by
      calc 3 * (H.erase h₁).card = ∑ _h ∈ H.erase h₁, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ h ∈ H.erase h₁, (V h).card := Finset.sum_le_sum fun h hh => hV_ge3 h (Finset.mem_of_mem_erase hh)
    rw [Finset.card_erase_of_mem hh₁] at hrest
    omega
  have hsum_V_le : (∑ h ∈ H, (V h).card) ≤ ∑ h ∈ H, (LeafEdges C B h).card :=
    Finset.sum_le_sum hV_le_edges
  have hH3 : H.card = 3 := by omega
  have hsum_eq10 : (∑ h ∈ H, (LeafEdges C B h).card) = 10 := by omega
  -- All 10 edges of `AllBEdges C B` are used by `H.biUnion LeafEdges`!
  have hall_edges_used : H.biUnion (fun h => LeafEdges C B h) = AllBEdges C B :=
    Finset.eq_of_subset_of_card_le hunion_sub (by rw [Finset.card_biUnion hdisj_H, allBEdges_card hE hT, hBcard]; omega)
  -- Therefore EVERY `b v = v.val`!
  have h_input_sep : ∀ w : Fin 5, ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z →
      ∀ w' : Fin 5, Trace C (fun q => q ∉ B) w'.val z → w' = w := by
    intro w z hzB hwz w' hw'z
    have to_nb : ∀ {x y}, Trace C (fun q => q ∉ B) x y → Trace C (fun q => ¬ Branch C q) x y := by
      intro x y hxy; induction hxy with
      | refl => exact ReflTransGen.refl
      | tail _ h ih => exact ih.tail ⟨tightCut_not_branch hE hT (live_of_lnext h.2) h.1, h.2⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hzB
    -- Since `Trace (¬ Branch) w.val (b v)` and `b v` is branching, `b w = b v`!
    have hbw : b w = b v := by
      have hmin : b w ≤ b v := Nat.find_min' (hex_br w) ⟨(hb_spec v).1, (hb_spec v).2.1, to_nb hwz⟩
      by_contra hne
      have hlt : b w < b v := lt_of_le_of_ne hmin hne
      exact absurd (hb_spec w).2.1 (trace_strict_not_branch (to_nb hwz) (hb_spec w).2.2 hlt)
    have hbw' : b w' = b v := by
      have hmin : b w' ≤ b v := Nat.find_min' (hex_br w') ⟨(hb_spec v).1, (hb_spec v).2.1, to_nb hw'z⟩
      by_contra hne
      have hlt : b w' < b v := lt_of_le_of_ne hmin hne
      exact absurd (hb_spec w').2.1 (trace_strict_not_branch (to_nb hw'z) (hb_spec w').2.2 hlt)
    exact hb_inj (hbw'.trans hbw.symm)
  have hbv_eq : ∀ v : Fin 5, b v = v.val := by
    intro v
    by_contra hne
    have hvb : Trace C (fun q => q ∉ B) v.val (b v) := by
      have to_notB : ∀ x y, Trace C (fun q => ¬ Branch C q) x y → Trace C (fun q => q ∉ B) x y := by
        intro x y htr
        induction htr with
        | refl => exact ReflTransGen.refl
        | @tail a c hta hac ih =>
          have haB : a ∉ B := fun ha => hac.1 (hBbr a ha)
          exact ih.tail ⟨haB, hac.2⟩
      exact to_notB v.val (b v) (hb_spec v).2.2
    obtain ⟨p, hpAll, _, hpNotL, _⟩ :=
      non_input_branch_uses_edge hC hE hT h_input_sep (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) hvb hne
    rw [← hall_edges_used] at hpAll
    obtain ⟨h, hhH, hpL⟩ := Finset.mem_biUnion.mp hpAll
    exact hpNotL h (hH_mem h hhH).2.2.1 (andAnc_to_trace_notB (hH_mem h hhH).2.2.2 hnoB_out) hpL
  -- Now write `H = {h₁, h₂, h₃}` with `h₂ ≠ h₃`, `h₁ ≠ h₂`, `h₁ ≠ h₃`!
  have herase2 : (H.erase h₁).card = 2 := by rw [Finset.card_erase_of_mem hh₁, hH3]
  obtain ⟨h₂, h₃, h23, hpair23⟩ := Finset.card_eq_two.mp herase2
  have hh₂ : h₂ ∈ H := Finset.mem_of_mem_erase (by rw [hpair23]; simp)
  have hh₃ : h₃ ∈ H := Finset.mem_of_mem_erase (by rw [hpair23]; simp)
  have h12 : h₁ ≠ h₂ := (Finset.mem_erase.mp (by rw [hpair23]; simp)).1.symm
  have h13 : h₁ ≠ h₃ := (Finset.mem_erase.mp (by rw [hpair23]; simp)).1.symm
  -- Since `1, 2, 3, 4 ∈ V h₁` and each vertex appears in at most 2 of `{V h₁, V h₂, V h₃}`,
  -- `V h₂` and `V h₃` are DISJOINT on `{1, 2, 3, 4}`!
  have hdisj23 : ∀ k : Fin 5, k ≠ 0 → ¬ (k ∈ V h₂ ∧ k ∈ V h₃) := by
    intro k hk ⟨hk2, hk3⟩
    have hk1 : k ∈ V h₁ := hV1_all k hk
    have hsub : ({h₁, h₂, h₃} : Finset ℕ) ⊆ H.filter (fun h => k ∈ V h) := by
      intro h hh; simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      simp only [Finset.mem_filter]
      rcases hh with rfl | rfl | rfl
      · exact ⟨hh₁, hk1⟩
      · exact ⟨hh₂, hk2⟩
      · exact ⟨hh₃, hk3⟩
    have hcard3 : ({h₁, h₂, h₃} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
    have := Finset.card_le_card hsub
    have := hfreq_le2 k
    omega
  -- Since `V h₂` and `V h₃` are vertex covers of the bowtie, each hits `{1, 2}` and `{3, 4}`!
  -- By `hdisj23`, one hits `a ∈ {1,2}`, the other `a' ∈ {1,2}`; one hits `c ∈ {3,4}`, the other `c' ∈ {3,4}`!
  have hV2_12 : (1 : Fin 5) ∈ V h₂ ∨ (2 : Fin 5) ∈ V h₂ := hV_vc h₂ hh₂ 1 2 (by decide)
  have hV3_12 : (1 : Fin 5) ∈ V h₃ ∨ (2 : Fin 5) ∈ V h₃ := hV_vc h₃ hh₃ 1 2 (by decide)
  have hV2_34 : (3 : Fin 5) ∈ V h₂ ∨ (4 : Fin 5) ∈ V h₂ := hV_vc h₂ hh₂ 3 4 (by decide)
  have hV3_34 : (3 : Fin 5) ∈ V h₃ ∨ (4 : Fin 5) ∈ V h₃ := hV_vc h₃ hh₃ 3 4 (by decide)
  -- Helper: if `k ∈ V h` and `k'` is the mate of `k` in its triangle with `k' ∉ V h` and `0 ∉ V h'`...
  -- Even simpler: for any `h ∈ H` and any edge `bowtieAdj x y` with `y ∉ V h`:
  -- since `val C (pairIn x y) h = true`, and every leaf `b w ∈ Leaves C B h` equals `w.val`,
  -- on `pairIn x y` ONLY `x` can be true among `Leaves C B h`, so by `internal_mono`, `val C (sing x) h = true`!
  have sing_true_of_avoid : ∀ h ∈ H, ∀ x y : Fin 5, bowtieAdj x y → y ∉ V h →
      val C (sing x) h = true := by
    intro h hh x y hxy hyV
    have hht : val C (pairIn x y) h = true := hH_ge h hh (pairIn x y) ((bowtie_pair_iff hE x y).mpr hxy)
    apply internal_mono hC hE hT (hH_noin h hh) _ h
      ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩) hht
    intro w hw hwx
    have hwB : w ∈ B := by obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw; exact ((mem_LeafEdges hE).mp hp).1
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hwB
    rw [hbv_eq z, val_input] at hwx ⊢
    simp only [pairIn, sing, decide_eq_true_eq] at hwx ⊢
    rcases hwx with rfl | rfl
    · rfl
    · exfalso; apply hyV; simp [V, hw]
  -- Pick `a ∈ {1,2}` with `a ∈ V h₂` (so `a' ∈ V h₃, a' ∉ V h₂`) and `c' ∈ {3,4}` with `c' ∈ V h₃` (so `c ∈ V h₂, c ∉ V h₃`)!
  -- Wait: then on `pairIn a c'`:
  --   * `h₁`: `0 ∉ V h₁` and `bowtieAdj a 0`, so `val (sing a) h₁ = true` -> `val (pairIn a c') h₁ = true`!
  --   * `h₂`: `a' ∉ V h₂` and `bowtieAdj a a'`, so `val (sing a) h₂ = true` -> `val (pairIn a c') h₂ = true`!
  --   * `h₃`: `c ∉ V h₃` and `bowtieAdj c' c`, so `val (sing c') h₃ = true` -> `val (pairIn a c') h₃ = true`!
  --   * Hence `val (pairIn a c') C.output = true`, contradicting `¬ bowtieAdj a c'`!!
  have kill_ac' : ∀ a a' c c' : Fin 5,
      bowtieAdj a 0 → bowtieAdj a a' → bowtieAdj c' c → ¬ bowtieAdj a c' →
      a' ∉ V h₂ → c ∉ V h₃ → False := by
    intro a a' c c' ha0 haa' hc'c hnac' ha'2 hc3
    have ht1 : val C (pairIn a c') h₁ = true :=
      val_mono hC (x := sing a) (y := pairIn a c')
        (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) h₁
        (sing_true_of_avoid h₁ hh₁ a 0 ha0 h0V1)
    have ht2 : val C (pairIn a c') h₂ = true :=
      val_mono hC (x := sing a) (y := pairIn a c')
        (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) h₂
        (sing_true_of_avoid h₂ hh₂ a a' haa' ha'2)
    have ht3 : val C (pairIn a c') h₃ = true :=
      val_mono hC (x := sing c') (y := pairIn a c')
        (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) h₃
        (sing_true_of_avoid h₃ hh₃ c' c hc'c hc3)
    have hout : val C (pairIn a c') C.output = true := by
      apply hH_eval (pairIn a c')
      intro h hh
      by_cases h1 : h = h₁
      · subst h1; exact ht1
      · have hmem : h ∈ H.erase h₁ := Finset.mem_erase.mpr ⟨h1, hh⟩
        rw [hpair23, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact ht2
        · exact ht3
    exact hnac' ((bowtie_pair_iff hE a c').mp hout)
  rcases hV2_12 with h1_2 | h2_2 <;> rcases hV3_34 with h3_3 | h4_3
  · have h2_3 : (2 : Fin 5) ∈ V h₃ := hV3_12.resolve_left (fun h => hdisj23 1 (by decide) ⟨h1_2, h⟩)
    have h4_2 : (4 : Fin 5) ∈ V h₂ := hV2_34.resolve_left (fun h => hdisj23 3 (by decide) ⟨h, h3_3⟩)
    exact kill_ac' 1 2 4 3 (by decide) (by decide) (by decide) (by decide)
      (fun h => hdisj23 2 (by decide) ⟨h, h2_3⟩) (fun h => hdisj23 4 (by decide) ⟨h4_2, h⟩)
  · have h2_3 : (2 : Fin 5) ∈ V h₃ := hV3_12.resolve_left (fun h => hdisj23 1 (by decide) ⟨h1_2, h⟩)
    have h3_2 : (3 : Fin 5) ∈ V h₂ := hV2_34.resolve_right (fun h => hdisj23 4 (by decide) ⟨h, h4_3⟩)
    exact kill_ac' 1 2 3 4 (by decide) (by decide) (by decide) (by decide)
      (fun h => hdisj23 2 (by decide) ⟨h, h2_3⟩) (fun h => hdisj23 3 (by decide) ⟨h3_2, h⟩)
  · have h1_3 : (1 : Fin 5) ∈ V h₃ := hV3_12.resolve_right (fun h => hdisj23 2 (by decide) ⟨h2_2, h⟩)
    have h4_2 : (4 : Fin 5) ∈ V h₂ := hV2_34.resolve_left (fun h => hdisj23 3 (by decide) ⟨h, h3_3⟩)
    exact kill_ac' 2 1 4 3 (by decide) (by decide) (by decide) (by decide)
      (fun h => hdisj23 1 (by decide) ⟨h, h1_3⟩) (fun h => hdisj23 4 (by decide) ⟨h4_2, h⟩)
  · have h1_3 : (1 : Fin 5) ∈ V h₃ := hV3_12.resolve_right (fun h => hdisj23 2 (by decide) ⟨h2_2, h⟩)
    have h3_2 : (3 : Fin 5) ∈ V h₂ := hV2_34.resolve_right (fun h => hdisj23 4 (by decide) ⟨h, h4_3⟩)
    exact kill_ac' 2 1 3 4 (by decide) (by decide) (by decide) (by decide)
      (fun h => hdisj23 1 (by decide) ⟨h, h1_3⟩) (fun h => hdisj23 3 (by decide) ⟨h3_2, h⟩)

/-! ## Section 5: Case `|D_L| = 1` and final theorem -/

/-- Helper: on a branch-free chain `v → ... → C.output` with a UNIQUE live narrow OR gate `d*`,
    `d*` lies on the chain, `d* = p ∨ q` with `p ≤ x_v`, `q` not reachable from `v`, `S(q) = ∅`,
    and `AndAnc C d* C.output`. -/
theorem unique_narrow_on_chain {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {d : ℕ} (hd_uniq : ∀ w, Live C w → isNarrowOr C w → w = d)
    {v₀ : Fin 5} (hv₀_chain : Trace C (fun z => z ∉ B) v₀.val C.output) :
    ∃ p q, p ≠ q ∧ LNext C p d ∧ LNext C q d ∧
      Trace C (fun z => z ∉ B) v₀.val p ∧ p ∉ B ∧
      d ∉ B ∧ Live C d ∧ isOrGate C d ∧
      (∀ x, val C x d = (val C x p || val C x q)) ∧
      (∀ x, val C x p = true → x v₀ = true) ∧
      ¬ ReflTransGen (Next C) v₀.val q ∧
      (∀ u : Fin 5, val C (sing u) q = false) ∧
      AndAnc C d C.output ∧
      Trace C (fun z => z ∉ B) d C.output := by
  have to_nb : ∀ {x y}, Trace C (fun z => z ∉ B) x y → Trace C (fun z => ¬ Branch C z) x y := by
    intro x y hxy
    induction hxy with
    | refl => exact ReflTransGen.refl
    | tail _ h ih => exact ih.tail ⟨tightCut_not_branch hE hT (live_of_lnext h.2) h.1, h.2⟩
  have hv₀_nb : Trace C (fun z => ¬ Branch C z) v₀.val C.output := to_nb hv₀_chain
  have trace_live : ∀ {x y}, Trace C (fun z => z ∉ B) x y → Live C x → Live C y := by
    intro x y hxy; induction hxy with | refl => exact id | tail _ h _ => intro _; exact h.2.2
  -- First, show `d` MUST lie on `v₀`'s chain (else `and_chain_le_input` gives `C.output ≤ x_{v₀}`, impossible!).
  have hd_on : Trace C (fun z => z ∉ B) v₀.val d ∧ d ≤ C.output := by
    by_contra hno
    have hle := and_chain_le_input hC hE hv₀_nb ReflTransGen.refl (fun u hu hle hnw => by
      have hul : Live C u := by
        have hs : ∀ x y, Trace C (fun z => ¬ Branch C z) x y → Live C x → Live C y := by
          intro x y hxy; induction hxy with | refl => exact id | tail _ h _ => intro _; exact h.2.2
        exact hs v₀.val u hu (input_live hE v₀)
      have hud : u = d := hd_uniq u hul hnw
      subst hud
      -- Convert `Trace (¬ Branch) v₀.val u` to `Trace (· ∉ B) v₀.val u` using `hv₀_chain`!
      have hu_notB : Trace C (fun z => z ∉ B) v₀.val u := by
        suffices ∀ {x y}, Trace C (fun z => z ∉ B) x C.output →
            Trace C (fun z => ¬ Branch C z) x y → y ≤ C.output → Trace C (fun z => z ∉ B) x y from
          this hv₀_chain hu hle
        intro x y hxO
        induction hxO using ReflTransGen.head_induction_on with
        | refl =>
          intro hxy hyle
          have := trace_le hxy
          have : C.output = y := by omega
          subst this; exact ReflTransGen.refl
        | @head a c hac hcO ih =>
          intro hxy hyle
          rcases hxy.cases_head with rfl | ⟨c', hac', hc'y⟩
          · exact ReflTransGen.refl
          · have hceq : c' = c := trace_lnext_unique hac'.1 hac'.2 hac.2
            subst c'
            exact ReflTransGen.head hac (ih hc'y hyle)
      exact hno ⟨hu_notB, hle⟩)
    obtain ⟨a, b, hav, hbv, hab⟩ := bowtie_edge_avoid v₀
    have ht := hle (pairIn a b) ((bowtie_pair_iff hE a b).mpr hab)
    simp only [pairIn, decide_eq_true_eq] at ht
    rcases ht with rfl | rfl
    · exact hav rfl
    · exact hbv rfl
  have hdl : Live C d := trace_live hd_on.1 (input_live hE v₀)
  -- Show `d ∉ B` and `Trace (· ∉ B) d C.output`!
  have hd_notB_and_out : d ∉ B ∧ Trace C (fun z => z ∉ B) d C.output := by
    suffices ∀ {x}, Trace C (fun z => z ∉ B) x C.output → Trace C (fun z => z ∉ B) x d →
        d ∉ B ∧ Trace C (fun z => z ∉ B) d C.output from this hv₀_chain hd_on.1
    intro x hxO hxd
    induction hxd using ReflTransGen.head_induction_on with
    | refl =>
      rcases hxO.cases_head with rfl | ⟨_, hstep, _⟩
      · exact ⟨fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl, ReflTransGen.refl⟩
      · exact ⟨hstep.1, ReflTransGen.head hstep ‹_›⟩
    | @head a c hac hcd ih =>
      rcases hxO.cases_head with rfl | ⟨c', hac', hc'O⟩
      · have := live_le_output hdl; have := trace_le hcd; have := hac.2.1.1; omega
      · have hceq : c' = c := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hac.2) hac.1) hac'.2 hac.2
        subst c'
        exact ih hc'O
  -- `d` must be a live narrow OR gate (Wait: could `d` NOT be narrow OR? No, we used `hd_uniq` ONLY to get `d` on chain,
  -- actually wait: in `hd_on` we DID prove `d` is narrow OR because `and_chain_le_input` found a narrow OR gate `u = d`!).
  -- Let's explicitly record `isNarrowOr C d`!
  have hd_nw : isNarrowOr C d := by
    by_contra hnot
    have hle := and_chain_le_input hC hE hv₀_nb ReflTransGen.refl (fun u hu _ hnw => by
      have hul : Live C u := by
        have hs : ∀ x y, Trace C (fun z => ¬ Branch C z) x y → Live C x → Live C y := by
          intro x y hxy; induction hxy with | refl => exact id | tail _ h _ => intro _; exact h.2.2
        exact hs v₀.val u hu (input_live hE v₀)
      exact hnot (hd_uniq u hul hnw ▸ hnw))
    obtain ⟨a, b, hav, hbv, hab⟩ := bowtie_edge_avoid v₀
    have ht := hle (pairIn a b) ((bowtie_pair_iff hE a b).mpr hab)
    simp only [pairIn, decide_eq_true_eq] at ht
    rcases ht with rfl | rfl
    · exact hav rfl
    · exact hbv rfl
  obtain ⟨dp, dg, hdg, hdp, hd_or⟩ := hd_nw.1
  have hd5 : 5 ≤ d := by omega
  rcases hd_on.1.cases_tail with heq | ⟨p, hTp, hpB, hlnp⟩
  · have := v₀.isLt; omega
  obtain ⟨dp', dg', a, b, hdg', hdp', hab, hlna, hlnb, hall, hain, hbin⟩ := tightCut_gate_inputs hC hE hT hdl hd5
  have hpeq : dp' = dp := by omega
  subst dp'; rw [hdg] at hdg'; cases hdg'
  -- Pick `q ≠ p` among `{a, b}`!
  have hq_ex : ∃ q, q ≠ p ∧ LNext C q d ∧ (∀ i ∈ dg.inputs, i = p ∨ i = q) ∧ p ∈ dg.inputs ∧ q ∈ dg.inputs := by
    have hpin : p ∈ dg.inputs := by
      obtain ⟨_, p', g', hg', hdp'', hpin⟩ := hlnp.1
      have : p' = dp := by omega
      subst p'; rw [hdg] at hg'; cases hg'; exact hpin
    rcases hall p hpin with rfl | rfl
    · exact ⟨b, hab.symm, hlnb, hall, hain, hbin⟩
    · exact ⟨a, hab, hlna, fun i hi => (hall i hi).symm, hbin, hain⟩
  obtain ⟨q, hqp, hlnq, hall_pq, hpin, hqin⟩ := hq_ex
  have hd_val : ∀ x, val C x d = (val C x p || val C x q) := by
    intro x
    cases hd : val C x d
    · symm; rw [Bool.or_eq_false_iff]
      constructor
      · cases hp : val C x p
        · rfl
        · have := (val_or x hdg hd_or).mpr ⟨p, hpin, by have := hlnp.1.1; omega, hp⟩
          rw [← hdp, hd] at this; cases this
      · cases hq : val C x q
        · rfl
        · have := (val_or x hdg hd_or).mpr ⟨q, hqin, by have := hlnq.1.1; omega, hq⟩
          rw [← hdp, hd] at this; cases this
    · symm; rw [Bool.or_eq_true]
      obtain ⟨i, hi, _, hix⟩ := (val_or x hdg hd_or).mp (hdp ▸ hd)
      rcases hall_pq i hi with rfl | rfl
      · exact Or.inl hix
      · exact Or.inr hix
  have hp_le : ∀ x, val C x p = true → x v₀ = true :=
    and_chain_le_input hC hE (to_nb hTp) (live_of_lnext hlnp) (fun u hu hle hnw => by
      have hul : Live C u := by
        have hs : ∀ x y, Trace C (fun z => ¬ Branch C z) x y → Live C x → Live C y := by
          intro x y hxy; induction hxy with | refl => exact id | tail _ h _ => intro _; exact h.2.2
        exact hs v₀.val u hu (input_live hE v₀)
      have hud := hd_uniq u hul hnw
      have := hlnp.1.1
      omega)
  have hq_nr : ¬ ReflTransGen (Next C) v₀.val q :=
    chain_other_not_reach (to_nb hTp) (tightCut_not_branch hE hT (live_of_lnext hlnp) hpB) hlnp hlnq hqp
  have hq_sing : ∀ u : Fin 5, val C (sing u) q = false := by
    intro u
    cases h : val C (sing u) q
    · rfl
    · have hdt : val C (sing u) d = true := by rw [hd_val, h, Bool.or_true]
      have huv0 : u = v₀ := chain_sing_subset hC hE (to_nb hd_on.1) hdl hdt
      subst huv0
      -- Since `q` doesn't depend on `v₀`, `val C zeroIn q = val C (sing v₀) q = true`!
      have hq0 : val C zeroIn q = true := by
        rw [← h]
        exact eval_eq_of_no_reach (v := u) (x := zeroIn) (y := sing u)
          (fun i hi => by simp [zeroIn, sing, hi]) q hq_nr
      -- Pick any `w ≠ u`!
      obtain ⟨w, hwu⟩ : ∃ w : Fin 5, w ≠ u := by
        fin_cases u
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      have hqw : val C (sing w) q = true :=
        val_mono hC (x := zeroIn) (y := sing w) (fun i hi => by simp [zeroIn] at hi) q hq0
      have hdw : val C (sing w) d = true := by rw [hd_val, hqw, Bool.or_true]
      exact absurd (chain_sing_subset hC hE (to_nb hd_on.1) hdl hdw) hwu
  -- Prove `AndAnc C d C.output`: every gate strictly after `d` on `d → ... → C.output` is an AND gate!
  have hd_anc : AndAnc C d C.output := by
    have htr := hd_notB_and_out.2
    suffices ∀ {y}, Trace C (fun z => z ∉ B) d y → (∀ w, Trace C (fun z => z ∉ B) d w → w ≤ y → d < w → isAndGate C w) →
        AndAnc C d y by
      apply this htr
      intro w hdw _ hltw
      have hwl : Live C w := trace_live hdw hdl
      have hw5 : 5 ≤ w := by omega
      have hw_lt := (live_le_output hwl).trans_lt (output_bounds hE).2
      set wp := w - 5
      have hwp : w = 5 + wp := by omega
      obtain ⟨wg, hwg⟩ : ∃ wg, C.gates[wp]? = some wg := ⟨C.gates[wp], List.getElem?_eq_getElem (by omega)⟩
      rcases mono_op hC hwg with hop | hop
      · exact ⟨wp, wg, hwg, hwp, hop⟩
      · exfalso
        have hw_nw : isNarrowOr C w :=
          ⟨⟨wp, wg, hwg, hwp, hop⟩, chain_not_wide hC hE (to_nb (hd_on.1.trans hdw)) hwl⟩
        have := hd_uniq w hwl hw_nw
        omega
    intro y hdy hAll
    induction hdy with
    | refl => exact ReflTransGen.refl
    | @tail a c hda hac ih =>
      have hda_and := ih (fun w hdw hle hlt => hAll w hdw (hle.trans hac.2.1.1.le) hlt)
      have hc_and := hAll c (hda.tail hac) le_rfl (lt_of_le_of_lt (trace_le hda) hac.2.1.1)
      exact hda_and.tail ⟨hac.2, hc_and⟩
  exact ⟨p, q, hqp.symm, hlnp, hlnq, hTp, hpB, hd_notB_and_out.1, hdl, hd_nw.1, hd_val, hp_le, hq_nr, hq_sing, hd_anc, hd_notB_and_out.2⟩

theorem trace_notB_to_nb {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {x y : ℕ} (h : Trace C (fun z => z ∉ B) x y) : Trace C (fun z => ¬ Branch C z) x y := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ step ih => exact ih.tail ⟨tightCut_not_branch hE hT (live_of_lnext step.2) step.1, step.2⟩

theorem trace_notB_live {C : Circuit} {B : Finset ℕ} {x y : ℕ}
    (h : Trace C (fun z => z ∉ B) x y) (hx : Live C x) : Live C y := by
  induction h with
  | refl => exact hx
  | tail _ step _ => exact step.2.2

theorem trace_nb_live {C : Circuit} {x y : ℕ}
    (h : Trace C (fun z => ¬ Branch C z) x y) (hx : Live C x) : Live C y := by
  induction h with
  | refl => exact hx
  | tail _ step _ => exact step.2.2

theorem trace_notB_det {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {x y z : ℕ} (hxy : Trace C (fun q => q ∉ B) x y) (hxz : Trace C (fun q => q ∉ B) x z)
    (hle : y ≤ z) : Trace C (fun q => q ∉ B) y z := by
  induction hxy using ReflTransGen.head_induction_on with
  | refl => exact hxz
  | @head s t hst hty ih =>
    rcases hxz.cases_head with rfl | ⟨t', hst', ht'z⟩
    · have := trace_le hty; have := hst.2.1.1; omega
    · have hteq : t' = t :=
        trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hst.2) hst.1) hst'.2 hst.2
      subst hteq
      exact ih ht'z

theorem trace_nb_det {C : Circuit} {x y z : ℕ}
    (hxy : Trace C (fun q => ¬ Branch C q) x y) (hxz : Trace C (fun q => ¬ Branch C q) x z)
    (hle : y ≤ z) : Trace C (fun q => ¬ Branch C q) y z := by
  induction hxy using ReflTransGen.head_induction_on with
  | refl => exact hxz
  | @head s t hst hty ih =>
    rcases hxz.cases_head with rfl | ⟨t', hst', ht'z⟩
    · have := trace_le hty; have := hst.2.1.1; omega
    · have hteq : t' = t := trace_lnext_unique hst.1 hst'.2 hst.2
      subst hteq
      exact ih ht'z

theorem trace_notB_of_B_not_out {C : Circuit} {B : Finset ℕ} (hT : TightCut C B)
    {b : ℕ} (hb : b ∈ B) (h : Trace C (fun q => q ∉ B) b C.output) : False := by
  rcases h.cases_head with hbo | ⟨_, step, _⟩
  · exact (Finset.mem_erase.mp (hT.1 hb)).1 hbo
  · exact step.1 hb

/-- Two wires reaching distinct inputs `w₁ ≠ w₂` (both `∉ B`) of a common gate `g` are
    incomparable under `Trace (· ∉ B)`. -/
theorem incomp_of_distinct_inputs {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {r₁ r₂ w₁ w₂ g : ℕ} (hne : w₁ ≠ w₂) (hw1B : w₁ ∉ B) (hw2B : w₂ ∉ B)
    (hln1 : LNext C w₁ g) (hln2 : LNext C w₂ g)
    (h1 : Trace C (fun q => q ∉ B) r₁ w₁) (h2 : Trace C (fun q => q ∉ B) r₂ w₂) :
    ¬ Trace C (fun q => q ∉ B) r₁ r₂ ∧ ¬ Trace C (fun q => q ∉ B) r₂ r₁ := by
  have aux : ∀ a₁ a₂ u₁ u₂ : ℕ, u₁ ≠ u₂ → u₁ ∉ B → u₂ ∉ B → LNext C u₁ g → LNext C u₂ g →
      Trace C (fun q => q ∉ B) a₁ u₁ → Trace C (fun q => q ∉ B) a₂ u₂ →
      ¬ Trace C (fun q => q ∉ B) a₁ a₂ := by
    intro a₁ a₂ u₁ u₂ hu12 hu1B hu2B hlu1 hlu2 ha1 ha2 h12
    have ha1_u2 : Trace C (fun q => q ∉ B) a₁ u₂ := h12.trans ha2
    rcases le_total u₁ u₂ with hle | hle
    · have htr := trace_notB_det hE hT ha1 ha1_u2 hle
      rcases htr.cases_head with rfl | ⟨z, hz, hzu2⟩
      · exact hu12 rfl
      · have hzg : z = g := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hlu1) hu1B) hz.2 hlu1
        subst z
        have := trace_le hzu2; have := hlu2.1.1; omega
    · have htr := trace_notB_det hE hT ha1_u2 ha1 hle
      rcases htr.cases_head with rfl | ⟨z, hz, hzu1⟩
      · exact hu12 rfl
      · have hzg : z = g := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hlu2) hu2B) hz.2 hlu2
        subst z
        have := trace_le hzu1; have := hlu1.1.1; omega
  exact ⟨aux r₁ r₂ w₁ w₂ hne hw1B hw2B hln1 hln2 h1 h2,
         aux r₂ r₁ w₂ w₁ hne.symm hw2B hw1B hln2 hln1 h2 h1⟩

/-- If `d` is the unique narrow OR gate and `Trace (· ∉ B) d C.output`, then any `b ∈ B` on
    `w`'s branch-free chain avoids `d`, satisfies `b ≤ x_w`, and if `b ≠ w.val` then `isAndGate C b`. -/
theorem other_branch_le_input {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {d : ℕ} (hd_uniq : ∀ z, Live C z → isNarrowOr C z → z = d)
    (hd_out : Trace C (fun z => z ∉ B) d C.output)
    {w : Fin 5} {b : ℕ} (hbB : b ∈ B) (hwb : Trace C (fun z => z ∉ B) w.val b) :
    (∀ x, val C x b = true → x w = true) ∧ (b ≠ w.val → isAndGate C b) := by
  have hbl : Live C b := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hbB))
  have hnoD : ∀ u, Trace C (fun z => ¬ Branch C z) w.val u → u ≤ b → ¬ isNarrowOr C u := by
    intro u hu hle hnw
    have hul : Live C u := trace_nb_live hu (input_live hE w)
    have hud : u = d := hd_uniq u hul hnw
    subst u
    -- Since `Trace (· ∉ B) w.val b` and `Trace (¬ Branch) w.val d` with `d ≤ b`, we get `Trace (· ∉ B) w.val d` and `Trace (· ∉ B) d b`.
    have hwd : Trace C (fun z => z ∉ B) w.val d := by
      suffices ∀ {x y}, Trace C (fun z => z ∉ B) x b → Trace C (fun z => ¬ Branch C z) x y → y ≤ b →
          Trace C (fun z => z ∉ B) x y from this hwb hu hle
      intro x y hxb
      induction hxb using ReflTransGen.head_induction_on with
      | refl =>
        intro hxy hyle
        have := trace_le hxy
        have : b = y := by omega
        subst this
        exact ReflTransGen.refl
      | @head a c hac hcb ih =>
        intro hxy hyle
        rcases hxy.cases_head with rfl | ⟨c', hac', hc'y⟩
        · exact ReflTransGen.refl
        · have hceq : c' = c := trace_lnext_unique hac'.1 hac'.2 hac.2
          subst c'
          exact ReflTransGen.head hac (ih hc'y hyle)
    have hdb : Trace C (fun z => z ∉ B) d b := trace_notB_det hE hT hwd hwb hle
    have hb_out : Trace C (fun z => z ∉ B) b C.output :=
      trace_notB_det hE hT hdb hd_out (live_le_output hbl)
    exact trace_notB_of_B_not_out hT hbB hb_out
  constructor
  · exact and_chain_le_input hC hE (trace_notB_to_nb hE hT hwb) hbl hnoD
  · intro hbne
    have hb5 : 5 ≤ b := by
      by_contra hlt; push Not at hlt
      rcases hwb.cases_tail with heq | ⟨u, _, _, hln⟩
      · exact hbne heq
      · have := hln.1.2.choose_spec.choose_spec.2.1; omega
    have hlt := (live_le_output hbl).trans_lt (output_bounds hE).2
    set p := b - 5
    have hbp : b = 5 + p := by omega
    obtain ⟨g, hg⟩ : ∃ g, C.gates[p]? = some g := ⟨C.gates[p], List.getElem?_eq_getElem (by omega)⟩
    rcases mono_op hC hg with hop | hop
    · exact ⟨p, g, hg, hbp, hop⟩
    · exfalso
      exact hnoD b (trace_notB_to_nb hE hT hwb) le_rfl
        ⟨⟨p, g, hg, hbp, hop⟩, chain_not_wide hC hE (trace_notB_to_nb hE hT hwb) hbl⟩

/-- On an AND-only branch-free chain `v₀ → ... → p` where `val (sing v₀) p = false`,
    find the first AND gate `a₀` with `val (sing v₀) a₀ = false` and its other input `e_w`. -/
theorem partner_before_d {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {v₀ : Fin 5} {p : ℕ}
    (hTp : Trace C (fun z => z ∉ B) v₀.val p) (hpl : Live C p)
    (hnoD : ∀ u, Trace C (fun z => ¬ Branch C z) v₀.val u → u ≤ p → ¬ isNarrowOr C u)
    (hp_false : val C (sing v₀) p = false) :
    ∃ e_w a₀, Live C e_w ∧ LNext C e_w a₀ ∧ a₀ ≤ p ∧
      Trace C (fun z => z ∉ B) v₀.val a₀ ∧
      (∀ w : Fin 5, bowtieAdj v₀ w → val C (sing w) e_w = true) ∧
      isWide C e_w ∧
      ¬ ReflTransGen (Next C) v₀.val e_w ∧
      (e_w ∉ B → Trace C (fun z => z ∉ B) e_w p) := by
  have hnb := trace_notB_to_nb hE hT hTp
  -- Induct on `hTp` to find the first wire where `val (sing v₀) = false`!
  suffices aux : ∀ y, Trace C (fun z => z ∉ B) v₀.val y → y ≤ p → val C (sing v₀) y = false →
      ∃ e_w a₀, Live C e_w ∧ LNext C e_w a₀ ∧ a₀ ≤ y ∧
        Trace C (fun z => z ∉ B) v₀.val a₀ ∧
        (∀ w : Fin 5, bowtieAdj v₀ w → val C (sing w) e_w = true) ∧
        ¬ ReflTransGen (Next C) v₀.val e_w by
    obtain ⟨e_w, a₀, hewl, hlne, ha0le, hTa0, hew_nbr, hew_nr⟩ := aux p hTp le_rfl hp_false
    obtain ⟨w₁, w₂, hw12, hvw1, hvw2⟩ := bowtie_deg2 v₀
    refine ⟨e_w, a₀, hewl, hlne, ha0le, hTa0, hew_nbr, ⟨w₁, w₂, hw12, hew_nbr w₁ hvw1, hew_nbr w₂ hvw2⟩, hew_nr, ?_⟩
    intro heB
    have ha0p : Trace C (fun z => z ∉ B) a₀ p := trace_notB_det hE hT hTa0 hTp ha0le
    exact ReflTransGen.head ⟨heB, hlne⟩ ha0p
  intro y hy
  induction hy with
  | refl =>
    intro _ hf
    rw [val_input] at hf; simp [sing] at hf
  | @tail u a hTu hua ih =>
    intro hale haf
    cases hu : val C (sing v₀) u
    · obtain ⟨e_w, a₀, hewl, hlne, ha0u, hTa0, hew_nbr, hew_nr⟩ := ih (hua.2.1.1.le.trans hale) hu
      exact ⟨e_w, a₀, hewl, hlne, ha0u.trans hua.2.1.1.le, hTa0, hew_nbr, hew_nr⟩
    · -- `a` is the FIRST wire with `val (sing v₀) a = false`, while `u` has `val (sing v₀) u = true`!
      have hal : Live C a := hua.2.2
      have ha5 : 5 ≤ a := by obtain ⟨_, _, _, _, hap, _⟩ := hua.2.1; omega
      obtain ⟨ap, ag, i₁, i₂, hag, hap, hi12, hlni1, hlni2, hall, hi1in, hi2in⟩ :=
        tightCut_gate_inputs hC hE hT hal ha5
      have ha_and : ag.op = GateOp.and := by
        rcases mono_op hC hag with hop | hop
        · exact hop
        · exfalso
          exact hnoD a (trace_notB_to_nb hE hT (hTu.tail hua)) hale
            ⟨⟨ap, ag, hag, hap, hop⟩, chain_not_wide hC hE (trace_notB_to_nb hE hT (hTu.tail hua)) hal⟩
      have huin : u ∈ ag.inputs := by
        obtain ⟨_, ap', ag', hag', hap', huin⟩ := hua.2.1
        have : ap' = ap := by omega
        subst ap'; rw [hag] at hag'; cases hag'; exact huin
      have he_ex : ∃ e_w, e_w ≠ u ∧ LNext C e_w a ∧ e_w ∈ ag.inputs := by
        rcases hall u huin with rfl | rfl
        · exact ⟨i₂, hi12.symm, hlni2, hi2in⟩
        · exact ⟨i₁, hi12, hlni1, hi1in⟩
      obtain ⟨e_w, heu, hlne, hein⟩ := he_ex
      have he_nr : ¬ ReflTransGen (Next C) v₀.val e_w :=
        chain_other_not_reach (trace_notB_to_nb hE hT hTu)
          (tightCut_not_branch hE hT (live_of_lnext hua.2) hua.1) hua.2 hlne heu
      refine ⟨e_w, a, live_of_lnext hlne, hlne, le_rfl, hTu.tail hua, ?_, he_nr⟩
      intro w hvw
      have ha_pair : val C (pairIn v₀ w) a = true := by
        by_contra hfa
        have hfa' : val C (pairIn v₀ w) a = false := Bool.eq_false_iff.mpr hfa
        have hres := no_bypass_output hC (trace_notB_to_nb hE hT (hTu.tail hua)) hal
          (x := pairIn v₀ w) (y := sing w)
          (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_left hi)
          (fun ht => by rw [hfa'] at ht; cases ht)
          ((bowtie_pair_iff hE v₀ w).mpr hvw)
        rw [bowtie_sing hE w] at hres; cases hres
      have he_pair : val C (pairIn v₀ w) e_w = true :=
        ((val_and (pairIn v₀ w) hag ha_and).mp (hap ▸ ha_pair) e_w hein).2
      rw [← he_pair]
      exact eval_eq_of_no_reach (v := v₀) (x := sing w) (y := pairIn v₀ w)
        (fun i hi => by simp [sing, pairIn, hi]) e_w he_nr

/-- Helper: if every wire strictly after `x` on `Trace (· ∉ B) x t` is an `AND` gate, then `AndAnc C x t`. -/
theorem trace_notB_to_andAnc {C : Circuit} {B : Finset ℕ} {x t : ℕ}
    (h : Trace C (fun z => z ∉ B) x t)
    (hand : ∀ w, Trace C (fun z => z ∉ B) x w → x < w → w ≤ t → isAndGate C w) :
    AndAnc C x t := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail u a hxu hua ih =>
    have h1 := ih (fun w hxw hlt hle => hand w hxw hlt (hle.trans hua.2.1.1.le))
    have h2 := hand a (hxu.tail hua) (lt_of_le_of_lt (trace_le hxu) hua.2.1.1) le_rfl
    exact h1.tail ⟨hua.2, h2⟩

/-- On an AND-only branch-free segment `d → ... → t` continuing `v₀ → ... → d`, if
    `val (sing v₀) d = true` and `val (sing v₀) t = false`, find the first AND gate `a_after`
    with `val (sing v₀) a_after = false` and its other input `r`. -/
theorem partner_after_d {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {v₀ : Fin 5} {d t : ℕ}
    (hTd : Trace C (fun z => z ∉ B) v₀.val d)
    (hdt : Trace C (fun z => z ∉ B) d t)
    (hdt_and : ∀ w, Trace C (fun z => z ∉ B) d w → d < w → w ≤ t → isAndGate C w)
    (hd_true : val C (sing v₀) d = true)
    (ht_false : val C (sing v₀) t = false) :
    ∃ r u_after a_after, Live C r ∧ LNext C u_after a_after ∧ LNext C r a_after ∧
      r ≠ u_after ∧ u_after ∉ B ∧
      Trace C (fun z => z ∉ B) d u_after ∧ AndAnc C a_after t ∧
      AndAnc C r t ∧
      val C (sing v₀) r = false ∧
      (∀ w : Fin 5, bowtieAdj v₀ w → val C (sing w) r = true) ∧
      isWide C r ∧
      ¬ ReflTransGen (Next C) v₀.val r ∧
      Trace C (fun z => z ∉ B) a_after t ∧
      (r ∉ B → Trace C (fun z => z ∉ B) r t) := by
  suffices aux : ∀ y, Trace C (fun z => z ∉ B) d y → y ≤ t → val C (sing v₀) y = false →
      ∃ r u_after a_after, Live C r ∧ LNext C u_after a_after ∧ LNext C r a_after ∧
        r ≠ u_after ∧ u_after ∉ B ∧
        Trace C (fun z => z ∉ B) d u_after ∧ a_after ≤ y ∧
        isAndGate C a_after ∧
        val C (sing v₀) r = false ∧
        (∀ w : Fin 5, bowtieAdj v₀ w → val C (sing w) r = true) ∧
        ¬ ReflTransGen (Next C) v₀.val r by
    obtain ⟨r, u_after, a_after, hrl, hlnu, hlnr, hru, huB, hdu, ha_le, ha_and, hrf, hr_nbr, hr_nr⟩ :=
      aux t hdt le_rfl ht_false
    have hda : Trace C (fun z => z ∉ B) d a_after := hdu.tail ⟨huB, hlnu⟩
    have hat : Trace C (fun z => z ∉ B) a_after t := trace_notB_det hE hT hda hdt ha_le
    have hat_anc : AndAnc C a_after t := trace_notB_to_andAnc hat (fun w haw hlt hle =>
      hdt_and w (hda.trans haw) (lt_of_le_of_lt (trace_le hda) hlt) hle)
    have hrt_anc : AndAnc C r t := ReflTransGen.head ⟨hlnr, ha_and⟩ hat_anc
    obtain ⟨w₁, w₂, hw12, hvw1, hvw2⟩ := bowtie_deg2 v₀
    exact ⟨r, u_after, a_after, hrl, hlnu, hlnr, hru, huB, hdu, hat_anc, hrt_anc, hrf, hr_nbr,
      ⟨w₁, w₂, hw12, hr_nbr w₁ hvw1, hr_nbr w₂ hvw2⟩, hr_nr, hat,
      fun hrB => ReflTransGen.head ⟨hrB, hlnr⟩ hat⟩
  intro y hdy
  induction hdy with
  | refl => intro _ hf; rw [hd_true] at hf; cases hf
  | @tail u a hdu hua ih =>
    intro hale haf
    cases hu : val C (sing v₀) u
    · obtain ⟨r, ua, aa, hrl, hlnu, hlnr, hru, huB, hdua, haau, ha_and, hrf, hr_nbr, hr_nr⟩ :=
        ih (hua.2.1.1.le.trans hale) hu
      exact ⟨r, ua, aa, hrl, hlnu, hlnr, hru, huB, hdua, haau.trans hua.2.1.1.le, ha_and, hrf, hr_nbr, hr_nr⟩
    · have hal : Live C a := hua.2.2
      have ha_and : isAndGate C a := hdt_and a (hdu.tail hua) (lt_of_le_of_lt (trace_le hdu) hua.2.1.1) hale
      obtain ⟨ap, ag, hag, hap, hop⟩ := ha_and
      have ha5 : 5 ≤ a := by omega
      obtain ⟨ap', ag', i₁, i₂, hag', hap', hi12, hlni1, hlni2, hall, hi1in, hi2in⟩ :=
        tightCut_gate_inputs hC hE hT hal ha5
      have : ap' = ap := by omega
      subst ap'; rw [hag] at hag'; cases hag'
      have huin : u ∈ ag.inputs := by
        obtain ⟨_, p', g', hg', hap'', huin⟩ := hua.2.1
        have : p' = ap := by omega
        subst p'; rw [hag] at hg'; cases hg'; exact huin
      have hr_ex : ∃ r, r ≠ u ∧ LNext C r a ∧ r ∈ ag.inputs := by
        rcases hall u huin with rfl | rfl
        · exact ⟨i₂, hi12.symm, hlni2, hi2in⟩
        · exact ⟨i₁, hi12, hlni1, hi1in⟩
      obtain ⟨r, hru, hlnr, hrin⟩ := hr_ex
      have hrf : val C (sing v₀) r = false := by
        cases h : val C (sing v₀) r
        · rfl
        · have hat : val C (sing v₀) a = true := by
            rw [hap, val_and (sing v₀) hag hop]
            intro i hi
            rcases hall i hi with rfl | rfl <;> rcases hall u huin with h1 | h2 <;>
              rcases hall r hrin with h3 | h4
            all_goals first
              | (subst u; exact ⟨by have := hua.2.1.1; omega, hu⟩)
              | (subst r; exact ⟨by have := hlnr.1.1; omega, h⟩)
              | (exact absurd (h1.trans h3.symm) hru.symm)
              | (exact absurd (h2.trans h4.symm) hru.symm)
              | (subst i; exact ⟨by have := hua.2.1.1; omega, hu⟩)
              | (subst i; exact ⟨by have := hlnr.1.1; omega, h⟩)
          rw [haf] at hat; cases hat
      have hTvu : Trace C (fun z => z ∉ B) v₀.val u := hTd.trans hdu
      have hr_nr : ¬ ReflTransGen (Next C) v₀.val r :=
        chain_other_not_reach (trace_notB_to_nb hE hT hTvu)
          (tightCut_not_branch hE hT (live_of_lnext hua.2) hua.1) hua.2 hlnr hru
      refine ⟨r, u, a, live_of_lnext hlnr, hua.2, hlnr, hru, hua.1, hdu, le_rfl,
        ⟨ap, ag, hag, hap, hop⟩, hrf, ?_, hr_nr⟩
      intro w hvw
      have ha_pair : val C (pairIn v₀ w) a = true := by
        by_contra hfa
        have hfa' : val C (pairIn v₀ w) a = false := Bool.eq_false_iff.mpr hfa
        have hres := no_bypass_output hC (trace_notB_to_nb hE hT (hTvu.tail hua)) hal
          (x := pairIn v₀ w) (y := sing w)
          (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_left hi)
          (fun ht => by rw [hfa'] at ht; cases ht)
          ((bowtie_pair_iff hE v₀ w).mpr hvw)
        rw [bowtie_sing hE w] at hres; cases hres
      have hr_pair : val C (pairIn v₀ w) r = true :=
        ((val_and (pairIn v₀ w) hag hop).mp (hap ▸ ha_pair) r hrin).2
      rw [← hr_pair]
      exact eval_eq_of_no_reach (v := v₀) (x := sing w) (y := pairIn v₀ w)
        (fun i hi => by simp [sing, pairIn, hi]) r hr_nr

/-- If `d → ... → C.output` is an AND-only chain avoiding `B`, every vertex `w ≠ v₀` hits `b w ∈ B`
    with `b w ≤ x_w`, and every edge of `AllBEdges C B` outside `R.biUnion (LeafEdges C B)`
    (where every `r ∈ R` reaches `d` via `Trace (· ∉ B)`) starts at `b c`, then `d = C.output`. -/
theorem no_and_after_d_if_le_one_leftover {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {v₀ c : Fin 5} {b : Fin 5 → ℕ} (hcv₀ : c ≠ v₀)
    (hB_eq : B = (Finset.univ.erase v₀).image b)
    (hb_tr : ∀ w : Fin 5, w ≠ v₀ → Trace C (fun z => z ∉ B) w.val (b w))
    (hb_le : ∀ w : Fin 5, w ≠ v₀ → ∀ x, val C x (b w) = true → x w = true)
    {d : ℕ} (hTd : Trace C (fun z => z ∉ B) v₀.val d)
    (hd_out : Trace C (fun z => z ∉ B) d C.output)
    (hd_and : AndAnc C d C.output)
    {R : Finset ℕ} (hR_tr : ∀ r ∈ R, r ∉ B ∧ Trace C (fun z => z ∉ B) r d)
    (hleft : ∀ p ∈ AllBEdges C B, p ∉ R.biUnion (fun r => LeafEdges C B r) → p.1 = b c) :
    d = C.output := by
  classical
  rcases hd_out.cases_head with rfl | ⟨a, hda, ha_out⟩
  · rfl
  · exfalso
    have hal : Live C a := hda.2.2
    have ha5 : 5 ≤ a := by obtain ⟨_, _, _, _, hap, _⟩ := hda.2.1; omega
    obtain ⟨ap, ag, i₁, i₂, hag, hap, hi12, hlni1, hlni2, hall, hi1in, hi2in⟩ :=
      tightCut_gate_inputs hC hE hT hal ha5
    have hdin : d ∈ ag.inputs := by
      obtain ⟨_, p', g', hg', hap', hdin⟩ := hda.2.1
      have : p' = ap := by omega
      subst p'; rw [hag] at hg'; cases hg'; exact hdin
    have hr_ex : ∃ r, r ≠ d ∧ LNext C r a ∧ r ∈ ag.inputs := by
      rcases hall d hdin with rfl | rfl
      · exact ⟨i₂, hi12.symm, hlni2, hi2in⟩
      · exact ⟨i₁, hi12, hlni1, hi1in⟩
    obtain ⟨r, hrd, hlnr, hrin⟩ := hr_ex
    -- Show `AndAnc C r C.output` (first show `AndAnc C a C.output` and `isAndGate C a`)!
    have ha_anc_and : isAndGate C a ∧ AndAnc C a C.output := by
      rcases hd_and.cases_head with hdo | ⟨a', hda', ha'o⟩
      · have := hda.2.1.1; have := live_le_output hal; omega
      · have haeq : a' = a :=
          trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hda.2) hda.1) hda'.1 hda.2
        subst a'
        exact ⟨hda'.2, ha'o⟩
    have hr_anc : AndAnc C r C.output := ReflTransGen.head ⟨hlnr, ha_anc_and.1⟩ ha_anc_and.2
    by_cases hrB : r ∈ B
    · rw [hB_eq] at hrB
      obtain ⟨w, hw, hbw⟩ := Finset.mem_image.mp hrB
      have hwne : w ≠ v₀ := (Finset.mem_erase.mp hw).1
      obtain ⟨x, y, hxw, hyw, hxy⟩ := bowtie_edge_avoid w
      have hrt := andAnc_val_le hr_anc (pairIn x y) ((bowtie_pair_iff hE x y).mpr hxy)
      have hwt := hb_le w hwne (pairIn x y) (hbw ▸ hrt)
      simp only [pairIn, decide_eq_true_eq] at hwt
      rcases hwt with rfl | rfl
      · exact hxw rfl
      · exact hyw rfl
    · -- Show `∀ u ∈ Internal C B r, 5 ≤ u`!
      have hnoin : ∀ u ∈ Internal C B r, 5 ≤ u := by
        intro u hu
        obtain ⟨_, _, huTr⟩ := (mem_Internal hE).mp hu
        by_contra hlt; push Not at hlt
        let w : Fin 5 := ⟨u, hlt⟩
        by_cases hwv : w = v₀
        · have hv0r : Trace C (fun z => z ∉ B) v₀.val r := by rw [← hwv]; exact huTr
          exact (incomp_of_distinct_inputs hE hT hrd hrB hda.1 hlnr hda.2 ReflTransGen.refl hTd).2 hv0r
        · have hwO : Trace C (fun z => z ∉ B) w.val C.output :=
            (huTr.tail ⟨hrB, hlnr⟩).trans ha_out
          have hwb := hb_tr w hwv
          have hbwB : b w ∈ B := by rw [hB_eq]; exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩, rfl⟩
          have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hbwB))
          exact trace_notB_of_B_not_out hT hbwB (trace_notB_det hE hT hwb hwO (live_le_output hbwl))
      -- Every `b' ∈ Leaves C B r` equals `b c`!
      have hLeaves_sub : ∀ b' ∈ Leaves C B r, b' = b c := by
        intro b' hb'
        obtain ⟨p, hpL, rfl⟩ := Finset.mem_image.mp hb'
        apply hleft p (leafEdges_subset_allBEdges hE hpL)
        intro hpU
        obtain ⟨h, hhR, hpH⟩ := Finset.mem_biUnion.mp hpU
        have hincomp := incomp_of_distinct_inputs hE hT hrd hrB hda.1 hlnr hda.2 ReflTransGen.refl (hR_tr h hhR).2
        exact Finset.disjoint_left.mp (leafEdges_disjoint hE hT hincomp.1 hincomp.2) hpL hpH
      -- Pick an edge `{x, y}` avoiding `c`: then `val (pairIn x y) r = false`, contradicting `AndAnc r C.output`!
      obtain ⟨x, y, hxc, hyc, hxy⟩ := bowtie_edge_avoid c
      have hrf : val C (pairIn x y) r = false := by
        apply internal_false hC hE hT hnoin _ r ((mem_Internal hE).mpr ⟨live_of_lnext hlnr, hrB, ReflTransGen.refl⟩)
        intro b' hb'
        rw [hLeaves_sub b' hb']
        cases h : val C (pairIn x y) (b c)
        · rfl
        · have hc := hb_le c hcv₀ (pairIn x y) h
          simp only [pairIn, decide_eq_true_eq] at hc
          rcases hc with rfl | rfl
          · exact absurd rfl hxc
          · exact absurd rfl hyc
      have hrt := andAnc_val_le hr_anc (pairIn x y) ((bowtie_pair_iff hE x y).mpr hxy)
      rw [hrf] at hrt; cases hrt

/-- If all edges of `AllBEdges C B` are already covered by `LeafEdges C B r_main ∪ R.biUnion (LeafEdges C B)`,
    then `a_main` is the ONLY gate on `d → ... → C.output`, so `d ∧ r_main → C.output`. -/
theorem only_one_and_after_d_if_all_used {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {v₀ : Fin 5} {b : Fin 5 → ℕ}
    (hB_eq : B = (Finset.univ.erase v₀).image b)
    (hb_tr : ∀ w : Fin 5, w ≠ v₀ → Trace C (fun z => z ∉ B) w.val (b w))
    (hb_le : ∀ w : Fin 5, w ≠ v₀ → ∀ x, val C x (b w) = true → x w = true)
    {d r_main u_main a_main : ℕ}
    (hTd : Trace C (fun z => z ∉ B) v₀.val d)
    (hd_out : Trace C (fun z => z ∉ B) d C.output)
    (hd_and : AndAnc C d C.output)
    (hdu : Trace C (fun z => z ∉ B) d u_main) (huB : u_main ∉ B)
    (hlnu : LNext C u_main a_main) (hlnr : LNext C r_main a_main) (hru : r_main ≠ u_main)
    (hrB : r_main ∉ B) (ha_out : Trace C (fun z => z ∉ B) a_main C.output)
    {R : Finset ℕ} (hR_tr : ∀ r ∈ R, r ∉ B ∧ Trace C (fun z => z ∉ B) r d)
    (hall_used : AllBEdges C B ⊆ LeafEdges C B r_main ∪ R.biUnion (fun r => LeafEdges C B r)) :
    ∀ x, val C x d = true → val C x r_main = true → val C x C.output = true := by
  classical
  -- Show EVERY step `u → a` on `d → ... → C.output` has `a = a_main`!
  have hstep_eq : ∀ u a, Trace C (fun z => z ∉ B) d u → u ∉ B → LNext C u a →
      Trace C (fun z => z ∉ B) a C.output → isAndGate C a → AndAnc C a C.output → a = a_main := by
    intro u a hdu' hu'B hlnu' ha'O ha'_and ha'_anc
    by_contra hne
    have hal : Live C a := hlnu'.2
    have ha5 : 5 ≤ a := by obtain ⟨_, _, _, _, hap, _⟩ := hlnu'.1; omega
    obtain ⟨ap, ag, i₁, i₂, hag, hap, hi12, hlni1, hlni2, hall, hi1in, hi2in⟩ :=
      tightCut_gate_inputs hC hE hT hal ha5
    have huin : u ∈ ag.inputs := by
      obtain ⟨_, p', g', hg', hap', huin⟩ := hlnu'.1
      have : p' = ap := by omega
      subst p'; rw [hag] at hg'; cases hg'; exact huin
    have hr'_ex : ∃ r', r' ≠ u ∧ LNext C r' a ∧ r' ∈ ag.inputs := by
      rcases hall u huin with rfl | rfl
      · exact ⟨i₂, hi12.symm, hlni2, hi2in⟩
      · exact ⟨i₁, hi12, hlni1, hi1in⟩
    obtain ⟨r', hr'u, hlnr', _⟩ := hr'_ex
    have hr'_anc : AndAnc C r' C.output := ReflTransGen.head ⟨hlnr', ha'_and⟩ ha'_anc
    by_cases hr'B : r' ∈ B
    · rw [hB_eq] at hr'B
      obtain ⟨w, hw, hbw⟩ := Finset.mem_image.mp hr'B
      have hwne : w ≠ v₀ := (Finset.mem_erase.mp hw).1
      obtain ⟨x, y, hxw, hyw, hxy⟩ := bowtie_edge_avoid w
      have hrt := andAnc_val_le hr'_anc (pairIn x y) ((bowtie_pair_iff hE x y).mpr hxy)
      have hwt := hb_le w hwne (pairIn x y) (hbw ▸ hrt)
      simp only [pairIn, decide_eq_true_eq] at hwt
      rcases hwt with rfl | rfl
      · exact hxw rfl
      · exact hyw rfl
    · have hnoin : ∀ q ∈ Internal C B r', 5 ≤ q := by
        intro q hq
        obtain ⟨_, _, hqTr⟩ := (mem_Internal hE).mp hq
        by_contra hlt; push Not at hlt
        let w : Fin 5 := ⟨q, hlt⟩
        by_cases hwv : w = v₀
        · have hv0r' : Trace C (fun z => z ∉ B) v₀.val r' := by rw [← hwv]; exact hqTr
          exact (incomp_of_distinct_inputs hE hT hr'u hr'B hu'B hlnr' hlnu' ReflTransGen.refl (hTd.trans hdu')).2 hv0r'
        · have hwO : Trace C (fun z => z ∉ B) w.val C.output := (hqTr.tail ⟨hr'B, hlnr'⟩).trans ha'O
          have hwb := hb_tr w hwv
          have hbwB : b w ∈ B := by rw [hB_eq]; exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩, rfl⟩
          have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hbwB))
          exact trace_notB_of_B_not_out hT hbwB (trace_notB_det hE hT hwb hwO (live_le_output hbwl))
      obtain ⟨p, hpL⟩ := leafEdges_nonempty hC hE hT (live_of_lnext hlnr') hr'B hnoin
      have hpU := hall_used (leafEdges_subset_allBEdges hE hpL)
      rcases Finset.mem_union.mp hpU with hpM | hpR
      · -- `r'` and `r_main` are incomparable! Compare `a` and `a_main` (`a ≠ a_main`)!
        have hda : Trace C (fun z => z ∉ B) d a := hdu'.tail ⟨hu'B, hlnu'⟩
        have hdam : Trace C (fun z => z ∉ B) d a_main := hdu.tail ⟨huB, hlnu⟩
        have hincomp : ¬ Trace C (fun z => z ∉ B) r' r_main ∧ ¬ Trace C (fun z => z ∉ B) r_main r' := by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · -- `a < a_main`, so `a ≤ u_main`!
            have hau : Trace C (fun z => z ∉ B) a u_main := by
              have ha_am : Trace C (fun z => z ∉ B) a a_main := trace_notB_det hE hT hda hdam hlt.le
              have hau' : a ≤ u_main := by
                rcases ha_am.cases_tail with heq | ⟨u₂, ha_u2, hu2B, hln_u2⟩
                · exact absurd heq.symm hne
                · have hdu2 : Trace C (fun z => z ∉ B) d u₂ := hda.trans ha_u2
                  -- Compare `u₂` and `u_main`: both step to `a_main` along `d → ... → a_main`!
                  rcases le_total u₂ u_main with hle | hle
                  · exact (trace_le ha_u2).trans hle
                  · have hu_u2 := trace_notB_det hE hT hdu hdu2 hle
                    rcases hu_u2.cases_head with rfl | ⟨z, hstep, hzu2⟩
                    · exact trace_le ha_u2
                    · have hza : z = a_main := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hlnu) huB) hstep.2 hlnu
                      subst z
                      have := trace_le hzu2; have := hln_u2.1.1; omega
              exact trace_notB_det hE hT hda hdu hau'
            exact incomp_of_distinct_inputs hE hT hru.symm huB hrB hlnu hlnr (ReflTransGen.head ⟨hr'B, hlnr'⟩ hau) ReflTransGen.refl
          · -- `a_main < a`, so `a_main ≤ u`!
            have ham_u : Trace C (fun z => z ∉ B) a_main u := by
              have ham_a : Trace C (fun z => z ∉ B) a_main a := trace_notB_det hE hT hdam hda hgt.le
              have hle' : a_main ≤ u := by
                rcases ham_a.cases_tail with heq | ⟨u₂, ham_u2, hu2B, hln_u2⟩
                · exact absurd heq hne
                · have hdu2 : Trace C (fun z => z ∉ B) d u₂ := hdam.trans ham_u2
                  rcases le_total u₂ u with hle | hle
                  · exact (trace_le ham_u2).trans hle
                  · have hu_u2 := trace_notB_det hE hT hdu' hdu2 hle
                    rcases hu_u2.cases_head with rfl | ⟨z, hstep, hzu2⟩
                    · exact trace_le ham_u2
                    · have hza : z = a := trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hlnu') hu'B) hstep.2 hlnu'
                      subst z
                      have := trace_le hzu2; have := hln_u2.1.1; omega
              exact trace_notB_det hE hT hdam hdu' hle'
            exact incomp_of_distinct_inputs hE hT hr'u hr'B hu'B hlnr' hlnu' ReflTransGen.refl (ReflTransGen.head ⟨hrB, hlnr⟩ ham_u)
        exact Finset.disjoint_left.mp (leafEdges_disjoint hE hT hincomp.1 hincomp.2) hpL hpM
      · obtain ⟨h, hhR, hpH⟩ := Finset.mem_biUnion.mp hpR
        have hincomp := incomp_of_distinct_inputs hE hT hr'u hr'B hu'B hlnr' hlnu' ReflTransGen.refl ((hR_tr h hhR).2.trans hdu')
        exact Finset.disjoint_left.mp (leafEdges_disjoint hE hT hincomp.1 hincomp.2) hpL hpH
  -- Now deduce `d = u_main` AND `a_main = C.output`!
  -- First, `d → a₁` is the first step of `hd_out`, so `a₁ = a_main`, forcing `u_main = d`!
  have hd_and_all : ∀ w, Trace C (fun z => z ∉ B) d w → d < w → w ≤ C.output → isAndGate C w := by
    intro w hdw hlt hle
    -- Induct on `hd_and`!
    suffices ∀ {x}, AndAnc C x C.output → Trace C (fun z => z ∉ B) x C.output →
        Trace C (fun z => z ∉ B) x w → x < w → isAndGate C w from this hd_and hd_out hdw hlt
    intro x hx_and hxO
    induction hx_and using ReflTransGen.head_induction_on with
    | refl => intro _ hlt'; have := trace_le hdw; omega
    | @head s t hst htO ih =>
      intro hsw hlt'
      rcases hxO.cases_head with rfl | ⟨t', hst', ht'O⟩
      · have := hst.1.1.1; have := live_le_output hst.1.2; omega
      · have hteq : t' = t :=
          trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hst'.2) hst'.1) hst'.2 hst.1
        subst t'
        rcases hsw.cases_head with rfl | ⟨t₂, hst₂, ht₂w⟩
        · omega
        · have ht₂eq : t₂ = t :=
            trace_lnext_unique (tightCut_not_branch hE hT (live_of_lnext hst'.2) hst'.1) hst₂.2 hst'.2
          subst t₂
          by_cases htw : t = w
          · exact htw ▸ hst.2
          · exact ih ht'O ht₂w (lt_of_le_of_ne (trace_le ht₂w) htw)
  have hu_eq_d : u_main = d := by
    rcases hdu.cases_head with rfl | ⟨a₁, hda₁, ha₁u⟩
    · rfl
    · exfalso
      have ha₁O : Trace C (fun z => z ∉ B) a₁ C.output := (ha₁u.tail ⟨huB, hlnu⟩).trans ha_out
      have ha₁_and : isAndGate C a₁ := hd_and_all a₁ (ReflTransGen.single hda₁) hda₁.2.1.1 (live_le_output hda₁.2.2)
      have ha₁_anc : AndAnc C a₁ C.output := trace_notB_to_andAnc ha₁O (fun w haw hlt hle =>
        hd_and_all w (ReflTransGen.head hda₁ haw) (lt_trans hda₁.2.1.1 hlt) hle)
      have heq := hstep_eq d a₁ ReflTransGen.refl hda₁.1 hda₁.2 ha₁O ha₁_and ha₁_anc
      subst heq
      have := trace_le ha₁u; have := hlnu.1.1; omega
  have ha_eq_out : a_main = C.output := by
    rcases ha_out.cases_head with rfl | ⟨a₂, ham2, ha₂O⟩
    · rfl
    · exfalso
      have hdam : Trace C (fun z => z ∉ B) d a_main := hdu.tail ⟨huB, hlnu⟩
      have ha₂_and : isAndGate C a₂ :=
        hd_and_all a₂ (hdam.tail ham2) (lt_of_le_of_lt (trace_le hdam) ham2.2.1.1) (live_le_output ham2.2.2)
      have ha₂_anc : AndAnc C a₂ C.output := trace_notB_to_andAnc ha₂O (fun w haw hlt hle =>
        hd_and_all w ((hdam.tail ham2).trans haw) (lt_of_le_of_lt (trace_le (hdam.tail ham2)) hlt) hle)
      have heq := hstep_eq a_main a₂ hdam ham2.1 ham2.2 ha₂O ha₂_and ha₂_anc
      have := ham2.2.1.1; omega
  -- Evaluate `a_main = C.output` as `AND(u_main, r_main) = AND(d, r_main)`!
  intro x hdx hrx
  have hal : Live C a_main := hlnu.2
  have ha5 : 5 ≤ a_main := by obtain ⟨_, _, _, _, hap, _⟩ := hlnu.1; omega
  have hdam : Trace C (fun z => z ∉ B) d a_main := hdu.tail ⟨huB, hlnu⟩
  have ha_and : isAndGate C a_main :=
    hd_and_all a_main hdam (lt_of_le_of_lt (trace_le hdu) hlnu.1.1) (live_le_output hal)
  obtain ⟨ap, ag, hag, hap, hop⟩ := ha_and
  obtain ⟨ap', ag', i₁, i₂, hag', hap', hi12, hlni1, hlni2, hall, hi1in, hi2in⟩ :=
    tightCut_gate_inputs hC hE hT hal ha5
  have : ap' = ap := by omega
  subst ap'; rw [hag] at hag'; cases hag'
  have huin : u_main ∈ ag.inputs := by
    obtain ⟨_, p', g', hg', hap'', h⟩ := hlnu.1
    have : p' = ap := by omega
    subst p'; rw [hag] at hg'; cases hg'; exact h
  have hrin : r_main ∈ ag.inputs := by
    obtain ⟨_, p', g', hg', hap'', h⟩ := hlnr.1
    have : p' = ap := by omega
    subst p'; rw [hag] at hg'; cases hg'; exact h
  rw [← ha_eq_out, hap, val_and x hag hop]
  intro i hi
  rcases hall i hi with rfl | rfl <;> rcases hall u_main huin with h1 | h2 <;> rcases hall r_main hrin with h3 | h4
  all_goals first
    | (subst u_main; exact ⟨by have := hlnu.1.1; omega, hu_eq_d ▸ hdx⟩)
    | (subst r_main; exact ⟨by have := hlnr.1.1; omega, hrx⟩)
    | (exact absurd (h1.trans h3.symm) hru.symm)
    | (exact absurd (h2.trans h4.symm) hru.symm)
    | (subst i; exact ⟨by have := hlnu.1.1; omega, hu_eq_d ▸ hdx⟩)
    | (subst i; exact ⟨by have := hlnr.1.1; omega, hrx⟩)

/-- If every leftover edge outside `R.biUnion (LeafEdges C B)` (where `r ∈ R` reaches `C.output` via `Trace (· ∉ B)`)
    starts at `b c` (with `b c ≤ x_c`), and `w` has a bowtie neighbor `y` distinct from `c`, then `b w = w.val`! -/
theorem branch_eq_input_of_only_leftover {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    (h_input_sep : ∀ w : Fin 5, ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z →
      ∀ w' : Fin 5, Trace C (fun q => q ∉ B) w'.val z → w' = w)
    {w c y : Fin 5} {bw bc : ℕ}
    (hbwB : bw ∈ B) (hwb : Trace C (fun q => q ∉ B) w.val bw)
    (hbw_and : bw ≠ w.val → isAndGate C bw)
    (hbc_le : ∀ x, val C x bc = true → x c = true)
    (hyw : y ≠ w) (hyc : y ≠ c) (hwc : w ≠ c) (hwy : bowtieAdj w y)
    {R : Finset ℕ} (hR_out : ∀ r ∈ R, r ∉ B ∧ Trace C (fun q => q ∉ B) r C.output)
    (hleft : ∀ p ∈ AllBEdges C B, p ∉ R.biUnion (fun r => LeafEdges C B r) → p.1 = bc) :
    bw = w.val := by
  classical
  by_contra hne
  obtain ⟨p, hpAll, _, _, u₁, u₂, _, hln1, hln2, _, _, hcase⟩ :=
    non_input_branch_uses_edge hC hE hT h_input_sep hbwB hwb hne
  have hbl : Live C bw := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hbwB))
  obtain ⟨bp, bg, hbg, hbp, hop⟩ := hbw_and hne
  have hu2in : u₂ ∈ bg.inputs := by
    obtain ⟨_, p', g', hg', hbp', h⟩ := hln2.1
    have : p' = bp := by omega
    subst p'; rw [hbg] at hg'; cases hg'; exact h
  have hbc_false : val C (pairIn w y) bc = false := by
    cases h : val C (pairIn w y) bc
    · rfl
    · have hc := hbc_le (pairIn w y) h
      simp only [pairIn, decide_eq_true_eq] at hc
      rcases hc with rfl | rfl
      · exact absurd rfl hwc
      · exact absurd rfl hyc
  -- Helper: any edge `p` with `p.2 = bw ∨ (p.2 ∉ B ∧ Trace (· ∉ B) p.2 bw)` is outside `R.biUnion (LeafEdges C B)`.
  have not_in_R : ∀ p : ℕ × ℕ, (p.2 = bw ∨ (p.2 ∉ B ∧ Trace C (fun q => q ∉ B) p.2 bw)) →
      p ∉ R.biUnion (fun r => LeafEdges C B r) := by
    intro p hp hpU
    obtain ⟨r, hrR, hpL⟩ := Finset.mem_biUnion.mp hpU
    obtain ⟨_, hpI, _⟩ := (mem_LeafEdges hE).mp hpL
    obtain ⟨_, hp2B, hp2Tr⟩ := (mem_Internal hE).mp hpI
    rcases hp with hpeq | ⟨_, hp2b⟩
    · exact hp2B (hpeq ▸ hbwB)
    · have hp2O : Trace C (fun q => q ∉ B) p.2 C.output := hp2Tr.trans (hR_out r hrR).2
      exact trace_notB_of_B_not_out hT hbwB (trace_notB_det hE hT hp2b hp2O (live_le_output hbl))
  have hu2_false : val C (pairIn w y) u₂ = false := by
    rcases hcase with ⟨hu2_eq, hp2_eq⟩ | ⟨hu2B, _, hnoin⟩
    · have hp1 : p.1 = bc := hleft p hpAll (not_in_R p (Or.inl hp2_eq))
      rw [hu2_eq, hp1]
      exact hbc_false
    · apply internal_false hC hE hT hnoin _ u₂ ((mem_Internal hE).mpr ⟨live_of_lnext hln2, hu2B, ReflTransGen.refl⟩)
      intro z hz
      obtain ⟨p', hp'L, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨_, hp'I, _⟩ := (mem_LeafEdges hE).mp hp'L
      obtain ⟨_, hp'2B, hp'2Tu2⟩ := (mem_Internal hE).mp hp'I
      have hp'1 : p'.1 = bc :=
        hleft p' (leafEdges_subset_allBEdges hE hp'L)
          (not_in_R p' (Or.inr ⟨hp'2B, hp'2Tu2.tail ⟨hu2B, hln2⟩⟩))
      rw [hp'1]; exact hbc_false
  have hbw_false : val C (pairIn w y) bw = false := by
    cases h : val C (pairIn w y) bw
    · rfl
    · have ht := ((val_and (pairIn w y) hbg hop).mp (hbp ▸ h) u₂ hu2in).2
      rw [hu2_false] at ht; cases ht
  have hres := no_bypass_output hC (trace_notB_to_nb hE hT hwb) hbl
    (x := pairIn w y) (y := sing y)
    (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_left hi)
    (fun ht => by rw [hbw_false] at ht; cases ht)
    ((bowtie_pair_iff hE w y).mpr hwy)
  rw [bowtie_sing hE y] at hres; cases hres

/-- Two branch-free chains from distinct inputs `u' ≠ v'` that meet at a live wire `t` must first
    meet at the unique narrow OR gate `d = pu ∨ pv`, with `pu ≤ x_{u'}`, `pv ≤ x_{v'}`, and `AndAnc C d t`. -/
theorem two_chains_meet_at_unique_narrow {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {d : ℕ} (hd_uniq : ∀ z, Live C z → isNarrowOr C z → z = d)
    {u' v' : Fin 5} (huv' : u' ≠ v') {t : ℕ} (htl : Live C t)
    (hu : Trace C (fun z => ¬ Branch C z) u'.val t)
    (hv : Trace C (fun z => ¬ Branch C z) v'.val t) :
    ∃ pu pv, pu ≠ pv ∧ LNext C pu d ∧ LNext C pv d ∧
      Trace C (fun z => ¬ Branch C z) u'.val pu ∧
      Trace C (fun z => ¬ Branch C z) v'.val pv ∧
      Trace C (fun z => ¬ Branch C z) u'.val d ∧
      Trace C (fun z => ¬ Branch C z) v'.val d ∧
      Trace C (fun z => ¬ Branch C z) d t ∧
      (∀ x, val C x d = (val C x pu || val C x pv)) ∧
      (∀ x, val C x pu = true → x u' = true) ∧
      (∀ x, val C x pv = true → x v' = true) ∧
      AndAnc C d t := by
  classical
  -- Find the minimum common wire `m` on both chains (`m ∈ Finset.range (t + 1)`).
  let Common : Finset ℕ := (Finset.range (t + 1)).filter
    (fun w => Trace C (fun z => ¬ Branch C z) u'.val w ∧ Trace C (fun z => ¬ Branch C z) v'.val w)
  have ht_mem : t ∈ Common := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self t), hu, hv⟩
  obtain ⟨m, hm_mem, hm_min⟩ := Finset.exists_min_image Common id ⟨t, ht_mem⟩
  obtain ⟨hm_rng, hmu, hmv⟩ := Finset.mem_filter.mp hm_mem
  have hm_le : m ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm_rng)
  have hml : Live C m := trace_nb_live hmu (input_live hE u')
  have hmt : Trace C (fun z => ¬ Branch C z) m t := trace_nb_det hmu hu hm_le
  -- Since `u' ≠ v'`, `m ≠ u'.val` and `m ≠ v'.val`, so both chains take a last step into `m`!
  rcases hmu.cases_tail with hmu_eq | ⟨pu, hTpu, hpu_nb, hlnpu⟩
  · exfalso
    have hm5 : m < 5 := by rw [hmu_eq]; exact u'.isLt
    rcases hmv.cases_tail with hmv_eq | ⟨_, _, _, hln⟩
    · exact huv' (Fin.ext (hmu_eq.symm.trans hmv_eq))
    · obtain ⟨_, _, _, _, hmp, _⟩ := hln.1; omega
  rcases hmv.cases_tail with hmv_eq | ⟨pv, hTpv, hpv_nb, hlnpv⟩
  · exfalso
    obtain ⟨_, _, _, _, hmp, _⟩ := hlnpu.1; have := v'.isLt; omega
  have hpuv : pu ≠ pv := by
    intro heq; subst heq
    have hpu_mem : pu ∈ Common :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hlnpu.1.1; omega), hTpu, hTpv⟩
    have hle_m : m ≤ pu := hm_min pu hpu_mem
    have := hlnpu.1.1; omega
  have hno_common : ∀ w, Trace C (fun z => ¬ Branch C z) u'.val w → w ≤ pu →
      Trace C (fun z => ¬ Branch C z) v'.val w → w ≤ pv → False := by
    intro w hwu hwpu hwv _
    have hw_mem : w ∈ Common :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hlnpu.1.1; omega), hwu, hwv⟩
    have hle_m : m ≤ w := hm_min w hw_mem
    have := hlnpu.1.1; omega
  -- Inspect gate `m`: it has two distinct inputs `pu ≠ pv`, so `g.inputs = {pu, pv}`!
  obtain ⟨_, mp, mg, hmg, hmp, hpuin⟩ := hlnpu.1
  have hpvin : pv ∈ mg.inputs := by
    obtain ⟨_, mp', mg', hmg', hmp', hpvin⟩ := hlnpv.1
    have : mp' = mp := by omega
    subst mp'; rw [hmg] at hmg'; cases hmg'; exact hpvin
  have hmlen : mg.inputs.length ≤ 2 := (hC mg (List.mem_of_getElem? hmg)).2
  have hall_in : ∀ i ∈ mg.inputs, i = pu ∨ i = pv := by
    rcases hgi : mg.inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · simp [hgi] at hpuin
    · simp [hgi] at hpuin hpvin; exact absurd (hpuin.trans hpvin.symm) hpuv
    · simp only [hgi, List.mem_cons, List.not_mem_nil, or_false] at hpuin hpvin ⊢
      intro i hi
      rcases hpuin with rfl | rfl <;> rcases hpvin with rfl | rfl <;>
        rcases hi with rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hpuv
    · simp [hgi] at hmlen
  -- Prove `m` is NOT an AND gate (else BOTH `u' → pu` and `v' → pv` contain a narrow OR gate, contradicting uniqueness of `d`!)
  have hm_or : mg.op = GateOp.or := by
    rcases mono_op hC hmg with hop | hop
    · exfalso
      -- Must have a narrow OR gate on `u' → ... → pu`!
      have hdu_ex : ∃ w, Trace C (fun z => ¬ Branch C z) u'.val w ∧ w ≤ pu ∧ isNarrowOr C w := by
        by_contra hno; push Not at hno
        have hpu_le := and_chain_le_input hC hE hTpu (live_of_lnext hlnpu) hno
        obtain ⟨y, hyu', hv'y⟩ := bowtie_other_nbr v' u' huv'.symm
        have hm_false : val C (pairIn v' y) m = false := by
          cases h : val C (pairIn v' y) m
          · rfl
          · have hput := ((val_and (pairIn v' y) hmg hop).mp (hmp ▸ h) pu hpuin).2
            have hu't := hpu_le (pairIn v' y) hput
            simp only [pairIn, decide_eq_true_eq] at hu't
            rcases hu't with rfl | rfl
            · exact absurd rfl huv'
            · exact absurd rfl hyu'
        have hres := no_bypass_output hC hmv hml
          (x := pairIn v' y) (y := sing y)
          (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_left hi)
          (fun ht => by rw [hm_false] at ht; cases ht)
          ((bowtie_pair_iff hE v' y).mpr hv'y)
        rw [bowtie_sing hE y] at hres; cases hres
      -- Must ALSO have a narrow OR gate on `v' → ... → pv`!
      have hdv_ex : ∃ w, Trace C (fun z => ¬ Branch C z) v'.val w ∧ w ≤ pv ∧ isNarrowOr C w := by
        by_contra hno; push Not at hno
        have hpv_le := and_chain_le_input hC hE hTpv (live_of_lnext hlnpv) hno
        obtain ⟨y, hyv', hu'y⟩ := bowtie_other_nbr u' v' huv'
        have hm_false : val C (pairIn u' y) m = false := by
          cases h : val C (pairIn u' y) m
          · rfl
          · have hpvt := ((val_and (pairIn u' y) hmg hop).mp (hmp ▸ h) pv hpvin).2
            have hv't := hpv_le (pairIn u' y) hpvt
            simp only [pairIn, decide_eq_true_eq] at hv't
            rcases hv't with rfl | rfl
            · exact absurd rfl huv'
            · exact absurd rfl hyv'
        have hres := no_bypass_output hC hmu hml
          (x := pairIn u' y) (y := sing y)
          (fun i hi hxi => by simp only [pairIn, sing, decide_eq_true_eq] at hxi ⊢; exact hxi.resolve_left hi)
          (fun ht => by rw [hm_false] at ht; cases ht)
          ((bowtie_pair_iff hE u' y).mpr hu'y)
        rw [bowtie_sing hE y] at hres; cases hres
      obtain ⟨w₁, hw1u, hw1le, hw1nw⟩ := hdu_ex
      obtain ⟨w₂, hw2v, hw2le, hw2nw⟩ := hdv_ex
      have h1d : w₁ = d := hd_uniq w₁ (trace_nb_live hw1u (input_live hE u')) hw1nw
      have h2d : w₂ = d := hd_uniq w₂ (trace_nb_live hw2v (input_live hE v')) hw2nw
      rw [h1d] at hw1u hw1le
      rw [h2d] at hw2v hw2le
      exact hno_common d hw1u hw1le hw2v hw2le
    · exact hop
  -- Thus `m` is a live narrow OR gate, so `m = d`!
  have hmd : m = d := hd_uniq m hml ⟨⟨mp, mg, hmg, hmp, hm_or⟩, chain_not_wide hC hE hmu hml⟩
  subst hmd
  -- Evaluate `m = pu ∨ pv`, and prove `pu ≤ x_{u'}`, `pv ≤ x_{v'}`, `AndAnc C m t`!
  have hm_val : ∀ x, val C x m = (val C x pu || val C x pv) := by
    intro x
    cases hm : val C x m
    · symm; rw [Bool.or_eq_false_iff]
      constructor
      · cases h1 : val C x pu
        · rfl
        · have := (val_or x hmg hm_or).mpr ⟨pu, hpuin, by have := hlnpu.1.1; omega, h1⟩
          rw [← hmp, hm] at this; cases this
      · cases h2 : val C x pv
        · rfl
        · have := (val_or x hmg hm_or).mpr ⟨pv, hpvin, by have := hlnpv.1.1; omega, h2⟩
          rw [← hmp, hm] at this; cases this
    · symm; rw [Bool.or_eq_true]
      obtain ⟨i, hi, _, hix⟩ := (val_or x hmg hm_or).mp (hmp ▸ hm)
      rcases hall_in i hi with rfl | rfl
      · exact Or.inl hix
      · exact Or.inr hix
  have hpu_le : ∀ x, val C x pu = true → x u' = true :=
    and_chain_le_input hC hE hTpu (live_of_lnext hlnpu) (fun w hwu hle hnw => by
      have := hd_uniq w (trace_nb_live hwu (input_live hE u')) hnw
      have := hlnpu.1.1; omega)
  have hpv_le : ∀ x, val C x pv = true → x v' = true :=
    and_chain_le_input hC hE hTpv (live_of_lnext hlnpv) (fun w hwv hle hnw => by
      have := hd_uniq w (trace_nb_live hwv (input_live hE v')) hnw
      have := hlnpv.1.1; omega)
  have hmt_anc : AndAnc C m t := by
    suffices ∀ {y}, Trace C (fun z => ¬ Branch C z) m y →
        (∀ w, Trace C (fun z => ¬ Branch C z) m w → m < w → w ≤ y → isAndGate C w) → AndAnc C m y by
      apply this hmt
      intro w hmw hlt _
      have hwl : Live C w := trace_nb_live hmw hml
      have hw5 : 5 ≤ w := by omega
      have hw_lt := (live_le_output hwl).trans_lt (output_bounds hE).2
      set wp := w - 5
      have hwp : w = 5 + wp := by omega
      obtain ⟨wg, hwg⟩ : ∃ wg, C.gates[wp]? = some wg := ⟨C.gates[wp], List.getElem?_eq_getElem (by omega)⟩
      rcases mono_op hC hwg with hop | hop
      · exact ⟨wp, wg, hwg, hwp, hop⟩
      · exfalso
        have := hd_uniq w hwl ⟨⟨wp, wg, hwg, hwp, hop⟩, chain_not_wide hC hE (hmu.trans hmw) hwl⟩
        omega
    intro y hmy hAll
    induction hmy with
    | refl => exact ReflTransGen.refl
    | @tail a c hma hac ih =>
      exact (ih (fun w hmw hlt hle => hAll w hmw hlt (hle.trans hac.2.1.1.le))).tail
        ⟨hac.2, hAll c (hma.tail hac) (lt_of_le_of_lt (trace_le hma) hac.2.1.1) le_rfl⟩
  exact ⟨pu, pv, hpuv, hlnpu, hlnpv, hTpu, hTpv, hmu, hmv, hmt, hm_val, hpu_le, hpv_le, hmt_anc⟩

/-- If `r₁ ≠ r₂ ∈ R` have disjoint `LeafEdges` and both contain `z ∈ B` in `Leaves`,
    then EVERY edge `p ∈ AllBEdges C B` with `p.1 = z` lies in `R.biUnion (LeafEdges C B)`. -/
theorem fiber_covered_of_two_leaves {C : Circuit} (hE : BowtieEval C) {B : Finset ℕ} (hT : TightCut C B)
    {R : Finset ℕ} {r₁ r₂ z : ℕ} (hr1 : r₁ ∈ R) (hr2 : r₂ ∈ R) (_h12 : r₁ ≠ r₂)
    (hdisj : Disjoint (LeafEdges C B r₁) (LeafEdges C B r₂))
    (hzB : z ∈ B) (hz1 : z ∈ Leaves C B r₁) (hz2 : z ∈ Leaves C B r₂) :
    ∀ p ∈ AllBEdges C B, p.1 = z → p ∈ R.biUnion (fun r => LeafEdges C B r) := by
  classical
  set F1 := fiber (LeafEdges C B r₁) z
  set F2 := fiber (LeafEdges C B r₂) z
  have hF12 : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    exact Finset.disjoint_left.mp hdisj (mem_fiber.mp h1).1 (mem_fiber.mp h2).1
  have hc1 : 1 ≤ F1.card := Nat.succ_le_iff.mpr (Finset.card_pos.mpr (by
    obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp hz1; exact ⟨p, mem_fiber.mpr ⟨hp, hp1⟩⟩))
  have hc2 : 1 ≤ F2.card := Nat.succ_le_iff.mpr (Finset.card_pos.mpr (by
    obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp hz2; exact ⟨p, mem_fiber.mpr ⟨hp, hp1⟩⟩))
  have hsub : F1 ∪ F2 ⊆ fiber (AllBEdges C B) z := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h2
    · exact mem_fiber.mpr ⟨leafEdges_subset_allBEdges hE (mem_fiber.mp h1).1, (mem_fiber.mp h1).2⟩
    · exact mem_fiber.mpr ⟨leafEdges_subset_allBEdges hE (mem_fiber.mp h2).1, (mem_fiber.mp h2).2⟩
  have heq : F1 ∪ F2 = fiber (AllBEdges C B) z :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [allBEdges_fiber_card hE hT hzB, Finset.card_union_of_disjoint hF12]; omega)
  intro p hp hp1
  have hpU : p ∈ F1 ∪ F2 := heq.symm ▸ mem_fiber.mpr ⟨hp, hp1⟩
  rcases Finset.mem_union.mp hpU with h1 | h2
  · exact Finset.mem_biUnion.mpr ⟨r₁, hr1, (mem_fiber.mp h1).1⟩
  · exact Finset.mem_biUnion.mpr ⟨r₂, hr2, (mem_fiber.mp h2).1⟩

/-- Subcase 3C-i: `|D_L| = 1`, `TightCut C B` on 4 branches for `{1, 2, 3, 4}`, and `v₀ = 0` has a
    branch-free chain to `C.output`. Impossible! -/
theorem single_inelig_v0_zero {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {d : ℕ} (hd_uniq : ∀ z, Live C z → isNarrowOr C z → z = d)
    {b : Fin 5 → ℕ}
    (hb_inj : ∀ u v : Fin 5, u ≠ 0 → v ≠ 0 → b u = b v → u = v)
    (hB_eq : B = (Finset.univ.erase (0 : Fin 5)).image b)
    (hb_tr : ∀ w : Fin 5, w ≠ 0 → Trace C (fun z => z ∉ B) w.val (b w))
    (hv0_chain : Trace C (fun z => z ∉ B) (0 : Fin 5).val C.output) : False := by
  classical
  have hBcard : B.card = 4 := by
    rw [hB_eq, Finset.card_image_of_injOn (fun u hu v hv huv =>
      hb_inj u v (Finset.mem_erase.mp (Finset.mem_coe.mp hu)).1 (Finset.mem_erase.mp (Finset.mem_coe.mp hv)).1 huv)]
    simp
  have hAllCard : (AllBEdges C B).card = 8 := by rw [allBEdges_card hE hT, hBcard]
  obtain ⟨p, q, hqp, hlnp, hlnq, hTp, hpB, hdB, hdl, _hd_or, hd_val, hp_le, hq_nr, hq_sing, hd_anc, hd_out⟩ :=
    unique_narrow_on_chain hC hE hT hd_uniq hv0_chain
  have hTd : Trace C (fun z => z ∉ B) (0 : Fin 5).val d := hTp.tail ⟨hpB, hlnp⟩
  have hb_mem : ∀ w : Fin 5, w ≠ 0 → b w ∈ B := fun w hw => by
    rw [hB_eq]; exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩, rfl⟩
  have hb_le : ∀ w : Fin 5, w ≠ 0 → ∀ x, val C x (b w) = true → x w = true := fun w hw =>
    (other_branch_le_input hC hE hT hd_uniq hd_out (hb_mem w hw) (hb_tr w hw)).1
  have hb_not_wide : ∀ z ∈ B, ¬ isWide C z := by
    intro z hz ⟨u₁, u₂, h12, hzu1, hzu2⟩
    rw [hB_eq] at hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hw0 := (Finset.mem_erase.mp hw).1
    have h1 : w = u₁ := by have := hb_le w hw0 (sing u₁) hzu1; simp [sing] at this; exact this
    have h2 : w = u₂ := by have := hb_le w hw0 (sing u₂) hzu2; simp [sing] at this; exact this
    exact h12 (h1.symm.trans h2)
  have h_input_sep : ∀ w : Fin 5, ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z →
      ∀ w' : Fin 5, Trace C (fun q => q ∉ B) w'.val z → w' = w := by
    have hneq0 : ∀ z ∈ B, ¬ Trace C (fun q => q ∉ B) (0 : Fin 5).val z := by
      intro z hz h0z
      have hzl : Live C z := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hz))
      exact trace_notB_of_B_not_out hT hz (trace_notB_det hE hT h0z hv0_chain (live_le_output hzl))
    have huniq_b : ∀ w : Fin 5, w ≠ 0 → ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z → z = b w := by
      intro w hw z hz hwz
      have hwb := hb_tr w hw
      rcases le_total z (b w) with hle | hle
      · rcases (trace_notB_det hE hT hwz hwb hle).cases_head with rfl | ⟨_, step, _⟩
        · rfl
        · exact absurd hz step.1
      · rcases (trace_notB_det hE hT hwb hwz hle).cases_head with rfl | ⟨_, step, _⟩
        · rfl
        · exact absurd (hb_mem w hw) step.1
    intro w z hz hwz w' hw'z
    have hw0 : w ≠ 0 := fun h => hneq0 z hz (h ▸ hwz)
    have hw'0 : w' ≠ 0 := fun h => hneq0 z hz (h ▸ hw'z)
    exact hb_inj w' w hw'0 hw0 ((huniq_b w' hw'0 z hz hw'z).symm.trans (huniq_b w hw0 z hz hwz))
  -- Helper: `q` is true on `{1, 2}` and `{3, 4}`!
  have hq_edge : ∀ x y : Fin 5, x ≠ 0 → y ≠ 0 → bowtieAdj x y → val C (pairIn x y) q = true := by
    intro x y hx0 hy0 hxy
    have hdt : val C (pairIn x y) d = true := andAnc_val_le hd_anc (pairIn x y) ((bowtie_pair_iff hE x y).mpr hxy)
    have hpf : val C (pairIn x y) p = false := by
      cases h : val C (pairIn x y) p
      · rfl
      · have h0 := hp_le (pairIn x y) h
        simp only [pairIn, decide_eq_true_eq] at h0
        rcases h0 with h1 | h2
        · exact absurd h1.symm hx0
        · exact absurd h2.symm hy0
    rw [hd_val, hpf, Bool.false_or] at hdt
    exact hdt
  -- Show `∀ z, AndAnc C z q → z ∉ B`!
  have hq_noB : ∀ z, AndAnc C z q → z ∉ B := by
    intro z hzq hzB
    rw [hB_eq] at hzB
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
    have hw0 := (Finset.mem_erase.mp hw).1
    have kill_pair : ∀ x y : Fin 5, x ≠ 0 → y ≠ 0 → x ≠ w → y ≠ w → bowtieAdj x y → False := by
      intro x y hx0 hy0 hxw hyw hxy
      have hzt := andAnc_val_le hzq (pairIn x y) (hq_edge x y hx0 hy0 hxy)
      have hwt := hb_le w hw0 (pairIn x y) hzt
      simp only [pairIn, decide_eq_true_eq] at hwt
      rcases hwt with rfl | rfl
      · exact hxw rfl
      · exact hyw rfl
    fin_cases w
    · exact hw0 rfl
    · exact kill_pair 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact kill_pair 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact kill_pair 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact kill_pair 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hqB : q ∉ B := hq_noB q ReflTransGen.refl
  obtain ⟨H, hH_mem, hH_ge, hH_eval, hH_incomp⟩ :=
    and_tree_decomp hC hE hT q (live_of_lnext hlnq) hq_noB
  have hH_to_q : ∀ h ∈ H, Trace C (fun z => z ∉ B) h q := fun h hh =>
    andAnc_to_trace_notB (hH_mem h hh).2.2.2 hq_noB
  have hH_to_d : ∀ h ∈ H, h ∉ B ∧ Trace C (fun z => z ∉ B) h d := fun h hh =>
    ⟨(hH_mem h hh).2.2.1, (hH_to_q h hh).tail ⟨hqB, hlnq⟩⟩
  have hH_noin : ∀ h ∈ H, ∀ u ∈ Internal C B h, 5 ≤ u := by
    intro h hh u hu
    obtain ⟨_, _, huTh⟩ := (mem_Internal hE).mp hu
    by_contra hlt; push Not at hlt
    let w : Fin 5 := ⟨u, hlt⟩
    by_cases hw0 : w = 0
    · have h0q : Trace C (fun z => z ∉ B) (0 : Fin 5).val q := by
        have := huTh.trans (hH_to_q h hh); rwa [← hw0]
      have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
        intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
      exact hq_nr (hstep h0q)
    · have hwO : Trace C (fun z => z ∉ B) w.val C.output :=
        (huTh.trans (hH_to_d h hh).2).trans hd_out
      have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 (hb_mem w hw0)))
      exact trace_notB_of_B_not_out hT (hb_mem w hw0) (trace_notB_det hE hT (hb_tr w hw0) hwO (live_le_output hbwl))
  have hH_card_ge2 : 2 ≤ H.card := by
    by_contra hlt; push Not at hlt
    interval_cases hc : H.card
    · have hHe : H = ∅ := Finset.card_eq_zero.mp hc
      have hq0 : val C zeroIn q = true := hH_eval zeroIn (fun h hh => by rw [hHe] at hh; simp at hh)
      have hq1 : val C (sing 0) q = true := val_mono hC (x := zeroIn) (y := sing 0) (fun _ hi => by simp [zeroIn] at hi) q hq0
      rw [hq_sing 0] at hq1; cases hq1
    · obtain ⟨h, hHs⟩ := Finset.card_eq_one.mp hc
      have hh : h ∈ H := by rw [hHs]; simp
      have hh5 : 5 ≤ h := hH_noin h hh h ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
      have hlt_o := (live_le_output (hH_mem h hh).1).trans_lt (output_bounds hE).2
      set hp := h - 5
      have hhp : h = 5 + hp := by omega
      obtain ⟨hg, hhg⟩ : ∃ hg, C.gates[hp]? = some hg := ⟨C.gates[hp], List.getElem?_eq_getElem (by omega)⟩
      have hor : hg.op = GateOp.or := (mono_op hC hhg).resolve_left (fun hop => (hH_mem h hh).2.1 ⟨hp, hg, hhg, hhp, hop⟩)
      have hnw : isNarrowOr C h := ⟨⟨hp, hg, hhg, hhp, hor⟩, fun ⟨u₁, _, _, h1, _⟩ => by
        have hqu1 : val C (sing u₁) q = true := hH_eval (sing u₁) (fun h' hh' => by rw [hHs, Finset.mem_singleton] at hh'; subst h'; exact h1)
        rw [hq_sing u₁] at hqu1; cases hqu1⟩
      have hhd : h = d := hd_uniq h (hH_mem h hh).1 hnw
      have := andAnc_le (hH_mem h hh).2.2.2
      have := hlnq.1.1
      omega
  -- Every `h ∈ H` hits `{b 1, b 2}` and `{b 3, b 4}` (hence `2 ≤ (LeafEdges C B h).card`)!
  have hH_hits : ∀ h ∈ H, (b 1 ∈ Leaves C B h ∨ b 2 ∈ Leaves C B h) ∧
      (b 3 ∈ Leaves C B h ∨ b 4 ∈ Leaves C B h) ∧ 2 ≤ (LeafEdges C B h).card := by
    intro h hh
    have hit_pair : ∀ x y : Fin 5, x ≠ 0 → y ≠ 0 → bowtieAdj x y →
        b x ∈ Leaves C B h ∨ b y ∈ Leaves C B h := by
      intro x y hx0 hy0 hxy
      by_contra hno; push Not at hno
      have hhf : val C (pairIn x y) h = false := by
        apply internal_false hC hE hT (hH_noin h hh) _ h
          ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
        intro z hz
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hw0 := (Finset.mem_erase.mp hw).1
        cases hv : val C (pairIn x y) (b w)
        · rfl
        · have hwt := hb_le w hw0 (pairIn x y) hv
          simp only [pairIn, decide_eq_true_eq] at hwt
          rcases hwt with rfl | rfl
          · exact absurd hz hno.1
          · exact absurd hz hno.2
      have hht := hH_ge h hh (pairIn x y) (hq_edge x y hx0 hy0 hxy)
      rw [hhf] at hht; cases hht
    have h12 := hit_pair 1 2 (by decide) (by decide) (by decide)
    have h34 := hit_pair 3 4 (by decide) (by decide) (by decide)
    have hcard : 2 ≤ (LeafEdges C B h).card := by
      have hsub : ∃ x y, x ≠ y ∧ x ∈ Leaves C B h ∧ y ∈ Leaves C B h := by
        rcases h12 with h1 | h2 <;> rcases h34 with h3 | h4
        · exact ⟨b 1, b 3, fun heq => absurd (hb_inj 1 3 (by decide) (by decide) heq) (by decide), h1, h3⟩
        · exact ⟨b 1, b 4, fun heq => absurd (hb_inj 1 4 (by decide) (by decide) heq) (by decide), h1, h4⟩
        · exact ⟨b 2, b 3, fun heq => absurd (hb_inj 2 3 (by decide) (by decide) heq) (by decide), h2, h3⟩
        · exact ⟨b 2, b 4, fun heq => absurd (hb_inj 2 4 (by decide) (by decide) heq) (by decide), h2, h4⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := hsub
      calc 2 = ({x, y} : Finset ℕ).card := (Finset.card_pair hxy).symm
        _ ≤ (Leaves C B h).card := Finset.card_le_card (by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
        _ ≤ (LeafEdges C B h).card := Finset.card_image_le
    exact ⟨h12, h34, hcard⟩
  -- Shared finisher for any partner wire `e_w` hitting all 4 of `{b 1, b 2, b 3, b 4}` and incomparable to `H`!
  have finish_with_partner : ∀ (e_w : ℕ), Live C e_w → e_w ∉ B →
      Trace C (fun z => z ∉ B) e_w C.output →
      (∀ u ∈ Internal C B e_w, 5 ≤ u) →
      (∀ w : Fin 5, w ≠ 0 → val C (sing w) e_w = true) →
      (∀ h ∈ H, ¬ Trace C (fun z => z ∉ B) e_w h ∧ ¬ Trace C (fun z => z ∉ B) h e_w) →
      (AllBEdges C B ⊆ LeafEdges C B e_w ∪ H.biUnion (fun h => LeafEdges C B h) →
        ∀ x, val C x d = true → val C x e_w = true → val C x C.output = true) → False := by
    intro e_w hewl hewB hewO hew_noin hew_sing hew_incomp h_and_out
    have hew_leaves : ∀ w : Fin 5, w ≠ 0 → b w ∈ Leaves C B e_w := by
      intro w hw0
      by_contra hno
      have hwf : val C (sing w) e_w = false := by
        apply internal_false hC hE hT hew_noin _ e_w ((mem_Internal hE).mpr ⟨hewl, hewB, ReflTransGen.refl⟩)
        intro z hz
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB
        obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hzB
        have hw'0 := (Finset.mem_erase.mp hw').1
        cases hv : val C (sing w) (b w')
        · rfl
        · have hweq : w' = w := by have := hb_le w' hw'0 (sing w) hv; simp [sing] at this; exact this
          exact absurd (hweq ▸ hz) hno
      rw [hew_sing w hw0] at hwf; cases hwf
    have hew_card : 4 ≤ (LeafEdges C B e_w).card := by
      have hsub : B ⊆ Leaves C B e_w := by
        intro z hz; rw [hB_eq] at hz; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact hew_leaves w (Finset.mem_erase.mp hw).1
      calc 4 = B.card := hBcard.symm
        _ ≤ (Leaves C B e_w).card := Finset.card_le_card hsub
        _ ≤ (LeafEdges C B e_w).card := Finset.card_image_le
    have hew_notH : e_w ∉ H := fun h => (hew_incomp e_w h).1 ReflTransGen.refl
    set R := insert e_w H
    have hR_disj : (R : Set ℕ).PairwiseDisjoint (fun r => LeafEdges C B r) := by
      intro r₁ h1 r₂ h2 hne
      have hr1 := Finset.mem_insert.mp (Finset.mem_coe.mp h1)
      have hr2 := Finset.mem_insert.mp (Finset.mem_coe.mp h2)
      rcases hr1 with rfl | h1H <;> rcases hr2 with rfl | h2H
      · exact absurd rfl hne
      · exact leafEdges_disjoint hE hT (hew_incomp r₂ h2H).1 (hew_incomp r₂ h2H).2
      · exact leafEdges_disjoint hE hT (hew_incomp r₁ h1H).2 (hew_incomp r₁ h1H).1
      · exact leafEdges_disjoint hE hT (hH_incomp r₁ h1H r₂ h2H hne) (hH_incomp r₂ h2H r₁ h1H hne.symm)
    have hR_sub : R.biUnion (fun r => LeafEdges C B r) ⊆ AllBEdges C B := by
      intro pr hpr; obtain ⟨r, _, hprL⟩ := Finset.mem_biUnion.mp hpr; exact leafEdges_subset_allBEdges hE hprL
    have hR_card : (R.biUnion (fun r => LeafEdges C B r)).card =
        (LeafEdges C B e_w).card + ∑ h ∈ H, (LeafEdges C B h).card := by
      rw [Finset.card_biUnion hR_disj, Finset.sum_insert hew_notH]
    have hH_sum : 2 * H.card ≤ ∑ h ∈ H, (LeafEdges C B h).card := by
      calc 2 * H.card = ∑ _h ∈ H, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ h ∈ H, (LeafEdges C B h).card := Finset.sum_le_sum fun h hh => (hH_hits h hh).2.2
    have hU_le : (R.biUnion (fun r => LeafEdges C B r)).card ≤ 8 :=
      hAllCard ▸ Finset.card_le_card hR_sub
    have hH2 : H.card = 2 := by omega
    have hU_eq : R.biUnion (fun r => LeafEdges C B r) = AllBEdges C B :=
      Finset.eq_of_subset_of_card_le hR_sub (by omega)
    have hAll_sub : AllBEdges C B ⊆ LeafEdges C B e_w ∪ H.biUnion (fun h => LeafEdges C B h) := by
      rw [← hU_eq, Finset.biUnion_insert]
    have h_out := h_and_out hAll_sub
    have hbv_eq : ∀ w : Fin 5, w ≠ 0 → b w = w.val := by
      intro w hw0
      by_contra hne
      obtain ⟨pr, hprAll, _, hprNotL, _⟩ := non_input_branch_uses_edge hC hE hT h_input_sep (hb_mem w hw0) (hb_tr w hw0) hne
      rw [← hU_eq] at hprAll
      obtain ⟨r, hrR, hprL⟩ := Finset.mem_biUnion.mp hprAll
      rcases Finset.mem_insert.mp hrR with rfl | hrH
      · exact hprNotL r hewB hewO hprL
      · exact hprNotL r (hH_mem r hrH).2.2.1 ((hH_to_d r hrH).2.trans hd_out) hprL
    obtain ⟨h₁, h₂, h12, hHpair⟩ := Finset.card_eq_two.mp hH2
    have hh1 : h₁ ∈ H := by rw [hHpair]; simp
    have hh2 : h₂ ∈ H := by rw [hHpair]; simp
    -- Since `b w ∈ Leaves e_w` for all `w ≠ 0`, `h₁` and `h₂` CANNOT both contain `b w`!
    have hdisj12 : ∀ w : Fin 5, w ≠ 0 → ¬ (b w ∈ Leaves C B h₁ ∧ b w ∈ Leaves C B h₂) := by
      intro w hw0 ⟨hm1, hm2⟩
      have hsub3 : ({e_w, h₁, h₂} : Finset ℕ) ⊆ R.filter (fun r => b w ∈ Leaves C B r) := by
        intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        simp only [Finset.mem_filter]
        rcases hr with rfl | rfl | rfl
        · exact ⟨Finset.mem_insert_self _ _, hew_leaves w hw0⟩
        · exact ⟨Finset.mem_insert_of_mem hh1, hm1⟩
        · exact ⟨Finset.mem_insert_of_mem hh2, hm2⟩
      have hne1 : e_w ≠ h₁ := fun h => hew_notH (h ▸ hh1)
      have hne2 : e_w ≠ h₂ := fun h => hew_notH (h ▸ hh2)
      have hc3 : ({e_w, h₁, h₂} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]), Finset.card_pair h12]
      have hle2 := freq_le_two hE hT hR_disj (hb_mem w hw0)
      have hle3 := Finset.card_le_card hsub3
      omega
    have kill_ac' : ∀ a a' c c' : Fin 5, a ≠ 0 → a' ≠ 0 → c ≠ 0 → c' ≠ 0 →
        bowtieAdj a a' → bowtieAdj c c' → ¬ bowtieAdj a c' →
        b a' ∉ Leaves C B h₁ → b c ∉ Leaves C B h₂ → False := by
      intro a a' c c' ha0 ha'0 hc0 hc'0 haa' hcc' hnac' ha'1 hc2
      have ht1 : val C (pairIn a c') h₁ = true := by
        apply internal_mono hC hE hT (hH_noin h₁ hh1) _ h₁
          ((mem_Internal hE).mpr ⟨(hH_mem h₁ hh1).1, (hH_mem h₁ hh1).2.2.1, ReflTransGen.refl⟩)
          (hH_ge h₁ hh1 (pairIn a a') (hq_edge a a' ha0 ha'0 haa'))
        intro z hz hzx
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hw0 := (Finset.mem_erase.mp hw).1
        rw [hbv_eq w hw0, val_input] at hzx ⊢
        simp only [pairIn, decide_eq_true_eq] at hzx ⊢
        rcases hzx with rfl | rfl
        · exact Or.inl rfl
        · exact absurd hz ha'1
      have ht2 : val C (pairIn a c') h₂ = true := by
        apply internal_mono hC hE hT (hH_noin h₂ hh2) _ h₂
          ((mem_Internal hE).mpr ⟨(hH_mem h₂ hh2).1, (hH_mem h₂ hh2).2.2.1, ReflTransGen.refl⟩)
          (hH_ge h₂ hh2 (pairIn c c') (hq_edge c c' hc0 hc'0 hcc'))
        intro z hz hzx
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hw0 := (Finset.mem_erase.mp hw).1
        rw [hbv_eq w hw0, val_input] at hzx ⊢
        simp only [pairIn, decide_eq_true_eq] at hzx ⊢
        rcases hzx with rfl | rfl
        · exact absurd hz hc2
        · exact Or.inr rfl
      have hqt : val C (pairIn a c') q = true := hH_eval (pairIn a c') (fun h hh => by
        rw [hHpair, Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with rfl | rfl
        · exact ht1
        · exact ht2)
      have hdt : val C (pairIn a c') d = true := by rw [hd_val, hqt, Bool.or_true]
      have hewt : val C (pairIn a c') e_w = true :=
        val_mono hC (x := sing a) (y := pairIn a c')
          (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) e_w (hew_sing a ha0)
      exact hnac' ((bowtie_pair_iff hE a c').mp (h_out (pairIn a c') hdt hewt))
    rcases (hH_hits h₁ hh1).1 with h1_1 | h2_1 <;> rcases (hH_hits h₂ hh2).2.1 with h3_2 | h4_2
    · have h2_2 := (hH_hits h₂ hh2).1.resolve_left (fun h => hdisj12 1 (by decide) ⟨h1_1, h⟩)
      have h4_1 := (hH_hits h₁ hh1).2.1.resolve_left (fun h => hdisj12 3 (by decide) ⟨h, h3_2⟩)
      exact kill_ac' 1 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun h => hdisj12 2 (by decide) ⟨h, h2_2⟩) (fun h => hdisj12 4 (by decide) ⟨h4_1, h⟩)
    · have h2_2 := (hH_hits h₂ hh2).1.resolve_left (fun h => hdisj12 1 (by decide) ⟨h1_1, h⟩)
      have h3_1 := (hH_hits h₁ hh1).2.1.resolve_right (fun h => hdisj12 4 (by decide) ⟨h, h4_2⟩)
      exact kill_ac' 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun h => hdisj12 2 (by decide) ⟨h, h2_2⟩) (fun h => hdisj12 3 (by decide) ⟨h3_1, h⟩)
    · have h1_2 := (hH_hits h₂ hh2).1.resolve_right (fun h => hdisj12 2 (by decide) ⟨h2_1, h⟩)
      have h4_1 := (hH_hits h₁ hh1).2.1.resolve_left (fun h => hdisj12 3 (by decide) ⟨h, h3_2⟩)
      exact kill_ac' 2 1 4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun h => hdisj12 1 (by decide) ⟨h, h1_2⟩) (fun h => hdisj12 4 (by decide) ⟨h4_1, h⟩)
    · have h1_2 := (hH_hits h₂ hh2).1.resolve_right (fun h => hdisj12 2 (by decide) ⟨h2_1, h⟩)
      have h3_1 := (hH_hits h₁ hh1).2.1.resolve_right (fun h => hdisj12 4 (by decide) ⟨h, h4_2⟩)
      exact kill_ac' 2 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun h => hdisj12 1 (by decide) ⟨h, h1_2⟩) (fun h => hdisj12 3 (by decide) ⟨h3_1, h⟩)
  -- Now split on `val C (sing 0) p`!
  cases hp0 : val C (sing 0) p
  · have hnoD_p : ∀ u, Trace C (fun z => ¬ Branch C z) (0 : Fin 5).val u → u ≤ p → ¬ isNarrowOr C u := by
      intro u hu hle hnw
      have := hd_uniq u (trace_nb_live hu (input_live hE 0)) hnw
      have := hlnp.1.1; omega
    obtain ⟨e_w, a₀, hewl, _, _, _, hew_nbr, hew_wide, hew_nr, hew_to_p⟩ :=
      partner_before_d hC hE hT hTp (live_of_lnext hlnp) hnoD_p hp0
    have hewB : e_w ∉ B := fun h => hb_not_wide e_w h hew_wide
    have hew_p : Trace C (fun z => z ∉ B) e_w p := hew_to_p hewB
    have hew_d : Trace C (fun z => z ∉ B) e_w d := hew_p.tail ⟨hpB, hlnp⟩
    have hew_noin : ∀ u ∈ Internal C B e_w, 5 ≤ u := by
      intro u hu; obtain ⟨_, _, huTe⟩ := (mem_Internal hE).mp hu
      by_contra hlt; push Not at hlt
      let w : Fin 5 := ⟨u, hlt⟩
      by_cases hw0 : w = 0
      · have h0e : Trace C (fun z => z ∉ B) (0 : Fin 5).val e_w := by rwa [← hw0]
        have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
          intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
        exact hew_nr (hstep h0e)
      · have hwO : Trace C (fun z => z ∉ B) w.val C.output := (huTe.trans hew_d).trans hd_out
        have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 (hb_mem w hw0)))
        exact trace_notB_of_B_not_out hT (hb_mem w hw0) (trace_notB_det hE hT (hb_tr w hw0) hwO (live_le_output hbwl))
    have hew_sing : ∀ w : Fin 5, w ≠ 0 → val C (sing w) e_w = true := fun w hw0 =>
      hew_nbr w (by fin_cases w <;> first | exact absurd rfl hw0 | decide)
    apply finish_with_partner e_w hewl hewB (hew_d.trans hd_out) hew_noin hew_sing
      (fun h hh => incomp_of_distinct_inputs hE hT hqp hpB hqB hlnp hlnq hew_p (hH_to_q h hh))
    intro hAll_sub x hdx _
    have hd_eq_out : d = C.output := by
      apply no_and_after_d_if_le_one_leftover hC hE hT (c := 1) (by decide) hB_eq hb_tr hb_le hTd hd_out hd_anc
        (R := insert e_w H) (fun r hr => by
          rcases Finset.mem_insert.mp hr with rfl | hrH
          · exact ⟨hewB, hew_d⟩
          · exact hH_to_d r hrH)
      intro pr hpr hnot
      exfalso; apply hnot
      rw [Finset.biUnion_insert]
      exact hAll_sub hpr
    exact hd_eq_out ▸ hdx
  · have hd0 : val C (sing 0) d = true := by rw [hd_val, hp0, Bool.true_or]
    have hdt_and : ∀ w, Trace C (fun z => z ∉ B) d w → d < w → w ≤ C.output → isAndGate C w := by
      intro w hdw hlt _
      have hwl : Live C w := trace_notB_live hdw hdl
      have hw5 : 5 ≤ w := by obtain ⟨_, _, _, hdp, _⟩ := _hd_or; omega
      have hlt_o := (live_le_output hwl).trans_lt (output_bounds hE).2
      set wp := w - 5
      have hwp : w = 5 + wp := by omega
      obtain ⟨wg, hwg⟩ : ∃ wg, C.gates[wp]? = some wg := ⟨C.gates[wp], List.getElem?_eq_getElem (by omega)⟩
      rcases mono_op hC hwg with hop | hop
      · exact ⟨wp, wg, hwg, hwp, hop⟩
      · exfalso
        have := hd_uniq w hwl ⟨⟨wp, wg, hwg, hwp, hop⟩, chain_not_wide hC hE (trace_notB_to_nb hE hT (hTd.trans hdw)) hwl⟩
        omega
    obtain ⟨r, u_after, a_after, hrl, hlnu, hlnr, hru, huB, hdu, _ha_anc, _hr_anc, _hrf, hr_nbr, hr_wide, hr_nr, ha_out, hr_to_out⟩ :=
      partner_after_d hC hE hT hTd hd_out hdt_and hd0 (bowtie_sing hE 0)
    have hrB : r ∉ B := fun h => hb_not_wide r h hr_wide
    have hr_noin : ∀ u ∈ Internal C B r, 5 ≤ u := by
      intro u hu; obtain ⟨_, _, huTr⟩ := (mem_Internal hE).mp hu
      by_contra hlt; push Not at hlt
      let w : Fin 5 := ⟨u, hlt⟩
      by_cases hw0 : w = 0
      · have h0r : Trace C (fun z => z ∉ B) (0 : Fin 5).val r := by rwa [← hw0]
        have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
          intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
        exact hr_nr (hstep h0r)
      · have hwO : Trace C (fun z => z ∉ B) w.val C.output := (huTr.trans (hr_to_out hrB))
        have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 (hb_mem w hw0)))
        exact trace_notB_of_B_not_out hT (hb_mem w hw0) (trace_notB_det hE hT (hb_tr w hw0) hwO (live_le_output hbwl))
    have hr_sing : ∀ w : Fin 5, w ≠ 0 → val C (sing w) r = true := fun w hw0 =>
      hr_nbr w (by fin_cases w <;> first | exact absurd rfl hw0 | decide)
    apply finish_with_partner r hrl hrB (hr_to_out hrB) hr_noin hr_sing
      (fun h hh => incomp_of_distinct_inputs hE hT hru hrB huB hlnr hlnu ReflTransGen.refl ((hH_to_d h hh).2.trans hdu))
    intro hAll_sub
    exact only_one_and_after_d_if_all_used hC hE hT hB_eq hb_tr hb_le hTd hd_out hd_anc
      hdu huB hlnu hlnr hru hrB ha_out hH_to_d hAll_sub

/-- Subcase 3C-ii: `|D_L| = 1`, `TightCut C B` on 4 branches for `Finset.univ.erase v₀`,
    and leaf `v₀ ∈ {1, 2, 3, 4}` (with triangle mate `v₁` and opposite triangle `{a, c}`) has
    a branch-free chain to `C.output`. Impossible! -/
theorem single_inelig_v0_leaf {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {B : Finset ℕ} (hT : TightCut C B)
    {d : ℕ} (hd_uniq : ∀ z, Live C z → isNarrowOr C z → z = d)
    {v₀ v₁ a c : Fin 5}
    (hv0_ne0 : v₀ ≠ 0) (hv1_ne0 : v₁ ≠ 0) (ha_ne0 : a ≠ 0) (hc_ne0 : c ≠ 0)
    (hv01 : v₀ ≠ v₁) (hv0a : v₀ ≠ a) (hv0c : v₀ ≠ c)
    (hv1a : v₁ ≠ a) (hv1c : v₁ ≠ c) (hac : a ≠ c)
    (hadj_0v0 : bowtieAdj 0 v₀) (hadj_0v1 : bowtieAdj 0 v₁) (hadj_v0v1 : bowtieAdj v₀ v₁)
    (hadj_0a : bowtieAdj 0 a) (hadj_0c : bowtieAdj 0 c) (hadj_ac : bowtieAdj a c)
    (hnadj_v1a : ¬ bowtieAdj v₁ a) (hnadj_v1c : ¬ bowtieAdj v₁ c)
    {b : Fin 5 → ℕ}
    (hb_inj : ∀ u v : Fin 5, u ≠ v₀ → v ≠ v₀ → b u = b v → u = v)
    (hB_eq : B = (Finset.univ.erase v₀).image b)
    (hb_tr : ∀ w : Fin 5, w ≠ v₀ → Trace C (fun z => z ∉ B) w.val (b w))
    (hv0_chain : Trace C (fun z => z ∉ B) v₀.val C.output) : False := by
  classical
  have hfive : ∀ w : Fin 5, w = 0 ∨ w = v₀ ∨ w = v₁ ∨ w = a ∨ w = c := by
    have hcard5 : ({0, v₀, v₁, a, c} : Finset (Fin 5)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hv0_ne0.symm, hv1_ne0.symm, ha_ne0.symm, hc_ne0.symm]),
          Finset.card_insert_of_notMem (by simp [hv01, hv0a, hv0c]),
          Finset.card_insert_of_notMem (by simp [hv1a, hv1c]),
          Finset.card_pair hac]
    have huniv : ({0, v₀, v₁, a, c} : Finset (Fin 5)) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hcard5)
    intro w
    have hw : w ∈ ({0, v₀, v₁, a, c} : Finset (Fin 5)) := by rw [huniv]; exact Finset.mem_univ w
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
  have hBcard : B.card = 4 := by
    rw [hB_eq, Finset.card_image_of_injOn (fun u hu v hv huv =>
      hb_inj u v (Finset.mem_erase.mp (Finset.mem_coe.mp hu)).1 (Finset.mem_erase.mp (Finset.mem_coe.mp hv)).1 huv)]
    simp
  have hAllCard : (AllBEdges C B).card = 8 := by rw [allBEdges_card hE hT, hBcard]
  obtain ⟨p, q, hqp, hlnp, hlnq, hTp, hpB, hdB, hdl, _hd_or, hd_val, hp_le, hq_nr, hq_sing, hd_anc, hd_out⟩ :=
    unique_narrow_on_chain hC hE hT hd_uniq hv0_chain
  have hTd : Trace C (fun z => z ∉ B) v₀.val d := hTp.tail ⟨hpB, hlnp⟩
  have hb_mem : ∀ w : Fin 5, w ≠ v₀ → b w ∈ B := fun w hw => by
    rw [hB_eq]; exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩, rfl⟩
  have hb_le : ∀ w : Fin 5, w ≠ v₀ → ∀ x, val C x (b w) = true → x w = true := fun w hw =>
    (other_branch_le_input hC hE hT hd_uniq hd_out (hb_mem w hw) (hb_tr w hw)).1
  have hb_and : ∀ w : Fin 5, w ≠ v₀ → b w ≠ w.val → isAndGate C (b w) := fun w hw =>
    (other_branch_le_input hC hE hT hd_uniq hd_out (hb_mem w hw) (hb_tr w hw)).2
  have hb_not_wide : ∀ z ∈ B, ¬ isWide C z := by
    intro z hz ⟨u₁, u₂, h12, hzu1, hzu2⟩
    rw [hB_eq] at hz; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hwv := (Finset.mem_erase.mp hw).1
    have h1 : w = u₁ := by have := hb_le w hwv (sing u₁) hzu1; simp [sing] at this; exact this
    have h2 : w = u₂ := by have := hb_le w hwv (sing u₂) hzu2; simp [sing] at this; exact this
    exact h12 (h1.symm.trans h2)
  have h_input_sep : ∀ w : Fin 5, ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z →
      ∀ w' : Fin 5, Trace C (fun q => q ∉ B) w'.val z → w' = w := by
    have hneqv : ∀ z ∈ B, ¬ Trace C (fun q => q ∉ B) v₀.val z := by
      intro z hz hvz
      have hzl : Live C z := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hz))
      exact trace_notB_of_B_not_out hT hz (trace_notB_det hE hT hvz hv0_chain (live_le_output hzl))
    have huniq_b : ∀ w : Fin 5, w ≠ v₀ → ∀ z ∈ B, Trace C (fun q => q ∉ B) w.val z → z = b w := by
      intro w hw z hz hwz
      have hwb := hb_tr w hw
      rcases le_total z (b w) with hle | hle
      · rcases (trace_notB_det hE hT hwz hwb hle).cases_head with rfl | ⟨_, step, _⟩
        · rfl
        · exact absurd hz step.1
      · rcases (trace_notB_det hE hT hwb hwz hle).cases_head with rfl | ⟨_, step, _⟩
        · rfl
        · exact absurd (hb_mem w hw) step.1
    intro w z hz hwz w' hw'z
    have hwv : w ≠ v₀ := fun h => hneqv z hz (h ▸ hwz)
    have hw'v : w' ≠ v₀ := fun h => hneqv z hz (h ▸ hw'z)
    exact hb_inj w' w hw'v hwv ((huniq_b w' hw'v z hz hw'z).symm.trans (huniq_b w hwv z hz hwz))
  have hq_edge : ∀ x y : Fin 5, x ≠ v₀ → y ≠ v₀ → bowtieAdj x y → val C (pairIn x y) q = true := by
    intro x y hxv hyv hxy
    have hdt : val C (pairIn x y) d = true := andAnc_val_le hd_anc (pairIn x y) ((bowtie_pair_iff hE x y).mpr hxy)
    have hpf : val C (pairIn x y) p = false := by
      cases h : val C (pairIn x y) p
      · rfl
      · have hv := hp_le (pairIn x y) h
        simp only [pairIn, decide_eq_true_eq] at hv
        rcases hv with h1 | h2
        · exact absurd h1.symm hxv
        · exact absurd h2.symm hyv
    rw [hd_val, hpf, Bool.false_or] at hdt
    exact hdt
  have hq_noB : ∀ z, AndAnc C z q → z ∉ B := by
    intro z hzq hzB
    rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
    have hwv := (Finset.mem_erase.mp hw).1
    have kill_pair : ∀ x y : Fin 5, x ≠ v₀ → y ≠ v₀ → x ≠ w → y ≠ w → bowtieAdj x y → False := by
      intro x y hxv hyv hxw hyw hxy
      have hzt := andAnc_val_le hzq (pairIn x y) (hq_edge x y hxv hyv hxy)
      have hwt := hb_le w hwv (pairIn x y) hzt
      simp only [pairIn, decide_eq_true_eq] at hwt
      rcases hwt with rfl | rfl
      · exact hxw rfl
      · exact hyw rfl
    rcases hfive w with rfl | rfl | rfl | rfl | rfl
    · exact kill_pair a c hv0a.symm hv0c.symm ha_ne0 hc_ne0 hadj_ac
    · exact hwv rfl
    · exact kill_pair a c hv0a.symm hv0c.symm hv1a.symm hv1c.symm hadj_ac
    · exact kill_pair 0 c hv0_ne0.symm hv0c.symm ha_ne0.symm hac.symm hadj_0c
    · exact kill_pair 0 a hv0_ne0.symm hv0a.symm hc_ne0.symm hac hadj_0a
  have hqB : q ∉ B := hq_noB q ReflTransGen.refl
  obtain ⟨H, hH_mem, hH_ge, hH_eval, hH_incomp⟩ :=
    and_tree_decomp hC hE hT q (live_of_lnext hlnq) hq_noB
  have hH_to_q : ∀ h ∈ H, Trace C (fun z => z ∉ B) h q := fun h hh =>
    andAnc_to_trace_notB (hH_mem h hh).2.2.2 hq_noB
  have hH_to_d : ∀ h ∈ H, h ∉ B ∧ Trace C (fun z => z ∉ B) h d := fun h hh =>
    ⟨(hH_mem h hh).2.2.1, (hH_to_q h hh).tail ⟨hqB, hlnq⟩⟩
  have hH_noin : ∀ h ∈ H, ∀ u ∈ Internal C B h, 5 ≤ u := by
    intro h hh u hu; obtain ⟨_, _, huTh⟩ := (mem_Internal hE).mp hu
    by_contra hlt; push Not at hlt
    let w : Fin 5 := ⟨u, hlt⟩
    by_cases hwv : w = v₀
    · have hvq : Trace C (fun z => z ∉ B) v₀.val q := by
        have := huTh.trans (hH_to_q h hh); rwa [← hwv]
      have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
        intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
      exact hq_nr (hstep hvq)
    · have hwO : Trace C (fun z => z ∉ B) w.val C.output := (huTh.trans (hH_to_d h hh).2).trans hd_out
      have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 (hb_mem w hwv)))
      exact trace_notB_of_B_not_out hT (hb_mem w hwv) (trace_notB_det hE hT (hb_tr w hwv) hwO (live_le_output hbwl))
  have hH_card_ge2 : 2 ≤ H.card := by
    by_contra hlt; push Not at hlt
    interval_cases hc : H.card
    · have hHe : H = ∅ := Finset.card_eq_zero.mp hc
      have hq0 : val C zeroIn q = true := hH_eval zeroIn (fun h hh => by rw [hHe] at hh; simp at hh)
      have hq1 : val C (sing 0) q = true := val_mono hC (x := zeroIn) (y := sing 0) (fun _ hi => by simp [zeroIn] at hi) q hq0
      rw [hq_sing 0] at hq1; cases hq1
    · obtain ⟨h, hHs⟩ := Finset.card_eq_one.mp hc
      have hh : h ∈ H := by rw [hHs]; simp
      have hh5 : 5 ≤ h := hH_noin h hh h ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
      have hlt_o := (live_le_output (hH_mem h hh).1).trans_lt (output_bounds hE).2
      set hp := h - 5
      have hhp : h = 5 + hp := by omega
      obtain ⟨hg, hhg⟩ : ∃ hg, C.gates[hp]? = some hg := ⟨C.gates[hp], List.getElem?_eq_getElem (by omega)⟩
      have hor : hg.op = GateOp.or := (mono_op hC hhg).resolve_left (fun hop => (hH_mem h hh).2.1 ⟨hp, hg, hhg, hhp, hop⟩)
      have hnw : isNarrowOr C h := ⟨⟨hp, hg, hhg, hhp, hor⟩, fun ⟨u₁, _, _, h1, _⟩ => by
        have hqu1 : val C (sing u₁) q = true := hH_eval (sing u₁) (fun h' hh' => by rw [hHs, Finset.mem_singleton] at hh'; subst h'; exact h1)
        rw [hq_sing u₁] at hqu1; cases hqu1⟩
      have hhd : h = d := hd_uniq h (hH_mem h hh).1 hnw
      have := andAnc_le (hH_mem h hh).2.2.2; have := hlnq.1.1; omega
  -- Helper: any `r ∉ B` with `∀ u ∈ Internal C B r, 5 ≤ u` and `val (pairIn x y) r = true` (`x, y ≠ v₀`)
  -- must contain `b x ∈ Leaves C B r ∨ b y ∈ Leaves C B r`!
  have leaf_hit_pair : ∀ r, Live C r → r ∉ B → (∀ u ∈ Internal C B r, 5 ≤ u) →
      ∀ x y : Fin 5, x ≠ v₀ → y ≠ v₀ → val C (pairIn x y) r = true →
      b x ∈ Leaves C B r ∨ b y ∈ Leaves C B r := by
    intro r hrl hrB hr_noin x y _ _ hrt
    by_contra hno; push Not at hno
    have hrf : val C (pairIn x y) r = false := by
      apply internal_false hC hE hT hr_noin _ r ((mem_Internal hE).mpr ⟨hrl, hrB, ReflTransGen.refl⟩)
      intro z hz
      have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
      rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
      have hwv := (Finset.mem_erase.mp hw).1
      cases hv : val C (pairIn x y) (b w)
      · rfl
      · have hwt := hb_le w hwv (pairIn x y) hv
        simp only [pairIn, decide_eq_true_eq] at hwt
        rcases hwt with rfl | rfl
        · exact absurd hz hno.1
        · exact absurd hz hno.2
    rw [hrf] at hrt; cases hrt
  have leaf_hit_sing : ∀ r, Live C r → r ∉ B → (∀ u ∈ Internal C B r, 5 ≤ u) →
      ∀ x : Fin 5, x ≠ v₀ → val C (sing x) r = true → b x ∈ Leaves C B r := by
    intro r hrl hrB hr_noin x _ hrt
    by_contra hno
    have hrf : val C (sing x) r = false := by
      apply internal_false hC hE hT hr_noin _ r ((mem_Internal hE).mpr ⟨hrl, hrB, ReflTransGen.refl⟩)
      intro z hz
      have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
      rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
      have hwv := (Finset.mem_erase.mp hw).1
      cases hv : val C (sing x) (b w)
      · rfl
      · have hweq : w = x := by have := hb_le w hwv (sing x) hv; simp [sing] at this; exact this
        exact absurd (hweq ▸ hz) hno
    rw [hrf] at hrt; cases hrt
  -- Paw properties of every `h ∈ H`!
  have hH_paw : ∀ h ∈ H, (b a ∈ Leaves C B h ∨ b c ∈ Leaves C B h) ∧
      (b 0 ∉ Leaves C B h → b v₁ ∈ Leaves C B h ∧ b a ∈ Leaves C B h ∧ b c ∈ Leaves C B h ∧ 3 ≤ (LeafEdges C B h).card) := by
    intro h hh
    have hac_hit := leaf_hit_pair h (hH_mem h hh).1 (hH_mem h hh).2.2.1 (hH_noin h hh)
      a c hv0a.symm hv0c.symm (hH_ge h hh (pairIn a c) (hq_edge a c hv0a.symm hv0c.symm hadj_ac))
    refine ⟨hac_hit, fun h0not => ?_⟩
    have hv1_hit := (leaf_hit_pair h (hH_mem h hh).1 (hH_mem h hh).2.2.1 (hH_noin h hh)
      0 v₁ hv0_ne0.symm hv01.symm (hH_ge h hh (pairIn 0 v₁) (hq_edge 0 v₁ hv0_ne0.symm hv01.symm hadj_0v1))).resolve_left h0not
    have ha_hit := (leaf_hit_pair h (hH_mem h hh).1 (hH_mem h hh).2.2.1 (hH_noin h hh)
      0 a hv0_ne0.symm hv0a.symm (hH_ge h hh (pairIn 0 a) (hq_edge 0 a hv0_ne0.symm hv0a.symm hadj_0a))).resolve_left h0not
    have hc_hit := (leaf_hit_pair h (hH_mem h hh).1 (hH_mem h hh).2.2.1 (hH_noin h hh)
      0 c hv0_ne0.symm hv0c.symm (hH_ge h hh (pairIn 0 c) (hq_edge 0 c hv0_ne0.symm hv0c.symm hadj_0c))).resolve_left h0not
    have hcard3 : 3 ≤ (LeafEdges C B h).card := by
      have hne1 : b v₁ ≠ b a := fun heq => hv1a (hb_inj v₁ a hv01.symm hv0a.symm heq)
      have hne2 : b v₁ ≠ b c := fun heq => hv1c (hb_inj v₁ c hv01.symm hv0c.symm heq)
      have hne3 : b a ≠ b c := fun heq => hac (hb_inj a c hv0a.symm hv0c.symm heq)
      calc 3 = ({b v₁, b a, b c} : Finset ℕ).card := by
            rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]), Finset.card_pair hne3]
        _ ≤ (Leaves C B h).card := Finset.card_le_card (by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption)
        _ ≤ (LeafEdges C B h).card := Finset.card_image_le
    exact ⟨hv1_hit, ha_hit, hc_hit, hcard3⟩
  -- Shared extraction: given ANY partner `e_w` with `b 0, b v₁ ∈ Leaves e_w` and incomparable to `H`,
  -- deduce `H = {h₁, h₂}` with exact leaf profiles!
  have split_H_of_partner : ∀ e_w, b 0 ∈ Leaves C B e_w → b v₁ ∈ Leaves C B e_w →
      (∀ h ∈ H, ¬ Trace C (fun z => z ∉ B) e_w h ∧ ¬ Trace C (fun z => z ∉ B) h e_w) →
      ∃ h₁ h₂, h₁ ≠ h₂ ∧ H = {h₁, h₂} ∧ e_w ∉ H ∧
        ((insert e_w H : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun r => LeafEdges C B r) ∧
        b 0 ∉ Leaves C B h₁ ∧ b v₁ ∈ Leaves C B h₁ ∧ b a ∈ Leaves C B h₁ ∧ b c ∈ Leaves C B h₁ ∧
        3 ≤ (LeafEdges C B h₁).card ∧
        b 0 ∈ Leaves C B h₂ ∧ b v₁ ∉ Leaves C B h₂ ∧ (b a ∈ Leaves C B h₂ ∨ b c ∈ Leaves C B h₂) ∧
        2 ≤ (LeafEdges C B h₂).card := by
    intro e_w hew0 hewv1 hew_incomp
    have hew_notH : e_w ∉ H := fun h => (hew_incomp e_w h).1 ReflTransGen.refl
    set R := insert e_w H
    have hR_disj : (R : Set ℕ).PairwiseDisjoint (fun r => LeafEdges C B r) := by
      intro r₁ h1 r₂ h2 hne
      have hr1 := Finset.mem_insert.mp (Finset.mem_coe.mp h1)
      have hr2 := Finset.mem_insert.mp (Finset.mem_coe.mp h2)
      rcases hr1 with rfl | h1H <;> rcases hr2 with rfl | h2H
      · exact absurd rfl hne
      · exact leafEdges_disjoint hE hT (hew_incomp r₂ h2H).1 (hew_incomp r₂ h2H).2
      · exact leafEdges_disjoint hE hT (hew_incomp r₁ h1H).2 (hew_incomp r₁ h1H).1
      · exact leafEdges_disjoint hE hT (hH_incomp r₁ h1H r₂ h2H hne) (hH_incomp r₂ h2H r₁ h1H hne.symm)
    -- At most 1 element of `H` contains `b 0`, and at most 1 contains `b v₁`!
    have hH0_le1 : (H.filter (fun h => b 0 ∈ Leaves C B h)).card ≤ 1 := by
      have h1 := freq_le_two hE hT hR_disj (hb_mem 0 hv0_ne0.symm)
      have heq : R.filter (fun r => b 0 ∈ Leaves C B r) = insert e_w (H.filter (fun h => b 0 ∈ Leaves C B h)) := by
        ext r; simp only [R, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hrH, hr0⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hrH, hr0⟩
        · rintro (rfl | ⟨hrH, hr0⟩)
          · exact ⟨Or.inl rfl, hew0⟩
          · exact ⟨Or.inr hrH, hr0⟩
      rw [heq, Finset.card_insert_of_notMem (fun h => hew_notH (Finset.mem_filter.mp h).1)] at h1
      omega
    have hHv1_le1 : (H.filter (fun h => b v₁ ∈ Leaves C B h)).card ≤ 1 := by
      have h1 := freq_le_two hE hT hR_disj (hb_mem v₁ hv01.symm)
      have heq : R.filter (fun r => b v₁ ∈ Leaves C B r) = insert e_w (H.filter (fun h => b v₁ ∈ Leaves C B h)) := by
        ext r; simp only [R, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hrH, hr1⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hrH, hr1⟩
        · rintro (rfl | ⟨hrH, hr1⟩)
          · exact ⟨Or.inl rfl, hewv1⟩
          · exact ⟨Or.inr hrH, hr1⟩
      rw [heq, Finset.card_insert_of_notMem (fun h => hew_notH (Finset.mem_filter.mp h).1)] at h1
      omega
    have hHno0_le1 : (H.filter (fun h => b 0 ∉ Leaves C B h)).card ≤ 1 := by
      calc (H.filter (fun h => b 0 ∉ Leaves C B h)).card
          ≤ (H.filter (fun h => b v₁ ∈ Leaves C B h)).card := Finset.card_le_card (fun h hh => by
              obtain ⟨hhH, h0n⟩ := Finset.mem_filter.mp hh
              exact Finset.mem_filter.mpr ⟨hhH, ((hH_paw h hhH).2 h0n).1⟩)
        _ ≤ 1 := hHv1_le1
    have hsum : (H.filter (fun h => b 0 ∈ Leaves C B h)).card + (H.filter (fun h => b 0 ∉ Leaves C B h)).card = H.card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
      congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    have hc_no0 : (H.filter (fun h => b 0 ∉ Leaves C B h)).card = 1 := by omega
    have hc_yes0 : (H.filter (fun h => b 0 ∈ Leaves C B h)).card = 1 := by omega
    obtain ⟨h₁, hh1_s⟩ := Finset.card_eq_one.mp hc_no0
    obtain ⟨h₂, hh2_s⟩ := Finset.card_eq_one.mp hc_yes0
    have hh1_f : h₁ ∈ H.filter (fun h => b 0 ∉ Leaves C B h) := by rw [hh1_s]; simp
    have hh2_f : h₂ ∈ H.filter (fun h => b 0 ∈ Leaves C B h) := by rw [hh2_s]; simp
    obtain ⟨hh1, h1_no0⟩ := Finset.mem_filter.mp hh1_f
    obtain ⟨hh2, h2_yes0⟩ := Finset.mem_filter.mp hh2_f
    have h12 : h₁ ≠ h₂ := fun heq => h1_no0 (heq ▸ h2_yes0)
    have hHpair : H = {h₁, h₂} := by
      ext h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hh
        by_cases h0 : b 0 ∈ Leaves C B h
        · right; have : h ∈ H.filter (fun x => b 0 ∈ Leaves C B x) := Finset.mem_filter.mpr ⟨hh, h0⟩
          rw [hh2_s, Finset.mem_singleton] at this; exact this
        · left; have : h ∈ H.filter (fun x => b 0 ∉ Leaves C B x) := Finset.mem_filter.mpr ⟨hh, h0⟩
          rw [hh1_s, Finset.mem_singleton] at this; exact this
      · rintro (rfl | rfl)
        · exact hh1
        · exact hh2
    obtain ⟨h1_v1, h1_a, h1_c, h1_card3⟩ := (hH_paw h₁ hh1).2 h1_no0
    have h2_nov1 : b v₁ ∉ Leaves C B h₂ := by
      intro h2_v1
      have hsub : ({h₁, h₂} : Finset ℕ) ⊆ H.filter (fun h => b v₁ ∈ Leaves C B h) := by
        intro h hh; simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hh1, h1_v1⟩
        · exact Finset.mem_filter.mpr ⟨hh2, h2_v1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair h12] at this
      omega
    have h2_ac := (hH_paw h₂ hh2).1
    have h2_card2 : 2 ≤ (LeafEdges C B h₂).card := by
      have hne_0a : b 0 ≠ b a := fun heq => ha_ne0.symm (hb_inj 0 a hv0_ne0.symm hv0a.symm heq)
      have hne_0c : b 0 ≠ b c := fun heq => hc_ne0.symm (hb_inj 0 c hv0_ne0.symm hv0c.symm heq)
      rcases h2_ac with h2a | h2c
      · calc 2 = ({b 0, b a} : Finset ℕ).card := (Finset.card_pair hne_0a).symm
          _ ≤ (Leaves C B h₂).card := Finset.card_le_card (by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
          _ ≤ (LeafEdges C B h₂).card := Finset.card_image_le
      · calc 2 = ({b 0, b c} : Finset ℕ).card := (Finset.card_pair hne_0c).symm
          _ ≤ (Leaves C B h₂).card := Finset.card_le_card (by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
          _ ≤ (LeafEdges C B h₂).card := Finset.card_image_le
    exact ⟨h₁, h₂, h12, hHpair, hew_notH, hR_disj, h1_no0, h1_v1, h1_a, h1_c, h1_card3, h2_yes0, h2_nov1, h2_ac, h2_card2⟩
  -- Split on `val C (sing v₀) p`!
  cases hp0 : val C (sing v₀) p
  · -- Case A: `val (sing v₀) p = false`!
    have hnoD_p : ∀ u, Trace C (fun z => ¬ Branch C z) v₀.val u → u ≤ p → ¬ isNarrowOr C u := by
      intro u hu hle hnw
      have := hd_uniq u (trace_nb_live hu (input_live hE v₀)) hnw
      have := hlnp.1.1; omega
    obtain ⟨e_w, a₀, hewl, _, _, _, hew_nbr, hew_wide, hew_nr, hew_to_p⟩ :=
      partner_before_d hC hE hT hTp (live_of_lnext hlnp) hnoD_p hp0
    have hewB : e_w ∉ B := fun h => hb_not_wide e_w h hew_wide
    have hew_p : Trace C (fun z => z ∉ B) e_w p := hew_to_p hewB
    have hew_d : Trace C (fun z => z ∉ B) e_w d := hew_p.tail ⟨hpB, hlnp⟩
    have hew_noin : ∀ u ∈ Internal C B e_w, 5 ≤ u := by
      intro u hu; obtain ⟨_, _, huTe⟩ := (mem_Internal hE).mp hu
      by_contra hlt; push Not at hlt
      let w : Fin 5 := ⟨u, hlt⟩
      by_cases hwv : w = v₀
      · have hve : Trace C (fun z => z ∉ B) v₀.val e_w := by rwa [← hwv]
        have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
          intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
        exact hew_nr (hstep hve)
      · have hwO : Trace C (fun z => z ∉ B) w.val C.output := (huTe.trans hew_d).trans hd_out
        have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 (hb_mem w hwv)))
        exact trace_notB_of_B_not_out hT (hb_mem w hwv) (trace_notB_det hE hT (hb_tr w hwv) hwO (live_le_output hbwl))
    have hew0 : b 0 ∈ Leaves C B e_w :=
      leaf_hit_sing e_w hewl hewB hew_noin 0 hv0_ne0.symm (hew_nbr 0 (bowtieAdj_symm hadj_0v0))
    have hewv1 : b v₁ ∈ Leaves C B e_w :=
      leaf_hit_sing e_w hewl hewB hew_noin v₁ hv01.symm (hew_nbr v₁ hadj_v0v1)
    obtain ⟨h₁, h₂, h12, hHpair, hew_notH, hR_disj, h1_no0, h1_v1, h1_a, h1_c, h1_card3, h2_yes0, h2_nov1, h2_ac, _⟩ :=
      split_H_of_partner e_w hew0 hewv1 (fun h hh => incomp_of_distinct_inputs hE hT hqp hpB hqB hlnp hlnq hew_p (hH_to_q h hh))
    have hh1 : h₁ ∈ H := by rw [hHpair]; simp
    have hh2 : h₂ ∈ H := by rw [hHpair]; simp
    set R := insert e_w H
    have hR_to_d : ∀ r ∈ R, r ∉ B ∧ Trace C (fun z => z ∉ B) r d := by
      intro r hr; rcases Finset.mem_insert.mp hr with rfl | hrH
      · exact ⟨hewB, hew_d⟩
      · exact hH_to_d r hrH
    -- Helper for Subcase A2: when `b y ∉ Leaves h₂` and `b x ∈ Leaves h₂` (with `{x, y} = {a, c}`)!
    have kill_omit : ∀ x y : Fin 5, (x = a ∧ y = c ∨ x = c ∧ y = a) →
        b x ∈ Leaves C B h₂ → b y ∉ Leaves C B h₂ → False := by
      intro x y hxy h2x h2ny
      have hxv0 : x ≠ v₀ := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hv0a.symm; exact hv0c.symm]
      have hyv0 : y ≠ v₀ := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hv0c.symm; exact hv0a.symm]
      have hx0 : x ≠ 0 := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact ha_ne0; exact hc_ne0]
      have hy0 : y ≠ 0 := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hc_ne0; exact ha_ne0]
      have hxy_ne : x ≠ y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hac; exact hac.symm]
      have hv1x_ne : v₁ ≠ x := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hv1a; exact hv1c]
      have hv1y_ne : v₁ ≠ y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hv1c; exact hv1a]
      have hadj_0x : bowtieAdj 0 x := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hadj_0a; exact hadj_0c]
      have hnadj_v1x : ¬ bowtieAdj v₁ x := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hnadj_v1a; exact hnadj_v1c]
      have h1x : b x ∈ Leaves C B h₁ := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h1_a; exact h1_c]
      -- Every leftover edge outside `R.biUnion (LeafEdges C B)` MUST start at `b y`!
      have hleft_y : ∀ pr ∈ AllBEdges C B, pr ∉ R.biUnion (fun r => LeafEdges C B r) → pr.1 = b y := by
        intro pr hpr hnot
        have hprB : pr.1 ∈ B := ((mem_AllBEdges hE).mp hpr).1
        rw [hB_eq] at hprB; obtain ⟨w, hw, hbw⟩ := Finset.mem_image.mp hprB
        have hwv := (Finset.mem_erase.mp hw).1
        have hne_e1 : e_w ≠ h₁ := fun h => hew_notH (h ▸ hh1)
        have hne_e2 : e_w ≠ h₂ := fun h => hew_notH (h ▸ hh2)
        have hcov0 := fiber_covered_of_two_leaves hE hT (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hh2) hne_e2
          (hR_disj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hh2) hne_e2) (hb_mem 0 hv0_ne0.symm) hew0 h2_yes0
        have hcovv1 := fiber_covered_of_two_leaves hE hT (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hh1) hne_e1
          (hR_disj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hh1) hne_e1) (hb_mem v₁ hv01.symm) hewv1 h1_v1
        have hcovx := fiber_covered_of_two_leaves hE hT (R := R) (Finset.mem_insert_of_mem hh1) (Finset.mem_insert_of_mem hh2) h12
          (hR_disj (Finset.mem_insert_of_mem hh1) (Finset.mem_insert_of_mem hh2) h12) (hb_mem x hxv0) h1x h2x
        rcases hfive w with rfl | rfl | rfl | rfl | rfl
        · exact absurd (hcov0 pr hpr hbw.symm) hnot
        · exact absurd rfl hwv
        · exact absurd (hcovv1 pr hpr hbw.symm) hnot
        · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd (hcovx pr hpr hbw.symm) hnot
          · exact hbw.symm
        · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hbw.symm
          · exact absurd (hcovx pr hpr hbw.symm) hnot
      have hd_out_eq : d = C.output :=
        no_and_after_d_if_le_one_leftover hC hE hT hyv0 hB_eq hb_tr hb_le hTd hd_out hd_anc hR_to_d hleft_y
      have hbv1_eq : b v₁ = v₁.val :=
        branch_eq_input_of_only_leftover hC hE hT h_input_sep (hb_mem v₁ hv01.symm) (hb_tr v₁ hv01.symm)
          (hb_and v₁ hv01.symm) (hb_le y hyv0) hv1_ne0.symm hy0.symm hv1y_ne (bowtieAdj_symm hadj_0v1)
          (fun r hr => ⟨(hR_to_d r hr).1, (hR_to_d r hr).2.trans hd_out⟩) hleft_y
      have hbx_eq : b x = x.val :=
        branch_eq_input_of_only_leftover hC hE hT h_input_sep (hb_mem x hxv0) (hb_tr x hxv0)
          (hb_and x hxv0) (hb_le y hyv0) hx0.symm hy0.symm hxy_ne (bowtieAdj_symm hadj_0x)
          (fun r hr => ⟨(hR_to_d r hr).1, (hR_to_d r hr).2.trans hd_out⟩) hleft_y
      -- Now evaluate `h₁` and `h₂` on `pairIn v₁ x`!
      have ht1 : val C (pairIn v₁ x) h₁ = true := by
        apply internal_mono hC hE hT (hH_noin h₁ hh1) _ h₁
          ((mem_Internal hE).mpr ⟨(hH_mem h₁ hh1).1, (hH_mem h₁ hh1).2.2.1, ReflTransGen.refl⟩)
          (hH_ge h₁ hh1 (pairIn 0 v₁) (hq_edge 0 v₁ hv0_ne0.symm hv01.symm hadj_0v1))
        intro z hz hzx
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hwv := (Finset.mem_erase.mp hw).1
        have hwt := hb_le w hwv (pairIn 0 v₁) hzx
        simp only [pairIn, decide_eq_true_eq] at hwt
        rcases hwt with rfl | rfl
        · exact absurd hz h1_no0
        · rw [hbv1_eq, val_input]; simp [pairIn]
      have ht2 : val C (pairIn v₁ x) h₂ = true := by
        have hac_xy : val C (pairIn x y) h₂ = true := by
          have hadj_xy : bowtieAdj x y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hadj_ac; exact bowtieAdj_symm hadj_ac]
          exact hH_ge h₂ hh2 (pairIn x y) (hq_edge x y hxv0 hyv0 hadj_xy)
        apply internal_mono hC hE hT (hH_noin h₂ hh2) _ h₂
          ((mem_Internal hE).mpr ⟨(hH_mem h₂ hh2).1, (hH_mem h₂ hh2).2.2.1, ReflTransGen.refl⟩) hac_xy
        intro z hz hzx
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hwv := (Finset.mem_erase.mp hw).1
        have hwt := hb_le w hwv (pairIn x y) hzx
        simp only [pairIn, decide_eq_true_eq] at hwt
        rcases hwt with rfl | rfl
        · rw [hbx_eq, val_input]; simp [pairIn]
        · exact absurd hz h2ny
      have hqt : val C (pairIn v₁ x) q = true := hH_eval (pairIn v₁ x) (fun h hh => by
        rw [hHpair, Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with rfl | rfl <;> assumption)
      have hdt : val C (pairIn v₁ x) d = true := by rw [hd_val, hqt, Bool.or_true]
      exact hnadj_v1x ((bowtie_pair_iff hE v₁ x).mp (hd_out_eq ▸ hdt))
    by_cases h2a : b a ∈ Leaves C B h₂
    · by_cases h2c : b c ∈ Leaves C B h₂
      · -- Subcase A1: `b a ∈ Leaves h₂ ∧ b c ∈ Leaves h₂`, so ALL 8 edges are used!
        have hew_card2 : 2 ≤ (LeafEdges C B e_w).card := by
          have hne01 : b 0 ≠ b v₁ := fun heq => hv1_ne0.symm (hb_inj 0 v₁ hv0_ne0.symm hv01.symm heq)
          calc 2 = ({b 0, b v₁} : Finset ℕ).card := (Finset.card_pair hne01).symm
            _ ≤ (Leaves C B e_w).card := Finset.card_le_card (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
            _ ≤ (LeafEdges C B e_w).card := Finset.card_image_le
        have h2_card3 : 3 ≤ (LeafEdges C B h₂).card := by
          have hne1 : b 0 ≠ b a := fun heq => ha_ne0.symm (hb_inj 0 a hv0_ne0.symm hv0a.symm heq)
          have hne2 : b 0 ≠ b c := fun heq => hc_ne0.symm (hb_inj 0 c hv0_ne0.symm hv0c.symm heq)
          have hne3 : b a ≠ b c := fun heq => hac (hb_inj a c hv0a.symm hv0c.symm heq)
          calc 3 = ({b 0, b a, b c} : Finset ℕ).card := by
                rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]), Finset.card_pair hne3]
            _ ≤ (Leaves C B h₂).card := Finset.card_le_card (by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl | rfl <;> assumption)
            _ ≤ (LeafEdges C B h₂).card := Finset.card_image_le
        have hR_sub : R.biUnion (fun r => LeafEdges C B r) ⊆ AllBEdges C B := by
          intro pr hpr; obtain ⟨r, _, hprL⟩ := Finset.mem_biUnion.mp hpr; exact leafEdges_subset_allBEdges hE hprL
        have hR_eq : R.biUnion (fun r => LeafEdges C B r) = AllBEdges C B :=
          Finset.eq_of_subset_of_card_le hR_sub (by
            rw [Finset.card_biUnion hR_disj, Finset.sum_insert hew_notH, hHpair, Finset.sum_pair h12, hAllCard]
            omega)
        have hleft_vac : ∀ pr ∈ AllBEdges C B, pr ∉ R.biUnion (fun r => LeafEdges C B r) → pr.1 = b a :=
          fun pr hpr hnot => absurd (hR_eq.symm ▸ hpr) hnot
        have hd_out_eq : d = C.output :=
          no_and_after_d_if_le_one_leftover hC hE hT hv0a.symm hB_eq hb_tr hb_le hTd hd_out hd_anc hR_to_d hleft_vac
        have hbv1_eq : b v₁ = v₁.val := by
          by_contra hne
          obtain ⟨pr, hprAll, _, hprNotL, _⟩ := non_input_branch_uses_edge hC hE hT h_input_sep (hb_mem v₁ hv01.symm) (hb_tr v₁ hv01.symm) hne
          rw [← hR_eq] at hprAll; obtain ⟨r, hrR, hprL⟩ := Finset.mem_biUnion.mp hprAll
          exact hprNotL r (hR_to_d r hrR).1 ((hR_to_d r hrR).2.trans hd_out) hprL
        -- `h₂` is a live WIDE OR gate (not AND, `< d`, so not `d`), so `val (sing x) h₂ = true` for some `x ∈ {a, c}`!
        have h2_wide : isWide C h₂ := by
          have hh5 : 5 ≤ h₂ := hH_noin h₂ hh2 h₂ ((mem_Internal hE).mpr ⟨(hH_mem h₂ hh2).1, (hH_mem h₂ hh2).2.2.1, ReflTransGen.refl⟩)
          have hlt_o := (live_le_output (hH_mem h₂ hh2).1).trans_lt (output_bounds hE).2
          set hp := h₂ - 5
          have hhp : h₂ = 5 + hp := by omega
          obtain ⟨hg, hhg⟩ : ∃ hg, C.gates[hp]? = some hg := ⟨C.gates[hp], List.getElem?_eq_getElem (by omega)⟩
          have hor : hg.op = GateOp.or := (mono_op hC hhg).resolve_left (fun hop => (hH_mem h₂ hh2).2.1 ⟨hp, hg, hhg, hhp, hop⟩)
          by_contra hnw
          have h2d : h₂ = d := hd_uniq h₂ (hH_mem h₂ hh2).1 ⟨⟨hp, hg, hhg, hhp, hor⟩, hnw⟩
          have := andAnc_le (hH_mem h₂ hh2).2.2.2; have := hlnq.1.1; omega
        obtain ⟨s₁, s₂, hs12, hs1, hs2⟩ := h2_wide
        have h2_not_sing : ∀ w : Fin 5, (w = v₀ ∨ w = v₁) → val C (sing w) h₂ = false := by
          intro w hw
          apply internal_false hC hE hT (hH_noin h₂ hh2) _ h₂
            ((mem_Internal hE).mpr ⟨(hH_mem h₂ hh2).1, (hH_mem h₂ hh2).2.2.1, ReflTransGen.refl⟩)
          intro z hz
          have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          rw [hB_eq] at hzB; obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hzB
          have hw'v := (Finset.mem_erase.mp hw').1
          cases hv : val C (sing w) (b w')
          · rfl
          · have hweq : w' = w := by have := hb_le w' hw'v (sing w) hv; simp [sing] at this; exact this
            rcases hw with rfl | rfl
            · exact absurd hweq hw'v
            · exact absurd (hweq ▸ hz) h2_nov1
        have hex_ac : ∃ x : Fin 5, (x = a ∨ x = c) ∧ val C (sing x) h₂ = true := by
          by_cases h1 : s₁ = 0
          · have h2ne0 : s₂ ≠ 0 := fun h => hs12 (h1.trans h.symm)
            rcases hfive s₂ with hs | hs | hs | hs | hs
            · exact absurd hs h2ne0
            · rw [hs, h2_not_sing v₀ (Or.inl rfl)] at hs2; cases hs2
            · rw [hs, h2_not_sing v₁ (Or.inr rfl)] at hs2; cases hs2
            · exact ⟨a, Or.inl rfl, hs ▸ hs2⟩
            · exact ⟨c, Or.inr rfl, hs ▸ hs2⟩
          · rcases hfive s₁ with hs | hs | hs | hs | hs
            · exact absurd hs h1
            · rw [hs, h2_not_sing v₀ (Or.inl rfl)] at hs1; cases hs1
            · rw [hs, h2_not_sing v₁ (Or.inr rfl)] at hs1; cases hs1
            · exact ⟨a, Or.inl rfl, hs ▸ hs1⟩
            · exact ⟨c, Or.inr rfl, hs ▸ hs1⟩
        obtain ⟨x, hxac, hx2⟩ := hex_ac
        have ht1 : val C (pairIn v₁ x) h₁ = true := by
          apply internal_mono hC hE hT (hH_noin h₁ hh1) _ h₁
            ((mem_Internal hE).mpr ⟨(hH_mem h₁ hh1).1, (hH_mem h₁ hh1).2.2.1, ReflTransGen.refl⟩)
            (hH_ge h₁ hh1 (pairIn 0 v₁) (hq_edge 0 v₁ hv0_ne0.symm hv01.symm hadj_0v1))
          intro z hz hzx
          have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
          have hwv := (Finset.mem_erase.mp hw).1
          have hwt := hb_le w hwv (pairIn 0 v₁) hzx
          simp only [pairIn, decide_eq_true_eq] at hwt
          rcases hwt with rfl | rfl
          · exact absurd hz h1_no0
          · rw [hbv1_eq, val_input]; simp [pairIn]
        have ht2 : val C (pairIn v₁ x) h₂ = true :=
          val_mono hC (x := sing x) (y := pairIn v₁ x)
            (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inr hi) h₂ hx2
        have hqt : val C (pairIn v₁ x) q = true := hH_eval (pairIn v₁ x) (fun h hh => by
          rw [hHpair, Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with rfl | rfl <;> assumption)
        have hdt : val C (pairIn v₁ x) d = true := by rw [hd_val, hqt, Bool.or_true]
        have hadj_v1x := (bowtie_pair_iff hE v₁ x).mp (hd_out_eq ▸ hdt)
        rcases hxac with rfl | rfl
        · exact hnadj_v1a hadj_v1x
        · exact hnadj_v1c hadj_v1x
      · exact kill_omit a c (Or.inl ⟨rfl, rfl⟩) h2a h2c
    · exact kill_omit c a (Or.inr ⟨rfl, rfl⟩) (h2_ac.resolve_left h2a) h2a
  · -- Case B: `val (sing v₀) p = true`!
    have hd0 : val C (sing v₀) d = true := by rw [hd_val, hp0, Bool.true_or]
    have hdt_and : ∀ w, Trace C (fun z => z ∉ B) d w → d < w → w ≤ C.output → isAndGate C w := by
      intro w hdw hlt _
      have hwl : Live C w := trace_notB_live hdw hdl
      have hw5 : 5 ≤ w := by obtain ⟨_, _, _, hdp, _⟩ := _hd_or; omega
      have hlt_o := (live_le_output hwl).trans_lt (output_bounds hE).2
      set wp := w - 5
      have hwp : w = 5 + wp := by omega
      obtain ⟨wg, hwg⟩ : ∃ wg, C.gates[wp]? = some wg := ⟨C.gates[wp], List.getElem?_eq_getElem (by omega)⟩
      rcases mono_op hC hwg with hop | hop
      · exact ⟨wp, wg, hwg, hwp, hop⟩
      · exfalso
        have := hd_uniq w hwl ⟨⟨wp, wg, hwg, hwp, hop⟩, chain_not_wide hC hE (trace_notB_to_nb hE hT (hTd.trans hdw)) hwl⟩
        omega
    obtain ⟨r, u_after, a_after, hrl, hlnu, hlnr, hru, huB, hdu, _ha_anc, hr_anc, _hrf, hr_nbr, hr_wide, hr_nr, ha_out, hr_to_out⟩ :=
      partner_after_d hC hE hT hTd hd_out hdt_and hd0 (bowtie_sing hE v₀)
    have hrB : r ∉ B := fun h => hb_not_wide r h hr_wide
    have hr_noin : ∀ u ∈ Internal C B r, 5 ≤ u := by
      intro u hu; obtain ⟨_, _, huTr⟩ := (mem_Internal hE).mp hu
      by_contra hlt; push Not at hlt
      let w : Fin 5 := ⟨u, hlt⟩
      by_cases hwv : w = v₀
      · have hvr : Trace C (fun z => z ∉ B) v₀.val r := by rwa [← hwv]
        have hstep : ∀ {x y}, Trace C (fun z => z ∉ B) x y → ReflTransGen (Next C) x y := by
          intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
        exact hr_nr (hstep hvr)
      · have hwO : Trace C (fun z => z ∉ B) w.val C.output := huTr.trans (hr_to_out hrB)
        have hbwl : Live C (b w) := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 (hb_mem w hwv)))
        exact trace_notB_of_B_not_out hT (hb_mem w hwv) (trace_notB_det hE hT (hb_tr w hwv) hwO (live_le_output hbwl))
    have hr0 : b 0 ∈ Leaves C B r :=
      leaf_hit_sing r hrl hrB hr_noin 0 hv0_ne0.symm (hr_nbr 0 (bowtieAdj_symm hadj_0v0))
    have hrv1 : b v₁ ∈ Leaves C B r :=
      leaf_hit_sing r hrl hrB hr_noin v₁ hv01.symm (hr_nbr v₁ hadj_v0v1)
    have hrac : b a ∈ Leaves C B r ∨ b c ∈ Leaves C B r :=
      leaf_hit_pair r hrl hrB hr_noin a c hv0a.symm hv0c.symm
        (andAnc_val_le hr_anc (pairIn a c) ((bowtie_pair_iff hE a c).mpr hadj_ac))
    obtain ⟨h₁, h₂, h12, hHpair, hr_notH, hR_disj, h1_no0, h1_v1, h1_a, h1_c, h1_card3, h2_yes0, h2_nov1, h2_ac, h2_card2⟩ :=
      split_H_of_partner r hr0 hrv1 (fun h hh => incomp_of_distinct_inputs hE hT hru hrB huB hlnr hlnu ReflTransGen.refl ((hH_to_d h hh).2.trans hdu))
    have hh1 : h₁ ∈ H := by rw [hHpair]; simp
    have hh2 : h₂ ∈ H := by rw [hHpair]; simp
    set R := insert r H
    have hr_card3 : 3 ≤ (LeafEdges C B r).card := by
      have hne01 : b 0 ≠ b v₁ := fun heq => hv1_ne0.symm (hb_inj 0 v₁ hv0_ne0.symm hv01.symm heq)
      rcases hrac with hra | hrc
      · have hne0a : b 0 ≠ b a := fun heq => ha_ne0.symm (hb_inj 0 a hv0_ne0.symm hv0a.symm heq)
        have hne1a : b v₁ ≠ b a := fun heq => hv1a (hb_inj v₁ a hv01.symm hv0a.symm heq)
        calc 3 = ({b 0, b v₁, b a} : Finset ℕ).card := by
              rw [Finset.card_insert_of_notMem (by simp [hne01, hne0a]), Finset.card_pair hne1a]
          _ ≤ (Leaves C B r).card := Finset.card_le_card (by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl | rfl <;> assumption)
          _ ≤ (LeafEdges C B r).card := Finset.card_image_le
      · have hne0c : b 0 ≠ b c := fun heq => hc_ne0.symm (hb_inj 0 c hv0_ne0.symm hv0c.symm heq)
        have hne1c : b v₁ ≠ b c := fun heq => hv1c (hb_inj v₁ c hv01.symm hv0c.symm heq)
        calc 3 = ({b 0, b v₁, b c} : Finset ℕ).card := by
              rw [Finset.card_insert_of_notMem (by simp [hne01, hne0c]), Finset.card_pair hne1c]
          _ ≤ (Leaves C B r).card := Finset.card_le_card (by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl | rfl <;> assumption)
          _ ≤ (LeafEdges C B r).card := Finset.card_image_le
    have hR_sub : R.biUnion (fun w => LeafEdges C B w) ⊆ AllBEdges C B := by
      intro pr hpr; obtain ⟨w, _, hprL⟩ := Finset.mem_biUnion.mp hpr; exact leafEdges_subset_allBEdges hE hprL
    have hR_eq : R.biUnion (fun w => LeafEdges C B w) = AllBEdges C B :=
      Finset.eq_of_subset_of_card_le hR_sub (by
        rw [Finset.card_biUnion hR_disj, Finset.sum_insert hr_notH, hHpair, Finset.sum_pair h12, hAllCard]
        omega)
    have hAll_sub : AllBEdges C B ⊆ LeafEdges C B r ∪ H.biUnion (fun h => LeafEdges C B h) := by
      rw [← hR_eq, Finset.biUnion_insert]
    have h_out := only_one_and_after_d_if_all_used hC hE hT hB_eq hb_tr hb_le hTd hd_out hd_anc
      hdu huB hlnu hlnr hru hrB ha_out hH_to_d hAll_sub
    have hbv_eq : ∀ w : Fin 5, w ≠ v₀ → b w = w.val := by
      intro w hwv
      by_contra hne
      obtain ⟨pr, hprAll, _, hprNotL, _⟩ := non_input_branch_uses_edge hC hE hT h_input_sep (hb_mem w hwv) (hb_tr w hwv) hne
      rw [← hR_eq] at hprAll; obtain ⟨z, hzR, hprL⟩ := Finset.mem_biUnion.mp hprAll
      rcases Finset.mem_insert.mp hzR with rfl | hzH
      · exact hprNotL z hrB (hr_to_out hrB) hprL
      · exact hprNotL z (hH_mem z hzH).2.2.1 ((hH_to_d z hzH).2.trans hd_out) hprL
    -- Since `b y ∈ Leaves r` for some `y ∈ {a, c}`, and `b y ∈ Leaves h₁`, `freq_le_two` forces `b y ∉ Leaves h₂`!
    have kill_B : ∀ x y : Fin 5, (x = a ∧ y = c ∨ x = c ∧ y = a) → b y ∈ Leaves C B r → False := by
      intro x y hxy hry
      have hxv0 : x ≠ v₀ := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hv0a.symm; exact hv0c.symm]
      have hyv0 : y ≠ v₀ := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hv0c.symm; exact hv0a.symm]
      have hnadj_v1x : ¬ bowtieAdj v₁ x := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hnadj_v1a; exact hnadj_v1c]
      have h1y : b y ∈ Leaves C B h₁ := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h1_c; exact h1_a]
      have h2ny : b y ∉ Leaves C B h₂ := by
        intro h2y
        have hsub3 : ({r, h₁, h₂} : Finset ℕ) ⊆ R.filter (fun z => b y ∈ Leaves C B z) := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          simp only [Finset.mem_filter]
          rcases hz with rfl | rfl | rfl
          · exact ⟨Finset.mem_insert_self _ _, hry⟩
          · exact ⟨Finset.mem_insert_of_mem hh1, h1y⟩
          · exact ⟨Finset.mem_insert_of_mem hh2, h2y⟩
        have hne1 : r ≠ h₁ := fun h => hr_notH (h ▸ hh1)
        have hne2 : r ≠ h₂ := fun h => hr_notH (h ▸ hh2)
        have hc3 : ({r, h₁, h₂} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]), Finset.card_pair h12]
        have hle2 := freq_le_two hE hT hR_disj (hb_mem y hyv0)
        have hle3 := Finset.card_le_card hsub3
        omega
      have ht1 : val C (pairIn v₁ x) h₁ = true := by
        apply internal_mono hC hE hT (hH_noin h₁ hh1) _ h₁
          ((mem_Internal hE).mpr ⟨(hH_mem h₁ hh1).1, (hH_mem h₁ hh1).2.2.1, ReflTransGen.refl⟩)
          (hH_ge h₁ hh1 (pairIn 0 v₁) (hq_edge 0 v₁ hv0_ne0.symm hv01.symm hadj_0v1))
        intro z hz hzx
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hwv := (Finset.mem_erase.mp hw).1
        rw [hbv_eq w hwv, val_input] at hzx ⊢
        simp only [pairIn, decide_eq_true_eq] at hzx ⊢
        rcases hzx with rfl | rfl
        · exact absurd hz h1_no0
        · exact Or.inl rfl
      have ht2 : val C (pairIn v₁ x) h₂ = true := by
        have hadj_xy : bowtieAdj x y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hadj_ac; exact bowtieAdj_symm hadj_ac]
        apply internal_mono hC hE hT (hH_noin h₂ hh2) _ h₂
          ((mem_Internal hE).mpr ⟨(hH_mem h₂ hh2).1, (hH_mem h₂ hh2).2.2.1, ReflTransGen.refl⟩)
          (hH_ge h₂ hh2 (pairIn x y) (hq_edge x y hxv0 hyv0 hadj_xy))
        intro z hz hzx
        have hzB : z ∈ B := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
        rw [hB_eq] at hzB; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzB
        have hwv := (Finset.mem_erase.mp hw).1
        rw [hbv_eq w hwv, val_input] at hzx ⊢
        simp only [pairIn, decide_eq_true_eq] at hzx ⊢
        rcases hzx with rfl | rfl
        · exact Or.inr rfl
        · exact absurd hz h2ny
      have hqt : val C (pairIn v₁ x) q = true := hH_eval (pairIn v₁ x) (fun h hh => by
        rw [hHpair, Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with rfl | rfl <;> assumption)
      have hdt : val C (pairIn v₁ x) d = true := by rw [hd_val, hqt, Bool.or_true]
      have hrt : val C (pairIn v₁ x) r = true :=
        val_mono hC (x := sing v₁) (y := pairIn v₁ x)
          (fun i hi => by simp only [sing, pairIn, decide_eq_true_eq] at hi ⊢; exact Or.inl hi) r (hr_nbr v₁ hadj_v0v1)
      exact hnadj_v1x ((bowtie_pair_iff hE v₁ x).mp (h_out (pairIn v₁ x) hdt hrt))
    rcases hrac with hra | hrc
    · exact kill_B c a (Or.inr ⟨rfl, rfl⟩) hra
    · exact kill_B a c (Or.inl ⟨rfl, rfl⟩) hrc

/-- Subcase `|S| = 3` of `|D_L| = 1`: `S = {0, u, v}` where `{0, u, u'}` and `{0, v, v'}` are
    the two triangles of the bowtie, `u', v' ∉ S`, and `(liveGates C).card ≤ 8`. Impossible! -/
theorem case_one_narrow_S3 {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    {d : ℕ} (hd_uniq : ∀ z, Live C z → isNarrowOr C z → z = d)
    (hG_le : (liveGates C).card ≤ 8)
    {u u' v v' : Fin 5}
    (hu0 : u ≠ 0) (hu'0 : u' ≠ 0) (hv0 : v ≠ 0) (hv'0 : v' ≠ 0)
    (huu' : u ≠ u') (huv : u ≠ v) (huv' : u ≠ v')
    (hu'v : u' ≠ v) (hu'v' : u' ≠ v') (hvv' : v ≠ v')
    (hadj_0u : bowtieAdj 0 u) (hadj_0u' : bowtieAdj 0 u') (hadj_uu' : bowtieAdj u u')
    (hadj_0v : bowtieAdj 0 v) (hadj_0v' : bowtieAdj 0 v') (hadj_vv' : bowtieAdj v v')
    (hnadj_uv : ¬ bowtieAdj u v) (hnadj_uv' : ¬ bowtieAdj u v')
    (hnadj_u'v : ¬ bowtieAdj u' v) (hnadj_u'v' : ¬ bowtieAdj u' v')
    (he0 : Eligible C 0) (heu : Eligible C u) (hev : Eligible C v)
    (hnu' : ¬ Eligible C u') (hnv' : ¬ Eligible C v') : False := by
  classical
  have hfive : ∀ w : Fin 5, w = 0 ∨ w = u ∨ w = u' ∨ w = v ∨ w = v' := by
    have hc5 : ({0, u, u', v, v'} : Finset (Fin 5)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hu0.symm, hu'0.symm, hv0.symm, hv'0.symm]),
          Finset.card_insert_of_notMem (by simp [huu', huv, huv']),
          Finset.card_insert_of_notMem (by simp [hu'v, hu'v']),
          Finset.card_pair hvv']
    have huniv : ({0, u, u', v, v'} : Finset (Fin 5)) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hc5)
    intro w
    have hw : w ∈ ({0, u, u', v, v'} : Finset (Fin 5)) := by rw [huniv]; exact Finset.mem_univ w
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
  set B_all := ((living C).erase C.output).filter (Branch C)
  have hBall_le4 : B_all.card ≤ 4 := by
    have hbud := live_budget_exact hC hE
    have hsub : B_all ⊆ (living C).erase C.output := Finset.filter_subset _ _
    have h1 : B_all.card ≤ ∑ a ∈ B_all, (outdeg C a - 1) := by
      calc B_all.card = ∑ _a ∈ B_all, 1 := by simp
        _ ≤ ∑ a ∈ B_all, (outdeg C a - 1) := Finset.sum_le_sum fun a ha => by
            have := (branch_iff_two_le_outdeg hE a).mp (Finset.mem_filter.mp ha).2; omega
    have h2 : ∑ a ∈ B_all, (outdeg C a - 1) ≤ ∑ a ∈ (living C).erase C.output, (outdeg C a - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    omega
  -- `b0, bu, bv` are three distinct elements of `B_all`!
  set b0 := firstBranch C 0 he0
  set bu := firstBranch C u heu
  set bv := firstBranch C v hev
  have sb0 := firstBranch_spec hC hE he0
  have sbu := firstBranch_spec hC hE heu
  have sbv := firstBranch_spec hC hE hev
  have mem_Ball : ∀ w, Live C w → Branch C w → w ∈ B_all := fun w hwl hwb => by
    have hne : w ≠ C.output := by
      intro h; have := (branch_iff_two_le_outdeg hE w).mp hwb; rw [h, outdeg_output hE] at this; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, (mem_living hE).mpr hwl⟩, hwb⟩
  have hb0_mem : b0 ∈ B_all := mem_Ball b0 sb0.1 sb0.2.2.1
  have hbu_mem : bu ∈ B_all := mem_Ball bu sbu.1 sbu.2.2.1
  have hbv_mem : bv ∈ B_all := mem_Ball bv sbv.1 sbv.2.2.1
  have h0u_ne : b0 ≠ bu := fun h => hu0.symm (firstBranch_injective hC hE he0 heu h)
  have h0v_ne : b0 ≠ bv := fun h => hv0.symm (firstBranch_injective hC hE he0 hev h)
  have huv_ne : bu ≠ bv := fun h => huv (firstBranch_injective hC hE heu hev h)
  have nb_to_notB : ∀ {x y}, Trace C (fun z => ¬ Branch C z) x y → Trace C (fun z => z ∉ B_all) x y := by
    intro x y hxy
    induction hxy with
    | refl => exact ReflTransGen.refl
    | tail _ s ih => exact ih.tail ⟨fun h => s.1 (Finset.mem_filter.mp h).2, s.2⟩
  have notB_to_nb : ∀ {x y}, Trace C (fun z => z ∉ B_all) x y → Trace C (fun z => ¬ Branch C z) x y := by
    intro x y hxy
    induction hxy with
    | refl => exact ReflTransGen.refl
    | tail _ s ih =>
      have hnb : ¬ Branch C _ := fun hb => s.1 (mem_Ball _ (live_of_lnext s.2) hb)
      exact ih.tail ⟨hnb, s.2⟩
  -- Every vertex either hits some wire in `B_all` via `Trace (· ∉ B_all)` or reaches `C.output` via `Trace (· ∉ B_all)`!
  have chain_hit_or_out : ∀ w : Fin 5,
      (∃ z ∈ B_all, Trace C (fun q => q ∉ B_all) w.val z) ∨ Trace C (fun q => q ∉ B_all) w.val C.output := by
    intro w
    by_cases hex : ∃ z ∈ B_all, Trace C (fun q => q ∉ B_all) w.val z
    · exact Or.inl hex
    · right; push Not at hex
      suffices ∀ k x, x = C.output - k → Live C x → Trace C (fun q => q ∉ B_all) w.val x →
          Trace C (fun q => q ∉ B_all) w.val C.output from
        this (C.output - w.val) w.val (by have := live_le_output (input_live hE w); omega) (input_live hE w) ReflTransGen.refl
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro x hxk hxl hTx
        by_cases hxo : x = C.output
        · exact hxo ▸ hTx
        · have hxB : x ∉ B_all := fun hx => hex x hx hTx
          rcases hxl.cases_head with rfl | ⟨x', hxx', hx'o⟩
          · exact absurd rfl hxo
          · have := live_le_output hx'o; have := hxx'.1
            exact ih (C.output - x') (by omega) x' (by omega) hx'o (hTx.tail ⟨hxB, hxx', hx'o⟩)
  -- Any `z ∈ B_all` hit by `w ∈ {u', v'}` is distinct from `b0, bu, bv`!
  have hit_not_elig : ∀ (w : Fin 5), w ≠ 0 → w ≠ u → w ≠ v →
      ∀ z ∈ B_all, Trace C (fun q => q ∉ B_all) w.val z → z ≠ b0 ∧ z ≠ bu ∧ z ≠ bv := by
    intro w hw0 hwu hwv z hz hwz
    have hzl : Live C z := (mem_living hE).mp (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1)
    refine ⟨?_, ?_, ?_⟩
    · intro h; subst h; exact hw0.symm (chain_sing_subset hC hE (notB_to_nb hwz) hzl sb0.2.1.1)
    · intro h; subst h; exact hwu.symm (chain_sing_subset hC hE (notB_to_nb hwz) hzl sbu.2.1.1)
    · intro h; subst h; exact hwv.symm (chain_sing_subset hC hE (notB_to_nb hwz) hzl sbv.2.1.1)
  -- Helper: if `z ∈ B_all` is distinct from `b0, bu, bv`, then `B_all = {b0, bu, bv, z}`, `B_all.card = 4`, and `TightCut C B_all`!
  have make_tight4 : ∀ z ∈ B_all, z ≠ b0 → z ≠ bu → z ≠ bv →
      B_all = {b0, bu, bv, z} ∧ B_all.card = 4 ∧ TightCut C B_all := by
    intro z hz hz0 hzu hzv
    have hsub4 : ({b0, bu, bv, z} : Finset ℕ) ⊆ B_all := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hc4 : ({b0, bu, bv, z} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [h0u_ne, h0v_ne, hz0.symm]),
          Finset.card_insert_of_notMem (by simp [huv_ne, hzu.symm]),
          Finset.card_pair hzv.symm]
    have heq : ({b0, bu, bv, z} : Finset ℕ) = B_all := Finset.eq_of_subset_of_card_le hsub4 (by omega)
    have hBc : B_all.card = 4 := by rw [← heq, hc4]
    have hT : TightCut C B_all := tightCut_of_le hC hE (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) (by omega)
    exact ⟨heq.symm, hBc, hT⟩
  -- Now case-split on whether `u'` and `v'` hit `B_all`!
  rcases chain_hit_or_out u' with ⟨bu', hbu'_mem, hu'b⟩ | hu'out
  · rcases chain_hit_or_out v' with ⟨bv', hbv'_mem, hv'b⟩ | hv'out
    · -- Subcase 3.4: BOTH `u'` and `v'` hit `B_all`! They MUST hit the SAME `b*`!
      obtain ⟨hbu'_0, hbu'_u, hbu'_v⟩ := hit_not_elig u' hu'0 huu'.symm hu'v bu' hbu'_mem hu'b
      obtain ⟨hbv'_0, hbv'_u, hbv'_v⟩ := hit_not_elig v' hv'0 huv'.symm hvv'.symm bv' hbv'_mem hv'b
      obtain ⟨hB_eq4, _hBc4, hT⟩ := make_tight4 bu' hbu'_mem hbu'_0 hbu'_u hbu'_v
      have hbv'_eq : bv' = bu' := by
        have hmem : bv' ∈ ({b0, bu, bv, bu'} : Finset ℕ) := hB_eq4 ▸ hbv'_mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact absurd rfl hbv'_0
        · exact absurd rfl hbv'_u
        · exact absurd rfl hbv'_v
        · rfl
      rw [hbv'_eq] at hv'b
      set bs := bu'
      have hbs_l : Live C bs := (mem_living hE).mp (Finset.mem_of_mem_erase (Finset.mem_filter.mp hbu'_mem).1)
      have hbs_br : Branch C bs := (Finset.mem_filter.mp hbu'_mem).2
      obtain ⟨pu, pv, hpuv, hlnpu, hlnpv, hTpu_nb, hTpv_nb, hu'd_nb, hv'd_nb, hd_bs_nb, hd_val, hpu_le, hpv_le, hd_bs_anc⟩ :=
        two_chains_meet_at_unique_narrow hC hE hd_uniq hu'v' hbs_l (notB_to_nb hu'b) (notB_to_nb hv'b)
      have hTpu : Trace C (fun z => z ∉ B_all) u'.val pu := nb_to_notB hTpu_nb
      have hTpv : Trace C (fun z => z ∉ B_all) v'.val pv := nb_to_notB hTpv_nb
      have hu'd : Trace C (fun z => z ∉ B_all) u'.val d := nb_to_notB hu'd_nb
      have hv'd : Trace C (fun z => z ∉ B_all) v'.val d := nb_to_notB hv'd_nb
      have hd_bs : Trace C (fun z => z ∉ B_all) d bs := nb_to_notB hd_bs_nb
      have hpuB : pu ∉ B_all := by
        rcases hu'd_nb.cases_tail with heq | ⟨pu', _, hpu'_nb, hlnpu'⟩
        · have := hlnpu.1.1; have := u'.isLt; have := hlnpu.1.2.choose_spec.choose_spec.2.1; omega
        · intro hmem
          have hbr := (Finset.mem_filter.mp hmem).2
          have hpu_le_d : pu ≤ d := hlnpu.1.1.le
          have htr := trace_nb_det hTpu_nb hu'd_nb hpu_le_d
          rcases htr.cases_head with rfl | ⟨_, step, _⟩
          · have := hlnpu.1.1; omega
          · exact step.1 hbr
      have hpvB : pv ∉ B_all := by
        intro hmem
        have hbr := (Finset.mem_filter.mp hmem).2
        have htr := trace_nb_det hTpv_nb hv'd_nb hlnpv.1.1.le
        rcases htr.cases_head with rfl | ⟨_, step, _⟩
        · have := hlnpv.1.1; omega
        · exact step.1 hbr
      -- `bs ≤ x_{u'} ∨ x_{v'}`!
      have hbs_le : ∀ x, val C x bs = true → x u' = true ∨ x v' = true := by
        intro x hx
        have hdt := andAnc_val_le hd_bs_anc x hx
        rw [hd_val, Bool.or_eq_true] at hdt
        rcases hdt with h1 | h2
        · exact Or.inl (hpu_le x h1)
        · exact Or.inr (hpv_le x h2)
      -- `val (sing u') bs = false` and `val (sing v') bs = false` (since `u', v' ∉ S`)!
      have hbs_zero : val C zeroIn bs = false := by
        cases h : val C zeroIn bs
        · rfl
        · rcases hbs_le zeroIn h with h1 | h2
          · simp [zeroIn] at h1
          · simp [zeroIn] at h2
      have hbs_fu' : val C (sing u') bs = false := by
        cases h : val C (sing u') bs
        · rfl
        · exact absurd ⟨bs, hbs_l, ⟨h, hbs_zero⟩, hbs_br⟩ hnu'
      have hbs_fv' : val C (sing v') bs = false := by
        cases h : val C (sing v') bs
        · rfl
        · exact absurd ⟨bs, hbs_l, ⟨h, hbs_zero⟩, hbs_br⟩ hnv'
      -- Also `b0 ≤ x_0`, `bu ≤ x_u`, `bv ≤ x_v` (because `d` reaches `bs ∉ {b0, bu, bv}`, so `d` isn't on `w → b_w`)!
      have elig_le : ∀ (w : Fin 5) (bw : ℕ), bw ∈ B_all → bw ≠ bs →
          Trace C (fun z => ¬ Branch C z) w.val bw → Live C bw →
          ∀ x, val C x bw = true → x w = true := by
        intro w bw hbwB hbw_ne hwb hbl
        apply and_chain_le_input hC hE hwb hbl
        intro z hzw hle hnw
        have hzd : z = d := hd_uniq z (trace_nb_live hzw (input_live hE w)) hnw
        subst z
        have hwb_nB := nb_to_notB hwb
        have hwd_nB := nb_to_notB hzw
        have hdbw : Trace C (fun q => q ∉ B_all) d bw := trace_notB_det hE hT hwd_nB hwb_nB hle
        rcases le_total bw bs with h1 | h2
        · rcases (trace_notB_det hE hT hdbw hd_bs h1).cases_head with rfl | ⟨_, step, _⟩
          · exact hbw_ne rfl
          · exact step.1 hbwB
        · rcases (trace_notB_det hE hT hd_bs hdbw h2).cases_head with rfl | ⟨_, step, _⟩
          · exact hbw_ne rfl
          · exact step.1 hbu'_mem
      have hb0_le := elig_le 0 b0 hb0_mem hbu'_0.symm sb0.2.2.2 sb0.1
      have hbu_le := elig_le u bu hbu_mem hbu'_u.symm sbu.2.2.2 sbu.1
      have hbv_le := elig_le v bv hbv_mem hbu'_v.symm sbv.2.2.2 sbv.1
      have hb_not_wide : ∀ z ∈ B_all, ¬ isWide C z := by
        intro z hz
        have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
        rcases hz4 with rfl | rfl | rfl | rfl
        · exact chain_not_wide hC hE sb0.2.2.2 sb0.1
        · exact chain_not_wide hC hE sbu.2.2.2 sbu.1
        · exact chain_not_wide hC hE sbv.2.2.2 sbv.1
        · exact chain_not_wide hC hE (notB_to_nb hu'b) hbs_l
      -- Build `H = AndLeaves C.output`!
      have hOut_noB : ∀ z, AndAnc C z C.output → z ∉ B_all := by
        intro z hzo hzB
        have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
        rcases hz4 with rfl | rfl | rfl | rfl
        · have ht := hb0_le (pairIn u u') (andAnc_val_le hzo (pairIn u u') ((bowtie_pair_iff hE u u').mpr hadj_uu'))
          simp only [pairIn, decide_eq_true_eq] at ht; rcases ht with h1 | h2
          · exact hu0 h1.symm
          · exact hu'0 h2.symm
        · have ht := hbu_le (pairIn 0 v) (andAnc_val_le hzo (pairIn 0 v) ((bowtie_pair_iff hE 0 v).mpr hadj_0v))
          simp only [pairIn, decide_eq_true_eq] at ht; rcases ht with h1 | h2
          · exact hu0 h1
          · exact huv h2
        · have ht := hbv_le (pairIn 0 u) (andAnc_val_le hzo (pairIn 0 u) ((bowtie_pair_iff hE 0 u).mpr hadj_0u))
          simp only [pairIn, decide_eq_true_eq] at ht; rcases ht with h1 | h2
          · exact hv0 h1
          · exact huv h2.symm
        · rcases hbs_le (pairIn 0 u) (andAnc_val_le hzo (pairIn 0 u) ((bowtie_pair_iff hE 0 u).mpr hadj_0u)) with h1 | h2
          · simp only [pairIn, decide_eq_true_eq] at h1; rcases h1 with h | h; exact hu'0 h; exact huu' h.symm
          · simp only [pairIn, decide_eq_true_eq] at h2; rcases h2 with h | h; exact hv'0 h; exact huv' h.symm
      obtain ⟨H, hH_mem, hH_ge, hH_eval, hH_incomp⟩ :=
        and_tree_decomp hC hE hT C.output ReflTransGen.refl hOut_noB
      have hH_out : ∀ h ∈ H, Trace C (fun z => z ∉ B_all) h C.output := fun h hh =>
        andAnc_to_trace_notB (hH_mem h hh).2.2.2 hOut_noB
      -- Every `w : Fin 5` hits `B_all`, so `∀ h ∈ H, ∀ q ∈ Internal C B_all h, 5 ≤ q`!
      have hAll_hit_B : ∀ w : Fin 5, ∃ z ∈ B_all, Trace C (fun q => q ∉ B_all) w.val z := by
        intro w
        rcases hfive w with rfl | rfl | rfl | rfl | rfl
        · exact ⟨b0, hb0_mem, nb_to_notB sb0.2.2.2⟩
        · exact ⟨bu, hbu_mem, nb_to_notB sbu.2.2.2⟩
        · exact ⟨bs, hbu'_mem, hu'b⟩
        · exact ⟨bv, hbv_mem, nb_to_notB sbv.2.2.2⟩
        · exact ⟨bs, hbu'_mem, hv'b⟩
      have hH_noin : ∀ h ∈ H, ∀ q ∈ Internal C B_all h, 5 ≤ q := by
        intro h hh q hq; obtain ⟨_, _, hqTh⟩ := (mem_Internal hE).mp hq
        by_contra hlt; push Not at hlt
        let w : Fin 5 := ⟨q, hlt⟩
        obtain ⟨z, hzB, hwz⟩ := hAll_hit_B w
        have hwO : Trace C (fun x => x ∉ B_all) w.val C.output := hqTh.trans (hH_out h hh)
        have hzl : Live C z := (mem_living hE).mp (Finset.mem_of_mem_erase (hT.1 hzB))
        exact trace_notB_of_B_not_out hT hzB (trace_notB_det hE hT hwz hwO (live_le_output hzl))
      -- Every `h ∈ H` is wide (not AND, `5 ≤ h`, and cannot be `d` since `d` reaches `bs ∈ B_all`)!
      have hH_wide : ∀ h ∈ H, isWide C h := by
        intro h hh
        have hh5 := hH_noin h hh h ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
        have hlt_o := (live_le_output (hH_mem h hh).1).trans_lt (output_bounds hE).2
        set hp := h - 5
        have hhp : h = 5 + hp := by omega
        obtain ⟨hg, hhg⟩ : ∃ hg, C.gates[hp]? = some hg := ⟨C.gates[hp], List.getElem?_eq_getElem (by omega)⟩
        have hor : hg.op = GateOp.or := (mono_op hC hhg).resolve_left (fun hop => (hH_mem h hh).2.1 ⟨hp, hg, hhg, hhp, hop⟩)
        by_contra hnw
        have hhd : h = d := hd_uniq h (hH_mem h hh).1 ⟨⟨hp, hg, hhg, hhp, hor⟩, hnw⟩
        subst hhd
        exact trace_notB_of_B_not_out hT hbu'_mem (trace_notB_det hE hT hd_bs (hH_out h hh) (live_le_output hbs_l))
      have hH_card_ge3 : 3 ≤ H.card := by
        by_contra hlt; push Not at hlt
        interval_cases hc : H.card
        · have hHe := Finset.card_eq_zero.mp hc
          have h0 := hH_eval zeroIn (fun h hh => by rw [hHe] at hh; simp at hh)
          rw [bowtie_zero hE] at h0; cases h0
        · obtain ⟨h, hHs⟩ := Finset.card_eq_one.mp hc
          have hh : h ∈ H := by rw [hHs]; simp
          obtain ⟨s₁, _, _, hs1, _⟩ := hH_wide h hh
          have h0 := hH_eval (sing s₁) (fun h' hh' => by rw [hHs, Finset.mem_singleton] at hh'; subst h'; exact hs1)
          rw [bowtie_sing hE s₁] at h0; cases h0
        · obtain ⟨h₁, h₂, _, hHpair⟩ := Finset.card_eq_two.mp hc
          have hh1 : h₁ ∈ H := by rw [hHpair]; simp
          have hh2 : h₂ ∈ H := by rw [hHpair]; simp
          exact two_wide_or_ne_bowtie hC hE (hH_wide h₁ hh1) (hH_wide h₂ hh2) (fun x =>
            ⟨fun hx => ⟨hH_ge h₁ hh1 x hx, hH_ge h₂ hh2 x hx⟩,
             fun ⟨h1, h2⟩ => hH_eval x (fun h hh => by rw [hHpair, Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with rfl | rfl <;> assumption)⟩)
      -- Helper: any `r ∉ B_all` with `Trace (· ∉ B_all) r bs` is incomparable to EVERY `h ∈ H`!
      have incomp_bs_H : ∀ r, r ∉ B_all → Trace C (fun z => z ∉ B_all) r bs →
          ∀ h ∈ H, ¬ Trace C (fun z => z ∉ B_all) r h ∧ ¬ Trace C (fun z => z ∉ B_all) h r := by
        intro r _ hrbs h hh
        constructor
        · intro hrh
          exact trace_notB_of_B_not_out hT hbu'_mem (trace_notB_det hE hT hrbs (hrh.trans (hH_out h hh)) (live_le_output hbs_l))
        · intro hhr
          exact trace_notB_of_B_not_out hT hbu'_mem (trace_notB_det hE hT (hhr.trans hrbs) (hH_out h hh) (live_le_output hbs_l))
      -- Helper: every `h ∈ H` hits `{b0, bu}` AND `{b0, bv}`!
      have hH_hit_0u : ∀ h ∈ H, b0 ∈ Leaves C B_all h ∨ bu ∈ Leaves C B_all h := by
        intro h hh; by_contra hno; push Not at hno
        have hhf : val C (pairIn 0 u) h = false := by
          apply internal_false hC hE hT (hH_noin h hh) _ h
            ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
          intro z hz
          have hzB : z ∈ B_all := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hzB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
          rcases hz4 with rfl | rfl | rfl | rfl
          · exact absurd hz hno.1
          · exact absurd hz hno.2
          · cases hval : val C (pairIn 0 u) bv
            · rfl
            · have hv := hbv_le (pairIn 0 u) hval; simp only [pairIn, decide_eq_true_eq] at hv
              rcases hv with h1 | h2; exact absurd h1 hv0; exact absurd h2 huv.symm
          · cases hval : val C (pairIn 0 u) bs
            · rfl
            · rcases hbs_le (pairIn 0 u) hval with h1 | h2
              · simp only [pairIn, decide_eq_true_eq] at h1; rcases h1 with h1 | h1; exact absurd h1 hu'0; exact absurd h1 huu'.symm
              · simp only [pairIn, decide_eq_true_eq] at h2; rcases h2 with h2 | h2; exact absurd h2 hv'0; exact absurd h2 huv'.symm
        have hht := hH_ge h hh (pairIn 0 u) ((bowtie_pair_iff hE 0 u).mpr hadj_0u)
        rw [hhf] at hht; cases hht
      have hH_hit_0v : ∀ h ∈ H, b0 ∈ Leaves C B_all h ∨ bv ∈ Leaves C B_all h := by
        intro h hh; by_contra hno; push Not at hno
        have hhf : val C (pairIn 0 v) h = false := by
          apply internal_false hC hE hT (hH_noin h hh) _ h
            ((mem_Internal hE).mpr ⟨(hH_mem h hh).1, (hH_mem h hh).2.2.1, ReflTransGen.refl⟩)
          intro z hz
          have hzB : z ∈ B_all := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hzB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
          rcases hz4 with rfl | rfl | rfl | rfl
          · exact absurd hz hno.1
          · cases hval : val C (pairIn 0 v) bu
            · rfl
            · have hu' := hbu_le (pairIn 0 v) hval; simp only [pairIn, decide_eq_true_eq] at hu'
              rcases hu' with h1 | h2; exact absurd h1 hu0; exact absurd h2 huv
          · exact absurd hz hno.2
          · cases hval : val C (pairIn 0 v) bs
            · rfl
            · rcases hbs_le (pairIn 0 v) hval with h1 | h2
              · simp only [pairIn, decide_eq_true_eq] at h1; rcases h1 with h1 | h1; exact absurd h1 hu'0; exact absurd h1 hu'v
              · simp only [pairIn, decide_eq_true_eq] at h2; rcases h2 with h2 | h2; exact absurd h2 hv'0; exact absurd h2 hvv'.symm
        have hht := hH_ge h hh (pairIn 0 v) ((bowtie_pair_iff hE 0 v).mpr hadj_0v)
        rw [hhf] at hht; cases hht
      -- Helper: for `r ∉ B_all` with `∀ q ∈ Internal C B_all r, 5 ≤ q`:
      -- `val (sing 0) r = true → b0 ∈ Leaves r`, `val (sing u) r = true → bu ∈ Leaves r`, `val (sing v) r = true → bv ∈ Leaves r`!
      have leaf_of_sing0 : ∀ r, Live C r → r ∉ B_all → (∀ q ∈ Internal C B_all r, 5 ≤ q) →
          val C (sing 0) r = true → b0 ∈ Leaves C B_all r := by
        intro r hrl hrB hr_noin hrt; by_contra hno
        have hrf : val C (sing 0) r = false := by
          apply internal_false hC hE hT hr_noin _ r ((mem_Internal hE).mpr ⟨hrl, hrB, ReflTransGen.refl⟩)
          intro z hz
          have hzB : z ∈ B_all := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hzB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
          rcases hz4 with rfl | rfl | rfl | rfl
          · exact absurd hz hno
          · cases h : val C (sing 0) bu; rfl; have := hbu_le (sing 0) h; simp [sing] at this; exact absurd this hu0
          · cases h : val C (sing 0) bv; rfl; have := hbv_le (sing 0) h; simp [sing] at this; exact absurd this hv0
          · cases h : val C (sing 0) bs; rfl
            rcases hbs_le (sing 0) h with h1 | h2
            · simp [sing] at h1; exact absurd h1 hu'0
            · simp [sing] at h2; exact absurd h2 hv'0
        rw [hrf] at hrt; cases hrt
      have leaf_of_singu : ∀ r, Live C r → r ∉ B_all → (∀ q ∈ Internal C B_all r, 5 ≤ q) →
          val C (sing u) r = true → bu ∈ Leaves C B_all r := by
        intro r hrl hrB hr_noin hrt; by_contra hno
        have hrf : val C (sing u) r = false := by
          apply internal_false hC hE hT hr_noin _ r ((mem_Internal hE).mpr ⟨hrl, hrB, ReflTransGen.refl⟩)
          intro z hz
          have hzB : z ∈ B_all := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hzB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
          rcases hz4 with rfl | rfl | rfl | rfl
          · cases h : val C (sing u) b0; rfl; have := hb0_le (sing u) h; simp [sing] at this; exact absurd this.symm hu0
          · exact absurd hz hno
          · cases h : val C (sing u) bv; rfl; have := hbv_le (sing u) h; simp [sing] at this; exact absurd this.symm huv
          · cases h : val C (sing u) bs; rfl
            rcases hbs_le (sing u) h with h1 | h2
            · simp [sing] at h1; exact absurd h1.symm huu'
            · simp [sing] at h2; exact absurd h2.symm huv'
        rw [hrf] at hrt; cases hrt
      have leaf_of_singv : ∀ r, Live C r → r ∉ B_all → (∀ q ∈ Internal C B_all r, 5 ≤ q) →
          val C (sing v) r = true → bv ∈ Leaves C B_all r := by
        intro r hrl hrB hr_noin hrt; by_contra hno
        have hrf : val C (sing v) r = false := by
          apply internal_false hC hE hT hr_noin _ r ((mem_Internal hE).mpr ⟨hrl, hrB, ReflTransGen.refl⟩)
          intro z hz
          have hzB : z ∈ B_all := by obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hz; exact ((mem_LeafEdges hE).mp hpr).1
          have hz4 : z ∈ ({b0, bu, bv, bs} : Finset ℕ) := hB_eq4 ▸ hzB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz4
          rcases hz4 with rfl | rfl | rfl | rfl
          · cases h : val C (sing v) b0; rfl; have := hb0_le (sing v) h; simp [sing] at this; exact absurd this.symm hv0
          · cases h : val C (sing v) bu; rfl; have := hbu_le (sing v) h; simp [sing] at this; exact absurd this huv
          · exact absurd hz hno
          · cases h : val C (sing v) bs; rfl
            rcases hbs_le (sing v) h with h1 | h2
            · simp [sing] at h1; exact absurd h1 hu'v
            · simp [sing] at h2; exact absurd h2.symm hvv'
        rw [hrf] at hrt; cases hrt
      -- Helper: if ANY `r ∉ B_all` reaches `bs` and has `b0 ∈ Leaves r` AND `bw ∈ Leaves r` (where every `h ∈ H` hits `{b0, bw}`), contradiction!
      have kill_with_two_leaves : ∀ (r bw : ℕ), r ∉ B_all → Trace C (fun z => z ∉ B_all) r bs →
          bw ∈ B_all → b0 ∈ Leaves C B_all r → bw ∈ Leaves C B_all r →
          (∀ h ∈ H, b0 ∈ Leaves C B_all h ∨ bw ∈ Leaves C B_all h) → False := by
        intro r bw hrB hrbs hbwB hr0 hrw hHit
        have hr_notH : r ∉ H := fun h => (incomp_bs_H r hrB hrbs r h).1 ReflTransGen.refl
        set R := insert r H
        have hR_disj : (R : Set ℕ).PairwiseDisjoint (fun x => LeafEdges C B_all x) := by
          intro x₁ h1 x₂ h2 hne
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp h1) with rfl | h1H <;>
            rcases Finset.mem_insert.mp (Finset.mem_coe.mp h2) with rfl | h2H
          · exact absurd rfl hne
          · exact leafEdges_disjoint hE hT (incomp_bs_H x₁ hrB hrbs x₂ h2H).1 (incomp_bs_H x₁ hrB hrbs x₂ h2H).2
          · exact leafEdges_disjoint hE hT (incomp_bs_H x₂ hrB hrbs x₁ h1H).2 (incomp_bs_H x₂ hrB hrbs x₁ h1H).1
          · exact leafEdges_disjoint hE hT (hH_incomp x₁ h1H x₂ h2H hne) (hH_incomp x₂ h2H x₁ h1H hne.symm)
        have hle1 : ∀ z ∈ B_all, z ∈ Leaves C B_all r → (H.filter (fun h => z ∈ Leaves C B_all h)).card ≤ 1 := by
          intro z hzB hrz
          have h2 := freq_le_two hE hT hR_disj hzB
          have heq : R.filter (fun x => z ∈ Leaves C B_all x) = insert r (H.filter (fun h => z ∈ Leaves C B_all h)) := by
            ext x; simp only [R, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hxH, hxz⟩; exact Or.inl rfl; exact Or.inr ⟨hxH, hxz⟩
            · rintro (rfl | ⟨hxH, hxz⟩); exact ⟨Or.inl rfl, hrz⟩; exact ⟨Or.inr hxH, hxz⟩
          rw [heq, Finset.card_insert_of_notMem (fun h => hr_notH (Finset.mem_filter.mp h).1)] at h2
          omega
        have hc0 := hle1 b0 hb0_mem hr0
        have hcw := hle1 bw hbwB hrw
        have hsub : H ⊆ H.filter (fun h => b0 ∈ Leaves C B_all h) ∪ H.filter (fun h => bw ∈ Leaves C B_all h) := by
          intro h hh; rw [Finset.mem_union]
          rcases hHit h hh with h1 | h2
          · exact Or.inl (Finset.mem_filter.mpr ⟨hh, h1⟩)
          · exact Or.inr (Finset.mem_filter.mpr ⟨hh, h2⟩)
        have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        omega
      -- Helper: every gate strictly after `d` on `d → ... → bs` is an AND gate!
      have hd_bs_all_and : ∀ w, Trace C (fun z => z ∉ B_all) d w → d < w → w ≤ bs → isAndGate C w := by
        intro w hdw hlt _
        have hdl : Live C d := trace_nb_live hu'd_nb (input_live hE u')
        have hwl : Live C w := trace_notB_live hdw hdl
        have hw5 : 5 ≤ w := by have := hlnpu.1.2.choose_spec.choose_spec.2.1; omega
        have hlt_o := (live_le_output hwl).trans_lt (output_bounds hE).2
        set wp := w - 5
        have hwp : w = 5 + wp := by omega
        obtain ⟨wg, hwg⟩ : ∃ wg, C.gates[wp]? = some wg := ⟨C.gates[wp], List.getElem?_eq_getElem (by omega)⟩
        rcases mono_op hC hwg with hop | hop
        · exact ⟨wp, wg, hwg, hwp, hop⟩
        · exfalso
          have := hd_uniq w hwl ⟨⟨wp, wg, hwg, hwp, hop⟩, chain_not_wide hC hE (hu'd_nb.trans (notB_to_nb hdw)) hwl⟩
          omega
      -- Helper: no input `< 5` is in `Internal C B_all r` when `Trace (· ∉ B_all) r bs` and `u', v'` cannot reach `r`!
      have noin_of_bs : ∀ r, Trace C (fun z => z ∉ B_all) r bs →
          ¬ Trace C (fun z => z ∉ B_all) u'.val r → ¬ Trace C (fun z => z ∉ B_all) v'.val r →
          ∀ q ∈ Internal C B_all r, 5 ≤ q := by
        intro r hrbs hnr_u' hnr_v' q hq
        obtain ⟨_, _, hqTr⟩ := (mem_Internal hE).mp hq
        by_contra hlt; push Not at hlt
        let w : Fin 5 := ⟨q, hlt⟩
        have kill_elig : ∀ (bw : ℕ), bw ∈ B_all → bw ≠ bs → Trace C (fun z => z ∉ B_all) w.val bw → False := by
          intro bw hbwB hne hwb
          have hwr : Trace C (fun z => z ∉ B_all) w.val bs := hqTr.trans hrbs
          rcases le_total bw bs with h1 | h2
          · rcases (trace_notB_det hE hT hwb hwr h1).cases_head with rfl | ⟨_, step, _⟩
            · exact hne rfl
            · exact step.1 hbwB
          · rcases (trace_notB_det hE hT hwr hwb h2).cases_head with rfl | ⟨_, step, _⟩
            · exact hne rfl
            · exact step.1 hbu'_mem
        rcases hfive w with hw | hw | hw | hw | hw
        · exact kill_elig b0 hb0_mem hbu'_0.symm (hw ▸ nb_to_notB sb0.2.2.2)
        · exact kill_elig bu hbu_mem hbu'_u.symm (hw ▸ nb_to_notB sbu.2.2.2)
        · exact hnr_u' (hw ▸ hqTr)
        · exact kill_elig bv hbv_mem hbu'_v.symm (hw ▸ nb_to_notB sbv.2.2.2)
        · exact hnr_v' (hw ▸ hqTr)
      -- Now split on `val C (sing u') pu` and `val C (sing v') pv`!
      cases hpu_t : val C (sing u') pu
      · cases hpv_t : val C (sing v') pv
        · -- Both `pu(e_{u'}) = false` and `pv(e_{v'}) = false`!
          have hnoD_pu : ∀ z, Trace C (fun q => ¬ Branch C q) u'.val z → z ≤ pu → ¬ isNarrowOr C z := by
            intro z hz hle hnw; have := hd_uniq z (trace_nb_live hz (input_live hE u')) hnw; have := hlnpu.1.1; omega
          have hnoD_pv : ∀ z, Trace C (fun q => ¬ Branch C q) v'.val z → z ≤ pv → ¬ isNarrowOr C z := by
            intro z hz hle hnw; have := hd_uniq z (trace_nb_live hz (input_live hE v')) hnw; have := hlnpv.1.1; omega
          obtain ⟨hu_w, _, huwl, _, _, _, huw_nbr, huw_wide, huw_nr, huw_to_pu⟩ :=
            partner_before_d hC hE hT hTpu (live_of_lnext hlnpu) hnoD_pu hpu_t
          obtain ⟨hv_w, _, hvwl, _, _, _, hvw_nbr, hvw_wide, hvw_nr, hvw_to_pv⟩ :=
            partner_before_d hC hE hT hTpv (live_of_lnext hlnpv) hnoD_pv hpv_t
          have huwB : hu_w ∉ B_all := fun h => hb_not_wide hu_w h huw_wide
          have hvwB : hv_w ∉ B_all := fun h => hb_not_wide hv_w h hvw_wide
          have huw_pu : Trace C (fun z => z ∉ B_all) hu_w pu := huw_to_pu huwB
          have hvw_pv : Trace C (fun z => z ∉ B_all) hv_w pv := hvw_to_pv hvwB
          have huw_bs : Trace C (fun z => z ∉ B_all) hu_w bs := (huw_pu.tail ⟨hpuB, hlnpu⟩).trans hd_bs
          have hvw_bs : Trace C (fun z => z ∉ B_all) hv_w bs := (hvw_pv.tail ⟨hpvB, hlnpv⟩).trans hd_bs
          have hstep_n : ∀ {x y}, Trace C (fun z => z ∉ B_all) x y → ReflTransGen (Next C) x y := by
            intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
          have huw_noin := noin_of_bs hu_w huw_bs (fun h => huw_nr (hstep_n h))
            (incomp_of_distinct_inputs hE hT hpuv.symm hpvB hpuB hlnpv hlnpu hTpv huw_pu).1
          have hvw_noin := noin_of_bs hv_w hvw_bs
            (incomp_of_distinct_inputs hE hT hpuv hpuB hpvB hlnpu hlnpv hTpu hvw_pv).1 (fun h => hvw_nr (hstep_n h))
          have huw0 : b0 ∈ Leaves C B_all hu_w :=
            leaf_of_sing0 hu_w huwl huwB huw_noin (huw_nbr 0 (bowtieAdj_symm hadj_0u'))
          have hvw0 : b0 ∈ Leaves C B_all hv_w :=
            leaf_of_sing0 hv_w hvwl hvwB hvw_noin (hvw_nbr 0 (bowtieAdj_symm hadj_0v'))
          have hinc_uv := incomp_of_distinct_inputs hE hT hpuv hpuB hpvB hlnpu hlnpv huw_pu hvw_pv
          have huw_ne_hvw : hu_w ≠ hv_w := fun h => hinc_uv.1 (h ▸ ReflTransGen.refl)
          have huw_notH : hu_w ∉ H := fun h => (incomp_bs_H hu_w huwB huw_bs hu_w h).1 ReflTransGen.refl
          have hvw_notH : hv_w ∉ H := fun h => (incomp_bs_H hv_w hvwB hvw_bs hv_w h).1 ReflTransGen.refl
          -- No `h ∈ H` can contain `b0` in `Leaves C B_all h`!
          have hH_no_b0 : ∀ h ∈ H, b0 ∉ Leaves C B_all h := by
            intro h hh hb0h
            set R3 : Finset ℕ := {hu_w, hv_w, h}
            have hR3_disj : (R3 : Set ℕ).PairwiseDisjoint (fun x => LeafEdges C B_all x) := by
              intro x₁ h1 x₂ h2 hne
              have hx1 : x₁ ∈ R3 := Finset.mem_coe.mp h1
              have hx2 : x₂ ∈ R3 := Finset.mem_coe.mp h2
              simp only [R3, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
              rcases hx1 with rfl | rfl | rfl <;> rcases hx2 with rfl | rfl | rfl
              · exact absurd rfl hne
              · exact leafEdges_disjoint hE hT hinc_uv.1 hinc_uv.2
              · exact leafEdges_disjoint hE hT (incomp_bs_H x₁ huwB huw_bs x₂ hh).1 (incomp_bs_H x₁ huwB huw_bs x₂ hh).2
              · exact leafEdges_disjoint hE hT hinc_uv.2 hinc_uv.1
              · exact absurd rfl hne
              · exact leafEdges_disjoint hE hT (incomp_bs_H x₁ hvwB hvw_bs x₂ hh).1 (incomp_bs_H x₁ hvwB hvw_bs x₂ hh).2
              · exact leafEdges_disjoint hE hT (incomp_bs_H x₂ huwB huw_bs x₁ hh).2 (incomp_bs_H x₂ huwB huw_bs x₁ hh).1
              · exact leafEdges_disjoint hE hT (incomp_bs_H x₂ hvwB hvw_bs x₁ hh).2 (incomp_bs_H x₂ hvwB hvw_bs x₁ hh).1
              · exact absurd rfl hne
            have hle2 := freq_le_two hE hT hR3_disj hb0_mem
            have hfilt : R3.filter (fun x => b0 ∈ Leaves C B_all x) = R3 := by
              ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]
              intro hx; simp only [R3, Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            have hne_uh : hu_w ≠ h := fun e => huw_notH (e ▸ hh)
            have hne_vh : hv_w ≠ h := fun e => hvw_notH (e ▸ hh)
            have hc3 : R3.card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [huw_ne_hvw, hne_uh]),
                  Finset.card_pair hne_vh]
            rw [hfilt, hc3] at hle2; omega
          -- Hence EVERY `h ∈ H` contains `bu ∈ Leaves C B_all h`, contradicting `freq_le_two` on `H` and `3 ≤ H.card`!
          have hH_disj : (H : Set ℕ).PairwiseDisjoint (fun x => LeafEdges C B_all x) := fun x₁ h1 x₂ h2 hne =>
            leafEdges_disjoint hE hT (hH_incomp x₁ h1 x₂ h2 hne) (hH_incomp x₂ h2 x₁ h1 hne.symm)
          have hle2 := freq_le_two hE hT hH_disj hbu_mem
          have hfilt : H.filter (fun h => bu ∈ Leaves C B_all h) = H := by
            ext h; simp only [Finset.mem_filter, and_iff_left_iff_imp]
            intro hh; exact (hH_hit_0u h hh).resolve_left (hH_no_b0 h hh)
          rw [hfilt] at hle2; omega
        · -- `val (sing v') pv = true`! Apply `partner_after_d` to `v' → d → bs`!
          have hdv' : val C (sing v') d = true := by rw [hd_val, hpv_t, Bool.or_true]
          obtain ⟨r, u_after, a_after, hrl, hlnu, hlnr, hru, huB, hdu, _, _, _, hr_nbr, hr_wide, hr_nr, _, hr_to_bs⟩ :=
            partner_after_d hC hE hT hv'd hd_bs hd_bs_all_and hdv' hbs_fv'
          have hrB : r ∉ B_all := fun h => hb_not_wide r h hr_wide
          have hstep_n : ∀ {x y}, Trace C (fun z => z ∉ B_all) x y → ReflTransGen (Next C) x y := by
            intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
          have hr_noin := noin_of_bs r (hr_to_bs hrB)
            (incomp_of_distinct_inputs hE hT hru.symm huB hrB hlnu hlnr (hu'd.trans hdu) ReflTransGen.refl).1
            (fun h => hr_nr (hstep_n h))
          exact kill_with_two_leaves r bv hrB (hr_to_bs hrB) hbv_mem
            (leaf_of_sing0 r hrl hrB hr_noin (hr_nbr 0 (bowtieAdj_symm hadj_0v')))
            (leaf_of_singv r hrl hrB hr_noin (hr_nbr v (bowtieAdj_symm hadj_vv')))
            hH_hit_0v
      · -- `val (sing u') pu = true`! Apply `partner_after_d` to `u' → d → bs`!
        have hdu' : val C (sing u') d = true := by rw [hd_val, hpu_t, Bool.true_or]
        obtain ⟨r, u_after, a_after, hrl, hlnu, hlnr, hru, huB, hdu, _, _, _, hr_nbr, hr_wide, hr_nr, _, hr_to_bs⟩ :=
          partner_after_d hC hE hT hu'd hd_bs hd_bs_all_and hdu' hbs_fu'
        have hrB : r ∉ B_all := fun h => hb_not_wide r h hr_wide
        have hstep_n : ∀ {x y}, Trace C (fun z => z ∉ B_all) x y → ReflTransGen (Next C) x y := by
          intro x y hxy; induction hxy with | refl => exact ReflTransGen.refl | tail _ s ih => exact ih.tail s.2.1
        have hr_noin := noin_of_bs r (hr_to_bs hrB) (fun h => hr_nr (hstep_n h))
          (incomp_of_distinct_inputs hE hT hru.symm huB hrB hlnu hlnr (hv'd.trans hdu) ReflTransGen.refl).1
        exact kill_with_two_leaves r bu hrB (hr_to_bs hrB) hbu_mem
          (leaf_of_sing0 r hrl hrB hr_noin (hr_nbr 0 (bowtieAdj_symm hadj_0u')))
          (leaf_of_singu r hrl hrB hr_noin (hr_nbr u (bowtieAdj_symm hadj_uu')))
          hH_hit_0u
    · -- Subcase 3.2: `u'` hits `bu'`, `v'` avoids `B_all`! Apply `single_inelig_v0_leaf` with `v₀ := v'`!
      obtain ⟨hbu'_0, hbu'_u, hbu'_v⟩ := hit_not_elig u' hu'0 huu'.symm hu'v bu' hbu'_mem hu'b
      obtain ⟨hB_eq4, _, hT⟩ := make_tight4 bu' hbu'_mem hbu'_0 hbu'_u hbu'_v
      let b_ext : Fin 5 → ℕ := fun w =>
        if w = 0 then b0 else if w = u then bu else if w = v then bv else bu'
      have hb_ext_inj : ∀ x y : Fin 5, x ≠ v' → y ≠ v' → b_ext x = b_ext y → x = y := by
        intro x y hxv hyv hxy
        rcases hfive x with rfl | rfl | rfl | rfl | rfl <;> rcases hfive y with rfl | rfl | rfl | rfl | rfl
        all_goals first
          | rfl
          | exact absurd rfl hxv
          | exact absurd rfl hyv
          | (simp only [b_ext, hu0, hu'0, hv0, huu', huv, hu'v, huu'.symm, huv.symm, hu'v.symm, if_true, if_false] at hxy
             first | exact absurd hxy h0u_ne | exact absurd hxy h0u_ne.symm
                   | exact absurd hxy h0v_ne | exact absurd hxy h0v_ne.symm
                   | exact absurd hxy huv_ne | exact absurd hxy huv_ne.symm
                   | exact absurd hxy hbu'_0 | exact absurd hxy hbu'_0.symm
                   | exact absurd hxy hbu'_u | exact absurd hxy hbu'_u.symm
                   | exact absurd hxy hbu'_v | exact absurd hxy hbu'_v.symm)
      have hB_img : B_all = (Finset.univ.erase v').image b_ext := by
        rw [hB_eq4]; ext z
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨0, hv'0.symm, by simp [b_ext]⟩
          · exact ⟨u, huv', by simp [b_ext, hu0]⟩
          · exact ⟨v, hvv', by simp [b_ext, hv0, huv.symm]⟩
          · exact ⟨u', hu'v', by simp [b_ext, hu'0, huu'.symm, hu'v]⟩
        · rintro ⟨w, hwv', rfl⟩
          rcases hfive w with rfl | rfl | rfl | rfl | rfl
          · left; simp [b_ext]
          · right; left; simp [b_ext, hu0]
          · right; right; right; simp [b_ext, hu'0, huu'.symm, hu'v]
          · right; right; left; simp [b_ext, hv0, huv.symm]
          · exact absurd rfl hwv'
      have hb_ext_tr : ∀ w : Fin 5, w ≠ v' → Trace C (fun z => z ∉ B_all) w.val (b_ext w) := by
        intro w hwv'
        rcases hfive w with rfl | rfl | rfl | rfl | rfl
        · simpa [b_ext] using nb_to_notB sb0.2.2.2
        · simpa [b_ext, hu0] using nb_to_notB sbu.2.2.2
        · simpa [b_ext, hu'0, huu'.symm, hu'v] using hu'b
        · simpa [b_ext, hv0, huv.symm] using nb_to_notB sbv.2.2.2
        · exact absurd rfl hwv'
      exact single_inelig_v0_leaf hC hE hT hd_uniq hv'0 hv0 hu0 hu'0 hvv'.symm huv'.symm hu'v'.symm
        huv.symm hu'v.symm huu' hadj_0v' hadj_0v (bowtieAdj_symm hadj_vv') hadj_0u hadj_0u' hadj_uu'
        (fun h => hnadj_uv (bowtieAdj_symm h)) (fun h => hnadj_u'v (bowtieAdj_symm h))
        hb_ext_inj hB_img hb_ext_tr hv'out
  · rcases chain_hit_or_out v' with ⟨bv', hbv'_mem, hv'b⟩ | hv'out
    · -- Subcase 3.3: `v'` hits `bv'`, `u'` avoids `B_all`! Apply `single_inelig_v0_leaf` with `v₀ := u'`!
      obtain ⟨hbv'_0, hbv'_u, hbv'_v⟩ := hit_not_elig v' hv'0 huv'.symm hvv'.symm bv' hbv'_mem hv'b
      obtain ⟨hB_eq4, _, hT⟩ := make_tight4 bv' hbv'_mem hbv'_0 hbv'_u hbv'_v
      let b_ext : Fin 5 → ℕ := fun w =>
        if w = 0 then b0 else if w = u then bu else if w = v then bv else bv'
      have hb_ext_inj : ∀ x y : Fin 5, x ≠ u' → y ≠ u' → b_ext x = b_ext y → x = y := by
        intro x y hxu hyu hxy
        rcases hfive x with rfl | rfl | rfl | rfl | rfl <;> rcases hfive y with rfl | rfl | rfl | rfl | rfl
        all_goals first
          | rfl
          | exact absurd rfl hxu
          | exact absurd rfl hyu
          | (simp only [b_ext, hu0, hv0, hv'0, huv, huv', hvv', huv.symm, huv'.symm, hvv'.symm, if_true, if_false] at hxy
             first | exact absurd hxy h0u_ne | exact absurd hxy h0u_ne.symm
                   | exact absurd hxy h0v_ne | exact absurd hxy h0v_ne.symm
                   | exact absurd hxy huv_ne | exact absurd hxy huv_ne.symm
                   | exact absurd hxy hbv'_0 | exact absurd hxy hbv'_0.symm
                   | exact absurd hxy hbv'_u | exact absurd hxy hbv'_u.symm
                   | exact absurd hxy hbv'_v | exact absurd hxy hbv'_v.symm)
      have hB_img : B_all = (Finset.univ.erase u').image b_ext := by
        rw [hB_eq4]; ext z
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨0, hu'0.symm, by simp [b_ext]⟩
          · exact ⟨u, huu', by simp [b_ext, hu0]⟩
          · exact ⟨v, hu'v.symm, by simp [b_ext, hv0, huv.symm]⟩
          · exact ⟨v', hu'v'.symm, by simp [b_ext, hv'0, huv'.symm, hvv'.symm]⟩
        · rintro ⟨w, hwu', rfl⟩
          rcases hfive w with rfl | rfl | rfl | rfl | rfl
          · left; simp [b_ext]
          · right; left; simp [b_ext, hu0]
          · exact absurd rfl hwu'
          · right; right; left; simp [b_ext, hv0, huv.symm]
          · right; right; right; simp [b_ext, hv'0, huv'.symm, hvv'.symm]
      have hb_ext_tr : ∀ w : Fin 5, w ≠ u' → Trace C (fun z => z ∉ B_all) w.val (b_ext w) := by
        intro w hwu'
        rcases hfive w with rfl | rfl | rfl | rfl | rfl
        · simpa [b_ext] using nb_to_notB sb0.2.2.2
        · simpa [b_ext, hu0] using nb_to_notB sbu.2.2.2
        · exact absurd rfl hwu'
        · simpa [b_ext, hv0, huv.symm] using nb_to_notB sbv.2.2.2
        · simpa [b_ext, hv'0, huv'.symm, hvv'.symm] using hv'b
      exact single_inelig_v0_leaf hC hE hT hd_uniq hu'0 hu0 hv0 hv'0 huu'.symm hu'v hu'v'
        huv huv' hvv' hadj_0u' hadj_0u (bowtieAdj_symm hadj_uu') hadj_0v hadj_0v' hadj_vv'
        hnadj_uv hnadj_uv' hb_ext_inj hB_img hb_ext_tr hu'out
    · -- Subcase 3.1: NEITHER `u'` nor `v'` hits `B_all`! Both reach `C.output` via `Trace (¬ Branch)`!
      obtain ⟨pu, pv, _, _, _, _, _, _, _, _, hd_val, hpu_le, hpv_le, hd_out_anc⟩ :=
        two_chains_meet_at_unique_narrow hC hE hd_uniq hu'v' ReflTransGen.refl (notB_to_nb hu'out) (notB_to_nb hv'out)
      have hdt := andAnc_val_le hd_out_anc (pairIn 0 u) ((bowtie_pair_iff hE 0 u).mpr hadj_0u)
      rw [hd_val, Bool.or_eq_true] at hdt
      rcases hdt with h1 | h2
      · have hu't := hpu_le (pairIn 0 u) h1
        simp only [pairIn, decide_eq_true_eq] at hu't
        rcases hu't with h | h
        · exact hu'0 h
        · exact huu' h.symm
      · have hv't := hpv_le (pairIn 0 u) h2
        simp only [pairIn, decide_eq_true_eq] at hv't
        rcases hv't with h | h
        · exact hv'0 h
        · exact huv' h.symm

/-- Case 2: If there is EXACTLY ONE live narrow OR gate (`liveNarrowOr.card = 1`), then `9 ≤ liveGates.card`. -/
theorem case_one_narrow {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C)
    (hD1 : (liveNarrowOr C).card = 1) : 9 ≤ (liveGates C).card := by
  classical
  by_contra hlt; push Not at hlt
  have hG_le : (liveGates C).card ≤ 8 := by omega
  obtain ⟨dj, hdj_s⟩ := Finset.card_eq_one.mp hD1
  set d := 5 + dj
  have hd_uniq : ∀ z, Live C z → isNarrowOr C z → z = d := by
    intro z hzl hnw
    obtain ⟨p, g, hg, hzp, _⟩ := hnw.1
    have hp_lt : p < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
    have hp_mem : p ∈ liveNarrowOr C :=
      mem_liveNarrowOr.mpr ⟨mem_liveGates.mpr ⟨hp_lt, hzp ▸ hzl⟩, hzp ▸ hnw⟩
    rw [hdj_s, Finset.mem_singleton] at hp_mem
    omega
  set B_all := ((living C).erase C.output).filter (Branch C)
  have hBall_le4 : B_all.card ≤ 4 := by
    have hbud := live_budget_exact hC hE
    have h1 : B_all.card ≤ ∑ a ∈ B_all, (outdeg C a - 1) := by
      calc B_all.card = ∑ _a ∈ B_all, 1 := by simp
        _ ≤ ∑ a ∈ B_all, (outdeg C a - 1) := Finset.sum_le_sum fun a ha => by
            have := (branch_iff_two_le_outdeg hE a).mp (Finset.mem_filter.mp ha).2; omega
    have h2 : ∑ a ∈ B_all, (outdeg C a - 1) ≤ ∑ a ∈ (living C).erase C.output, (outdeg C a - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    omega
  set S : Finset (Fin 5) := Finset.univ.filter (Eligible C)
  have hS_ge3 : 3 ≤ S.card := bowtie_vc_ge3 S (fun u v huv => by
    rcases eligible_covers_edge hC hE huv with hu | hv
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩))
  let b_elig : Fin 5 → ℕ := fun v => if h : Eligible C v then firstBranch C v h else 0
  have hb_mem : ∀ v ∈ S, b_elig v ∈ B_all := by
    intro v hv
    have hev : Eligible C v := (Finset.mem_filter.mp hv).2
    have hsp := firstBranch_spec hC hE hev
    have hne : firstBranch C v hev ≠ C.output := by
      intro h; have := (branch_iff_two_le_outdeg hE _).mp hsp.2.2.1; rw [h, outdeg_output hE] at this; omega
    have hmemB : firstBranch C v hev ∈ B_all :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, (mem_living hE).mpr hsp.1⟩, hsp.2.2.1⟩
    simpa [b_elig, hev] using hmemB
  have hb_injOn : Set.InjOn b_elig S := by
    intro u hu v hv huv
    have heu : Eligible C u := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hev : Eligible C v := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    simp only [b_elig, dite_eq_left, heu, hev] at huv
    exact firstBranch_injective hC hE heu hev huv
  have hS_le4 : S.card ≤ 4 := by
    calc S.card = (S.image b_elig).card := (Finset.card_image_of_injOn hb_injOn).symm
      _ ≤ B_all.card := Finset.card_le_card (Finset.image_subset_iff.mpr hb_mem)
      _ ≤ 4 := hBall_le4
  interval_cases hSc : S.card
  · -- `S.card = 3`: `0 ∈ S`, one of `{1, 2}` in `S`, one of `{3, 4}` in `S`!
    have h0S : (0 : Fin 5) ∈ S := by
      by_contra h0
      have hsub : ({1, 2, 3, 4} : Finset (Fin 5)) ⊆ S := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact (eligible_covers_edge hC hE (u := 0) (v := 1) (by decide)).elim
            (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) h0)
            (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · exact (eligible_covers_edge hC hE (u := 0) (v := 2) (by decide)).elim
            (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) h0)
            (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · exact (eligible_covers_edge hC hE (u := 0) (v := 3) (by decide)).elim
            (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) h0)
            (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · exact (eligible_covers_edge hC hE (u := 0) (v := 4) (by decide)).elim
            (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) h0)
            (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have := Finset.card_le_card hsub; simp at this; omega
    have h12 : Eligible C 1 ∨ Eligible C 2 := eligible_covers_edge hC hE (u := 1) (v := 2) (by decide)
    have h34 : Eligible C 3 ∨ Eligible C 4 := eligible_covers_edge hC hE (u := 3) (v := 4) (by decide)
    have he0 : Eligible C 0 := (Finset.mem_filter.mp h0S).2
    have hnot_both : ∀ a b c : Fin 5, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
        Eligible C a → Eligible C b → Eligible C c → False := by
      intro a b c ha0 hb0 hc0 hab hac hbc hea heb hec
      have hsub : ({0, a, b, c} : Finset (Fin 5)) ⊆ S := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact h0S
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hea⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heb⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hec⟩
      have hc4 : ({0, a, b, c} : Finset (Fin 5)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [ha0.symm, hb0.symm, hc0.symm]),
            Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have := Finset.card_le_card hsub; omega
    rcases h12 with he1 | he2 <;> rcases h34 with he3 | he4
    · exact case_one_narrow_S3 hC hE hd_uniq hG_le (u := 1) (u' := 2) (v := 3) (v' := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        he0 he1 he3
        (fun he2 => hnot_both 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he1 he2 he3)
        (fun he4 => hnot_both 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he1 he3 he4)
    · exact case_one_narrow_S3 hC hE hd_uniq hG_le (u := 1) (u' := 2) (v := 4) (v' := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        he0 he1 he4
        (fun he2 => hnot_both 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he1 he2 he4)
        (fun he3 => hnot_both 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he1 he3 he4)
    · exact case_one_narrow_S3 hC hE hd_uniq hG_le (u := 2) (u' := 1) (v := 3) (v' := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        he0 he2 he3
        (fun he1 => hnot_both 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he1 he2 he3)
        (fun he4 => hnot_both 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he2 he3 he4)
    · exact case_one_narrow_S3 hC hE hd_uniq hG_le (u := 2) (u' := 1) (v := 4) (v' := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        he0 he2 he4
        (fun he1 => hnot_both 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he1 he2 he4)
        (fun he3 => hnot_both 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he2 he3 he4)
  · -- `S.card = 4`: `B_all = S.image b_elig`, `TightCut C B_all`, unique `v₀ ∉ S` avoids `B_all`!
    have hBall_eq : B_all = S.image b_elig :=
      (Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hb_mem) (by
        rw [Finset.card_image_of_injOn hb_injOn, hSc]; omega)).symm
    have hBall_card4 : B_all.card = 4 := by rw [hBall_eq, Finset.card_image_of_injOn hb_injOn, hSc]
    have hT : TightCut C B_all := tightCut_of_le hC hE (Finset.filter_subset _ _)
      (fun z hz => (Finset.mem_filter.mp hz).2) (by omega)
    have hcomp_card : (Finset.univ \ S).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hSc]
    obtain ⟨v₀, hv₀_s⟩ := Finset.card_eq_one.mp hcomp_card
    have hv₀_notS : v₀ ∉ S := (Finset.mem_sdiff.mp (by rw [hv₀_s]; simp)).2
    have hS_eq : S = Finset.univ.erase v₀ := by
      ext w; simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hw h; subst h; exact hv₀_notS hw
      · intro hne; by_contra hw
        have : w ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩
        rw [hv₀_s, Finset.mem_singleton] at this; exact hne this
    have hB_img : B_all = (Finset.univ.erase v₀).image b_elig := by rw [hBall_eq, hS_eq]
    have hb_inj : ∀ x y : Fin 5, x ≠ v₀ → y ≠ v₀ → b_elig x = b_elig y → x = y := fun x y hx hy hxy =>
      hb_injOn (by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
               (by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩) hxy
    have hb_tr : ∀ w : Fin 5, w ≠ v₀ → Trace C (fun z => z ∉ B_all) w.val (b_elig w) := by
      intro w hw
      have hwS : w ∈ S := by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩
      have hew : Eligible C w := (Finset.mem_filter.mp hwS).2
      have hsp := firstBranch_spec hC hE hew
      have nb_to_notB : ∀ {x y}, Trace C (fun z => ¬ Branch C z) x y → Trace C (fun z => z ∉ B_all) x y := by
        intro x y hxy
        induction hxy with
        | refl => exact ReflTransGen.refl
        | tail _ s ih => exact ih.tail ⟨fun h => s.1 (Finset.mem_filter.mp h).2, s.2⟩
      simpa [b_elig, hew] using nb_to_notB hsp.2.2.2
    -- `v₀` cannot hit any wire in `B_all`, hence `Trace (· ∉ B_all) v₀.val C.output`!
    have hv₀_no_B : ∀ z ∈ B_all, ¬ Trace C (fun q => q ∉ B_all) v₀.val z := by
      intro z hz hvz
      rw [hB_img] at hz; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hwv := (Finset.mem_erase.mp hw).1
      have hwS : w ∈ S := by rw [hS_eq]; exact hw
      have hew : Eligible C w := (Finset.mem_filter.mp hwS).2
      have hsp := firstBranch_spec hC hE hew
      have htr_nb := trace_notB_to_nb hE hT hvz
      have hbw_eq : b_elig w = firstBranch C w hew := by simp [b_elig, hew]
      rw [hbw_eq] at htr_nb
      exact hwv (chain_sing_subset hC hE htr_nb hsp.1 hsp.2.1.1)
    have hv₀_out : Trace C (fun q => q ∉ B_all) v₀.val C.output := by
      suffices ∀ k x, x = C.output - k → Live C x → Trace C (fun q => q ∉ B_all) v₀.val x →
          Trace C (fun q => q ∉ B_all) v₀.val C.output from
        this (C.output - v₀.val) v₀.val (by have := live_le_output (input_live hE v₀); omega) (input_live hE v₀) ReflTransGen.refl
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro x hxk hxl hTx
        by_cases hxo : x = C.output
        · exact hxo ▸ hTx
        · have hxB : x ∉ B_all := fun hx => hv₀_no_B x hx hTx
          rcases hxl.cases_head with rfl | ⟨x', hxx', hx'o⟩
          · exact absurd rfl hxo
          · have := live_le_output hx'o; have := hxx'.1
            exact ih (C.output - x') (by omega) x' (by omega) hx'o (hTx.tail ⟨hxB, hxx', hx'o⟩)
    fin_cases v₀
    · exact single_inelig_v0_zero hC hE hT hd_uniq hb_inj hB_img hb_tr hv₀_out
    · exact single_inelig_v0_leaf hC hE hT hd_uniq (v₀ := 1) (v₁ := 2) (a := 3) (c := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hb_inj hB_img hb_tr hv₀_out
    · exact single_inelig_v0_leaf hC hE hT hd_uniq (v₀ := 2) (v₁ := 1) (a := 3) (c := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hb_inj hB_img hb_tr hv₀_out
    · exact single_inelig_v0_leaf hC hE hT hd_uniq (v₀ := 3) (v₁ := 4) (a := 1) (c := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hb_inj hB_img hb_tr hv₀_out
    · exact single_inelig_v0_leaf hC hE hT hd_uniq (v₀ := 4) (v₁ := 3) (a := 1) (c := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hb_inj hB_img hb_tr hv₀_out

/-- Main live bound: `(liveGates C).card + (liveNarrowOr C).card ≥ 10`. -/
theorem main_bound {C : Circuit} (hC : Monotone2 C) (hE : BowtieEval C) :
    10 ≤ (liveGates C).card + (liveNarrowOr C).card := by
  by_cases hD0 : (liveNarrowOr C).card = 0
  · have := case_zero_narrow hC hE hD0; omega
  · by_cases hD1 : (liveNarrowOr C).card = 1
    · have := case_one_narrow hC hE hD1; omega
    · have := eight_live_gates hC hE; omega

end PEqualNP.Outside.L_meta_700_aux

theorem PEqualNP.Outside.L_meta_700 :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 5 → Bool,
        (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 5,
            (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧
            x u = true ∧ x v = true)) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∃ u v : Fin 5, u ≠ v ∧
          (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧
          (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) →
        j ∈ B) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ¬ (∃ u v : Fin 5, u ≠ v ∧
          (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧
          (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) →
        j ∈ D) →
      10 ≤ A.card + B.card + 2 * D.card := by
  intro C A B D hC hE hA hB hD
  have h1 := PEqualNP.Outside.L_meta_700_aux.main_bound hC hE
  have h2 := PEqualNP.Outside.L_meta_700_aux.cost_ge_live hC hA hB hD
  omega
