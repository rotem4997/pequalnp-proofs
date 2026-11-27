import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def gsupp (L : List (Finset ℕ)) (g : Gate) : Finset ℕ :=
  (eff g).toFinset.biUnion fun a => L.getD a ∅

def supps (gs : List Gate) (L : List (Finset ℕ)) : List (Finset ℕ) :=
  gs.foldl (fun L g => L ++ [gsupp L g]) L

theorem supps_cons (g : Gate) (gs : List Gate) (L : List (Finset ℕ)) :
    supps (g :: gs) L = supps gs (L ++ [gsupp L g]) := rfl

theorem fs_lt (L : List (Finset ℕ)) (S : Finset ℕ) (k : ℕ) (h : k < L.length) :
    (L ++ [S]).getD k ∅ = L.getD k ∅ := List.getD_append _ _ _ _ h

theorem fs_eq (L : List (Finset ℕ)) (S : Finset ℕ) : (L ++ [S]).getD L.length ∅ = S := by simp

theorem fs_ne (L : List (Finset ℕ)) (S : Finset ℕ) (k : ℕ) (h : k ≠ L.length) :
    (L ++ [S]).getD k ∅ = L.getD k ∅ := by
  by_cases hk : k < L.length
  · exact fs_lt L S k hk
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem eval_congr (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (f f' : ℕ → Bool) (h : ∀ a ∈ eff g, f a = f' a) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rcases g with ⟨op, ins⟩
  rcases hop with h' | h' | h'
  · simp only at h'; subst h'
    congr 1
    exact List.map_congr_left (fun a ha => h a ha)
  · simp only at h'; subst h'
    congr 1
    exact List.map_congr_left (fun a ha => h a ha)
  · simp only at h'; subst h'
    cases ins with
    | nil => rfl
    | cons a t =>
      show (!(f a)) = !(f' a)
      rw [h a (by simp [eff])]

theorem eff_card (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    (eff g).toFinset.card ≤ (if (!g.op.eval [false]) = true then 1 else 0) + 1 := by
  rcases g with ⟨op, ins⟩
  refine le_trans (List.toFinset_card_le _) ?_
  rcases hop with h' | h' | h'
  · simp only at h'; subst h'
    simpa [eff, GateOp.eval] using hlen
  · simp only at h'; subst h'
    simpa [eff, GateOp.eval] using hlen
  · simp only at h'; subst h'
    simp [eff, GateOp.eval]

def Cnt (t : ℕ) (L : List (Finset ℕ)) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_step (t c : ℕ) (L : List (Finset ℕ)) (g : Gate) (hg : (eff g).toFinset.card ≤ c + 1)
    (h : Cnt t L) : Cnt (t + c) (L ++ [gsupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gsupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (eff g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [fs_eq] at hij
        obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hij
        exact ⟨a, Finset.mem_union_right _ ha, hia⟩
      · rw [fs_ne _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ (eff g).toFinset).card ≤ (W.card - 1) + (c + 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left hg _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ (eff g).toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gsupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact fs_ne _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_supps (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset ℕ)),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    Cnt t L → Cnt (t + gs.countP (fun g => !g.op.eval [false])) (supps gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    obtain ⟨hop, hlen⟩ := hok g (by simp)
    have := ih (t + (if (!g.op.eval [false]) = true then 1 else 0)) (L ++ [gsupp L g])
      (fun g' hg' => hok g' (by simp [hg'])) (cnt_step t _ L g (eff_card g hop hlen) h)
    rw [supps_cons, List.countP_cons]
    have e : t + (List.countP (fun g => !g.op.eval [false]) gs + if (!g.op.eval [false]) = true then 1 else 0)
        = t + (if (!g.op.eval [false]) = true then 1 else 0) + List.countP (fun g => !g.op.eval [false]) gs := by omega
    rw [e]
    exact this

theorem agree (x y : List Bool) (gs : List Gate) :
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ (L : List (Finset ℕ)) (w w' : List Bool), w.length = L.length → w'.length = L.length →
    (∀ k, (∀ i ∈ L.getD k ∅, x.getD i false = y.getD i false) → w.getD k false = w'.getD k false) →
    ∀ k, (∀ i ∈ (supps gs L).getD k ∅, x.getD i false = y.getD i false) →
      (wf gs w).getD k false = (wf gs w').getD k false := by
  induction gs with
  | nil => intro _ L w w' _ _ h k hk; exact h k hk
  | cons g gs ih =>
    intro hok L w w' hl hl' h k hk
    rw [supps_cons] at hk
    rw [wf_cons, wf_cons]
    refine ih (fun g' hg' => hok g' (by simp [hg'])) (L ++ [gsupp L g]) _ _ (by simp [hl]) (by simp [hl']) ?_ k hk
    intro j hj
    rcases Nat.lt_trichotomy j L.length with hlt | heq | hgt
    · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
      exact h j (by rw [fs_lt _ _ _ hlt] at hj; exact hj)
    · subst heq
      rw [fs_eq] at hj
      have e1 := getD_snoc_eq w (g.op.eval (g.inputs.map fun i => w.getD i false))
      have e2 := getD_snoc_eq w' (g.op.eval (g.inputs.map fun i => w'.getD i false))
      rw [hl] at e1
      rw [hl'] at e2
      rw [e1, e2]
      refine eval_congr g (hok g (by simp)).1 _ _ ?_
      intro a ha
      refine h a (fun i hi => hj i ?_)
      exact Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hi⟩
    · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_3266

open PEqualNP.Outside.L_meta_3266 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C hC
  have hc0 : Cnt 0 ((List.range n).map fun i => ({i} : Finset ℕ)) := by
    intro W
    refine le_trans Finset.card_biUnion_le ?_
    rw [zero_add, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro j _
    by_cases hjn : j < n
    · simp [List.getD_eq_getElem?_getD, hjn]
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
  refine ⟨(supps C.gates ((List.range n).map fun i => ({i} : Finset ℕ))).getD C.output ∅, ?_, ?_⟩
  · have := cnt_supps C.gates 0 _ hC hc0 {C.output}
    simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at this
    exact this
  · intro x y hx hy hxy
    show (wf C.gates x).getD C.output false = (wf C.gates y).getD C.output false
    refine agree x y C.gates hC _ x y (by simp [hx]) (by simp [hy]) ?_ C.output hxy
    intro k hk
    by_cases hkn : k < n
    · exact hk k (by simp [List.getD_eq_getElem?_getD, hkn])
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
