import Mathlib
import PEqualNP.Defs

-- A circuit with at most one gate, fed the ten inputs, the wire x0 AND x2, and an AND of at most
-- two of those wires, depends on at most five named wires and the two inputs 0 and 2. Some input
-- v outside them is free; adding v next to a neighbour changes the Petersen edge function but
-- not the circuit output.
namespace PEqualNP.Outside.L_meta_7989
open PEqualNP.CircuitLowerBounds

def F (x9 : Fin 10 → Bool) : Bool :=
  (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)))

def W (y : Fin 10 → Bool) : List Bool :=
  List.ofFn y ++ [y (0 : Fin (10 : ℕ)) && y (2 : Fin (10 : ℕ))]

def L (x2 : List (Fin 12)) (y : Fin 10 → Bool) : List Bool :=
  W y ++ [GateOp.and.eval (List.map (fun (x9 : Fin (12 : ℕ)) => (W y).getD (↑x9) Bool.false) x2)]

def nb (v : ℕ) : ℕ := [1, 0, 1, 2, 3, 0, 1, 2, 3, 4].getD v 0

def sgl (w : ℕ) : Fin 10 → Bool := fun k => decide (k.val = w)

def pr (w v : ℕ) : Fin 10 → Bool := fun k => decide (k.val = w ∨ k.val = v)

theorem F_sgl : ∀ v : Fin 10, F (sgl (nb v.val)) = false := by decide

theorem F_pr : ∀ v : Fin 10, F (pr (nb v.val) v.val) = true := by decide

theorem agree_sp (v : ℕ) : ∀ k : Fin 10, k.val ≠ v → sgl (nb v) k = pr (nb v) v k := by
  intro k hk
  simp [sgl, pr, hk]

theorem getD_ofFn (x : Fin 10 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem app_agree (l l' : List Bool) (a : Bool) (hl : l.length = l'.length) (v : ℕ)
    (h : ∀ i, i ≠ v → l.getD i false = l'.getD i false) :
    ∀ i, i ≠ v → (l ++ [a]).getD i false = (l' ++ [a]).getD i false := by
  intro i hi
  by_cases hi' : i < l.length
  · rw [List.getD_append _ _ _ _ hi', List.getD_append _ _ _ _ (hl ▸ hi')]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

theorem W_agree (v : ℕ) (hv0 : v ≠ 0) (hv2 : v ≠ 2) (y y' : Fin 10 → Bool)
    (h : ∀ k : Fin 10, k.val ≠ v → y k = y' k) :
    ∀ i, i ≠ v → (W y).getD i false = (W y').getD i false := by
  have h0 : y (0 : Fin 10) = y' (0 : Fin 10) := h 0 (fun e => hv0 (by rw [← e]; rfl))
  have h2 : y (2 : Fin 10) = y' (2 : Fin 10) := h 2 (fun e => hv2 (by rw [← e]; rfl))
  unfold W
  rw [h0, h2]
  apply app_agree _ _ _ (by simp) v
  intro i hi
  rw [getD_ofFn, getD_ofFn]
  split_ifs with hi10
  · exact h ⟨i, hi10⟩ hi
  · rfl

theorem L_agree (x2 : List (Fin 12)) (v : ℕ) (hv0 : v ≠ 0) (hv2 : v ≠ 2)
    (hx2 : ∀ j ∈ x2, j.val ≠ v) (y y' : Fin 10 → Bool)
    (h : ∀ k : Fin 10, k.val ≠ v → y k = y' k) :
    ∀ i, i ≠ v → (L x2 y).getD i false = (L x2 y').getD i false := by
  have hW := W_agree v hv0 hv2 y y' h
  have hA : GateOp.and.eval (List.map (fun (x9 : Fin 12) => (W y).getD (↑x9) false) x2) =
      GateOp.and.eval (List.map (fun (x9 : Fin 12) => (W y').getD (↑x9) false) x2) := by
    congr 1
    apply List.map_congr_left
    intro j hj
    exact hW j.val (hx2 j hj)
  unfold L
  rw [hA]
  exact app_agree (W y) (W y') _ (by simp [W]) v hW

theorem L_length (x2 : List (Fin 12)) (y : Fin 10 → Bool) : (L x2 y).length = 12 := by
  simp [L, W]

theorem pick (l : List ℕ) (hl : l.length ≤ 5) :
    ∃ v : Fin 10, v.val ≠ 0 ∧ v.val ≠ 2 ∧ v.val ∉ l := by
  by_contra hc
  push_neg at hc
  have hsub : ({1, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hx' : x < 10 ∧ x ≠ 0 ∧ x ≠ 2 := by omega
    exact List.mem_toFinset.2 (hc ⟨x, hx'.1⟩ hx'.2.1 hx'.2.2)
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le l
  have h3 : ({1, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ).card = 8 := by decide
  omega

end PEqualNP.Outside.L_meta_7989

theorem PEqualNP.Outside.L_meta_7989 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         x1.gates[(1 : ℕ)]? = Option.none →           ∃ (x7 : Fin (10 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ))];             x1.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (12 : ℕ)) => x8.getD (↑x9) Bool.false) x2)]) ≠ (fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) x7 := by
  intro C x2 hfan _ hlen2 hnone
  by_contra hall
  have hF : ∀ y : Fin 10 → Bool,
      C.eval (PEqualNP.Outside.L_meta_7989.L x2 y) = PEqualNP.Outside.L_meta_7989.F y := by
    intro y
    by_contra hne
    exact hall ⟨y, hne⟩
  obtain ⟨gs, o⟩ := C
  have hlen : gs.length ≤ 1 := by
    have h : gs[1]? = none := hnone
    rw [List.getElem?_eq_none_iff] at h
    omega
  match gs, hlen with
  | [], _ =>
    have hE : ∀ y : Fin 10 → Bool, (PEqualNP.Outside.L_meta_7989.L x2 y).getD o false =
        PEqualNP.Outside.L_meta_7989.F y := fun y => hF y
    obtain ⟨v, hv0, hv2, hvl⟩ := PEqualNP.Outside.L_meta_7989.pick
      (x2.map (fun j => j.val) ++ [o]) (by simp; omega)
    have hx2 : ∀ j ∈ x2, j.val ≠ v.val :=
      fun j hj e => hvl (List.mem_append_left _ (List.mem_map.2 ⟨j, hj, e⟩))
    have ho : o ≠ v.val := fun e => hvl (List.mem_append_right _ (by simp [e]))
    have hag := PEqualNP.Outside.L_meta_7989.L_agree x2 v.val hv0 hv2 hx2 _ _
      (PEqualNP.Outside.L_meta_7989.agree_sp v.val)
    have h1 := hE (PEqualNP.Outside.L_meta_7989.sgl (PEqualNP.Outside.L_meta_7989.nb v.val))
    have h2 := hE (PEqualNP.Outside.L_meta_7989.pr (PEqualNP.Outside.L_meta_7989.nb v.val) v.val)
    rw [hag o ho, PEqualNP.Outside.L_meta_7989.F_sgl v] at h1
    rw [h1, PEqualNP.Outside.L_meta_7989.F_pr v] at h2
    exact Bool.noConfusion h2
  | [g], _ =>
    have hE : ∀ y : Fin 10 → Bool, (PEqualNP.Outside.L_meta_7989.L x2 y ++
        [g.op.eval (g.inputs.map fun i => (PEqualNP.Outside.L_meta_7989.L x2 y).getD i false)]).getD
          o false = PEqualNP.Outside.L_meta_7989.F y := fun y => hF y
    have hg := (hfan g (by simp)).2
    obtain ⟨v, hv0, hv2, hvl⟩ := PEqualNP.Outside.L_meta_7989.pick
      (x2.map (fun j => j.val) ++ g.inputs ++ [o]) (by simp; omega)
    have hx2 : ∀ j ∈ x2, j.val ≠ v.val := fun j hj e =>
      hvl (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨j, hj, e⟩)))
    have hgi : ∀ i ∈ g.inputs, i ≠ v.val := fun i hi e =>
      hvl (List.mem_append_left _ (List.mem_append_right _ (e ▸ hi)))
    have ho : o ≠ v.val := fun e => hvl (List.mem_append_right _ (by simp [e]))
    have hag := PEqualNP.Outside.L_meta_7989.L_agree x2 v.val hv0 hv2 hx2 _ _
      (PEqualNP.Outside.L_meta_7989.agree_sp v.val)
    have hgate : g.op.eval (g.inputs.map fun i => (PEqualNP.Outside.L_meta_7989.L x2
        (PEqualNP.Outside.L_meta_7989.sgl (PEqualNP.Outside.L_meta_7989.nb v.val))).getD i false) =
        g.op.eval (g.inputs.map fun i => (PEqualNP.Outside.L_meta_7989.L x2
        (PEqualNP.Outside.L_meta_7989.pr (PEqualNP.Outside.L_meta_7989.nb v.val) v.val)).getD i
          false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (hgi i hi)
    have h1 := hE (PEqualNP.Outside.L_meta_7989.sgl (PEqualNP.Outside.L_meta_7989.nb v.val))
    have h2 := hE (PEqualNP.Outside.L_meta_7989.pr (PEqualNP.Outside.L_meta_7989.nb v.val) v.val)
    rw [hgate, PEqualNP.Outside.L_meta_7989.app_agree _ _ _
      (by rw [PEqualNP.Outside.L_meta_7989.L_length, PEqualNP.Outside.L_meta_7989.L_length])
      v.val hag o ho, PEqualNP.Outside.L_meta_7989.F_sgl v] at h1
    rw [h1, PEqualNP.Outside.L_meta_7989.F_pr v] at h2
    exact Bool.noConfusion h2
