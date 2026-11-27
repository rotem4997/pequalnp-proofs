import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3893

open PEqualNP.CircuitLowerBounds

def gateVal (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def initWires (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 3]

def w1 (g0 : Gate) (x : Fin 9 → Bool) : List Bool :=
  initWires x ++ [gateVal g0 (initWires x)]

def w2 (g0 g1 : Gate) (x : Fin 9 → Bool) : List Bool :=
  w1 g0 x ++ [gateVal g1 (w1 g0 x)]

lemma wires_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun l g => l ++ [gateVal g l]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_two_getD (g0 g1 : Gate) (rest : List Gate) (x : Fin 9 → Bool)
    (i : ℕ) (hi : i < 12) :
    (({ gates := g0 :: g1 :: rest, output := 0 } : Circuit).wires (initWires x)).getD i false =
      (w2 g0 g1 x).getD i false := by
  have hlen : (w2 g0 g1 x).length = 12 := by simp [w2, w1, initWires]
  simpa [Circuit.wires, w2, w1, gateVal] using wires_preserves rest (w2 g0 g1 x) i (by omega)

def initSupp (i : ℕ) : Finset (Fin 9) :=
  if h : i < 9 then {⟨i, h⟩} else if i = 9 then {0, 3} else ∅

def gateSupp (supp : ℕ → Finset (Fin 9)) (g : Gate) : Finset (Fin 9) :=
  g.inputs.foldr (fun i acc => supp i ∪ acc) ∅

def supp1 (g0 : Gate) (i : ℕ) : Finset (Fin 9) :=
  if i = 10 then gateSupp initSupp g0 else initSupp i

def supp2 (g0 g1 : Gate) (i : ℕ) : Finset (Fin 9) :=
  if i = 11 then gateSupp (supp1 g0) g1 else supp1 g0 i

lemma mem_gateSupp (supp : ℕ → Finset (Fin 9)) (g : Gate) {i : ℕ}
    (hi : i ∈ g.inputs) : supp i ⊆ gateSupp supp g := by
  rcases g with ⟨op, ins⟩
  intro k hk
  dsimp [gateSupp]
  dsimp at hi
  induction ins with
  | nil => cases hi
  | cons a l ih =>
    simp only [List.mem_cons] at hi
    simp only [List.foldr_cons, Finset.mem_union]
    rcases hi with rfl | hl
    · exact Or.inl hk
    · exact Or.inr (ih hl)

lemma list_map_eq {α β : Type} (f g : α → β) (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

lemma gateVal_eq_of_eq (g : Gate) (wA wB : List Bool)
    (h : ∀ i ∈ g.inputs, wA.getD i false = wB.getD i false) :
    gateVal g wA = gateVal g wB := by
  unfold gateVal
  congr 1
  exact list_map_eq _ _ g.inputs h

lemma initWires_eq_of_agree (x y : Fin 9 → Bool) (i : ℕ)
    (h : ∀ k ∈ initSupp i, x k = y k) :
    (initWires x).getD i false = (initWires y).getD i false := by
  by_cases hi : i < 9
  · have hk : (⟨i, hi⟩ : Fin 9) ∈ initSupp i := by simp [initSupp, hi]
    have hxy := h ⟨i, hi⟩ hk
    have hlx : i < (List.ofFn x).length := by simp [hi]
    have hly : i < (List.ofFn y).length := by simp [hi]
    simp only [initWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hlx,
      List.getElem?_append_left hly, List.getElem?_eq_getElem hlx,
      List.getElem?_eq_getElem hly, List.getElem_ofFn, Option.getD_some, hxy]
  · by_cases hi9 : i = 9
    · subst hi9
      have h0 : x 0 = y 0 := h 0 (by simp [initSupp])
      have h3 : x 3 = y 3 := h 3 (by simp [initSupp])
      have hlx : (List.ofFn x).length ≤ 9 := by simp
      have hly : (List.ofFn y).length ≤ 9 := by simp
      simp only [initWires, List.getD_eq_getElem?_getD, List.getElem?_append_right hlx,
        List.getElem?_append_right hly, List.length_ofFn, Nat.sub_self]
      simp [h0, h3]
    · have hxlen : (initWires x).length ≤ i := by simp [initWires]; omega
      have hylen : (initWires y).length ≤ i := by simp [initWires]; omega
      rw [List.getD_eq_default _ _ hxlen, List.getD_eq_default _ _ hylen]

lemma w1_eq_of_agree (g0 : Gate) (x y : Fin 9 → Bool) (i : ℕ)
    (h : ∀ k ∈ supp1 g0 i, x k = y k) :
    (w1 g0 x).getD i false = (w1 g0 y).getD i false := by
  by_cases hi10 : i = 10
  · subst hi10
    have hxlen : (initWires x).length = 10 := by simp [initWires]
    have hylen : (initWires y).length = 10 := by simp [initWires]
    have hg : gateVal g0 (initWires x) = gateVal g0 (initWires y) := by
      apply gateVal_eq_of_eq
      intro j hj
      apply initWires_eq_of_agree
      intro k hk
      apply h k
      have hs : supp1 g0 10 = gateSupp initSupp g0 := by simp [supp1]
      rw [hs]
      exact mem_gateSupp initSupp g0 hj hk
    simp only [w1, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : (initWires x).length ≤ 10),
      List.getElem?_append_right (by omega : (initWires y).length ≤ 10),
      hxlen, hylen, Nat.sub_self]
    simp [hg]
  · have hs : supp1 g0 i = initSupp i := by simp [supp1, hi10]
    rw [hs] at h
    by_cases hi : i < 10
    · have hlx : i < (initWires x).length := by simp [initWires, hi]
      have hly : i < (initWires y).length := by simp [initWires, hi]
      simp only [w1, List.getD_eq_getElem?_getD, List.getElem?_append_left hlx,
        List.getElem?_append_left hly]
      simpa only [List.getD_eq_getElem?_getD] using initWires_eq_of_agree x y i h
    · have hxlen : (w1 g0 x).length ≤ i := by simp [w1, initWires]; omega
      have hylen : (w1 g0 y).length ≤ i := by simp [w1, initWires]; omega
      rw [List.getD_eq_default _ _ hxlen, List.getD_eq_default _ _ hylen]

lemma w2_eq_of_agree (g0 g1 : Gate) (x y : Fin 9 → Bool) (i : ℕ)
    (h : ∀ k ∈ supp2 g0 g1 i, x k = y k) :
    (w2 g0 g1 x).getD i false = (w2 g0 g1 y).getD i false := by
  by_cases hi11 : i = 11
  · subst hi11
    have hxlen : (w1 g0 x).length = 11 := by simp [w1, initWires]
    have hylen : (w1 g0 y).length = 11 := by simp [w1, initWires]
    have hg : gateVal g1 (w1 g0 x) = gateVal g1 (w1 g0 y) := by
      apply gateVal_eq_of_eq
      intro j hj
      apply w1_eq_of_agree
      intro k hk
      apply h k
      have hs : supp2 g0 g1 11 = gateSupp (supp1 g0) g1 := by simp [supp2]
      rw [hs]
      exact mem_gateSupp (supp1 g0) g1 hj hk
    simp only [w2, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : (w1 g0 x).length ≤ 11),
      List.getElem?_append_right (by omega : (w1 g0 y).length ≤ 11),
      hxlen, hylen, Nat.sub_self]
    simp [hg]
  · have hs : supp2 g0 g1 i = supp1 g0 i := by simp [supp2, hi11]
    rw [hs] at h
    by_cases hi : i < 11
    · have hlx : i < (w1 g0 x).length := by simp [w1, initWires, hi]
      have hly : i < (w1 g0 y).length := by simp [w1, initWires, hi]
      simp only [w2, List.getD_eq_getElem?_getD, List.getElem?_append_left hlx,
        List.getElem?_append_left hly]
      simpa only [List.getD_eq_getElem?_getD] using w1_eq_of_agree g0 x y i h
    · have hxlen : (w2 g0 g1 x).length ≤ i := by simp [w2, w1, initWires]; omega
      have hylen : (w2 g0 g1 y).length ≤ i := by simp [w2, w1, initWires]; omega
      rw [List.getD_eq_default _ _ hxlen, List.getD_eq_default _ _ hylen]

lemma initSupp_card_le_one {i : ℕ} (hi : i ≠ 9) : (initSupp i).card ≤ 1 := by
  by_cases h9 : i < 9
  · simp [initSupp, h9]
  · simp [initSupp, h9, hi]

lemma initSupp_nine : initSupp 9 = ({0, 3} : Finset (Fin 9)) := by
  simp [initSupp]

lemma initSupp_card_le_two (i : ℕ) : (initSupp i).card ≤ 2 := by
  by_cases hi : i = 9
  · rw [hi, initSupp_nine]
    exact Finset.card_le_two
  · exact (initSupp_card_le_one hi).trans (by omega)

lemma gateSupp_init_prop (g : Gate) (hg : g.inputs.length ≤ 2) :
    (gateSupp initSupp g).card ≤ 2 ∨
      (({0, 3} : Finset (Fin 9)) ⊆ gateSupp initSupp g ∧ (gateSupp initSupp g).card ≤ 3) := by
  rcases g with ⟨op, ins⟩
  dsimp at hg
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · left; simp [gateSupp]
  · left; simpa [gateSupp] using initSupp_card_le_two a
  · have hgs : gateSupp initSupp ⟨op, [a, b]⟩ = initSupp a ∪ initSupp b := by
      simp [gateSupp]
    rw [hgs]
    by_cases ha : a = 9 <;> by_cases hb : b = 9
    · left; rw [ha, hb, Finset.union_idempotent, initSupp_nine]; exact Finset.card_le_two
    · right
      rw [ha, initSupp_nine]
      refine ⟨Finset.subset_union_left, ?_⟩
      have h1 : ({0, 3} : Finset (Fin 9)).card ≤ 2 := Finset.card_le_two
      have h2 : (initSupp b).card ≤ 1 := initSupp_card_le_one hb
      have hu := Finset.card_union_le ({0, 3} : Finset (Fin 9)) (initSupp b)
      omega
    · right
      rw [hb, initSupp_nine]
      refine ⟨Finset.subset_union_right, ?_⟩
      have h1 : (initSupp a).card ≤ 1 := initSupp_card_le_one ha
      have h2 : ({0, 3} : Finset (Fin 9)).card ≤ 2 := Finset.card_le_two
      have hu := Finset.card_union_le (initSupp a) ({0, 3} : Finset (Fin 9))
      omega
    · left
      have h1 : (initSupp a).card ≤ 1 := initSupp_card_le_one ha
      have h2 : (initSupp b).card ≤ 1 := initSupp_card_le_one hb
      have hu := Finset.card_union_le (initSupp a) (initSupp b)
      omega
  · simp at hg

lemma supp1_card_le_three (g0 : Gate) (hg0 : g0.inputs.length ≤ 2) (i : ℕ) :
    (supp1 g0 i).card ≤ 3 := by
  by_cases hi : i = 10
  · rw [hi]
    simp only [supp1, ↓reduceIte]
    rcases gateSupp_init_prop g0 hg0 with h | h
    · omega
    · exact h.2
  · simp only [supp1, hi, ↓reduceIte]
    exact (initSupp_card_le_two i).trans (by omega)

lemma supp1_ten_union_card_le_four (g0 : Gate) (hg0 : g0.inputs.length ≤ 2) (b : ℕ) :
    (supp1 g0 10 ∪ supp1 g0 b).card ≤ 4 := by
  by_cases hb10 : b = 10
  · rw [hb10, Finset.union_idempotent]
    exact (supp1_card_le_three g0 hg0 10).trans (by omega)
  · simp only [supp1, ↓reduceIte, hb10]
    by_cases hb9 : b = 9
    · rw [hb9, initSupp_nine]
      rcases gateSupp_init_prop g0 hg0 with h | ⟨hsub, hcard⟩
      · have h2 : ({0, 3} : Finset (Fin 9)).card ≤ 2 := Finset.card_le_two
        have hu := Finset.card_union_le (gateSupp initSupp g0) ({0, 3} : Finset (Fin 9))
        omega
      · rw [Finset.union_eq_left.mpr hsub]
        omega
    · have h1 : (initSupp b).card ≤ 1 := initSupp_card_le_one hb9
      have h3 : (gateSupp initSupp g0).card ≤ 3 := by
        simpa [supp1] using supp1_card_le_three g0 hg0 10
      have hu := Finset.card_union_le (gateSupp initSupp g0) (initSupp b)
      omega

lemma supp1_union_card_le_four (g0 : Gate) (hg0 : g0.inputs.length ≤ 2) (a b : ℕ) :
    (supp1 g0 a ∪ supp1 g0 b).card ≤ 4 := by
  by_cases ha : a = 10
  · rw [ha]
    exact supp1_ten_union_card_le_four g0 hg0 b
  · by_cases hb : b = 10
    · rw [hb, Finset.union_comm]
      exact supp1_ten_union_card_le_four g0 hg0 a
    · simp only [supp1, ha, hb, ↓reduceIte]
      have h1 : (initSupp a).card ≤ 2 := initSupp_card_le_two a
      have h2 : (initSupp b).card ≤ 2 := initSupp_card_le_two b
      have hu := Finset.card_union_le (initSupp a) (initSupp b)
      omega

lemma supp2_card_le_four (g0 g1 : Gate) (hg0 : g0.inputs.length ≤ 2)
    (hg1 : g1.inputs.length ≤ 2) (i : ℕ) : (supp2 g0 g1 i).card ≤ 4 := by
  by_cases hi : i = 11
  · subst hi
    simp only [supp2, ↓reduceIte]
    rcases g1 with ⟨op, ins⟩
    dsimp at hg1
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [gateSupp]
    · simpa [gateSupp] using (supp1_card_le_three g0 hg0 a).trans (by omega)
    · simpa [gateSupp] using supp1_union_card_le_four g0 hg0 a b
    · simp at hg1
  · simp only [supp2, hi, ↓reduceIte]
    exact (supp1_card_le_three g0 hg0 i).trans (by omega)

lemma card_fin9 (S : Finset (Fin 9)) :
    S.card =
      (if (0 : Fin 9) ∈ S then 1 else 0) + (if (1 : Fin 9) ∈ S then 1 else 0) +
      (if (2 : Fin 9) ∈ S then 1 else 0) + (if (3 : Fin 9) ∈ S then 1 else 0) +
      (if (4 : Fin 9) ∈ S then 1 else 0) + (if (5 : Fin 9) ∈ S then 1 else 0) +
      (if (6 : Fin 9) ∈ S then 1 else 0) + (if (7 : Fin 9) ∈ S then 1 else 0) +
      (if (8 : Fin 9) ∈ S then 1 else 0) := by
  have hf : S.card = ∑ i ∈ (Finset.univ : Finset (Fin 9)), (if i ∈ S then 1 else 0) := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp
  have hu : (Finset.univ : Finset (Fin 9)) = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by decide
  rw [hf, hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  omega

lemma one_le_of_not_disjoint {S : Finset (Fin 9)} {u v : Fin 9}
    (h : ¬ (u ∉ S ∧ v ∉ S)) :
    1 ≤ (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all

lemma exists_edge_disjoint (S : Finset (Fin 9)) (hS : S.card ≤ 4) :
    ∃ u v : Fin 9, u ∉ S ∧ v ∉ S ∧
      ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3) ∨
       (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 0) ∨ (u = 5 ∧ v = 7) ∨
       (u = 6 ∧ v = 8)) := by
  by_contra h
  have h01 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨0, 1, hu, hv, Or.inl ⟨rfl, rfl⟩⟩)
  have h12 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨1, 2, hu, hv, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
  have h23 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨2, 3, hu, hv, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
  have h34 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨3, 4, hu, hv, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)
  have h40 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨4, 0, hu, hv, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)
  have h57 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨5, 7, hu, hv, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩)
  have h68 := one_le_of_not_disjoint (fun ⟨hu, hv⟩ => h ⟨6, 8, hu, hv, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩)
  have hc := card_fin9 S
  omega

end PEqualNP.Outside.L_meta_3893

theorem PEqualNP.Outside.L_meta_3893 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       ∀ (x4 : ℕ),         have x5 : (Fin (9 : ℕ) → Bool) → ℕ → Bool := fun (x5 : Fin (9 : ℕ) → Bool) (x6 : ℕ) => ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))])).getD x6 Bool.false;         have x6 : (Fin (9 : ℕ) → Bool) → Bool := fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ));         (∀ (x7 : Fin (9 : ℕ) → Bool), x6 x7 = Bool.true → x5 x7 x4 = Bool.true) → (∃ (x8 : Fin (9 : ℕ) → Bool), x5 x8 x4 = Bool.false) → (12 : ℕ) ≤ x4 := by
  intro x1 hlen hfan x4 x5 x6 htrue hfalse
  by_contra hlt
  have hx4 : x4 < 12 := by omega
  rcases x1 with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · have hg0 : g0.inputs.length ≤ 2 := (hfan g0 (by simp)).2
    have hg1 : g1.inputs.length ≤ 2 := (hfan g1 (by simp)).2
    obtain ⟨u, v, hu, hv, hedge⟩ :=
      PEqualNP.Outside.L_meta_3893.exists_edge_disjoint
        (PEqualNP.Outside.L_meta_3893.supp2 g0 g1 x4)
        (PEqualNP.Outside.L_meta_3893.supp2_card_le_four g0 g1 hg0 hg1 x4)
    obtain ⟨y, hy⟩ := hfalse
    let y' : Fin 9 → Bool := fun k => if k = u ∨ k = v then true else y k
    have hagree : ∀ k ∈ PEqualNP.Outside.L_meta_3893.supp2 g0 g1 x4, y' k = y k := by
      intro k hk
      have hku : k ≠ u := fun h => hu (h ▸ hk)
      have hkv : k ≠ v := fun h => hv (h ▸ hk)
      simp [y', hku, hkv]
    have hw_eq : x5 y' x4 = x5 y x4 := by
      change (({ gates := g0 :: g1 :: rest, output := 0 } :
          PEqualNP.CircuitLowerBounds.Circuit).wires
            (PEqualNP.Outside.L_meta_3893.initWires y')).getD x4 false =
        (({ gates := g0 :: g1 :: rest, output := 0 } :
          PEqualNP.CircuitLowerBounds.Circuit).wires
            (PEqualNP.Outside.L_meta_3893.initWires y)).getD x4 false
      rw [PEqualNP.Outside.L_meta_3893.wires_two_getD g0 g1 rest y' x4 hx4,
        PEqualNP.Outside.L_meta_3893.wires_two_getD g0 g1 rest y x4 hx4]
      exact PEqualNP.Outside.L_meta_3893.w2_eq_of_agree g0 g1 y' y x4 hagree
    have hy'f : x5 y' x4 = Bool.false := hw_eq.trans hy
    have hy'u : y' u = Bool.true := by simp [y']
    have hy'v : y' v = Bool.true := by simp [y']
    have hx6 : x6 y' = Bool.true := by
      rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [x6, hy'u, hy'v]
    have hy't : x5 y' x4 = Bool.true := htrue y' hx6
    rw [hy'f] at hy't
    cases hy't
