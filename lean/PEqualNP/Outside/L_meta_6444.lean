import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6444

open PEqualNP.CircuitLowerBounds

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem getD_append_singleton {α : Type*} (l : List α) (a d : α) (w : ℕ) :
    (l ++ [a]).getD w d = if w < l.length then l.getD w d else if w = l.length then a else d := by
  by_cases h1 : w < l.length
  · simp only [h1, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h1,
      ← List.getD_eq_getElem _ _ h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : w = l.length
    · subst h2
      simp only [↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp
    · simp only [h2, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by simp; omega)]

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ rest, gs.foldl F w = w ++ rest := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (F w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ r, ?_⟩
    rw [List.foldl_cons, hr]
    simp [F]

theorem fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  obtain ⟨r, hr⟩ := fold_prefix gs w
  rw [hr, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hi,
    ← List.getD_eq_getElem _ _ hi]

theorem gate_agree (g : Gate) (v : ℕ) (Sv : ℕ → Prop)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hbad : v ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
      g.op = GateOp.or ∧ ∃ s, Sv s ∧ s ∈ g.inputs)
    (w w' : List Bool)
    (hS : ∀ s, Sv s → w.getD s false = true ∧ w'.getD s false = true)
    (hag : ∀ i, i ≠ v → w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hfan
  simp only at hop hlen hbad ⊢
  by_cases hv : v ∈ List.take (bif op.eval [false] then 1 else 2) ins
  · obtain ⟨rfl, s, hs, hsin⟩ := hbad hv
    have h1 := (hS s hs).1
    have h2 := (hS s hs).2
    simp only [GateOp.eval]
    rw [List.any_eq_true.mpr ⟨w.getD s false, List.mem_map.mpr ⟨s, hsin, rfl⟩, by simpa using h1⟩,
      List.any_eq_true.mpr ⟨w'.getD s false, List.mem_map.mpr ⟨s, hsin, rfl⟩, by simpa using h2⟩]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hk : (bif GateOp.and.eval [false] then 1 else 2) = 2 := by decide
      rw [hk, List.take_of_length_le hlen] at hv
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun h => hv (h ▸ hi))
    · have hk : (bif GateOp.or.eval [false] then 1 else 2) = 2 := by decide
      rw [hk, List.take_of_length_le hlen] at hv
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun h => hv (h ▸ hi))
    · have hk : (bif GateOp.not.eval [false] then 1 else 2) = 1 := by decide
      rw [hk] at hv
      cases ins with
      | nil => simp [GateOp.eval]
      | cons j t =>
        have hj : j ≠ v := fun h => hv (by simp [h])
        simp only [GateOp.eval, List.map_cons, List.headD_cons, hag j hj]

theorem wires_agree (gs : List Gate) (v : ℕ) (Sv : ℕ → Prop)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hbad : ∀ g ∈ gs, v ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
      g.op = GateOp.or ∧ ∃ s, Sv s ∧ s ∈ g.inputs)
    (w w' : List Bool) (hlen : w.length = w'.length)
    (hS : ∀ s, Sv s → w.getD s false = true ∧ w'.getD s false = true)
    (hag : ∀ i, i ≠ v → w.getD i false = w'.getD i false) :
    ∀ i, i ≠ v → (gs.foldl F w).getD i false = (gs.foldl F w').getD i false := by
  induction gs generalizing w w' with
  | nil => simpa using hag
  | cons g gs ih =>
    have hga := gate_agree g v Sv (hfan g (by simp)) (hbad g (by simp)) w w' hS hag
    simp only [List.foldl_cons]
    apply ih (fun g' h => hfan g' (by simp [h])) (fun g' h => hbad g' (by simp [h]))
    · simp [F, hlen]
    · intro s hs
      have h1 := (hS s hs).1
      have h2 := (hS s hs).2
      have hs1 : s < w.length := by
        by_contra hc
        rw [List.getD_eq_default _ _ (by omega)] at h1
        exact Bool.false_ne_true h1
      have hs2 : s < w'.length := by omega
      simp only [F, getD_append_singleton, hs1, hs2, ↓reduceIte]
      exact ⟨h1, h2⟩
    · intro i hi
      simp only [F, getD_append_singleton, hlen, hga]
      split_ifs
      · rw [← hlen] at *
        exact hag i hi
      · rfl
      · rfl

theorem find_T {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (hA : ∀ a b : Fin n, G.Adj a b → a ∉ A) (hNF : PEqualNP.TopForm.NoFourCycle G)
    (v : Fin n) (S : Finset (Fin n)) (hvS : v ∉ S) (hdisj : Disjoint A S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) (hcard : S.card < (G.neighborFinset v).card) :
    ∃ T : Finset (Fin n), v ∉ T ∧ S ⊆ T ∧ (∀ t ∈ T, t ∉ A) ∧
      (∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b) ∧ ∃ t ∈ T, G.Adj v t := by
  by_cases hN : ∃ s ∈ S, G.Adj v s
  · refine ⟨S, hvS, subset_refl _, ?_, hind, hN⟩
    intro t ht htA
    exact Finset.disjoint_left.mp hdisj htA ht
  · push_neg at hN
    have hy : ∃ y ∈ G.neighborFinset v, ∀ s ∈ S, ¬ G.Adj y s := by
      by_contra hc
      push_neg at hc
      choose f hfS hfA using hc
      have hinj : (G.neighborFinset v).card ≤ S.card := by
        apply Finset.card_le_card_of_injOn (fun y => if h : y ∈ G.neighborFinset v then f y h else v)
        · intro y hy
          simp only [Finset.mem_coe] at hy ⊢
          rw [dif_pos hy]
          exact hfS y hy
        · intro y1 hy1 y2 hy2 he
          simp only [Finset.mem_coe] at hy1 hy2
          simp only [dif_pos hy1, dif_pos hy2] at he
          by_contra hne
          have hs := hfS y1 hy1
          have hsv : f y1 hy1 ≠ v := fun h => hvS (h ▸ hs)
          have hc := hNF (f y1 hy1) v hsv
          have h2 : ({y1, y2} : Finset (Fin n)) ⊆
              Finset.univ.filter (fun w => G.Adj (f y1 hy1) w ∧ G.Adj v w) := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hw with rfl | rfl
            · exact ⟨(hfA _ hy1).symm, (G.mem_neighborFinset _ _).mp hy1⟩
            · exact ⟨he ▸ (hfA _ hy2).symm, (G.mem_neighborFinset _ _).mp hy2⟩
          have h3 := Finset.card_le_card h2
          rw [Finset.card_pair hne] at h3
          omega
      omega
    obtain ⟨y, hyN, hyS⟩ := hy
    have hvy : G.Adj v y := (G.mem_neighborFinset _ _).mp hyN
    have hyS' : y ∉ S := fun h => hN y h hvy
    refine ⟨insert y S, ?_, Finset.subset_insert _ _, ?_, ?_, y, by simp, hvy⟩
    · simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => G.irrefl (h ▸ hvy), hvS⟩
    · intro t ht htA
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hA t v hvy.symm htA
      · exact Finset.disjoint_left.mp hdisj htA ht
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with h1 | h1 <;>
        rcases Finset.mem_insert.mp hb with h2 | h2
      · subst h1; subst h2; exact G.irrefl hab
      · subst h1; exact hyS b h2 hab
      · subst h2; exact hyS a h1 hab.symm
      · exact hind a h1 b h2 hab

end PEqualNP.Outside.L_meta_6444

theorem PEqualNP.Outside.L_meta_6444 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ x10 ∉ x4, ∀ (x12 : Finset (Fin x1)), x10 ∉ x12 → Disjoint x4 x12 → (∀ x15 ∈ x12, ∀ x17 ∈ x12, ¬x2.Adj x15 x17) → x12.card < (x2.neighborFinset x10).card → ∃ x17 ∈ x5.gates, ↑x10 ∈ List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs ∧ (x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ x18 ∈ x12, ↑x18 ∉ x17.inputs) := by
  intro n G _ A C hfan hfun hA hNF v hvA S hvS hdisj hind hcard
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hvT, hST, hTA, hTind, t, htT, hvt⟩ := PEqualNP.Outside.L_meta_6444.find_T G A hA hNF v S hvS hdisj hind hcard
  have hW : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G A x := fun x => congrFun hfun x
  have hwires : ∀ x : List Bool, C.wires x = C.gates.foldl PEqualNP.Outside.L_meta_6444.F x := fun x => rfl
  -- the output wire is not the input v
  have hout : C.output ≠ (v : ℕ) := by
    intro ho
    have h1 := hW (fun i => decide (i = v))
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun G A (fun i => decide (i = v)) = false := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
      refine ⟨fun a ha hav => hvA (hav ▸ ha), fun a b hab ha hb => G.irrefl (v := v) (by
        rw [ha, hb] at hab; exact hab)⟩
    rw [h2] at h1
    have h3 : C.eval (List.ofFn (fun i => decide (i = v))) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [hwires, ho, PEqualNP.Outside.L_meta_6444.fold_keep _ _ _ (by simp), PEqualNP.Outside.L_meta_6444.ofFn_getD]
      simp
    rw [h3] at h1
    exact absurd h1 (by decide)
  set x0 : Fin n → Bool := fun i => decide (i ∈ T) with hx0
  set x1 : Fin n → Bool := fun i => decide (i ∈ T ∨ i = v) with hx1
  have hf0 : PEqualNP.MetaComplexity.NestedCover.graphFun G A x0 = false := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, hx0, Bool.or_eq_false_iff,
      decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
    exact ⟨fun a ha haT => hTA a haT ha, fun a b hab ha hb => hTind a ha b hb hab⟩
  have hf1 : PEqualNP.MetaComplexity.NestedCover.graphFun G A x1 = true := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, hx1, Bool.or_eq_true,
      decide_eq_true_eq]
    exact Or.inr ⟨v, t, hvt, Or.inr rfl, Or.inl htT⟩
  have hagree := PEqualNP.Outside.L_meta_6444.wires_agree C.gates (v : ℕ) (fun s => ∃ u ∈ S, (u : ℕ) = s) hfan
    (fun g hg hv => by
      obtain ⟨h1, u, hu, hu2⟩ := hcon g hg hv
      exact ⟨h1, u, ⟨u, hu, rfl⟩, hu2⟩)
    (List.ofFn x0) (List.ofFn x1) (by simp)
    (by
      rintro s ⟨u, hu, rfl⟩
      simp only [PEqualNP.Outside.L_meta_6444.ofFn_getD, u.isLt, ↓reduceDIte, Fin.eta, hx0, hx1, decide_eq_true_eq]
      exact ⟨hST hu, Or.inl (hST hu)⟩)
    (by
      intro i hi
      simp only [PEqualNP.Outside.L_meta_6444.ofFn_getD, hx0, hx1]
      split_ifs with h
      · have : (⟨i, h⟩ : Fin n) ≠ v := fun e => hi (by rw [← e])
        simp [this]
      · rfl)
    C.output hout
  have e0 := hW x0
  have e1 := hW x1
  rw [hf0] at e0
  rw [hf1] at e1
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval at e0 e1
  rw [hwires] at e0 e1
  rw [hagree, e1] at e0
  exact absurd e0 (by decide)
