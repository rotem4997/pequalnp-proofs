import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7722

open PEqualNP.CircuitLowerBounds

theorem getD_append_agree (w1 w2 : List Bool) (b : Bool) (v : ℕ)
    (hl : w1.length = w2.length) (h : ∀ i, i ≠ v → w1.getD i false = w2.getD i false) :
    ∀ i, i ≠ v → (w1 ++ [b]).getD i false = (w2 ++ [b]).getD i false := by
  intro i hi
  by_cases hlt : i < w1.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)]
    exact h i hi
  · push_neg at hlt
    rw [List.getD_append_right _ _ _ _ hlt, List.getD_append_right _ _ _ _ (hl ▸ hlt), hl]

theorem fold_agree (v : ℕ) (gs : List Gate) (hv : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, i ≠ v → w1.getD i false = w2.getD i false) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).length ∧
      ∀ i, i ≠ v →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 hl h; exact ⟨hl, h⟩
  | cons g gs ih =>
    intro w1 w2 hl h
    simp only [List.foldl_cons]
    have hg : v ∉ g.inputs := hv g (by simp)
    have heq : (g.inputs.map fun i => w1.getD i false) = (g.inputs.map fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hg (e ▸ hi))
    rw [heq]
    apply ih (fun g' hg' => hv g' (by simp [hg'])) _ _ (by simp [hl])
    exact getD_append_agree _ _ _ v hl h

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp [h]
  · simp [h]

theorem relevant {x1 : ℕ} (G : SimpleGraph (Fin x1)) [DecidableRel G.Adj] (C : Circuit)
    (hC : ∀ x : Fin x1 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (v u : Fin x1) (hvu : G.Adj v u) :
    v.val = C.output ∨ ∃ g ∈ C.gates, v.val ∈ g.inputs := by
  by_contra hne
  push_neg at hne
  obtain ⟨hout, hin⟩ := hne
  have huv : u ≠ v := by rintro rfl; exact G.irrefl hvu
  let x : Fin x1 → Bool := fun w => decide (w = u ∨ w = v)
  let y : Fin x1 → Bool := fun w => decide (w = u)
  have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, x]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨v, u, hvu, by simp, by simp⟩
  have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, y]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not, decide_eq_true_eq]
    rintro ⟨a, b, hab, ha, hb⟩
    subst ha; subst hb
    exact G.irrefl hab
  have hagree := fold_agree v.val C.gates hin (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i hi
    rw [ofFn_getD, ofFn_getD]
    split_ifs with h
    · simp only [x, y]
      have : (⟨i, h⟩ : Fin x1) ≠ v := fun e => hi (by rw [← e])
      simp [this]
    · rfl)
  have e1 := hC x
  have e2 := hC y
  rw [hx] at e1
  rw [hy] at e2
  have : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
    unfold Circuit.eval Circuit.wires
    exact hagree.2 C.output (fun e => hout e.symm)
  rw [e1, e2] at this
  exact Bool.noConfusion this

end PEqualNP.Outside.L_meta_7722

theorem PEqualNP.Outside.L_meta_7722 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1 → Bool), x4.eval (List.ofFn x5) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ x5) → (∀ x6 ∈ x4.gates, x6.inputs.length ≤ (2 : ℕ)) → ∀ (x7 : Finset (Sym2 (Fin x1))), (∀ x8 ∈ x7, ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x2.degree x10 ≤ (3 : ℕ) ∧ x8 = s(x10, x11)) → x7.card ≤ (3 : ℕ) * ((2 : ℕ) * x4.size + (1 : ℕ)) := by
  classical
  intro n G _ C hC hfan E hE
  let S : Finset ℕ := insert C.output (C.gates.flatMap (fun g => g.inputs)).toFinset
  have hScard : S.card ≤ 2 * C.size + 1 := by
    have h1 : S.card ≤ (C.gates.flatMap (fun g => g.inputs)).toFinset.card + 1 :=
      Finset.card_insert_le _ _
    have h2 : (C.gates.flatMap (fun g => g.inputs)).toFinset.card ≤
        (C.gates.flatMap (fun g => g.inputs)).length := List.toFinset_card_le _
    have h3 : (C.gates.flatMap (fun g => g.inputs)).length ≤ 2 * C.size := by
      rw [List.length_flatMap]
      have := List.sum_le_length_nsmul (C.gates.map fun g => g.inputs.length) 2 (by
        intro a ha
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
        exact hfan g hg)
      simpa [PEqualNP.CircuitLowerBounds.Circuit.size, mul_comm] using this
    omega
  let f : E → Fin n := fun e => (hE e.1 e.2).choose
  have hf : ∀ e : E, ∃ b, G.Adj (f e) b ∧ G.degree (f e) ≤ 3 ∧ e.1 = s(f e, b) :=
    fun e => (hE e.1 e.2).choose_spec
  have hcard : E.attach.card ≤ 3 * (E.attach.image f).card := by
    apply Finset.card_le_mul_card_image
    intro a ha
    have hsub : ((E.attach.filter fun x => f x = a).map (Function.Embedding.subtype _)) ⊆
        G.incidenceFinset a := by
      intro e he
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.subtype_apply] at he
      obtain ⟨e', hfa, rfl⟩ := he
      obtain ⟨b, hab, _, heq⟩ := hf e'
      rw [hfa] at hab heq
      rw [SimpleGraph.mem_incidenceFinset, heq]
      exact ⟨hab, Sym2.mem_mk_left _ _⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_map, SimpleGraph.card_incidenceFinset_eq_degree] at this
    obtain ⟨e0, he0⟩ : ∃ e0 ∈ E.attach, f e0 = a := by
      simpa using ha
    obtain ⟨b, _, hdeg, _⟩ := hf e0
    rw [he0.2] at hdeg
    omega
  have himg : (E.attach.image f).card ≤ S.card := by
    have : ((E.attach.image f).map Fin.valEmbedding) ⊆ S := by
      intro k hk
      simp only [Finset.mem_map, Finset.mem_image, Finset.mem_attach, true_and,
        Fin.valEmbedding_apply] at hk
      obtain ⟨a, ⟨e, rfl⟩, rfl⟩ := hk
      obtain ⟨b, hab, _, _⟩ := hf e
      rcases L_meta_7722.relevant G C hC (f e) b hab with h | ⟨g, hg, hi⟩
      · simp [S, h]
      · simp only [S, Finset.mem_insert, List.mem_toFinset, List.mem_flatMap]
        exact Or.inr ⟨g, hg, hi⟩
    have := Finset.card_le_card this
    rwa [Finset.card_map] at this
  rw [Finset.card_attach] at hcard
  calc E.card ≤ 3 * (E.attach.image f).card := hcard
    _ ≤ 3 * (2 * C.size + 1) := by
      have := le_trans himg hScard
      omega
