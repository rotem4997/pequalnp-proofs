import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19361_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- Only the wires of a set of at most `|R| + |gs|` wires decide the wires in `R`. -/
theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

end PEqualNP.Outside.L_meta_19361_aux

open PEqualNP.Outside.L_meta_19361_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19361 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  0 < n → 0 < m → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  ∃ (u0 : Fin n) (v0 : Fin m),
    (n - (Finset.univ.filter (fun u : Fin n => ∀ v : Fin m, A u v = A u0 v)).card) +
    (m - (Finset.univ.filter (fun v : Fin m => ∀ u : Fin n, A u v = A u v0)).card) ≤ C.size + 1 := by
  intro n m A C hn hm hF hR
  obtain ⟨R', hc, hR'⟩ := cone (n + m) C.gates (fun g hg => (hF g hg).2) {C.output}
  rw [Finset.card_singleton] at hc
  have key : ∀ (u u' : Fin n) (v v' : Fin m), (∀ i ∈ R', ((oneEach u v).getD i false = true ↔
      (oneEach u' v').getD i false = true)) → A u v = A u' v' := by
    intro u u' v v' h
    have e1 := hR u v
    have e2 := hR u' v'
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [← e1, ← e2]
    exact hR' _ _ (by simp [oneEach]) (by simp [oneEach])
      (fun i hi => Bool.eq_iff_iff.2 (h i hi)) _ (Finset.mem_singleton_self _)
  let Fr := Finset.univ.filter (fun u : Fin n => ¬ u.val ∈ R')
  let Fc := Finset.univ.filter (fun v : Fin m => ¬ n + v.val ∈ R')
  have hr : ∃ u0 : Fin n, Fr.card ≤
      (Finset.univ.filter (fun u : Fin n => ∀ v : Fin m, A u v = A u0 v)).card := by
    by_cases h : Fr.Nonempty
    · obtain ⟨u0, hu0⟩ := h
      refine ⟨u0, Finset.card_le_card fun u hu => ?_⟩
      simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu0 ⊢
      intro v
      refine key _ _ v v fun i hi => ?_
      have : i ≠ u.val := fun e => hu (e ▸ hi)
      have : i ≠ u0.val := fun e => hu0 (e ▸ hi)
      simp only [oe]
      constructor <;> intro h <;> omega
    · exact ⟨⟨0, hn⟩, by rw [Finset.not_nonempty_iff_eq_empty.1 h]; simp⟩
  have hl : ∃ v0 : Fin m, Fc.card ≤
      (Finset.univ.filter (fun v : Fin m => ∀ u : Fin n, A u v = A u v0)).card := by
    by_cases h : Fc.Nonempty
    · obtain ⟨v0, hv0⟩ := h
      refine ⟨v0, Finset.card_le_card fun v hv => ?_⟩
      simp only [Fc, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv0 ⊢
      intro u
      refine key u u _ _ fun i hi => ?_
      have : i ≠ n + v.val := fun e => hv (e ▸ hi)
      have : i ≠ n + v0.val := fun e => hv0 (e ▸ hi)
      simp only [oe]
      constructor <;> intro h <;> omega
    · exact ⟨⟨0, hm⟩, by rw [Finset.not_nonempty_iff_eq_empty.1 h]; simp⟩
  obtain ⟨u0, hu0⟩ := hr
  obtain ⟨v0, hv0⟩ := hl
  refine ⟨u0, v0, ?_⟩
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => u.val ∈ R')
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun v : Fin m => n + v.val ∈ R')
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  change _ + Fr.card = n at h1
  change _ + Fc.card = m at h2
  have h3 : (Finset.univ.filter (fun u : Fin n => u.val ∈ R')).card ≤ (R'.filter (· < n)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, a.2⟩
  have h4 : (Finset.univ.filter (fun v : Fin m => n + v.val ∈ R')).card ≤
      (R'.filter (¬ · < n)).card := by
    rw [← Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h) :
      Function.Injective (fun v : Fin m => n + v.val))]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, by omega⟩
  have h5 := Finset.card_filter_add_card_filter_not (s := R') (· < n)
  simp only [Circuit.size]
  omega
