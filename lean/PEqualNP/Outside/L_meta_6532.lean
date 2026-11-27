import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6532

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6532

theorem PEqualNP.Outside.L_meta_6532 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < x1 + x3 ∧ x7 < x1 + x3) →     have x4 : Finset (Finset (Fin x1)) → Finset (Finset (Fin x1)) := fun (x4 : Finset (Finset (Fin x1))) => {x5 ∈ x4 | ∀ x6 ∈ x4, x6 ⊆ x5 → x5 ⊆ x6};     ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : Fin x1 → Bool) (x7 : ℕ), (x2.wires (List.ofFn x6)).getD x7 Bool.false = Bool.true ↔ ∃ x8 ∈ x5 x7, ∀ x9 ∈ x8, x6 x9 = Bool.true) ∧ ∀ x6 < x2.size, ∃ x8 < x1 + x6, ∃ x9 < x1 + x6, x8 ≠ x9 ∧ (x5 (x1 + x6) = x4 (x5 x8 ∪ x5 x9) ∨ x5 (x1 + x6) = x4 (Finset.image (fun (x10 : Finset (Fin x1) × Finset (Fin x1)) => x10.1 ∪ x10.2) (x5 x8 ×ˢ x5 x9))) := by
  intro n C hC mn
  classical
  have mn_sub : ∀ W, mn W ⊆ W := fun W => Finset.filter_subset _ _
  -- every member lies above a minimal member
  have mn_min : ∀ W, ∀ s ∈ W, ∃ r ∈ mn W, r ⊆ s := by
    intro W s hs
    obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (W.filter fun r => r ⊆ s) Finset.card ⟨s, Finset.mem_filter.2 ⟨hs, Finset.Subset.refl _⟩⟩
    rw [Finset.mem_filter] at hr
    refine ⟨r, Finset.mem_filter.2 ⟨hr.1, fun q hq hqr => ?_⟩, hr.2⟩
    have := hmin q (Finset.mem_filter.2 ⟨hq, hqr.trans hr.2⟩)
    exact (Finset.eq_of_subset_of_card_le hqr this).ge
  have mn_sem : ∀ W (x : Fin n → Bool), (∃ s ∈ mn W, ∀ v ∈ s, x v = true) ↔ ∃ s ∈ W, ∀ v ∈ s, x v = true := by
    intro W x
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, mn_sub W hs, h⟩
    · rintro ⟨s, hs, h⟩
      obtain ⟨r, hr, hrs⟩ := mn_min W s hs
      exact ⟨r, hr, fun v hv => h v (hrs hv)⟩
  let J : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun A B => Finset.image (fun p : Finset (Fin n) × Finset (Fin n) => p.1 ∪ p.2) (A ×ˢ B)
  have J_sem : ∀ A B (x : Fin n → Bool), (∃ s ∈ J A B, ∀ v ∈ s, x v = true) ↔ (∃ s ∈ A, ∀ v ∈ s, x v = true) ∧ ∃ s ∈ B, ∀ v ∈ s, x v = true := by
    intro A B x
    simp only [J, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨_, ⟨a, b, ⟨ha, hb⟩, rfl⟩, h⟩
      exact ⟨⟨a, ha, fun v hv => h v (Finset.mem_union_left _ hv)⟩, ⟨b, hb, fun v hv => h v (Finset.mem_union_right _ hv)⟩⟩
    · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
      exact ⟨_, ⟨a, b, ⟨ha, hb⟩, rfl⟩, fun v hv => (Finset.mem_union.1 hv).elim (h1 v) (h2 v)⟩
  let V : (Fin n → Bool) → ℕ → Bool := fun x w => (PEqualNP.Outside.L_meta_6532.run C.gates (List.ofFn x)).getD w false
  have key : ∀ k ≤ C.gates.length, ∃ W : ℕ → Finset (Finset (Fin n)), (∀ v : Fin n, W v = {{v}}) ∧
      (∀ x : Fin n → Bool, ∀ w < n + k, V x w = true ↔ ∃ s ∈ W w, ∀ v ∈ s, x v = true) ∧ (∀ w, n + k ≤ w → W w = ∅) ∧
      ∀ j < k, ∃ a < n + j, ∃ b < n + j, a ≠ b ∧ (W (n + j) = mn (W a ∪ W b) ∨ W (n + j) = mn (J (W a) (W b))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun w => if h : w < n then {{⟨w, h⟩}} else ∅, fun v => by simp, ?_, fun w hw => by simp at hw; simp [hw], fun j hj => by omega⟩
      intro x w hw
      simp only [Nat.add_zero] at hw
      simp only [V]
      rw [PEqualNP.Outside.L_meta_6532.run_input _ _ _ (by simpa using hw), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw, dif_pos hw]
      simp
    | succ k ih =>
      intro hk
      obtain ⟨W, w1, w2, w3, w4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, hne, ha, hb⟩ := hC k C.gates[k] (List.getElem?_eq_getElem hk')
      have rg := fun x : Fin n → Bool => PEqualNP.Outside.L_meta_6532.run_gate C.gates (List.ofFn x) k hk'
      simp only [List.length_ofFn, hab, List.map_cons, List.map_nil, if_pos ha, if_pos hb] at rg
      have fin : ∀ Z : Finset (Finset (Fin n)), (Z = mn (W a ∪ W b) ∨ Z = mn (J (W a) (W b))) → (∀ x : Fin n → Bool, V x (n + k) = true ↔ ∃ s ∈ Z, ∀ v ∈ s, x v = true) →
          ∃ W : ℕ → Finset (Finset (Fin n)), (∀ v : Fin n, W v = {{v}}) ∧
      (∀ x : Fin n → Bool, ∀ w < n + (k + 1), V x w = true ↔ ∃ s ∈ W w, ∀ v ∈ s, x v = true) ∧ (∀ w, n + (k + 1) ≤ w → W w = ∅) ∧
      ∀ j < k + 1, ∃ a < n + j, ∃ b < n + j, a ≠ b ∧ (W (n + j) = mn (W a ∪ W b) ∨ W (n + j) = mn (J (W a) (W b))) := by
        intro Z hZ hsem
        have upd : ∀ w, w ≠ n + k → Function.update W (n + k) Z w = W w := fun w hw => Function.update_of_ne hw _ _
        refine ⟨Function.update W (n + k) Z, fun v => ?_, ?_, fun w hw => ?_, ?_⟩
        · have := v.isLt
          rw [upd _ (by omega)]; exact w1 v
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hsem x
          · rw [upd w hwe]; exact w2 x w (by omega)
        · rw [upd w (by omega)]; exact w3 w (by omega)
        · intro j hj
          by_cases hje : j = k
          · subst hje
            refine ⟨a, ha, b, hb, hne, ?_⟩
            rw [Function.update_self, upd a (by omega), upd b (by omega)]
            exact hZ
          · obtain ⟨c, hc, d, hd, hcd, h⟩ := w4 j (by omega)
            refine ⟨c, hc, d, hd, hcd, ?_⟩
            rw [upd (n + j) (by omega), upd c (by omega), upd d (by omega)]
            exact h
      rcases hop with hop | hop
      · refine fin (mn (J (W a) (W b))) (Or.inr rfl) fun x => ?_
        rw [mn_sem, J_sem, ← w2 x a ha, ← w2 x b hb]
        simp only [V]
        rw [rg x, hop]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      · refine fin (mn (W a ∪ W b)) (Or.inl rfl) fun x => ?_
        rw [mn_sem]
        have : (∃ s ∈ W a ∪ W b, ∀ v ∈ s, x v = true) ↔ (∃ s ∈ W a, ∀ v ∈ s, x v = true) ∨ ∃ s ∈ W b, ∀ v ∈ s, x v = true := by
          simp only [Finset.mem_union]
          constructor
          · rintro ⟨s, hs | hs, h⟩
            · exact Or.inl ⟨s, hs, h⟩
            · exact Or.inr ⟨s, hs, h⟩
          · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
            · exact ⟨s, Or.inl hs, h⟩
            · exact ⟨s, Or.inr hs, h⟩
        rw [this, ← w2 x a ha, ← w2 x b hb]
        simp only [V]
        rw [rg x, hop]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  obtain ⟨W, w1, w2, w3, w4⟩ := key C.gates.length le_rfl
  refine ⟨W, w1, fun x w => ?_, w4⟩
  by_cases hw : w < n + C.gates.length
  · exact w2 x w hw
  · rw [w3 w (by omega)]
    change (PEqualNP.Outside.L_meta_6532.run C.gates (List.ofFn x)).getD w false = true ↔ _
    rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6532.run_length]; simp; omega)]
    simp
