import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5605
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (G : List Gate) (x : List Bool) :
    (G.foldl step x).length = x.length + G.length := by
  induction G generalizing x with
  | nil => simp
  | cons g G ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc (W : List Bool) (v : Bool) (w : ℕ) :
    (W ++ [v]).getD w false = if w = W.length then v else W.getD w false := by
  rcases lt_trichotomy w W.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _), if_pos rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (le_of_lt h), if_neg (Nat.ne_of_gt h)]
    have h1 : 1 ≤ w - W.length := by omega
    rw [List.getD_eq_default _ _ (by simpa using h1), List.getD_eq_default _ _ (le_of_lt h)]

lemma step_getD (W : List Bool) (g : Gate) (w : ℕ) :
    (step W g).getD w false =
      if w = W.length then g.op.eval (g.inputs.map fun i => W.getD i false) else W.getD w false :=
  getD_snoc W _ w

lemma eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with h1 | h1
  · rw [h1]
    simp only [GateOp.eval]
    intro hall
    rw [List.all_eq_true] at hall ⊢
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact h i hi (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [h1]
    simp only [GateOp.eval]
    intro hany
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨y, hy, hyt⟩ := hany
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact ⟨b i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hi hyt⟩

lemma key (n : ℕ) (G : List Gate)
    (hG : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ∃ D : Finset ℕ, D.card ≤ T.card + G.length ∧
      ∀ x x' : List Bool, x.length = n → x'.length = n →
        (∀ i ∈ D, x.getD i false = true → x'.getD i false = true) →
        ∀ w ∈ T, (G.foldl step x).getD w false = true → (G.foldl step x').getD w false = true := by
  induction G using List.reverseRecOn with
  | nil =>
    intro T
    exact ⟨T, by simp, fun x x' _ _ h w hw => by simpa using h w hw⟩
  | append_singleton G g ih =>
    intro T
    have hG' : ∀ g' ∈ G, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hG g' (by simp [h])
    have hg : g.inputs.length ≤ 2 := (hG g (by simp)).2
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := (hG g (by simp)).1
    by_cases hmT : n + G.length ∈ T
    · obtain ⟨D, hD, hDx⟩ := ih hG' (T.erase (n + G.length) ∪ g.inputs.toFinset)
      refine ⟨D, ?_, ?_⟩
      · have h1 : (T.erase (n + G.length) ∪ g.inputs.toFinset).card ≤ (T.card - 1) + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hmT]
          have := List.toFinset_card_le g.inputs
          omega
        have h2 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hmT⟩
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro x x' hx hx' hagree w hw
        have IH := hDx x x' hx hx' hagree
        have hl : (G.foldl step x).length = n + G.length := by rw [foldl_len, hx]
        have hl' : (G.foldl step x').length = n + G.length := by rw [foldl_len, hx']
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        rw [step_getD, step_getD, hl, hl']
        by_cases hwm : w = n + G.length
        · rw [if_pos hwm, if_pos hwm]
          exact eval_mono g hop _ _
            (fun i hi => IH i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
        · rw [if_neg hwm, if_neg hwm]
          exact IH w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩))
    · obtain ⟨D, hD, hDx⟩ := ih hG' T
      refine ⟨D, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro x x' hx hx' hagree w hw
        have IH := hDx x x' hx hx' hagree
        have hl : (G.foldl step x).length = n + G.length := by rw [foldl_len, hx]
        have hl' : (G.foldl step x').length = n + G.length := by rw [foldl_len, hx']
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        rw [step_getD, step_getD, hl, hl']
        have hwm : w ≠ n + G.length := fun h => hmT (h ▸ hw)
        rw [if_neg hwm, if_neg hwm]
        exact IH w hw

def adj (u v : Fin 4) : Bool := (63 : ℕ).testBit (4 * u.val + v.val)

lemma fool : ∀ D ∈ (Finset.range 8).powerset, D.card ≤ 3 →
    ∃ u v u' v' : Fin 4, adj u v = true ∧ adj u' v' = false ∧
      ∀ i ∈ D, (oneEach u v).getD i false = true → (oneEach u' v').getD i false = true := by
  decide +kernel

lemma lower (C : Circuit) (hM : Monotone2 C) (hsz : C.size ≤ 2)
    (hrep : ∀ (u v : Fin 4), C.eval (oneEach u v) = adj u v) : False := by
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hM g hg
    exact ⟨by simpa using h.1, h.2⟩
  obtain ⟨D, hD, hDx⟩ := key 8 C.gates hG {C.output}
  have hD3 : D.card ≤ 3 := by
    have h1 : D.card ≤ 1 + C.gates.length := by simpa using hD
    unfold Circuit.size at hsz
    omega
  have hsub : D.filter (fun i => i < 8) ∈ (Finset.range 8).powerset := by
    rw [Finset.mem_powerset]
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have hcard : (D.filter (fun i => i < 8)).card ≤ 3 := (Finset.card_filter_le _ _).trans hD3
  obtain ⟨u, v, u', v', hE, hN, hle⟩ := fool _ hsub hcard
  have hlen : ∀ a b : Fin 4, (oneEach a b).length = 8 := by
    intro a b
    simp [oneEach]
  have hagree : ∀ i ∈ D, (oneEach u v).getD i false = true → (oneEach u' v').getD i false = true := by
    intro i hi
    by_cases h8 : i < 8
    · exact hle i (Finset.mem_filter.mpr ⟨hi, h8⟩)
    · intro hc
      rw [List.getD_eq_default _ _ (by rw [hlen]; omega)] at hc
      exact absurd hc (by simp)
  have h := hDx _ _ (hlen u v) (hlen u' v') hagree C.output (by simp)
  have h1 := hrep u v
  have h2 := hrep u' v'
  rw [hE] at h1
  rw [hN] at h2
  unfold Circuit.eval Circuit.wires at h1 h2
  have h3 := h h1
  exact Bool.noConfusion (h3.symm.trans h2)

end PEqualNP.Outside.L_meta_5605

theorem PEqualNP.Outside.L_meta_5605 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (63 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (63 : ℕ).testBit (4 * u.val + v.val)) 2 := by
  refine ⟨⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩], 10⟩, ?_, ?_, ?_⟩, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide
  · rintro ⟨C, hM, hsz, hrep⟩
    exact PEqualNP.Outside.L_meta_5605.lower C hM hsz hrep
