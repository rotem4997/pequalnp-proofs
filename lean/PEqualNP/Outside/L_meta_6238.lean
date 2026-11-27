import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6238

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



open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem orS (n : ℕ) (gs : List Gate) :
    (gs.foldl (CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD j [] ↔
      (d = j ∨ (gs[j].op = GateOp.or ∧ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
        d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (CleanedNonEdge.orStep n) [] with hr
    have hold : ∀ i, i < gs.length → (CleanedNonEdge.orStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [CleanedNonEdge.orStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine or_congr_right (and_congr_right fun _ => exists_congr fun w =>
        and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hw => ?_)
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (CleanedNonEdge.orStep n r g).getD gs.length [] = r.length ::
          (@ite _ (g.op = GateOp.or) (Classical.dec _)
            ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => r.getD (w - n) [])) []) := by
        rw [← h1]
        unfold CleanedNonEdge.orStep
        rw [getD_at']
        congr 1
        split_ifs <;> rfl
      rw [e2, List.mem_cons, h1]
      refine or_congr_right ?_
      split_ifs with ho
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, ho, true_and]
        refine exists_congr fun w => ?_
        constructor
        · rintro ⟨⟨q1, q2, q3⟩, q4⟩
          exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
        · rintro ⟨q1, q2, q3, q4⟩
          rw [hold _ (by omega)] at q4
          exact ⟨⟨q1, q2, q3⟩, q4⟩
      · simp [ho]

theorem gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6238

theorem PEqualNP.Outside.L_meta_6238 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → ∃ (x7 : Finset (Fin x1)), x7.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → s(x8, x9) ∉ PEqualNP.TopForm.Ustar x2 x4 → x8 ∈ x7 ∨ x9 ∈ x7 := by
  intro n G _ C hC4 hC
  classical
  have hAO := hC.1
  have gA : ∀ j (hj : j < C.gates.length), PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := fun j hj => List.getD_eq_getElem _ _ hj
  have g2 : ∀ j (hj : j < C.gates.length), ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
    intro j hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hAO.2.2 _ (List.getElem_mem hj))
    have h3 := hAO.2.1 j hj
    rw [gA j hj, hab] at h3
    exact ⟨a, b, hab, h3 a (by simp), h3 b (by simp)⟩
  -- an OR wire above an input that is on is on
  have up : ∀ (x : Fin n → Bool) (k d : ℕ), k < C.gates.length → d ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] → ∀ hd : d < C.gates.length, C.gates[d].op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ∀ i : Fin n, (i : ℕ) ∈ C.gates[d].inputs → x i = true → (PEqualNP.Outside.L_meta_6238.run C.gates (List.ofFn x)).getD (n + k) false = true := by
    intro x k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro d hk hdk hd hop i hi hxi
      have rg := PEqualNP.Outside.L_meta_6238.run_gate C.gates (List.ofFn x) k hk
      rw [List.length_ofFn] at rg
      have hs := ((PEqualNP.Outside.L_meta_6238.orS n C.gates).2 k hk d).1 hdk
      rcases hs with rfl | ⟨hor, w, hw, hw1, hw2, hdw⟩
      · rw [rg, hop]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        refine ⟨i, hi, ?_⟩
        rw [if_pos (by have := i.isLt; omega), PEqualNP.Outside.L_meta_6238.run_input _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD, hxi]
      · have := ih (w - n) (by omega) d (by omega) hdw hd hop i hi hxi
        rw [show n + (w - n) = w by omega] at this
        rw [rg, hor]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        exact ⟨w, hw, by rw [if_pos hw2]; exact this⟩
  have upw : ∀ (x : Fin n → Bool) (w : ℕ), w < n + C.gates.length → ∀ i ∈ PEqualNP.TopForm.orIn n C w, x i = true → (PEqualNP.Outside.L_meta_6238.run C.gates (List.ofFn x)).getD w false = true := by
    intro x w hw i hi hxi
    simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with rfl | ⟨k, hk, ⟨h1, h2⟩, h3, h4⟩
    · rw [PEqualNP.Outside.L_meta_6238.run_input _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, hxi]
    · rw [gA k hk] at h3 h4
      have := up x (w - n) k (by omega) h2 hk h3 i h4 hxi
      rwa [show n + (w - n) = w by omega] at this
  have top : ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v := by
    intro a ha u hu v hv
    simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hal, hop, hbel⟩ := ha
    obtain ⟨p, q, hpq, hp, hq⟩ := g2 a hal
    rw [gA a hal] at hop
    have e0 : PEqualNP.TopForm.opnd C a 0 = p := by simp [PEqualNP.TopForm.opnd, gA a hal, hpq]
    have e1 : PEqualNP.TopForm.opnd C a 1 = q := by simp [PEqualNP.TopForm.opnd, gA a hal, hpq]
    simp only [PEqualNP.TopForm.side, e0, e1] at hu hv
    let x : Fin n → Bool := fun i => decide (i = u ∨ i = v)
    have rg := PEqualNP.Outside.L_meta_6238.run_gate C.gates (List.ofFn x) a hal
    rw [List.length_ofFn, hop, hpq] at rg
    simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at rg
    rw [upw x p (by omega) u hu (by simp [x]), upw x q (by omega) v hv (by simp [x])] at rg
    have := hbel x rg
    rw [PEqualNP.Outside.L_meta_6238.gf] at this
    obtain ⟨c, d, h, hc, hd⟩ := this
    have hc' : c = u ∨ c = v := by simpa [x] using hc
    have hd' : d = u ∨ d = v := by simpa [x] using hd
    rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl
    · exact absurd h (G.loopless.irrefl _)
    · exact h
    · exact h.symm
    · exact absurd h (G.loopless.irrefl _)
  -- the centre of a top with two nonempty sides
  have cen : ∀ a ∈ PEqualNP.TopForm.tops G C, ∃ c : Finset (Fin n), c.card ≤ 1 ∧ ∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, u ∈ c ∨ v ∈ c := by
    intro a ha
    by_cases h0 : (PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1
    · exact ⟨_, h0, fun u hu v hv => Or.inl hu⟩
    · refine ⟨_, ?_, fun u hu v hv => Or.inr hv⟩
      by_contra h1
      obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.1 (by omega : 1 < (PEqualNP.TopForm.side (n := n) C a 0).card)
      obtain ⟨v, hv, v', hv', hvv⟩ := Finset.one_lt_card.1 (by omega : 1 < (PEqualNP.TopForm.side (n := n) C a 1).card)
      have h2 := hC4 u u' huu
      have h3 : ({v, v'} : Finset (Fin n)) ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj u' w := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with rfl | rfl
        · exact ⟨top a ha u hu _ hv, top a ha u' hu' _ hv⟩
        · exact ⟨top a ha u hu _ hv', top a ha u' hu' _ hv'⟩
      have h4 := Finset.card_le_card h3
      rw [Finset.card_pair hvv] at h4
      omega
  choose! c hc1 hc2 using cen
  refine ⟨(PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless (n := n) G C).biUnion c, ?_, ?_⟩
  · refine (Finset.card_biUnion_le_card_mul _ _ 1 fun a ha => hc1 a (Finset.mem_sdiff.1 ha).1).trans (by simp)
  · intro u v huv hU
    have hstar : s(u, v) ∈ PEqualNP.TopForm.starEdges G C := by
      by_contra h
      exact hU (Finset.mem_sdiff.2 ⟨by simpa using huv, h⟩)
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.exists] at hstar
    obtain ⟨a, ha, p, q, ⟨hp, hq⟩, e⟩ := hstar
    have hnc : a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless (n := n) G C := by
      refine Finset.mem_sdiff.2 ⟨ha, fun h => ?_⟩
      simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at h
      rcases h.2 with h | h
      · rw [h] at hp; simp at hp
      · rw [h] at hq; simp at hq
    have hcov := hc2 a ha p hp q hq
    simp only [Finset.mem_biUnion]
    rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcov.imp (fun h => ⟨a, hnc, h⟩) (fun h => ⟨a, hnc, h⟩)
    · exact hcov.symm.imp (fun h => ⟨a, hnc, h⟩) (fun h => ⟨a, hnc, h⟩)
