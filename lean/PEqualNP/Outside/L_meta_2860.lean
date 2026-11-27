import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2860_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := ext gs w
  rw [hs]; exact List.getD_append _ _ _ _ h

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := ext gs w
  rw [hs]; simp [hl]

theorem at_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) ∧
    ∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  obtain ⟨q, hq, hql⟩ := ext (gs.take j) w
  have hQ : ((gs.take j).foldl step w).length = w.length + j := by
    rw [hq]; simp [hql]; omega
  obtain ⟨t, ht, _⟩ := ext (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have hf : gs.foldl step w = step ((gs.take j).foldl step w) gs[j] ++ t := by
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons, ht]
  rw [hf]
  constructor
  · rw [← hQ]
    simp [step, List.getD_eq_getElem?_getD]
  · intro i hi
    rw [← hQ] at hi
    have hi2 : i < (step ((gs.take j).foldl step w) gs[j]).length := by simp [step]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi2]
    simp only [step]
    rw [List.getElem?_append_left hi]

theorem loc (n : ℕ) (gs : List Gate) (w : List Bool) (hw : w.length = n) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < n + j) :
    (gs.foldl step w).getD (n + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl step w).getD i false) := by
  obtain ⟨h1, h2⟩ := at_gate gs w j hj
  rw [hw] at h1 h2
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (h2 i (hrb i hi)).symm

theorem bfact (p q r : Bool) : ((p || q) && (p || r)) = (p || (q && r)) := by
  cases p <;> cases q <;> cases r <;> rfl

end PEqualNP.Outside.L_meta_2860_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2860_aux in
theorem PEqualNP.Outside.L_meta_2860 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → n ≤ u → u < v → v < n + m → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] → (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → C.output ≠ v → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  rintro n ⟨gs, out⟩ m u v z a b hRB hm hnu huv hvm hmop hmin huop huin hvop hvin hnr hout
  simp only at hm hout
  have hga : ∀ j (hj : j < gs.length), PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ j = gs[j] := by
    intro j hj
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  have hul : u - n < gs.length := by omega
  have hvl : v - n < gs.length := by omega
  rw [hga m hm] at hmop hmin
  rw [hga _ hul] at huop huin
  rw [hga _ hvl] at hvop hvin
  have hRB2 : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j :=
    fun j hj i hi => hRB j hj i (by rw [hga j hj]; exact hi)
  have hzu : z < u := by
    have := hRB2 _ hul z (by rw [huin]; simp)
    omega
  have hau : a < u := by
    have := hRB2 _ hul a (by rw [huin]; simp)
    omega
  have hbv : b < v := by
    have := hRB2 _ hvl b (by rw [hvin]; simp)
    omega
  obtain ⟨G, hG⟩ : ∃ G, G = (gs.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩ := ⟨_, rfl⟩
  rw [← hG]
  have hlen : G.length = gs.length := by rw [hG]; simp
  have hGm : ∀ (h : m < G.length), G[m] = ⟨GateOp.or, [z, v]⟩ := by
    intro h; subst hG; simp
  have hGv : ∀ (h : v - n < G.length), G[v - n] = ⟨GateOp.and, [a, b]⟩ := by
    intro h; subst hG
    rw [List.getElem_set_of_ne (by omega)]
    simp
  have hGo : ∀ j (h : j < G.length) (h2 : j < gs.length), j ≠ m → j ≠ v - n → G[j] = gs[j] := by
    intro j h h2 h3 h4; subst hG
    rw [List.getElem_set_of_ne (Ne.symm h3), List.getElem_set_of_ne (Ne.symm h4)]
  have hgb : ∀ j (hj : j < G.length), PEqualNP.MetaComplexity.NestedCover.gateAt ⟨G, out⟩ j = G[j] := by
    intro j hj
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  have hRB3 : ∀ j (hj : j < G.length), ∀ i ∈ G[j].inputs, i < n + j := by
    intro j hj i hi
    by_cases h1 : j = m
    · subst h1
      rw [hGm hj] at hi
      simp at hi
      omega
    · by_cases h2 : j = v - n
      · subst h2
        rw [hGv hj] at hi
        simp at hi
        omega
      · rw [hGo j hj (by omega) h1 h2] at hi
        exact hRB2 j (by omega) i hi
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    rw [hgb j hj] at hi
    exact hRB3 j hj i hi
  · simp [Circuit.size, hlen]
  · intro x
    show (G.foldl step (List.ofFn x)).getD out false = (gs.foldl step (List.ofFn x)).getD out false
    have hx : (List.ofFn x).length = n := by simp
    have hL := fun j hj => loc n gs (List.ofFn x) hx j hj (hRB2 j hj)
    have hM := fun j hj => loc n G (List.ofFn x) hx j hj (hRB3 j hj)
    have hl1 := fold_len gs (List.ofFn x)
    have hl2 := fold_len G (List.ofFn x)
    have hf1 := fold_get gs (List.ofFn x)
    have hf2 := fold_get G (List.ofFn x)
    rw [hx] at hl1 hl2 hf1 hf2
    generalize gs.foldl step (List.ofFn x) = W at hL hl1 hf1 ⊢
    generalize G.foldl step (List.ofFn x) = V at hM hl2 hf2 ⊢
    have key : ∀ i, i ≠ v → V.getD i false = W.getD i false := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hne
        rcases lt_or_ge i n with hin | hin
        · rw [hf1 i hin, hf2 i hin]
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hin
          by_cases hjl : j < gs.length
          · by_cases hjm : j = m
            · subst hjm
              have eu := hL (u - n) hul
              have ev := hL (v - n) hvl
              have ew := hM (v - n) (by omega)
              rw [show n + (u - n) = u by omega, huop, huin] at eu
              rw [show n + (v - n) = v by omega, hvop, hvin] at ev
              rw [show n + (v - n) = v by omega, hGv (by omega)] at ew
              rw [hM j (by omega), hL j hjl, hGm (by omega), hmop, hmin]
              have iz := ih z (by omega) (by omega)
              have ia := ih a (by omega) (by omega)
              have ib := ih b (by omega) (by omega)
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false] at eu ev ew ⊢
              rw [eu, ev, ew, iz, ia, ib]
              exact (bfact _ _ _).symm
            · have hjv : j ≠ v - n := by omega
              rw [hM j (by omega), hL j hjl, hGo j (by omega) hjl hjm hjv]
              congr 1
              apply List.map_congr_left
              intro i hi
              apply ih i (hRB2 j hjl i hi)
              intro h
              subst h
              exact hnr j hjl hjm (by rw [hga j hjl]; exact hi)
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    exact key out hout
