import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_2391_401 :
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        let T : Finset ℕ := PEqualNP.TopForm.tops G C'
        let C0 : Finset ℕ := PEqualNP.TopForm.centreless G C'
        let J : Finset ℕ := PEqualNP.TopForm.junk G C'
        let U : Finset (Sym2 (Fin 26)) := PEqualNP.TopForm.Ustar G C'
        PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧ J.card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' ∧
        (∀ u v : Fin 26, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
          PEqualNP.CleanedNonEdge.OrReaches 26 C' (PEqualNP.TopForm.opnd C' a b) h) ∧
        G.edgeFinset.card + (T \ C0).card + 2 * C0.card + J.card +
          (PEqualNP.TopForm.orN G C' \ PEqualNP.TopForm.lam G C').card ≤ C'.size + U.card + 1 ∧
        ∀ K : Finset (Fin 26), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K →
          K.card ≤ (T \ C0).card) →
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size ≤ 64 →
      PEqualNP.TopForm.junk G C = {g} →
      let T : Finset ℕ := PEqualNP.TopForm.tops G C
      let C0 : Finset ℕ := PEqualNP.TopForm.centreless G C
      let U : Finset (Sym2 (Fin 26)) := PEqualNP.TopForm.Ustar G C
      (T \ C0).card + 2 * C0.card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ 12 + U.card →
      52 ≤ 4 * (T \ C0).card + U.card →
      2 ≤ U.card →
      False) →
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size ≤ 64 →
      let T : Finset ℕ := PEqualNP.TopForm.tops G C
      let J : Finset ℕ := PEqualNP.TopForm.junk G C
      let U : Finset (Sym2 (Fin 26)) := PEqualNP.TopForm.Ustar G C
      let R : Finset ℕ := PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C
      PEqualNP.TopForm.centreless G C = ∅ →
      2 ≤ J.card →
      1 ≤ (PEqualNP.TopForm.mixing G C).card →
      3 ≤ U.card →
      T.card + J.card + R.card ≤ 13 + U.card →
      52 ≤ 4 * T.card + U.card →
      (∀ K : Finset (Fin 26), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ T.card) →
      False) →
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size ≤ 64 →
      let T : Finset ℕ := PEqualNP.TopForm.tops G C
      let C0 : Finset ℕ := PEqualNP.TopForm.centreless G C
      let J : Finset ℕ := PEqualNP.TopForm.junk G C
      let U : Finset (Sym2 (Fin 26)) := PEqualNP.TopForm.Ustar G C
      let R : Finset ℕ := PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C
      1 ≤ C0.card →
      2 ≤ J.card →
      4 ≤ U.card →
      (T \ C0).card + 2 * C0.card + J.card + R.card ≤ 13 + U.card →
      52 ≤ 4 * (T \ C0).card + U.card →
      (∀ K : Finset (Fin 26), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
      False) →
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ := by
  intro c1 c2 c3 c4 G _ C hadj hLeast
  let _ : DecidableEq GateOp := gateOpDecEq
  let rel0 : Fin 26 → Fin 26 → Prop := fun a b =>
    a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let G0 : SimpleGraph (Fin 26) := SimpleGraph.fromRel rel0
  have hrel_iff : ∀ a b : Fin 26, G0.Adj a b ↔
      ∃ (u t : Fin 13), (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        (a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t ∨ b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t) := by
    dsimp only [G0, rel0, SimpleGraph.fromRel]
    decide +kernel
  have hGeq : G = G0 := by
    ext a b
    exact (hadj a b).trans (hrel_iff a b).symm
  have hNoFour0 : ∀ a b : Fin 26, a ≠ b →
      (Finset.univ.filter fun w : Fin 26 => G0.Adj a w ∧ G0.Adj b w).card ≤ 1 := by
    dsimp only [G0, rel0, SimpleGraph.fromRel]
    decide +kernel
  have hNoFour : NoFourCycle G := by
    intro a b hab
    have hfilt : (Finset.univ.filter fun w : Fin 26 => G.Adj a w ∧ G.Adj b w) =
        (Finset.univ.filter fun w : Fin 26 => G0.Adj a w ∧ G0.Adj b w) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hGeq]
    rw [hfilt]
    exact hNoFour0 a b hab
  have hDeg4_0 : ∀ v : Fin 26, (Finset.univ.filter fun w : Fin 26 => G0.Adj v w).card = 4 := by
    dsimp only [G0, rel0, SimpleGraph.fromRel]
    decide +kernel
  have hDeg4 : ∀ v : Fin 26, (Finset.univ.filter fun w : Fin 26 => G.Adj v w).card = 4 := by
    intro v
    have hfilt : (Finset.univ.filter fun w : Fin 26 => G.Adj v w) =
        (Finset.univ.filter fun w : Fin 26 => G0.Adj v w) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hGeq]
    rw [hfilt]
    exact hDeg4_0 v
  have hCard52_0 : G0.edgeFinset.card = 52 := by
    dsimp only [G0, rel0, SimpleGraph.fromRel]
    decide +kernel
  have hCard52 : G.edgeFinset.card = 52 := by
    have hEF : G.edgeFinset = G0.edgeFinset := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, hGeq]
    rw [hEF]
    exact hCard52_0
  have hNonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfoldW_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp [stepW]; omega
  have hfoldW_getD : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (stepW w g) i (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hwire_input : ∀ (D : Circuit) (x : Fin 26 → Bool) (v : Fin 26), wireVal 26 D v.val x = x v := by
    intro D x v
    change (D.gates.foldl stepW (List.ofFn x)).getD v.val false = x v
    rw [hfoldW_getD D.gates (List.ofFn x) v.val (by simp)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [v.isLt]
  have hgate_eval : ∀ (D : Circuit) (x : Fin 26 → Bool) (k : ℕ), k < D.gates.length →
      gateVal 26 D k x = (gateAt D k).op.eval ((gateAt D k).inputs.map fun i =>
        if i < 26 + k then wireVal 26 D i x else false) := by
    intro D x k hk
    let gk : Gate := D.gates[k]
    have hsplit : D.gates = D.gates.take k ++ gk :: D.gates.drop (k + 1) := by
      simp only [gk]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hga : gateAt D k = gk := by
      unfold gateAt; simp only [gk, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem, Option.getD_some]
    rw [hga]
    let w0 := (D.gates.take k).foldl stepW (List.ofFn x)
    have hw0_len : w0.length = 26 + k := by
      simp [w0, hfoldW_len, Nat.min_eq_left hk.le]
    have h1' : gateVal 26 D k x = gk.op.eval (gk.inputs.map fun i => w0.getD i false) := by
      change (D.gates.foldl stepW (List.ofFn x)).getD (26 + k) false = _
      rw [hsplit, List.foldl_append, List.foldl_cons]
      rw [hfoldW_getD (D.gates.drop (k + 1)) (stepW w0 gk) (26 + k) (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, hw0_len]
    rw [h1']
    congr 1
    refine List.map_congr_left fun i _ => ?_
    by_cases hi : i < 26 + k
    · simp only [hi, ↓reduceIte]
      change w0.getD i false = (D.gates.foldl stepW (List.ofFn x)).getD i false
      rw [hsplit, List.foldl_append]
      exact (hfoldW_getD _ w0 i (by omega)).symm
    · simp only [hi, ↓reduceIte]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show w0.length ≤ i by omega)]
  let pGates (p : ℕ) : List Gate :=
    [ ⟨GateOp.or, [13 + p, 13 + (p + 12) % 13]⟩,
      ⟨GateOp.or, [13 + (p + 10) % 13, 13 + (p + 4) % 13]⟩,
      ⟨GateOp.or, [26 + 4 * p, 26 + 4 * p + 1]⟩,
      ⟨GateOp.and, [p, 26 + 4 * p + 2]⟩ ]
  let topOrs : List Gate :=
    ⟨GateOp.or, [29, 33]⟩ ::
      (List.range 11).map (fun k => ⟨GateOp.or, [78 + k, 29 + 4 * (k + 2)]⟩)
  let Cstar : Circuit := ⟨(List.range 13).flatMap pGates ++ topOrs, 89⟩
  have hstarSz : Cstar.gates.length = 64 := by
    dsimp only [Cstar, pGates, topOrs]; decide +kernel
  have hstarAO : IsAO2 26 Cstar := by
    dsimp only [Cstar, pGates, topOrs]; decide +kernel
  have hstar_p : ∀ p : Fin 13,
      gateAt Cstar (4 * p.val) = ⟨GateOp.or, [13 + p.val, 13 + (p.val + 12) % 13]⟩ ∧
      gateAt Cstar (4 * p.val + 1) = ⟨GateOp.or, [13 + (p.val + 10) % 13, 13 + (p.val + 4) % 13]⟩ ∧
      gateAt Cstar (4 * p.val + 2) = ⟨GateOp.or, [26 + 4 * p.val, 26 + 4 * p.val + 1]⟩ ∧
      gateAt Cstar (4 * p.val + 3) = ⟨GateOp.and, [p.val, 26 + 4 * p.val + 2]⟩ := by
    intro p
    have hp : p.val < 13 := p.isLt
    interval_cases p.val <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hstar_t0 : gateAt Cstar 52 = ⟨GateOp.or, [29, 33]⟩ := rfl
  have hstar_tk : ∀ k : Fin 11,
      gateAt Cstar (53 + k.val) = ⟨GateOp.or, [78 + k.val, 29 + 4 * (k.val + 2)]⟩ := by
    intro k
    have hk : k.val < 11 := k.isLt
    interval_cases k.val <;> rfl
  have hsub_val : ∀ p : Fin 13,
      (p - 1).val = (p.val + 12) % 13 ∧ (p - 3).val = (p.val + 10) % 13 ∧ (p - 9).val = (p.val + 4) % 13 := by
    decide
  have hstar_p_eval : ∀ (x : Fin 26 → Bool) (p : Fin 13),
      wireVal 26 Cstar (29 + 4 * p.val) x = true ↔
        ∃ t : Fin 13, (p = t ∨ p = t + 1 ∨ p = t + 3 ∨ p = t + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 t) = true := by
    intro x p
    have hp13 := p.isLt
    obtain ⟨hg0, hg1, hg2, hg3⟩ := hstar_p p
    obtain ⟨hs1, hs3, hs9⟩ := hsub_val p
    have h0 : wireVal 26 Cstar (26 + 4 * p.val) x =
        (x (Fin.natAdd 13 p) || x (Fin.natAdd 13 (p - 1))) := by
      change gateVal 26 Cstar (4 * p.val) x = _
      rw [hgate_eval Cstar x (4 * p.val) (by omega), hg0]
      dsimp only [GateOp.eval]
      have ha : 13 + p.val < 26 + 4 * p.val := by omega
      have hb : 13 + (p.val + 12) % 13 < 26 + 4 * p.val := by omega
      simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [← hs1]
      have h1' := hwire_input Cstar x (Fin.natAdd 13 p)
      have h2' := hwire_input Cstar x (Fin.natAdd 13 (p - 1))
      simp only [Fin.val_natAdd] at h1' h2'
      rw [h1', h2']
    have h1 : wireVal 26 Cstar (26 + 4 * p.val + 1) x =
        (x (Fin.natAdd 13 (p - 3)) || x (Fin.natAdd 13 (p - 9))) := by
      change gateVal 26 Cstar (4 * p.val + 1) x = _
      rw [hgate_eval Cstar x (4 * p.val + 1) (by omega), hg1]
      dsimp only [GateOp.eval]
      have ha : 13 + (p.val + 10) % 13 < 26 + (4 * p.val + 1) := by omega
      have hb : 13 + (p.val + 4) % 13 < 26 + (4 * p.val + 1) := by omega
      simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [← hs3, ← hs9]
      have h1' := hwire_input Cstar x (Fin.natAdd 13 (p - 3))
      have h2' := hwire_input Cstar x (Fin.natAdd 13 (p - 9))
      simp only [Fin.val_natAdd] at h1' h2'
      rw [h1', h2']
    have h2 : wireVal 26 Cstar (26 + 4 * p.val + 2) x =
        ((x (Fin.natAdd 13 p) || x (Fin.natAdd 13 (p - 1))) ||
         (x (Fin.natAdd 13 (p - 3)) || x (Fin.natAdd 13 (p - 9)))) := by
      change gateVal 26 Cstar (4 * p.val + 2) x = _
      rw [hgate_eval Cstar x (4 * p.val + 2) (by omega), hg2]
      dsimp only [GateOp.eval]
      have ha : 26 + 4 * p.val < 26 + (4 * p.val + 2) := by omega
      have hb : 26 + 4 * p.val + 1 < 26 + (4 * p.val + 2) := by omega
      simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [h0, h1]
    have h3 : wireVal 26 Cstar (29 + 4 * p.val) x =
        (x (Fin.castAdd 13 p) &&
         ((x (Fin.natAdd 13 p) || x (Fin.natAdd 13 (p - 1))) ||
          (x (Fin.natAdd 13 (p - 3)) || x (Fin.natAdd 13 (p - 9))))) := by
      rw [show 29 + 4 * p.val = 26 + (4 * p.val + 3) by omega]
      change gateVal 26 Cstar (4 * p.val + 3) x = _
      rw [hgate_eval Cstar x (4 * p.val + 3) (by omega), hg3]
      dsimp only [GateOp.eval]
      have ha : p.val < 26 + (4 * p.val + 3) := by omega
      have hb : 26 + 4 * p.val + 2 < 26 + (4 * p.val + 3) := by omega
      simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have hp' := hwire_input Cstar x (Fin.castAdd 13 p)
      simp only [Fin.val_castAdd] at hp'
      rw [hp', h2]
    rw [h3]
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    constructor
    · rintro ⟨hxp, (ht | ht) | (ht | ht)⟩
      · exact ⟨p, Or.inl rfl, hxp, ht⟩
      · exact ⟨p - 1, Or.inr (Or.inl (by abel)), hxp, ht⟩
      · exact ⟨p - 3, Or.inr (Or.inr (Or.inl (by abel))), hxp, ht⟩
      · exact ⟨p - 9, Or.inr (Or.inr (Or.inr (by abel))), hxp, ht⟩
    · rintro ⟨t, hinc, hxp, hxt⟩
      refine ⟨hxp, ?_⟩
      rcases hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxt)
      · left; right; simpa using hxt
      · right; left; simpa using hxt
      · right; right; simpa using hxt
  have hstar_chain : ∀ (x : Fin 26 → Bool) (k : ℕ), k ≤ 11 →
      (wireVal 26 Cstar (78 + k) x = true ↔
        ∃ p : Fin 13, p.val ≤ k + 1 ∧ wireVal 26 Cstar (29 + 4 * p.val) x = true) := by
    intro x k
    induction k with
    | zero =>
      intro _
      rw [show 78 + 0 = 26 + 52 by omega]
      change gateVal 26 Cstar 52 x = true ↔ _
      rw [hgate_eval Cstar x 52 (by omega), hstar_t0]
      dsimp only [GateOp.eval]
      simp only [List.map_cons, List.map_nil, show 29 < 26 + 52 by omega, show 33 < 26 + 52 by omega,
        ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · exact ⟨⟨0, by omega⟩, by dsimp; omega, h⟩
        · exact ⟨⟨1, by omega⟩, by dsimp; omega, h⟩
      · rintro ⟨p, hp, hval⟩
        have : p.val = 0 ∨ p.val = 1 := by omega
        rcases this with h0 | h1
        · left; simpa [h0] using hval
        · right; simpa [h1] using hval
    | succ k ih =>
      intro hk
      rw [show 78 + (k + 1) = 26 + (53 + k) by omega]
      change gateVal 26 Cstar (53 + k) x = true ↔ _
      have htk := hstar_tk ⟨k, by omega⟩
      dsimp only at htk
      rw [hgate_eval Cstar x (53 + k) (by omega), htk]
      dsimp only [GateOp.eval]
      have ha : 78 + k < 26 + (53 + k) := by omega
      have hb : 29 + 4 * (k + 2) < 26 + (53 + k) := by omega
      simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, Bool.or_eq_true]
      rw [ih (by omega)]
      constructor
      · rintro (⟨p, hp, hval⟩ | hval)
        · exact ⟨p, by omega, hval⟩
        · exact ⟨⟨k + 2, by omega⟩, by dsimp; omega, hval⟩
      · rintro ⟨p, hp, hval⟩
        by_cases hle : p.val ≤ k + 1
        · exact Or.inl ⟨p, hle, hval⟩
        · right
          have hpeq : p.val = k + 2 := by omega
          simpa [hpeq] using hval
  have hstarFun : circuitFun 26 Cstar = graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    have h1' : circuitFun 26 Cstar x = wireVal 26 Cstar (78 + 11) x := rfl
    rw [h1', hstar_chain x 11 (le_refl 11)]
    change (∃ p : Fin 13, p.val ≤ 12 ∧ wireVal 26 Cstar (29 + 4 * p.val) x = true) ↔
      (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
        decide (∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨p, _, hval⟩
      obtain ⟨t, hinc, hxp, hxt⟩ := (hstar_p_eval x p).mp hval
      exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 t, (hadj _ _).mpr ⟨p, t, hinc, Or.inl ⟨rfl, rfl⟩⟩, hxp, hxt⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      obtain ⟨p, t, hinc, hor⟩ := (hadj u v).mp huv
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p, by omega, (hstar_p_eval x p).mpr ⟨t, hinc, hxu, hxv⟩⟩
      · exact ⟨p, by omega, (hstar_p_eval x p).mpr ⟨t, hinc, hxv, hxu⟩⟩
  have hCsize : C.size ≤ 64 := by
    have hle := hLeast.2.2 Cstar hstarAO hstarFun
    change C.size ≤ Cstar.gates.length at hle
    omega
  have hVC_drop : ∀ (U : Finset (Sym2 (Fin 26))) (K : Finset (Fin 26)),
      IsMinCover (G.deleteEdges ↑U) K → 52 ≤ 4 * K.card + U.card := by
    intro U K hK
    have hsub : G.edgeFinset \ U ⊆
        K.biUnion fun v => (Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w) := by
      intro e he
      obtain ⟨heG, heU⟩ := Finset.mem_sdiff.mp he
      rw [SimpleGraph.mem_edgeFinset] at heG
      induction e using Sym2.ind with
      | _ u v =>
        have hadj' : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨heG, heU⟩
        rcases hK.1 hadj' with hu | hv
        · refine Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr ⟨v, ?_, rfl⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, heG⟩
        · refine Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨u, ?_, Sym2.eq_swap⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, heG.symm⟩
    have hc1 : G.edgeFinset.card - U.card ≤ (G.edgeFinset \ U).card := Finset.le_card_sdiff U G.edgeFinset
    have hc2 : (G.edgeFinset \ U).card ≤
        (K.biUnion fun v => (Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w)).card :=
      Finset.card_le_card hsub
    have hc3 : (K.biUnion fun v => (Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w)).card ≤
        ∑ v ∈ K, ((Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w)).card :=
      Finset.card_biUnion_le
    have hc4 : (∑ v ∈ K, ((Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w)).card) ≤
        ∑ v ∈ K, 4 := by
      refine Finset.sum_le_sum fun v _ => ?_
      exact Finset.card_image_le.trans (le_of_eq (hDeg4 v))
    have hc5 : (∑ _v ∈ K, 4) = 4 * K.card := by simp [Nat.mul_comm]
    omega
  have hexMinCover : ∀ U : Finset (Sym2 (Fin 26)), ∃ K : Finset (Fin 26), IsMinCover (G.deleteEdges ↑U) K := by
    classical
    intro U
    let H := G.deleteEdges (↑U : Set (Sym2 (Fin 26)))
    let S : Finset (Finset (Fin 26)) := Finset.univ.filter fun K => H.IsVertexCover (K : Set (Fin 26))
    have hS : S.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
    obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image S Finset.card hS
    exact ⟨K, (Finset.mem_filter.mp hK).2, fun K' hK' => hmin K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK'⟩)⟩
  obtain ⟨D, hDL, hDsz, hDjc, hDTF, hDoff, hDcnt, hDcov⟩ := c1 G C hNoFour hNonempty hLeast
  have hDle64 : D.size ≤ 64 := by omega
  obtain ⟨K0, hK0⟩ := hexMinCover (Ustar G D)
  have hK0_le : K0.card ≤ (tops G D \ centreless G D).card := hDcov K0 hK0
  have hVC0 : 52 ≤ 4 * (tops G D \ centreless G D).card + (Ustar G D).card := by
    have := hVC_drop (Ustar G D) K0 hK0
    omega
  have hCnt : (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
      (orN G D \ lam G D).card ≤ 13 + (Ustar G D).card := by
    rw [hCard52] at hDcnt
    omega
  have hmix_sub : mixing G D ⊆ orN G D \ lam G D := by
    intro m hm
    change m ∈ (orN G D).filter (fun m => (orIn 26 D (opnd D m 0) = ∅) ≠ (orIn 26 D (opnd D m 1) = ∅)) at hm
    rw [Finset.mem_filter] at hm
    refine Finset.mem_sdiff.mpr ⟨hm.1, fun hl => ?_⟩
    change m ∈ (orN G D).filter (fun h => (orIn 26 D (opnd D h 0)).Nonempty ∧ (orIn 26 D (opnd D h 1)).Nonempty ∧
      ∃ a ∈ tops G D, ∃ b : Fin 2, (side (n := 26) D a (1 - b)).card = 1 ∧ OrReaches 26 D (opnd D a b) h) at hl
    rw [Finset.mem_filter] at hl
    apply hm.2
    have h0ne : orIn 26 D (opnd D m 0) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hl.2.1
    have h1ne : orIn 26 D (opnd D m 1) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hl.2.2.1
    exact propext ⟨fun h => absurd h h0ne, fun h => absurd h h1ne⟩
  have hmix_pos : centreless G D = ∅ → (Ustar G D).Nonempty → 1 ≤ (mixing G D).card := by
    intro hC0emp hUne
    obtain ⟨⟨hAndOr, hReads, hLen2⟩, _, _⟩ := hDL
    have hgateAt_mem : ∀ k < D.gates.length, gateAt D k ∈ D.gates := by
      intro k hk
      have : gateAt D k = D.gates[k] := by
        change D.gates.getD k ⟨GateOp.or, []⟩ = D.gates[k]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      rw [this]
      exact List.getElem_mem hk
    have hinputs_eq : ∀ k < D.gates.length, (gateAt D k).inputs = [opnd D k 0, opnd D k 1] := by
      intro k hk
      obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hLen2 _ (hgateAt_mem k hk))
      change (gateAt D k).inputs = [(gateAt D k).inputs.getD 0 0, (gateAt D k).inputs.getD 1 0]
      rw [hin]
      rfl
    have hopnd_lt : ∀ k < D.gates.length, ∀ b : Fin 2, opnd D k b < 26 + k := by
      intro k hk b
      apply hReads k hk
      rw [hinputs_eq k hk]
      by_cases hb : b = 0
      · rw [hb]; exact List.mem_cons_self
      · have hb1 : b = 1 := Fin.ext (by have := b.isLt; have : b.val ≠ 0 := fun h => hb (Fin.ext h); omega)
        rw [hb1]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hgate_or : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or → ∀ x : Fin 26 → Bool,
        gateVal 26 D k x = (wireVal 26 D (opnd D k 0) x || wireVal 26 D (opnd D k 1) x) := by
      intro k hk hop x
      rw [hgate_eval D x k hk, hop, hinputs_eq k hk]
      dsimp only [GateOp.eval]
      simp only [List.map_cons, List.map_nil, hopnd_lt k hk 0, hopnd_lt k hk 1, ↓reduceIte,
        List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have horFold_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
        (gs.foldl (orStep 26) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp
      | cons g gs ih =>
        intro cs; simp only [List.foldl_cons]; rw [ih]
        change (cs ++ [_]).length + gs.length = _
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have horFold_getD : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ), k < cs.length →
        (gs.foldl (orStep 26) cs).getD k [] = cs.getD k [] := by
      intro gs
      induction gs with
      | nil => intro cs k _; rfl
      | cons g gs ih =>
        intro cs k hk
        simp only [List.foldl_cons]
        have hlen1 : k < (orStep 26 cs g).length := by
          change k < (cs ++ [_]).length
          simp only [List.length_append, List.length_singleton]; omega
        rw [ih (orStep 26 cs g) k hlen1]
        unfold orStep
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
    have horSets_mem_iff : ∀ k < D.gates.length, ∀ g : ℕ,
        g ∈ (orSets 26 D).getD k [] ↔ g = k ∨ ((gateAt D k).op = GateOp.or ∧
          ∃ w ∈ (gateAt D k).inputs, 26 ≤ w ∧ w < 26 + k ∧ g ∈ (orSets 26 D).getD (w - 26) []) := by
      intro k hk g
      let gk : Gate := D.gates[k]
      have hsplit : D.gates = D.gates.take k ++ gk :: D.gates.drop (k + 1) := by
        simp only [gk]
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      have hga : gateAt D k = gk := by
        unfold gateAt; simp only [gk, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem, Option.getD_some]
      rw [hga]
      let pre := (D.gates.take k).foldl (orStep 26) []
      have hpre_len : pre.length = k := by simp [pre, horFold_len, Nat.min_eq_left hk.le]
      have hc : orSets 26 D = (D.gates.drop (k + 1)).foldl (orStep 26) (orStep 26 pre gk) := by
        unfold orSets; rw (occs := [1]) [hsplit]; rw [List.foldl_append, List.foldl_cons]
      have h1' : (orSets 26 D).getD k [] = (orStep 26 pre gk).getD k [] := by
        rw [hc, horFold_getD _ _ k (by change k < (pre ++ [_]).length; simp [hpre_len])]
      have h2' : ∀ m < k, (orSets 26 D).getD m [] = pre.getD m [] := by
        intro m hm
        rw [hc, horFold_getD _ _ m (by change m < (pre ++ [_]).length; simp [hpre_len]; omega)]
        unfold orStep
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show m < pre.length by omega)]
      rw [h1']
      have hget : (orStep 26 pre gk).getD k [] =
          k :: (if gk.op = GateOp.or then
            (gk.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap (fun w => pre.getD (w - 26) [])
            else []) := by
        unfold orStep
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right hpre_len.le, hpre_len, Nat.sub_self]
        simp
      rw [hget]
      by_cases hop : gk.op = GateOp.or
      · simp only [hop, ↓reduceIte, true_and, List.mem_cons, List.mem_flatMap, List.mem_filter,
          decide_eq_true_eq]
        constructor
        · rintro (rfl | ⟨w, ⟨hw, h26, hlt⟩, hg⟩)
          · exact Or.inl rfl
          · refine Or.inr ⟨w, hw, h26, hlt, ?_⟩
            rw [h2' (w - 26) (by omega)]
            exact hg
        · rintro (rfl | ⟨w, hw, h26, hlt, hg⟩)
          · exact Or.inl rfl
          · refine Or.inr ⟨w, ⟨hw, h26, hlt⟩, ?_⟩
            rw [h2' (w - 26) (by omega)] at hg
            exact hg
      · simp [hop]
    have horReaches_iff : ∀ k < D.gates.length, ∀ g : ℕ,
        OrReaches 26 D (26 + k) g ↔ g = k ∨ ((gateAt D k).op = GateOp.or ∧
          (OrReaches 26 D (opnd D k 0) g ∨ OrReaches 26 D (opnd D k 1) g)) := by
      intro k hk g
      unfold OrReaches
      simp only [Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
      rw [horSets_mem_iff k hk g, hinputs_eq k hk]
      constructor
      · rintro (rfl | ⟨hop, w, hw, h26, hlt, hg⟩)
        · exact Or.inl rfl
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact Or.inr ⟨hop, Or.inl ⟨h26, hg⟩⟩
          · exact Or.inr ⟨hop, Or.inr ⟨h26, hg⟩⟩
      · rintro (rfl | ⟨hop, ⟨h26, hg⟩ | ⟨h26, hg⟩⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨hop, opnd D k 0, by simp, h26, hopnd_lt k hk 0, hg⟩
        · exact Or.inr ⟨hop, opnd D k 1, by simp, h26, hopnd_lt k hk 1, hg⟩
    have horReaches_bounds : ∀ w g : ℕ, OrReaches 26 D w g →
        26 + g ≤ w ∧ g < D.gates.length ∧ w < 26 + D.gates.length := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro g hr
        obtain ⟨h26, hmem⟩ := hr
        have hwlt : w - 26 < D.gates.length := by
          by_contra hge
          have hlen : (orSets 26 D).length = D.gates.length := by
            unfold orSets; simpa using horFold_len D.gates []
          have : (orSets 26 D).getD (w - 26) [] = [] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (orSets 26 D).length ≤ w - 26 by omega)]
            rfl
          rw [this] at hmem
          simp at hmem
        have hwk : w = 26 + (w - 26) := by omega
        rw [hwk] at hmem ⊢
        have hr' : OrReaches 26 D (26 + (w - 26)) g := ⟨by omega, by simpa using hmem⟩
        rw [horReaches_iff (w - 26) hwlt g] at hr'
        rcases hr' with rfl | ⟨_, h0 | h1'⟩
        · exact ⟨by omega, hwlt, by omega⟩
        · have hlt := hopnd_lt (w - 26) hwlt 0
          have hb := ih (opnd D (w - 26) 0) (by omega) g h0
          omega
        · have hlt := hopnd_lt (w - 26) hwlt 1
          have hb := ih (opnd D (w - 26) 1) (by omega) g h1'
          omega
    have horReaches_val : ∀ w g : ℕ, OrReaches 26 D w g → ∀ x : Fin 26 → Bool,
        gateVal 26 D g x = true → wireVal 26 D w x = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro g hr x hg
        have hb := horReaches_bounds w g hr
        have hwk : w = 26 + (w - 26) := by omega
        have hwl : w - 26 < D.gates.length := by omega
        rw [hwk] at hr ⊢
        rw [horReaches_iff (w - 26) hwl g] at hr
        rcases hr with rfl | ⟨hop, h0 | h1'⟩
        · exact hg
        · change gateVal 26 D (w - 26) x = true
          rw [hgate_or (w - 26) hwl hop x]
          have := ih _ (by have := hopnd_lt (w - 26) hwl 0; omega) g h0 x hg
          simp [this]
        · change gateVal 26 D (w - 26) x = true
          rw [hgate_or (w - 26) hwl hop x]
          have := ih _ (by have := hopnd_lt (w - 26) hwl 1; omega) g h1' x hg
          simp [this]
    have horIn_val : ∀ (w : ℕ) (u : Fin 26), u ∈ orIn 26 D w → wireVal 26 D w (pairInput u u) = true := by
      intro w u hu
      change u ∈ Finset.univ.filter (fun i : Fin 26 => (i : ℕ) = w ∨ ∃ k < D.gates.length,
        OrReaches 26 D w k ∧ (gateAt D k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt D k).inputs) at hu
      rw [Finset.mem_filter] at hu
      rcases hu.2 with rfl | ⟨k, hk, hr, hop, hin⟩
      · rw [hwire_input D (pairInput u u) u]
        exact decide_eq_true (Or.inl rfl)
      · apply horReaches_val w k hr
        rw [hgate_or k hk hop]
        rw [hinputs_eq k hk] at hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with h0 | h1'
        · rw [← h0, hwire_input D (pairInput u u) u]
          have ht : pairInput u u u = true := decide_eq_true (Or.inl rfl)
          rw [ht, Bool.true_or]
        · rw [← h1', hwire_input D (pairInput u u) u]
          have ht : pairInput u u u = true := decide_eq_true (Or.inl rfl)
          rw [ht, Bool.or_true]
    have horIn_not_below : ∀ k < D.gates.length, (orIn 26 D (26 + k)).Nonempty → ¬ BelowF G D k := by
      intro k _ hne hbel
      obtain ⟨u, hu⟩ := hne
      have hv : gateVal 26 D k (pairInput u u) = true := horIn_val (26 + k) u hu
      have hf := hbel (pairInput u u) hv
      change (decide (∃ a ∈ (∅ : Finset (Fin 26)), pairInput u u a = true) ||
        decide (∃ a b : Fin 26, G.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true)) = true at hf
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq] at hf
      obtain ⟨a, b, hab, ha, hb⟩ := hf
      change decide (a = u ∨ a = u) = true at ha
      change decide (b = u ∨ b = u) = true at hb
      rw [decide_eq_true_eq, or_self] at ha hb
      rw [ha, hb] at hab
      exact G.irrefl hab
    have horIn_or_mem : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or → ∀ u : Fin 26,
        u ∈ orIn 26 D (26 + k) → u ∈ orIn 26 D (opnd D k 0) ∨ u ∈ orIn 26 D (opnd D k 1) := by
      intro k hk hop u hu
      change u ∈ Finset.univ.filter (fun i : Fin 26 => (i : ℕ) = 26 + k ∨ ∃ m < D.gates.length,
        OrReaches 26 D (26 + k) m ∧ (gateAt D m).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt D m).inputs) at hu
      rw [Finset.mem_filter] at hu
      rcases hu.2 with hEq | ⟨m, hm, hr, hmop, hmin⟩
      · have := u.isLt; omega
      · rw [horReaches_iff k hk m] at hr
        rcases hr with rfl | ⟨_, h0 | h1'⟩
        · rw [hinputs_eq m hm] at hmin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmin
          rcases hmin with h0 | h1'
          · left
            change u ∈ Finset.univ.filter _
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inl h0⟩
          · right
            change u ∈ Finset.univ.filter _
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inl h1'⟩
        · left
          change u ∈ Finset.univ.filter _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inr ⟨m, hm, h0, hmop, hmin⟩⟩
        · right
          change u ∈ Finset.univ.filter _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inr ⟨m, hm, h1', hmop, hmin⟩⟩
    have hfind_mix : ∀ (w h : ℕ), h ∈ junk G D → OrReaches 26 D w h → (orIn 26 D w).Nonempty →
        ∃ m ∈ mixing G D, True := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro h hh hr hne
        have hb := horReaches_bounds w h hr
        have hwk : w = 26 + (w - 26) := by omega
        have hwl : w - 26 < D.gates.length := by omega
        rw [hwk] at hr hne
        rw [horReaches_iff (w - 26) hwl h] at hr
        rcases hr with rfl | ⟨hop, h0 | h1'⟩
        · obtain ⟨u, hu⟩ := hne
          change w - 26 ∈ (Finset.range D.gates.length).filter (fun j => (gateAt D j).op = GateOp.and ∧ IsDirty 26 G D j) at hh
          rw [Finset.mem_filter] at hh
          have hop_and : (gateAt D (w - 26)).op = GateOp.and := hh.2.1
          change u ∈ Finset.univ.filter (fun i : Fin 26 => (i : ℕ) = 26 + (w - 26) ∨ ∃ m < D.gates.length,
            OrReaches 26 D (26 + (w - 26)) m ∧ (gateAt D m).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt D m).inputs) at hu
          rw [Finset.mem_filter] at hu
          rcases hu.2 with hEq | ⟨m, hm, hrm, hmop, _⟩
          · have := u.isLt; omega
          · rw [horReaches_iff (w - 26) hwl m] at hrm
            rcases hrm with rfl | ⟨hor, _⟩
            · rw [hop_and] at hmop; cases hmop
            · rw [hop_and] at hor; cases hor
        · by_cases hne0 : (orIn 26 D (opnd D (w - 26) 0)).Nonempty
          · exact ih (opnd D (w - 26) 0) (by have := hopnd_lt (w - 26) hwl 0; omega) h hh h0 hne0
          · rw [Finset.not_nonempty_iff_eq_empty] at hne0
            obtain ⟨u, hu⟩ := hne
            have hu1 : u ∈ orIn 26 D (opnd D (w - 26) 1) := by
              rcases horIn_or_mem (w - 26) hwl hop u hu with ha | hb'
              · rw [hne0] at ha; exact absurd ha (Finset.notMem_empty u)
              · exact hb'
            have hne1 : orIn 26 D (opnd D (w - 26) 1) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨u, hu1⟩
            refine ⟨w - 26, ?_, trivial⟩
            change w - 26 ∈ ((Finset.range D.gates.length).filter fun j => (gateAt D j).op = GateOp.or ∧ ¬ BelowF G D j).filter _
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
            refine ⟨⟨hwl, hop, horIn_not_below (w - 26) hwl ⟨u, hu⟩⟩, ?_⟩
            intro hEq
            exact hne1 (hEq ▸ hne0)
        · by_cases hne1 : (orIn 26 D (opnd D (w - 26) 1)).Nonempty
          · exact ih (opnd D (w - 26) 1) (by have := hopnd_lt (w - 26) hwl 1; omega) h hh h1' hne1
          · rw [Finset.not_nonempty_iff_eq_empty] at hne1
            obtain ⟨u, hu⟩ := hne
            have hu0 : u ∈ orIn 26 D (opnd D (w - 26) 0) := by
              rcases horIn_or_mem (w - 26) hwl hop u hu with ha | hb'
              · exact ha
              · rw [hne1] at hb'; exact absurd hb' (Finset.notMem_empty u)
            have hne0 : orIn 26 D (opnd D (w - 26) 0) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨u, hu0⟩
            refine ⟨w - 26, ?_, trivial⟩
            change w - 26 ∈ ((Finset.range D.gates.length).filter fun j => (gateAt D j).op = GateOp.or ∧ ¬ BelowF G D j).filter _
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
            refine ⟨⟨hwl, hop, horIn_not_below (w - 26) hwl ⟨u, hu⟩⟩, ?_⟩
            intro hEq
            exact hne0 (hEq.symm ▸ hne1)
    obtain ⟨e, he⟩ := hUne
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a, ha, b, h, hh, hreach⟩ := hDoff u v he
      have ha_not : a ∉ centreless G D := by rw [hC0emp]; exact Finset.notMem_empty a
      change a ∉ (tops G D).filter (fun a => side (n := 26) D a 0 = ∅ ∨ side (n := 26) D a 1 = ∅) at ha_not
      rw [Finset.mem_filter, not_and, not_or] at ha_not
      obtain ⟨hs0, hs1⟩ := ha_not ha
      have hne_ab : (orIn 26 D (opnd D a b)).Nonempty := by
        by_cases hb : b = 0
        · rw [hb]; exact Finset.nonempty_iff_ne_empty.mpr hs0
        · have hb1 : b = 1 := Fin.ext (by have := b.isLt; have : b.val ≠ 0 := fun h => hb (Fin.ext h); omega)
          rw [hb1]; exact Finset.nonempty_iff_ne_empty.mpr hs1
      obtain ⟨m, hm, _⟩ := hfind_mix (opnd D a b) h hh hreach hne_ab
      exact Finset.card_pos.mpr ⟨m, hm⟩
  by_cases hj0 : (junk G D).card = 0
  · rw [hDjc] at hj0
    exact Finset.card_eq_zero.mp hj0
  · exfalso
    by_cases hj1 : (junk G D).card = 1
    · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj1
      have hU2 : 2 ≤ (Ustar G D).card := by
        by_contra hlt
        have hle1 : (Ustar G D).card ≤ 1 := by omega
        by_cases hU0 : (Ustar G D).card = 0
        · omega
        · have hUne : (Ustar G D).Nonempty := Finset.card_pos.mp (by omega)
          have hC0z : (centreless G D).card = 0 := by omega
          have hC0emp : centreless G D = ∅ := Finset.card_eq_zero.mp hC0z
          have hm1 : 1 ≤ (mixing G D).card := hmix_pos hC0emp hUne
          have hm2 : (mixing G D).card ≤ (orN G D \ lam G D).card := Finset.card_le_card hmix_sub
          omega
      have hCnt1 : (tops G D \ centreless G D).card + 2 * (centreless G D).card +
          (orN G D \ lam G D).card ≤ 12 + (Ustar G D).card := by omega
      exact c2 G D g hGeq hDL hDTF hDle64 hg hCnt1 hVC0 hU2
    · have hj2 : 2 ≤ (junk G D).card := by omega
      by_cases hC0emp : centreless G D = ∅
      · have hUpos : 1 ≤ (Ustar G D).card := by
          by_contra h0
          have : (Ustar G D).card = 0 := by omega
          omega
        have hm1 : 1 ≤ (mixing G D).card := hmix_pos hC0emp (Finset.card_pos.mp hUpos)
        have hm2 : (mixing G D).card ≤ (orN G D \ lam G D).card := Finset.card_le_card hmix_sub
        have hU3 : 3 ≤ (Ustar G D).card := by
          by_contra hlt
          have hle2 : (Ustar G D).card ≤ 2 := by omega
          omega
        have hTs : tops G D \ centreless G D = tops G D := by rw [hC0emp, Finset.sdiff_empty]
        have hC0z : (centreless G D).card = 0 := by rw [hC0emp, Finset.card_empty]
        have hCnt3 : (tops G D).card + (junk G D).card + (orN G D \ lam G D).card ≤ 13 + (Ustar G D).card := by
          rw [hTs, hC0z] at hCnt; omega
        have hVC3 : 52 ≤ 4 * (tops G D).card + (Ustar G D).card := by
          rw [hTs] at hVC0; exact hVC0
        have hCov3 : ∀ K : Finset (Fin 26), IsMinCover (G.deleteEdges ↑(Ustar G D)) K → K.card ≤ (tops G D).card := by
          intro K hK; rw [← hTs]; exact hDcov K hK
        exact c3 G D hGeq hDL hDTF hDle64 hC0emp hj2 hm1 hU3 hCnt3 hVC3 hCov3
      · have hC0pos : 1 ≤ (centreless G D).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC0emp)
        have hU4 : 4 ≤ (Ustar G D).card := by
          by_contra hlt
          have hle3 : (Ustar G D).card ≤ 3 := by omega
          omega
        exact c4 G D hGeq hDL hDTF hDle64 hC0pos hj2 hU4 hCnt hVC0 hDcov
