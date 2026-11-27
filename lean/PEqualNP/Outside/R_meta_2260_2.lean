import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2260_2
    (two : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (i j : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → i < j → junk G C = {i,j} → InCone 11 C i j →
      let U := Ustar G C
      let V := centreless G C
      let R := orN G C \ lam G C
      let T := tops G C
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side C a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      C.size = 21 → (T \ V).card = 5 → V = ∅ → U.card = 2 →
      (∀ e ∈ U, ∀ f ∈ U, e ≠ f → ∀ w : Fin 11, w ∈ e → w ∉ f) →
      (∃ m h : ℕ, R = {m} ∧ h ∈ junk G C ∧ 11 + h ∈ (gateAt C m).inputs ∧
        ∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2,
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) m ∧
          gateVal 11 C h (pairInput u v) = true) →
      False)
    (three : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (i j : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → i < j → junk G C = {i,j} → InCone 11 C i j →
      let U := Ustar G C
      let V := centreless G C
      let R := orN G C \ lam G C
      let T := tops G C
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side C a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true) →
      C.size ≤ 21 → U.card = 3 →
      ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K →
      4 ≤ K.card → K.card ≤ (T \ V).card →
      0 < 2 * V.card + R.card → (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 →
      False)
    (many : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (i j : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → junk G C = {i,j} → InCone 11 C i j →
      let U := Ustar G C
      let V := centreless G C
      let R := orN G C \ lam G C
      let T := tops G C
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side C a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true) →
      C.size ≤ 21 → 4 ≤ U.card →
      ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K →
      7 ≤ K.card + U.card → K.card ≤ (T \ V).card →
      0 < 2 * V.card + R.card → (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 →
      False) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x12 ∈ x9,             have x14 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x12;             (∀ x15 ∈ x14 (0 : Fin (2 : ℕ)), ∀ x17 ∈ x14 (1 : Fin (2 : ℕ)), x1.Adj x15 x17) ∧ ((x14 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x14 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x13 x14 : Fin (11 : ℕ)), s(x13, x14) ∈ x11 → ∃ x16 ∈ x9, ∃ (x17 : Fin (2 : ℕ)) (x18 : ℕ), (x18 = x4 ∨ x18 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x16 x17) x18 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x18 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x15 → x15.card ≤ (x9 \ x10).card) → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → (22 : ℕ) ≤ x3.size := by
  intro G inst C i j hG hLeast hTop
  dsimp only
  intro hStars hTrace hCount hCover hJunk hCone
  by_contra hShort
  have hSize : C.size ≤ 21 := by omega
  classical
  let G₀ := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let U := Ustar G C
  let T := tops G C
  let V := centreless G C
  let R := orN G C \ lam G C
  let J := junk G C
  let H := G.deleteEdges (U : Set _)
  change 17 + (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card at hCount
  have fullCover (K : Finset (Fin 11)) (hK : G.IsVertexCover (K : Set _)) :
      7 ≤ K.card := by
    let w (v : Fin 11) : ℕ := if v ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : G₀.Adj u v) : 1 ≤ w u + w v := by
      have huv : G.Adj u v := hG ▸ he
      rcases hK huv with hu | hv
      · change u ∈ K at hu
        simp -congrConsts [w, hu]
      · change v ∈ K at hv
        simp -congrConsts [w, hv]
    have h0 := ew 1 4 (by decide +kernel)
    have h1 := ew 4 8 (by decide +kernel)
    have h2 := ew 8 1 (by decide +kernel)
    have h3 := ew 3 6 (by decide +kernel)
    have h4 := ew 6 7 (by decide +kernel)
    have h5 := ew 7 3 (by decide +kernel)
    have h6 := ew 0 9 (by decide +kernel)
    have h7 := ew 9 5 (by decide +kernel)
    have h8 := ew 5 2 (by decide +kernel)
    have h9 := ew 2 10 (by decide +kernel)
    have h10 := ew 10 0 (by decide +kernel)
    have hw : ∑ v, w v = K.card := by simp -congrConsts [w]
    simp -congrConsts [id (@Fin.sum_univ_succ)] at hw
    omega
  have residual (W : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11))
      (hK : (G.deleteEdges (W : Set _)).IsVertexCover (K : Set _)) :
      7 ≤ K.card + W.card := by
    let A := W.image (fun e => e.out.1)
    have hA : A.card ≤ W.card := Finset.card_image_le
    have hU := Finset.card_union_le K A
    have hfull : G.IsVertexCover ((K ∪ A : Finset (Fin 11)) : Set _) := by
      intro u v huv
      by_cases he : s(u,v) ∈ W
      · have hv := Finset.mem_image_of_mem (fun e : Sym2 (Fin 11) => e.out.1) he
        have hs := Sym2.out_fst_mem s(u,v)
        rw [Sym2.mem_iff] at hs
        rcases hs with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hv))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hv))
      · exact (hK (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩)).imp
          (Finset.mem_union_left A) (Finset.mem_union_left A)
    have hc := fullCover (K ∪ A) hfull
    omega
  let covers := Finset.univ.filter (fun (K : Finset (Fin 11)) => H.IsVertexCover (K : Set _))
  have hCovers : covers.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, fun {_ _} _ => Or.inl (Finset.mem_univ _)⟩⟩
  obtain ⟨K, hK, hMin⟩ := Finset.exists_min_image covers Finset.card hCovers
  have hKMin : IsMinCover H K :=
    ⟨(Finset.mem_filter.mp hK).2, fun A hA =>
      hMin A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
  have hKT : K.card ≤ (T \ V).card := hCover K hKMin
  have hKU := residual U K hKMin.1
  have hU2 : 2 ≤ U.card := by omega
  have hRoutes : (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true) := by
    intro u v huv
    obtain ⟨a, ha, b, h, hh, hval, hr, hhval⟩ := hTrace u v huv
    have hmem : h ∈ J := by
      change h ∈ junk G C
      rw [hJunk]
      simpa -congrConsts only [id (@Finset.mem_insert), id (@Finset.mem_singleton)] using hh
    exact ⟨a, ha, b, h, hmem, hval, hr, hhval⟩

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp -congrConsts only [id (@List.foldl_cons)]
      have hlt : i < (stepWire w g).length := by simp -congrConsts [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp -congrConsts [stepWire, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp -congrConsts [List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp -congrConsts at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp -congrConsts [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp -congrConsts only [id (@List.getElem_cons_zero)]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp -congrConsts [stepWire]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp -congrConsts [stepWire]; omega)]
          simp -congrConsts [stepWire, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa -congrConsts using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp -congrConsts [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp -congrConsts only [id (@List.getElem_cons_succ)]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    delta gateAt
    simp -congrConsts [hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    delta GateOp.eval
    simp -congrConsts only [id (@List.any_map), id (@List.any_eq_true), id (@Function.comp_apply), id (@id_eq)]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  let OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
    ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < n + k

  have coneStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl

  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [coneStep_eq]
      omega

  have cones_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [cones_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp -congrConsts; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp -congrConsts
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_right (by omega)]
          simp -congrConsts [hlen]
        rw [e2, e1]
        simp -congrConsts only [id (@List.mem_flatMap), id (@List.mem_filter), id (@List.mem_cons), id (@decide_eq_true_eq)]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp -congrConsts, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · rintro ⟨h0, _⟩
          simp -congrConsts at h0
          omega

  have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
      InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone n C i k) := by
    have h := cones_char n C.gates i j
    unfold InCone cones gateAt
    rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - n, by omega, ?_, h3⟩
      have : n + (w - n) = w := by omega
      rw [this]
      exact hw
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
      have : n + k - n = k := by omega
      rw [this]
      exact h3

  letI : DecidableEq GateOp := gateOpDecEq
  have orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      orStep n cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := rfl

  have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [orStep_eq]
      omega

  have orSets_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [orSets_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp -congrConsts; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp -congrConsts
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [id (@List.mem_cons), id (@List.mem_flatMap), id (@List.mem_filter), id (@decide_eq_true_eq)]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp -congrConsts, Or.inl h3⟩
            · refine ⟨by simp -congrConsts, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [id (@List.mem_singleton)]
          constructor
          · intro h3
            exact ⟨by simp -congrConsts, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · rintro ⟨h0, _⟩
          simp -congrConsts at h0
          omega

  have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char n C.gates g k
    unfold OrReaches orSets gateAt
    have e : n + k - n = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

  have reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w2) :
      ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

  have orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
      ∀ w, OrReaches n C w g →
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

  have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
      Relation.ReflTransGen (OrStep n C) p u.val := by
    delta orIn at hu
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    delta orIn
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

  have two_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
      ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < n + k ∧ q < n + k ∧ opnd C k 0 = p ∧
        opnd C k 1 = q := by
    obtain ⟨_, hRB, h2⟩ := hA
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
    exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp -congrConsts), hRB k hk q (by rw [hin]; simp -congrConsts),
      by delta opnd; simp -congrConsts [hin], by delta opnd; simp -congrConsts [hin]⟩

  have reach_gate {n : ℕ} {C : Circuit} {k w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) (n + k) w') :
      w' = n + k ∨ (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ Relation.ReflTransGen (OrStep n C) c w') := by
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, hr⟩
    · exact Or.inl h.symm
    · obtain ⟨k', hk', e, hop, hin, hlt⟩ := hstep
      have hkk : k' = k := by omega
      subst hkk
      exact Or.inr ⟨hk', hop, c, hin, hlt, hr⟩

  have orIn_gate {n : ℕ} {C : Circuit} {k : ℕ} (u : Fin n) (hu : u ∈ orIn n C (n + k)) :
      k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ u ∈ orIn n C c := by
    rcases reach_gate (mem_orIn_reach u hu) with h | ⟨hk, hop, c, hc, hlt, hr⟩
    · have := u.isLt
      omega
    · exact ⟨hk, hop, c, hc, hlt, reach_mem_orIn u hr⟩

  have coneStrict : ∀ k h, InCone 11 C h k → h < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro h hh
      obtain ⟨_, p, hp, _, hpath⟩ := (inCone_iff 11 C h k).mp hh
      rcases hpath with rfl | hpath
      · exact hp
      · exact (ih p hp h hpath).trans hp
  have hOrder : i < j := coneStrict j i hCone
  let path := Relation.ReflTransGen (OrStep 11 C)
  have andEmpty (k : ℕ) (hk : (gateAt C k).op = GateOp.and) :
      orIn 11 C (11 + k) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    have hor := (orIn_gate u hu).2.1
    rw [hk] at hor
    cases hor
  have charge (k w : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) (hw : w ∈ (gateAt C k).inputs)
      (he : orIn 11 C w = ∅) (x : Fin 11 → Bool)
      (hd : val C (List.ofFn x) (11 + k) = true) (hx : graphFun G ∅ x = false) :
      k ∈ R := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · delta orN gatesWhere
      simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_range)]
      exact ⟨hk, hop, fun hbelow => Bool.false_ne_true (hx ▸ hbelow x hd)⟩
    · intro hlam
      have hnon := (Finset.mem_filter.mp hlam).2
      obtain ⟨p, q, hpq, _, _, hp, hq⟩ := two_inputs hLeast.1 hk
      rw [hpq] at hw
      simp -congrConsts only [id (@List.mem_cons), id (@List.not_mem_nil), id (@or_false)] at hw
      rcases hw with rfl | rfl
      · exact (Finset.not_nonempty_iff_eq_empty.mpr (hp.symm ▸ he)) hnon.1
      · exact (Finset.not_nonempty_iff_eq_empty.mpr (hq.symm ▸ he)) hnon.2.1
  have nonemptySide (a : ℕ) (ha : a ∈ T) (b : Fin 2) (hn : a ∉ V) :
      (orIn 11 C (opnd C a b)).Nonempty := by
    have hside : side (n := 11) C a b ≠ ∅ := by
      intro he
      apply hn
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    exact Finset.nonempty_iff_ne_empty.mpr hside
  have findCharge (w h : ℕ) (hn : (orIn 11 C w).Nonempty) (hh : h ∈ J)
      (hr : OrReaches 11 C w h) :
      ∃ m ∈ R, path w (11 + m) ∧ 11 + h ∈ (gateAt C m).inputs := by
    obtain ⟨hop, _, x, hval, hx⟩ := (Finset.mem_filter.mp hh).2
    rcases Relation.ReflTransGen.cases_tail (orReaches_reach h w hr).1 with he | ⟨r, hp, hs⟩
    · rw [← he, andEmpty h hop] at hn
      exact (Finset.not_nonempty_empty hn).elim
    · obtain ⟨m, hm, rfl, hor, hread, hlt⟩ := hs
      have hd : val C (List.ofFn x) (11 + m) = true := by
        exact (val_or (by simp -congrConsts) hm hor).mpr ⟨11 + h, hread, hlt, hval⟩
      exact ⟨m, charge m _ hm hor hread (andEmpty h hop) x hd hx, hp, hread⟩
  have offCharge : 0 < 2 * V.card + R.card := by
    by_cases hv : V.Nonempty
    · have := Finset.card_pos.mpr hv
      omega
    · have hv0 := Finset.not_nonempty_iff_eq_empty.mp hv
      obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a, ha, b, h, hh, _, hr, _⟩ := hRoutes u v he
        obtain ⟨m, hm, _, _⟩ := findCharge _ h (nonemptySide a ha b (by simp -congrConsts [hv0])) hh hr
        have := Finset.card_pos.mpr (show R.Nonempty from ⟨m, hm⟩)
        omega
  have hBudget : (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 := by omega
  by_cases hu2 : U.card = 2
  · have hV : V = ∅ := Finset.card_eq_zero.mp (by omega)
    have hR : R.card = 1 := by omega
    obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hR
    have disj : ∀ e ∈ U, ∀ f ∈ U, e ≠ f → ∀ w : Fin 11, w ∈ e → w ∉ f := by
      intro e he f hf hef w hwe hwf
      have hpair : U = {e, f} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro s hs
          simp -congrConsts only [id (@Finset.mem_insert), id (@Finset.mem_singleton)] at hs
          rcases hs with rfl | rfl
          · exact he
          · exact hf
        · simp -congrConsts [hu2, hef]
      have hfull : G.IsVertexCover ((insert w K : Finset (Fin 11)) : Set _) := by
        intro u v huv
        by_cases h : s(u,v) ∈ U
        · have hw : w ∈ s(u,v) := by
            rw [hpair, Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h
            · rwa [h]
            · rwa [h]
          rw [Sym2.mem_iff] at hw
          rcases hw with rfl | rfl
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr (Finset.mem_insert_self _ _)
        · simpa -congrConsts only [id (@Finset.coe_insert), id (@Set.mem_insert_iff)] using
            (hKMin.1 (SimpleGraph.deleteEdges_adj.mpr ⟨huv,h⟩)).imp
              (fun hu => Or.inr hu) (fun hv => Or.inr hv)
      have hc := fullCover (insert w K) hfull
      have hi := Finset.card_insert_le w K
      omega
    have junction (u v : Fin 11) (he : s(u,v) ∈ U) :
        ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true ∧ path (opnd C a b) (11 + m) ∧
          11 + h ∈ (gateAt C m).inputs := by
      obtain ⟨a, ha, b, h, hh, hv, hr, hhval⟩ := hRoutes u v he
      obtain ⟨k, hk, hpath, hread⟩ :=
        findCharge _ h (nonemptySide a ha b (by simp -congrConsts [hV])) hh hr
      have eq : k = m := by simpa -congrConsts only [hm, id (@Finset.mem_singleton)] using hk
      subst k
      exact ⟨a, ha, b, h, hh, hv, hr, hhval, hpath, hread⟩
    have singletonSource : ∃ h ∈ J, 11 + h ∈ (gateAt C m).inputs ∧
        ∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2,
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) m ∧
          OrReaches 11 C (opnd C a b) h ∧ gateVal 11 C h (pairInput u v) = true := by
      obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a, ha, b, h, hh, _, _, _, hp, hread⟩ := junction u v he
        have hmem : m ∈ R := by simp -congrConsts [hm]
        have hdata : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
          have ho := (Finset.mem_sdiff.mp hmem).1
          change m ∈ orN G C at ho
          delta orN gatesWhere at ho
          simpa -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_range)] using ho
        obtain ⟨hlen, ho, _⟩ := hdata
        have hmOr : (orIn 11 C (11 + m)).Nonempty := by
          by_contra hno
          have hme := Finset.not_nonempty_iff_eq_empty.mp hno
          rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨w, _, hs⟩
          · have hn := nonemptySide a ha b (by simp -congrConsts [hV])
            rw [← heq, hme] at hn
            exact Finset.not_nonempty_empty hn
          · obtain ⟨k, hk, rfl, hkop, hkmem, hklt⟩ := hs
            obtain ⟨_, _, x, hd, hx⟩ := (Finset.mem_filter.mp hh).2
            have hmv : val C (List.ofFn x) (11 + m) = true :=
              (val_or (by simp -congrConsts) hlen ho).mpr
                ⟨11 + h, hread, hLeast.1.2.1 m hlen _ hread, hd⟩
            have hkv : val C (List.ofFn x) (11 + k) = true :=
              (val_or (by simp -congrConsts) hk hkop).mpr ⟨11 + m, hkmem, hklt, hmv⟩
            have hkR := charge k _ hk hkop hkmem hme x hkv hx
            have : k = m := by simpa -congrConsts only [hm, id (@Finset.mem_singleton)] using hkR
            omega
        have huniq (h' : ℕ) (hh' : h' ∈ J) (hd : 11 + h' ∈ (gateAt C m).inputs) : h' = h := by
          by_contra hne
          obtain ⟨p, q, hpq, _, _, _, _⟩ := two_inputs hLeast.1 hlen
          have he1 := andEmpty h (Finset.mem_filter.mp hh).2.1
          have he2 := andEmpty h' (Finset.mem_filter.mp hh').2.1
          have hshape : (gateAt C m).inputs = [11+h,11+h'] ∨
              (gateAt C m).inputs = [11+h',11+h] := by
            rw [hpq] at hread hd
            simp -congrConsts only [id (@List.mem_cons), id (@List.not_mem_nil), id (@or_false)] at hread hd
            rcases hread with he | he <;> rcases hd with he' | he'
            · omega
            · exact Or.inl (by rw [hpq, ← he, ← he'])
            · exact Or.inr (by rw [hpq, ← he', ← he])
            · omega
          obtain ⟨t, ht⟩ := hmOr
          obtain ⟨_, _, w, hw, _, htw⟩ := orIn_gate t ht
          rcases hshape with he | he <;> rw [he] at hw <;>
            simp -congrConsts only [id (@List.mem_cons), id (@List.not_mem_nil), id (@or_false)] at hw <;>
            rcases hw with rfl | rfl <;> simp -congrConsts [he1, he2] at htw
        refine ⟨h, hh, hread, ?_⟩
        intro u' v' he'
        obtain ⟨a', ha', b', h', hh', hv, hr, hvh, hp', hd⟩ := junction u' v' he'
        have heq := huniq h' hh' hd
        subst h'
        exact ⟨a', ha', b', hv, reach_orReaches hp' m rfl hlen, hr, hvh⟩
    obtain ⟨h, hh, hread, hroute⟩ := singletonSource
    refine two G C i j (by exact hG) hLeast hTop hOrder hJunk hCone hStars
      (by omega) (show (T \ V).card = 5 by omega) hV hu2 disj ⟨m, h, hm, hh, hread, ?_⟩
    intro u v he
    obtain ⟨a, ha, b, hv, hr, _, hhval⟩ := hroute u v he
    exact ⟨a, ha, b, hv, hr, hhval⟩
  · by_cases hu3 : U.card = 3
    · exact three G C i j (by exact hG) hLeast hTop hOrder hJunk hCone hStars hRoutes hSize hu3
        K hKMin (by omega) hKT offCharge hBudget
    · exact many G C i j (by exact hG) hLeast hTop hJunk hCone hStars hRoutes hSize (show 4 ≤ U.card by omega)
        K hKMin hKU hKT offCharge hBudget

