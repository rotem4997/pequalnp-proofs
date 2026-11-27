import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.CircuitMoves

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_5997_2
    (hNorm : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin (26 : ℕ) => a.val < (13 : ℕ) ∧ (13 : ℕ) ≤ b.val ∧ a.val ≠ (0 : ℕ) ∧ (a.val + (26 : ℕ) - b.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO G C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D ∧ D.size = C.size ∧ PEqualNP.TopForm.TopForm G D)
    (hOneJunk : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin (26 : ℕ) => a.val < (13 : ℕ) ∧ (13 : ℕ) ≤ b.val ∧ a.val ≠ (0 : ℕ) ∧ (a.val + (26 : ℕ) - b.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.junk G C).card = (1 : ℕ) →
      (59 : ℕ) ≤ C.size)
    (hLowSurcharge : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin (26 : ℕ) => a.val < (13 : ℕ) ∧ (13 : ℕ) ≤ b.val ∧ a.val ≠ (0 : ℕ) ∧ (a.val + (26 : ℕ) - b.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
      (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ (3 : ℕ) →
      (59 : ℕ) ≤ C.size)
    (hHighSurcharge : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin (26 : ℕ) => a.val < (13 : ℕ) ∧ (13 : ℕ) ≤ b.val ∧ a.val ≠ (0 : ℕ) ∧ (a.val + (26 : ℕ) - b.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
      (4 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card →
      (59 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  intro x1 hx1_ao hx1_spec
  let stepWire : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_and_def : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or_def : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have wires_def : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl stepWire x := fun _ _ => rfl
  have size_def : ∀ D : Circuit, D.size = D.gates.length := fun _ => rfl
  have eval_def : ∀ (D : Circuit) (x : List Bool), D.eval x = (D.wires x).getD D.output false := fun _ _ => rfl
  have circuitFun_def : ∀ (n : ℕ) (D : Circuit) (x : Fin n → Bool), circuitFun n D x = D.eval (List.ofFn x) := fun _ _ _ => rfl
  have gateAt_def : ∀ (D : Circuit) (j : ℕ), gateAt D j = D.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have opnd_def : ∀ (D : Circuit) (a : ℕ) (b : Fin 2), opnd D a b = (gateAt D a).inputs.getD b.val 0 := fun _ _ _ => rfl
  have pairInput_def : ∀ (u v w : Fin 26), pairInput u v w = decide (w = u ∨ w = v) := fun _ _ _ => rfl
  have cones_def : ∀ (n : ℕ) (C : Circuit), cones n C = C.gates.foldl (coneStep n) [] := fun _ _ => rfl
  have coneStep_def : ∀ (n : ℕ) (cs : List (List ℕ)) (g : Gate),
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ _ => rfl
  have eraseGate_pos : ∀ (n : ℕ) (D : Circuit) (m p : ℕ), m < D.gates.length →
      eraseGate n D m p = ⟨D.gates.take m ++ (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩), eraseRedirect n m p D.output⟩ := by
    intro n D m p hm
    change (if m < D.gates.length then ⟨D.gates.take m ++ (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩), eraseRedirect n m p D.output⟩ else D) = _
    simp only [hm, ↓reduceIte]
  have mem_gatesWhere_iff : ∀ (D : Circuit) (P : ℕ → Prop) [DecidablePred P] (j : ℕ),
      j ∈ gatesWhere D P ↔ j < D.gates.length ∧ P j := by
    intro D P _ j
    change j ∈ (Finset.range D.gates.length).filter P ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
  have mem_tops_iff : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Circuit) (j : ℕ),
      j ∈ tops G D ↔ j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧ BelowF G D j :=
    fun G _ D j => mem_gatesWhere_iff D _ j
  have mem_orT_iff : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Circuit) (j : ℕ),
      j ∈ orT G D ↔ j < D.gates.length ∧ (gateAt D j).op = GateOp.or ∧ BelowF G D j :=
    fun G _ D j => mem_gatesWhere_iff D _ j
  have mem_orN_iff : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Circuit) (j : ℕ),
      j ∈ orN G D ↔ j < D.gates.length ∧ (gateAt D j).op = GateOp.or ∧ ¬ BelowF G D j :=
    fun G _ D j => mem_gatesWhere_iff D _ j
  have graphFun_empty_iff : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (x : Fin 26 → Bool),
      graphFun G ∅ x = true ↔ ∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro G _ x
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) || decide (∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  have graphFun_empty_false : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (x : Fin 26 → Bool),
      graphFun G ∅ x = false ↔ ¬ ∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro G _ x
    rw [Bool.eq_false_iff, ne_eq, graphFun_empty_iff G x]
  let G0 : SimpleGraph (Fin 26) :=
    SimpleGraph.fromRel fun a b : Fin 26 =>
      a.val < 13 ∧ 13 ≤ b.val ∧ a.val ≠ 0 ∧ (a.val + 26 - b.val) % 13 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]
  let adjB : ℕ → ℕ → Bool := fun a b =>
    (decide (a < 13) && decide (13 ≤ b) && decide (a ≠ 0) && ([0, 1, 3, 9].contains ((a + 26 - b) % 13))) ||
    (decide (b < 13) && decide (13 ≤ a) && decide (b ≠ 0) && ([0, 1, 3, 9].contains ((b + 26 - a) % 13)))
  have hadj_iff : ∀ u v : Fin 26, G0.Adj u v ↔ adjB u.val v.val = true := by
    intro u v
    simp only [G0, SimpleGraph.fromRel_adj, adjB, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, and_assoc]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨?_, h⟩
      intro heq
      subst heq
      rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega
  have hx1_fun : circuitFun 26 x1 = graphFun G0 ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [circuitFun_def, graphFun_empty_iff]
    rw [hx1_spec x]
    constructor
    · rintro ⟨p, l, hinc, hp0, hxp, hxl⟩
      refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, ?_, hxp, hxl⟩
      rw [hadj_iff]
      have hsub_lem : ∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
          ((p.val + 26 - (13 + l.val)) % 13) ∈ ([0, 1, 3, 9] : List ℕ) := by
        decide +kernel
      have hsub := hsub_lem p l hinc
      have hpne : p.val ≠ 0 := fun h => hp0 (Fin.ext h)
      simp only [adjB, Fin.val_castAdd, Fin.val_natAdd, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, List.contains_eq_mem]
      left
      exact ⟨⟨⟨p.isLt, by omega⟩, hpne⟩, hsub⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      rw [hadj_iff] at huv
      simp only [adjB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.contains_eq_mem] at huv
      have hdiff : ∀ p l : Fin 13, ((p.val + 26 - (13 + l.val)) % 13) ∈ ([0, 1, 3, 9] : List ℕ) →
          p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := by decide +kernel
      rcases huv with ⟨⟨⟨hu13, hv13⟩, hune⟩, hmem⟩ | ⟨⟨⟨hv13, hu13⟩, hvne⟩, hmem⟩
      · refine ⟨⟨u.val, hu13⟩, ⟨v.val - 13, by omega⟩, hdiff _ _ (by simpa [show 13 + (v.val - 13) = v.val by omega] using hmem), fun h => hune (congrArg Fin.val h), ?_, ?_⟩
        · have hu_eq : Fin.castAdd 13 (⟨u.val, hu13⟩ : Fin 13) = u := Fin.ext rfl
          rwa [hu_eq]
        · have hv_eq : Fin.natAdd 13 (⟨v.val - 13, by omega⟩ : Fin 13) = v := Fin.ext (by rw [Fin.val_natAdd]; dsimp only; omega)
          rwa [hv_eq]
      · refine ⟨⟨v.val, hv13⟩, ⟨u.val - 13, by omega⟩, hdiff _ _ (by simpa [show 13 + (u.val - 13) = u.val by omega] using hmem), fun h => hvne (congrArg Fin.val h), ?_, ?_⟩
        · have hv_eq : Fin.castAdd 13 (⟨v.val, hv13⟩ : Fin 13) = v := Fin.ext rfl
          rwa [hv_eq]
        · have hu_eq : Fin.natAdd 13 (⟨u.val - 13, by omega⟩ : Fin 13) = u := Fin.ext (by rw [Fin.val_natAdd]; dsimp only; omega)
          rwa [hu_eq]
  let hasCirc : ℕ → Prop := fun k => ∃ D : Circuit, IsAO2 26 D ∧ circuitFun 26 D = graphFun G0 ∅ ∧ D.size = k
  have hex : ∃ k, hasCirc k := ⟨x1.size, x1, hx1_ao, hx1_fun, rfl⟩
  obtain ⟨C0, hC0_ao, hC0_fun, hC0_sz⟩ := Nat.find_spec hex
  have hC0_least : IsLeastAO G0 C0 :=
    ⟨hC0_ao, hC0_fun, fun D hD hDf => hC0_sz ▸ Nat.find_min' hex ⟨D, hD, hDf, rfl⟩⟩
  have hC0_le : C0.size ≤ x1.size := hC0_sz ▸ Nat.find_min' hex ⟨x1, hx1_ao, hx1_fun, rfl⟩
  obtain ⟨C, hL, hC_sz, hT⟩ := hNorm G0 C0 rfl hC0_least
  suffices h59 : 59 ≤ C.size by omega
  by_cases hj1 : (junk G0 C).card = 1
  · exact hOneJunk G0 C rfl hL hT hj1
  by_cases hj2 : 2 ≤ (junk G0 C).card
  · by_cases hsur : 2 * (centreless G0 C).card + (junk G0 C).card + (orN G0 C \ lam G0 C).card ≤ 3
    · exact hLowSurcharge G0 C rfl hL hT hj2 hsur
    · exact hHighSurcharge G0 C rfl hL hT hj2 (by omega)
  have hj0 : (junk G0 C).card = 0 := by omega
  have hj_empty : junk G0 C = ∅ := Finset.card_eq_zero.mp hj0
  have hno_junk : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G0 C j := by
    intro j hj hop
    by_contra hnb
    have hdirty : IsDirtyAnd 26 G0 C j := by
      refine ⟨hop, hj, ?_⟩
      exact Classical.byContradiction fun hno =>
        hnb fun x hx => Bool.eq_true_of_not_eq_false fun hf => hno ⟨x, hx, hf⟩
    have hjmem : j ∈ junk G0 C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hdirty⟩
    rw [hj_empty] at hjmem
    exact Finset.notMem_empty j hjmem
  have hcountP26 : ∀ p : ℕ → Bool,
      (Finset.univ.filter fun w : Fin 26 => p w.val = true).card = (List.range 26).countP p := by
    intro p
    rw [List.countP_eq_length_filter]
    have h1 : (Finset.univ.filter fun w : Fin 26 => p w.val = true).card =
        ((List.finRange 26).filter fun w : Fin 26 => p w.val).length := by
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 26).filter _)]
      congr 1
      ext w
      simp
    rw [h1]
    have hmap : List.range 26 = (List.finRange 26).map Fin.val := by
      apply List.ext_getElem <;> simp
    rw [hmap, List.filter_map, List.length_map]
    rfl
  have hnoC4 : NoFourCycle G0 := by
    have hchk : (List.range 26).all (fun a => (List.range 26).all fun b =>
        decide (a = b) || decide (((List.range 26).countP fun w => adjB a w && adjB b w) ≤ 1)) = true := by
      decide +kernel
    intro a b hab
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hchk
    have hne : a.val ≠ b.val := fun he => hab (Fin.ext he)
    have h1 := (hchk a.val a.isLt b.val b.isLt).resolve_left hne
    have heq : (Finset.univ.filter fun w : Fin 26 => G0.Adj a w ∧ G0.Adj b w) =
        (Finset.univ.filter fun w : Fin 26 => (adjB a.val w.val && adjB b.val w.val) = true) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hadj_iff, Bool.and_eq_true]
    rw [heq, hcountP26 (fun w => adjB a.val w && adjB b.val w)]
    exact h1
  have hedgeCard : G0.edgeFinset.card = 48 := by
    let S : Finset (Fin 26 × Fin 26) := Finset.univ.filter fun p => p.1.val < 13 ∧ adjB p.1.val p.2.val = true
    let f : Fin 26 × Fin 26 → Sym2 (Fin 26) := fun p => s(p.1, p.2)
    have hinj : Set.InjOn f S := by
      intro p1 hp1 p2 hp2 h
      simp only [f, Sym2.eq_iff] at h
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        have ha1 := hp1.2
        simp only [adjB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha1
        have hp11 : p1.1.val < 13 := hp1.1
        rcases ha1 with ⟨⟨⟨_, hv1⟩, _⟩, _⟩ | ⟨⟨⟨_, hu1⟩, _⟩, _⟩
        · have : p1.2.val < 13 := by rw [h2]; exact hp2.1
          omega
        · omega
    have himg : S.image f = G0.edgeFinset := by
      ext e
      obtain ⟨⟨u, v⟩, huv_eq⟩ := Quot.exists_rep e
      have he_eq : e = s(u, v) := huv_eq.symm
      rw [he_eq]
      simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset, S, Finset.mem_filter,
        Finset.mem_univ, true_and, f]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨_, hab⟩, heq⟩
        rw [← heq]; simp only [SimpleGraph.mem_edgeSet, hadj_iff]; exact hab
      · intro huv
        rw [SimpleGraph.mem_edgeSet, hadj_iff] at huv
        have hbip : adjB u.val v.val = true → u.val < 13 ∨ v.val < 13 := by
          simp only [adjB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rintro (⟨⟨⟨h, _⟩, _⟩, _⟩ | ⟨⟨⟨h, _⟩, _⟩, _⟩)
          · exact Or.inl h
          · exact Or.inr h
        rcases hbip huv with hu | hv
        · exact ⟨(u, v), ⟨hu, huv⟩, rfl⟩
        · have hvu : adjB v.val u.val = true := (hadj_iff v u).mp ((hadj_iff u v).mpr huv).symm
          exact ⟨(v, u), ⟨hv, hvu⟩, Sym2.eq_swap⟩
    rw [← himg, Finset.card_image_of_injOn hinj]
    let S_list : List (ℕ × ℕ) :=
      (List.range 13).flatMap fun a => ((List.range 26).filter fun b => adjB a b).map fun b => (a, b)
    have hS_mem : ∀ p ∈ S_list, p.1 < 13 ∧ p.2 < 26 ∧ adjB p.1 p.2 = true := by
      intro p hp
      simp only [S_list, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter] at hp
      rcases hp with ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
      exact ⟨ha, hb, hab⟩
    let S_fin : List (Fin 26 × Fin 26) :=
      S_list.pmap (fun p h => (⟨p.1, by omega⟩, ⟨p.2, by omega⟩)) hS_mem
    have hL_nodup : S_list.Nodup := by decide +kernel
    have hS_nodup : S_fin.Nodup :=
      hL_nodup.pmap fun p1 _ p2 _ he => Prod.ext
        (congrArg Fin.val (Prod.ext_iff.mp he).1)
        (congrArg Fin.val (Prod.ext_iff.mp he).2)
    have hS_eq : S = S_fin.toFinset := by
      ext ⟨u, v⟩
      simp only [S, S_fin, List.mem_toFinset, List.mem_pmap, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hu, huv⟩
        refine ⟨(u.val, v.val), ?_, Prod.ext rfl rfl⟩
        simp only [S_list, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter]
        exact ⟨u.val, hu, v.val, ⟨v.isLt, huv⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, hab, hpair⟩
        obtain ⟨ha, hb, hab_adj⟩ := hS_mem (a, b) hab
        have hu : u.val = a := congrArg Fin.val (Prod.ext_iff.mp hpair).1.symm
        have hv : v.val = b := congrArg Fin.val (Prod.ext_iff.mp hpair).2.symm
        rw [hu, hv]
        exact ⟨ha, hab_adj⟩
    rw [hS_eq, List.toFinset_card_of_nodup hS_nodup, List.length_pmap]
    exact (by decide +kernel : S_list.length = 48)
  have hcover12 : ∀ K : Finset (Fin 26), (∀ u v : Fin 26, G0.Adj u v → u ∈ K ∨ v ∈ K) → 12 ≤ K.card := by
    intro K hK
    let mp : Fin 12 → Fin 26 := fun p => ⟨p.val + 1, by omega⟩
    let ml : Fin 12 → Fin 26 := fun p => ⟨14 + p.val, by omega⟩
    have hadj_m : ∀ p : Fin 12, G0.Adj (mp p) (ml p) := by
      intro p
      rw [hadj_iff]
      have : ∀ q : Fin 12, adjB (q.val + 1) (14 + q.val) = true := by decide +kernel
      exact this p
    let g : Fin 12 → Fin 26 := fun p => if mp p ∈ K then mp p else ml p
    have hgK : ∀ p : Fin 12, g p ∈ K := by
      intro p
      dsimp only [g]
      split_ifs with h
      · exact h
      · exact (hK (mp p) (ml p) (hadj_m p)).resolve_left h
    have hginj : Function.Injective g := by
      intro p1 p2 heq
      have hp1 := p1.isLt
      have hp2 := p2.isLt
      have hval := congrArg Fin.val heq
      dsimp only [g, mp, ml] at hval
      split_ifs at hval <;> (dsimp only at hval; exact Fin.ext (by omega))
    calc 12 = (Finset.univ : Finset (Fin 12)).card := (Finset.card_fin 12).symm
      _ = ((Finset.univ : Finset (Fin 12)).image g).card := (Finset.card_image_of_injective _ hginj).symm
      _ ≤ K.card := Finset.card_le_card (fun x hx => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
          exact hgK p)

  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepWire]; omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (stepWire w g) i (by simp [stepWire]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length (by simp [stepWire])]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · simp only [hi, ↓reduceIte]
          rw [foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp only [hi, ↓reduceIte]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  let val : Circuit → List Bool → ℕ → Bool := fun D x u => (D.wires x).getD u false
  have hgateAt_mem : ∀ (D : Circuit) (k : ℕ), k < D.gates.length → gateAt D k ∈ D.gates := by
    intro D k hk
    rw [gateAt_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have val_input : ∀ (D : Circuit) (x : Fin 26 → Bool) (u : ℕ) (hu : u < 26),
      val D (List.ofFn x) u = x ⟨u, hu⟩ := by
    intro D x u hu
    dsimp only [val]; rw [wires_def]
    rw [foldl_getD_lt _ _ _ (by simpa using hu)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hu]
    rfl
  have val_ge : ∀ (D : Circuit) (x : Fin 26 → Bool) (u : ℕ), 26 + D.gates.length ≤ u →
      val D (List.ofFn x) u = false := by
    intro D x u hu
    dsimp only [val]; rw [wires_def]
    apply getD_ge
    rw [foldl_len, List.length_ofFn]
    omega
  have val_gate : ∀ (D : Circuit) (x : Fin 26 → Bool) (j : ℕ), j < D.gates.length →
      val D (List.ofFn x) (26 + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map fun i =>
        if i < 26 + j then val D (List.ofFn x) i else false) := by
    intro D x j hj
    have h1 := foldl_getD_gate D.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at h1
    have hg : gateAt D j = D.gates[j] := by
      rw [gateAt_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hg]
    exact h1
  have val_or : ∀ (D : Circuit), IsAO2 26 D → ∀ (x : Fin 26 → Bool) (j : ℕ),
      j < D.gates.length → (gateAt D j).op = GateOp.or →
      (val D (List.ofFn x) (26 + j) = true ↔
        val D (List.ofFn x) (opnd D j 0) = true ∨ val D (List.ofFn x) (opnd D j 1) = true) := by
    intro D hD x j hj hop
    have hmem : gateAt D j ∈ D.gates := hgateAt_mem D j hj
    have hlen : (gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have ha : a < 26 + j := hD.2.1 j hj a (by rw [hab]; simp)
    have hb : b < 26 + j := hD.2.1 j hj b (by rw [hab]; simp)
    have e0 : opnd D j 0 = a := by simp [opnd_def, hab]
    have e1 : opnd D j 1 = b := by simp [opnd_def, hab]
    rw [val_gate D x j hj, hop, hab, e0, e1, eval_or_def]
    simp [ha, hb]
  have val_and : ∀ (D : Circuit), IsAO2 26 D → ∀ (x : Fin 26 → Bool) (j : ℕ),
      j < D.gates.length → (gateAt D j).op = GateOp.and →
      (val D (List.ofFn x) (26 + j) = true ↔
        val D (List.ofFn x) (opnd D j 0) = true ∧ val D (List.ofFn x) (opnd D j 1) = true) := by
    intro D hD x j hj hop
    have hmem : gateAt D j ∈ D.gates := hgateAt_mem D j hj
    have hlen : (gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have ha : a < 26 + j := hD.2.1 j hj a (by rw [hab]; simp)
    have hb : b < 26 + j := hD.2.1 j hj b (by rw [hab]; simp)
    have e0 : opnd D j 0 = a := by simp [opnd_def, hab]
    have e1 : opnd D j 1 = b := by simp [opnd_def, hab]
    rw [val_gate D x j hj, hop, hab, e0, e1, eval_and_def]
    simp [ha, hb]
  have erase_props : ∀ (D : Circuit) (j p : ℕ), IsAO2 26 D → j < D.gates.length → p < 26 + j →
      (eraseGate 26 D j p).size + 1 = D.size ∧
      IsAO2 26 (eraseGate 26 D j p) ∧
      (∀ (x : Fin 26 → Bool),
        (val D (List.ofFn x) (26 + j) = val D (List.ofFn x) p ∨
          (D.output ≠ 26 + j ∧ ∀ k, j < k → k < D.gates.length → 26 + j ∉ (gateAt D k).inputs)) →
        (eraseGate 26 D j p).eval (List.ofFn x) = D.eval (List.ofFn x)) := by
    intro D j p hD hj hp
    have hlen : (eraseGate 26 D j p).gates.length + 1 = D.gates.length := by
      rw [eraseGate_pos 26 D j p hj]; simp; omega
    have hAO_er : IsAO2 26 (eraseGate 26 D j p) := by
      rw [eraseGate_pos 26 D j p hj]
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_map] at hg
        rcases hg with hg | ⟨g0, hg0, rfl⟩
        · exact hD.1 g (List.mem_of_mem_take hg)
        · exact hD.1 g0 (List.mem_of_mem_drop hg0)
      · intro k hk i hi
        simp only [List.length_append, List.length_take, List.length_map, List.length_drop] at hk
        by_cases hkj : k < j
        · have hgate : gateAt ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 26 j p)⟩), eraseRedirect 26 j p D.output⟩ k = gateAt D k := by
            rw [gateAt_def, gateAt_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hkj]
          rw [hgate] at hi
          exact hD.2.1 k (by omega) i hi
        · have hgate : gateAt ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 26 j p)⟩), eraseRedirect 26 j p D.output⟩ k =
              ⟨(gateAt D (k + 1)).op, (gateAt D (k + 1)).inputs.map (eraseRedirect 26 j p)⟩ := by
            rw [gateAt_def, gateAt_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by simp; omega)]
            have ht : (D.gates.take j).length = j := by simp; omega
            rw [ht, List.getElem?_map, List.getElem?_drop, show j + 1 + (k - j) = k + 1 by omega,
              List.getElem?_eq_getElem (by omega)]
            rfl
          rw [hgate] at hi
          simp only [List.mem_map] at hi
          obtain ⟨u, hu, rfl⟩ := hi
          have hu_lt := hD.2.1 (k + 1) (by omega) u hu
          unfold eraseRedirect
          split_ifs with heq hgt <;> omega
      · intro g hg
        simp only [List.mem_append, List.mem_map] at hg
        rcases hg with hg | ⟨g0, hg0, rfl⟩
        · exact hD.2.2 g (List.mem_of_mem_take hg)
        · simp [hD.2.2 g0 (List.mem_of_mem_drop hg0)]
    refine ⟨hlen, hAO_er, fun x hx => ?_⟩
    let pre := D.gates.take j
    let post := D.gates.drop (j + 1)
    let gj := D.gates[j]
    have hgs : D.gates = pre ++ gj :: post := by
      simp only [pre, post, gj]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hpre_len : pre.length = j := by simp [pre]; omega
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = 26 + j := by
      simp [w0, foldl_len, hpre_len]
    let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
    let shiftDown : ℕ → ℕ := fun u => if 26 + j < u then u - 1 else u
    let wiresMatch : List Bool → List Bool → Prop := fun wC wD =>
      wC.length = wD.length + 1 ∧
      w0.length ≤ wD.length ∧
      wC.getD w0.length false = bOld ∧
      (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
      (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
      (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)
    have hm0 : wiresMatch (stepWire w0 gj) w0 := by
      refine ⟨by simp [stepWire], le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
      · simp [stepWire, List.getD_eq_getElem?_getD, bOld]
      · intro u hu; simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
      · intro u hu
        rw [getD_ge w0 (u - 1) (by omega), getD_ge (stepWire w0 gj) u (by simp [stepWire]; omega)]
    have hm_step : ∀ {wC wD : List Bool} {b : Bool}, wiresMatch wC wD →
        wiresMatch (wC ++ [b]) (wD ++ [b]) := by
      intro wC wD b hm
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm
      refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        simpa [List.getD_eq_getElem?_getD] using h3
      · intro u hu
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        simpa [List.getD_eq_getElem?_getD] using h4 u hu
      · intro u hu
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        simpa [List.getD_eq_getElem?_getD] using h5 u hu
      · intro u hu
        by_cases hlt : u - 1 < wD.length
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hlt, List.getElem?_append_left (by omega)]
          simpa [List.getD_eq_getElem?_getD] using h6 u hu
        · by_cases heq : u - 1 = wD.length
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq,
              show u = wC.length by omega, List.getElem?_append_right le_rfl,
              List.getElem?_append_right le_rfl]
            simp
          · rw [getD_ge (wD ++ [b]) (u - 1) (by simp; omega), getD_ge (wC ++ [b]) u (by simp; omega)]
    have hCi : val D (List.ofFn x) p = w0.getD p false := by
      dsimp only [val]; rw [wires_def]
      rw [hgs, List.foldl_append]
      exact foldl_getD_lt (gj :: post) w0 p (by omega)
    have hCj : val D (List.ofFn x) (26 + j) = bOld := by
      dsimp only [val]; rw [wires_def]
      rw [hgs, List.foldl_append, List.foldl_cons, foldl_getD_lt post (stepWire w0 gj) (26 + j) (by simp [stepWire]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
    have halias_get : ∀ {vC vD : List Bool}, wiresMatch vC vD → ∀ u,
        (u = 26 + j → val D (List.ofFn x) (26 + j) = val D (List.ofFn x) p) →
        vD.getD (eraseRedirect 26 j p u) false = vC.getD u false := by
      intro vC vD hmv u hu
      unfold eraseRedirect
      by_cases heq : u = 26 + j
      · have hv : w0.getD p false = bOld := by rw [← hCi, ← hCj]; exact (hu heq).symm
        subst heq
        simp only [↓reduceIte]
        rw [hmv.2.2.2.1 p (by omega), hv, ← hw0_len, hmv.2.2.1]
      · simp only [heq, ↓reduceIte]
        by_cases hgt : 26 + j < u
        · simp only [hgt, ↓reduceIte]
          rw [← hw0_len] at hgt
          exact hmv.2.2.2.2.2 u hgt
        · simp only [hgt, ↓reduceIte]
          have hlt : u < w0.length := by omega
          rw [hmv.2.2.2.1 u hlt, hmv.2.2.2.2.1 u hlt]
    have hfold : ∀ (k : ℕ) (gsC : List Gate), gsC.length = post.length - k →
        post.drop k = gsC →
        ∀ vC vD : List Bool, wiresMatch vC vD →
        wiresMatch (gsC.foldl stepWire vC)
          ((gsC.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 26 j p)⟩)).foldl stepWire vD) := by
      intro k gsC
      induction gsC generalizing k with
      | nil => intro _ _ vC vD hmv; exact hmv
      | cons gC restC ih =>
        intro hlen_eq hdrop vC vD hmv
        simp only [List.map_cons, List.foldl_cons]
        have hk_lt : k < post.length := by
          have := congrArg List.length hdrop
          simp at this
          omega
        have hg_eq : gateAt D (j + 1 + k) = gC := by
          have hget_opt : D.gates[j + 1 + k]? = some gC := by
            have h1 : (D.gates.drop (j + 1)).drop k = gC :: restC := hdrop
            rw [List.drop_drop, Nat.add_comm (j + 1) k] at h1
            have h2 := congrArg (fun l : List Gate => l[0]?) h1
            rw [Nat.add_comm (j + 1) k]
            simpa [List.getElem?_drop] using h2
          rw [gateAt_def, List.getD_eq_getElem?_getD, hget_opt]; rfl
        have hstep_eq : gC.op.eval ((gC.inputs.map (eraseRedirect 26 j p)).map fun i => vD.getD i false) =
            gC.op.eval (gC.inputs.map fun i => vC.getD i false) := by
          congr 1
          rw [List.map_map]
          refine List.map_congr_left fun u hu => ?_
          refine halias_get hmv u ?_
          intro hu_eq
          rcases hx with heq | ⟨_, hno⟩
          · exact heq
          · exfalso
            exact hno (j + 1 + k) (by omega) (by have := congrArg List.length hgs; simp at this; omega)
              (by rw [hg_eq, ← hu_eq]; exact hu)
        unfold stepWire
        rw [hstep_eq]
        have hrest : post.drop (k + 1) = restC := by
          have h1 := congrArg (fun l : List Gate => l.drop 1) hdrop
          simpa [List.drop_drop] using h1
        have hlen_rest : restC.length = post.length - (k + 1) := by
          rw [← hrest, List.length_drop]
        exact ih (k + 1) hlen_rest hrest _ _ (hm_step hmv)
    have hmEnd := hfold 0 post (by simp) (by simp) (stepWire w0 gj) w0 hm0
    have heq_D : D.wires (List.ofFn x) = post.foldl stepWire (stepWire w0 gj) := by
      rw [wires_def]
      conv_lhs => rw [hgs, List.foldl_append, List.foldl_cons]
    have heq_E : (eraseGate 26 D j p).wires (List.ofFn x) =
        (post.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 26 j p)⟩)).foldl stepWire w0 := by
      rw [eraseGate_pos 26 D j p hj, wires_def]
      rw [List.foldl_append]
    rw [eval_def, eval_def, heq_E, heq_D, eraseGate_pos 26 D j p hj]
    refine halias_get hmEnd D.output ?_
    intro ho
    rcases hx with heq | ⟨hne, _⟩
    · exact heq
    · exact absurd ho hne
  let appOr : Circuit → ℕ → ℕ → Circuit :=
    fun D a b => ⟨D.gates ++ [⟨GateOp.or, [a, b]⟩], 26 + D.gates.length⟩
  have appOr_props : ∀ (D : Circuit) (a b : ℕ), IsAO2 26 D → a < 26 + D.gates.length → b < 26 + D.gates.length →
      (appOr D a b).size = D.size + 1 ∧
      IsAO2 26 (appOr D a b) ∧
      (∀ (x : Fin 26 → Bool), (appOr D a b).eval (List.ofFn x) = (val D (List.ofFn x) a || val D (List.ofFn x) b)) ∧
      (∀ (x : Fin 26 → Bool) (u : ℕ), u < 26 + D.gates.length →
        val (appOr D a b) (List.ofFn x) u = val D (List.ofFn x) u) := by
    intro D a b hD ha hb
    refine ⟨by rw [size_def, size_def]; simp [appOr], ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [appOr, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hD.1 g hg
        · exact Or.inr rfl
      · intro k hk i hi
        simp only [appOr, List.length_append, List.length_singleton] at hk
        by_cases hlt : k < D.gates.length
        · have hg : gateAt (appOr D a b) k = gateAt D k := by
            rw [gateAt_def, gateAt_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]; simp [appOr, List.getElem?_append_left hlt]
          rw [hg] at hi
          exact hD.2.1 k hlt i hi
        · have hk_eq : k = D.gates.length := by omega
          subst hk_eq
          have hg : gateAt (appOr D a b) D.gates.length = ⟨GateOp.or, [a, b]⟩ := by
            rw [gateAt_def, List.getD_eq_getElem?_getD]; simp [appOr]
          rw [hg] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> assumption
      · intro g hg
        simp only [appOr, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hD.2.2 g hg
        · rfl
    · intro x
      show (appOr D a b).eval (List.ofFn x) = _
      rw [eval_def, wires_def]
      simp only [appOr, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (D.gates.foldl stepWire (List.ofFn x)).length = 26 + D.gates.length := by
        rw [foldl_len, List.length_ofFn]
      have hget : (stepWire (D.gates.foldl stepWire (List.ofFn x)) ⟨GateOp.or, [a, b]⟩).getD (26 + D.gates.length) false =
          (GateOp.or).eval ([a, b].map fun i => (D.gates.foldl stepWire (List.ofFn x)).getD i false) := by
        rw [← hlen]
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [hget, eval_or_def]
      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rfl
    · intro x u hu
      dsimp only [val]; rw [wires_def]
      simp only [appOr, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (D.gates.foldl stepWire (List.ofFn x)).length = 26 + D.gates.length := by
        rw [foldl_len, List.length_ofFn]
      change (D.gates.foldl stepWire (List.ofFn x) ++ [_]).getD u false =
        (D.gates.foldl stepWire (List.ofFn x)).getD u false
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hlen]; exact hu)]
  have hout_bounds : 26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
    constructor
    · by_contra hlt
      have hout26 : C.output < 26 := by omega
      let x0 : Fin 26 → Bool := fun i => decide (i.val = C.output)
      have h1 : C.eval (List.ofFn x0) = true := by
        show val C (List.ofFn x0) C.output = true
        rw [val_input C x0 C.output hout26]
        simp [x0]
      have h2 : graphFun G0 ∅ x0 = false := by
        rw [graphFun_empty_false]
        rintro ⟨u, v, huv, hu, hv⟩
        simp only [x0, decide_eq_true_eq] at hu hv
        exact G0.ne_of_adj huv (Fin.ext (hu.trans hv.symm))
      have hfun := congrFun hL.2.1 x0
      change C.eval (List.ofFn x0) = graphFun G0 ∅ x0 at hfun
      rw [h1, h2] at hfun
      cases hfun
    · by_contra hle
      have hout_ge : 26 + C.gates.length ≤ C.output := by omega
      let x114 : Fin 26 → Bool := fun i => decide (i.val = 1 ∨ i.val = 14)
      have h1 : C.eval (List.ofFn x114) = false := val_ge C x114 C.output hout_ge
      have h2 : graphFun G0 ∅ x114 = true := by
        rw [graphFun_empty_iff]
        refine ⟨1, 14, ?_, by decide, by decide⟩
        rw [hadj_iff]
        decide +kernel
      have hfun := congrFun hL.2.1 x114
      change C.eval (List.ofFn x114) = graphFun G0 ∅ x114 at hfun
      rw [h1, h2] at hfun
      cases hfun
  have hleast_read : ∀ j < C.gates.length, 26 + j ≠ C.output →
      ∃ r < C.gates.length, 26 + j ∈ (gateAt C r).inputs := by
    intro j hj hne
    by_contra hno
    push Not at hno
    have hno' : ∀ k, j < k → k < C.gates.length → 26 + j ∉ (gateAt C k).inputs :=
      fun k _ hk => hno k hk
    have ep := erase_props C j 0 hL.1 hj (by omega)
    have hev : circuitFun 26 (eraseGate 26 C j 0) = graphFun G0 ∅ := by
      funext x
      rw [← hL.2.1]
      exact ep.2.2 x (Or.inr ⟨hne.symm, hno'⟩)
    have hle := hL.2.2 _ ep.2.1 hev
    omega
  have hleast_nodup : ∀ j < C.gates.length, ∀ p < 26 + j,
      ∃ x : Fin 26 → Bool, val C (List.ofFn x) (26 + j) ≠ val C (List.ofFn x) p := by
    intro j hj p hp
    by_contra hno
    push Not at hno
    have hno' : ∀ x : Fin 26 → Bool, val C (List.ofFn x) (26 + j) = val C (List.ofFn x) p := by
      intro x
      exact hno x
    have ep := erase_props C j p hL.1 hj hp
    have hev : circuitFun 26 (eraseGate 26 C j p) = graphFun G0 ∅ := by
      funext x
      rw [← hL.2.1]
      exact ep.2.2 x (Or.inl (hno' x))
    have hle := hL.2.2 _ ep.2.1 hev
    omega
  have hno_const_false : ∀ j < C.gates.length, ∃ x : Fin 26 → Bool, val C (List.ofFn x) (26 + j) = true := by
    intro j hj
    by_contra hbad
    let bad := (Finset.range C.gates.length).filter fun m =>
      ∀ x : Fin 26 → Bool, val C (List.ofFn x) (26 + m) = false
    have hne_bad : bad.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, fun x =>
      Bool.eq_false_iff.mpr fun ht => hbad ⟨x, ht⟩⟩⟩
    let m := bad.max' hne_bad
    have hm_mem := Finset.max'_mem bad hne_bad
    have hm_lt : m < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1
    have hm_false : ∀ x : Fin 26 → Bool, val C (List.ofFn x) (26 + m) = false :=
      (Finset.mem_filter.mp hm_mem).2
    have hm_ne_out : 26 + m ≠ C.output := by
      intro heq
      let x114 : Fin 26 → Bool := fun i => decide (i.val = 1 ∨ i.val = 14)
      have h1 : val C (List.ofFn x114) C.output = false := by rw [← heq]; exact hm_false x114
      have h2 : graphFun G0 ∅ x114 = true := by
        rw [graphFun_empty_iff]
        refine ⟨1, 14, ?_, by decide, by decide⟩
        rw [hadj_iff]; decide +kernel
      have hfun := congrFun hL.2.1 x114
      change val C (List.ofFn x114) C.output = graphFun G0 ∅ x114 at hfun
      rw [h1, h2] at hfun
      cases hfun
    obtain ⟨r, hr, hmr⟩ := hleast_read m hm_lt hm_ne_out
    have hr_gt : m < r := by
      have hlt := hL.1.2.1 r hr (26 + m) hmr
      omega
    have hr_not_bad : ¬ ∀ x : Fin 26 → Bool, val C (List.ofFn x) (26 + r) = false := by
      intro hrf
      have hrm : r ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hrf⟩
      have := Finset.le_max' bad r hrm
      omega
    have hrmem : gateAt C r ∈ C.gates := hgateAt_mem C r hr
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hrmem)
    have ha : a < 26 + r := hL.1.2.1 r hr a (by rw [hab]; simp)
    have hb : b < 26 + r := hL.1.2.1 r hr b (by rw [hab]; simp)
    have e0 : opnd C r 0 = a := by simp [opnd_def, hab]
    have e1 : opnd C r 1 = b := by simp [opnd_def, hab]
    rcases hL.1.1 _ hrmem with hand | hor
    · apply hr_not_bad
      intro x
      apply Bool.eq_false_iff.mpr
      intro hrt
      have hboth := (val_and C hL.1 x r hr hand).mp hrt
      rw [hab] at hmr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr
      rcases hmr with hm0 | hm1
      · have := hboth.1; rw [e0, ← hm0, hm_false x] at this; cases this
      · have := hboth.2; rw [e1, ← hm1, hm_false x] at this; cases this
    · rw [hab] at hmr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr
      rcases hmr with hm0 | hm1
      · obtain ⟨x, hx⟩ := hleast_nodup r hr b hb
        apply hx
        apply Bool.eq_iff_iff.mpr
        rw [val_or C hL.1 x r hr hor, e0, ← hm0, hm_false x, e1]
        simp
      · obtain ⟨x, hx⟩ := hleast_nodup r hr a ha
        apply hx
        apply Bool.eq_iff_iff.mpr
        rw [val_or C hL.1 x r hr hor, e1, ← hm1, hm_false x, e0]
        simp
  have htwo_readers : ∀ j < C.gates.length, BelowF G0 C j → ∀ r1 r2 : ℕ, r1 < r2 → r2 < C.gates.length →
      26 + j ∈ (gateAt C r1).inputs → 26 + j ∈ (gateAt C r2).inputs → False := by
    intro j hj hBj r1 r2 h12 hr2 hm1 hm2
    have hred : ∀ (D : Circuit), IsAO2 26 D → ∀ s r : ℕ, r < D.gates.length →
        26 + s ∈ (gateAt D r).inputs → ∃ p < 26 + r, ∀ x : Fin 26 → Bool,
          val D (List.ofFn x) (26 + s) = false → val D (List.ofFn x) (26 + r) = val D (List.ofFn x) p := by
      intro D hD s r hr hms
      have hrm : gateAt D r ∈ D.gates := hgateAt_mem D r hr
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hD.2.2 _ hrm)
      have ha : a < 26 + r := hD.2.1 r hr a (by rw [hab]; simp)
      have hb : b < 26 + r := hD.2.1 r hr b (by rw [hab]; simp)
      have e0 : opnd D r 0 = a := by simp [opnd_def, hab]
      have e1 : opnd D r 1 = b := by simp [opnd_def, hab]
      rw [hab] at hms
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hms
      rcases hD.1 _ hrm with hand | hor
      · refine ⟨26 + s, ?_, fun x hs => ?_⟩
        · rcases hms with h | h <;> omega
        · rw [hs]
          apply Bool.eq_false_iff.mpr
          intro ht
          have hboth := (val_and D hD x r hr hand).mp ht
          rcases hms with h | h
          · rw [e0, ← h, hs] at hboth; cases hboth.1
          · rw [e1, ← h, hs] at hboth; cases hboth.2
      · rcases hms with h | h
        · refine ⟨b, hb, fun x hs => ?_⟩
          apply Bool.eq_iff_iff.mpr
          have hwr := val_or D hD x r hr hor
          rw [e0, e1, ← h, hs] at hwr
          simpa using hwr
        · refine ⟨a, ha, fun x hs => ?_⟩
          apply Bool.eq_iff_iff.mpr
          have hwr := val_or D hD x r hr hor
          rw [e0, e1, ← h, hs] at hwr
          simpa using hwr
    have her_lt : ∀ (D : Circuit) (r p : ℕ), r < D.gates.length → ∀ (x : Fin 26 → Bool) (u : ℕ),
        u < 26 + r → val (eraseGate 26 D r p) (List.ofFn x) u = val D (List.ofFn x) u := by
      intro D r p hr x u hu
      dsimp only [val]; rw [wires_def]
      rw [eraseGate_pos 26 D r p hr, wires_def]
      rw [List.foldl_append]
      conv_rhs => rw [← List.take_append_drop r D.gates, List.foldl_append]
      have hlen : ((D.gates.take r).foldl stepWire (List.ofFn x)).length = 26 + r := by
        rw [foldl_len, List.length_ofFn, List.length_take]; omega
      rw [foldl_getD_lt _ ((D.gates.take r).foldl stepWire (List.ofFn x)) u (by rw [hlen]; exact hu),
        foldl_getD_lt (D.gates.drop r) ((D.gates.take r).foldl stepWire (List.ofFn x)) u (by rw [hlen]; exact hu)]
    have her_gate : ∀ (D : Circuit) (r p k : ℕ), r < D.gates.length → k < r →
        gateAt (eraseGate 26 D r p) k = gateAt D k := by
      intro D r p k hr hk
      rw [gateAt_def, gateAt_def, eraseGate_pos 26 D r p hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk]
    have her_out : ∀ (D : Circuit) (r p : ℕ), r < D.gates.length → p < 26 + r →
        D.output < 26 + D.gates.length → (eraseGate 26 D r p).output < 26 + (eraseGate 26 D r p).gates.length := by
      intro D r p hr hp ho
      rw [eraseGate_pos 26 D r p hr]; simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
      unfold eraseRedirect
      split_ifs with h1 h2 <;> omega
    obtain ⟨p2, hp2, hv2⟩ := hred C hL.1 j r2 hr2 hm2
    let D1 := eraseGate 26 C r2 p2
    have ep1 := erase_props C r2 p2 hL.1 hr2 hp2
    have hD1_sz : D1.gates.length + 1 = C.gates.length := ep1.1
    have hD1_AO : IsAO2 26 D1 := ep1.2.1
    have hm1' : 26 + j ∈ (gateAt D1 r1).inputs := by
      rw [her_gate C r2 p2 r1 hr2 h12]; exact hm1
    have hr1' : r1 < D1.gates.length := by omega
    obtain ⟨p1, hp1, hv1⟩ := hred D1 hD1_AO j r1 hr1' hm1'
    let D2 := eraseGate 26 D1 r1 p1
    have ep2 := erase_props D1 r1 p1 hD1_AO hr1' hp1
    have hD2_sz : D2.gates.length + 1 = D1.gates.length := ep2.1
    have ho1 : D1.output < 26 + D1.gates.length := her_out C r2 p2 hr2 hp2 hout_bounds.2
    have ho2 : D2.output < 26 + D2.gates.length := her_out D1 r1 p1 hr1' hp1 ho1
    have hj_lt_D2 : 26 + j < 26 + D2.gates.length := by
      have hj1 : j < r1 := by have := hL.1.2.1 r1 (by omega) (26 + j) hm1; omega
      omega
    let D3 := appOr D2 D2.output (26 + j)
    have ap3 := appOr_props D2 D2.output (26 + j) ep2.2.1 ho2 hj_lt_D2
    have hev3 : circuitFun 26 D3 = graphFun G0 ∅ := by
      funext x
      rw [← hL.2.1]
      change D3.eval (List.ofFn x) = C.eval (List.ofFn x)
      rw [ap3.2.2.1 x]
      have hj_eq : val D2 (List.ofFn x) (26 + j) = val C (List.ofFn x) (26 + j) := by
        have hj1 : j < r1 := by have := hL.1.2.1 r1 (by omega) (26 + j) hm1; omega
        rw [her_lt D1 r1 p1 hr1' x (26 + j) (by omega), her_lt C r2 p2 hr2 x (26 + j) (by omega)]
      rw [hj_eq]
      cases hx : val C (List.ofFn x) (26 + j)
      · rw [Bool.or_false]
        have hx1 : val D1 (List.ofFn x) (26 + j) = false := by
          rw [her_lt C r2 p2 hr2 x (26 + j) (by have := hL.1.2.1 r1 (by omega) (26 + j) hm1; omega)]
          exact hx
        exact (ep2.2.2 x (Or.inl (hv1 x hx1))).trans (ep1.2.2 x (Or.inl (hv2 x hx)))
      · rw [Bool.or_true]
        have hF := hBj x hx
        rw [← hL.2.1] at hF
        exact hF.symm
    have hle := hL.2.2 D3 ap3.2.1 hev3
    have hap3_sz : D3.gates.length = D2.gates.length + 1 := ap3.1
    change C.gates.length ≤ D3.gates.length at hle
    omega
  have hcone_len : ∀ (gs : List Gate) (cs : List (List ℕ)), (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih => intro cs; rw [List.foldl_cons, ih, coneStep_def]; simp; omega
  have hcone_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (m : ℕ), m < cs.length →
      (gs.foldl (coneStep 26) cs).getD m [] = cs.getD m [] := by
    intro gs
    induction gs with
    | nil => intro cs m _; rfl
    | cons g gs ih =>
      intro cs m hm
      rw [List.foldl_cons, ih (coneStep 26 cs g) m (by rw [coneStep_def]; simp; omega)]
      rw [coneStep_def]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
  have hcone_iff : ∀ i k : ℕ, k < C.gates.length →
      (InCone 26 C i k ↔ ∃ w ∈ (gateAt C k).inputs, 26 ≤ w ∧ w < 26 + k ∧ (i = w - 26 ∨ InCone 26 C i (w - 26))) := by
    intro i k hk
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let gk := C.gates[k]
    have hgs : C.gates = pre ++ gk :: post := by
      simp only [pre, post, gk]; rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hpre_len : pre.length = k := by simp [pre]; omega
    have hga : gateAt C k = gk := by rw [gateAt_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rw [hga]
    have hc : cones 26 C = post.foldl (coneStep 26) (coneStep 26 (pre.foldl (coneStep 26) []) gk) := by
      rw [cones_def, hgs, List.foldl_append, List.foldl_cons]
    have hl0 : (pre.foldl (coneStep 26) []).length = k := by rw [hcone_len]; simp [hpre_len]
    have h1 : (cones 26 C).getD k [] =
        (gk.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
          (fun w => (w - 26) :: (pre.foldl (coneStep 26) []).getD (w - 26) []) := by
      rw [hc, hcone_lt post _ k (by rw [coneStep_def]; simp [hl0])]
      rw [coneStep_def]; simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hl0, Nat.sub_self, List.getElem?_cons_zero]
      rfl
    have h2 : ∀ m, m < k → (cones 26 C).getD m [] = (pre.foldl (coneStep 26) []).getD m [] := by
      intro m hm
      rw [hc, hcone_lt post _ m (by rw [coneStep_def]; simp [hl0]; omega)]
      rw [coneStep_def]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : m < (pre.foldl (coneStep 26) []).length)]
    unfold InCone
    rw [h1]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
      refine ⟨w, hw, hn, hlt, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right; rw [h2 (w - 26) (by omega)]; exact h
    · rintro ⟨w, hw, hn, hlt, h⟩
      refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right; rw [← h2 (w - 26) (by omega)]; exact h
  have hcone_c1 : ∀ i k : ℕ, k < C.gates.length → 26 + i ∈ (gateAt C k).inputs → InCone 26 C i k := by
    intro i k hk hm
    rw [hcone_iff i k hk]
    have hlt := hL.1.2.1 k hk (26 + i) hm
    exact ⟨26 + i, hm, by omega, hlt, Or.inl (by omega)⟩
  have hcone_c2 : ∀ t i k : ℕ, k < C.gates.length → InCone 26 C t i →
      26 + i ∈ (gateAt C k).inputs → InCone 26 C t k := by
    intro t i k hk hti hm
    rw [hcone_iff t k hk]
    have hlt := hL.1.2.1 k hk (26 + i) hm
    exact ⟨26 + i, hm, by omega, hlt, Or.inr (by simpa [Nat.add_sub_cancel_left] using hti)⟩
  let noAndBelow : ℕ → Prop := fun w =>
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      w ≠ 26 + j ∧ (26 ≤ w → ¬ InCone 26 C j (w - 26))
  have hand_opnd_noAnd : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ b : Fin 2, noAndBelow (opnd C k b) := by
    intro k hk hkop b
    have hmem : gateAt C k ∈ C.gates := by
      exact hgateAt_mem C k hk
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hL.1.2.2 _ hmem)
    have hopnd_mem : opnd C k b ∈ (gateAt C k).inputs := by
      fin_cases b <;> simp [opnd_def, huv]
    intro j hj hjop
    constructor
    · intro heq
      have hc := hcone_c1 j k hk (by rw [← heq]; exact hopnd_mem)
      exact hT j hj k hk hjop (hno_junk j hj hjop) hkop hc
    · intro hge hc
      have hlt := hL.1.2.1 k hk (opnd C k b) hopnd_mem
      have hmem2 : 26 + (opnd C k b - 26) ∈ (gateAt C k).inputs := by
        rwa [show 26 + (opnd C k b - 26) = opnd C k b by omega]
      have hc2 := hcone_c2 j (opnd C k b - 26) k hk hc hmem2
      exact hT j hj k hk hjop (hno_junk j hj hjop) hkop hc2
  let suppStep : List (Finset (Fin 26)) → Gate → List (Finset (Fin 26)) :=
    fun L g => L ++ [if g.op = GateOp.or then (g.inputs.map fun i => L.getD i ∅).foldr (· ∪ ·) ∅ else ∅]
  let orSupp : List (Finset (Fin 26)) := C.gates.foldl suppStep (List.ofFn fun i : Fin 26 => ({i} : Finset (Fin 26)))
  have hsupp_len : ∀ (gs : List Gate) (L : List (Finset (Fin 26))), (gs.foldl suppStep L).length = L.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro L; simp
    | cons g gs ih => intro L; rw [List.foldl_cons, ih]; simp [suppStep]; omega
  have hsupp_lt : ∀ (gs : List Gate) (L : List (Finset (Fin 26))) (i : ℕ), i < L.length →
      (gs.foldl suppStep L).getD i ∅ = L.getD i ∅ := by
    intro gs
    induction gs with
    | nil => intro L i _; rfl
    | cons g gs ih =>
      intro L i hi
      rw [List.foldl_cons, ih (suppStep L g) i (by simp [suppStep]; omega)]
      simp [suppStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hsupp_input : ∀ u : ℕ, (hu : u < 26) → orSupp.getD u ∅ = {⟨u, hu⟩} := by
    intro u hu
    unfold orSupp
    rw [hsupp_lt C.gates _ u (by simpa using hu)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hu]
    rfl
  have hsupp_or : ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      orSupp.getD (26 + k) ∅ = orSupp.getD (opnd C k 0) ∅ ∪ orSupp.getD (opnd C k 1) ∅ := by
    intro k hk hkop
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let gk := C.gates[k]
    have hgs : C.gates = pre ++ gk :: post := by
      simp only [pre, post, gk]; rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hpre_len : pre.length = k := by simp [pre]; omega
    have hga : gateAt C k = gk := by rw [gateAt_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have hgk_mem : gk ∈ C.gates := by rw [← hga]; exact hgateAt_mem C k hk
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 gk hgk_mem)
    have ha : a < 26 + k := hL.1.2.1 k hk a (by rw [hga, hab]; simp)
    have hb : b < 26 + k := hL.1.2.1 k hk b (by rw [hga, hab]; simp)
    have e0 : opnd C k 0 = a := by simp [opnd_def, hga, hab]
    have e1 : opnd C k 1 = b := by simp [opnd_def, hga, hab]
    let L0 := pre.foldl suppStep (List.ofFn fun i : Fin 26 => ({i} : Finset (Fin 26)))
    have hL0_len : L0.length = 26 + k := by simp [L0, hsupp_len, hpre_len]
    have hor : orSupp = post.foldl suppStep (suppStep L0 gk) := by
      simp only [orSupp, L0]; rw [hgs, List.foldl_append, List.foldl_cons]
    have hgk_op : gk.op = GateOp.or := by rw [← hga]; exact hkop
    have hget_k : orSupp.getD (26 + k) ∅ = (gk.inputs.map fun i => L0.getD i ∅).foldr (· ∪ ·) ∅ := by
      rw [hor, hsupp_lt post (suppStep L0 gk) (26 + k) (by simp [suppStep, hL0_len])]
      simp only [suppStep, hgk_op, ↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hL0_len, Nat.sub_self, List.getElem?_cons_zero]
      rfl
    have hget_lt : ∀ w, w < 26 + k → orSupp.getD w ∅ = L0.getD w ∅ := by
      intro w hw
      rw [hor, hsupp_lt post (suppStep L0 gk) w (by simp [suppStep, hL0_len]; omega)]
      simp [suppStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < L0.length)]
    rw [hget_k, e0, e1, hget_lt a ha, hget_lt b hb, hab]
    simp
  have hnoAnd_child : ∀ w, w < 26 + C.gates.length → noAndBelow w → 26 ≤ w →
      (gateAt C (w - 26)).op = GateOp.or ∧
      noAndBelow (opnd C (w - 26) 0) ∧ noAndBelow (opnd C (w - 26) 1) := by
    intro w hw hna hge
    let k := w - 26
    have hk : k < C.gates.length := by omega
    have hkop : (gateAt C k).op = GateOp.or := by
      have hk_mem : gateAt C k ∈ C.gates := by
        exact hgateAt_mem C k hk
      rcases hL.1.1 _ hk_mem with hand | hor
      · exfalso; exact (hna k hk hand).1 (by omega)
      · exact hor
    have hsub : ∀ b : Fin 2, noAndBelow (opnd C k b) := by
      intro b j hj hjop
      have hm_mem : gateAt C k ∈ C.gates := hgateAt_mem C k hk
      obtain ⟨a0, a1, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hm_mem)
      have hop_mem : opnd C k b ∈ (gateAt C k).inputs := by
        fin_cases b <;> simp [opnd_def, hab]
      constructor
      · intro heq
        have hc := hcone_c1 j k hk (by rw [← heq]; exact hop_mem)
        exact (hna j hj hjop).2 hge hc
      · intro hge2 hc
        have hlt := hL.1.2.1 k hk _ hop_mem
        have hc2 := hcone_c2 j (opnd C k b - 26) k hk hc
          (by simpa [show 26 + (opnd C k b - 26) = opnd C k b by omega] using hop_mem)
        exact (hna j hj hjop).2 hge hc2
    exact ⟨hkop, hsub 0, hsub 1⟩
  have hval_orSupp : ∀ w : ℕ, w < 26 + C.gates.length → noAndBelow w →
      ∀ x : Fin 26 → Bool, val C (List.ofFn x) w = true ↔ ∃ t ∈ orSupp.getD w ∅, x t = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hna x
      by_cases hw26 : w < 26
      · rw [val_input C x w hw26, hsupp_input w hw26]
        simp
      · have hge : 26 ≤ w := by omega
        obtain ⟨hkop, hna0, hna1⟩ := hnoAnd_child w hw hna hge
        let k := w - 26
        have hk : k < C.gates.length := by omega
        have hw_eq : 26 + k = w := by omega
        have h0_lt : opnd C k 0 < w := by have := hL.1.2.1 k hk (opnd C k 0) (by
          have hm : gateAt C k ∈ C.gates := by exact hgateAt_mem C k hk
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hm); simp [opnd_def, hab]); omega
        have h1_lt : opnd C k 1 < w := by have := hL.1.2.1 k hk (opnd C k 1) (by
          have hm : gateAt C k ∈ C.gates := by exact hgateAt_mem C k hk
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hm); simp [opnd_def, hab]); omega
        rw [← hw_eq, val_or C hL.1 x k hk hkop, hsupp_or k hk hkop,
          ih (opnd C k 0) (by omega) (by omega) hna0,
          ih (opnd C k 1) (by omega) (by omega) hna1]
        simp only [Finset.mem_union]
        constructor
        · rintro (⟨t, ht, hxt⟩ | ⟨t, ht, hxt⟩)
          · exact ⟨t, Or.inl ht, hxt⟩
          · exact ⟨t, Or.inr ht, hxt⟩
        · rintro ⟨t, ht | ht, hxt⟩
          · exact Or.inl ⟨t, ht, hxt⟩
          · exact Or.inr ⟨t, ht, hxt⟩
  have horN_noAnd : ∀ k ∈ orN G0 C, noAndBelow (26 + k) := by
    intro k hk
    by_contra hbad
    let bad := (orN G0 C).filter fun m => ¬ noAndBelow (26 + m)
    have hne : bad.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hbad⟩⟩
    let m := bad.max' hne
    have hm_mem := Finset.max'_mem bad hne
    have hm_orN : m ∈ orN G0 C := (Finset.mem_filter.mp hm_mem).1
    have hm_bad : ¬ noAndBelow (26 + m) := (Finset.mem_filter.mp hm_mem).2
    have hm_lt : m < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hm_orN).1
    have hm_op : (gateAt C m).op = GateOp.or := (Finset.mem_filter.mp hm_orN).2.1
    have hm_nb : ¬ BelowF G0 C m := (Finset.mem_filter.mp hm_orN).2.2
    have hm_ne_out : 26 + m ≠ C.output := by
      intro heq
      apply hm_nb
      intro x hx
      have hfun := congrFun hL.2.1 x
      rw [← hfun]
      change val C (List.ofFn x) C.output = true
      rw [← heq]; exact hx
    obtain ⟨r, hr, hmr⟩ := hleast_read m hm_lt hm_ne_out
    have hr_gt : m < r := by have := hL.1.2.1 r hr (26 + m) hmr; omega
    have hr_no_and : (gateAt C r).op = GateOp.or := by
      have hrm : gateAt C r ∈ C.gates := by
        exact hgateAt_mem C r hr
      rcases hL.1.1 _ hrm with hand | hor
      · exfalso
        dsimp only [noAndBelow] at hm_bad
        push Not at hm_bad
        obtain ⟨j, hj, hjop, hjm⟩ := hm_bad
        by_cases heq : 26 + m = 26 + j
        · have : j = m := by omega
          subst this; rw [hm_op] at hjop; cases hjop
        · obtain ⟨_, hc⟩ := hjm heq
          have hc' : InCone 26 C j m := by simpa [Nat.add_sub_cancel_left] using hc
          exact hT j hj r hr hjop (hno_junk j hj hjop) hand (hcone_c2 j m r hr hc' hmr)
      · exact hor
    have hr_nb : ¬ BelowF G0 C r := by
      intro hBr
      apply hm_nb
      intro x hx
      change val C (List.ofFn x) (26 + m) = true at hx
      apply hBr x
      change val C (List.ofFn x) (26 + r) = true
      have hrm : gateAt C r ∈ C.gates := hgateAt_mem C r hr
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hrm)
      rw [val_or C hL.1 x r hr hr_no_and]
      rw [hab] at hmr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr
      rcases hmr with h | h
      · left; simpa [opnd_def, hab, h] using hx
      · right; simpa [opnd_def, hab, h] using hx
    have hr_orN : r ∈ orN G0 C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hr_no_and, hr_nb⟩
    have hr_bad : ¬ noAndBelow (26 + r) := by
      intro hna
      dsimp only [noAndBelow] at hm_bad
      push Not at hm_bad
      obtain ⟨j, hj, hjop, hjm⟩ := hm_bad
      by_cases heq : 26 + m = 26 + j
      · have : j = m := by omega
        subst this; rw [hm_op] at hjop; cases hjop
      · obtain ⟨_, hc⟩ := hjm heq
        have hc' : InCone 26 C j m := by simpa [Nat.add_sub_cancel_left] using hc
        exact (hna j hj hjop).2 (by omega) (by simpa [Nat.add_sub_cancel_left] using hcone_c2 j m r hr hc' hmr)
    have hrm_bad : r ∈ bad := Finset.mem_filter.mpr ⟨hr_orN, hr_bad⟩
    have := Finset.le_max' bad r hrm_bad
    omega
  have horN_card2 : ∀ k ∈ orN G0 C, 2 ≤ (orSupp.getD (26 + k) ∅).card := by
    intro k hk
    have hk_lt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hna := horN_noAnd k hk
    let S := orSupp.getD (26 + k) ∅
    by_contra hlt
    have hc : S.card = 0 ∨ S.card = 1 := by dsimp only [S]; omega
    rcases hc with h0 | h1
    · have hemp : S = ∅ := Finset.card_eq_zero.mp h0
      obtain ⟨x, hx⟩ := hno_const_false k hk_lt
      rw [hval_orSupp (26 + k) (by omega) hna x] at hx
      obtain ⟨t, ht, _⟩ := hx
      change t ∈ S at ht
      rw [hemp] at ht
      exact Finset.notMem_empty t ht
    · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
      obtain ⟨x, hx⟩ := hleast_nodup k hk_lt t.val (by omega)
      apply hx
      apply Bool.eq_iff_iff.mpr
      rw [hval_orSupp (26 + k) (by omega) hna x, val_input C x t.val t.isLt]
      change (∃ u ∈ S, x u = true) ↔ x t = true
      simp [ht]
  let T := tops G0 C
  let OT := orT G0 C
  let ON := orN G0 C
  have hT_eq : ∀ j, j ∈ T ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
    intro j
    dsimp only [T]; rw [mem_tops_iff]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hno_junk j h.1 h.2⟩⟩
  have hsplit : T.card + OT.card + ON.card = C.gates.length := by
    have h1 : Disjoint T OT := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have h1 := ((hT_eq j).1 hj1).2
      have h2 := (Finset.mem_filter.mp hj2).2.1
      rw [h1] at h2; cases h2
    have h2 : Disjoint (T ∪ OT) ON := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have hnb := (Finset.mem_filter.mp hj2).2.2
      rcases Finset.mem_union.mp hj1 with hjT | hjOT
      · exact hnb (hno_junk j ((hT_eq j).1 hjT).1 ((hT_eq j).1 hjT).2)
      · exact hnb (Finset.mem_filter.mp hjOT).2.2
    have hun : T ∪ OT ∪ ON = Finset.range C.gates.length := by
      ext j
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_range, hT_eq]
      dsimp only [OT, ON]
      rw [mem_orT_iff, mem_orN_iff]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro hj
        have hm : gateAt C j ∈ C.gates := by
          exact hgateAt_mem C j hj
        rcases hL.1.1 _ hm with hand | hor
        · exact Or.inl (Or.inl ⟨hj, hand⟩)
        · by_cases hb : BelowF G0 C j
          · exact Or.inl (Or.inr ⟨hj, hor, hb⟩)
          · exact Or.inr ⟨hj, hor, hb⟩
    have hc := congrArg Finset.card hun
    rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, Finset.card_range] at hc
    exact hc
  have hhas_top : ∀ j < C.gates.length, BelowF G0 C j →
      ∃ t ∈ T, t = j ∨ InCone 26 C t j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hBj
      have hm : gateAt C j ∈ C.gates := by
        exact hgateAt_mem C j hj
      rcases hL.1.1 _ hm with hand | hor
      · exact ⟨j, (hT_eq j).2 ⟨hj, hand⟩, Or.inl rfl⟩
      · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hm)
        have ha : a < 26 + j := hL.1.2.1 j hj a (by rw [hab]; simp)
        have hBa : ∀ x : Fin 26 → Bool, val C (List.ofFn x) a = true → graphFun G0 ∅ x = true := by
          intro x hxa
          apply hBj x
          change val C (List.ofFn x) (26 + j) = true
          rw [val_or C hL.1 x j hj hor]
          left; simpa [opnd_def, hab] using hxa
        have hna : 26 ≤ a := by
          by_contra hlt
          let x0 : Fin 26 → Bool := fun i => decide (i.val = a)
          have h1 : val C (List.ofFn x0) a = true := by rw [val_input C x0 a (by omega)]; simp [x0]
          have h2 := hBa x0 h1
          rw [graphFun_empty_iff] at h2
          obtain ⟨u, v, huv, hu, hv⟩ := h2
          simp only [x0, decide_eq_true_eq] at hu hv
          exact G0.ne_of_adj huv (Fin.ext (hu.trans hv.symm))
        let a' := a - 26
        have ha' : a' < j := by omega
        have hBa' : BelowF G0 C a' := fun x hx => by
          change val C (List.ofFn x) (26 + a') = true at hx
          rw [show 26 + a' = a by omega] at hx
          exact hBa x hx
        obtain ⟨t, htT, htj⟩ := ih a' ha' (by omega) hBa'
        refine ⟨t, htT, Or.inr ?_⟩
        have hmem : 26 + a' ∈ (gateAt C j).inputs := by rw [hab]; simp [a', show 26 + (a - 26) = a by omega]
        rcases htj with hta' | hcone
        · rw [hta']; exact hcone_c1 a' j hj hmem
        · exact hcone_c2 t a' j hj hcone hmem
  have hup : ∀ s < C.gates.length, (∃ t ∈ T, InCone 26 C t s) → BelowF G0 C s := by
    intro s hs h
    obtain ⟨t, htT, hts⟩ := h
    have ht_lt : t < C.gates.length := ((hT_eq t).1 htT).1
    have ht_op : (gateAt C t).op = GateOp.and := ((hT_eq t).1 htT).2
    have hdown : ∀ d s : ℕ, s < C.gates.length → C.gates.length - s = d → InCone 26 C t s → BelowF G0 C s := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro s hs hd hcs
        by_cases hso : 26 + s = C.output
        · intro x hx
          have hfun := congrFun hL.2.1 x
          rw [← hfun]
          change val C (List.ofFn x) C.output = true
          rw [← hso]; exact hx
        · obtain ⟨k, hk, hmk⟩ := hleast_read s hs hso
          have hsk : s < k := by have := hL.1.2.1 k hk (26 + s) hmk; omega
          have hck := hcone_c2 t s k hk hcs hmk
          have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
          have hkm : gateAt C k ∈ C.gates := by
            exact hgateAt_mem C k hk
          have hkop : (gateAt C k).op = GateOp.or := by
            rcases hL.1.1 _ hkm with hand | hor
            · exact absurd hck (hT t ht_lt k hk ht_op (hno_junk t ht_lt ht_op) hand)
            · exact hor
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hkm)
          intro x hx
          change val C (List.ofFn x) (26 + s) = true at hx
          apply hBk x
          change val C (List.ofFn x) (26 + k) = true
          rw [val_or C hL.1 x k hk hkop]
          rw [hab] at hmk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
          rcases hmk with h | h
          · left; simpa [opnd_def, hab, h] using hx
          · right; simpa [opnd_def, hab, h] using hx
    exact hdown (C.gates.length - s) s hs rfl hts
  have hT_le_OT : T.card ≤ OT.card + 1 := by
    have hread_OT : ∀ j ∈ T ∪ OT, 26 + j ≠ C.output →
        ∃ r ∈ OT, ∃ idx : Fin 2, opnd C r idx = 26 + j ∧
          ∀ r' ∈ OT, ∀ idx' : Fin 2, opnd C r' idx' = 26 + j → r' = r ∧ idx' = idx := by
      intro j hj hne
      have hj_lt : j < C.gates.length := by
        rcases Finset.mem_union.mp hj with h | h
        · exact ((hT_eq j).1 h).1
        · exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
      have hjB : BelowF G0 C j := by
        rcases Finset.mem_union.mp hj with h | h
        · exact hno_junk j hj_lt ((hT_eq j).1 h).2
        · exact (Finset.mem_filter.mp h).2.2
      obtain ⟨r, hr, hmr⟩ := hleast_read j hj_lt hne
      obtain ⟨t, htT, htj⟩ := hhas_top j hj_lt hjB
      have htr : InCone 26 C t r := by
        rcases htj with rfl | hc
        · exact hcone_c1 t r hr hmr
        · exact hcone_c2 t j r hr hc hmr
      have ht_lt := ((hT_eq t).1 htT).1
      have ht_op := ((hT_eq t).1 htT).2
      have hrm : gateAt C r ∈ C.gates := by
        exact hgateAt_mem C r hr
      have hrop : (gateAt C r).op = GateOp.or := by
        rcases hL.1.1 _ hrm with hand | hor
        · exact absurd htr (hT t ht_lt r hr ht_op (hno_junk t ht_lt ht_op) hand)
        · exact hor
      have hrB : BelowF G0 C r := hup r hr ⟨t, htT, htr⟩
      have hrOT : r ∈ OT := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hrop, hrB⟩
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ hrm)
      have hidx : ∃ idx : Fin 2, opnd C r idx = 26 + j := by
        rw [hab] at hmr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr
        rcases hmr with h | h
        · exact ⟨0, by simp [opnd_def, hab, h]⟩
        · exact ⟨1, by simp [opnd_def, hab, h]⟩
      obtain ⟨idx, hidx_eq⟩ := hidx
      refine ⟨r, hrOT, idx, hidx_eq, fun r' hrOT' idx' hidx' => ?_⟩
      have hr' : r' < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hrOT').1
      have hr'm : gateAt C r' ∈ C.gates := by
        exact hgateAt_mem C r' hr'
      obtain ⟨a', b', hab'⟩ := List.length_eq_two.mp (hL.1.2.2 _ hr'm)
      have hmr' : 26 + j ∈ (gateAt C r').inputs := by
        rw [← hidx', hab']
        fin_cases idx' <;> simp [opnd_def, hab']
      have hreq : r' = r := by
        by_contra hne_r
        rcases lt_or_gt_of_ne hne_r with hlt | hlt
        · exact htwo_readers j hj_lt hjB r' r hlt hr hmr' hmr
        · exact htwo_readers j hj_lt hjB r r' hlt hr' hmr hmr'
      subst r'
      refine ⟨rfl, ?_⟩
      by_contra hne_idx
      have hop_eq : opnd C r 0 = opnd C r 1 := by
        fin_cases idx <;> fin_cases idx'
        · exact absurd rfl hne_idx
        · exact hidx_eq.trans hidx'.symm
        · exact hidx'.trans hidx_eq.symm
        · exact absurd rfl hne_idx
      have ha_eq_b : a = b := by simpa [opnd_def, hab] using hop_eq
      subst b
      obtain ⟨x, hx⟩ := hleast_nodup r hr a (by have := hL.1.2.1 r hr a (by rw [hab]; simp); exact this)
      apply hx
      apply Bool.eq_iff_iff.mpr
      rw [val_or C hL.1 x r hr hrop]
      simp [opnd_def, hab]
    let outIdx := C.output - 26
    let S_src := (T ∪ OT).erase outIdx
    have h_inj : ∀ j ∈ S_src, ∃ p : ℕ × Fin 2, p.1 ∈ OT ∧ opnd C p.1 p.2 = 26 + j := by
      intro j hj
      have hjU := (Finset.mem_erase.mp hj).2
      have hj_ne : 26 + j ≠ C.output := by
        have hne := (Finset.mem_erase.mp hj).1
        omega
      obtain ⟨r, hrOT, idx, hidx, _⟩ := hread_OT j hjU hj_ne
      exact ⟨(r, idx), hrOT, hidx⟩
    let f : ℕ → ℕ × Fin 2 := fun j =>
      if hj : j ∈ S_src then (Classical.choose (h_inj j hj)) else (0, 0)
    have hf_mem : ∀ j ∈ S_src, f j ∈ OT ×ˢ (Finset.univ : Finset (Fin 2)) := by
      intro j hj
      simp only [f, dif_pos hj, Finset.mem_product, Finset.mem_univ, and_true]
      exact (Classical.choose_spec (h_inj j hj)).1
    have hf_inj : Set.InjOn f S_src := by
      intro j1 hj1 j2 hj2 heq
      have hj1' : j1 ∈ S_src := hj1
      have hj2' : j2 ∈ S_src := hj2
      have h1 := (Classical.choose_spec (h_inj j1 hj1')).2
      have h2 := (Classical.choose_spec (h_inj j2 hj2')).2
      simp only [f, dif_pos hj1', dif_pos hj2'] at heq
      rw [heq] at h1
      have : 26 + j1 = 26 + j2 := h1.symm.trans h2
      omega
    have hcard_le : S_src.card ≤ (OT ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      calc S_src.card = (S_src.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ (OT ×ˢ (Finset.univ : Finset (Fin 2))).card :=
            Finset.card_le_card (fun p hp => by obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp; exact hf_mem j hj)
    rw [Finset.card_product, Finset.card_fin] at hcard_le
    have hdisj : Disjoint T OT := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have h1 := ((hT_eq j).1 hj1).2
      have h2 := (Finset.mem_filter.mp hj2).2.1
      rw [h1] at h2; cases h2
    have hc1 : (T ∪ OT).card = T.card + OT.card := Finset.card_union_of_disjoint hdisj
    have hc2 : (T ∪ OT).card - 1 ≤ S_src.card := by
      by_cases hm : outIdx ∈ T ∪ OT
      · rw [Finset.card_erase_of_mem hm]
      · dsimp only [S_src]; rw [Finset.erase_eq_self.mpr hm]; omega
    omega
  have hT_star : ∀ a ∈ T,
      ((orSupp.getD (opnd C a 0) ∅).Nonempty ∧ (orSupp.getD (opnd C a 1) ∅).Nonempty) ∧
      (∀ u ∈ orSupp.getD (opnd C a 0) ∅, ∀ v ∈ orSupp.getD (opnd C a 1) ∅, G0.Adj u v) ∧
      ((orSupp.getD (opnd C a 0) ∅).card = 1 ∨ (orSupp.getD (opnd C a 1) ∅).card = 1) := by
    intro a ha
    have ha_lt := ((hT_eq a).1 ha).1
    have ha_op := ((hT_eq a).1 ha).2
    have hBa := hno_junk a ha_lt ha_op
    have hna0 := hand_opnd_noAnd a ha_lt ha_op 0
    have hna1 := hand_opnd_noAnd a ha_lt ha_op 1
    have ha_mem : gateAt C a ∈ C.gates := by
      exact hgateAt_mem C a ha_lt
    obtain ⟨w0, w1, hw⟩ := List.length_eq_two.mp (hL.1.2.2 _ ha_mem)
    have h0_lt : opnd C a 0 < 26 + C.gates.length := by
      have := hL.1.2.1 a ha_lt w0 (by rw [hw]; simp); simp [opnd_def, hw]; omega
    have h1_lt : opnd C a 1 < 26 + C.gates.length := by
      have := hL.1.2.1 a ha_lt w1 (by rw [hw]; simp); simp [opnd_def, hw]; omega
    have hnon : (orSupp.getD (opnd C a 0) ∅).Nonempty ∧ (orSupp.getD (opnd C a 1) ∅).Nonempty := by
      obtain ⟨x, hx⟩ := hno_const_false a ha_lt
      rw [val_and C hL.1 x a ha_lt ha_op] at hx
      rw [hval_orSupp (opnd C a 0) h0_lt hna0 x] at hx
      rw [hval_orSupp (opnd C a 1) h1_lt hna1 x] at hx
      exact ⟨⟨hx.1.choose, hx.1.choose_spec.1⟩, ⟨hx.2.choose, hx.2.choose_spec.1⟩⟩
    have hadj_all : ∀ u ∈ orSupp.getD (opnd C a 0) ∅, ∀ v ∈ orSupp.getD (opnd C a 1) ∅, G0.Adj u v := by
      intro u hu v hv
      let x := pairInput u v
      have h0 : val C (List.ofFn x) (opnd C a 0) = true :=
        (hval_orSupp (opnd C a 0) h0_lt hna0 x).mpr ⟨u, hu, by simp [x, pairInput_def]⟩
      have h1 : val C (List.ofFn x) (opnd C a 1) = true :=
        (hval_orSupp (opnd C a 1) h1_lt hna1 x).mpr ⟨v, hv, by simp [x, pairInput_def]⟩
      have ha_true : val C (List.ofFn x) (26 + a) = true :=
        (val_and C hL.1 x a ha_lt ha_op).mpr ⟨h0, h1⟩
      have hF := hBa x ha_true
      rw [graphFun_empty_iff] at hF
      obtain ⟨u', v', huv', hu', hv'⟩ := hF
      simp only [x, pairInput_def, decide_eq_true_eq] at hu' hv'
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact absurd rfl (G0.ne_of_adj huv')
      · exact huv'
      · exact huv'.symm
      · exact absurd rfl (G0.ne_of_adj huv')
    have hcard1 : (orSupp.getD (opnd C a 0) ∅).card = 1 ∨ (orSupp.getD (opnd C a 1) ∅).card = 1 := by
      by_contra hcon
      simp only [not_or] at hcon
      have hc0 : 1 < (orSupp.getD (opnd C a 0) ∅).card := by
        have := Finset.card_pos.mpr hnon.1; omega
      have hc1 : 1 < (orSupp.getD (opnd C a 1) ∅).card := by
        have := Finset.card_pos.mpr hnon.2; omega
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp hc0
      have hsub : orSupp.getD (opnd C a 1) ∅ ⊆ Finset.univ.filter fun w => G0.Adj p1 w ∧ G0.Adj p2 w := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hadj_all p1 hp1 q hq, hadj_all p2 hp2 q hq⟩
      have := (Finset.card_le_card hsub).trans (hnoC4 p1 p2 hpne)
      omega
    exact ⟨hnon, hadj_all, hcard1⟩
  let sideIdx : ℕ → Fin 2 := fun a =>
    if (orSupp.getD (opnd C a 0) ∅).card = 1 then 0 else 1
  let ctr : ℕ → Fin 26 := fun a =>
    if ha : a ∈ T then
      if h0 : (orSupp.getD (opnd C a 0) ∅).card = 1 then
        (Finset.card_eq_one.mp h0).choose
      else
        (Finset.card_eq_one.mp ((hT_star a ha).2.2.resolve_left h0)).choose
    else 0
  let leafWire : ℕ → ℕ := fun a => opnd C a (1 - sideIdx a)
  let leafSet : ℕ → Finset (Fin 26) := fun a => orSupp.getD (leafWire a) ∅
  have hctr_spec : ∀ a ∈ T,
      orSupp.getD (opnd C a (sideIdx a)) ∅ = {ctr a} ∧
      ∀ v ∈ leafSet a, G0.Adj (ctr a) v := by
    intro a ha
    dsimp only [sideIdx, ctr, leafWire, leafSet]
    rw [dif_pos ha]
    split_ifs with h0
    · have hspec := (Finset.card_eq_one.mp h0).choose_spec
      refine ⟨hspec, fun v hv => ?_⟩
      exact (hT_star a ha).2.1 _ (Finset.eq_singleton_iff_unique_mem.mp hspec).1 v hv
    · have h1 := (hT_star a ha).2.2.resolve_left h0
      have hspec := (Finset.card_eq_one.mp h1).choose_spec
      refine ⟨hspec, fun v hv => ?_⟩
      exact ((hT_star a ha).2.1 v hv _ (Finset.eq_singleton_iff_unique_mem.mp hspec).1).symm
  have hedge_cov : ∀ u v : Fin 26, G0.Adj u v →
      ∃ a ∈ T, s(u, v) = s(ctr a, if u = ctr a then v else u) ∧
        (if u = ctr a then v else u) ∈ leafSet a := by
    intro u v huv
    let x := pairInput u v
    have htrace : ∀ w : ℕ, w < 26 + C.gates.length →
        (∀ y : Fin 26 → Bool, val C (List.ofFn y) w = true → graphFun G0 ∅ y = true) →
        val C (List.ofFn x) w = true →
        ∃ a ∈ T, val C (List.ofFn x) (26 + a) = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hBw hxw
        by_cases hw26 : w < 26
        · exfalso
          let z : Fin 26 → Bool := fun i => decide (i.val = w)
          have hz1 : val C (List.ofFn z) w = true := by rw [val_input C z w hw26]; simp [z]
          have hz2 := hBw z hz1
          rw [graphFun_empty_iff] at hz2
          obtain ⟨p, q, hpq, hp, hq⟩ := hz2
          simp only [z, decide_eq_true_eq] at hp hq
          exact G0.ne_of_adj hpq (Fin.ext (hp.trans hq.symm))
        · let k := w - 26
          have hk : k < C.gates.length := by omega
          have hw_eq : 26 + k = w := by omega
          have hkm : gateAt C k ∈ C.gates := by
            exact hgateAt_mem C k hk
          rcases hL.1.1 _ hkm with hand | hor
          · exact ⟨k, (hT_eq k).2 ⟨hk, hand⟩, by rwa [hw_eq]⟩
          · rw [← hw_eq, val_or C hL.1 x k hk hor] at hxw
            obtain ⟨i, j, hij⟩ := List.length_eq_two.mp (hL.1.2.2 _ hkm)
            have hi : opnd C k 0 < w := by
              have := hL.1.2.1 k hk i (by rw [hij]; simp); simp [opnd_def, hij]; omega
            have hj : opnd C k 1 < w := by
              have := hL.1.2.1 k hk j (by rw [hij]; simp); simp [opnd_def, hij]; omega
            have hBi : ∀ b : Fin 2, ∀ y : Fin 26 → Bool, val C (List.ofFn y) (opnd C k b) = true → graphFun G0 ∅ y = true := by
              intro b y hy
              apply hBw y
              rw [← hw_eq, val_or C hL.1 y k hk hor]
              fin_cases b
              · exact Or.inl hy
              · exact Or.inr hy
            rcases hxw with h0 | h1
            · exact ih (opnd C k 0) hi (by omega) (hBi 0) h0
            · exact ih (opnd C k 1) hj (by omega) (hBi 1) h1
    have hout_true : val C (List.ofFn x) C.output = true := by
      have hfun := congrFun hL.2.1 x
      change val C (List.ofFn x) C.output = graphFun G0 ∅ x at hfun
      rw [hfun]
      rw [graphFun_empty_iff]
      exact ⟨u, v, huv, by simp [x, pairInput_def], by simp [x, pairInput_def]⟩
    have houtB : ∀ y : Fin 26 → Bool, val C (List.ofFn y) C.output = true → graphFun G0 ∅ y = true := by
      intro y hy
      have hfun := congrFun hL.2.1 y
      change val C (List.ofFn y) C.output = graphFun G0 ∅ y at hfun
      rwa [← hfun]
    obtain ⟨a, ha, ha_true⟩ := htrace C.output hout_bounds.2 houtB hout_true
    have ha_lt := ((hT_eq a).1 ha).1
    have ha_op := ((hT_eq a).1 ha).2
    have hna0 := hand_opnd_noAnd a ha_lt ha_op 0
    have hna1 := hand_opnd_noAnd a ha_lt ha_op 1
    have ha_mem : gateAt C a ∈ C.gates := by
      exact hgateAt_mem C a ha_lt
    obtain ⟨w0, w1, hw⟩ := List.length_eq_two.mp (hL.1.2.2 _ ha_mem)
    have h0_lt : opnd C a 0 < 26 + C.gates.length := by
      have := hL.1.2.1 a ha_lt w0 (by rw [hw]; simp); simp [opnd_def, hw]; omega
    have h1_lt : opnd C a 1 < 26 + C.gates.length := by
      have := hL.1.2.1 a ha_lt w1 (by rw [hw]; simp); simp [opnd_def, hw]; omega
    rw [val_and C hL.1 x a ha_lt ha_op] at ha_true
    obtain ⟨h0, h1⟩ := ha_true
    rw [hval_orSupp (opnd C a 0) h0_lt hna0 x] at h0
    rw [hval_orSupp (opnd C a 1) h1_lt hna1 x] at h1
    obtain ⟨t0, ht0, hxt0⟩ := h0
    obtain ⟨t1, ht1, hxt1⟩ := h1
    simp only [x, pairInput_def, decide_eq_true_eq] at hxt0 hxt1
    have hadj_t : G0.Adj t0 t1 := (hT_star a ha).2.1 t0 ht0 t1 ht1
    have hne_t : t0 ≠ t1 := G0.ne_of_adj hadj_t
    have hctr_spec_a := hctr_spec a ha
    have hits : (t0 = ctr a ∧ t1 ∈ leafSet a) ∨ (t1 = ctr a ∧ t0 ∈ leafSet a) := by
      by_cases hs : sideIdx a = 0
      · have h0s : orSupp.getD (opnd C a 0) ∅ = {ctr a} := by rw [← hs]; exact hctr_spec_a.1
        have ht0' : t0 = ctr a := by rw [h0s, Finset.mem_singleton] at ht0; exact ht0
        have hl1 : leafSet a = orSupp.getD (opnd C a 1) ∅ := by
          dsimp only [leafSet, leafWire]; rw [hs]; rfl
        exact Or.inl ⟨ht0', by rw [hl1]; exact ht1⟩
      · have h1eq : sideIdx a = 1 := Fin.ext (by have := (sideIdx a).isLt; omega)
        have h1s : orSupp.getD (opnd C a 1) ∅ = {ctr a} := by rw [← h1eq]; exact hctr_spec_a.1
        have ht1' : t1 = ctr a := by rw [h1s, Finset.mem_singleton] at ht1; exact ht1
        have hl0 : leafSet a = orSupp.getD (opnd C a 0) ∅ := by
          dsimp only [leafSet, leafWire]; rw [h1eq]; rfl
        exact Or.inr ⟨ht1', by rw [hl0]; exact ht0⟩
    rcases hits with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;> rcases hxt0 with rfl | rfl <;> rcases hxt1 with rfl | rfl
    · exact (hne_t rfl).elim
    · exact ⟨a, ha, by rw [if_pos rfl], by rw [if_pos rfl]; exact hl⟩
    · exact ⟨a, ha, by rw [if_neg (G0.ne_of_adj huv)]; exact Sym2.eq_swap, by rw [if_neg (G0.ne_of_adj huv)]; exact hl⟩
    · exact (hne_t rfl).elim
    · exact (hne_t rfl).elim
    · exact ⟨a, ha, by rw [if_neg (G0.ne_of_adj huv)]; exact Sym2.eq_swap, by rw [if_neg (G0.ne_of_adj huv)]; exact hl⟩
    · exact ⟨a, ha, by rw [if_pos rfl], by rw [if_pos rfl]; exact hl⟩
    · exact (hne_t rfl).elim
  have h12_T : 12 ≤ T.card := by
    have hcov : ∀ u v : Fin 26, G0.Adj u v → u ∈ T.image ctr ∨ v ∈ T.image ctr := by
      intro u v huv
      obtain ⟨a, ha, hsym, _⟩ := hedge_cov u v huv
      have hmem : ctr a ∈ s(u, v) := by rw [hsym]; exact Sym2.mem_mk_left _ _
      rw [Sym2.mem_iff] at hmem
      rcases hmem with h | h
      · exact Or.inl (Finset.mem_image.mpr ⟨a, ha, h⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨a, ha, h⟩)
    exact (hcover12 (T.image ctr) hcov).trans Finset.card_image_le
  let OrStepR : ℕ → ℕ → Prop := fun u v =>
    ∃ k < C.gates.length, u = 26 + k ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
  let Tc : Fin 26 → Finset ℕ := fun c => T.filter fun a => ctr a = c
  let Reach_c : Fin 26 → Finset ℕ := fun c =>
    (Finset.range (26 + C.gates.length)).filter fun w =>
      ∃ a ∈ Tc c, Relation.ReflTransGen OrStepR (leafWire a) w
  let Oc : Fin 26 → Finset ℕ := fun c =>
    ((Reach_c c).filter fun w => 26 ≤ w).image fun w => w - 26
  have hReach_sub_leaf : ∀ c : Fin 26, ∀ w ∈ Reach_c c, ∃ a ∈ Tc c,
      w < 26 + C.gates.length ∧ noAndBelow w ∧ orSupp.getD w ∅ ⊆ leafSet a := by
    intro c w hw
    simp only [Reach_c, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hw_lt, a, haTc, hr⟩ := hw
    have haT : a ∈ T := (Finset.mem_filter.mp haTc).1
    have ha_lt := ((hT_eq a).1 haT).1
    have ha_op := ((hT_eq a).1 haT).2
    have hna_start : noAndBelow (leafWire a) := hand_opnd_noAnd a ha_lt ha_op (1 - sideIdx a)
    have hstep : ∀ u v : ℕ, Relation.ReflTransGen OrStepR u v →
        u < 26 + C.gates.length → noAndBelow u →
        v < 26 + C.gates.length ∧ noAndBelow v ∧ orSupp.getD v ∅ ⊆ orSupp.getD u ∅ := by
      intro u v huv
      induction huv with
      | refl => intro hu hnu; exact ⟨hu, hnu, Finset.Subset.refl _⟩
      | @tail y z _ hyz ih =>
        intro hu hnu
        obtain ⟨hy_lt, hny, hy_sub⟩ := ih hu hnu
        obtain ⟨k, hk, hy_eq, hkop, hzm⟩ := hyz
        have hz_lt : z < 26 + k := hL.1.2.1 k hk z hzm
        have hy26 : 26 ≤ y := by omega
        obtain ⟨_, hna0, hna1⟩ := hnoAnd_child y hy_lt hny hy26
        have hk_eq : y - 26 = k := by omega
        rw [hk_eq] at hna0 hna1
        have hkm : gateAt C k ∈ C.gates := by
          exact hgateAt_mem C k hk
        obtain ⟨p0, p1, hp⟩ := List.length_eq_two.mp (hL.1.2.2 _ hkm)
        have hz_opnd : z = opnd C k 0 ∨ z = opnd C k 1 := by
          rw [hp] at hzm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hzm
          rcases hzm with h | h
          · exact Or.inl (by simp [opnd_def, hp, h])
          · exact Or.inr (by simp [opnd_def, hp, h])
        have hnz : noAndBelow z := by rcases hz_opnd with rfl | rfl <;> assumption
        have hz_sub : orSupp.getD z ∅ ⊆ orSupp.getD y ∅ := by
          rw [hy_eq, hsupp_or k hk hkop]
          rcases hz_opnd with rfl | rfl
          · exact Finset.subset_union_left
          · exact Finset.subset_union_right
        exact ⟨by omega, hnz, hz_sub.trans hy_sub⟩
    have hlw_lt : leafWire a < 26 + C.gates.length := by
      have ha_mem : gateAt C a ∈ C.gates := by
        exact hgateAt_mem C a ha_lt
      obtain ⟨w0, w1, hw⟩ := List.length_eq_two.mp (hL.1.2.2 _ ha_mem)
      have h_op_lt : ∀ b : Fin 2, opnd C a b < 26 + C.gates.length := by
        intro b
        have hbm : opnd C a b ∈ (gateAt C a).inputs := by fin_cases b <;> simp [opnd_def, hw]
        have := hL.1.2.1 a ha_lt _ hbm
        omega
      exact h_op_lt (1 - sideIdx a)
    exact ⟨a, haTc, hstep (leafWire a) w hr hlw_lt hna_start⟩
  have hOc_sub : ∀ c : Fin 26, Oc c ⊆ ON := by
    intro c k hk
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
    have hwR := (Finset.mem_filter.mp hw).1
    have hw26 := (Finset.mem_filter.mp hw).2
    obtain ⟨a, haTc, hw_lt, hna, hsub⟩ := hReach_sub_leaf c w hwR
    have hk_lt : w - 26 < C.gates.length := by omega
    have hkop : (gateAt C (w - 26)).op = GateOp.or := (hnoAnd_child w hw_lt hna hw26).1
    have hk_nb : ¬ BelowF G0 C (w - 26) := by
      intro hB
      have haT : a ∈ T := (Finset.mem_filter.mp haTc).1
      have ha_lt := ((hT_eq a).1 haT).1
      have ha_op := ((hT_eq a).1 haT).2
      have hno := hno_const_false (w - 26) hk_lt
      obtain ⟨x, hx⟩ := hno
      have hxw : val C (List.ofFn x) w = true := by simpa [show 26 + (w - 26) = w by omega] using hx
      rw [hval_orSupp w hw_lt hna x] at hxw
      obtain ⟨t, ht, _⟩ := hxw
      let y : Fin 26 → Bool := fun i => decide (i = t)
      have hyw : val C (List.ofFn y) w = true :=
        (hval_orSupp w hw_lt hna y).mpr ⟨t, ht, by simp [y]⟩
      have hyF := hB y (show val C (List.ofFn y) (26 + (w - 26)) = true by rw [show 26 + (w - 26) = w by omega]; exact hyw)
      rw [graphFun_empty_iff] at hyF
      obtain ⟨u, v, huv, hu, hv⟩ := hyF
      simp only [y, decide_eq_true_eq] at hu hv
      exact G0.ne_of_adj huv (hu.trans hv.symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, hkop, hk_nb⟩
  have hOc_disj : ∀ c1 c2 : Fin 26, c1 ≠ c2 → Disjoint (Oc c1) (Oc c2) := by
    intro c1 c2 hne
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨w1, hw1, rfl⟩ := Finset.mem_image.mp hk1
    obtain ⟨w2, hw2, heqw⟩ := Finset.mem_image.mp hk2
    have hw1R := (Finset.mem_filter.mp hw1).1
    have hw1_26 := (Finset.mem_filter.mp hw1).2
    have hw2R := (Finset.mem_filter.mp hw2).1
    have hw2_26 := (Finset.mem_filter.mp hw2).2
    have hw_eq : w1 = w2 := by omega
    subst hw_eq
    obtain ⟨a1, ha1Tc, hw1_lt, hna1, hsub1⟩ := hReach_sub_leaf c1 w1 hw1R
    obtain ⟨a2, ha2Tc, _, _, hsub2⟩ := hReach_sub_leaf c2 w1 hw2R
    have hc1 : ctr a1 = c1 := (Finset.mem_filter.mp ha1Tc).2
    have hc2 : ctr a2 = c2 := (Finset.mem_filter.mp ha2Tc).2
    have hk_orN : w1 - 26 ∈ ON := hOc_sub c1 (Finset.mem_image.mpr ⟨w1, hw1, rfl⟩)
    have hcard := horN_card2 (w1 - 26) hk_orN
    rw [show 26 + (w1 - 26) = w1 by omega] at hcard
    have hsub_nbr : orSupp.getD w1 ∅ ⊆ Finset.univ.filter fun v => G0.Adj c1 v ∧ G0.Adj c2 v := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := (hctr_spec a1 (Finset.mem_filter.mp ha1Tc).1).2 v (hsub1 hv)
      have h2 := (hctr_spec a2 (Finset.mem_filter.mp ha2Tc).1).2 v (hsub2 hv)
      rw [hc1] at h1; rw [hc2] at h2
      exact ⟨h1, h2⟩
    have := (Finset.card_le_card hsub_nbr).trans (hnoC4 c1 c2 hne)
    omega
  have hReach_count : ∀ c : Fin 26,
      ((Reach_c c).filter fun w => w < 26).card ≤ (Tc c).card + (Oc c).card := by
    intro c
    let R_roots := (Tc c).image leafWire
    let G_gates := (Reach_c c).filter fun w => 26 ≤ w
    have hcov_R : Reach_c c ⊆ R_roots ∪ G_gates.biUnion fun w => (gateAt C (w - 26)).inputs.toFinset := by
      intro w hw
      simp only [Reach_c, Finset.mem_filter, Finset.mem_range] at hw
      obtain ⟨hw_lt, a, haTc, hr⟩ := hw
      rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨y, hyr, hyw⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haTc, rfl⟩)
      · obtain ⟨k, hk, hy_eq, _, hwm⟩ := hyw
        have hy_lt : y < 26 + C.gates.length := by omega
        have hy_mem : y ∈ G_gates := Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy_lt, a, haTc, hyr⟩, by omega⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨y, hy_mem, List.mem_toFinset.mpr (by simpa [hy_eq, Nat.add_sub_cancel_left] using hwm)⟩)
    have hbi_le : (G_gates.biUnion fun w => (gateAt C (w - 26)).inputs.toFinset).card ≤ 2 * G_gates.card := by
      calc (G_gates.biUnion fun w => (gateAt C (w - 26)).inputs.toFinset).card
          ≤ ∑ w ∈ G_gates, ((gateAt C (w - 26)).inputs.toFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ G_gates, 2 := by
            refine Finset.sum_le_sum fun w hw => ?_
            have hwR := (Finset.mem_filter.mp hw).1
            have hw26 := (Finset.mem_filter.mp hw).2
            have hw_lt : w < 26 + C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hwR).1
            have hkm : gateAt C (w - 26) ∈ C.gates := by
              exact hgateAt_mem C (w - 26) (by omega)
            exact (List.toFinset_card_le _).trans_eq (hL.1.2.2 _ hkm)
        _ = 2 * G_gates.card := by simp [Nat.mul_comm]
    have hR_le : (Reach_c c).card ≤ (Tc c).card + 2 * G_gates.card := by
      calc (Reach_c c).card
          ≤ (R_roots ∪ G_gates.biUnion fun w => (gateAt C (w - 26)).inputs.toFinset).card :=
            Finset.card_le_card hcov_R
        _ ≤ R_roots.card + (G_gates.biUnion fun w => (gateAt C (w - 26)).inputs.toFinset).card :=
            Finset.card_union_le _ _
        _ ≤ (Tc c).card + 2 * G_gates.card := by
            have : R_roots.card ≤ (Tc c).card := Finset.card_image_le (s := Tc c) (f := leafWire)
            omega
    have hdisj_RG : Disjoint ((Reach_c c).filter fun w => w < 26) G_gates := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    have hun_RG : ((Reach_c c).filter fun w => w < 26) ∪ G_gates = Reach_c c := by
      ext w
      simp only [G_gates, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hw26 : w < 26
        · exact Or.inl ⟨h, hw26⟩
        · exact Or.inr ⟨h, by omega⟩
    have hRG_card : ((Reach_c c).filter fun w => w < 26).card + G_gates.card = (Reach_c c).card := by
      rw [← Finset.card_union_of_disjoint hdisj_RG, hun_RG]
    have hG_eq_Oc : G_gates.card = (Oc c).card := by
      apply (Finset.card_image_of_injOn _).symm
      intro w1 hw1 w2 hw2 heq
      have h1 := (Finset.mem_filter.mp hw1).2
      have h2 := (Finset.mem_filter.mp hw2).2
      change w1 - 26 = w2 - 26 at heq
      omega
    omega
  have horSupp_reach : ∀ w : ℕ, w < 26 + C.gates.length → noAndBelow w →
      ∀ t ∈ orSupp.getD w ∅, Relation.ReflTransGen OrStepR w t.val := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hna t ht
      by_cases hw26 : w < 26
      · rw [hsupp_input w hw26, Finset.mem_singleton] at ht
        subst ht
        exact Relation.ReflTransGen.refl
      · have hge : 26 ≤ w := by omega
        obtain ⟨hkop, hna0, hna1⟩ := hnoAnd_child w hw hna hge
        let k := w - 26
        have hk : k < C.gates.length := by omega
        have hw_eq : 26 + k = w := by omega
        have hkm : gateAt C k ∈ C.gates := by
          exact hgateAt_mem C k hk
        obtain ⟨a0, a1, ha⟩ := List.length_eq_two.mp (hL.1.2.2 _ hkm)
        have h0_lt : opnd C k 0 < w := by
          have := hL.1.2.1 k hk a0 (by rw [ha]; simp); simp [opnd_def, ha]; omega
        have h1_lt : opnd C k 1 < w := by
          have := hL.1.2.1 k hk a1 (by rw [ha]; simp); simp [opnd_def, ha]; omega
        rw [← hw_eq, hsupp_or k hk hkop, Finset.mem_union] at ht
        rcases ht with ht0 | ht1
        · have hr := ih (opnd C k 0) h0_lt (by omega) hna0 t ht0
          refine Relation.ReflTransGen.head ⟨k, hk, hw_eq.symm, hkop, ?_⟩ hr
          simp [opnd_def, ha]
        · have hr := ih (opnd C k 1) h1_lt (by omega) hna1 t ht1
          refine Relation.ReflTransGen.head ⟨k, hk, hw_eq.symm, hkop, ?_⟩ hr
          simp [opnd_def, ha]
  have hedge_in_Reach : ∀ e ∈ G0.edgeFinset, ∃ c : Fin 26, ∃ w ∈ (Reach_c c).filter (fun w => w < 26),
      e = if hw : w < 26 then s(c, ⟨w, hw⟩) else s(c, c) := by
    intro e he
    obtain ⟨⟨u, v⟩, huv_eq⟩ := Quot.exists_rep e
    have he_eq : e = s(u, v) := huv_eq.symm
    rw [he_eq] at he ⊢
    · have huv : G0.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨a, ha, hsym, hl⟩ := hedge_cov u v huv
      let c := ctr a
      let l := if u = c then v else u
      have ha_lt := ((hT_eq a).1 ha).1
      have ha_op := ((hT_eq a).1 ha).2
      have ha_mem : gateAt C a ∈ C.gates := by
        exact hgateAt_mem C a ha_lt
      obtain ⟨w0, w1, hw⟩ := List.length_eq_two.mp (hL.1.2.2 _ ha_mem)
      have hlw_lt : leafWire a < 26 + C.gates.length := by
        have h_op_lt : ∀ b : Fin 2, opnd C a b < 26 + C.gates.length := by
          intro b
          have hbm : opnd C a b ∈ (gateAt C a).inputs := by fin_cases b <;> simp [opnd_def, hw]
          have := hL.1.2.1 a ha_lt _ hbm
          omega
        exact h_op_lt (1 - sideIdx a)
      have hna := hand_opnd_noAnd a ha_lt ha_op (1 - sideIdx a)
      have hr := horSupp_reach (leafWire a) hlw_lt hna l hl
      have hwR : l.val ∈ (Reach_c c).filter (fun w => w < 26) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), a, ?_, hr⟩, l.isLt⟩
        exact Finset.mem_filter.mpr ⟨ha, rfl⟩
      refine ⟨c, l.val, hwR, ?_⟩
      rw [dif_pos l.isLt]
      exact hsym
  let allLeaves : Finset (Sym2 (Fin 26)) :=
    (Finset.univ : Finset (Fin 26)).biUnion fun c =>
      ((Reach_c c).filter fun w => w < 26).image fun w => if hw : w < 26 then s(c, ⟨w, hw⟩) else s(c, c)
  have h48_le : 48 ≤ T.card + ON.card := by
    have hsub : G0.edgeFinset ⊆ allLeaves := by
      intro e he
      obtain ⟨c, w, hw, rfl⟩ := hedge_in_Reach e he
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
    have h1 : G0.edgeFinset.card ≤ allLeaves.card := Finset.card_le_card hsub
    have h2 : allLeaves.card ≤ ∑ c : Fin 26, ((Reach_c c).filter fun w => w < 26).card := by
      calc allLeaves.card
          ≤ ∑ c : Fin 26, (((Reach_c c).filter fun w => w < 26).image fun w =>
              if hw : w < 26 then s(c, ⟨w, hw⟩) else s(c, c)).card := Finset.card_biUnion_le
        _ ≤ ∑ c : Fin 26, ((Reach_c c).filter fun w => w < 26).card :=
            Finset.sum_le_sum fun c _ => Finset.card_image_le
    have h3 : (∑ c : Fin 26, ((Reach_c c).filter fun w => w < 26).card) ≤
        (∑ c : Fin 26, (Tc c).card) + ∑ c : Fin 26, (Oc c).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun c _ => hReach_count c
    have hTc_sum : (∑ c : Fin 26, (Tc c).card) = T.card := by
      have hdisj : ∀ c1 ∈ (Finset.univ : Finset (Fin 26)), ∀ c2 ∈ (Finset.univ : Finset (Fin 26)),
          c1 ≠ c2 → Disjoint (Tc c1) (Tc c2) := by
        intro c1 _ c2 _ hne
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
      have hun : (Finset.univ : Finset (Fin 26)).biUnion Tc = T := by
        ext a
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Tc, Finset.mem_filter]
        exact ⟨fun h => by obtain ⟨_, h1, _⟩ := h; exact h1, fun h => ⟨ctr a, h, rfl⟩⟩
      rw [← hun, Finset.card_biUnion hdisj]
    have hOc_sum : (∑ c : Fin 26, (Oc c).card) ≤ ON.card := by
      have hun : (Finset.univ : Finset (Fin 26)).biUnion Oc ⊆ ON := by
        intro k hk
        obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hk
        exact hOc_sub c hkc
      rw [← Finset.card_biUnion (fun c1 _ c2 _ hne => hOc_disj c1 c2 hne)]
      exact Finset.card_le_card hun
    rw [hedgeCard] at h1
    omega
  change 59 ≤ C.gates.length
  omega
