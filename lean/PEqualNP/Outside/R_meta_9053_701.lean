import PEqualNP.Defs

open PEqualNP.AndCount

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_9053_701
    (hNorm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : AndCountCircuit n),
      C.WellFormed → C.Computes G →
      ∃ D : AndCountCircuit n, D.WellFormed ∧ D.Computes G ∧ D.size ≤ C.size ∧
        ∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i))
    (hDirty19 :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size ≤ 19 →
        (∃ i : Fin C.size, ∃ u ∈ C.leftVars i, ∃ v ∈ C.rightVars i, ¬ G.Adj u v) → False)
    (hDirty20 :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 20 →
        (∃ i : Fin C.size, ∃ u ∈ C.leftVars i, ∃ v ∈ C.rightVars i, ¬ G.Adj u v) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : Fin (3 : ℕ) → Fin (14 : ℕ) → Fin (42 : ℕ) := fun (x2 : Fin (3 : ℕ)) (x3 : Fin (14 : ℕ)) => Fin.ofNat (42 : ℕ) (if ↑x3 < (7 : ℕ) then ((9 : ℕ) * ↑x3 + ↑x2) % (21 : ℕ) else (21 : ℕ) + ((9 : ℕ) * (↑x3 - (7 : ℕ)) + ↑x2 + (5 : ℕ)) % (21 : ℕ)); ∀ (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x3.WellFormed → x3.Computes x1 → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x7 : Fin (3 : ℕ)), x6.WellFormed ∧ x6.Computes x1 ∧ x6.size ≤ x3.size ∧ (3 : ℕ) * {x8 : Fin x6.size | x6.gateVal (Finset.image (x2 x7) Finset.univ) x8 = Bool.true}.ncard ≤ x6.size := by
  dsimp only at hDirty19 hDirty20 ⊢
  let Rrel : Fin 42 → Fin 42 → Prop := fun a b =>
    a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  let e : Fin 3 → Fin 14 → Fin 42 := fun r j =>
    Fin.ofNat 42 (if j.val < 7 then (9 * j.val + r.val) % 21
      else 21 + (9 * (j.val - 7) + r.val + 5) % 21)
  have hCard7 : (Finset.univ.filter (fun j : Fin 21 => Fin.castAdd 21 j ∈ Finset.image (e 0) Finset.univ)).card = 7 := by
    decide
  have hDiffUnique : ∀ (p d1 d2 : ℕ), p < 21 → p ≠ 0 → d1 ≠ d2 →
      d1 ∈ ([0, 5, 7, 17, 20] : List ℕ) → d2 ∈ ([0, 5, 7, 17, 20] : List ℕ) →
      (d1 + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) →
      (d2 + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) → False := by
    intro p d1 d2 hp hp0 hne hd1 hd2 hm1 hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd1 hd2 hm1 hm2
    rcases hd1 with rfl | rfl | rfl | rfl | rfl <;>
    rcases hd2 with rfl | rfl | rfl | rfl | rfl <;>
    omega
  have hDeg5 : ∀ u : Fin 42, (Finset.univ.filter (fun v : Fin 42 => Rrel u v ∨ Rrel v u)).card = 5 := by
    decide +kernel
  have h105 : (Finset.univ.filter (fun p : Fin 42 × Fin 42 => Rrel p.1 p.2)).card = 105 := by
    decide +kernel
  classical
  intro C hWF hComp
  let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel Rrel
  have hAdj : ∀ a b : Fin 42, G.Adj a b ↔ (Rrel a b ∨ Rrel b a) := by
    intro a b
    rw [SimpleGraph.fromRel_adj]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega
  by_cases hBig : 21 ≤ C.size
  · -- Explicit 21-gate point-star circuit balanced on Fano block r = 0
    let S0 : AndCountCircuit 42 := {
      size := 21
      leftVars := fun j => {Fin.castAdd 21 j}
      leftGates := fun _ => ∅
      rightVars := fun j => Finset.univ.filter (fun w : Fin 42 => G.Adj (Fin.castAdd 21 j) w)
      rightGates := fun _ => ∅
      outVars := ∅
      outGates := Finset.univ
    }
    obtain ⟨S, hSsz, hSlv, hSlg, hSrv, hSrg, hSov, hSog⟩ :
        ∃ S : AndCountCircuit 42,
          ∃ hsz : S.size = 21,
          (∀ j : Fin S.size, S.leftVars j = {Fin.castAdd 21 ⟨j.val, by omega⟩}) ∧
          (∀ j : Fin S.size, S.leftGates j = ∅) ∧
          (∀ j : Fin S.size, S.rightVars j = Finset.univ.filter (fun w : Fin 42 => G.Adj (Fin.castAdd 21 ⟨j.val, by omega⟩) w)) ∧
          (∀ j : Fin S.size, S.rightGates j = ∅) ∧
          S.outVars = ∅ ∧
          S.outGates = Finset.univ :=
      ⟨S0, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩
    have hSWF : S.WellFormed := fun j => ⟨by rw [hSlg]; simp, by rw [hSrg]; simp⟩
    have hNoGates : ∀ (U B : Finset (Fin 42)) (i : Fin S.size) (val : Fin S.size → Bool),
        AndCountCircuit.sideTrue U B ∅ i val = decide (∃ v ∈ B, v ∈ U) := by
      intro U B i val
      unfold AndCountCircuit.sideTrue
      simp
    have hSGV : ∀ (U : Finset (Fin 42)) (j : Fin S.size),
        S.gateVal U j = true ↔
          (Fin.castAdd 21 ⟨j.val, by omega⟩ ∈ U ∧ ∃ w ∈ U, G.Adj (Fin.castAdd 21 ⟨j.val, by omega⟩) w) := by
      intro U j
      have hfuel : S.gateVal U j = S.gateValFuel U (20 + 1) j := by
        change S.gateValFuel U S.size j = S.gateValFuel U (20 + 1) j
        rw [hSsz]
      rw [hfuel]
      change (AndCountCircuit.sideTrue U (S.leftVars j) (S.leftGates j) j (S.gateValFuel U 20) &&
          AndCountCircuit.sideTrue U (S.rightVars j) (S.rightGates j) j (S.gateValFuel U 20)) = true ↔ _
      rw [hSlg j, hSrg j, hNoGates, hNoGates, hSlv j, hSrv j]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_singleton, exists_eq_left,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, w, h2, h3⟩; exact ⟨h1, w, h3, h2⟩
      · rintro ⟨h1, w, h2, h3⟩; exact ⟨h1, w, h3, h2⟩
    have hSComp : S.Computes G := by
      intro U
      unfold AndCountCircuit.eval
      rw [hSov, hSog]
      simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj⟩
        obtain ⟨h1, w, hw, hadj⟩ := (hSGV U j).mp hj
        exact ⟨Fin.castAdd 21 ⟨j.val, by omega⟩, h1, w, hw, hadj⟩
      · rintro ⟨a, ha, c, hc, hadj⟩
        rcases (hAdj a c).mp hadj with ⟨ha21, _, _⟩ | ⟨hc21, _, _⟩
        · let j : Fin S.size := ⟨a.val, by omega⟩
          have haj : Fin.castAdd 21 ⟨j.val, by omega⟩ = a := by ext; simp [j]
          exact ⟨j, (hSGV U j).mpr ⟨haj.symm ▸ ha, c, hc, haj.symm ▸ hadj⟩⟩
        · let j : Fin S.size := ⟨c.val, by omega⟩
          have hcj : Fin.castAdd 21 ⟨j.val, by omega⟩ = c := by ext; simp [j]
          exact ⟨j, (hSGV U j).mpr ⟨hcj.symm ▸ hc, a, ha, hcj.symm ▸ hadj.symm⟩⟩
    let to21 : Fin S.size → Fin 21 := fun j => ⟨j.val, by omega⟩
    have hNcard : {j : Fin S.size | S.gateVal (Finset.image (e 0) Finset.univ) j = true}.ncard ≤ 7 := by
      let A : Finset (Fin S.size) :=
        Finset.univ.filter (fun j : Fin S.size => S.gateVal (Finset.image (e 0) Finset.univ) j = true)
      have hset : {j : Fin S.size | S.gateVal (Finset.image (e 0) Finset.univ) j = true} = ↑A := by
        ext j; simp [A]
      rw [hset, Set.ncard_coe_finset]
      have hMaps : ∀ j ∈ A, to21 j ∈
          Finset.univ.filter (fun j : Fin 21 => Fin.castAdd 21 j ∈ Finset.image (e 0) Finset.univ) := by
        intro j hj
        have hgv : S.gateVal (Finset.image (e 0) Finset.univ) j = true := (Finset.mem_filter.mp hj).2
        have h1 : Fin.castAdd 21 (to21 j) ∈ Finset.image (e 0) Finset.univ := ((hSGV _ j).mp hgv).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
      have hInj : Set.InjOn to21 ↑A := fun a _ b _ h => Fin.ext (congrArg (Fin.val : Fin 21 → ℕ) h)
      exact (Finset.card_le_card_of_injOn to21 hMaps hInj).trans (le_of_eq hCard7)
    refine ⟨S, 0, hSWF, hSComp, by omega, ?_⟩
    change 3 * {j : Fin S.size | S.gateVal (Finset.image (e 0) Finset.univ) j = true}.ncard ≤ S.size
    omega
  · -- Case C.size ≤ 20: normalize, rule out clean-only circuits by 20*5 < 105, then dispatch to hDirty19/hDirty20
    exfalso
    obtain ⟨D, hDWF, hDComp, hDsz, hDdisj⟩ := hNorm 42 G C hWF hComp
    have hDout : D.outVars = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      have hev : D.eval {v} = true := by
        unfold AndCountCircuit.eval
        rw [decide_eq_true_eq]
        exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
      obtain ⟨a, ha, c, hc, hadj⟩ := (hDComp {v}).mp hev
      rw [Finset.mem_singleton] at ha hc
      subst ha; subst hc
      exact G.ne_of_adj hadj rfl
    have hBirth : ∀ u v : Fin 42, G.Adj u v →
        ∃ i : Fin D.size, (u ∈ D.leftVars i ∧ v ∈ D.rightVars i) ∨ (v ∈ D.leftVars i ∧ u ∈ D.rightVars i) := by
      intro u v huv
      have hev : D.eval {u, v} = true := (hDComp {u, v}).mpr ⟨u, by simp, v, by simp, huv⟩
      unfold AndCountCircuit.eval at hev
      rw [decide_eq_true_eq] at hev
      simp only [hDout, Finset.notMem_empty, false_and, exists_false, false_or] at hev
      obtain ⟨j, _, hj⟩ := hev
      have hfuel : ∀ (d : ℕ) (i : Fin D.size), D.gateValFuel {u, v} d i = true →
          ∃ k : Fin D.size, (u ∈ D.leftVars k ∧ v ∈ D.rightVars k) ∨ (v ∈ D.leftVars k ∧ u ∈ D.rightVars k) := by
        intro d
        induction d with
        | zero =>
          intro _ h
          change false = true at h
          exact Bool.noConfusion h
        | succ d ih =>
          intro i hi
          change (decide ((∃ w ∈ D.leftVars i, w ∈ ({u, v} : Finset (Fin 42))) ∨
              ∃ j ∈ D.leftGates i, j < i ∧ D.gateValFuel {u, v} d j = true) &&
            decide ((∃ w ∈ D.rightVars i, w ∈ ({u, v} : Finset (Fin 42))) ∨
              ∃ j ∈ D.rightGates i, j < i ∧ D.gateValFuel {u, v} d j = true)) = true at hi
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hi
          rcases hi with ⟨hL, hR⟩
          rcases hL with ⟨a, haL, haUV⟩ | ⟨k, _, _, hk⟩
          · rcases hR with ⟨b, hbR, hbUV⟩ | ⟨k, _, _, hk⟩
            · rw [Finset.mem_insert, Finset.mem_singleton] at haUV hbUV
              rcases haUV with rfl | rfl <;> rcases hbUV with rfl | rfl
              · exact (Finset.disjoint_left.mp (hDdisj i) haL hbR).elim
              · exact ⟨i, Or.inl ⟨haL, hbR⟩⟩
              · exact ⟨i, Or.inr ⟨haL, hbR⟩⟩
              · exact (Finset.disjoint_left.mp (hDdisj i) haL hbR).elim
            · exact ih k hk
          · exact ih k hk
      exact hfuel D.size j hj
    by_cases hDirty : ∃ i : Fin D.size, ∃ u ∈ D.leftVars i, ∃ v ∈ D.rightVars i, ¬ G.Adj u v
    · by_cases h19 : D.size ≤ 19
      · exact hDirty19 D hDWF hDComp hDout hDdisj h19 hDirty
      · exact hDirty20 D hDWF hDComp hDout hDdisj (by omega) hDirty
    · push Not at hDirty
      -- All gates clean: C4-freeness (via mod-21 translation invariance) + degree 5 gives <= 5 edges per gate
      have hNoC4Bip : ∀ (p1 p2 l1 l2 : Fin 42), p1 ≠ p2 → l1 ≠ l2 →
          Rrel p1 l1 → Rrel p1 l2 → Rrel p2 l1 → ¬ Rrel p2 l2 := by
        intro p1 p2 l1 l2 hp hl h11 h12 h21 h22
        let dp : Fin 21 := ⟨(p2.val + 21 - p1.val) % 21, Nat.mod_lt _ (by omega)⟩
        let d1 : Fin 21 := ⟨(l1.val + 21 - p1.val) % 21, Nat.mod_lt _ (by omega)⟩
        let d2 : Fin 21 := ⟨(l2.val + 21 - p1.val) % 21, Nat.mod_lt _ (by omega)⟩
        have hdp : dp.val ≠ 0 := by
          intro h0
          apply hp; ext
          have := h11.1; have := h21.1
          simp only [dp] at h0; omega
        have hd12 : d1 ≠ d2 := by
          intro heq
          apply hl; ext
          have hval := congrArg Fin.val heq
          simp only [d1, d2] at hval
          have := h11.1; have := h11.2.1; have := h12.2.1; have := l1.isLt; have := l2.isLt
          omega
        have hm1 : (d1.val + 21 - dp.val) % 21 = (l1.val + 21 - p2.val) % 21 := by
          simp only [d1, dp]
          have := h11.1; have := h21.1; have := h11.2.1; have := l1.isLt
          omega
        have hm2 : (d2.val + 21 - dp.val) % 21 = (l2.val + 21 - p2.val) % 21 := by
          simp only [d2, dp]
          have := h11.1; have := h21.1; have := h12.2.1; have := l2.isLt
          omega
        exact hDiffUnique dp.val d1.val d2.val dp.isLt hdp (fun h => hd12 (Fin.ext h)) h11.2.2 h12.2.2 (hm1 ▸ h21.2.2) (hm2 ▸ h22.2.2)
      let Eall : Finset (Fin 42 × Fin 42) := Finset.univ.filter (fun p => Rrel p.1 p.2)
      let Egate (i : Fin D.size) : Finset (Fin 42 × Fin 42) :=
        Eall.filter (fun p => (p.1 ∈ D.leftVars i ∧ p.2 ∈ D.rightVars i) ∨
          (p.2 ∈ D.leftVars i ∧ p.1 ∈ D.rightVars i))
      have hCoverAll : Eall ⊆ Finset.univ.biUnion Egate := by
        intro p hp
        have hrel : Rrel p.1 p.2 := (Finset.mem_filter.mp hp).2
        obtain ⟨i, hi⟩ := hBirth p.1 p.2 ((hAdj p.1 p.2).mpr (Or.inl hrel))
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hp, hi⟩⟩
      have hGateLe5 : ∀ i : Fin D.size, (Egate i).card ≤ 5 := by
        intro i
        have hOneSide : (D.leftVars i).card ≤ 1 ∨ (D.rightVars i).card ≤ 1 := by
          by_contra hBoth
          push Not at hBoth
          obtain ⟨u1, hu1, u2, hu2, huNe⟩ := Finset.one_lt_card.mp hBoth.1
          obtain ⟨v1, hv1, v2, hv2, hvNe⟩ := Finset.one_lt_card.mp hBoth.2
          have e11 := (hAdj u1 v1).mp (hDirty i u1 hu1 v1 hv1)
          have e12 := (hAdj u1 v2).mp (hDirty i u1 hu1 v2 hv2)
          have e21 := (hAdj u2 v1).mp (hDirty i u2 hu2 v1 hv1)
          have e22 := (hAdj u2 v2).mp (hDirty i u2 hu2 v2 hv2)
          rcases e11 with r11 | r11
          · have r12 : Rrel u1 v2 := e12.resolve_right (fun h => by have := r11.1; have := h.2.1; omega)
            have r21 : Rrel u2 v1 := e21.resolve_right (fun h => by have := r11.2.1; have := h.1; omega)
            have r22 : Rrel u2 v2 := e22.resolve_right (fun h => by have := r21.1; have := h.2.1; omega)
            exact hNoC4Bip u1 u2 v1 v2 huNe hvNe r11 r12 r21 r22
          · have r12 : Rrel v2 u1 := e12.resolve_left (fun h => by have := r11.2.1; have := h.1; omega)
            have r21 : Rrel v1 u2 := e21.resolve_left (fun h => by have := r11.1; have := h.2.1; omega)
            have r22 : Rrel v2 u2 := e22.resolve_left (fun h => by have := r21.2.1; have := h.1; omega)
            exact hNoC4Bip v1 v2 u1 u2 hvNe huNe r11 r21 r12 r22
        have hStarLe : ∀ w : Fin 42,
            (Eall.filter (fun p => p.1 = w ∨ p.2 = w)).card ≤ 5 := by
          intro w
          let f : Fin 42 × Fin 42 → Fin 42 := fun p => if p.1 = w then p.2 else p.1
          have hMaps : ∀ p ∈ Eall.filter (fun p => p.1 = w ∨ p.2 = w),
              f p ∈ Finset.univ.filter (fun v : Fin 42 => Rrel w v ∨ Rrel v w) := by
            intro p hp
            simp only [Finset.mem_filter, Eall, Finset.mem_univ, true_and] at hp ⊢
            rcases hp.2 with h1 | h2
            · subst h1; simp only [f, ite_true]; exact Or.inl hp.1
            · subst h2
              have hne : p.1 ≠ p.2 := fun h => by have := congrArg Fin.val h; have := hp.1.1; have := hp.1.2.1; omega
              simp only [f, hne, ite_false]; exact Or.inr hp.1
          have hInj : Set.InjOn f ↑(Eall.filter (fun p => p.1 = w ∨ p.2 = w)) := by
            intro p hp q hq hf
            simp only [Finset.mem_coe, Finset.mem_filter, Eall, Finset.mem_univ, true_and] at hp hq
            have hp_lt : p.1.val < 21 := hp.1.1
            have hp_ge : 21 ≤ p.2.val := hp.1.2.1
            have hq_lt : q.1.val < 21 := hq.1.1
            have hq_ge : 21 ≤ q.2.val := hq.1.2.1
            rcases hp.2 with hpw | hpw <;> rcases hq.2 with hqw | hqw
            · simp only [f, hpw, hqw, ite_true] at hf; exact Prod.ext (hpw.trans hqw.symm) hf
            · have := congrArg Fin.val (hpw.trans hqw.symm); omega
            · have := congrArg Fin.val (hpw.trans hqw.symm); omega
            · have hne1 : p.1 ≠ w := fun h => by have := congrArg Fin.val (h.trans hpw.symm); omega
              have hne2 : q.1 ≠ w := fun h => by have := congrArg Fin.val (h.trans hqw.symm); omega
              simp only [f, hne1, hne2, ite_false] at hf
              exact Prod.ext hf (hpw.trans hqw.symm)
          calc (Eall.filter (fun p => p.1 = w ∨ p.2 = w)).card
              ≤ (Finset.univ.filter (fun v : Fin 42 => Rrel w v ∨ Rrel v w)).card :=
                Finset.card_le_card_of_injOn f hMaps hInj
            _ = 5 := hDeg5 w
        rcases hOneSide with hL1 | hR1
        · rcases Finset.card_le_one_iff_subset_singleton.mp hL1 with ⟨w, hw⟩
          refine (Finset.card_le_card ?_).trans (hStarLe w)
          intro p hp
          simp only [Egate, Finset.mem_filter] at hp ⊢
          refine ⟨hp.1, ?_⟩
          rcases hp.2 with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inl (Finset.mem_singleton.mp (hw h1))
          · exact Or.inr (Finset.mem_singleton.mp (hw h1))
        · rcases Finset.card_le_one_iff_subset_singleton.mp hR1 with ⟨w, hw⟩
          refine (Finset.card_le_card ?_).trans (hStarLe w)
          intro p hp
          simp only [Egate, Finset.mem_filter] at hp ⊢
          refine ⟨hp.1, ?_⟩
          rcases hp.2 with ⟨_, h2⟩ | ⟨_, h2⟩
          · exact Or.inr (Finset.mem_singleton.mp (hw h2))
          · exact Or.inl (Finset.mem_singleton.mp (hw h2))
      have hBound : Eall.card ≤ D.size * 5 := by
        calc Eall.card
            ≤ (Finset.univ.biUnion Egate).card := Finset.card_le_card hCoverAll
          _ ≤ (Finset.univ : Finset (Fin D.size)).card * 5 :=
              Finset.card_biUnion_le_card_mul _ _ 5 (fun i _ => hGateLe5 i)
          _ = D.size * 5 := by simp
      have hEall105 : Eall.card = 105 := h105
      omega
