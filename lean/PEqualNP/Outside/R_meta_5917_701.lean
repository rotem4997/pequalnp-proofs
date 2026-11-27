import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_5917_701
    (deepDeepCleanCenters :
      ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
        IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
          ∀ e ∈ Ustar G C,
            (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
              u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
            (∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C,
              ∃ g ∈ junk G C, ∃ h ∈ junk G C,
              g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
              (∃ j ∈ junk G C, InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h) ∧
              gateVal n C g (pairInput u u) = true ∧ gateVal n C h (pairInput v v) = true ∧
              ((∀ S : Finset (Fin n), S.card ≤ 2 → u ∉ S →
                  gateVal n C g (fun i => decide (i ∈ S)) = true → ∃ x ∈ S, ∃ y ∈ S, G.Adj x y) ∨
               (∀ S : Finset (Fin n), S.card ≤ 2 → v ∉ S →
                  gateVal n C h (fun i => decide (i ∈ S)) = true → ∃ x ∈ S, ∃ y ∈ S, G.Adj x y))) →
            e ∈ E)
    (deepDeepBothPairOnly :
      ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
        IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
          ∀ e ∈ Ustar G C,
            (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
              u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
            (∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C,
              ∃ g ∈ junk G C, ∃ h ∈ junk G C,
              g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
              (∃ j ∈ junk G C, InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h) ∧
              gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
              gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧
              gateVal n C h (pairInput u u) = false ∧ gateVal n C h (pairInput v v) = false) →
            e ∈ E)
    (deepDeepOneSidedSing :
      ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
        IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
          ∀ e ∈ Ustar G C,
            (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
              u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
            (∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
              ∃ g ∈ junk G C, ∃ h ∈ junk G C,
              g ≠ h ∧ OrReaches n C (opnd C a b) g ∧ OrReaches n C (opnd C a (1 - b)) h ∧
              (∃ j ∈ junk G C, InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h) ∧
              gateVal n C g (pairInput u u) = true ∧ gateVal n C h (pairInput u v) = true ∧
              gateVal n C h (pairInput v v) = false) →
            e ∈ E) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∃ (x9 : Finset (Sym2 (Fin x2))), x9.card ≤ x1 * (x5.size + (1 : ℕ)) ∧ ∀ x10 ∈ PEqualNP.TopForm.Ustar x3 x5, (¬∃ (x12 : Fin x2) (x13 : Fin x2), x10 = s(x12, x13) ∧ ∃ x14 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x15 : Fin (2 : ℕ)), ∃ x16 ∈ PEqualNP.TopForm.junk x3 x5, x12 ∈ PEqualNP.TopForm.side x5 x14 x15 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x14 ((1 : Fin (2 : ℕ)) - x15)) x16 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x16 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (∃ (x13 : Fin x2) (x14 : Fin x2), x10 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x16 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x17 ∈ PEqualNP.TopForm.junk x3 x5, x16 ≠ x17 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x15 (0 : Fin (2 : ℕ))) x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x15 (1 : Fin (2 : ℕ))) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ (∃ x18 ∈ PEqualNP.TopForm.junk x3 x5, PEqualNP.EdgeOwnership.InCone x2 x5 x18 x16) ∧ ∃ x18 ∈ PEqualNP.TopForm.junk x3 x5, PEqualNP.EdgeOwnership.InCone x2 x5 x18 x17) → x10 ∈ x9 := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  let input {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ S)
  let hit {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
    ∃ u ∈ S, ∃ v ∈ S, G.Adj u v
  let fires {n : ℕ} (C : Circuit) (i : ℕ) (S : Finset (Fin n)) : Prop :=
    gateVal n C i (input S) = true
  -- Semantics 1: Monotonicity of AO2 circuits on all wires
  have wires_mono : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      ∀ (x y : Fin n → Bool), (∀ i, x i = true → y i = true) →
      ∀ k, (C.wires (List.ofFn x)).getD k false = true →
           (C.wires (List.ofFn y)).getD k false = true := by
    intro n C hAO x y hle
    have hfold : ∀ (gs : List Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        w1.length = w2.length →
        (∀ k, w1.getD k false = true → w2.getD k false = true) →
        ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD k false = true →
             (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD k false = true := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ hw k hk; exact hw k hk
      | cons g rest ih =>
        intro w1 w2 hgs hlen hw
        rw [List.foldl_cons, List.foldl_cons]
        apply ih
        · intro g' hg'; exact hgs g' (List.mem_cons_of_mem g hg')
        · simp [hlen]
        · intro k hk
          have hg := hgs g List.mem_cons_self
          by_cases hlt : k < w1.length
          · have hlt2 : k < w2.length := hlen ▸ hlt
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt, ← List.getD_eq_getElem _ _ hlt] at hk
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt2, ← List.getD_eq_getElem _ _ hlt2]
            exact hw k hk
          · by_cases heq : k = w1.length
            · subst heq
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)] at hk
              simp only [Nat.sub_self, List.getElem_cons_zero] at hk
              rw [hlen, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rcases hg with hand | hor
              · rw [hand] at hk ⊢
                change (g.inputs.map fun i => w1.getD i false).all id = true at hk
                change (g.inputs.map fun i => w2.getD i false).all id = true
                simp only [List.all_eq_true, List.mem_map, id_eq] at hk ⊢
                rintro _ ⟨i, hi, rfl⟩
                exact hw i (hk _ ⟨i, hi, rfl⟩)
              · rw [hor] at hk ⊢
                change (g.inputs.map fun i => w1.getD i false).any id = true at hk
                change (g.inputs.map fun i => w2.getD i false).any id = true
                simp only [List.any_eq_true, List.mem_map, id_eq] at hk ⊢
                obtain ⟨_, ⟨i, hi, rfl⟩, h1⟩ := hk
                exact ⟨_, ⟨i, hi, rfl⟩, hw i h1⟩
            · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
              cases hk
    have hinit : ∀ k, (List.ofFn x).getD k false = true → (List.ofFn y).getD k false = true := by
      intro k hk
      by_cases hlt : k < n
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn] at hk
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact hle ⟨k, hlt⟩ hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        cases hk
    exact hfold C.gates (List.ofFn x) (List.ofFn y) hAO.1 (by simp) hinit
  have fires_mono : ∀ {n : ℕ} {C : Circuit}, IsAO2 n C →
      ∀ (i : ℕ) (A B : Finset (Fin n)), A ⊆ B → fires C i A → fires C i B := by
    intro n C hAO i A B hAB hA
    apply wires_mono n C hAO (input A) (input B)
    · intro v hv
      simp only [input, decide_eq_true_eq] at hv ⊢
      exact hAB hv
    · exact hA
  -- Semantics 2: OrReaches implies gate index < C.gates.length and propagates true to wireVal
  have orReaches_props : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool),
      (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ w g, OrReaches n C w g →
        g < C.gates.length ∧ (gateVal n C g x = true → wireVal n C w x = true) := by
    intro n C x hAO
    have hinv : ∀ (gs : List Gate) (cs : List (List ℕ)) (ws : List Bool),
        (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ws.length = n + cs.length →
        (∀ j < cs.length, ∀ k ∈ cs.getD j [], k ≤ j) →
        (∀ j < cs.length, ∀ k ∈ cs.getD j [], ws.getD (n + k) false = true → ws.getD (n + j) false = true) →
        (gs.foldl (orStep n) cs).length = cs.length + gs.length ∧
        (∀ j < (gs.foldl (orStep n) cs).length, ∀ k ∈ (gs.foldl (orStep n) cs).getD j [], k ≤ j) ∧
        (∀ j < (gs.foldl (orStep n) cs).length, ∀ k ∈ (gs.foldl (orStep n) cs).getD j [],
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).getD (n + k) false = true →
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).getD (n + j) false = true) := by
      intro gs
      induction gs with
      | nil =>
        intro cs ws _ _ hb hs
        exact ⟨by simp, hb, hs⟩
      | cons g rest ih =>
        intro cs ws hgs hlen hb hs
        rw [List.foldl_cons, List.foldl_cons]
        let newC : List ℕ := cs.length :: (if g.op = GateOp.or then
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) [])
          else [])
        let cs' : List (List ℕ) := cs ++ [newC]
        let newB : Bool := g.op.eval (g.inputs.map fun i => ws.getD i false)
        let ws' : List Bool := ws ++ [newB]
        have hcs'_eq : orStep n cs g = cs' := rfl
        rw [hcs'_eq]
        have hlen' : ws'.length = n + cs'.length := by simp [ws', cs', hlen]; omega
        have hb' : ∀ j < cs'.length, ∀ k ∈ cs'.getD j [], k ≤ j := by
          intro j hj k hk
          by_cases hlt : j < cs.length
          · rw [List.getD_eq_getElem _ _ hj, List.getElem_append_left hlt, ← List.getD_eq_getElem _ _ hlt] at hk
            exact hb j hlt k hk
          · have hj_eq : j = cs.length := by simp [cs'] at hj; omega
            subst hj_eq
            rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right (Nat.le_refl _)] at hk
            simp only [Nat.sub_self, List.getElem_cons_zero, newC, List.mem_cons] at hk
            rcases hk with rfl | hk
            · exact Nat.le_refl _
            · by_cases hor : g.op = GateOp.or
              · simp only [hor, ite_true, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk
                obtain ⟨w, ⟨_, hnw, hwlt⟩, hkw⟩ := hk
                have := hb (w - n) (by omega) k hkw
                omega
              · simp [hor] at hk
        have hs' : ∀ j < cs'.length, ∀ k ∈ cs'.getD j [],
            ws'.getD (n + k) false = true → ws'.getD (n + j) false = true := by
          intro j hj k hk hwk
          have hkj : k ≤ j := hb' j hj k hk
          by_cases hlt : j < cs.length
          · rw [List.getD_eq_getElem _ _ hj, List.getElem_append_left hlt, ← List.getD_eq_getElem _ _ hlt] at hk
            have hklt : n + k < ws.length := by omega
            have hjlt : n + j < ws.length := by omega
            rw [List.getD_eq_getElem _ _ (by simp [ws']; omega), List.getElem_append_left hklt, ← List.getD_eq_getElem _ _ hklt] at hwk
            rw [List.getD_eq_getElem _ _ (by simp [ws']; omega), List.getElem_append_left hjlt, ← List.getD_eq_getElem _ _ hjlt]
            exact hs j hlt k hk hwk
          · have hj_eq : j = cs.length := by simp [cs'] at hj; omega
            subst hj_eq
            rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right (Nat.le_refl _)] at hk
            simp only [Nat.sub_self, List.getElem_cons_zero, newC, List.mem_cons] at hk
            rcases hk with rfl | hk
            · exact hwk
            · by_cases hor : g.op = GateOp.or
              · simp only [hor, ite_true, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk
                obtain ⟨w, ⟨hwg, hnw, hwlt⟩, hkw⟩ := hk
                have hkle : k ≤ w - n := hb (w - n) (by omega) k hkw
                have hklt : n + k < ws.length := by omega
                rw [List.getD_eq_getElem _ _ (by simp [ws']; omega), List.getElem_append_left hklt, ← List.getD_eq_getElem _ _ hklt] at hwk
                have hww : ws.getD w false = true := by
                  have h1 := hs (w - n) (by omega) k hkw hwk
                  have h2 : n + (w - n) = w := by omega
                  rwa [h2] at h1
                rw [← hlen, List.getD_eq_getElem _ _ (by simp [ws']), List.getElem_append_right (Nat.le_refl _)]
                simp only [Nat.sub_self, List.getElem_cons_zero, newB, hor]
                change (g.inputs.map fun i => ws.getD i false).any id = true
                simp only [List.any_eq_true, List.mem_map, id_eq]
                exact ⟨true, ⟨w, hwg, hww⟩, rfl⟩
              · simp [hor] at hk
        obtain ⟨hL, hB, hS⟩ := ih cs' ws' (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) hlen' hb' hs'
        refine ⟨?_, hB, hS⟩
        have hcs'_len : cs'.length = cs.length + 1 := by simp [cs']
        change (rest.foldl (orStep n) cs').length = cs.length + (rest.length + 1)
        omega
    obtain ⟨hL, hB, hS⟩ := hinv C.gates [] (List.ofFn x) hAO (by simp) (by intro j hj; simp at hj) (by intro j hj; simp at hj)
    have hlen : (orSets n C).length = C.gates.length := by
      change (C.gates.foldl (orStep n) []).length = C.gates.length
      simpa using hL
    intro w g hOR
    obtain ⟨hnw, hmem⟩ := hOR
    by_cases hlt : w - n < (orSets n C).length
    · have hgle : g ≤ w - n := hB (w - n) hlt g hmem
      refine ⟨by omega, ?_⟩
      intro hgv
      have hw : wireVal n C (n + (w - n)) x = true := hS (w - n) hlt g hmem hgv
      have heq : n + (w - n) = w := by omega
      rwa [heq] at hw
    · rw [List.getD_eq_default _ _ (by omega)] at hmem
      cases hmem
  -- Semantics 3: Prefix invariance of wires + AND gate firing at a top gate implies G has an edge in S
  have top_clean : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit},
      IsAO2 n C → ∀ {a g h : ℕ}, a ∈ tops G C →
      OrReaches n C (opnd C a 0) g → OrReaches n C (opnd C a 1) h →
      ∀ S : Finset (Fin n), fires C g S → fires C h S → hit G S := by
    intro n G _ C hAO a g h htop hlg hrh S hfg hfh
    have htop' : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
      have hm := Finset.mem_filter.mp htop
      exact ⟨Finset.mem_range.mp hm.1, hm.2.1, hm.2.2⟩
    obtain ⟨ha_lt, ha_and, ha_below⟩ := htop'
    have hwl : wireVal n C (opnd C a 0) (input S) = true :=
      (orReaches_props n C (input S) hAO.1 _ _ hlg).2 hfg
    have hwr : wireVal n C (opnd C a 1) (input S) = true :=
      (orReaches_props n C (input S) hAO.1 _ _ hrh).2 hfh
    have hfold_append : ∀ (gs : List Gate) (w0 : List Bool),
        w0.length ≤ (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length ∧
        ∀ k < w0.length,
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD k false = w0.getD k false := by
      intro gs
      induction gs with
      | nil => intro w0; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
      | cons g rest ih =>
        intro w0
        rw [List.foldl_cons]
        obtain ⟨hl, hk⟩ := ih (w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)])
        have hl' : w0.length ≤ (w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)]).length := by simp
        refine ⟨hl'.trans hl, ?_⟩
        intro k hlt
        rw [hk k (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt, ← List.getD_eq_getElem _ _ hlt]
    have hfold_len : ∀ (gs : List Gate) (w0 : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length = w0.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w0; simp
      | cons g rest ih => intro w0; rw [List.foldl_cons, ih]; simp; omega
    let ga : Gate := C.gates[a]
    have hga_eq : gateAt C a = ga := by
      change C.gates.getD a ⟨GateOp.or, []⟩ = C.gates[a]
      exact List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ ha_lt
    have hgates_split : C.gates = C.gates.take a ++ ga :: C.gates.drop (a + 1) := by
      conv_lhs => rw [← List.take_append_drop a C.gates]
      congr 1
      exact (List.getElem_cons_drop ha_lt).symm
    let wpre : List Bool := (C.gates.take a).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (input S))
    have hwpre_len : wpre.length = n + a := by
      rw [hfold_len]; simp [Nat.min_eq_left (Nat.le_of_lt ha_lt)]
    have hwires_eq : C.wires (List.ofFn (input S)) =
        (C.gates.drop (a + 1)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (wpre ++ [ga.op.eval (ga.inputs.map fun i => wpre.getD i false)]) := by
      change C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (input S)) = _
      conv_lhs => rw [hgates_split]
      rw [List.foldl_append, List.foldl_cons]
    have hread_pre : ∀ w < n + a, wpre.getD w false = wireVal n C w (input S) := by
      intro w hw
      have h1 : (C.wires (List.ofFn (input S))).getD w false =
          (wpre ++ [ga.op.eval (ga.inputs.map fun i => wpre.getD i false)]).getD w false := by
        rw [hwires_eq]
        exact (hfold_append _ _).2 w (by simp [hwpre_len]; omega)
      have h2 : (wpre ++ [ga.op.eval (ga.inputs.map fun i => wpre.getD i false)]).getD w false = wpre.getD w false := by
        rw [List.getD_eq_getElem _ _ (by simp [hwpre_len]; omega), List.getElem_append_left (by omega),
          ← List.getD_eq_getElem _ _ (by omega)]
      exact (h1.trans h2).symm
    have hga_len : ga.inputs.length = 2 := hAO.2.2 ga (List.getElem_mem ha_lt)
    have hga_op : ga.op = GateOp.and := hga_eq ▸ ha_and
    have hga_true : gateVal n C a (input S) = true := by
      change (C.wires (List.ofFn (input S))).getD (n + a) false = true
      rw [hwires_eq]
      rw [(hfold_append _ _).2 (n + a) (by simp [hwpre_len])]
      rw [← hwpre_len, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero, hga_op]
      change (ga.inputs.map fun i => wpre.getD i false).all id = true
      simp only [List.all_eq_true, List.mem_map, id_eq]
      rintro _ ⟨w, hw_mem, rfl⟩
      have hw_lt : w < n + a := hAO.2.1 a ha_lt w (hga_eq.symm ▸ hw_mem)
      rw [hread_pre w hw_lt]
      obtain ⟨k, hk, hwk⟩ := List.getElem_of_mem hw_mem
      have hlt2 : k < 2 := by omega
      have hcases : k = 0 ∨ k = 1 := by omega
      rcases hcases with rfl | rfl
      · have : w = opnd C a 0 := by
          change w = (gateAt C a).inputs.getD 0 0
          rw [hga_eq, List.getD_eq_getElem _ _ (by omega), hwk]
        rwa [this]
      · have : w = opnd C a 1 := by
          change w = (gateAt C a).inputs.getD 1 0
          rw [hga_eq, List.getD_eq_getElem _ _ (by omega), hwk]
        rwa [this]
    have hgf : graphFun G ∅ (input S) = true := ha_below (input S) hga_true
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), input S a = true) ||
      decide (∃ u v, G.Adj u v ∧ input S u = true ∧ input S v = true)) = true at hgf
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq, input] at hgf
    obtain ⟨u, v, huv, hu, hv⟩ := hgf
    exact ⟨u, hu, v, hv, huv⟩
  -- Combinatorial core: girth >= 5 implies C4-free, singleton star, shared leaves bound, certified edge bound <= 2 * C.size
  have girth_no_square : ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
      (∀ a (w : G.Walk a a), w.IsCycle → 5 ≤ w.length) →
      ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False := by
    intro n G girth a b c d hac hbd hab hbc hcd hda
    let W : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have cycle : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons]
      simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
    have h5 := girth a W cycle
    have len : W.length = 4 := rfl
    omega
  have singleton_cross : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (f h : Finset (Fin n) → Prop),
      (∀ A B, A ⊆ B → f A → f B) → (∀ A B, A ⊆ B → h A → h B) →
      (∀ S, f S → h S → hit G S) → ∀ x y : Fin n, f {x} → h {y} → G.Adj x y := by
    intro n G f h mf mh clean x y fx hy
    obtain ⟨i, hi, j, hj, e⟩ := clean {x, y} (mf {x} {x, y} (by simp) fx) (mh {y} {x, y} (by simp) hy)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact False.elim (e.ne rfl)
    · exact e
    · exact e.symm
    · exact False.elim (e.ne rfl)
  have singleton_star : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (f h : Finset (Fin n) → Prop),
      (∀ A B, A ⊆ B → f A → f B) → (∀ A B, A ⊆ B → h A → h B) →
      (∀ S, f S → h S → hit G S) →
      (∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False) →
      (∀ a c, f {a} → f {c} → a = c) ∨ (∀ b d, h {b} → h {d} → b = d) := by
    intro n G f h mf mh clean square
    by_cases hleft : ∀ a c, f {a} → f {c} → a = c
    · exact Or.inl hleft
    · right
      push Not at hleft
      obtain ⟨a, c, ha, hc, hac⟩ := hleft
      intro b d hb hd
      by_contra hbd
      have edge := singleton_cross G f h mf mh clean
      exact square a b c d hac hbd (edge a b ha hb) (edge c b hc hb).symm (edge c d hc hd) (edge a d ha hd).symm
  have witness_neighbor : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) {S : Finset (Fin n)} {t : Fin n},
      ¬ hit G S → hit G (insert t S) → ∃ v ∈ S, G.Adj v t := by
    intro n G S t indep h
    obtain ⟨a, ha, b, hb, e⟩ := h
    rcases Finset.mem_insert.mp ha with rfl | has
    · rcases Finset.mem_insert.mp hb with rfl | hbs
      · exact False.elim (e.ne rfl)
      · exact ⟨b, hbs, e.symm⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbs
      · exact ⟨a, has, e⟩
      · exact False.elim (indep ⟨a, has, b, hbs, e⟩)
  have shared_leaves_bound : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) (S T : Finset (Fin n))
      (f : Finset (Fin n) → Prop), (∀ A B, A ⊆ B → f A → f B) →
      f {c} → f S → ¬ hit G S → c ∉ S →
      (∀ t ∈ T, ∃ h : Finset (Fin n) → Prop,
        (∀ A B, A ⊆ B → h A → h B) ∧ (∀ X, f X → h X → hit G X) ∧ h {t}) →
      (∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False) →
      T.card ≤ S.card := by
    intro n G c S T f mf fc fs indep avoid partners square
    let L := fun v => T.filter fun t => G.Adj v t
    have center : ∀ t ∈ T, G.Adj c t := by
      intro t ht
      obtain ⟨h, mh, clean, ht'⟩ := partners t ht
      exact singleton_cross G f h mf mh clean c t fc ht'
    have cover : T ⊆ S.biUnion L := by
      intro t ht
      obtain ⟨h, mh, clean, ht'⟩ := partners t ht
      have joined := clean (insert t S) (mf _ _ (Finset.subset_insert _ _) fs) (mh {t} _ (by simp) ht')
      obtain ⟨v, hv, adj⟩ := witness_neighbor G indep joined
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨ht, adj⟩⟩
    have small : ∀ v ∈ S, (L v).card ≤ 1 := by
      intro v hv
      apply Finset.card_le_one.mpr
      intro p hp q hq
      obtain ⟨pt, ep⟩ := Finset.mem_filter.mp hp
      obtain ⟨qt, eq'⟩ := Finset.mem_filter.mp hq
      by_contra pq
      exact square c p v q (fun he => avoid (he ▸ hv)) pq
        (center p pt) ep.symm eq' (center q qt).symm
    calc T.card ≤ (S.biUnion L).card := Finset.card_le_card cover
      _ ≤ S.card * 1 := Finset.card_biUnion_le_card_mul S L 1 small
      _ = S.card := Nat.mul_one _
  let Partner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (t : Fin n) : Prop :=
    ∃ a ∈ tops G C, ∃ h, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧ OrReaches n C (opnd C a (1 - b)) h ∧ fires C h {t}
  let CenterCert {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) (c : Fin n) : Prop :=
    fires C g {c} ∧ (∀ d : Fin n, fires C g {d} → d = c) ∧
      ∃ S : Finset (Fin n), fires C g S ∧ ¬ hit G S ∧ c ∉ S ∧ S.card ≤ 2
  let CertifiedEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
    ∃ g < C.gates.length, ∃ c t, e = s(c, t) ∧ CenterCert G C g c ∧ Partner G C g t
  have short_bound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a (w : G.Walk a a), w.IsCycle → 5 ≤ w.length) → IsAO2 n C →
      ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, CertifiedEdge G C e) → E.card ≤ 2 * C.size := by
    intro n G _ C girth ao E eligible
    let cells := fun g => E.filter fun e => ∃ c t, e = s(c, t) ∧ CenterCert G C g c ∧ Partner G C g t
    have cover : E ⊆ (Finset.range C.gates.length).biUnion cells := by
      intro e he
      obtain ⟨g, hg, hcert⟩ := eligible e he
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_range.mpr hg, Finset.mem_filter.mpr ⟨he, hcert⟩⟩
    apply (Finset.card_le_card cover).trans
    rw [Nat.mul_comm]
    change _ ≤ C.gates.length * 2
    conv_rhs => rw [← Finset.card_range C.gates.length]
    apply Finset.card_biUnion_le_card_mul
    intro g hg
    by_cases hne : (cells g).Nonempty
    · obtain ⟨e, he⟩ := hne
      obtain ⟨_, c, t, _, ⟨fc, unique, S, fs, ind, away, sz⟩, _⟩ := Finset.mem_filter.mp he
      let leaves := Finset.univ.filter (Partner G C g)
      have bound : leaves.card ≤ S.card := by
        apply shared_leaves_bound G c S leaves (fires C g) (fires_mono ao g) fc fs ind away _ (girth_no_square G girth)
        intro t' ht'
        obtain ⟨a, ha, h, b, l, r, fh⟩ := (Finset.mem_filter.mp ht').2
        refine ⟨fires C h, fires_mono ao h, ?_, fh⟩
        fin_cases b
        · simp only [Fin.zero_eta, sub_zero] at l r
          exact top_clean ao ha l r
        · simp only [Fin.mk_one, sub_self] at l r
          intro X fg fh'
          exact top_clean ao ha r l X fh' fg
      have inc : cells g ⊆ leaves.image (fun v => s(c, v)) := by
        intro e' he'
        obtain ⟨_, d, v, eqn, cc, hv⟩ := Finset.mem_filter.mp he'
        obtain rfl := unique d cc.1
        exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, eqn.symm⟩
      exact (Finset.card_le_card inc).trans (Finset.card_image_le.trans (bound.trans sz))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  -- Combine the proved short bound (<= 2 * C.size) with the 3 residual hypotheses
  obtain ⟨k1, hk1⟩ := deepDeepCleanCenters
  obtain ⟨k2, hk2⟩ := deepDeepBothPairOnly
  obtain ⟨k3, hk3⟩ := deepDeepOneSidedSing
  refine ⟨2 + k1 + k2 + k3, ?_⟩
  intro n G _ C hGirth hLeast hTop
  obtain ⟨E1, hE1card, hE1mem⟩ := hk1 n G C hGirth hLeast hTop
  obtain ⟨E2, hE2card, hE2mem⟩ := hk2 n G C hGirth hLeast hTop
  obtain ⟨E3, hE3card, hE3mem⟩ := hk3 n G C hGirth hLeast hTop
  let E0 : Finset (Sym2 (Fin n)) := (Ustar G C).filter (CertifiedEdge G C)
  have hE0card : E0.card ≤ 2 * C.size :=
    short_bound n G C hGirth hLeast.1 E0 (fun _ he => (Finset.mem_filter.mp he).2)
  refine ⟨E0 ∪ E1 ∪ E2 ∪ E3, ?_, ?_⟩
  · have h1 := Finset.card_union_le (E0 ∪ E1 ∪ E2) E3
    have h2 := Finset.card_union_le (E0 ∪ E1) E2
    have h3 := Finset.card_union_le E0 E1
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    omega
  · intro e heU hNoSide hDD
    obtain ⟨u, v, heuv, a, ha, g, hg, h, hh, hne, hlg, hrh, hguv, hhuv, hdeepg, hdeeph⟩ := hDD
    have hpair_symm : pairInput u v = pairInput v u := by
      funext w
      change decide (w = u ∨ w = v) = decide (w = v ∨ w = u)
      simp only [or_comm]
    have hconv : ∀ (k : ℕ) (c : Fin n), gateVal n C k (pairInput c c) = true → fires C k {c} := by
      intro k c hkc
      have heq : input {c} = pairInput c c := by
        funext w
        change decide (w ∈ ({c} : Finset (Fin n))) = decide (w = c ∨ w = c)
        simp
      simpa only [fires, heq] using hkc
    have hmatch : ∀ (p q : Fin n), e = s(p, q) →
        gateVal n C g (pairInput p p) = true → gateVal n C h (pairInput q q) = true →
        e ∈ E0 ∪ E1 ∪ E2 ∪ E3 := by
      intro p q hepq hgp hhq
      by_cases hBg : ∃ S : Finset (Fin n), S.card ≤ 2 ∧ p ∉ S ∧
          (∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) ∧ gateVal n C g (fun i => decide (i ∈ S)) = true
      · by_cases hBh : ∃ S : Finset (Fin n), S.card ≤ 2 ∧ q ∉ S ∧
            (∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) ∧ gateVal n C h (fun i => decide (i ∈ S)) = true
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨heU, ?_⟩
          have hg_lt : g < C.gates.length := (orReaches_props n C (input {p}) hLeast.1.1 _ _ hlg).1
          have hh_lt : h < C.gates.length := (orReaches_props n C (input {q}) hLeast.1.1 _ _ hrh).1
          have hstar := singleton_star G (fires C g) (fires C h) (fires_mono hLeast.1 g) (fires_mono hLeast.1 h)
            (top_clean hLeast.1 ha hlg hrh) (girth_no_square G hGirth)
          rcases hstar with hug | huh
          · obtain ⟨Sg, hSgsz, hSgp, hSgind, hSgf⟩ := hBg
            refine ⟨g, hg_lt, p, q, hepq, ⟨hconv g p hgp, fun d fd => hug d p fd (hconv g p hgp),
              Sg, hSgf, ?_, hSgp, hSgsz⟩, a, ha, h, 0, hlg, by simpa only [sub_zero] using hrh, hconv h q hhq⟩
            rintro ⟨x, hx, y, hy, hxy⟩
            exact hSgind x hx y hy hxy
          · obtain ⟨Sh, hShsz, hShq, hShind, hShf⟩ := hBh
            refine ⟨h, hh_lt, q, p, hepq.trans Sym2.eq_swap, ⟨hconv h q hhq, fun d fd => huh d q fd (hconv h q hhq),
              Sh, hShf, ?_, hShq, hShsz⟩, a, ha, g, 1, hrh, by simpa only [sub_self] using hlg, hconv g p hgp⟩
            rintro ⟨x, hx, y, hy, hxy⟩
            exact hShind x hx y hy hxy
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          apply Finset.mem_union_right
          apply hE1mem e heU hNoSide
          refine ⟨p, q, hepq, a, ha, g, hg, h, hh, hne, hlg, hrh, hdeepg, hdeeph, hgp, hhq, Or.inr ?_⟩
          intro S hSsz hSq hSf
          by_contra hNoEdge
          exact hBh ⟨S, hSsz, hSq, fun x hx y hy hxy => hNoEdge ⟨x, hx, y, hy, hxy⟩, hSf⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply hE1mem e heU hNoSide
        refine ⟨p, q, hepq, a, ha, g, hg, h, hh, hne, hlg, hrh, hdeepg, hdeeph, hgp, hhq, Or.inl ?_⟩
        intro S hSsz hSp hSf
        by_contra hNoEdge
        exact hBg ⟨S, hSsz, hSp, fun x hx y hy hxy => hNoEdge ⟨x, hx, y, hy, hxy⟩, hSf⟩
    cases hgu : gateVal n C g (pairInput u u)
    · cases hgv : gateVal n C g (pairInput v v)
      · cases hhu : gateVal n C h (pairInput u u)
        · cases hhv : gateVal n C h (pairInput v v)
          · -- All four singletons false -> deepDeepBothPairOnly (E2)
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            exact hE2mem e heU hNoSide ⟨u, v, heuv, a, ha, g, hg, h, hh, hne, hlg, hrh, hdeepg, hdeeph, hguv, hhuv, hgu, hgv, hhu, hhv⟩
          · -- h fires {v}, g does not fire {u} -> deepDeepOneSidedSing (E3) with b = 1, (v, u), (h, g)
            apply Finset.mem_union_right
            exact hE3mem e heU hNoSide ⟨v, u, heuv.trans Sym2.eq_swap, a, ha, 1, h, hh, g, hg, hne.symm, hrh, by simpa only [sub_self] using hlg, hdeeph, hdeepg, hhv, hpair_symm ▸ hguv, hgu⟩
        · -- h fires {u}, g does not fire {v} -> deepDeepOneSidedSing (E3) with b = 1, (u, v), (h, g)
          apply Finset.mem_union_right
          exact hE3mem e heU hNoSide ⟨u, v, heuv, a, ha, 1, h, hh, g, hg, hne.symm, hrh, by simpa only [sub_self] using hlg, hdeeph, hdeepg, hhu, hguv, hgv⟩
      · cases hhu : gateVal n C h (pairInput u u)
        · -- g fires {v}, h does not fire {u} -> deepDeepOneSidedSing (E3) with b = 0, (v, u), (g, h)
          apply Finset.mem_union_right
          exact hE3mem e heU hNoSide ⟨v, u, heuv.trans Sym2.eq_swap, a, ha, 0, g, hg, h, hh, hne, hlg, by simpa only [sub_zero] using hrh, hdeepg, hdeeph, hgv, hpair_symm ▸ hhuv, hhu⟩
        · -- g fires {v}, h fires {u}
          exact hmatch v u (heuv.trans Sym2.eq_swap) hgv hhu
    · cases hhv : gateVal n C h (pairInput v v)
      · -- g fires {u}, h does not fire {v} -> deepDeepOneSidedSing (E3) with b = 0, (u, v), (g, h)
        apply Finset.mem_union_right
        exact hE3mem e heU hNoSide ⟨u, v, heuv, a, ha, 0, g, hg, h, hh, hne, hlg, by simpa only [sub_zero] using hrh, hdeepg, hdeeph, hgu, hhuv, hhv⟩
      · -- g fires {u}, h fires {v}
        exact hmatch u v heuv hgu hhv
