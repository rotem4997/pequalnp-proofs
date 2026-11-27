import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count gates that own two vertex-disjoint edges. Either repair keeps the circuit least.
-- The two repairs only inspect false positives on the four endpoints of those edges.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2448_263
    (hBase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅)
    (hSingle : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      let conflict (C : Circuit) (j : ℕ) (a b c d : Fin n) :=
        G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
          a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
      let cost (C : Circuit) := Set.ncard {j : ℕ | ∃ a b c d, conflict C j a b c d}
      ∀ (C : Circuit) (j : ℕ) (a b c d : Fin n),
        IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → conflict C j a b c d →
        (∃ u, (u = a ∨ u = b ∨ u = c ∨ u = d) ∧ gateVal n C j (pairInput u u) = true) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ cost D < cost C)
    (hPair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      let conflict (C : Circuit) (j : ℕ) (a b c d : Fin n) :=
        G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
          a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
      let cost (C : Circuit) := Set.ncard {j : ℕ | ∃ a b c d, conflict C j a b c d}
      ∀ (C : Circuit) (j : ℕ) (a b c d : Fin n),
        IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → conflict C j a b c d →
        let endpoint (w : Fin n) := w = a ∨ w = b ∨ w = c ∨ w = d
        (∀ w, endpoint w → gateVal n C j (pairInput w w) = false) →
        (∃ u, endpoint u ∧ ∃ v, endpoint v ∧
          u ≠ v ∧ ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ cost D < cost C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  classical
  intro n G _ htri hsquare
  have hfour : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hap, hbp⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨haq, hbq⟩ := (Finset.mem_filter.mp hq).2
    exact (hsquare a p b q hap hbp.symm hbq haq.symm).resolve_left hab
  -- Wire evaluation and cone descent are adapted from R_meta_2448_17.
  have pairDirt (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (hm : Monotone2 C)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (a b c d : Fin n)
    (ab : Owns n C j a b) (cd : Owns n C j c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ u ∈ ({a,b,c,d} : Finset (Fin n)), ∃ v ∈ ({a,b,c,d} : Finset (Fin n)), ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
    classical
    let stepWire (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have wires_eq_foldl (C : Circuit) (x : List Bool) :
        C.wires x = C.gates.foldl stepWire x := rfl

    have foldl_stepWire_length (gs : List Gate) (w : List Bool) :
        (gs.foldl stepWire w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [stepWire]
        omega

    have foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl stepWire w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
        rw [ih (stepWire w g) hlt]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

    have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
        w.getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

    have split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
        ∃ (pre post : List Gate) (gj : Gate),
          gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
      refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
      rw [List.cons_getElem_drop_succ, List.take_append_drop]

    let W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
      (C.wires (List.ofFn x)).getD u false

    have gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
      change C.gates.getD k _ = _
      simp [List.getD_eq_getElem?_getD, hk]

    have W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
        W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
          if i < n + k then W n C x i else false) := by
      obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
      have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
      rw [hga]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + k := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
        simp only [W]
        rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
        rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
      rw [hCj]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      by_cases hi : i < n + k
      · simp only [hi, ↓reduceIte]
        simp only [W]
        rw [wires_eq_foldl, hgs, List.foldl_append]
        exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_length w0 i (by omega)

    have W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
        W n C x u = x ⟨u, hu⟩ := by
      simp only [W]
      rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
      simp [List.getD_eq_getElem?_getD, hu]

    have coneEq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
        coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
    have coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [coneEq]
        omega

    have coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
        (coneStep n cs g).getD cs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
      simp [coneEq, List.getD_eq_getElem?_getD]

    have coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
        (coneStep n cs g).getD m [] = cs.getD m [] := by
      simp [coneEq, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

    have coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
        (hk : k < cs.length) :
        (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
      induction gs generalizing cs with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        rw [ih (coneStep n cs g) (by simp [coneEq]; omega)]
        exact coneStep_getD_lt n cs g k hk

    have inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
        InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
          (i = w - n ∨ InCone n C i (w - n)) := by
      obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
      have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
      rw [hga]
      have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
        delta cones
        rw [hgs, List.foldl_append, List.foldl_cons]
      have hl0 : (pre.foldl (coneStep n) []).length = k := by
        rw [coneFold_length]; simp [hpre_len]
      have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
        simp [coneEq, hl0]
      have h1 : (cones n C).getD k [] =
          (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
        rw [hc, coneFold_getD_lt n post _ k (by omega)]
        have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
        rw [hl0] at h
        exact h
      have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
        intro m hm
        rw [hc, coneFold_getD_lt n post _ m (by omega)]
        exact coneStep_getD_lt n _ gk m (by omega)
      unfold InCone
      rw [h1]
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
        refine ⟨w, hw, hn, hlt, ?_⟩
        rcases h with h | h
        · exact Or.inl h
        · right
          rw [h2 (w - n) (by omega)]
          exact h
      · rintro ⟨w, hw, hn, hlt, h⟩
        refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
        rcases h with h | h
        · exact Or.inl h
        · right
          rw [← h2 (w - n) (by omega)]
          exact h


    have ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
        (if c then b else false) = true ↔ c ∧ b = true := by
      by_cases h : c <;> simp [h]

    have W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
        (hop : (gateAt C k).op = GateOp.and) :
        W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
      rw [W_gate n C x k hk, hop]
      have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
      simp only [andEval, List.all_eq_true, List.mem_map, id_eq]
      constructor
      · intro h w hw
        exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
      · rintro h b ⟨w, hw, rfl⟩
        exact (ite_true_iff _ _).mpr (h w hw)

    have W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
        (hop : (gateAt C k).op = GateOp.or) :
        W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
      rw [W_gate n C x k hk, hop]
      have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
      simp only [orEval, List.any_eq_true, List.mem_map, id_eq]
      constructor
      · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
        exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
      · rintro ⟨w, hw, h⟩
        exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

    have inCone_lt (n : ℕ) (C : Circuit) :
        ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk i hi
        obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
        rcases h with h | h
        · omega
        · have := ih (w - n) (by omega) (by omega) i h
          omega

    have gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
        ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
          (gateAt C k).inputs.length ≤ 2 := by
      have hg := hM (C.gates[k]) (List.getElem_mem hk)
      rw [← gateAt_eq C k hk] at hg
      have h1 := hg.1
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      exact ⟨h1, hg.2⟩

    let Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
      ∀ P : ℕ → Prop, P t.val →
        (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
          ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

    have reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

    have reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
        (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
        (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
      fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

    have reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
        (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
      h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
        (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

    have descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
        ∀ k, k < C.gates.length → W n C x (n + k) = true →
          (gateAt C k).op = GateOp.and ∨
          (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
          (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk hx
        rcases (gate_mono2 C hM k hk).1 with hop | hop
        · exact Or.inl hop
        · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
          by_cases hwn : w < n
          · right; right
            refine ⟨⟨w, hwn⟩, ?_, ?_⟩
            · rw [← W_input n C x w hwn]; exact hwx
            · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
          · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
            have he : n + k' - n = k' := by omega
            rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
            · right; left
              exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
                h, hwx⟩
            · right; left
              exact ⟨i, (inCone_iff n C i k hk).mpr
                ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
            · right; right
              exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

    have owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
        (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
        ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
      obtain ⟨_, _, hval, hno⟩ := ho
      intro w hw
      have hval' : W n C (pairInput p q) (n + j) = true := hval
      obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
      refine ⟨hlt, ?_⟩
      by_cases hwn : w < n
      · rw [W_input n C _ w hwn] at hwx
        have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
        rcases h' with h | h
        · left
          rw [← h]; exact reach_refl n C ⟨w, hwn⟩
        · right
          rw [← h]; exact reach_refl n C ⟨w, hwn⟩
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have he : n + k' - n = k' := by omega
        have hk'j : k' < j := by omega
        have hc : InCone n C k' j :=
          (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
        rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
        · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
          rw [hwx] at hf
          exact absurd hf (by simp)
        · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
            ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
          have hij := inCone_lt n C j hj i hc2
          have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
          rw [hix] at hf
          exact absurd hf (by simp)
        · have h' : t = p ∨ t = q := of_decide_eq_true ht
          rcases h' with h | h
          · left; rw [← h]; exact hdom
          · right; rw [← h]; exact hdom
    let S : Finset (Fin n) := {a,b,c,d}
    change ∃ u ∈ S, ∃ v ∈ S, ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true
    have haS : a ∈ S := by simp [S]
    have hbS : b ∈ S := by simp [S]
    have hcS : c ∈ S := by simp [S]
    have hdS : d ∈ S := by simp [S]
    by_contra! clean
    have F3 (s t : Fin n) (hsS : s ∈ S) (htS : t ∈ S)
        (hr : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C s w ∨ Reach n C t w)) :
        G.Adj s t := by
      by_contra hst
      have hs : pairInput s t s = true := decide_eq_true (Or.inl rfl : s = s ∨ s = t)
      have ht : pairInput s t t = true := decide_eq_true (Or.inr rfl : t = s ∨ t = t)
      have hval : W n C (pairInput s t) (n + j) = true :=
        (W_and_iff n C _ j ab.1 ab.2.1).mpr (fun w hw => ⟨(hr w hw).1,
          (hr w hw).2.elim (fun h => reach_val n C s w _ hs h) (fun h => reach_val n C t w _ ht h)⟩)
      have hval' : gateVal n C j (pairInput s t) = true := hval
      have hfalse := clean s hsS t htS hst
      simp [hval'] at hfalse
    have reach {s t : Fin n} (h : Owns n C j s t) := owns_reach n C hm j ab.1 ab.2.1 s t h
    have hlen := (gate_mono2 C hm j ab.1).2
    rcases hin : (gateAt C j).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨t, ts⟩⟩⟩
    · exact (F3 a a haS haS (by simp [hin])).ne rfl
    · have h := reach ab p (by simp [hin])
      rcases h.2 with ha | hb
      · exact (F3 a a haS haS (by simpa [hin] using And.intro h.1 ha)).ne rfl
      · exact (F3 b b hbS hbS (by simpa [hin] using And.intro h.1 hb)).ne rfl
    · have hp := (reach ab p (by simp [hin])).1
      have hq := (reach ab q (by simp [hin])).1
      have cross (s t : Fin n) (hsS : s ∈ S) (htS : t ∈ S) (hs : Reach n C s p) (ht : Reach n C t q) : G.Adj s t := by
        apply F3 s t hsS htS
        intro w hw
        simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hp, Or.inl hs⟩
        · exact ⟨hq, Or.inr ht⟩
      have sides {s t : Fin n} (hsS : s ∈ S) (htS : t ∈ S) (h : Owns n C j s t) :
          (Reach n C s p ∧ Reach n C t q) ∨ (Reach n C t p ∧ Reach n C s q) := by
        rcases (reach h p (by simp [hin])).2 with hs | ht <;>
          rcases (reach h q (by simp [hin])).2 with hu | hv
        · exact ((cross s s hsS hsS hs hu).ne rfl).elim
        · exact Or.inl ⟨hs, hv⟩
        · exact Or.inr ⟨ht, hu⟩
        · exact ((cross t t htS htS ht hv).ne rfl).elim
      have rectangle (s t u v : Fin n) (hsS : s ∈ S) (htS : t ∈ S) (huS : u ∈ S) (hvS : v ∈ S)
          (hs : Reach n C s p) (ht : Reach n C t q)
          (hu : Reach n C u p) (hv : Reach n C v q) : s = u ∨ t = v :=
        hfour s t u v (cross s t hsS htS hs ht) (cross u t huS htS hu ht).symm (cross u v huS hvS hu hv) (cross s v hsS hvS hs hv).symm
      rcases sides haS hbS ab with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rcases sides hcS hdS cd with ⟨hc, hd⟩ | ⟨hd, hc⟩
      · exact (rectangle a b c d haS hbS hcS hdS ha hb hc hd).elim hac hbd
      · exact (rectangle a b d c haS hbS hdS hcS ha hb hd hc).elim had hbc
      · exact (rectangle b a c d hbS haS hcS hdS hb ha hc hd).elim hbc had
      · exact (rectangle b a d c hbS haS hdS hcS hb ha hd hc).elim hbd hac
    · simp [hin] at hlen
  let conflict (C : Circuit) (j : ℕ) (a b c d : Fin n) :=
    G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
  let bad (C : Circuit) : Set ℕ := {j | ∃ a b c d, conflict C j a b c d}
  let admissible (k : ℕ) := ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
    circuitFun n C = graphFun G ∅ ∧ (bad C).ncard = k
  obtain ⟨B, hBmin, hBfun⟩ := hBase n G
  have hex : ∃ k, admissible k := ⟨_, B, hBmin, hBfun, rfl⟩
  obtain ⟨C, hmin, hfun, hcost⟩ := Nat.find_spec hex
  have hgood (j : ℕ) : j ∉ bad C := by
    rintro ⟨a, b, c, d, hconf⟩
    have h := hconf
    obtain ⟨_, _, hab, hcd, hac, had, hbc, hbd⟩ := h
    let V : Finset (Fin n) := {a,b,c,d}
    have improves : ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ (bad D).ncard < (bad C).ncard := by
      by_cases hs : ∃ u ∈ V, gateVal n C j (pairInput u u) = true
      · apply hSingle n G htri hfour C j a b c d hmin hfun hconf
        simpa only [V, Finset.mem_insert, Finset.mem_singleton] using hs
      · have hsilent (u : Fin n) (hu : u ∈ V) : gateVal n C j (pairInput u u) = false := by
          cases h : gateVal n C j (pairInput u u) with
          | false => rfl
          | true => exact (hs ⟨u, hu, h⟩).elim
        obtain ⟨u, hu, v, hv, hnon, hfire⟩ :=
          pairDirt n G C j hmin.1 hsquare a b c d hab hcd hac had hbc hbd
        have hne : u ≠ v := by
          rintro rfl
          rw [hsilent u hu] at hfire
          contradiction
        apply hPair n G htri hfour C j a b c d hmin hfun hconf
        · simpa only [V, Finset.mem_insert, Finset.mem_singleton] using hsilent
        · simp only [V, Finset.mem_insert, Finset.mem_singleton] at hu hv
          exact ⟨u, hu, v, hv, hne, hnon, hfire⟩
    obtain ⟨D, hDm, hDf, hsize, hdrop⟩ := improves
    have hDmin : IsMinimalMonoCircuit n D := ⟨hDm, fun E hEm hEf =>
      hsize.trans (hmin.2 E hEm (hEf.trans (hDf.trans hfun.symm)))⟩
    have hleast := Nat.find_min' hex
      (show admissible (bad D).ncard from ⟨D, hDmin, hDf, rfl⟩)
    omega
  refine ⟨C, hmin.1, hfun, fun D hD hDf => hmin.2 D hD (hDf.trans hfun.symm), ?_⟩
  intro j _ _
  by_cases used : ∃ a b, G.Adj a b ∧ Owns n C j a b
  · right
    -- The pairwise intersection argument follows the reduction R_meta_1031_1.
    have hmeet (u v p q : Fin n) (huv : G.Adj u v) (hpq : G.Adj p q)
        (h1 : Owns n C j u v) (h2 : Owns n C j p q) : u = p ∨ u = q ∨ v = p ∨ v = q := by
      by_contra hn
      push Not at hn
      exact hgood j ⟨u, v, p, q, huv, hpq, h1, h2, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩
    obtain ⟨a, b, hab, hoab⟩ := used
    by_cases ha : ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · push Not at ha
      obtain ⟨p, q, hpq, hopq, hpa, hqa⟩ := ha
      have hbpq : p = b ∨ q = b := by
        have h := hmeet p q a b hpq hab hopq hoab
        tauto
      have hext : ∃ w : Fin n, w ≠ a ∧ G.Adj b w ∧
          ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hpq, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
        · refine ⟨p, hpa, hpq.symm, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv hov
      by_contra hn
      push Not at hn
      have huva : u = a ∨ v = a := by
        have h := hmeet u v a b huv hab hov hoab
        tauto
      have huvw : u = w ∨ v = w := by
        have h := hmeetw u v huv hov
        tauto
      have hwaAdj : G.Adj w a := by
        rcases huva with h | h
        · subst u
          have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
          simpa [hvw] using huv.symm
        · subst v
          have huw : u = w := huvw.resolve_right (Ne.symm hwa)
          simpa [huw] using huv
      exact htri a b w hab hbw hwaAdj
  · left
    exact fun u v huv ho => used ⟨u, v, huv, ho⟩
