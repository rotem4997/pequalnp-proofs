import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- First exclude two disjoint owned edges with no connecting owned edge.
-- Every remaining nonempty gate graph is a double star or a five-cycle, up to isolates.
-- A five-cycle gate fires on a singleton. Its two inputs would otherwise color the cycle.
-- The second step extends the star condition to one more gate in such a circuit.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2448_17
    (hCross : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      let r (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j a b c d, r C j a b → r C j c d →
          r C j a c ∨ r C j a d ∨ r C j b c ∨ r C j b d)
    (hExtend : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      let r (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
      let eligible (C : Circuit) := IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j, (∀ a b, ¬r C j a b) ∨
          (∃ b c, r C j b c ∧ ∀ u v, r C j u v → u = b ∨ v = b ∨ u = c ∨ v = c) ∨
          ∃ a b c d e, r C j a b ∧ r C j b c ∧ r C j c d ∧ r C j d e ∧ r C j e a ∧
            (∀ u v, r C j u v → u = a ∨ u = b ∨ u = c ∨ u = d ∨ u = e) ∧
              gateVal n C j (pairInput a a) = true
      let stars (C : Circuit) (k : ℕ) := ∀ j < k,
        (∀ u v, ¬r C j u v) ∨ ∃ w, ∀ u v, r C j u v → u = w ∨ v = w
      ∀ (C : Circuit) (k : ℕ), eligible C → k < C.size → stars C k →
        ∃ D : Circuit, eligible D ∧ stars D (k + 1)) :
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
  have oddGate (n : ℕ) (C : Circuit) (hm : Monotone2 C) (j : ℕ)
    (a b c d e : Fin n) (ab : Owns n C j a b) (bc : Owns n C j b c)
    (cd : Owns n C j c d) (de : Owns n C j d e) (ea : Owns n C j e a) :
    ∃ z ∈ ({a,b,c,d,e} : Finset (Fin n)), gateVal n C j (pairInput z z) = true := by
    -- The wire and cone lemmas here are adapted from the fleet proof L_meta_1762.
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
    classical
    let S : Finset (Fin n) := {a,b,c,d,e}
    have ha : a ∈ S := by simp [S]
    have hb : b ∈ S := by simp [S]
    have hc : c ∈ S := by simp [S]
    have hd : d ∈ S := by simp [S]
    have he : e ∈ S := by simp [S]
    have reach {u v : Fin n} (h : Owns n C j u v) :=
      owns_reach n C hm j ab.1 ab.2.1 u v h
    have fires (z : Fin n) (hz : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ Reach n C z w) :
        gateVal n C j (pairInput z z) = true := by
      apply (W_and_iff n C _ j ab.1 ab.2.1).2
      intro w hw
      exact ⟨(hz w hw).1, reach_val n C z w _ (by change decide (z = z ∨ z = z) = true; simp) (hz w hw).2⟩
    have hlen := (gate_mono2 C hm j ab.1).2
    rcases hin : (gateAt C j).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨t, ts⟩⟩⟩
    · exact ⟨a, ha, fires a (by simp [hin])⟩
    · obtain ⟨hp, hpa | hpb⟩ := reach ab p (by simp [hin])
      · exact ⟨a, ha, fires a (by simpa [hin] using And.intro hp hpa)⟩
      · exact ⟨b, hb, fires b (by simpa [hin] using And.intro hp hpb)⟩
    · by_contra! hno
      have disj (z : Fin n) (hz : z ∈ S) : ¬(Reach n C z p ∧ Reach n C z q) := by
        intro h
        have hp := (reach ab p (by simp [hin])).1
        have hq := (reach ab q (by simp [hin])).1
        have hf := fires z (by
          intro w hw
          simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hp, h.1⟩
          · exact ⟨hq, h.2⟩)
        exact hno z hz hf
      have flip {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (huv : Owns n C j u v) :
          Reach n C u p ↔ ¬ Reach n C v p := by
        have h1 := (reach huv p (by simp [hin])).2
        have h2 := (reach huv q (by simp [hin])).2
        have h3 := disj u hu
        have h4 := disj v hv
        tauto
      have h1 := flip ha hb ab
      have h2 := flip hb hc bc
      have h3 := flip hc hd cd
      have h4 := flip hd he de
      have h5 := flip he ha ea
      tauto
    · simp [hin] at hlen
  let V := Fin n
  have classify (r : V → V → Prop)
      (sym : ∀ {u v}, r u v → r v u)
      (tri : ∀ {a b c}, r a b → r b c → ¬r c a)
      (sq : ∀ {a b c d}, r a b → r b c → r c d → r d a → a = c ∨ b = d)
      (cross : ∀ {a b c d}, r a b → r c d → r a c ∨ r a d ∨ r b c ∨ r b d) :
      (∀ a b, ¬r a b) ∨
        (∃ b c, r b c ∧ ∀ u v, r u v → u = b ∨ v = b ∨ u = c ∨ v = c) ∨
        ∃ a b c d e, r a b ∧ r b c ∧ r c d ∧ r d e ∧ r e a ∧
          ∀ u v, r u v → u = a ∨ u = b ∨ u = c ∨ u = d ∨ u = e := by
    classical
    by_cases empty : ∀ a b, ¬r a b
    · exact Or.inl empty
    right
    by_cases cover : ∃ b c, r b c ∧ ∀ u v, r u v → u = b ∨ v = b ∨ u = c ∨ v = c
    · exact Or.inl cover
    right
    have outside (b c : V) (bc : r b c) : ∃ x y, r x y ∧ x ≠ b ∧ x ≠ c ∧ y ≠ b ∧ y ≠ c := by
      by_contra! h
      apply cover
      refine ⟨b, c, bc, ?_⟩
      intro u v huv
      by_contra! hn
      exact hn.2.2.2 (h u v huv hn.1 hn.2.2.1 hn.2.1)
    push Not at empty
    obtain ⟨a, b, hab⟩ := empty
    obtain ⟨c, d, hcd, hca, hcb, hda, hdb⟩ := outside a b hab
    have path : ∃ a b c d, r a b ∧ r b c ∧ r c d ∧ a ≠ c ∧ b ≠ d := by
      rcases cross hab hcd with h | h | h | h
      · exact ⟨b, a, c, d, sym hab, h, hcd, Ne.symm hcb, Ne.symm hda⟩
      · exact ⟨b, a, d, c, sym hab, h, sym hcd, Ne.symm hdb, Ne.symm hca⟩
      · exact ⟨a, b, c, d, hab, h, hcd, Ne.symm hca, Ne.symm hdb⟩
      · exact ⟨a, b, d, c, hab, h, sym hcd, Ne.symm hda, Ne.symm hcb⟩
    obtain ⟨a, b, c, d, hab, hbc, hcd, hac, hbd⟩ := path
    obtain ⟨x, y, hxy, hxb, hxc, hyb, hyc⟩ := outside b c hbc
    have side {p q s t u : V} (hpq : r p q) (hqs : r q s) (htu : r t u) (hpt : r p t)
        (hps : p ≠ s) (htq : t ≠ q) (huq : u ≠ q) (hup : u ≠ p) :
        r u s ∧ t ≠ s := by
      have hstop : ¬r t s := fun h => htq ((sq hpt h (sym hqs) (sym hpq)).resolve_left hps)
      have hts : t ≠ s := by
        rintro rfl
        exact tri hpq hqs (sym hpt)
      refine ⟨?_, hts⟩
      rcases cross htu hqs with h | h | h | h
      · exact (tri hpt h (sym hpq)).elim
      · exact (hstop h).elim
      · exact ((sq hpt htu h (sym hpq)).elim (Ne.symm hup) htq).elim
      · exact h
    have pentagon : ∃ a b c d e, r a b ∧ r b c ∧ r c d ∧ r d e ∧ r e a ∧
        a ≠ c ∧ b ≠ d ∧ c ≠ e ∧ d ≠ a ∧ e ≠ b := by
      rcases cross hbc hxy with h | h | h | h
      · obtain ⟨hyd, hxd⟩ := side hbc hcd hxy h hbd hxc hyc hyb
        exact ⟨b,x,y,d,c,h,hxy,hyd,sym hcd,sym hbc,Ne.symm hyb,hxd,hyc,Ne.symm hbd,Ne.symm hxc⟩
      · obtain ⟨hxd, hyd⟩ := side hbc hcd (sym hxy) h hbd hyc hxc hxb
        exact ⟨b,y,x,d,c,h,sym hxy,hxd,sym hcd,sym hbc,Ne.symm hxb,hyd,hxc,Ne.symm hbd,Ne.symm hyc⟩
      · obtain ⟨hya, hxa⟩ := side (sym hbc) (sym hab) hxy h (Ne.symm hac) hxb hyb hyc
        exact ⟨c,x,y,a,b,h,hxy,hya,hab,hbc,Ne.symm hyc,hxa,hyb,hac,Ne.symm hxb⟩
      · obtain ⟨hxa, hya⟩ := side (sym hbc) (sym hab) (sym hxy) h (Ne.symm hac) hyb hxb hxc
        exact ⟨c,y,x,a,b,h,sym hxy,hxa,hab,hbc,Ne.symm hxc,hya,hxb,hac,Ne.symm hyb⟩
    obtain ⟨a,b,c,d,e,ab,bc,cd,de,ea,ac,bd,ce,da,eb⟩ := pentagon
    have neighbors {a b c d e z : V} (ab : r a b) (bc : r b c) (cd : r c d)
        (de : r d e) (ea : r e a) (ac : a ≠ c) (ad : a ≠ d) (az : r a z) :
        z = b ∨ z = e := by
      rcases cross az cd with h | h | h | h
      · exact (tri ab bc (sym h)).elim
      · exact (tri h de ea).elim
      · exact Or.inl ((sq az h (sym bc) (sym ab)).resolve_left ac)
      · exact Or.inr ((sq az h de ea).resolve_left ad)
    let T : Finset V := {a,b,c,d,e}
    have closed {u v : V} (hu : u ∈ T) (uv : r u v) : v ∈ T := by
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · have h := neighbors ab bc cd de ea ac (Ne.symm da) uv
        tauto
      · have h := neighbors bc cd de ea ab bd (Ne.symm eb) uv
        tauto
      · have h := neighbors cd de ea ab bc ce (Ne.symm ac) uv
        tauto
      · have h := neighbors de ea ab bc cd da (Ne.symm bd) uv
        tauto
      · have h := neighbors ea ab bc cd de eb (Ne.symm ce) uv
        tauto
    have ha : a ∈ T := by simp [T]
    have hb : b ∈ T := by simp [T]
    have support {u v} (uv : r u v) : u ∈ T := by
      rcases cross ab uv with h | h | h | h
      · exact closed ha h
      · exact closed (closed ha h) (sym uv)
      · exact closed hb h
      · exact closed (closed hb h) (sym uv)
    refine ⟨a, b, c, d, e, ab, bc, cd, de, ea, ?_⟩
    intro u v uv
    simpa only [T, Finset.mem_insert, Finset.mem_singleton] using support uv
  let r (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
  let eligible (C : Circuit) := IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
    ∀ j, (∀ a b, ¬r C j a b) ∨
      (∃ b c, r C j b c ∧ ∀ u v, r C j u v → u = b ∨ v = b ∨ u = c ∨ v = c) ∨
      ∃ a b c d e, r C j a b ∧ r C j b c ∧ r C j c d ∧ r C j d e ∧ r C j e a ∧
        (∀ u v, r C j u v → u = a ∨ u = b ∨ u = c ∨ u = d ∨ u = e) ∧
          gateVal n C j (pairInput a a) = true
  let stars (C : Circuit) (k : ℕ) := ∀ j < k,
    (∀ u v, ¬r C j u v) ∨ ∃ w, ∀ u v, r C j u v → u = w ∨ v = w
  obtain ⟨B, hmin, hfun, hcross⟩ := hCross n G htri hfour
  have hB : eligible B := by
    refine ⟨hmin, hfun, ?_⟩
    intro j
    have rsym {u v} (huv : r B j u v) : r B j v u := by
      have same : pairInput v u = pairInput u v := by
        funext x
        change decide (x = v ∨ x = u) = decide (x = u ∨ x = v)
        simp only [or_comm]
      refine ⟨huv.1.symm, ?_⟩
      have ho : Owns n B j u v := huv.2
      delta Owns at ho ⊢
      rw [same]
      exact ho
    have shapes := classify (r B j) (fun {u v} => @rsym u v)
      (fun {a b c} ab bc ca => htri a b c ab.1 bc.1 ca.1)
      (fun {a b c d} ab bc cd da => hsquare a b c d ab.1 bc.1 cd.1 da.1)
      (fun {a b c d} => hcross j a b c d)
    rcases shapes with empty | centers | ⟨a,b,c,d,e,ab,bc,cd,de,ea,hs⟩
    · exact Or.inl empty
    · exact Or.inr (Or.inl centers)
    · obtain ⟨z, hz, hf⟩ := oddGate n B hmin.1 j a b c d e ab.2 bc.2 cd.2 de.2 ea.2
      right
      right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h
      · exact ⟨a,b,c,d,e,ab,bc,cd,de,ea,hs,h ▸ hf⟩
      · refine ⟨b,c,d,e,a,bc,cd,de,ea,ab,?_,h ▸ hf⟩
        intro u v uv
        have := hs u v uv
        tauto
      · refine ⟨c,d,e,a,b,cd,de,ea,ab,bc,?_,h ▸ hf⟩
        intro u v uv
        have := hs u v uv
        tauto
      · refine ⟨d,e,a,b,c,de,ea,ab,bc,cd,?_,h ▸ hf⟩
        intro u v uv
        have := hs u v uv
        tauto
      · refine ⟨e,a,b,c,d,ea,ab,bc,cd,de,?_,h ▸ hf⟩
        intro u v uv
        have := hs u v uv
        tauto
  have sameSize (D : Circuit) (hD : eligible D) : D.size = B.size :=
    Nat.le_antisymm (hD.1.2 B hmin.1 (hfun.trans hD.2.1.symm))
      (hmin.2 D hD.1.1 (hD.2.1.trans hfun.symm))
  have prefixes (k : ℕ) (hk : k ≤ B.size) : ∃ D, eligible D ∧ stars D k := by
    induction k with
    | zero => exact ⟨B, hB, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
    | succ k ih =>
      obtain ⟨D, hD, hs⟩ := ih (by omega)
      exact hExtend n G htri hfour D k hD (by rw [sameSize D hD]; omega) hs
  obtain ⟨D, hD, hs⟩ := prefixes B.size (Nat.le_refl _)
  refine ⟨D, hD.1.1, hD.2.1, ?_, ?_⟩
  · intro E hE hEf
    exact hD.1.2 E hE (hEf.trans hD.2.1.symm)
  · intro j hj _
    have hbound : j < B.size := (show j < D.size from hj).trans_le (sameSize D hD).le
    rcases hs j hbound with empty | ⟨w, hw⟩
    · exact Or.inl (fun u v huv ho => empty u v ⟨huv, ho⟩)
    · exact Or.inr ⟨w, fun u v huv ho => hw u v ⟨huv, ho⟩⟩
