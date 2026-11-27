import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6708_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def W (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

private lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

private lemma W_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    W C x w = x.getD w false := by
  unfold W
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates x w hw]

private lemma W_oob (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    W C x w = false := by
  unfold W
  have hlen : (C.wires x).length = x.length + C.gates.length := by
    rw [wires_eq_foldl, foldl_stepWire_length]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.wires x).length ≤ w)]

private lemma W_gate (C : Circuit) (hrb : ReadsBack 26 C) (x : List Bool) (hx : x.length = 26)
    (k : ℕ) (hk : k < C.gates.length) :
    W C x (26 + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (W C x)) := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set w0 := (C.gates.take k).foldl stepWire x with hw0
  have hw0_len : w0.length = 26 + k := by
    simp [w0, foldl_stepWire_length, hx, List.length_take]; omega
  have hW : W C x (26 + k) = C.gates[k].op.eval (C.gates[k].inputs.map fun i => w0.getD i false) := by
    unfold W
    conv_lhs => rw [wires_eq_foldl, hsplit, List.foldl_append, List.foldl_cons, ← hw0]
    rw [foldl_stepWire_getD_lt _ _ (26 + k) (by simp [stepWire, hw0_len])]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [gateAt_eq C k hk, hW]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hilt : i < 26 + k := by
    have := hrb k hk i (by rw [gateAt_eq C k hk]; exact hi)
    exact this
  unfold W
  conv_rhs => rw [wires_eq_foldl, hsplit, List.foldl_append]
  exact (foldl_stepWire_getD_lt _ w0 i (by omega)).symm

private lemma gateOp_eval_and_iff (bs : List Bool) :
    GateOp.and.eval bs = true ↔ ∀ b ∈ bs, b = true := by
  simp [GateOp.eval, List.all_eq_true]

private lemma gateOp_eval_or_iff (bs : List Bool) :
    GateOp.or.eval bs = true ↔ ∃ b ∈ bs, b = true := by
  simp [GateOp.eval, List.any_eq_true]

private lemma W_mono (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (x y : List Bool) (hx : x.length = 26) (hy : y.length = 26)
    (hxy : ∀ i < 26, x.getD i false = true → y.getD i false = true) :
    ∀ w, W C x w = true → W C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hw26 : w < 26
    · rw [W_input C x w (by omega)] at hwx
      rw [W_input C y w (by omega)]
      exact hxy w hw26 hwx
    · by_cases hwk : w - 26 < C.gates.length
      · have hweq : w = 26 + (w - 26) := by omega
        rw [hweq] at hwx ⊢
        rw [W_gate C hrb x hx (w - 26) hwk] at hwx
        rw [W_gate C hrb y hy (w - 26) hwk]
        have hg : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq C (w - 26) hwk]; exact List.getElem_mem hwk
        obtain ⟨hop, _⟩ := hmono _ hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hwx ⊢
          rw [gateOp_eval_and_iff] at hwx ⊢
          intro b hb
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
          have hult : u < 26 + (w - 26) := hrb (w - 26) hwk u hu
          exact ih u (by omega) (hwx (W C x u) (List.mem_map_of_mem hu))
        · rw [hop] at hwx ⊢
          rw [gateOp_eval_or_iff] at hwx ⊢
          obtain ⟨b, hb, hbt⟩ := hwx
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
          have hult : u < 26 + (w - 26) := hrb (w - 26) hwk u hu
          exact ⟨W C y u, List.mem_map_of_mem hu, ih u (by omega) hbt⟩
      · rw [W_oob C x w (by omega)] at hwx
        cases hwx

/-! ### Cone properties -/

private lemma foldl_coneStep_length (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega

private lemma foldl_coneStep_getD_lt (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (gs.foldl (coneStep 26) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : j < (coneStep 26 cs g).length := by simp [coneStep]; omega
    rw [ih (coneStep 26 cs g) hlt]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

private lemma cones_getD_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones 26 C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + j))).flatMap
        (fun w => (w - 26) :: (cones 26 C).getD (w - 26) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set cs0 := (C.gates.take j).foldl (coneStep 26) [] with hcs0
  have hcs0_len : cs0.length = j := by
    simp [cs0, foldl_coneStep_length, List.length_take]; omega
  have h1 : (cones 26 C).getD j [] =
      (C.gates[j].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs0.length))).flatMap
        (fun w => (w - 26) :: cs0.getD (w - 26) []) := by
    conv_lhs => unfold cones; rw [hsplit, List.foldl_append, List.foldl_cons, ← hcs0]
    rw [foldl_coneStep_getD_lt _ _ j (by simp [coneStep, hcs0_len])]
    simp [coneStep, List.getD_eq_getElem?_getD, hcs0_len]
  rw [gateAt_eq C j hj, h1, hcs0_len]
  refine List.flatMap_congr fun w hw => ?_
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - 26 < cs0.length := by omega
  congr 1
  conv_rhs => unfold cones; rw [hsplit, List.foldl_append]
  exact (foldl_coneStep_getD_lt _ cs0 (w - 26) hlt).symm

private lemma inCone_iff (C : Circuit) (hrb : ReadsBack 26 C) (i j : ℕ) (hj : j < C.gates.length) :
    InCone 26 C i j ↔
      ∃ w ∈ (gateAt C j).inputs, 26 ≤ w ∧ (i = w - 26 ∨ InCone 26 C i (w - 26)) := by
  unfold InCone
  rw [cones_getD_eq C j hj, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hmem⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    simp only [List.mem_cons] at hmem
    exact ⟨w, hw.1, hw.2.1, hmem⟩
  · rintro ⟨w, hw, hw26, hmem⟩
    have hwlt : w < 26 + j := hrb j hj w hw
    refine ⟨w, ?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hw, hw26, hwlt⟩
    · simp only [List.mem_cons]
      exact hmem

private lemma inCone_lt (C : Circuit) (hrb : ReadsBack 26 C) :
    ∀ j, j < C.gates.length → ∀ i, InCone 26 C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i hij
    rw [inCone_iff C hrb i j hj] at hij
    rcases hij with ⟨w, hw, hw26, rfl | hsub⟩
    · have := hrb j hj w hw; omega
    · have hwlt : w < 26 + j := hrb j hj w hw
      have h1 := ih (w - 26) (by omega) (by omega) i hsub
      omega

private def InWireCone (C : Circuit) (a w : ℕ) : Prop :=
  w = 26 + a ∨ (26 ≤ w ∧ InCone 26 C a (w - 26))

private lemma inWireCone_step (C : Circuit) (hrb : ReadsBack 26 C)
    (k : ℕ) (hk : k < C.gates.length) (u : ℕ) (hu : u ∈ (gateAt C k).inputs)
    (a : ℕ) (ha : InWireCone C a u) :
    InCone 26 C a k := by
  rw [inCone_iff C hrb a k hk]
  rcases ha with rfl | ⟨hu26, hsub⟩
  · exact ⟨26 + a, hu, by omega, Or.inl (by omega)⟩
  · exact ⟨u, hu, hu26, Or.inr hsub⟩

private lemma inWireCone_of_inCone (C : Circuit) (hrb : ReadsBack 26 C)
    (k : ℕ) (hk : k < C.gates.length) (a : ℕ) (ha : InCone 26 C a k) :
    ∃ u ∈ (gateAt C k).inputs, u < 26 + k ∧ InWireCone C a u := by
  rw [inCone_iff C hrb a k hk] at ha
  rcases ha with ⟨u, hu, hu26, hmem⟩
  have hult : u < 26 + k := hrb k hk u hu
  refine ⟨u, hu, hult, ?_⟩
  rcases hmem with rfl | hsub
  · exact Or.inl (by omega)
  · exact Or.inr ⟨hu26, hsub⟩

/-! ### Input encoding for Finset (Fin 13) pairs -/

private def inp (A B : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun i : Fin 13 => Decidable.decide (i ∈ A)) ++
    (List.ofFn fun j : Fin 13 => Decidable.decide (j ∈ B))

private lemma inp_length (A B : Finset (Fin 13)) : (inp A B).length = 26 := by
  simp [inp]

private lemma inp_getD_lt13 (A B : Finset (Fin 13)) (i : ℕ) (hi : i < 13) :
    (inp A B).getD i false = Decidable.decide (⟨i, hi⟩ ∈ A) := by
  simp only [inp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hi]),
      List.getElem?_eq_getElem (by simp [hi]), Option.getD_some, List.getElem_ofFn]

private lemma inp_getD_ge13 (A B : Finset (Fin 13)) (i : ℕ) (hi1 : 13 ≤ i) (hi2 : i < 26) :
    (inp A B).getD i false = Decidable.decide (⟨i - 13, by omega⟩ ∈ B) := by
  simp only [inp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hi1]), List.length_ofFn,
      List.getElem?_eq_getElem (by simp; omega), Option.getD_some, List.getElem_ofFn]

private lemma inp_mono {A' A B' B : Finset (Fin 13)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ∀ i < 26, (inp A' B').getD i false = true → (inp A B).getD i false = true := by
  intro i hi hget
  by_cases hi13 : i < 13
  · rw [inp_getD_lt13 A' B' i hi13] at hget
    rw [inp_getD_lt13 A B i hi13]
    simp only [decide_eq_true_eq] at hget ⊢
    exact hA hget
  · rw [inp_getD_ge13 A' B' i (by omega) hi] at hget
    rw [inp_getD_ge13 A B i (by omega) hi]
    simp only [decide_eq_true_eq] at hget ⊢
    exact hB hget

private lemma W_inp_mono (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    {A' A B' B : Finset (Fin 13)} (hA : A' ⊆ A) (hB : B' ⊆ B) (w : ℕ) :
    W C (inp A' B') w = true → W C (inp A B) w = true :=
  W_mono C hmono hrb (inp A' B') (inp A B) (inp_length A' B') (inp_length A B) (inp_mono hA hB) w

private lemma witness_input_single (A B : Finset (Fin 13)) (w : ℕ) (hw : w < 26)
    (h : (inp A B).getD w false = true) :
    ∃ A' B' : Finset (Fin 13),
      A'.card + B'.card ≤ 1 ∧ A' ⊆ A ∧ B' ⊆ B ∧ (inp A' B').getD w false = true := by
  by_cases hw13 : w < 13
  · rw [inp_getD_lt13 A B w hw13] at h
    simp only [decide_eq_true_eq] at h
    refine ⟨{⟨w, hw13⟩}, ∅, by simp, Finset.singleton_subset_iff.mpr h, Finset.empty_subset _, ?_⟩
    rw [inp_getD_lt13 _ _ w hw13]
    simp
  · rw [inp_getD_ge13 A B w (by omega) hw] at h
    simp only [decide_eq_true_eq] at h
    refine ⟨∅, {⟨w - 13, by omega⟩}, by simp, Finset.empty_subset _, Finset.singleton_subset_iff.mpr h, ?_⟩
    rw [inp_getD_ge13 _ _ w (by omega) hw]
    simp

/-! ### Witness weight bounds by AND-depth structure -/

private lemma witness_no_and (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (A B : Finset (Fin 13)) :
    ∀ w, (∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a w) →
      W C (inp A B) w = true →
      ∃ A' B' : Finset (Fin 13),
        A'.card + B'.card ≤ 1 ∧ A' ⊆ A ∧ B' ⊆ B ∧ W C (inp A' B') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hno hwt
    by_cases hw26 : w < 26
    · rw [W_input C (inp A B) w (by rw [inp_length]; exact hw26)] at hwt
      obtain ⟨A', B', hcard, hA, hB, hget⟩ := witness_input_single A B w hw26 hwt
      refine ⟨A', B', hcard, hA, hB, ?_⟩
      rw [W_input C (inp A' B') w (by rw [inp_length]; exact hw26)]
      exact hget
    · by_cases hwk : w - 26 < C.gates.length
      · have hweq : w = 26 + (w - 26) := by omega
        have hne_and : (gateAt C (w - 26)).op ≠ GateOp.and :=
          fun hop => hno (w - 26) hwk hop (Or.inl hweq)
        have hg : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq C (w - 26) hwk]; exact List.getElem_mem hwk
        obtain ⟨hop, _⟩ := hmono _ hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hor : (gateAt C (w - 26)).op = GateOp.or := hop.resolve_left hne_and
        rw [hweq] at hwt ⊢
        rw [W_gate C hrb (inp A B) (inp_length A B) (w - 26) hwk, hor, gateOp_eval_or_iff] at hwt
        obtain ⟨b, hb, hbt⟩ := hwt
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
        have hult : u < 26 + (w - 26) := hrb (w - 26) hwk u hu
        have hno_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a u := by
          intro a ha hopa hau
          exact hno a ha hopa (Or.inr ⟨by omega, inWireCone_step C hrb (w - 26) hwk u hu a hau⟩)
        obtain ⟨A', B', hcard, hA, hB, hu'⟩ := ih u (by omega) hno_u hbt
        refine ⟨A', B', hcard, hA, hB, ?_⟩
        rw [W_gate C hrb (inp A' B') (inp_length A' B') (w - 26) hwk, hor, gateOp_eval_or_iff]
        exact ⟨W C (inp A' B') u, List.mem_map_of_mem hu, hu'⟩
      · rw [W_oob C (inp A B) w (by rw [inp_length]; omega)] at hwt
        cases hwt

private lemma true_of_i0 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (i₀ : ℕ) (A' B' : Finset (Fin 13)) (hi0t : W C (inp A' B') (26 + i₀) = true) :
    ∀ w, (∀ a < C.gates.length, (gateAt C a).op = GateOp.and → InWireCone C a w → a = i₀) →
      InWireCone C i₀ w → W C (inp A' B') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro honly hmem
    rcases hmem with rfl | ⟨hw26, hinc⟩
    · exact hi0t
    · by_cases hwk : w - 26 < C.gates.length
      · have hne : w - 26 ≠ i₀ := by
          have := inCone_lt C hrb (w - 26) hwk i₀ hinc; omega
        have hne_and : (gateAt C (w - 26)).op ≠ GateOp.and :=
          fun hop => hne (honly (w - 26) hwk hop (Or.inl (by omega)))
        have hg : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq C (w - 26) hwk]; exact List.getElem_mem hwk
        obtain ⟨hop, _⟩ := hmono _ hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hor : (gateAt C (w - 26)).op = GateOp.or := hop.resolve_left hne_and
        obtain ⟨u, hu, hult, hui0⟩ := inWireCone_of_inCone C hrb (w - 26) hwk i₀ hinc
        have honly_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → InWireCone C a u → a = i₀ := by
          intro a ha hopa hau
          exact honly a ha hopa (Or.inr ⟨hw26, inWireCone_step C hrb (w - 26) hwk u hu a hau⟩)
        have hut : W C (inp A' B') u = true := ih u (by omega) honly_u hui0
        rw [show w = 26 + (w - 26) by omega]
        rw [W_gate C hrb (inp A' B') (inp_length A' B') (w - 26) hwk, hor, gateOp_eval_or_iff]
        exact ⟨W C (inp A' B') u, List.mem_map_of_mem hu, hut⟩
      · exfalso
        unfold InCone cones at hinc
        have hlen : (C.gates.foldl (coneStep 26) []).length = C.gates.length := by
          rw [foldl_coneStep_length]; simp
        have hnone : (C.gates.foldl (coneStep 26) []).getD (w - 26) [] = [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.gates.foldl (coneStep 26) []).length ≤ w - 26)]
        rw [hnone] at hinc
        cases hinc

private lemma witness_of_i0_false (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (i₀ : ℕ) (A B : Finset (Fin 13)) (hi0f : W C (inp A B) (26 + i₀) = false) :
    ∀ w, (∀ a < C.gates.length, (gateAt C a).op = GateOp.and → InWireCone C a w → a = i₀) →
      W C (inp A B) w = true →
      ∃ A' B' : Finset (Fin 13),
        A'.card + B'.card ≤ 1 ∧ A' ⊆ A ∧ B' ⊆ B ∧ W C (inp A' B') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro honly hwt
    by_cases hw26 : w < 26
    · rw [W_input C (inp A B) w (by rw [inp_length]; exact hw26)] at hwt
      obtain ⟨A', B', hcard, hA, hB, hget⟩ := witness_input_single A B w hw26 hwt
      refine ⟨A', B', hcard, hA, hB, ?_⟩
      rw [W_input C (inp A' B') w (by rw [inp_length]; exact hw26)]
      exact hget
    · by_cases hwk : w - 26 < C.gates.length
      · have hweq : w = 26 + (w - 26) := by omega
        have hne_i0 : w - 26 ≠ i₀ := by
          intro heq
          rw [hweq, heq, hi0f] at hwt
          cases hwt
        have hne_and : (gateAt C (w - 26)).op ≠ GateOp.and :=
          fun hop => hne_i0 (honly (w - 26) hwk hop (Or.inl hweq))
        have hg : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq C (w - 26) hwk]; exact List.getElem_mem hwk
        obtain ⟨hop, _⟩ := hmono _ hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hor : (gateAt C (w - 26)).op = GateOp.or := hop.resolve_left hne_and
        rw [hweq] at hwt ⊢
        rw [W_gate C hrb (inp A B) (inp_length A B) (w - 26) hwk, hor, gateOp_eval_or_iff] at hwt
        obtain ⟨b, hb, hbt⟩ := hwt
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
        have hult : u < 26 + (w - 26) := hrb (w - 26) hwk u hu
        have honly_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → InWireCone C a u → a = i₀ := by
          intro a ha hopa hau
          exact honly a ha hopa (Or.inr ⟨by omega, inWireCone_step C hrb (w - 26) hwk u hu a hau⟩)
        obtain ⟨A', B', hcard, hA, hB, hu'⟩ := ih u (by omega) honly_u hbt
        refine ⟨A', B', hcard, hA, hB, ?_⟩
        rw [W_gate C hrb (inp A' B') (inp_length A' B') (w - 26) hwk, hor, gateOp_eval_or_iff]
        exact ⟨W C (inp A' B') u, List.mem_map_of_mem hu, hu'⟩
      · rw [W_oob C (inp A B) w (by rw [inp_length]; omega)] at hwt
        cases hwt

private lemma witness_no_j0 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (j₀ : ℕ)
    (hno_pair : ∀ a < C.gates.length, ∀ k < C.gates.length, k ≠ j₀ →
      (gateAt C a).op = GateOp.and → (gateAt C k).op = GateOp.and → ¬ InCone 26 C a k)
    (A B : Finset (Fin 13)) :
    ∀ w, ¬ InWireCone C j₀ w → W C (inp A B) w = true →
      ∃ A' B' : Finset (Fin 13),
        A'.card + B'.card ≤ 2 ∧ A' ⊆ A ∧ B' ⊆ B ∧ W C (inp A' B') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hnoj hwt
    by_cases hw26 : w < 26
    · rw [W_input C (inp A B) w (by rw [inp_length]; exact hw26)] at hwt
      obtain ⟨A', B', hcard, hA, hB, hget⟩ := witness_input_single A B w hw26 hwt
      refine ⟨A', B', by omega, hA, hB, ?_⟩
      rw [W_input C (inp A' B') w (by rw [inp_length]; exact hw26)]
      exact hget
    · by_cases hwk : w - 26 < C.gates.length
      · have hweq : w = 26 + (w - 26) := by omega
        have hne_j0 : w - 26 ≠ j₀ := fun heq => hnoj (Or.inl (by omega))
        have hg : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq C (w - 26) hwk]; exact List.getElem_mem hwk
        obtain ⟨hop, hlen⟩ := hmono _ hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rw [hweq] at hwt ⊢
        rcases hop with hand | hor
        · rw [W_gate C hrb (inp A B) (inp_length A B) (w - 26) hwk, hand, gateOp_eval_and_iff] at hwt
          have hno_op : ∀ u ∈ (gateAt C (w - 26)).inputs,
              ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a u := by
            intro u hu a ha hopa hau
            exact hno_pair a ha (w - 26) hwk hne_j0 hopa hand (inWireCone_step C hrb (w - 26) hwk u hu a hau)
          rcases hin : (gateAt C (w - 26)).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
          · refine ⟨∅, ∅, by simp, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
            rw [W_gate C hrb (inp ∅ ∅) (inp_length ∅ ∅) (w - 26) hwk, hand, hin]
            rfl
          · have hut : W C (inp A B) u = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            obtain ⟨A', B', hcard, hA, hB, hu'⟩ :=
              witness_no_and C hmono hrb A B u (hno_op u (by rw [hin]; simp)) hut
            refine ⟨A', B', by omega, hA, hB, ?_⟩
            rw [W_gate C hrb (inp A' B') (inp_length A' B') (w - 26) hwk, hand, hin]
            simp [GateOp.eval, hu']
          · have hut : W C (inp A B) u = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            have hvt : W C (inp A B) v = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            obtain ⟨A1, B1, hc1, hA1, hB1, hu'⟩ :=
              witness_no_and C hmono hrb A B u (hno_op u (by rw [hin]; simp)) hut
            obtain ⟨A2, B2, hc2, hA2, hB2, hv'⟩ :=
              witness_no_and C hmono hrb A B v (hno_op v (by rw [hin]; simp)) hvt
            have hc12 : (A1 ∪ A2).card + (B1 ∪ B2).card ≤ 2 := by
              have h1 := Finset.card_union_le A1 A2
              have h2 := Finset.card_union_le B1 B2
              omega
            refine ⟨A1 ∪ A2, B1 ∪ B2, hc12, Finset.union_subset hA1 hA2, Finset.union_subset hB1 hB2, ?_⟩
            rw [W_gate C hrb (inp (A1 ∪ A2) (B1 ∪ B2)) (inp_length _ _) (w - 26) hwk, hand, hin]
            have hu'' : W C (inp (A1 ∪ A2) (B1 ∪ B2)) u = true :=
              W_inp_mono C hmono hrb Finset.subset_union_left Finset.subset_union_left u hu'
            have hv'' : W C (inp (A1 ∪ A2) (B1 ∪ B2)) v = true :=
              W_inp_mono C hmono hrb Finset.subset_union_right Finset.subset_union_right v hv'
            simp [GateOp.eval, hu'', hv'']
          · rw [hin] at hlen; simp at hlen
        · rw [W_gate C hrb (inp A B) (inp_length A B) (w - 26) hwk, hor, gateOp_eval_or_iff] at hwt
          obtain ⟨b, hb, hbt⟩ := hwt
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
          have hult : u < 26 + (w - 26) := hrb (w - 26) hwk u hu
          have hnoj_u : ¬ InWireCone C j₀ u :=
            fun h => hnoj (Or.inr ⟨by omega, inWireCone_step C hrb (w - 26) hwk u hu j₀ h⟩)
          obtain ⟨A', B', hcard, hA, hB, hu'⟩ := ih u (by omega) hnoj_u hbt
          refine ⟨A', B', hcard, hA, hB, ?_⟩
          rw [W_gate C hrb (inp A' B') (inp_length A' B') (w - 26) hwk, hor, gateOp_eval_or_iff]
          exact ⟨W C (inp A' B') u, List.mem_map_of_mem hu, hu'⟩
      · rw [W_oob C (inp A B) w (by rw [inp_length]; omega)] at hwt
        cases hwt

private lemma witness_any (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hpairs : andPairs 26 C = 1) (A B : Finset (Fin 13)) :
    ∀ w, W C (inp A B) w = true →
      ∃ A' B' : Finset (Fin 13),
        A'.card + B'.card ≤ 3 ∧ A' ⊆ A ∧ B' ⊆ B ∧ W C (inp A' B') w = true := by
  unfold andPairs at hpairs
  obtain ⟨⟨i₀, j₀⟩, hset⟩ := Finset.card_eq_one.mp hpairs
  have hmem : (i₀, j₀) ∈ ({(i₀, j₀)} : Finset (ℕ × ℕ)) := Finset.mem_singleton_self _
  rw [← hset] at hmem
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  rcases hmem with ⟨⟨hi0_lt, hj0_lt⟩, hi0_and, hj0_and, hi0_j0⟩
  have huniq : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → InCone 26 C i j →
      i = i₀ ∧ j = j₀ := by
    intro i hi j hj hopi hopj hinc
    have hm : (i, j) ∈ ({(i₀, j₀)} : Finset (ℕ × ℕ)) := by
      rw [← hset]
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hopi, hopj, hinc⟩
    simpa using hm
  have hi0_lt_j0 : i₀ < j₀ := inCone_lt C hrb j₀ hj0_lt i₀ hi0_j0
  have hno_pair : ∀ a < C.gates.length, ∀ k < C.gates.length, k ≠ j₀ →
      (gateAt C a).op = GateOp.and → (gateAt C k).op = GateOp.and → ¬ InCone 26 C a k :=
    fun a ha k hk hne hopa hopk hinc => hne (huniq a ha k hk hopa hopk hinc).2
  have hnoj_i0 : ¬ InWireCone C j₀ (26 + i₀) := by
    rintro (heq | ⟨_, hinc⟩)
    · omega
    · have hlt := inCone_lt C hrb i₀ hi0_lt j₀ (by simpa using hinc)
      omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwt
    by_cases hwj : InWireCone C j₀ w
    · rcases hwj with rfl | ⟨hw26, hinc⟩
      · -- w = 26 + j₀ (the unique top AND gate)
        have hgj : gateAt C j₀ ∈ C.gates := by
          rw [gateAt_eq C j₀ hj0_lt]; exact List.getElem_mem hj0_lt
        obtain ⟨_, hlen⟩ := hmono _ hgj
        rw [W_gate C hrb (inp A B) (inp_length A B) j₀ hj0_lt, hj0_and, gateOp_eval_and_iff] at hwt
        have honly_op : ∀ u ∈ (gateAt C j₀).inputs,
            ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → InWireCone C a u → a = i₀ := by
          intro u hu a ha hopa hau
          exact (huniq a ha j₀ hj0_lt hopa hj0_and (inWireCone_step C hrb j₀ hj0_lt u hu a hau)).1
        cases hi0v : W C (inp A B) (26 + i₀)
        · -- i₀ evaluates to false on (A, B): each operand needs weight ≤ 1
          rcases hin : (gateAt C j₀).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
          · refine ⟨∅, ∅, by simp, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
            rw [W_gate C hrb (inp ∅ ∅) (inp_length ∅ ∅) j₀ hj0_lt, hj0_and, hin]; rfl
          · have hut : W C (inp A B) u = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            obtain ⟨A', B', hc, hA, hB, hu'⟩ :=
              witness_of_i0_false C hmono hrb i₀ A B hi0v u (honly_op u (by rw [hin]; simp)) hut
            refine ⟨A', B', by omega, hA, hB, ?_⟩
            rw [W_gate C hrb (inp A' B') (inp_length A' B') j₀ hj0_lt, hj0_and, hin]
            simp [GateOp.eval, hu']
          · have hut : W C (inp A B) u = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            have hvt : W C (inp A B) v = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            obtain ⟨A1, B1, hc1, hA1, hB1, hu'⟩ :=
              witness_of_i0_false C hmono hrb i₀ A B hi0v u (honly_op u (by rw [hin]; simp)) hut
            obtain ⟨A2, B2, hc2, hA2, hB2, hv'⟩ :=
              witness_of_i0_false C hmono hrb i₀ A B hi0v v (honly_op v (by rw [hin]; simp)) hvt
            have hc12 : (A1 ∪ A2).card + (B1 ∪ B2).card ≤ 3 := by
              have h1 := Finset.card_union_le A1 A2
              have h2 := Finset.card_union_le B1 B2
              omega
            refine ⟨A1 ∪ A2, B1 ∪ B2, hc12, Finset.union_subset hA1 hA2, Finset.union_subset hB1 hB2, ?_⟩
            rw [W_gate C hrb (inp (A1 ∪ A2) (B1 ∪ B2)) (inp_length _ _) j₀ hj0_lt, hj0_and, hin]
            have hu'' : W C (inp (A1 ∪ A2) (B1 ∪ B2)) u = true :=
              W_inp_mono C hmono hrb Finset.subset_union_left Finset.subset_union_left u hu'
            have hv'' : W C (inp (A1 ∪ A2) (B1 ∪ B2)) v = true :=
              W_inp_mono C hmono hrb Finset.subset_union_right Finset.subset_union_right v hv'
            simp [GateOp.eval, hu'', hv'']
          · rw [hin] at hlen; simp at hlen
        · -- i₀ evaluates to true on (A, B): weight ≤ 2 witness for i₀ covers any operand reaching i₀
          obtain ⟨A0, B0, hc0, hA0, hB0, hi0'⟩ :=
            witness_no_j0 C hmono hrb j₀ hno_pair A B (26 + i₀) hnoj_i0 hi0v
          rcases hin : (gateAt C j₀).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
          · refine ⟨∅, ∅, by simp, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
            rw [W_gate C hrb (inp ∅ ∅) (inp_length ∅ ∅) j₀ hj0_lt, hj0_and, hin]; rfl
          · have hut : W C (inp A B) u = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            by_cases hui : InWireCone C i₀ u
            · have hu' := true_of_i0 C hmono hrb i₀ A0 B0 hi0' u (honly_op u (by rw [hin]; simp)) hui
              refine ⟨A0, B0, by omega, hA0, hB0, ?_⟩
              rw [W_gate C hrb (inp A0 B0) (inp_length A0 B0) j₀ hj0_lt, hj0_and, hin]
              simp [GateOp.eval, hu']
            · have hno_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a u :=
                fun a ha hopa hau => hui ((honly_op u (by rw [hin]; simp) a ha hopa hau) ▸ hau)
              obtain ⟨A1, B1, hc1, hA1, hB1, hu'⟩ := witness_no_and C hmono hrb A B u hno_u hut
              refine ⟨A1, B1, by omega, hA1, hB1, ?_⟩
              rw [W_gate C hrb (inp A1 B1) (inp_length A1 B1) j₀ hj0_lt, hj0_and, hin]
              simp [GateOp.eval, hu']
          · have hut : W C (inp A B) u = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            have hvt : W C (inp A B) v = true := hwt _ (List.mem_map_of_mem (by rw [hin]; simp))
            by_cases hui : InWireCone C i₀ u
            · have hu0 := true_of_i0 C hmono hrb i₀ A0 B0 hi0' u (honly_op u (by rw [hin]; simp)) hui
              by_cases hvi : InWireCone C i₀ v
              · have hv0 := true_of_i0 C hmono hrb i₀ A0 B0 hi0' v (honly_op v (by rw [hin]; simp)) hvi
                refine ⟨A0, B0, by omega, hA0, hB0, ?_⟩
                rw [W_gate C hrb (inp A0 B0) (inp_length A0 B0) j₀ hj0_lt, hj0_and, hin]
                simp [GateOp.eval, hu0, hv0]
              · have hno_v : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a v :=
                  fun a ha hopa hav => hvi ((honly_op v (by rw [hin]; simp) a ha hopa hav) ▸ hav)
                obtain ⟨A2, B2, hc2, hA2, hB2, hv'⟩ := witness_no_and C hmono hrb A B v hno_v hvt
                have hc02 : (A0 ∪ A2).card + (B0 ∪ B2).card ≤ 3 := by
                  have h1 := Finset.card_union_le A0 A2
                  have h2 := Finset.card_union_le B0 B2
                  omega
                refine ⟨A0 ∪ A2, B0 ∪ B2, hc02, Finset.union_subset hA0 hA2, Finset.union_subset hB0 hB2, ?_⟩
                rw [W_gate C hrb (inp (A0 ∪ A2) (B0 ∪ B2)) (inp_length _ _) j₀ hj0_lt, hj0_and, hin]
                have hu'' : W C (inp (A0 ∪ A2) (B0 ∪ B2)) u = true :=
                  W_inp_mono C hmono hrb Finset.subset_union_left Finset.subset_union_left u hu0
                have hv'' : W C (inp (A0 ∪ A2) (B0 ∪ B2)) v = true :=
                  W_inp_mono C hmono hrb Finset.subset_union_right Finset.subset_union_right v hv'
                simp [GateOp.eval, hu'', hv'']
            · have hno_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a u :=
                fun a ha hopa hau => hui ((honly_op u (by rw [hin]; simp) a ha hopa hau) ▸ hau)
              obtain ⟨A1, B1, hc1, hA1, hB1, hu'⟩ := witness_no_and C hmono hrb A B u hno_u hut
              by_cases hvi : InWireCone C i₀ v
              · have hv0 := true_of_i0 C hmono hrb i₀ A0 B0 hi0' v (honly_op v (by rw [hin]; simp)) hvi
                have hc10 : (A1 ∪ A0).card + (B1 ∪ B0).card ≤ 3 := by
                  have h1 := Finset.card_union_le A1 A0
                  have h2 := Finset.card_union_le B1 B0
                  omega
                refine ⟨A1 ∪ A0, B1 ∪ B0, hc10, Finset.union_subset hA1 hA0, Finset.union_subset hB1 hB0, ?_⟩
                rw [W_gate C hrb (inp (A1 ∪ A0) (B1 ∪ B0)) (inp_length _ _) j₀ hj0_lt, hj0_and, hin]
                have hu'' : W C (inp (A1 ∪ A0) (B1 ∪ B0)) u = true :=
                  W_inp_mono C hmono hrb Finset.subset_union_left Finset.subset_union_left u hu'
                have hv'' : W C (inp (A1 ∪ A0) (B1 ∪ B0)) v = true :=
                  W_inp_mono C hmono hrb Finset.subset_union_right Finset.subset_union_right v hv0
                simp [GateOp.eval, hu'', hv'']
              · have hno_v : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ InWireCone C a v :=
                  fun a ha hopa hav => hvi ((honly_op v (by rw [hin]; simp) a ha hopa hav) ▸ hav)
                obtain ⟨A2, B2, hc2, hA2, hB2, hv'⟩ := witness_no_and C hmono hrb A B v hno_v hvt
                have hc12 : (A1 ∪ A2).card + (B1 ∪ B2).card ≤ 3 := by
                  have h1 := Finset.card_union_le A1 A2
                  have h2 := Finset.card_union_le B1 B2
                  omega
                refine ⟨A1 ∪ A2, B1 ∪ B2, hc12, Finset.union_subset hA1 hA2, Finset.union_subset hB1 hB2, ?_⟩
                rw [W_gate C hrb (inp (A1 ∪ A2) (B1 ∪ B2)) (inp_length _ _) j₀ hj0_lt, hj0_and, hin]
                have hu'' : W C (inp (A1 ∪ A2) (B1 ∪ B2)) u = true :=
                  W_inp_mono C hmono hrb Finset.subset_union_left Finset.subset_union_left u hu'
                have hv'' : W C (inp (A1 ∪ A2) (B1 ∪ B2)) v = true :=
                  W_inp_mono C hmono hrb Finset.subset_union_right Finset.subset_union_right v hv'
                simp [GateOp.eval, hu'', hv'']
          · rw [hin] at hlen; simp at hlen
      · -- w = 26 + k strictly above j₀: gate k cannot be AND, so it is OR
        by_cases hwk : w - 26 < C.gates.length
        · have hweq : w = 26 + (w - 26) := by omega
          have hne_and : (gateAt C (w - 26)).op ≠ GateOp.and := by
            intro hop
            have h1 := (huniq j₀ hj0_lt (w - 26) hwk hj0_and hop hinc).1
            omega
          have hg : gateAt C (w - 26) ∈ C.gates := by
            rw [gateAt_eq C (w - 26) hwk]; exact List.getElem_mem hwk
          obtain ⟨hop, _⟩ := hmono _ hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          have hor : (gateAt C (w - 26)).op = GateOp.or := hop.resolve_left hne_and
          rw [hweq] at hwt ⊢
          rw [W_gate C hrb (inp A B) (inp_length A B) (w - 26) hwk, hor, gateOp_eval_or_iff] at hwt
          obtain ⟨b, hb, hbt⟩ := hwt
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
          have hult : u < 26 + (w - 26) := hrb (w - 26) hwk u hu
          obtain ⟨A', B', hcard, hA, hB, hu'⟩ := ih u (by omega) hbt
          refine ⟨A', B', hcard, hA, hB, ?_⟩
          rw [W_gate C hrb (inp A' B') (inp_length A' B') (w - 26) hwk, hor, gateOp_eval_or_iff]
          exact ⟨W C (inp A' B') u, List.mem_map_of_mem hu, hu'⟩
        · rw [W_oob C (inp A B) w (by rw [inp_length]; omega)] at hwt
          cases hwt
    · -- ¬ InWireCone C j₀ w: Lemma C gives weight ≤ 2 ≤ 3
      obtain ⟨A', B', hcard, hA, hB, hw'⟩ := witness_no_j0 C hmono hrb j₀ hno_pair A B w hwj hwt
      exact ⟨A', B', by omega, hA, hB, hw'⟩

private lemma main (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hpairs : andPairs 26 C = 1) (A B : Finset (Fin 13)) :
    C.eval (inp A B) = true ↔
      ∃ A' B' : Finset (Fin 13), A'.card + B'.card ≤ 3 ∧ A' ⊆ A ∧ B' ⊆ B ∧ C.eval (inp A' B') = true := by
  constructor
  · intro h
    exact witness_any C hmono hrb hpairs A B C.output h
  · rintro ⟨A', B', _, hA, hB, h⟩
    exact W_inp_mono C hmono hrb hA hB C.output h

end PEqualNP.Outside.L_meta_6708_aux

theorem PEqualNP.Outside.L_meta_6708 :
    have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 → PEqualNP.TopForm.andPairs (26 : ℕ) x2 = (1 : ℕ) → ∀ (x6 x7 : Finset (Fin (13 : ℕ))), x2.eval (x1 x6 x7) = Bool.true ↔ ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), x8.card + x9.card ≤ (3 : ℕ) ∧ x8 ⊆ x6 ∧ x9 ⊆ x7 ∧ x2.eval (x1 x8 x9) = Bool.true := by
  intro x1 C hmono hrb hpairs A B
  exact PEqualNP.Outside.L_meta_6708_aux.main C hmono hrb hpairs A B
