import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8998_1
    (h1 :
      let ag : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        ∀ v : Fin 26 → Bool, (∃ l : Fin 13, ∀ l' : Fin 13, v (Fin.natAdd 13 l') = true → l' = l) →
          (D.eval (List.ofFn v) = true ↔
            ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
              v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true)
      let bc : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C =>
        ((C.lineDegrees 26 (Finset.Ico 13 26)).filter (fun x => decide (1 < x))).length
      ∀ C, PEqualNP.MetaComplexity.Monotone2 C → ag C →
        (∀ D, PEqualNP.MetaComplexity.Monotone2 D → ag D → C.size < D.size ∨ C.size = D.size ∧ bc C ≤ bc D) →
        ∀ i a b : ℕ, C.gates[i]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ →
        (∀ j < i, (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 ≤ 1) →
        1 < (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + i) 0 →
        let w := (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.take i) 0).wires (List.ofFn fun k : Fin 26 => decide (k.val < 13))
        ¬ (w.getD a false = false ∧ w.getD b false = false))
    (h2 :
      let ag : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        ∀ v : Fin 26 → Bool, (∃ l : Fin 13, ∀ l' : Fin 13, v (Fin.natAdd 13 l') = true → l' = l) →
          (D.eval (List.ofFn v) = true ↔
            ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
              v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true)
      let bc : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C =>
        ((C.lineDegrees 26 (Finset.Ico 13 26)).filter (fun x => decide (1 < x))).length
      ∀ C, PEqualNP.MetaComplexity.Monotone2 C → ag C →
        (∀ D, PEqualNP.MetaComplexity.Monotone2 D → ag D → C.size < D.size ∨ C.size = D.size ∧ bc C ≤ bc D) →
        ∀ i a b : ℕ, C.gates[i]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ →
        (∀ j < i, (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 ≤ 1) →
        1 < (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + i) 0 →
        let w := (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.take i) 0).wires (List.ofFn fun k : Fin 26 => decide (k.val < 13))
        ¬ (w.getD a false = true ∨ w.getD b false = true)) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x1 : Fin (13 : ℕ)) => {x1, x1 + (1 : Fin (13 : ℕ)), x1 + (3 : Fin (13 : ℕ)), x1 + (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)), ∀ (x4 : Fin (13 : ℕ)), x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true → x4 = x3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     x3.size ≤ (63 : ℕ) →       (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ x1 x7 → x3.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) →         (∀ (x7 x8 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x1 x7 x8 → ¬PEqualNP.GenericRejection.IsGeneric x1 (0 : ℕ) x7 x8 → x3.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) →           ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.Monotone2 x8 ∧               x8.size ≤ x3.size ∧                 (∀ (x9 : Fin (26 : ℕ) → Bool), x2 x9 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 x9) ∧                   ∀ (x9 x10 x11 : ℕ),                     x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } →                       have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.take x9 x8.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };                       have x14 : List ℕ := x13.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));                       (0 : ℕ) < Min.min (x14.getD x10 (0 : ℕ)) (x14.getD x11 (0 : ℕ)) →                         ∃ (x16 : ℕ) (x17 : ℕ),                           ∀ (x18 : Fin (26 : ℕ) → Bool),                             x2 x18 →                               have x20 : List Bool := x13.wires (List.ofFn x18);                               (x20.getD x10 Bool.false && x20.getD x11 Bool.false) = (x20.getD x16 Bool.false || x20.getD x17 Bool.false)) := by
  classical
  dsimp only
  intro C hM hsz hpos hdmf
  let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
  let A : (Fin 26 → Bool) → Prop := fun v => ∃ l : Fin 13, ∀ l' : Fin 13, v (Fin.natAdd 13 l') = true → l' = l
  let inc : (Fin 26 → Bool) → Bool := fun v => decide (∃ p l : Fin 13, p ∈ S l ∧ v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true)
  have hmono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ k, x.getD k false = true → y.getD k false = true) →
      ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD k false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD k false = true := by
    intro gs
    induction gs with
    | nil =>
      intro _ x y _ hxy k hk
      exact hxy k hk
    | cons g gs ih =>
      intro hgs x y hlen hxy k hk
      have hg := hgs g (by simp)
      have hgs' : ∀ g' ∈ gs, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (by simp [hg'])
      refine ih hgs' _ _ (by simp [hlen]) ?_ k hk
      intro j
      rcases lt_trichotomy j x.length with hj | hj | hj
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj,
          List.getElem?_append_left (by omega : j < y.length)]
        exact hxy j
      · subst hj
        have hxj : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD x.length false =
            g.op.eval (g.inputs.map fun i => x.getD i false) := by simp
        have hyj : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD y.length false =
            g.op.eval (g.inputs.map fun i => y.getD i false) := by simp
        rw [hxj, hlen, hyj]
        have heval_and : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
        have heval_or : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
        rcases Set.mem_insert_iff.mp hg.1 with hop | hop
        · rw [hop, heval_and, heval_and]
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact hxy i (h i hi)
        · rw [Set.mem_singleton_iff.mp hop, heval_or, heval_or]
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i, hi, hxi⟩
          exact ⟨i, hi, hxy i hxi⟩
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        intro h
        cases h
  have hC_mono : ∀ (x y : List Bool), x.length = y.length →
      (∀ k, x.getD k false = true → y.getD k false = true) →
      C.eval x = true → C.eval y = true := by
    intro x y hlen hxy hx
    exact hmono C.gates hM x y hlen hxy C.output hx
  have hinc_def : ∀ (X Y : Finset (Fin 13)),
      PEqualNP.GenericRejection.incidenceInput X Y =
        List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) :=
    fun _ _ => rfl
  have hinc_len : ∀ (X Y : Finset (Fin 13)),
      (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y; rw [hinc_def, List.length_append, List.length_ofFn, List.length_ofFn]
  have hinc_get : ∀ (X Y : Finset (Fin 13)) (k : ℕ),
      (PEqualNP.GenericRejection.incidenceInput X Y).getD k false =
        if hk1 : k < 13 then decide (⟨k, hk1⟩ ∈ X)
        else if hk2 : k < 26 then decide (⟨k - 13, by omega⟩ ∈ Y)
        else false := by
    intro X Y k
    rw [hinc_def]
    simp only [List.getD_eq_getElem?_getD]
    by_cases hk1 : k < 13
    · simp only [hk1, ↓reduceDIte]
      rw [List.getElem?_append_left (by simp; exact hk1), List.getElem?_ofFn]
      simp [hk1]
    · simp only [hk1, ↓reduceDIte]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      by_cases hk2 : k < 26
      · simp only [hk2, ↓reduceDIte]
        rw [List.getElem?_ofFn]
        simp [show k - 13 < 13 by omega]
      · simp only [hk2, ↓reduceDIte]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  have hofFn_get : ∀ (v : Fin 26 → Bool) (k : ℕ),
      (List.ofFn v).getD k false =
        if hk1 : k < 13 then v (Fin.castAdd 13 ⟨k, hk1⟩)
        else if hk2 : k < 26 then v (Fin.natAdd 13 (⟨k - 13, by omega⟩ : Fin 13))
        else false := by
    intro v k
    simp only [List.getD_eq_getElem?_getD]
    by_cases hk1 : k < 13
    · simp only [hk1, ↓reduceDIte, List.getElem?_ofFn, show k < 26 by omega]
      rfl
    · simp only [hk1, ↓reduceDIte]
      by_cases hk2 : k < 26
      · simp only [hk2, ↓reduceDIte, List.getElem?_ofFn]
        have he : (⟨k, hk2⟩ : Fin 26) = Fin.natAdd 13 (⟨k - 13, by omega⟩ : Fin 13) := Fin.ext (by simp; omega)
        rw [he]
        rfl
      · simp only [hk2, ↓reduceDIte]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  have hmem_self : ∀ l : Fin 13, l ∈ S l := fun l => Finset.mem_insert_self l _
  have hdiff_line : ∀ l l' : Fin 13, l ≠ l' → ∃ p : Fin 13, p ∈ S l' ∧ p ∉ S l := by
    decide
  have hc_agree : ∀ v : Fin 26 → Bool, A v → PEqualNP.MetaComplexity.circuitFun 26 C v = inc v := by
    intro v hv
    obtain ⟨l, hl⟩ := hv
    by_cases hvl : v (Fin.natAdd 13 l) = true
    · by_cases hp : ∃ p : Fin 13, p ∈ S l ∧ v (Fin.castAdd 13 p) = true
      · obtain ⟨p, hpl, hvp⟩ := hp
        have hinc_t : inc v = true := by
          simp only [inc, decide_eq_true_eq]
          exact ⟨p, l, hpl, hvp, hvl⟩
        have hle_sing : ∀ k, (PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin 13)) {l}).getD k false = true →
            (List.ofFn v).getD k false = true := by
          intro k hk
          rw [hinc_get] at hk
          rw [hofFn_get]
          by_cases hk1 : k < 13
          · simp only [hk1, ↓reduceDIte] at hk ⊢
            have hpeq : (⟨k, hk1⟩ : Fin 13) = p := by simpa using hk
            rw [hpeq]
            exact hvp
          · by_cases hk2 : k < 26
            · simp only [hk1, hk2, ↓reduceDIte] at hk ⊢
              have hleq : (⟨k - 13, by omega⟩ : Fin 13) = l := by simpa using hk
              rw [hleq]
              exact hvl
            · simp only [hk1, hk2, ↓reduceDIte] at hk
              cases hk
        have hC_t : C.eval (List.ofFn v) = true :=
          hC_mono (PEqualNP.GenericRejection.incidenceInput {p} {l}) (List.ofFn v)
            (by rw [hinc_len, List.length_ofFn]) hle_sing (hpos p l hpl)
        change C.eval (List.ofFn v) = inc v
        rw [hC_t, hinc_t]
      · have hinc_f : inc v = false := by
          simp only [inc, decide_eq_false_iff_not]
          rintro ⟨p, l', hpl', hvp, hvl'⟩
          have heq := hl l' hvl'
          subst heq
          exact hp ⟨p, hpl', hvp⟩
        have hdmf_l : PEqualNP.GenericRejection.IsMaximalFalse S (Finset.univ \ S l) {l} ∧
            ¬PEqualNP.GenericRejection.IsGeneric S 0 (Finset.univ \ S l) {l} := by
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · intro l' hl'
            rw [Finset.mem_singleton.mp hl']
            exact disjoint_sdiff_self_right
          · intro q hq hf
            have hqS : q ∈ S l := by
              by_contra hqn
              exact hq (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqn⟩)
            have hdisj := hf l (Finset.mem_singleton_self l)
            exact Finset.disjoint_right.mp hdisj (Finset.mem_insert_self q _) hqS
          · intro l' hl' hf
            have hne : l' ≠ l := fun h => hl' (Finset.mem_singleton.mpr h)
            obtain ⟨q, hq1, hq2⟩ := hdiff_line l l' hne.symm
            have hdisj := hf l' (Finset.mem_insert_self l' _)
            exact Finset.disjoint_right.mp hdisj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq2⟩) hq1
          · intro hg
            refine hg.2.2.2 l ?_
            intro l' hl'
            rw [Finset.mem_singleton.mp hl']
            exact hmem_self l
        have hC_l : C.eval (PEqualNP.GenericRejection.incidenceInput (Finset.univ \ S l) {l}) = false :=
          hdmf (Finset.univ \ S l) {l} hdmf_l.1 hdmf_l.2
        have hle_comp : ∀ k, (List.ofFn v).getD k false = true →
            (PEqualNP.GenericRejection.incidenceInput (Finset.univ \ S l) {l}).getD k false = true := by
          intro k hk
          rw [hofFn_get] at hk
          rw [hinc_get]
          by_cases hk1 : k < 13
          · simp only [hk1, ↓reduceDIte, decide_eq_true_eq, Finset.mem_sdiff, Finset.mem_univ,
              true_and] at hk ⊢
            intro hmem
            exact hp ⟨⟨k, hk1⟩, hmem, hk⟩
          · by_cases hk2 : k < 26
            · simp only [hk1, hk2, ↓reduceDIte, decide_eq_true_eq, Finset.mem_singleton] at hk ⊢
              exact hl ⟨k - 13, by omega⟩ hk
            · simp only [hk1, hk2, ↓reduceDIte] at hk
              cases hk
        have hC_f : C.eval (List.ofFn v) = false := by
          by_contra hnt
          have ht := Bool.eq_true_of_not_eq_false hnt
          have := hC_mono (List.ofFn v) (PEqualNP.GenericRejection.incidenceInput (Finset.univ \ S l) {l})
            (by rw [List.length_ofFn, hinc_len]) hle_comp ht
          rw [hC_l] at this
          cases this
        change C.eval (List.ofFn v) = inc v
        rw [hC_f, hinc_f]
    · have hvl_all : ∀ l' : Fin 13, v (Fin.natAdd 13 l') = false := fun l' => by
        by_contra hnt
        have ht := Bool.eq_true_of_not_eq_false hnt
        have heq := hl l' ht
        subst heq
        exact hvl ht
      have hinc_f : inc v = false := by
        simp only [inc, decide_eq_false_iff_not]
        rintro ⟨p, l', _, _, hvl'⟩
        rw [hvl_all l'] at hvl'
        cases hvl'
      have hdmf_0 : PEqualNP.GenericRejection.IsMaximalFalse S Finset.univ ∅ ∧
          ¬PEqualNP.GenericRejection.IsGeneric S 0 Finset.univ ∅ := by
        refine ⟨⟨fun _ hl0 => by simp at hl0, fun q hq => by simp at hq, fun l0 _ hf => ?_⟩, ?_⟩
        · have hdisj := hf l0 (Finset.mem_insert_self l0 ∅)
          exact Finset.disjoint_right.mp hdisj (Finset.mem_univ l0) (hmem_self l0)
        · intro hg
          exact hg.2.2.2 0 (fun l0 hl0 => by simp at hl0)
      have hC_0 : C.eval (PEqualNP.GenericRejection.incidenceInput Finset.univ ∅) = false :=
        hdmf Finset.univ ∅ hdmf_0.1 hdmf_0.2
      have hle_univ : ∀ k, (List.ofFn v).getD k false = true →
          (PEqualNP.GenericRejection.incidenceInput (Finset.univ : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD k false = true := by
        intro k hk
        rw [hofFn_get] at hk
        rw [hinc_get]
        by_cases hk1 : k < 13
        · simp only [hk1, ↓reduceDIte]; simp
        · by_cases hk2 : k < 26
          · simp only [hk1, hk2, ↓reduceDIte] at hk
            rw [hvl_all ⟨k - 13, by omega⟩] at hk
            cases hk
          · simp only [hk1, hk2, ↓reduceDIte] at hk
            cases hk
      have hC_f : C.eval (List.ofFn v) = false := by
        by_contra hnt
        have ht := Bool.eq_true_of_not_eq_false hnt
        have := hC_mono (List.ofFn v) (PEqualNP.GenericRejection.incidenceInput Finset.univ ∅)
          (by rw [List.length_ofFn, hinc_len]) hle_univ ht
        rw [hC_0] at this
        cases this
      change C.eval (List.ofFn v) = inc v
      rw [hC_f, hinc_f]
  let bc : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun C' =>
    ((C'.lineDegrees 26 (Finset.Ico 13 26)).filter (fun x => decide (1 < x))).length
  let Good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C' =>
    PEqualNP.MetaComplexity.Monotone2 C' ∧ ∀ v, A v → PEqualNP.MetaComplexity.circuitFun 26 C' v = inc v
  have hC_good : Good C := ⟨hM, hc_agree⟩
  have hex_sz : ∃ s : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Good D ∧ D.size = s :=
    ⟨C.size, C, hC_good, rfl⟩
  let s0 := Nat.find hex_sz
  have hs0 : ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Good D ∧ D.size = s0 := Nat.find_spec hex_sz
  have hs0_min : ∀ D, Good D → s0 ≤ D.size := fun D hD => Nat.find_min' hex_sz ⟨D, hD, rfl⟩
  have hex_bc : ∃ b : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Good D ∧ D.size = s0 ∧ bc D = b := by
    obtain ⟨D, hD1, hD2⟩ := hs0
    exact ⟨bc D, D, hD1, hD2, rfl⟩
  let b0 := Nat.find hex_bc
  obtain ⟨Cstar, hCstar_good, hCstar_sz, hCstar_bc⟩ := Nat.find_spec hex_bc
  have hb0_min : ∀ D, Good D → D.size = s0 → b0 ≤ bc D :=
    fun D hD hDs => Nat.find_min' hex_bc ⟨D, hD, hDs, rfl⟩
  have hCstar_min : ∀ D, Good D → Cstar.size < D.size ∨ (Cstar.size = D.size ∧ bc Cstar ≤ bc D) := by
    intro D hD
    have hle := hs0_min D hD
    rw [← hCstar_sz] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [hCstar_bc]
      exact hb0_min D hD (by rw [← hCstar_sz, heq])
  have hCstar_ag : ∀ v : Fin 26 → Bool, A v →
      (Cstar.eval (List.ofFn v) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true) := by
    intro v hv
    have he := hCstar_good.2 v hv
    change Cstar.eval (List.ofFn v) = inc v at he
    rw [he]
    simp [inc, S]
  have hmin_ag : ∀ D, PEqualNP.MetaComplexity.Monotone2 D →
      (∀ v : Fin 26 → Bool, A v → (D.eval (List.ofFn v) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true)) →
      Cstar.size < D.size ∨ (Cstar.size = D.size ∧ bc Cstar ≤ bc D) := by
    intro D hMD hAD
    apply hCstar_min D ⟨hMD, ?_⟩
    intro v hv
    have he := hAD v hv
    change PEqualNP.MetaComplexity.circuitFun 26 D v = inc v
    change D.eval (List.ofFn v) = true ↔ _ at he
    rw [show PEqualNP.MetaComplexity.circuitFun 26 D v = D.eval (List.ofFn v) from rfl, Bool.eq_iff_iff, he]
    simp [inc, S]
  let lstep : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun d g => d ++ [g.lineDegree d]
  let base26 : List ℕ := (List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0
  have hld_def : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).lineDegrees 26 (Finset.Ico 13 26) = gs.foldl lstep base26 :=
    fun _ => rfl
  have hld_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (b : List ℕ),
      (gs.foldl lstep b).length = b.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro b; simp
    | cons g gs ih => intro b; rw [List.foldl_cons, ih]; simp [lstep]; omega
  have hld_ext : ∀ (hs : List PEqualNP.CircuitLowerBounds.Gate) (b : List ℕ) (k : ℕ),
      k < b.length → (hs.foldl lstep b).getD k 0 = b.getD k 0 := by
    intro hs
    induction hs with
    | nil => intro b k _; rfl
    | cons g hs ih =>
      intro b k hk
      rw [List.foldl_cons, ih _ _ (by simp [lstep]; omega)]
      simp only [lstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have hld_at : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (b : List ℕ),
      ((gs ++ g :: hs).foldl lstep b).getD (b.length + gs.length) 0 = g.lineDegree (gs.foldl lstep b) := by
    intro gs g hs b
    rw [List.foldl_append, List.foldl_cons, hld_ext hs _ _ (by simp [lstep, hld_len]), ← hld_len gs b]
    simp [lstep]
  have hld_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (b : List ℕ) (k : ℕ),
      k < b.length + gs.length → ((gs ++ hs).foldl lstep b).getD k 0 = (gs.foldl lstep b).getD k 0 := by
    intro gs hs b k hk
    rw [List.foldl_append]
    exact hld_ext hs (gs.foldl lstep b) k (by rw [hld_len]; exact hk)
  have hbase_len : base26.length = 26 := by simp [base26]
  have hbase_le : ∀ k, base26.getD k 0 ≤ 1 := by
    intro k
    simp only [base26, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases h : (List.range 26)[k]? with _ | v
    · simp
    · simp only [Option.map_some, Option.getD_some]
      split_ifs <;> omega
  have hld_and : ∀ (ins : List ℕ) (d : List ℕ),
      (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and ins).lineDegree d =
        (ins.map fun i => d.getD i 0).sum := fun _ _ => rfl
  have hld_or : ∀ (ins : List ℕ) (d : List ℕ),
      (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or ins).lineDegree d =
        (ins.map fun i => d.getD i 0).foldr max 0 := fun _ _ => rfl
  refine ⟨Cstar, hCstar_good.1, ?_, ?_, ?_⟩
  · have := hs0_min C hC_good
    omega
  · intro v hv
    rw [hCstar_good.2 v hv, hc_agree v hv]
  · intro x9 x10 x11 hx9 hmin
    have hx9_lt : x9 < Cstar.gates.length := by
      by_contra hge
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hx9
      cases hx9
    have hsplit_x9 : Cstar.gates = Cstar.gates.take x9 ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [x10, x11]⟩ :: Cstar.gates.drop (x9 + 1) := by
      conv_lhs => rw [← List.take_append_drop x9 Cstar.gates]
      rw [List.drop_eq_getElem_cons hx9_lt]
      have hget : Cstar.gates[x9] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [x10, x11]⟩ := by
        rw [List.getElem?_eq_getElem hx9_lt] at hx9
        exact Option.some.inj hx9
      rw [hget]
    have hgt1_x9 : 1 < (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + x9) 0 := by
      have htake_len : (Cstar.gates.take x9).length = x9 := List.length_take_of_le (Nat.le_of_lt hx9_lt)
      have hat := hld_at (Cstar.gates.take x9) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [x10, x11]⟩
        (Cstar.gates.drop (x9 + 1)) base26
      rw [hbase_len, htake_len, ← hsplit_x9, ← hld_def Cstar.gates, ← hld_def (Cstar.gates.take x9),
        hld_and] at hat
      change 1 < ((PEqualNP.CircuitLowerBounds.Circuit.mk Cstar.gates 0).lineDegrees 26 (Finset.Ico 13 26)).getD (26 + x9) 0
      rw [hat]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    have hex_bad : ∃ j, 1 < (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 := ⟨x9, hgt1_x9⟩
    let i0 := Nat.find hex_bad
    have hi0_gt1 : 1 < (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + i0) 0 := Nat.find_spec hex_bad
    have hi0_min : ∀ j < i0, (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 ≤ 1 := fun j hj =>
      Nat.le_of_not_lt (Nat.find_min hex_bad hj)
    have hi0_lt : i0 < Cstar.gates.length := by
      by_contra hge
      have hle : Cstar.gates.length ≤ i0 := Nat.le_of_not_lt hge
      have hlen : (Cstar.lineDegrees 26 (Finset.Ico 13 26)).length = 26 + Cstar.gates.length := by
        change ((PEqualNP.CircuitLowerBounds.Circuit.mk Cstar.gates 0).lineDegrees 26 (Finset.Ico 13 26)).length = _
        rw [hld_def, hld_len, hbase_len]
      have hzero : (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + i0) 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      omega
    have hpre_le1 : ∀ k, ((PEqualNP.CircuitLowerBounds.Circuit.mk (Cstar.gates.take i0) 0).lineDegrees 26 (Finset.Ico 13 26)).getD k 0 ≤ 1 := by
      intro k
      rw [hld_def]
      have htake_len : (Cstar.gates.take i0).length = i0 := List.length_take_of_le (Nat.le_of_lt hi0_lt)
      by_cases hk : k < 26 + i0
      · have heq : ((Cstar.gates.take i0).foldl lstep base26).getD k 0 = (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD k 0 := by
          change _ = ((PEqualNP.CircuitLowerBounds.Circuit.mk Cstar.gates 0).lineDegrees 26 (Finset.Ico 13 26)).getD k 0
          rw [hld_def]
          conv_rhs => rw [← List.take_append_drop i0 Cstar.gates]
          exact (hld_prefix (Cstar.gates.take i0) (Cstar.gates.drop i0) base26 k (by omega)).symm
        rw [heq]
        by_cases hk26 : k < 26
        · change ((PEqualNP.CircuitLowerBounds.Circuit.mk Cstar.gates 0).lineDegrees 26 (Finset.Ico 13 26)).getD k 0 ≤ 1
          rw [hld_def, hld_ext Cstar.gates base26 k (by omega)]
          exact hbase_le k
        · have hk' : k = 26 + (k - 26) := by omega
          rw [hk']
          exact hi0_min (k - 26) (by omega)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hld_len, hbase_len, htake_len]; omega)]
        simp
    let g0 := Cstar.gates[i0]
    have hg0_mem : g0 ∈ Cstar.gates := List.getElem_mem hi0_lt
    have hg0_m := hCstar_good.1 g0 hg0_mem
    have hdeg_i0 : (Cstar.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + i0) 0 =
        g0.lineDegree ((PEqualNP.CircuitLowerBounds.Circuit.mk (Cstar.gates.take i0) 0).lineDegrees 26 (Finset.Ico 13 26)) := by
      have htake_len : (Cstar.gates.take i0).length = i0 := List.length_take_of_le (Nat.le_of_lt hi0_lt)
      have hsplit_i0 : Cstar.gates = Cstar.gates.take i0 ++ g0 :: Cstar.gates.drop (i0 + 1) := by
        conv_lhs => rw [← List.take_append_drop i0 Cstar.gates]
        rw [List.drop_eq_getElem_cons hi0_lt]
      have hat := hld_at (Cstar.gates.take i0) g0 (Cstar.gates.drop (i0 + 1)) base26
      rw [hbase_len, htake_len, ← hsplit_i0, ← hld_def Cstar.gates, ← hld_def (Cstar.gates.take i0)] at hat
      exact hat
    have hg0_and : g0.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases Set.mem_insert_iff.mp hg0_m.1 with hop | hop
      · exact hop
      · exfalso
        have hor := Set.mem_singleton_iff.mp hop
        rcases g0 with ⟨op0, ins0⟩
        simp only at hor
        subst hor
        rw [hld_or] at hdeg_i0
        have hfold_le : ∀ l : List ℕ,
            (l.map fun i => ((PEqualNP.CircuitLowerBounds.Circuit.mk (Cstar.gates.take i0) 0).lineDegrees 26 (Finset.Ico 13 26)).getD i 0).foldr max 0 ≤ 1 := by
          intro l
          induction l with
          | nil => simp
          | cons u t ih =>
            simp only [List.map_cons, List.foldr_cons]
            exact max_le (hpre_le1 u) ih
        have := hfold_le ins0
        rw [hdeg_i0] at hi0_gt1
        omega
    have hg0_len2 : g0.inputs.length = 2 := by
      have hle2 := hg0_m.2
      rcases g0 with ⟨op0, ins0⟩
      simp only at hg0_and hle2
      subst hg0_and
      rw [hld_and] at hdeg_i0
      rcases ins0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · simp only [List.map_nil, List.sum_nil] at hdeg_i0
        rw [hdeg_i0] at hi0_gt1
        omega
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hdeg_i0
        have := hpre_le1 a
        rw [hdeg_i0] at hi0_gt1
        omega
      · rfl
      · simp at hle2
    obtain ⟨a, b, hins⟩ := List.length_eq_two.mp hg0_len2
    have hgate : Cstar.gates[i0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ := by
      rw [List.getElem?_eq_getElem hi0_lt]
      congr 1
      have hget_eta : Cstar.gates[i0] = ⟨g0.op, g0.inputs⟩ := rfl
      rw [hget_eta, hg0_and, hins]
    have ha1 := h1 Cstar hCstar_good.1 hCstar_ag hmin_ag i0 a b hgate hi0_min hi0_gt1
    have ha2 := h2 Cstar hCstar_good.1 hCstar_ag hmin_ag i0 a b hgate hi0_min hi0_gt1
    dsimp only at ha1 ha2
    cases hwa : ((PEqualNP.CircuitLowerBounds.Circuit.mk (Cstar.gates.take i0) 0).wires (List.ofFn fun k : Fin 26 => decide (k.val < 13))).getD a false <;>
      cases hwb : ((PEqualNP.CircuitLowerBounds.Circuit.mk (Cstar.gates.take i0) 0).wires (List.ofFn fun k : Fin 26 => decide (k.val < 13))).getD b false
    · exact absurd ⟨hwa, hwb⟩ ha1
    · exact absurd (Or.inr hwb) ha2
    · exact absurd (Or.inl hwa) ha2
    · exact absurd (Or.inl hwa) ha2
