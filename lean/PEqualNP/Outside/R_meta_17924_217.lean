import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_17924_217
    (deg2 :
      let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        HasLineDegree 26 (Finset.Ico 13 26) C 2 →
        ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ¬ HasLineDegree 26 (Finset.range 13) C 1 →
        (∀ p l : Fin 13, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
        (∀ P L : Finset (Fin 13), IsMaximalFalse S P L → ¬ IsGeneric S 0 P L →
          C.eval (incidenceInput P L) = false) →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
          HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
          (∀ p l : Fin 13, p ∈ S l → D.eval (incidenceInput {p} {l}) = true) ∧
          D.eval (incidenceInput (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) = false ∧
          (∀ l : Fin 13, D.eval (incidenceInput (S l)ᶜ {l}) = false))
    (deg3 :
      let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        ¬ HasLineDegree 26 (Finset.Ico 13 26) C 2 →
        ¬ HasLineDegree 26 (Finset.range 13) C 2 →
        (∀ p l : Fin 13, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
        (∀ P L : Finset (Fin 13), IsMaximalFalse S P L → ¬ IsGeneric S 0 P L →
          C.eval (incidenceInput P L) = false) →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
          HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
          (∀ p l : Fin 13, p ∈ S l → D.eval (incidenceInput {p} {l}) = true) ∧
          D.eval (incidenceInput (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) = false ∧
          (∀ l : Fin 13, D.eval (incidenceInput (S l)ᶜ {l}) = false)) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x1 : Fin (13 : ℕ)) => {x1, x1 + (1 : Fin (13 : ℕ)), x1 + (3 : Fin (13 : ℕ)), x1 + (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ x1 x4 → x2.eval (PEqualNP.GenericRejection.incidenceInput {x3} {x4}) = Bool.true) ∧ x2.eval (PEqualNP.GenericRejection.incidenceInput (x1 (0 : Fin (13 : ℕ)) ∪ (x1 (0 : Fin (13 : ℕ)))ᶜ) (x1 (0 : Fin (13 : ℕ)) \ x1 (0 : Fin (13 : ℕ)))) = Bool.false ∧ ∀ (x3 : Fin (13 : ℕ)), x2.eval (PEqualNP.GenericRejection.incidenceInput (x1 x3)ᶜ {x3}) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (63 : ℕ) → (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ x1 x7 → x3.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x1 x7 x8 → ¬PEqualNP.GenericRejection.IsGeneric x1 (0 : ℕ) x7 x8 → x3.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x3.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x8 (1 : ℕ) ∧ x2 x8) := by
  dsimp only
  intro C hm hs hp hn
  let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
  have boundary : (IsMaximalFalse S (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0) ∧
      ¬ IsGeneric S 0 (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) ∧
      (∀ l : Fin 13, IsMaximalFalse S (S l)ᶜ {l} ∧ ¬ IsGeneric S 0 (S l)ᶜ {l}) := by
    decide +kernel
  have toX2 (D : Circuit)
      (h1 : ∀ p l : Fin 13, p ∈ S l → D.eval (incidenceInput {p} {l}) = true)
      (h2 : D.eval (incidenceInput (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) = false)
      (h3 : ∀ l : Fin 13, D.eval (incidenceInput (S l)ᶜ {l}) = false) :
      (∀ (x3 x4 : Fin 13), x3 ∈ S x4 → D.eval (incidenceInput {x3} {x4}) = true) ∧
      D.eval (incidenceInput (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) = false ∧
      ∀ (x3 : Fin 13), D.eval (incidenceInput (S x3)ᶜ {x3}) = false := ⟨h1, h2, h3⟩
  by_cases hL1 : HasLineDegree 26 (Finset.Ico 13 26) C 1
  · exact ⟨C, hm, le_rfl, hL1, hp, hn _ _ boundary.1.1 boundary.1.2,
      fun l => hn _ _ (boundary.2 l).1 (boundary.2 l).2⟩
  let pg (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩
  let pc (σ : ℕ → ℕ) (D : Circuit) : Circuit := ⟨D.gates.map (pg σ), σ D.output⟩
  have key_getD {α : Type} (d : α) (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i)
      (init init' : List α) (hl : init.length = n) (hl' : init'.length = n)
      (hi : ∀ i, i < n → init'.getD (σ i) d = init.getD i d) (t0 : List α) (i : ℕ) :
      (init' ++ t0).getD (σ i) d = (init ++ t0).getD i d := by
    by_cases h : i < n
    · have e1 : (init' ++ t0).getD (σ i) d = init'.getD (σ i) d :=
        List.getD_append init' t0 d (σ i) (by rw [hl']; exact hσ1 i h)
      have e2 : (init ++ t0).getD i d = init.getD i d :=
        List.getD_append init t0 d i (by rw [hl]; exact h)
      rw [e1, e2]
      exact hi i h
    · have h' : n ≤ i := Nat.le_of_not_lt h
      have e1 : (init' ++ t0).getD i d = t0.getD (i - init'.length) d :=
        List.getD_append_right init' t0 d i (by rw [hl']; exact h')
      have e2 : (init ++ t0).getD i d = t0.getD (i - init.length) d :=
        List.getD_append_right init t0 d i (by rw [hl]; exact h')
      rw [hσ2 i h', e1, e2, hl, hl']
  have perm_fold {α : Type} (d : α) (F : Gate → List α → α) (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i)
      (hF : ∀ (g : Gate) (acc acc' : List α), (∀ i, acc'.getD (σ i) d = acc.getD i d) →
        F (pg σ g) acc' = F g acc)
      (init init' : List α) (hl : init.length = n) (hl' : init'.length = n)
      (hi : ∀ i, i < n → init'.getD (σ i) d = init.getD i d) (gs : List Gate) (t0 : List α) :
      ∃ t, gs.foldl (fun acc g => acc ++ [F g acc]) (init ++ t0) = init ++ t ∧
        (gs.map (pg σ)).foldl (fun acc g => acc ++ [F g acc]) (init' ++ t0) = init' ++ t := by
    induction gs generalizing t0 with
    | nil => exact ⟨t0, rfl, rfl⟩
    | cons g gs ih =>
      obtain ⟨t, h1, h2⟩ := ih (t0 ++ [F g (init ++ t0)])
      refine ⟨t, ?_, ?_⟩
      · simp only [List.foldl_cons]
        rw [List.append_assoc]
        exact h1
      · simp only [List.map_cons, List.foldl_cons]
        rw [hF g (init ++ t0) (init' ++ t0) (key_getD d σ n hσ1 hσ2 init init' hl hl' hi t0),
          List.append_assoc]
        exact h2
  have pc_eval (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i) (D : Circuit)
      (x x' : List Bool) (hl : x.length = n) (hl' : x'.length = n)
      (hi : ∀ i, i < n → x'.getD (σ i) false = x.getD i false) :
      (pc σ D).eval x' = D.eval x := by
    have hF : ∀ (g : Gate) (acc acc' : List Bool),
        (∀ i, acc'.getD (σ i) false = acc.getD i false) →
        (pg σ g).op.eval ((pg σ g).inputs.map fun i => acc'.getD i false) =
          g.op.eval (g.inputs.map fun i => acc.getD i false) := by
      intro g acc acc' h
      show g.op.eval ((g.inputs.map σ).map fun i => acc'.getD i false) = _
      rw [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => h i)
    obtain ⟨t, h1, h2⟩ := perm_fold false
      (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)) σ n hσ1 hσ2 hF x x' hl hl' hi
      D.gates []
    rw [List.append_nil] at h1 h2
    unfold Circuit.eval Circuit.wires
    rw [h1, h2]
    exact key_getD false σ n hσ1 hσ2 x x' hl hl' hi t D.output
  have init_getD (n : ℕ) (m : Finset ℕ) (i : ℕ) (h : i < n) :
      ((List.range n).map fun i => if i ∈ m then 1 else 0).getD i 0 = if i ∈ m then 1 else 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
    rfl
  have pc_deg (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i) (D : Circuit)
      (m m' : Finset ℕ) (hmk : ∀ i, i < n → (i ∈ m ↔ σ i ∈ m')) :
      (pc σ D).lineDeg n m' = D.lineDeg n m := by
    have hF : ∀ (g : Gate) (acc acc' : List ℕ),
        (∀ i, acc'.getD (σ i) 0 = acc.getD i 0) →
        (pg σ g).lineDegree acc' = g.lineDegree acc := by
      intro g acc acc' h
      have hmm : ((pg σ g).inputs.map fun i => acc'.getD i 0) =
          (g.inputs.map fun i => acc.getD i 0) := by
        show ((g.inputs.map σ).map fun i => acc'.getD i 0) = _
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => h i)
      unfold Gate.lineDegree
      rw [hmm]
    have hi : ∀ i, i < n →
        ((List.range n).map fun i => if i ∈ m' then 1 else 0).getD (σ i) 0 =
          ((List.range n).map fun i => if i ∈ m then 1 else 0).getD i 0 := by
      intro i h
      rw [init_getD n m' (σ i) (hσ1 i h), init_getD n m i h]
      by_cases hm2 : i ∈ m
      · rw [ite_eq_left hm2, ite_eq_left ((hmk i h).mp hm2)]
      · rw [ite_eq_right hm2, ite_eq_right (fun h' => hm2 ((hmk i h).mpr h'))]
    have hl : ((List.range n).map fun i => if i ∈ m then 1 else 0).length = n := by simp
    have hl' : ((List.range n).map fun i => if i ∈ m' then 1 else 0).length = n := by simp
    obtain ⟨t, h1, h2⟩ := perm_fold 0 (fun g dd => g.lineDegree dd) σ n hσ1 hσ2 hF _ _ hl hl' hi
      D.gates []
    rw [List.append_nil] at h1 h2
    unfold Circuit.lineDeg Circuit.lineDegrees
    rw [h1, h2]
    exact key_getD 0 σ n hσ1 hσ2 _ _ hl hl' hi t D.output
  have pc_mono (σ : ℕ → ℕ) (D : Circuit) (h : Monotone2 D) : Monotone2 (pc σ D) := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := h g0 hg0
    refine ⟨h0.1, ?_⟩
    show (g0.inputs.map σ).length ≤ 2
    rw [List.length_map]
    exact h0.2
  have pc_size (σ : ℕ → ℕ) (D : Circuit) : (pc σ D).size = D.size := List.length_map _
  let sw (i : ℕ) : ℕ :=
    if i < 13 then 13 + (13 - i) % 13 else if i < 26 then (26 - i) % 13 else i
  have sw_lt (i : ℕ) (h : i < 26) : sw i < 26 := by unfold sw; split_ifs <;> omega
  have sw_ge (i : ℕ) (h : 26 ≤ i) : sw i = i := by unfold sw; split_ifs <;> omega
  have sw_mark_P_to_L (i : ℕ) (h : i < 26) :
      (i ∈ Finset.Ico 13 26 ↔ sw i ∈ Finset.range 13) := by
    rw [Finset.mem_range, Finset.mem_Ico]; unfold sw; split_ifs <;> omega
  have sw_mark_L_to_P (i : ℕ) (h : i < 26) :
      (i ∈ Finset.range 13 ↔ sw i ∈ Finset.Ico 13 26) := by
    rw [Finset.mem_range, Finset.mem_Ico]; unfold sw; split_ifs <;> omega
  have dual_deg_L (D : Circuit) (k : ℕ) :
      HasLineDegree 26 (Finset.Ico 13 26) (pc sw D) k ↔
      HasLineDegree 26 (Finset.range 13) D k := by
    unfold HasLineDegree
    rw [pc_deg sw 26 sw_lt sw_ge D (Finset.range 13) (Finset.Ico 13 26) sw_mark_L_to_P]
  have dual_deg_P (D : Circuit) (k : ℕ) :
      HasLineDegree 26 (Finset.range 13) (pc sw D) k ↔
      HasLineDegree 26 (Finset.Ico 13 26) D k := by
    unfold HasLineDegree
    rw [pc_deg sw 26 sw_lt sw_ge D (Finset.Ico 13 26) (Finset.range 13) sw_mark_P_to_L]
  let dualIn (x : Fin 26 → Bool) : Fin 26 → Bool := fun k => x ⟨sw k.val, sw_lt k.val k.isLt⟩
  have dual_eval (D : Circuit) (x : Fin 26 → Bool) :
      (pc sw D).eval (List.ofFn x) = D.eval (List.ofFn (dualIn x)) := by
    refine pc_eval sw 26 sw_lt sw_ge D (List.ofFn (dualIn x)) (List.ofFn x) (by simp) (by simp) ?_
    intro i h
    simp only [List.getD, List.getElem?_ofFn, dite_eq_left (sw_lt i h), dite_eq_left h,
      Option.getD_some, dualIn]
  have sw_cast : ∀ q : Fin 13,
      sw (Fin.castAdd 13 q : Fin 26).val = (Fin.natAdd 13 (-q) : Fin 26).val := by unfold sw; decide
  have sw_nat : ∀ l : Fin 13,
      sw (Fin.natAdd 13 l : Fin 26).val = (Fin.castAdd 13 (-l) : Fin 26).val := by unfold sw; decide
  have dualIn_cast (z : Fin 26 → Bool) (q : Fin 13) :
      dualIn z (Fin.castAdd 13 q) = z (Fin.natAdd 13 (-q)) := by
    show z ⟨sw (Fin.castAdd 13 q : Fin 26).val, _⟩ = _
    exact congrArg z (Fin.ext (sw_cast q))
  have dualIn_nat (z : Fin 26 → Bool) (l : Fin 13) :
      dualIn z (Fin.natAdd 13 l) = z (Fin.castAdd 13 (-l)) := by
    show z ⟨sw (Fin.natAdd 13 l : Fin 26).val, _⟩ = _
    exact congrArg z (Fin.ext (sw_nat l))
  let turn (T : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter (fun p => -p ∈ T)
  let vec (X Y : Finset (Fin 13)) : Fin 26 → Bool :=
    Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have vecInput (X Y : Finset (Fin 13)) : List.ofFn (vec X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have flipVec (X Y : Finset (Fin 13)) : dualIn (vec X Y) = vec (turn Y) (turn X) := by
    funext i
    refine Fin.addCases (m := 13) (n := 13) (fun u => ?_) (fun v => ?_) i
    · rw [dualIn_cast]
      simp only [vec, Fin.append_left, Fin.append_right, turn, Finset.mem_filter,
        Finset.mem_univ, true_and]
    · rw [dualIn_nat]
      simp only [vec, Fin.append_left, Fin.append_right, turn, Finset.mem_filter,
        Finset.mem_univ, true_and]
  have flipEval (D : Circuit) (P L : Finset (Fin 13)) :
      (pc sw D).eval (incidenceInput P L) = D.eval (incidenceInput (turn L) (turn P)) := by
    rw [← vecInput P L, dual_eval, flipVec, vecInput]
  have flipInc : ∀ p l : Fin 13, p ∈ S l ↔ -l ∈ S (-p) := by decide +kernel
  have memTurn (T : Finset (Fin 13)) (p : Fin 13) : p ∈ turn T ↔ -p ∈ T := by simp [turn]
  have turn_singleton (a : Fin 13) : turn {a} = {-a} := by
    ext x; simp [turn, neg_eq_iff_eq_neg]
  have dual_hp (D : Circuit)
      (hD : ∀ p l : Fin 13, p ∈ S l → D.eval (incidenceInput {p} {l}) = true) :
      ∀ p l : Fin 13, p ∈ S l → (pc sw D).eval (incidenceInput {p} {l}) = true := by
    intro p l hinc
    rw [flipEval, turn_singleton, turn_singleton]
    exact hD (-l) (-p) ((flipInc p l).mp hinc)
  have dual_hn (D : Circuit)
      (hD : ∀ P L : Finset (Fin 13), IsMaximalFalse S P L → ¬ IsGeneric S 0 P L →
        D.eval (incidenceInput P L) = false) :
      ∀ P L : Finset (Fin 13), IsMaximalFalse S P L → ¬ IsGeneric S 0 P L →
        (pc sw D).eval (incidenceInput P L) = false := by
    intro P L hmf hng
    rw [flipEval]
    apply hD (turn L) (turn P)
    · refine ⟨?_, ?_, ?_⟩
      · intro l hl
        rw [Finset.disjoint_left]
        intro p hps hpt
        rw [memTurn] at hl hpt
        have hfalse := Finset.disjoint_left.mp (hmf.1 (-p) hpt) ((flipInc p l).mp hps)
        exact hfalse hl
      · intro q hq hbad
        rw [memTurn] at hq
        apply hmf.2.2 (-q) hq
        intro l hl
        rw [Finset.disjoint_left]
        intro p hps hpP
        rcases Finset.mem_insert.mp hl with rfl | hlold
        · have h1 := Finset.disjoint_left.mp
            (hbad (-p) (by rw [memTurn]; simpa using hpP))
            (by simpa using (flipInc p (-q)).mp hps)
          exact h1 (Finset.mem_insert_self _ _)
        · exact Finset.disjoint_left.mp (hmf.1 l hlold) hps hpP
      · intro q hq hbad
        rw [memTurn] at hq
        apply hmf.2.1 (-q) hq
        intro l hl
        rw [Finset.disjoint_left]
        intro p hps hpP
        rcases Finset.mem_insert.mp hpP with rfl | hpold
        · have h1 := Finset.disjoint_left.mp (hbad q (Finset.mem_insert_self _ _))
            (by simpa using (flipInc (-q) l).mp hps)
          exact h1 (by rw [memTurn]; simpa using hl)
        · exact Finset.disjoint_left.mp (hmf.1 l hl) hps hpold
    · intro hg
      apply hng
      refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
      · intro l hl
        apply hg.2.2.2 (-l)
        intro p hp
        rw [memTurn] at hp
        simpa using (flipInc (-p) l).mp (hl hp)
      · intro p hp
        apply hg.2.2.1 (-p)
        intro l hl
        rw [memTurn] at hl
        simpa using (flipInc p (-l)).mp (hp (-l) hl)
  by_cases hP1 : HasLineDegree 26 (Finset.range 13) C 1
  · have hC' := pc sw C
    refine ⟨pc sw C, pc_mono sw C hm, (pc_size sw C).le, (dual_deg_L C 1).mpr hP1,
      dual_hp C hp, ?_, ?_⟩
    · have := dual_hn C hn _ _ boundary.1.1 boundary.1.2
      exact this
    · intro l
      exact dual_hn C hn _ _ (boundary.2 l).1 (boundary.2 l).2
  by_cases hL2 : HasLineDegree 26 (Finset.Ico 13 26) C 2
  · obtain ⟨D, hD1, hD2, hD3, hD4, hD5, hD6⟩ := deg2 C hm hs hL2 hL1 hP1 hp hn
    exact ⟨D, hD1, hD2, hD3, toX2 D hD4 hD5 hD6⟩
  by_cases hP2 : HasLineDegree 26 (Finset.range 13) C 2
  · obtain ⟨D, hD1, hD2, hD3, hD4, hD5, hD6⟩ :=
      deg2 (pc sw C) (pc_mono sw C hm) ((pc_size sw C).symm ▸ hs)
        ((dual_deg_L C 2).mpr hP2) (mt (dual_deg_L C 1).mp hP1)
        (mt (dual_deg_P C 1).mp hL1) (dual_hp C hp) (dual_hn C hn)
    exact ⟨D, hD1, hD2.trans (pc_size sw C).le, hD3, toX2 D hD4 hD5 hD6⟩
  · obtain ⟨D, hD1, hD2, hD3, hD4, hD5, hD6⟩ := deg3 C hm hs hL2 hP2 hp hn
    exact ⟨D, hD1, hD2, hD3, toX2 D hD4 hD5 hD6⟩
