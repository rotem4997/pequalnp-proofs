import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Input relabeling and the finite observability certificate are adapted from
-- R_meta_7217_317 (Apache-2.0). The copy-erasure decomposition follows
-- R_meta_7217_71. Here copy finding is required only for minimum-size circuits in canonical input order.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_7217_618
    (findCanonical :
      let target := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let inputs := fun (x : Fin 10 → Bool) => List.ofFn x ++ [x 0 && x 2]
      ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
        (∀ x, C.eval (inputs x) = target x) →
        (∀ D : Circuit, FanInTwo D → (∀ x, D.eval (inputs x) = target x) → C.size ≤ D.size) →
        ∃ (v : Fin 10) (S : Finset (Fin C.size)), 4 ≤ S.card ∧
          ∀ i ∈ S, ∃ j < 11 + i.val, ∀ x : Fin 10 → Bool, x v = false →
            let w := C.wires (inputs x)
            w.getD (11 + i.val) false = w.getD j false)
    (eraseCanonical :
      let inputs := fun (x : Fin 10 → Bool) => List.ofFn x ++ [x 0 && x 2]
      ∀ (C : Circuit) (v : Fin 10) (S : Finset (Fin C.size)), FanInTwo C →
        (∀ i ∈ S, ∃ j < 11 + i.val, ∀ x : Fin 10 → Bool, x v = false →
          (C.wires (inputs x)).getD (11 + i.val) false = (C.wires (inputs x)).getD j false) →
        ∃ D : Circuit, FanInTwo D ∧ D.size + S.card ≤ C.size ∧
          ∀ x : Fin 10 → Bool, x v = false → D.eval (inputs x) = C.eval (inputs x)) :
    (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (10 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (10 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (10 : ℕ) → Fin (10 : ℕ)) → (Fin (10 : ℕ) → Bool) → List Bool := fun (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Fin (10 : ℕ) → Bool) => List.ofFn (x3 ∘ x2) ++ [x3 (0 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (18 : ℕ) → (∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2 x4 x7) = x1 x7) → ∃ (x8 : Fin (10 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size + (4 : ℕ) ≤ x3.size ∧ ∀ (x10 : Fin (10 : ℕ) → Bool), x10 x8 = Bool.false → x9.eval (x2 x4 x10) = x3.eval (x2 x4 x10)) := by
  classical
  let edge : (Fin 10 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  let pre : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && x 2]
  have rewire_perm :
      ∀ (C : Circuit) (p : Fin 10 → Fin 10), FanInTwo C →
        ∃ E : Circuit, FanInTwo E ∧ E.size = C.size ∧
          ∀ x : Fin 10 → Bool, E.eval (pre x) = C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) := by
    intro C p hC
    let rename (i : ℕ) : ℕ := if hi : i < 10 then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < 10) : rename i < 10 := by
      simp [rename, hi]
    have late (i : ℕ) (hi : 10 ≤ i) : rename i = i := by
      simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let E : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hC g' hg').1, by simpa [mapGate] using (hC g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length) (lo : 10 ≤ x.length)
        (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have step : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [step]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases h10 : i < 10
            · have := early i h10
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x
    apply run C.gates _ _ (by simp [pre]) (by simp) _ C.output
    intro i
    by_cases hi : i < 10
    · have h1 : rename i < (List.ofFn x).length := by simpa using early i hi
      have h2 : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      simp [rename, hi]
    · rw [late i (by omega),
          List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  have rewire_inv :
      ∀ (D : Circuit) (p q : Fin 10 → Fin 10), (∀ i, p (q i) = i) → FanInTwo D →
        ∃ D' : Circuit, FanInTwo D' ∧ D'.size = D.size ∧
          ∀ x : Fin 10 → Bool, D'.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = D.eval (pre x) := by
    intro D p q hpq hD
    let rename (i : ℕ) : ℕ := if hi : i < 10 then (q ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < 10) : rename i < 10 := by
      simp [rename, hi]
    have late (i : ℕ) (hi : 10 ≤ i) : rename i = i := by
      simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D' : Circuit := ⟨D.gates.map mapGate, rename D.output⟩
    refine ⟨D', ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hD g' hg').1, by simpa [mapGate] using (hD g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length) (lo : 10 ≤ x.length)
        (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have step : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [step]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases h10 : i < 10
            · have := early i h10
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x
    apply run D.gates _ _ (by simp [pre]) (by simp [pre]) _ D.output
    intro i
    by_cases hi : i < 10
    · have h1 : rename i < (List.ofFn (x ∘ p)).length := by simpa using early i hi
      have h2 : i < (List.ofFn x).length := by simpa using hi
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [List.getElem_ofFn, Function.comp_apply]
      have hidx : (⟨rename i, early i hi⟩ : Fin 10) = q ⟨i, hi⟩ := by
        apply Fin.ext
        simp [rename, hi]
      rw [hidx, hpq ⟨i, hi⟩]
    · rw [late i (by omega),
          List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  have bij_of_computes :
      ∀ (C : Circuit) (p : Fin 10 → Fin 10),
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = edge x) →
        Function.Bijective p := by
    intro C p hcomp
    have hsurj : Function.Surjective p := by
      intro v
      by_contra hmiss
      push Not at hmiss
      let nb : Fin 10 → Fin 10 := fun j =>
        ([1, 0, 1, 4, 3, 7, 8, 5, 6, 4] : List (Fin 10)).getD j.val 4
      let xF : Fin 10 → Bool := fun j => decide (j = nb v)
      let xT : Fin 10 → Bool := fun j => decide (j = nb v ∨ j = v)
      have hdiff : edge xF ≠ edge xT := by
        have h : ∀ u : Fin 10,
            edge (fun j => decide (j = nb u)) ≠ edge (fun j => decide (j = nb u ∨ j = u)) := by
          decide
        exact h v
      have hsame_comp : xF ∘ p = xT ∘ p := by
        funext i
        have hne : p i ≠ v := hmiss i
        simp [xF, xT, hne]
      have hsame_extra : (xF 0 && xF 2) = (xT 0 && xT 2) := by
        have h : ∀ u : Fin 10,
            (decide ((0 : Fin 10) = nb u) && decide ((2 : Fin 10) = nb u)) =
            (decide ((0 : Fin 10) = nb u ∨ (0 : Fin 10) = u) &&
             decide ((2 : Fin 10) = nb u ∨ (2 : Fin 10) = u)) := by
          decide
        exact h v
      have heq : C.eval (List.ofFn (xF ∘ p) ++ [xF 0 && xF 2]) =
          C.eval (List.ofFn (xT ∘ p) ++ [xT 0 && xT 2]) := by
        rw [hsame_comp, hsame_extra]
      rw [hcomp xF, hcomp xT] at heq
      exact hdiff heq
    exact ⟨(Finite.injective_iff_surjective (f := p)).mpr hsurj, hsurj⟩
  dsimp only
  intro C p hC hsize hcomp
  have hbij : Function.Bijective p := bij_of_computes C p hcomp
  let eqp := Equiv.ofBijective p hbij
  obtain ⟨E, hE, hEsize, hEeval⟩ := rewire_perm C p hC
  have hEcomp : ∀ x : Fin 10 → Bool, E.eval (pre x) = edge x :=
    fun x => (hEeval x).trans (hcomp x)
  have hex : ∃ m : ℕ, ∃ M : Circuit, FanInTwo M ∧ M.size = m ∧
      ∀ x : Fin 10 → Bool, M.eval (pre x) = edge x := ⟨E.size, E, hE, rfl, hEcomp⟩
  obtain ⟨M, hM, hMsize, hMcomp⟩ := Nat.find_spec hex
  have hMmin (D : Circuit) (hD : FanInTwo D)
      (hd : ∀ x : Fin 10 → Bool, D.eval (pre x) = edge x) : M.size ≤ D.size := by
    rw [hMsize]
    exact Nat.find_min' hex ⟨D, hD, rfl, hd⟩
  have hMle : M.size ≤ E.size := hMmin E hE hEcomp
  obtain ⟨v, S, hfour, hw⟩ := findCanonical M hM (by omega) hMcomp hMmin
  obtain ⟨D, hD, hlen, heval⟩ := eraseCanonical M v S hM hw
  obtain ⟨D', hD', hDsize, hDeval⟩ := rewire_inv D p eqp.symm (fun i => eqp.apply_symm_apply i) hD
  refine ⟨v, D', hD', by omega, ?_⟩
  intro x hx
  exact (hDeval x).trans ((heval x hx).trans ((hMcomp x).trans (hcomp x).symm))
