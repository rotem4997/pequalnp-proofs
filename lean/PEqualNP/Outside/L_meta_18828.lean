import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18828_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

private def mapW (σ : Fin 26 → Fin 26) (w : ℕ) : ℕ :=
  if hw : w < 26 then (σ ⟨w, hw⟩).val else w

private def mapG (σ : Fin 26 → Fin 26) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapW σ)⟩

private theorem foldl_perm (σ : Fin 26 → Fin 26) (gs : List Gate)
    (j0 : ℕ) (hRB : ∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨.or, []⟩).inputs, w < 26 + j0 + j)
    (wd wc : List Bool) (hwd : wd.length = 26 + j0) (hwc : wc.length = 26 + j0)
    (hmatch : ∀ w < 26 + j0, wd.getD (mapW σ w) false = wc.getD w false) :
    ∀ w < 26 + j0 + gs.length,
      ((gs.map (mapG σ)).foldl stepW wd).getD (mapW σ w) false =
        (gs.foldl stepW wc).getD w false := by
  induction gs generalizing j0 wd wc with
  | nil =>
    intro w hw
    simpa using hmatch w (by simpa using hw)
  | cons g gs ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hval : (mapG σ g).op.eval ((mapG σ g).inputs.map fun i => wd.getD i false) =
        g.op.eval (g.inputs.map fun i => wc.getD i false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hlt : w < 26 + j0 := by
        have := hRB 0 (by simp) w (by simpa using hw)
        omega
      exact hmatch w hlt
    have hRB' : ∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨.or, []⟩).inputs, w < 26 + (j0 + 1) + j := by
      intro j hj w hw
      have := hRB (j + 1) (by simp; omega) w (by simpa using hw)
      omega
    have hnext := ih (j0 + 1) hRB' (stepW wd (mapG σ g)) (stepW wc g)
      (by simp [stepW, hwd]; omega) (by simp [stepW, hwc]; omega) ?_
    · intro w hw
      exact hnext w (by simp at hw ⊢; omega)
    · intro w hw
      by_cases hlt : w < 26 + j0
      · have hmlt : mapW σ w < wd.length := by
          dsimp only [mapW]
          split_ifs with h26
          · have := (σ ⟨w, h26⟩).isLt; omega
          · omega
        rw [stepW, List.getD_append _ _ _ _ hmlt, stepW, List.getD_append _ _ _ _ (by omega)]
        exact hmatch w hlt
      · have hweq : w = 26 + j0 := by omega
        subst hweq
        have hmw : mapW σ (26 + j0) = wd.length := by
          dsimp only [mapW]
          rw [dite_eq_right (by omega)]
          omega
        rw [hmw]
        have h1 : (stepW wd (mapG σ g)).getD wd.length false =
            (mapG σ g).op.eval ((mapG σ g).inputs.map fun i => wd.getD i false) := by
          simp [stepW, List.getD_eq_getElem?_getD]
        have h2 : (stepW wc g).getD (26 + j0) false =
            g.op.eval (g.inputs.map fun i => wc.getD i false) := by
          rw [← hwc]
          simp [stepW, List.getD_eq_getElem?_getD]
        rw [h1, h2, hval]

private theorem singer_shift (p l p0 : Fin 13) :
    p ∈ singerLines3 l ↔ p - p0 ∈ singerLines3 (l - p0) := by
  revert p l p0
  decide

private theorem singer_polar (p l l0 : Fin 13) :
    p ∈ singerLines3 l ↔ l0 - l ∈ singerLines3 (l0 - p) := by
  revert p l l0
  decide

private theorem exists_sym (v : Fin 26) :
    ∃ σ : Fin 26 → Fin 26, Function.Bijective σ ∧ σ v = 0 ∧
      ∀ x : Fin 26 → Bool,
        (∃ p l : Fin 13, p ∈ singerLines3 l ∧
          (x ∘ σ) (Fin.castAdd 13 p) = true ∧ (x ∘ σ) (Fin.natAdd 13 l) = true) ↔
        (∃ p l : Fin 13, p ∈ singerLines3 l ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  refine Fin.addCases (m := 13) (n := 13) (fun p0 => ?_) (fun l0 => ?_) v
  · let σ : Fin 26 → Fin 26 := Fin.addCases (m := 13) (n := 13) (motive := fun _ => Fin 26)
      (fun p => Fin.castAdd 13 (p - p0)) (fun l => Fin.natAdd 13 (l - p0))
    let τ : Fin 26 → Fin 26 := Fin.addCases (m := 13) (n := 13) (motive := fun _ => Fin 26)
      (fun p => Fin.castAdd 13 (p + p0)) (fun l => Fin.natAdd 13 (l + p0))
    have hσL : ∀ p : Fin 13, σ (Fin.castAdd 13 p) = Fin.castAdd 13 (p - p0) := Fin.addCases_left
    have hσR : ∀ l : Fin 13, σ (Fin.natAdd 13 l) = Fin.natAdd 13 (l - p0) := Fin.addCases_right
    have hτL : ∀ p : Fin 13, τ (Fin.castAdd 13 p) = Fin.castAdd 13 (p + p0) := Fin.addCases_left
    have hτR : ∀ l : Fin 13, τ (Fin.natAdd 13 l) = Fin.natAdd 13 (l + p0) := Fin.addCases_right
    have hbij : Function.Bijective σ := by
      rw [Function.bijective_iff_has_inverse]
      refine ⟨τ, ?_, ?_⟩
      · intro i
        refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
        · rw [hσL, hτL, sub_add_cancel]
        · rw [hσR, hτR, sub_add_cancel]
      · intro i
        refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
        · rw [hτL, hσL, add_sub_cancel_right]
        · rw [hτR, hσR, add_sub_cancel_right]
    have hzero : σ (Fin.castAdd 13 p0) = 0 := by
      rw [hσL, sub_self]; rfl
    refine ⟨σ, hbij, hzero, fun x => ?_⟩
    constructor
    · rintro ⟨p, l, hpl, hp, hl⟩
      refine ⟨p - p0, l - p0, (singer_shift p l p0).mp hpl, ?_, ?_⟩
      · simpa only [Function.comp_apply, hσL] using hp
      · simpa only [Function.comp_apply, hσR] using hl
    · rintro ⟨p, l, hpl, hp, hl⟩
      refine ⟨p + p0, l + p0, (singer_shift (p + p0) (l + p0) p0).mpr (by simpa using hpl), ?_, ?_⟩
      · simpa only [Function.comp_apply, hσL, add_sub_cancel_right] using hp
      · simpa only [Function.comp_apply, hσR, add_sub_cancel_right] using hl
  · let σ : Fin 26 → Fin 26 := Fin.addCases (m := 13) (n := 13) (motive := fun _ => Fin 26)
      (fun p => Fin.natAdd 13 (l0 - p)) (fun l => Fin.castAdd 13 (l0 - l))
    have hσL : ∀ p : Fin 13, σ (Fin.castAdd 13 p) = Fin.natAdd 13 (l0 - p) := Fin.addCases_left
    have hσR : ∀ l : Fin 13, σ (Fin.natAdd 13 l) = Fin.castAdd 13 (l0 - l) := Fin.addCases_right
    have hinv : Function.LeftInverse σ σ := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
      · rw [hσL, hσR, sub_sub_cancel]
      · rw [hσR, hσL, sub_sub_cancel]
    have hbij : Function.Bijective σ := by
      rw [Function.bijective_iff_has_inverse]
      exact ⟨σ, hinv, hinv⟩
    have hzero : σ (Fin.natAdd 13 l0) = 0 := by
      rw [hσR, sub_self]; rfl
    refine ⟨σ, hbij, hzero, fun x => ?_⟩
    constructor
    · rintro ⟨p, l, hpl, hp, hl⟩
      refine ⟨l0 - l, l0 - p, (singer_polar p l l0).mp hpl, ?_, ?_⟩
      · simpa only [Function.comp_apply, hσR] using hl
      · simpa only [Function.comp_apply, hσL] using hp
    · rintro ⟨p, l, hpl, hp, hl⟩
      refine ⟨l0 - l, l0 - p, (singer_polar (l0 - l) (l0 - p) l0).mpr (by simpa using hpl), ?_, ?_⟩
      · simpa only [Function.comp_apply, hσL, sub_sub_cancel] using hl
      · simpa only [Function.comp_apply, hσR, sub_sub_cancel] using hp

theorem transport_main :
    let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, p ∈ singerLines3 l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    ∀ (v : Fin 26) (C : Circuit), IsAO2 26 C →
      ∃ (σ : Fin 26 → Fin 26) (D : Circuit), Function.Bijective σ ∧ σ v = 0 ∧
        IsAO2 26 D ∧ D.size = C.size ∧
        (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ))) ∧
        ∀ x : Fin 26 → Bool, F (x ∘ σ) ↔ F x := by
  intro F v C hAO
  obtain ⟨σ, hbij, hzero, hF⟩ := exists_sym v
  let D : Circuit := ⟨C.gates.map (mapG σ), mapW σ C.output⟩
  have hDsz : D.size = C.size := by simp [D, Circuit.size]
  have hDAO : IsAO2 26 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩
      exact hAO.1 g0 hg0
    · intro j hj w hw
      have hjC : j < C.gates.length := by simpa [D] using hj
      have hgj : gateAt D j = mapG σ (gateAt C j) := by
        simp [gateAt, D, List.getD_eq_getElem?_getD, hjC]
      rw [hgj] at hw
      simp only [mapG, List.mem_map] at hw
      rcases hw with ⟨w0, hw0, rfl⟩
      have hlt0 : w0 < 26 + j := hAO.2.1 j hjC w0 hw0
      dsimp only [mapW]
      split_ifs with h26
      · have := (σ ⟨w0, h26⟩).isLt; omega
      · omega
    · intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩
      simpa [mapG] using hAO.2.2 g0 hg0
  have hDeval : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := by
    intro x
    by_cases hout : C.output < 26 + C.gates.length
    · have hRB : ∀ j < C.gates.length, ∀ w ∈ (C.gates.getD j ⟨.or, []⟩).inputs, w < 26 + 0 + j := by
        intro j hj w hw
        have := hAO.2.1 j hj w hw
        omega
      have hmatch0 : ∀ w < 26 + 0, (List.ofFn x).getD (mapW σ w) false =
          (List.ofFn (x ∘ σ)).getD w false := by
        intro w hw
        have hw26 : w < 26 := by omega
        dsimp only [mapW]
        rw [dite_eq_left hw26]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw26, (σ ⟨w, hw26⟩).isLt,
          dite_true, Option.getD_some, Function.comp_apply]
      have hsim := foldl_perm σ C.gates 0 hRB (List.ofFn x) (List.ofFn (x ∘ σ))
        (by simp) (by simp) hmatch0 C.output (by omega)
      exact hsim
    · have h1 : (D.wires (List.ofFn x)).length ≤ D.output := by
        change ((C.gates.map (mapG σ)).foldl stepW (List.ofFn x)).length ≤ mapW σ C.output
        rw [foldl_len, List.length_ofFn, List.length_map]
        dsimp only [mapW]
        split_ifs <;> omega
      have h2 : (C.wires (List.ofFn (x ∘ σ))).length ≤ C.output := by
        change (C.gates.foldl stepW (List.ofFn (x ∘ σ))).length ≤ C.output
        rw [foldl_len, List.length_ofFn]
        omega
      unfold Circuit.eval
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
  exact ⟨σ, D, hbij, hzero, hDAO, hDsz, hDeval, hF⟩

end PEqualNP.Outside.L_meta_18828_aux

theorem PEqualNP.Outside.L_meta_18828 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → ∃ (x5 : Fin (26 : ℕ) → Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), Function.Bijective x5 ∧ x5 x2 = (0 : Fin (26 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size = x3.size ∧ (∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = x3.eval (List.ofFn (x7 ∘ x5))) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x1 (x7 ∘ x5) ↔ x1 x7 := by
  exact PEqualNP.Outside.L_meta_18828_aux.transport_main
