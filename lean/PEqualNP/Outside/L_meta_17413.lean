import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17413_aux

private def step (w : List Bool) (g : Finset ℕ × Finset ℕ) : List Bool :=
  w ++ [decide (∀ a ∈ g.1, w.getD a false = true) || decide (∀ b ∈ g.2, w.getD b false = true)]

private def evalWires (gs : List (Finset ℕ × Finset ℕ)) (x : Fin 21 → Bool) : List Bool :=
  gs.foldl step (List.ofFn x ++ [false])

private def zeroIn : Fin 21 → Bool := fun _ => false

private def unitIn (i : Fin 21) : Fin 21 → Bool := fun j => decide (j = i)

private lemma evalWires_length (gs : List (Finset ℕ × Finset ℕ)) (x : Fin 21 → Bool) :
    (evalWires gs x).length = 22 + gs.length := by
  unfold evalWires
  have hgen : ∀ (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  rw [hgen]
  simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]

private lemma step_getD_lt (w : List Bool) (g : Finset ℕ × Finset ℕ) (idx : ℕ) (h : idx < w.length) :
    (step w g).getD idx false = w.getD idx false := by
  have h' : idx < (step w g).length := by
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega
  rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h']
  exact List.getElem_append_left h

private lemma step_getD_self (w : List Bool) (g : Finset ℕ × Finset ℕ) :
    (step w g).getD w.length false =
      (decide (∀ a ∈ g.1, w.getD a false = true) || decide (∀ b ∈ g.2, w.getD b false = true)) := by
  have hlt : w.length < (step w g).length := by
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [step, List.getElem_append_right (le_refl w.length), Nat.sub_self, List.getElem_cons_zero]

private lemma coloring_exists (gs : List (Finset ℕ × Finset ℕ)) :
    ∃ c : Fin 21 → ℕ,
      21 ≤ (Finset.univ.image c).card + gs.length ∧
      ∀ w : ℕ, (evalWires gs zeroIn).getD w false = false →
        ∀ i j : Fin 21,
          (evalWires gs (unitIn i)).getD w false = true →
          (evalWires gs (unitIn j)).getD w false = true →
          c i = c j := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun i => i.val, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ, Fintype.card_fin]
      simp
    · intro w _ i j hi hj
      simp only [evalWires, List.foldl_nil] at hi hj
      have hlen : ∀ x : Fin 21 → Bool, (List.ofFn x ++ [false]).length = 22 := by
        intro x; simp
      by_cases hw : w < 21
      · have hw' : w < (List.ofFn (unitIn i)).length := by simp; exact hw
        have hw1 : w < (List.ofFn (unitIn i) ++ [false]).length := by simp; omega
        have hw2 : w < (List.ofFn (unitIn j) ++ [false]).length := by simp; omega
        rw [List.getD_eq_getElem _ _ hw1, List.getElem_append_left hw', List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ hw2, List.getElem_append_left (by simp; exact hw), List.getElem_ofFn] at hj
        simp only [unitIn, decide_eq_true_eq] at hi hj
        rw [← hi, ← hj]
      · by_cases hw21 : w = 21
        · subst hw21
          have h1 : (List.ofFn (unitIn i) ++ [false]).getD 21 false = false := by
            have hlt : 21 < (List.ofFn (unitIn i) ++ [false]).length := by simp
            rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by simp)]
            simp
          rw [h1] at hi
          exact absurd hi (by decide)
        · have hge : (List.ofFn (unitIn i) ++ [false]).length ≤ w := by simp; omega
          rw [List.getD_eq_default _ _ hge] at hi
          exact absurd hi (by decide)
  | append_singleton gs g ih =>
    obtain ⟨c, hcard, hmono⟩ := ih
    have hcat : ∀ x : Fin 21 → Bool, evalWires (gs ++ [g]) x = step (evalWires gs x) g := by
      intro x
      unfold evalWires
      rw [List.foldl_append]
      rfl
    have hlen : ∀ x : Fin 21 → Bool, (evalWires gs x).length = 22 + gs.length :=
      fun x => evalWires_length gs x
    have hnew_len : (gs ++ [g]).length = gs.length + 1 := by simp
    by_cases htop : (evalWires (gs ++ [g]) zeroIn).getD (22 + gs.length) false = true
    · refine ⟨c, by omega, ?_⟩
      intro w hw0 i j hi hj
      rw [hcat] at hw0 hi hj
      by_cases hlt : w < 22 + gs.length
      · rw [step_getD_lt _ _ _ (by rw [hlen]; exact hlt)] at hw0 hi hj
        exact hmono w hw0 i j hi hj
      · by_cases heq : w = 22 + gs.length
        · subst heq
          rw [hcat] at htop
          rw [htop] at hw0
          exact absurd hw0 (by decide)
        · have hge : (step (evalWires gs (unitIn i)) g).length ≤ w := by
            simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]; omega
          rw [List.getD_eq_default _ _ hge] at hi
          exact absurd hi (by decide)
    · have htop0 : (evalWires (gs ++ [g]) zeroIn).getD (22 + gs.length) false = false :=
        Bool.eq_false_iff.mpr htop
      rw [hcat, ← hlen zeroIn, step_getD_self] at htop0
      have hboth := Bool.or_eq_false_iff.mp htop0
      have ha_ex : ∃ a ∈ g.1, (evalWires gs zeroIn).getD a false = false := by
        have h1 : ¬ ∀ a ∈ g.1, (evalWires gs zeroIn).getD a false = true := by
          intro hall
          have : decide (∀ a ∈ g.1, (evalWires gs zeroIn).getD a false = true) = true :=
            decide_eq_true hall
          rw [this] at hboth
          exact absurd hboth.1 (by decide)
        by_contra hnone
        apply h1
        intro a ha
        by_contra hne
        exact hnone ⟨a, ha, Bool.eq_false_iff.mpr hne⟩
      have hb_ex : ∃ b ∈ g.2, (evalWires gs zeroIn).getD b false = false := by
        have h1 : ¬ ∀ b ∈ g.2, (evalWires gs zeroIn).getD b false = true := by
          intro hall
          have : decide (∀ b ∈ g.2, (evalWires gs zeroIn).getD b false = true) = true :=
            decide_eq_true hall
          rw [this] at hboth
          exact absurd hboth.2 (by decide)
        by_contra hnone
        apply h1
        intro b hb
        by_contra hne
        exact hnone ⟨b, hb, Bool.eq_false_iff.mpr hne⟩
      obtain ⟨a, ha_mem, ha0⟩ := ha_ex
      obtain ⟨b, hb_mem, hb0⟩ := hb_ex
      have hnew_imp : ∀ i : Fin 21,
          (step (evalWires gs (unitIn i)) g).getD (22 + gs.length) false = true →
          (evalWires gs (unitIn i)).getD a false = true ∨ (evalWires gs (unitIn i)).getD b false = true := by
        intro i hi
        rw [← hlen (unitIn i), step_getD_self] at hi
        rcases Bool.or_eq_true_iff.mp hi with h1 | h2
        · left; exact (of_decide_eq_true h1) a ha_mem
        · right; exact (of_decide_eq_true h2) b hb_mem
      by_cases hexA : ∃ i0 : Fin 21, (evalWires gs (unitIn i0)).getD a false = true
      · by_cases hexB : ∃ j0 : Fin 21, (evalWires gs (unitIn j0)).getD b false = true
        · obtain ⟨i0, hi0⟩ := hexA
          obtain ⟨j0, hj0⟩ := hexB
          let colA := c i0
          let colB := c j0
          let c' : Fin 21 → ℕ := fun k => if c k = colB then colA else c k
          have hcard' : (Finset.univ.image c).card - 1 ≤ (Finset.univ.image c').card := by
            have hsub : (Finset.univ.image c).erase colB ⊆ Finset.univ.image c' := by
              intro x hx
              obtain ⟨hne, hxm⟩ := Finset.mem_erase.mp hx
              obtain ⟨k, _, hck⟩ := Finset.mem_image.mp hxm
              refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
              simp only [c', hck, ite_eq_right hne]
            have hmemB : colB ∈ Finset.univ.image c :=
              Finset.mem_image.mpr ⟨j0, Finset.mem_univ j0, rfl⟩
            have herase := Finset.card_erase_of_mem hmemB
            have hle := Finset.card_le_card hsub
            omega
          refine ⟨c', by omega, ?_⟩
          intro w hw0 i j hi hj
          rw [hcat] at hw0 hi hj
          by_cases hlt : w < 22 + gs.length
          · rw [step_getD_lt _ _ _ (by rw [hlen]; exact hlt)] at hw0 hi hj
            have hcij := hmono w hw0 i j hi hj
            simp only [c', hcij]
          · by_cases heq : w = 22 + gs.length
            · subst heq
              have hc' : ∀ k : Fin 21,
                  (step (evalWires gs (unitIn k)) g).getD (22 + gs.length) false = true →
                  c' k = colA := by
                intro k hk
                rcases hnew_imp k hk with hka | hkb
                · have hck : c k = colA := hmono a ha0 k i0 hka hi0
                  simp only [c', hck]
                  split_ifs <;> rfl
                · have hck : c k = colB := hmono b hb0 k j0 hkb hj0
                  simp only [c', hck, ite_true]
              rw [hc' i hi, hc' j hj]
            · have hge : (step (evalWires gs (unitIn i)) g).length ≤ w := by
                simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]; omega
              rw [List.getD_eq_default _ _ hge] at hi
              exact absurd hi (by decide)
        · refine ⟨c, by omega, ?_⟩
          intro w hw0 i j hi hj
          rw [hcat] at hw0 hi hj
          by_cases hlt : w < 22 + gs.length
          · rw [step_getD_lt _ _ _ (by rw [hlen]; exact hlt)] at hw0 hi hj
            exact hmono w hw0 i j hi hj
          · by_cases heq : w = 22 + gs.length
            · subst heq
              have hi' : (evalWires gs (unitIn i)).getD a false = true :=
                (hnew_imp i hi).resolve_right (fun h => hexB ⟨i, h⟩)
              have hj' : (evalWires gs (unitIn j)).getD a false = true :=
                (hnew_imp j hj).resolve_right (fun h => hexB ⟨j, h⟩)
              exact hmono a ha0 i j hi' hj'
            · have hge : (step (evalWires gs (unitIn i)) g).length ≤ w := by
                simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]; omega
              rw [List.getD_eq_default _ _ hge] at hi
              exact absurd hi (by decide)
      · refine ⟨c, by omega, ?_⟩
        intro w hw0 i j hi hj
        rw [hcat] at hw0 hi hj
        by_cases hlt : w < 22 + gs.length
        · rw [step_getD_lt _ _ _ (by rw [hlen]; exact hlt)] at hw0 hi hj
          exact hmono w hw0 i j hi hj
        · by_cases heq : w = 22 + gs.length
          · subst heq
            have hi' : (evalWires gs (unitIn i)).getD b false = true :=
              (hnew_imp i hi).resolve_left (fun h => hexA ⟨i, h⟩)
            have hj' : (evalWires gs (unitIn j)).getD b false = true :=
              (hnew_imp j hj).resolve_left (fun h => hexA ⟨j, h⟩)
            exact hmono b hb0 i j hi' hj'
          · have hge : (step (evalWires gs (unitIn i)) g).length ≤ w := by
              simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]; omega
            rw [List.getD_eq_default _ _ hge] at hi
            exact absurd hi (by decide)

private lemma main_proof :
    (have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → (Fin (21 : ℕ) → Bool) → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : Fin (21 : ℕ) → Bool) =>   have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (List.ofFn x3 ++ [Bool.false]) x1;   Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true); ∀ (x2 : List (Finset ℕ × Finset ℕ)) (x3 : Finset ℕ), (x1 x2 x3 fun (x4 : Fin (21 : ℕ)) => Bool.false) = Bool.false → (∀ (x5 : Fin (21 : ℕ)), (x1 x2 x3 fun (x6 : Fin (21 : ℕ)) => Decidable.decide (x6 = x5)) = Bool.true) → (20 : ℕ) ≤ x2.length) := by
  classical
  dsimp only
  intro gs out h0 h1
  have hw0_ex : ∃ w ∈ out, (evalWires gs zeroIn).getD w false = false := by
    have hnot : ¬ ∀ w ∈ out, (evalWires gs zeroIn).getD w false = true := by
      intro hall
      have htrue : decide (∀ w ∈ out, (evalWires gs zeroIn).getD w false = true) = true :=
        decide_eq_true hall
      change decide (∀ w ∈ out, (evalWires gs zeroIn).getD w false = true) = false at h0
      rw [htrue] at h0
      exact absurd h0 (by decide)
    by_contra hnone
    apply hnot
    intro w hw
    by_contra hne
    exact hnone ⟨w, hw, Bool.eq_false_iff.mpr hne⟩
  obtain ⟨w, hw_mem, hw0⟩ := hw0_ex
  have hw1 : ∀ i : Fin 21, (evalWires gs (unitIn i)).getD w false = true := by
    intro i
    have hi := h1 i
    change decide (∀ u ∈ out, (evalWires gs (unitIn i)).getD u false = true) = true at hi
    exact (of_decide_eq_true hi) w hw_mem
  obtain ⟨c, hcard, hmono⟩ := coloring_exists gs
  have hall_eq : ∀ i : Fin 21, c i = c 0 := fun i => hmono w hw0 i 0 (hw1 i) (hw1 0)
  have hsub : Finset.univ.image c ⊆ {c 0} := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_singleton.mpr (hall_eq i)
  have hle1 : (Finset.univ.image c).card ≤ 1 := by
    calc (Finset.univ.image c).card ≤ ({c 0} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  omega

end PEqualNP.Outside.L_meta_17413_aux

theorem PEqualNP.Outside.L_meta_17413 : (have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → (Fin (21 : ℕ) → Bool) → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : Fin (21 : ℕ) → Bool) =>   have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (List.ofFn x3 ++ [Bool.false]) x1;   Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true); ∀ (x2 : List (Finset ℕ × Finset ℕ)) (x3 : Finset ℕ), (x1 x2 x3 fun (x4 : Fin (21 : ℕ)) => Bool.false) = Bool.false → (∀ (x5 : Fin (21 : ℕ)), (x1 x2 x3 fun (x6 : Fin (21 : ℕ)) => Decidable.decide (x6 = x5)) = Bool.true) → (20 : ℕ) ≤ x2.length) :=
  PEqualNP.Outside.L_meta_17413_aux.main_proof
