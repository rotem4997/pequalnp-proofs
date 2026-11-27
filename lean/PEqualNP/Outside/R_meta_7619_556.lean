import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7619_556
    (targetBuilt :
      have B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}
      have F : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}
      ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 62 → L.Nodup → (∀ A ∈ L, A ∉ B) →
        (∀ i (A : Set (Fin 26 → Bool)), L[i]? = some A →
          ∃ U, (U ∈ B ∨ U ∈ L.take i) ∧ ∃ V, (V ∈ B ∨ V ∈ L.take i) ∧
            (A = U ∩ V ∨ A = U ∪ V)) →
        F ∉ L)
    (splitPair :
      have B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}
      have F : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}
      ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 62 → L.Nodup → (∀ A ∈ L, A ∉ B) → F ∉ L →
        (∀ i (A : Set (Fin 26 → Bool)), L[i]? = some A →
          ∃ U, (U ∈ B ∨ U ∈ L.take i) ∧ ∃ V, (V ∈ B ∨ V ∈ L.take i) ∧
            (A = U ∩ V ∨ A = U ∪ V)) →
        ∀ U ∈ L, ∀ V ∈ L, U ≠ V → F ⊆ U → U ≠ F → F ⊆ V → V ≠ F → U ∩ V ≠ F) :
    (let x1 : Type := Fin (26 : ℕ) → Bool; have x2 : Set (Set x1) := {∅, Set.univ} ∪ Set.range fun (x2 : Fin (26 : ℕ)) => {x3 : x1 | x3 x2 = Bool.true}; have x3 : Set x1 := {x3 : x1 | ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true}; ∀ (x4 : Finset (Set x1)), x4.card ≤ (62 : ℕ) → (∀ x6 ∈ x4, x6 ∉ x2) → ∃ (x7 : Set (Set x1)), x2 ⊆ x7 ∧ (∀ x8 ∈ x7, ∀ x10 ∈ x7, ∀ x12 ∈ x4, x12 = x8 ∩ x10 ∨ x12 = x8 ∪ x10 → x12 ∈ x7) ∧ ∀ x8 ∈ x7, ∀ x10 ∈ x7, x8 ∩ x10 ≠ x3) := by
  classical
  let X := Fin 26 → Bool
  let B : Set (Set X) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : X | x i = true}
  let F : Set X := {x : X | ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}
  change ∀ S : Finset (Set X), S.card ≤ 62 → (∀ A ∈ S, A ∉ B) →
    ∃ R : Set (Set X), B ⊆ R ∧
      (∀ U ∈ R, ∀ V ∈ R, ∀ A ∈ S, A = U ∩ V ∨ A = U ∪ V → A ∈ R) ∧
      ∀ U ∈ R, ∀ V ∈ R, U ∩ V ≠ F
  intro S hScard hSout
  have hexL : ∀ (k : ℕ) (L : List (Set X)), L.Nodup → L.toFinset ⊆ S →
      (∀ i (A : Set X), L[i]? = some A →
        ∃ U ∈ B ∪ (↑(L.take i).toFinset : Set (Set X)),
        ∃ V ∈ B ∪ (↑(L.take i).toFinset : Set (Set X)),
          A = U ∩ V ∨ A = U ∪ V) →
      S.card - L.length ≤ k →
      ∃ L' : List (Set X), L'.Nodup ∧ L'.toFinset ⊆ S ∧
        (∀ i (A : Set X), L'[i]? = some A →
          ∃ U ∈ B ∪ (↑(L'.take i).toFinset : Set (Set X)),
          ∃ V ∈ B ∪ (↑(L'.take i).toFinset : Set (Set X)),
            A = U ∩ V ∨ A = U ∪ V) ∧
        (∀ U ∈ B ∪ (↑L'.toFinset : Set (Set X)),
         ∀ V ∈ B ∪ (↑L'.toFinset : Set (Set X)),
         ∀ A ∈ S, A = U ∩ V ∨ A = U ∪ V →
           A ∈ B ∪ (↑L'.toFinset : Set (Set X))) := by
    intro k
    induction k with
    | zero =>
      intro L hnd hsub hbuild hrem
      have hcard_le : L.length ≤ S.card := by
        have := Finset.card_le_card hsub
        rwa [List.toFinset_card_of_nodup hnd] at this
      have hcard_eq : L.toFinset.card = S.card := by
        rw [List.toFinset_card_of_nodup hnd]; omega
      have hEq : L.toFinset = S := Finset.eq_of_subset_of_card_le hsub (by omega)
      refine ⟨L, hnd, hsub, hbuild, ?_⟩
      intro U _ V _ A hAS _
      exact Or.inr (by rw [Finset.mem_coe, hEq]; exact hAS)
    | succ k ih =>
      intro L hnd hsub hbuild hrem
      by_cases hclosed : ∀ U ∈ B ∪ (↑L.toFinset : Set (Set X)),
          ∀ V ∈ B ∪ (↑L.toFinset : Set (Set X)),
          ∀ A ∈ S, A = U ∩ V ∨ A = U ∪ V →
            A ∈ B ∪ (↑L.toFinset : Set (Set X))
      · exact ⟨L, hnd, hsub, hbuild, hclosed⟩
      · have hex : ∃ U ∈ B ∪ (↑L.toFinset : Set (Set X)),
            ∃ V ∈ B ∪ (↑L.toFinset : Set (Set X)),
            ∃ A ∈ S, (A = U ∩ V ∨ A = U ∪ V) ∧ A ∉ B ∪ (↑L.toFinset : Set (Set X)) := by
          by_contra hno
          apply hclosed
          intro U hU V hV A hAS hEq
          by_contra hnot
          exact hno ⟨U, hU, V, hV, A, hAS, hEq, hnot⟩
        obtain ⟨U, hU, V, hV, A, hAS, hAEq, hAnot⟩ := hex
        have hAnotL : A ∉ L := fun h => hAnot (Or.inr (by simpa using h))
        have hnd' : (L ++ [A]).Nodup := by
          rw [List.nodup_append]
          refine ⟨hnd, List.nodup_singleton A, ?_⟩
          intro x hx y hy heq
          rw [List.mem_singleton.mp hy] at heq
          subst heq
          exact hAnotL hx
        have hsub' : (L ++ [A]).toFinset ⊆ S := by
          intro x hx
          simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hsub (List.mem_toFinset.mpr hx)
          · exact hAS
        have hbuild' : ∀ i (E : Set X), (L ++ [A])[i]? = some E →
            ∃ U0 ∈ B ∪ (↑((L ++ [A]).take i).toFinset : Set (Set X)),
            ∃ V0 ∈ B ∪ (↑((L ++ [A]).take i).toFinset : Set (Set X)),
              E = U0 ∩ V0 ∨ E = U0 ∪ V0 := by
          intro i E hiE
          by_cases hlt : i < L.length
          · rw [List.getElem?_append_left hlt] at hiE
            rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
            exact hbuild i E hiE
          · have hge : L.length ≤ i := Nat.le_of_not_gt hlt
            rw [List.getElem?_append_right hge] at hiE
            have hiEq : i = L.length := by
              by_contra hne
              have hpos : 1 ≤ i - L.length := by omega
              rw [List.getElem?_eq_none (by simp; omega)] at hiE
              cases hiE
            subst hiEq
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hiE
            subst hiE
            rw [List.take_append_of_le_length le_rfl, List.take_length]
            exact ⟨U, hU, V, hV, hAEq⟩
        have hcard_le : (L ++ [A]).length ≤ S.card := by
          have := Finset.card_le_card hsub'
          rwa [List.toFinset_card_of_nodup hnd'] at this
        have hlen' : (L ++ [A]).length = L.length + 1 := by simp
        exact ih (L ++ [A]) hnd' hsub' hbuild' (by omega)
  obtain ⟨L, hnd, hsub, hbuild, hclosed⟩ := hexL S.card [] List.nodup_nil
    (by simp) (by intro i A h; simp at h) (by simp)
  have hLlen : L.length ≤ 62 := by
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at h1
    omega
  have hLout : ∀ A ∈ L, A ∉ B := fun A hA => hSout A (hsub (List.mem_toFinset.mpr hA))
  have hbuild' : ∀ i (A : Set (Fin 26 → Bool)), L[i]? = some A →
      ∃ U, (U ∈ B ∨ U ∈ L.take i) ∧ ∃ V, (V ∈ B ∨ V ∈ L.take i) ∧ (A = U ∩ V ∨ A = U ∪ V) := by
    intro i A hiA
    obtain ⟨U, hU, V, hV, hEq⟩ := hbuild i A hiA
    refine ⟨U, ?_, V, ?_, hEq⟩
    · rcases hU with hU | hU
      · exact Or.inl hU
      · exact Or.inr (List.mem_toFinset.mp hU)
    · rcases hV with hV | hV
      · exact Or.inl hV
      · exact Or.inr (List.mem_toFinset.mp hV)
  have hFnotL : F ∉ L := targetBuilt L hLlen hnd hLout hbuild'
  have hpair00 : (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))) ∈ F := by
    refine ⟨0, 0, by decide, ?_, ?_⟩ <;> simp
  have hpair112 : (fun i : Fin 26 => decide (i = Fin.castAdd 13 (1 : Fin 13) ∨ i = Fin.natAdd 13 (12 : Fin 13))) ∈ F := by
    refine ⟨1, 12, by decide, ?_, ?_⟩ <;> simp
  have hnotBaseSup : ∀ W ∈ B, F ⊆ W → W = Set.univ := by
    intro W hW hFW
    rcases hW with (rfl | rfl) | ⟨i, rfl⟩
    · exact (hFW hpair00).elim
    · rfl
    · exfalso
      have h1 : decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13)) = true := hFW hpair00
      have h2 : decide (i = Fin.castAdd 13 (1 : Fin 13) ∨ i = Fin.natAdd 13 (12 : Fin 13)) = true := hFW hpair112
      rw [decide_eq_true_eq] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with heq | heq <;>
        exact absurd (congrArg Fin.val heq) (by decide)
  refine ⟨B ∪ (↑L.toFinset : Set (Set X)), Set.subset_union_left, hclosed, ?_⟩
  intro U hU V hV hUV
  have hFU : F ⊆ U := by rw [← hUV]; exact Set.inter_subset_left
  have hFV : F ⊆ V := by rw [← hUV]; exact Set.inter_subset_right
  have hUinL : U ∈ L := by
    rcases hU with hUB | hUL
    · have hUuniv : U = Set.univ := hnotBaseSup U hUB hFU
      rw [hUuniv, Set.univ_inter] at hUV
      subst hUV
      rcases hV with hVB | hVL
      · have hFuniv : F = Set.univ := hnotBaseSup F hVB Set.Subset.rfl
        have hfalse_in : (fun _ : Fin 26 => false) ∈ F := by rw [hFuniv]; trivial
        obtain ⟨p, l, _, hp, _⟩ := hfalse_in
        cases hp
      · exact (hFnotL (List.mem_toFinset.mp hVL)).elim
    · exact List.mem_toFinset.mp hUL
  have hVinL : V ∈ L := by
    rcases hV with hVB | hVL
    · have hVuniv : V = Set.univ := hnotBaseSup V hVB hFV
      rw [hVuniv, Set.inter_univ] at hUV
      subst hUV
      exact (hFnotL hUinL).elim
    · exact List.mem_toFinset.mp hVL
  have hUneqF : U ≠ F := fun h => hFnotL (h ▸ hUinL)
  have hVneqF : V ≠ F := fun h => hFnotL (h ▸ hVinL)
  have hUneV : U ≠ V := by
    intro heq
    rw [heq, Set.inter_self] at hUV
    exact hVneqF hUV
  exact splitPair L hLlen hnd hLout hFnotL hbuild' U hUinL V hVinL hUneV
    hFU hUneqF hFV hVneqF hUV
