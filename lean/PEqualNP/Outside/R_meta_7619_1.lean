import PEqualNP.Defs

-- Turn a finite candidate pool into a bounded construction sequence.
theorem PEqualNP.Outside.R_meta_7619_1
    (enumerate : ∀ (B : Set (Set (Fin 26 → Bool))) (S : Finset (Set (Fin 26 → Bool))),
      (∀ A ∈ S, A ∉ B) →
      ∃ L : List (Set (Fin 26 → Bool)), L.Nodup ∧ L.toFinset ⊆ S ∧
        (∀ i (A : Set (Fin 26 → Bool)), L[i]? = some A →
          ∃ U ∈ B ∪ (↑(L.take i).toFinset : Set (Set (Fin 26 → Bool))),
          ∃ V ∈ B ∪ (↑(L.take i).toFinset : Set (Set (Fin 26 → Bool))),
            A = U ∩ V ∨ A = U ∪ V) ∧
        (∀ U ∈ B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool))),
         ∀ V ∈ B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool))),
         ∀ A ∈ S, A = U ∩ V ∨ A = U ∪ V →
           A ∈ B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool)))))
    (reject : let B : Set (Set (Fin 26 → Bool)) := ({∅, Set.univ} ∪ Set.range (fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}));
      ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 62 → (∀ i (A : Set (Fin 26 → Bool)), L[i]? = some A →
          ∃ U ∈ B ∪ (↑(L.take i).toFinset : Set (Set (Fin 26 → Bool))),
          ∃ V ∈ B ∪ (↑(L.take i).toFinset : Set (Set (Fin 26 → Bool))),
            A = U ∩ V ∨ A = U ∪ V) →
        ∀ U ∈ B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool))),
        ∀ V ∈ B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool))), U ∩ V ≠ {x : Fin 26 → Bool | ∃ p l : Fin 13, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}) :
let x1 : Type := Fin (26 : ℕ) → Bool; have x2 : Set (Set x1) := {∅, Set.univ} ∪ Set.range fun (x2 : Fin (26 : ℕ)) => {x3 : x1 | x3 x2 = Bool.true}; have x3 : Set x1 := {x3 : x1 | ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true}; ∀ (x4 : Finset (Set x1)), x4.card ≤ (62 : ℕ) → (∀ x6 ∈ x4, x6 ∉ x2) → ∃ (x7 : Set (Set x1)), x2 ⊆ x7 ∧ (∀ x8 ∈ x7, ∀ x10 ∈ x7, ∀ x12 ∈ x4, x12 = x8 ∩ x10 ∨ x12 = x8 ∪ x10 → x12 ∈ x7) ∧ ∀ x8 ∈ x7, ∀ x10 ∈ x7, x8 ∩ x10 ≠ x3 := by
  classical
  let B : Set (Set (Fin 26 → Bool)) := ({∅, Set.univ} ∪ Set.range (fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}))
  change ∀ S : Finset (Set (Fin 26 → Bool)), S.card ≤ 62 →
    (∀ A ∈ S, A ∉ B) → ∃ R : Set (Set (Fin 26 → Bool)), B ⊆ R ∧
      (∀ U ∈ R, ∀ V ∈ R, ∀ A ∈ S, A = U ∩ V ∨ A = U ∪ V → A ∈ R) ∧
      ∀ U ∈ R, ∀ V ∈ R, U ∩ V ≠ _
  intro S size outside
  obtain ⟨L, distinct, included, builds, closed⟩ := enumerate B S outside
  refine ⟨B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool))), Set.subset_union_left, closed, ?_⟩
  have length : L.length ≤ 62 := by
    have bound := Finset.card_le_card included
    rw [List.toFinset_card_of_nodup distinct] at bound
    omega
  exact reject L length builds
