import PEqualNP.Defs

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_7619_448
    (geometry : let I := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let E := fun (s : Finset (Fin 13)) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ I p l
      ∀ s, E (E s) = s → 6 ≤ s.card + (E s).card)
    (finiteBound : let I : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (p l : Fin (13 : ℕ)) =>
        (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]
      let E : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (s : Finset (Fin (13 : ℕ))) =>
        {l : Fin (13 : ℕ) | ∀ p ∈ s, ¬I p l}
      let T : Type := {z : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) //
        (∃ (p : Fin (13 : ℕ)) (l : Fin (13 : ℕ)), I p l ∧ z = ({p}, {l})) ∨
        z.2 = E z.1 ∧ z.1 = E z.2}
      have read : T → Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) := Subtype.val
      have B : Set (Set T) :=
        ({∅, Set.univ} ∪ Set.range fun (p : Fin (13 : ℕ)) => {t : T | p ∈ (read t).1}) ∪
        Set.range fun (l : Fin (13 : ℕ)) => {t : T | l ∈ (read t).2}
      ∀ (S : Finset (Set T)), S.card ≤ (62 : ℕ) → ∃ (R : Set (Set T)), B ⊆ R ∧
        (∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ S, c = a ∩ b ∨ c = a ∪ b → c ∈ R) ∧
        ∀ a ∈ R, ∀ b ∈ R, a ∩ b ≠ {t : T | (read t).1.card + (read t).2.card < (6 : ℕ)})
    : (let x1 : Type := Fin (26 : ℕ) → Bool; have x2 : Set (Set x1) := {∅, Set.univ} ∪ Set.range fun (x2 : Fin (26 : ℕ)) => {x3 : x1 | x3 x2 = Bool.true}; have x3 : Set x1 := {x3 : x1 | ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true}; ∀ (x4 : Finset (Set x1)), x4.card ≤ (62 : ℕ) → (∀ x6 ∈ x4, x6 ∉ x2) → ∃ (x7 : Set (Set x1)), x2 ⊆ x7 ∧ (∀ x8 ∈ x7, ∀ x10 ∈ x7, ∀ x12 ∈ x4, x12 = x8 ∩ x10 ∨ x12 = x8 ∪ x10 → x12 ∈ x7) ∧ ∀ x8 ∈ x7, ∀ x10 ∈ x7, x8 ∩ x10 ≠ x3) := by
  classical
  let I := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let E := fun (s : Finset (Fin 13)) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ I p l
  let T := {z : Finset (Fin 13) × Finset (Fin 13) // (∃ p l, I p l ∧ z = ({p},{l})) ∨ (z.2 = E z.1 ∧ z.1 = E z.2)}
  let read : T → Finset (Fin 13) × Finset (Fin 13) := Subtype.val
  let B : Set (Set T) := ({∅,Set.univ} ∪ Set.range (fun i : Fin 13 => {t : T | i ∈ (read t).1})) ∪ Set.range (fun i : Fin 13 => {t : T | i ∈ (read t).2})
  let obs (t : T) : Fin 26 → Bool :=
    fun k => Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ t.val.1)) (fun i => decide (i ∈ t.val.2)) k
  let F := {x : Fin 26 → Bool | ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}
  let P := {t : T | t.val.1.card + t.val.2.card < 6}
  have traceF : obs ⁻¹' F = P := by
    ext t
    change (∃ p l : Fin 13, I p l ∧ obs t (Fin.castAdd 13 p) = true ∧ obs t (Fin.natAdd 13 l) = true) ↔ _
    simp only [obs,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]
    change (∃ p l : Fin 13, I p l ∧ p ∈ t.val.1 ∧ l ∈ t.val.2) ↔ t.val.1.card + t.val.2.card < 6
    rcases t.property with h | h
    · obtain ⟨p,l,edge,h⟩ := h
      rw [h]
      simp [edge]
    · have stable : E (E t.val.1) = t.val.1 := by rw [← h.1,← h.2]
      have size := geometry t.val.1 stable
      change 6 ≤ t.val.1.card + (E t.val.1).card at size
      rw [← h.1] at size
      constructor
      · rintro ⟨p,l,edge,hp,hl⟩
        rw [h.1] at hl
        exact False.elim ((Finset.mem_filter.mp hl).2 p hp edge)
      · intro small
        omega
  intro X0 B0 F0 S bound _
  let sample (A : Set (Fin 26 → Bool)) := obs ⁻¹' A
  let SS := S.image sample
  have budget : SS.card ≤ 62 := Finset.card_image_le.trans bound
  obtain ⟨R,base,closure,safe⟩ := finiteBound SS budget
  let allGood : Set (Set (Fin 26 → Bool)) := {A | sample A ∈ R}
  refine ⟨allGood,?_,?_,?_⟩
  · intro A hA
    rcases hA with h | h
    · rcases h with h | h
      · subst A
        apply base
        apply Or.inl
        apply Or.inl
        left
        rfl
      · have hu : A = Set.univ := h
        subst A
        apply base
        apply Or.inl
        apply Or.inl
        right
        rfl
    · obtain ⟨i,rfl⟩ := h
      apply base
      refine Fin.addCases (m := 13) (n := 13) (motive := fun i : Fin 26 => sample {x | x i = true} ∈ B) ?_ ?_ i
      · intro p
        apply Or.inl
        apply Or.inr
        refine ⟨p,?_⟩
        ext t
        simp [sample,obs,read]
      · intro l
        apply Or.inr
        refine ⟨l,?_⟩
        ext t
        change l ∈ t.val.2 ↔ obs t (Fin.natAdd 13 l) = true
        simp only [obs,Fin.addCases_right,decide_eq_true_eq]
  · intro a ha b hb c hc op
    apply closure (sample a) ha (sample b) hb (sample c) (Finset.mem_image_of_mem _ hc)
    rcases op with op | op
    · exact Or.inl (congrArg sample op)
    · exact Or.inr (congrArg sample op)
  · intro a ha b hb eq
    apply safe (sample a) ha (sample b) hb
    exact (congrArg sample eq).trans traceF
