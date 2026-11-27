import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_3252_417
    (privateCount :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
        (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        ∀ (T : Finset (Fin N)) (l : Fin N), l ∈ T →
          q+2 ≤ T.card + Fintype.card {p : Fin N // I p l ∧ ∀ k ∈ T.erase l, ¬ I p k})
    (bound :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        100 < q → n = q^2+q+1 → (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        (∀ (T : Finset (Fin n)) (l : Fin n), l ∈ T →
          q+2 ≤ T.card + Fintype.card {p : Fin n // I p l ∧ ∀ k ∈ T.erase l, ¬ I p k}) →
        ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
          let m := n+n
          let one (p i : Fin n) := decide (i=p)
          let A (d : Bool) (w : ℕ) := {p : Fin n |
            (if d then (one p, fun _ => false) else (fun _ => false, one p)) ∈ W w}
          o < m+s →
          (∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true}) →
          (∀ g < s, ∃ a b, max a b < m+g ∧ W (m+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
          (∀ z : (Fin n → Bool) × (Fin n → Bool),
            Fintype.card {l : Fin n // z.2 l = true} ≤ q →
            (z ∈ W o ↔ ∃ p l, I p l ∧ z.1 p = true ∧ z.2 l = true)) →
          (∃ g < s, ∃ d : Bool, ∃ p r : Fin n, p ≠ r ∧ p ∈ A d (m+g) ∧ r ∈ A d (m+g) ∧
            ¬∃ a < m+g, ∃ b < m+g, A d (m+g) = A d a ∪ A d b) →
          n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x19 x21 (x12 + x20) ∧ x23 ∈ x19 x21 (x12 + x20) ∧ ¬∃ x24 < x12 + x20, ∃ x25 < x12 + x20, x19 x21 (x12 + x20) = x19 x21 x24 ∪ x19 x21 x25) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  dsimp only
  intro q n I inst large order degrees unique s o W out inputs steps positive negative witness
  apply bound q n I large order degrees unique (privateCount q n I degrees unique) s o W out inputs steps _ witness
  let below (a b : (Fin n → Bool) × (Fin n → Bool)) :=
    (∀ i, a.1 i = true → b.1 i = true) ∧ (∀ i, a.2 i = true → b.2 i = true)
  have monotone : ∀ w < n+n+s, ∀ a b, below a b → a ∈ W w → b ∈ W w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw a b le ha
      by_cases left : w < n
      · let p : Fin n := ⟨w,left⟩
        have eq : W w = {z | z.1 p = true} := (inputs p).1
        rw [eq] at ha ⊢
        exact le.1 p ha
      · by_cases right : w < n+n
        · let p : Fin n := ⟨w-n, by omega⟩
          have eq : w = n+p.val := by dsimp [p]; omega
          rw [eq,(inputs p).2] at ha ⊢
          exact le.2 p ha
        · let g := w-(n+n)
          have eq : w = n+n+g := by dsimp [g]; omega
          obtain ⟨u,v,lower,law⟩ := steps g (by omega)
          have mx : max u v < w := by rwa [eq]
          have hu : u < w := lt_of_le_of_lt (le_max_left _ _) mx
          have hv : v < w := lt_of_le_of_lt (le_max_right _ _) mx
          have um := ih u hu (by omega) a b le
          have vm := ih v hv (by omega) a b le
          rw [eq] at ha ⊢
          simp only [List.mem_cons,List.not_mem_nil,or_false] at law
          rcases law with union | copy | zero | inter
          · rw [union] at ha ⊢
            exact ha.elim (fun h => Or.inl (um h)) (fun h => Or.inr (vm h))
          · rw [copy] at ha ⊢
            exact um ha
          · rw [zero] at ha
            exact False.elim ha
          · rw [inter] at ha ⊢
            exact ⟨um ha.1,vm ha.2⟩
  intro z sparse
  constructor
  · intro accepted
    by_contra forbidden
    let a : Fin n → Bool := fun p => decide (¬ ∃ l, I p l ∧ z.2 l = true)
    apply negative z.2 sparse
    apply monotone o out z (a,z.2) ?_ accepted
    refine ⟨?_,fun i h => h⟩
    intro p hp
    change decide (¬ ∃ l, I p l ∧ z.2 l = true) = true
    apply decide_eq_true
    rintro ⟨l,inc,line⟩
    exact forbidden ⟨p,l,inc,hp,line⟩
  · rintro ⟨p,l,inc,hp,hl⟩
    apply monotone o out _ z ?_ (positive p l inc)
    refine ⟨?_,?_⟩
    · intro i hi
      change decide (i=p) = true at hi
      rw [of_decide_eq_true hi]
      exact hp
    · intro i hi
      change decide (i=l) = true at hi
      rw [of_decide_eq_true hi]
      exact hl
