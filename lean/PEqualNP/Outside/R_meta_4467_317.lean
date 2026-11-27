import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4467_317
  (absorb : ∀ (n : ℕ) (A B : Finset (Finset (Fin n))),
    let m := fun (T : Finset (Finset (Fin n))) => T.filter (fun C => ∀ D ∈ T, D ⊆ C → C ⊆ D)
    m (A ∪ B) = m (m A ∪ m B) ∧
      m (A.biUnion fun C => B.image (fun D => C ∪ D)) =
        m ((m A).biUnion fun C => (m B).image (fun D => C ∪ D)))
  (bound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (s o : ℕ) (G : ℕ → Finset (Finset (Fin (n+n)))),
    let m := fun (T : Finset (Finset (Fin (n+n)))) => T.filter (fun C => ∀ D ∈ T, D ⊆ C → C ⊆ D)
    300 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
    (∀ p t, p ≠ t → ∃! l, I p l ∧ I t l) → 3*n ≤ s+1 → o < n+n+s →
    (∀ i : Fin (n+n), G i = {{i}}) →
    (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧
      (G (n+n+j) = m (G a ∪ G b) ∨
       G (n+n+j) = m ((G a).biUnion fun C => (G b).image (fun D => C ∪ D)))) →
    (∀ C ∈ G o, ∀ p l, I p l → Fin.castAdd n p ∈ C ∨ Fin.natAdd n l ∈ C) →
    (∀ S : Finset (Fin n), S.card ≤ q → ∃ C ∈ G o,
      (∀ p, Fin.castAdd n p ∈ C ↔ ∃ l ∈ S, I p l) ∧
       ∀ l, Fin.natAdd n l ∈ C ↔ l ∉ S) → n*q ≤ 100*s) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 x6 : ℕ) (x7 : ℕ → Finset (Finset (Fin (x2 + x2)))),   (∃ x8 < x5,       ∃ (x9 : ℕ) (x10 : ℕ),         x9 < x10 ∧           x10 < x2 + x2 + x8 ∧             x7 (x2 + x2 + x8) = x7 x9 ∪ x7 x10 ∧               ∃ (x11 : Bool),                 ∀ x12 ∈ [x9, x10],                   ∃ (x14 : Fin x2 → Bool),                     have x15 : Bool → List Bool := fun (x15 : Bool) => if x11 = Bool.true then List.ofFn x14 ++ List.replicate x2 x15 else List.replicate x2 x15 ++ List.ofFn x14;                     have x16 : Bool → Prop := fun (x16 : Bool) => ∀ x17 ∈ x7 x12, ∃ x19 ∈ x17, (x15 x16).getD (↑x19) Bool.false = Bool.true;                     ¬(x16 Bool.false ↔ x16 Bool.true)) →     (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x11 : Fin x2), Fintype.card { x12 : Fin x2 // x3 x12 x11 } = x1 + (1 : ℕ)) → (∀ (x12 x13 : Fin x2), x12 ≠ x13 → ∃! x15 : Fin x2, x3 x12 x15 ∧ x3 x13 x15) → (3 : ℕ) * x2 ≤ x5 + (1 : ℕ) → x6 < x2 + x2 + x5 → (∀ (x15 : Fin (x2 + x2)), x7 ↑x15 = {{x15}}) → (∀ x16 < x5, ∃ (x18 : ℕ) (x19 : ℕ), x18 < x19 ∧ x19 < x2 + x2 + x16 ∧ (x7 (x2 + x2 + x16) = x7 x18 ∪ x7 x19 ∨ x7 (x2 + x2 + x16) = (x7 x18).biUnion fun (x20 : Finset (Fin (x2 + x2))) => Finset.image (fun (x21 : Finset (Fin (x2 + x2))) => x20 ∪ x21) (x7 x19))) → (∀ x17 ∈ x7 x6, ∀ (x19 x20 : Fin x2), x3 x19 x20 → Fin.castAdd x2 x19 ∈ x17 ∨ Fin.natAdd x2 x20 ∈ x17) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ x20 ∈ x7 x6, (∀ (x21 : Fin x2), Fin.castAdd x2 x21 ∈ x20 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ ∀ (x21 : Fin x2), Fin.natAdd x2 x21 ∈ x20 ↔ x21 ∉ x18) → x2 * x1 ≤ (100 : ℕ) * x5 := by
  classical
  intro q n I dec s o F _ hq hn deg unique size addr raw gates cover witness
  let m := fun (T : Finset (Finset (Fin (n+n)))) => T.filter (fun C => ∀ D ∈ T, D ⊆ C → C ⊆ D)
  let G := fun j => m (F j)
  apply bound q n I s o G hq hn deg unique size addr
  · intro i
    simp [G, m, raw i]
  · intro j hj
    obtain ⟨a,b,hab,hb,h⟩ := gates j hj
    refine ⟨a,b,hab,hb,?_⟩
    rcases h with h | h
    · exact Or.inl ((congrArg m h).trans (absorb (n+n) (F a) (F b)).1)
    · exact Or.inr ((congrArg m h).trans (absorb (n+n) (F a) (F b)).2)
  · intro C hc
    exact cover C (Finset.mem_filter.mp hc).1
  · intro S hs
    obtain ⟨C,hC,points,lines⟩ := witness S hs
    refine ⟨C, Finset.mem_filter.mpr ⟨hC, ?_⟩, points, lines⟩
    intro D hD sub i
    refine Fin.addCases (motive := fun i => i ∈ C → i ∈ D) ?_ ?_ i
    · intro p hp
      obtain ⟨l,hl,hpl⟩ := (points p).mp hp
      exact (cover D hD p l hpl).resolve_right (fun h => (lines l).mp (sub h) hl)
    · intro l hl
      have outside := (lines l).mp hl
      have privatePoint : ∃ p, I p l ∧ ∀ k ∈ S, ¬ I p k := by
        by_contra! h
        have picks (p : {p // I p l}) : ∃ k ∈ S, I p.1 k := h p.1 p.2
        let f (p : {p // I p l}) : ↥S := ⟨(picks p).choose, (picks p).choose_spec.1⟩
        have inj : Function.Injective f := by
          intro p t he
          apply Subtype.ext
          by_contra hn
          obtain ⟨k, _, only⟩ := unique p.1 t.1 hn
          have eq1 := only l ⟨p.2,t.2⟩
          have hf : (f p).1 = (f t).1 := congrArg Subtype.val he
          have ht : I t.1 (f p).1 := hf ▸ (picks t).choose_spec.2
          have eq2 := only (f p).1 ⟨(picks p).choose_spec.2,ht⟩
          exact outside ((eq1.trans eq2.symm) ▸ (f p).2)
        have bound := Fintype.card_le_of_injective f inj
        rw [deg, Fintype.card_coe] at bound
        omega
      obtain ⟨p,inc,avoid⟩ := privatePoint
      apply (cover D hD p l inc).resolve_left
      intro hp
      obtain ⟨k,hk,hpk⟩ := (points p).mp (sub hp)
      exact avoid k hk hpk
