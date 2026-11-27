import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3501_41
    (gateCover : ∀ (m : ℕ) (A B C : Finset (Finset (Fin m))) (x y : Set (Fin m)),
      let both := fun D : Finset (Finset (Fin m)) =>
        (∀ u ∈ D, ∃ i ∈ u, i ∈ x) ∧ (∃ u ∈ D, ∀ i ∈ u, i ∈ y)
      (C = A ∪ B ∨ C = A.biUnion fun u => B.image (u ∪ ·)) →
        both C → both A ∨ both B)
    (rectangleBound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      250 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (X : ℕ → Set (Fin n × Fin n)) (Y : ℕ → Set (Finset (Fin n))),
        let R := fun w => Set.prod (X w) (Y w)
        o < n+n+s →
        (∀ (i : Fin (n+n)) e T, (e,T) ∈ R i →
          (i = Fin.castAdd n e.1 ∧ ∃ k ∈ T, I e.1 k) ∨ (i = Fin.natAdd n e.2 ∧ e.2 ∉ T)) →
        (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧ R (n+n+j) ⊆ R a ∪ R b) →
        (∀ p l, I p l → ∀ T : Finset (Fin n), T.card ≤ q → ((p,l),T) ∈ R o) →
        n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Finset (Finset (Fin (x2 + x2)))),             x10 < x2 + x2 + x9 →               (∀ (x13 : Fin (x2 + x2)), x11 ↑x13 = {{x13}}) →                 (∀ x14 < x9, ∃ (x16 : ℕ) (x17 : ℕ), x16 < x17 ∧ x17 < x2 + x2 + x14 ∧ (x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∨ x11 (x2 + x2 + x14) = (x11 x16).biUnion fun (x18 : Finset (Fin (x2 + x2))) => Finset.image (fun (x19 : Finset (Fin (x2 + x2))) => x18 ∪ x19) (x11 x17))) →                   (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → Fin.castAdd x2 x17 ∈ x15 ∨ Fin.natAdd x2 x18 ∈ x15) →                     (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, (∀ (x19 : Fin x2), Fin.castAdd x2 x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ ∀ (x19 : Fin x2), Fin.natAdd x2 x19 ∈ x18 ↔ x19 ∉ x16) →                       (∃ x17 < x9,                           ∃ (x18 : ℕ) (x19 : ℕ),                             x18 < x19 ∧                               x19 < x2 + x2 + x17 ∧                                 x11 (x2 + x2 + x17) = x11 x18 ∪ x11 x19 ∧                                   ∃ (x20 : Bool),                                     ∀ x21 ∈ [x18, x19],                                       ∃ (x23 : Fin x2 → Bool),                                         have x24 : Bool → List Bool := fun (x24 : Bool) => if x20 = Bool.true then List.ofFn x23 ++ List.replicate x2 x24 else List.replicate x2 x24 ++ List.ofFn x23;                                         have x25 : Bool → Prop := fun (x25 : Bool) => ∀ x26 ∈ x11 x21, ∃ x28 ∈ x26, (x24 x25).getD (↑x28) Bool.false = Bool.true;                                         ¬(x25 Bool.false ↔ x25 Bool.true)) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q n I dec hq hn degree uniqueLine s o F ho inputs gates cover complete _
  classical
  let row (e : Fin n × Fin n) : Set (Fin (n+n)) :=
    {Fin.castAdd n e.1, Fin.natAdd n e.2}
  have chooseCover (T : Finset (Fin n)) : ∃ u : Finset (Fin (n+n)), T.card ≤ q →
      u ∈ F o ∧ (∀ p, Fin.castAdd n p ∈ u ↔ ∃ k ∈ T, I p k) ∧
        (∀ l, Fin.natAdd n l ∈ u ↔ l ∉ T) := by
    by_cases h : T.card ≤ q
    · obtain ⟨u, hu⟩ := complete T h
      exact ⟨u, fun _ => hu⟩
    · exact ⟨∅, fun ht => (h ht).elim⟩
  choose col hcol using chooseCover
  let X (w : ℕ) : Set (Fin n × Fin n) :=
    {e | ∀ u ∈ F w, ∃ i ∈ u, i ∈ row e}
  let Y (w : ℕ) : Set (Finset (Fin n)) :=
    {T | T.card ≤ q ∧ ∃ u ∈ F w, ∀ i ∈ u, i ∈ col T}
  refine rectangleBound q n I hq hn degree uniqueLine s o X Y ho ?_ ?_ ?_
  · intro i e T h
    obtain ⟨hx, small, u, hu, sub⟩ := h
    change ∀ v ∈ F i.val, ∃ z ∈ v, z ∈ row e at hx
    rw [inputs i] at hx hu
    obtain ⟨z,hz,pos⟩ := hx {i} (Finset.mem_singleton_self _)
    have hz' : z = i := Finset.mem_singleton.mp hz
    subst z
    have hu' : u = {i} := Finset.mem_singleton.mp hu
    subst u
    have neg := sub i (Finset.mem_singleton_self i)
    obtain ⟨_,points,lines⟩ := hcol T small
    change i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2 at pos
    rcases pos with hp | hl
    · subst i
      exact Or.inl ⟨rfl, (points e.1).mp neg⟩
    · subst i
      exact Or.inr ⟨rfl, (lines e.2).mp neg⟩
  · intro j hj
    obtain ⟨a,b,hab,hbj,op⟩ := gates j hj
    refine ⟨a,b,hab,hbj,?_⟩
    rintro ⟨e,T⟩ ⟨hx,small,hy⟩
    rcases gateCover (n+n) (F a) (F b) (F (n+n+j)) (row e)
        (col T : Set (Fin (n+n))) op ⟨hx,hy⟩ with h | h
    · exact Or.inl ⟨h.1,small,h.2⟩
    · exact Or.inr ⟨h.1,small,h.2⟩
  · intro p l inc T small
    refine ⟨?_,small,col T,(hcol T small).1,fun _ hi => hi⟩
    intro u hu
    rcases cover u hu p l inc with hp | hl
    · exact ⟨_, hp, by simp [row]⟩
    · exact ⟨_, hl, by simp [row]⟩
