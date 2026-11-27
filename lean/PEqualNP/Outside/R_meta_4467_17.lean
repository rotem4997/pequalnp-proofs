import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4467_17
    (compile : ∀ (n s o : ℕ) (F : ℕ → Finset (Finset (Fin n)))
      (E D : Type) (X : E → Fin n → Prop) (Y : D → Fin n → Prop),
      (∀ i : Fin n, F i = {{i}}) →
      (∀ j < s, ∃ a b, a < b ∧ b < n+j ∧
        (F (n+j) = F a ∪ F b ∨ F (n+j) = (F a).biUnion (fun u => (F b).image (u ∪ ·)))) →
      (∀ e, ∀ t ∈ F o, ∃ i ∈ t, X e i) →
      (∀ d, ∃ t ∈ F o, ∀ i ∈ t, Y d i) →
      ∃ (A : ℕ → Set E) (B : ℕ → Set D),
        (∀ i : Fin n, A i = {e | X e i} ∧ B i = {d | Y d i}) ∧
        (∀ j < s, ∃ a b, a < b ∧ b < n+j ∧
          (A (n+j)) ×ˢ (B (n+j)) ⊆ (A a) ×ˢ (B a) ∪ (A b) ×ˢ (B b)) ∧
        A o = Set.univ ∧ B o = Set.univ)
    (lower : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      300 ≤ q → n = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ)
        (A : ℕ → Set (Fin n × Fin n)) (B : ℕ → Set (Finset (Fin n))),
      3*n ≤ s+1 → o < n+n+s →
      (∀ t : Fin (n+n), ∀ e ∈ A t, ∀ S ∈ B t,
        (t = Fin.castAdd n e.1 ∧ ∃ l ∈ S, I e.1 l) ∨
        (t = Fin.natAdd n e.2 ∧ e.2 ∉ S)) →
      (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧
        ∀ e ∈ A (n+n+j), ∀ S ∈ B (n+n+j), (e ∈ A a ∧ S ∈ B a) ∨ (e ∈ A b ∧ S ∈ B b)) →
      (∀ p l, I p l → (p,l) ∈ A o) → (∀ S : Finset (Fin n), S.card ≤ q → S ∈ B o) →
      n*q ≤ 100*s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 x6 : ℕ) (x7 : ℕ → Finset (Finset (Fin (x2 + x2)))),   (∃ x8 < x5,       ∃ (x9 : ℕ) (x10 : ℕ),         x9 < x10 ∧           x10 < x2 + x2 + x8 ∧             x7 (x2 + x2 + x8) = x7 x9 ∪ x7 x10 ∧               ∃ (x11 : Bool),                 ∀ x12 ∈ [x9, x10],                   ∃ (x14 : Fin x2 → Bool),                     have x15 : Bool → List Bool := fun (x15 : Bool) => if x11 = Bool.true then List.ofFn x14 ++ List.replicate x2 x15 else List.replicate x2 x15 ++ List.ofFn x14;                     have x16 : Bool → Prop := fun (x16 : Bool) => ∀ x17 ∈ x7 x12, ∃ x19 ∈ x17, (x15 x16).getD (↑x19) Bool.false = Bool.true;                     ¬(x16 Bool.false ↔ x16 Bool.true)) →     (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x11 : Fin x2), Fintype.card { x12 : Fin x2 // x3 x12 x11 } = x1 + (1 : ℕ)) → (∀ (x12 x13 : Fin x2), x12 ≠ x13 → ∃! x15 : Fin x2, x3 x12 x15 ∧ x3 x13 x15) → (3 : ℕ) * x2 ≤ x5 + (1 : ℕ) → x6 < x2 + x2 + x5 → (∀ (x15 : Fin (x2 + x2)), x7 ↑x15 = {{x15}}) → (∀ x16 < x5, ∃ (x18 : ℕ) (x19 : ℕ), x18 < x19 ∧ x19 < x2 + x2 + x16 ∧ (x7 (x2 + x2 + x16) = x7 x18 ∪ x7 x19 ∨ x7 (x2 + x2 + x16) = (x7 x18).biUnion fun (x20 : Finset (Fin (x2 + x2))) => Finset.image (fun (x21 : Finset (Fin (x2 + x2))) => x20 ∪ x21) (x7 x19))) → (∀ x17 ∈ x7 x6, ∀ (x19 x20 : Fin x2), x3 x19 x20 → Fin.castAdd x2 x19 ∈ x17 ∨ Fin.natAdd x2 x20 ∈ x17) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ x20 ∈ x7 x6, (∀ (x21 : Fin x2), Fin.castAdd x2 x21 ∈ x20 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ ∀ (x21 : Fin x2), Fin.natAdd x2 x21 ∈ x20 ↔ x21 ∉ x18) → x2 * x1 ≤ (100 : ℕ) * x5 := by
  intro q n I inst s o F _ hq hn degree unique hsize ho raw gates cover witness
  classical
  let E := {e : Fin n × Fin n // I e.1 e.2}
  let D := {S : Finset (Fin n) // S.card ≤ q}
  let X (e : E) (i : Fin (n+n)) := i = Fin.castAdd n e.val.1 ∨ i = Fin.natAdd n e.val.2
  let Y (S : D) : Fin (n+n) → Prop := Fin.addCases
    (fun p => ∃ l ∈ S.val, I p l) (fun l => l ∉ S.val)
  have pos (e : E) (t) (ht : t ∈ F o) : ∃ i ∈ t, X e i := by
    rcases cover t ht e.val.1 e.val.2 e.property with h | h
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  have neg (S : D) : ∃ t ∈ F o, ∀ i ∈ t, Y S i := by
    obtain ⟨t, ht, hp, hl⟩ := witness S.val S.property
    refine ⟨t, ht, ?_⟩
    intro i
    refine Fin.addCases (fun p h => ?_) (fun l h => ?_) i
    · simpa only [Y, Fin.addCases_left] using (hp p).1 h
    · simpa only [Y, Fin.addCases_right] using (hl l).1 h
  obtain ⟨A, B, atoms, steps, topA, topB⟩ := compile (n+n) s o F E D X Y raw gates pos neg
  let rows (w : ℕ) : Set (Fin n × Fin n) := {e | ∃ h : I e.1 e.2, (⟨e,h⟩ : E) ∈ A w}
  let cols (w : ℕ) : Set (Finset (Fin n)) := {S | ∃ h : S.card ≤ q, (⟨S,h⟩ : D) ∈ B w}
  refine lower q n I hq hn degree unique s o rows cols hsize ho ?_ ?_ ?_ ?_
  · rintro t e ⟨hei,he⟩ S ⟨hSmall,hS⟩
    rw [(atoms t).1] at he
    rw [(atoms t).2] at hS
    change X ⟨e,hei⟩ t at he
    change Y ⟨S,hSmall⟩ t at hS
    rcases he with rfl | rfl
    · exact Or.inl ⟨rfl, by simpa only [Y, Fin.addCases_left] using hS⟩
    · exact Or.inr ⟨rfl, by simpa only [Y, Fin.addCases_right] using hS⟩
  · intro j hj
    obtain ⟨a,b,hab,hb,sub⟩ := steps j hj
    refine ⟨a,b,hab,hb,?_⟩
    rintro e ⟨hei,he⟩ S ⟨hSmall,hS⟩
    have hc : ((⟨e,hei⟩ : E), (⟨S,hSmall⟩ : D)) ∈
        (A a) ×ˢ (B a) ∪ (A b) ×ˢ (B b) := sub ⟨he,hS⟩
    rcases hc with h | h
    · exact Or.inl ⟨⟨hei,h.1⟩, ⟨hSmall,h.2⟩⟩
    · exact Or.inr ⟨⟨hei,h.1⟩, ⟨hSmall,h.2⟩⟩
  · intro p l hi
    exact ⟨hi, topA.symm ▸ Set.mem_univ _⟩
  · intro S hS
    exact ⟨hS, topB.symm ▸ Set.mem_univ _⟩
