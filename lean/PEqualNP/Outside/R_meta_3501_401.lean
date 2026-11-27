import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3501_401
    (product_rule : ∀ (d : ℕ) (U V : Finset (Finset (Fin d))) (P : Fin d → Prop),
      (∀ t ∈ U.biUnion (fun u => V.image (u ∪ ·)), ∃ i ∈ t, P i) ↔
      (∀ t ∈ U, ∃ i ∈ t, P i) ∨ (∀ t ∈ V, ∃ i ∈ t, P i))
    (rectangle_bound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      250 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (R : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n))),
      let box := fun w => (R w).1 ×ˢ (R w).2
      o < n+n+s →
      (∀ (i : Fin (n+n)) p l T, ((p,l),T) ∈ box i →
        (i = Fin.castAdd n p ∧ ∃ t ∈ T, I p t) ∨ (i = Fin.natAdd n l ∧ l ∉ T)) →
      (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧ box (n+n+j) ⊆ box a ∪ box b) →
      {e | I e.1 e.2} ×ˢ {T | T.card ≤ q} ⊆ box o → n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Finset (Finset (Fin (x2 + x2)))),             x10 < x2 + x2 + x9 →               (∀ (x13 : Fin (x2 + x2)), x11 ↑x13 = {{x13}}) →                 (∀ x14 < x9, ∃ (x16 : ℕ) (x17 : ℕ), x16 < x17 ∧ x17 < x2 + x2 + x14 ∧ (x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∨ x11 (x2 + x2 + x14) = (x11 x16).biUnion fun (x18 : Finset (Fin (x2 + x2))) => Finset.image (fun (x19 : Finset (Fin (x2 + x2))) => x18 ∪ x19) (x11 x17))) →                   (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → Fin.castAdd x2 x17 ∈ x15 ∨ Fin.natAdd x2 x18 ∈ x15) →                     (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, (∀ (x19 : Fin x2), Fin.castAdd x2 x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ ∀ (x19 : Fin x2), Fin.natAdd x2 x19 ∈ x18 ↔ x19 ∉ x16) →                       (∃ x17 < x9,                           ∃ (x18 : ℕ) (x19 : ℕ),                             x18 < x19 ∧                               x19 < x2 + x2 + x17 ∧                                 x11 (x2 + x2 + x17) = x11 x18 ∪ x11 x19 ∧                                   ∃ (x20 : Bool),                                     ∀ x21 ∈ [x18, x19],                                       ∃ (x23 : Fin x2 → Bool),                                         have x24 : Bool → List Bool := fun (x24 : Bool) => if x20 = Bool.true then List.ofFn x23 ++ List.replicate x2 x24 else List.replicate x2 x24 ++ List.ofFn x23;                                         have x25 : Bool → Prop := fun (x25 : Bool) => ∀ x26 ∈ x11 x21, ∃ x28 ∈ x26, (x24 x25).getD (↑x28) Bool.false = Bool.true;                                         ¬(x25 Bool.false ↔ x25 Bool.true)) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q n I inst hq hn degree uniqueLine s o F ho leaves gates cover witness _
  let separates (w : ℕ) (P : Fin (n+n) → Prop) := ∀ t ∈ F w, ∃ i ∈ t, P i
  let pos (e : Fin n × Fin n) (i : Fin (n+n)) :=
    i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2
  let neg (T : Finset (Fin n)) (i : Fin (n+n)) :=
    (∃ p, i = Fin.castAdd n p ∧ ¬ ∃ l ∈ T, I p l) ∨
    ∃ l, i = Fin.natAdd n l ∧ l ∈ T
  let R (w : ℕ) : Set (Fin n × Fin n) × Set (Finset (Fin n)) :=
    ( {e | separates w (pos e)}, {T | ¬ separates w (neg T)} )
  apply rectangle_bound q n I hq hn degree uniqueLine s o R ho
  · intro i p l T cell
    change separates i (pos (p,l)) ∧ ¬ separates i (neg T) at cell
    have raw (P : Fin (n+n) → Prop) : separates i P ↔ P i := by simp [separates, leaves]
    obtain ⟨edge, blocked⟩ := cell
    rw [raw] at edge blocked
    rcases edge with hp | hl
    · left
      refine ⟨hp, ?_⟩
      by_contra h
      exact blocked (Or.inl ⟨p, hp, h⟩)
    · exact Or.inr ⟨hl, fun h => blocked (Or.inr ⟨l, hl, h⟩)⟩
  · intro j hj
    obtain ⟨a,b,hab,hb,op⟩ := gates j hj
    refine ⟨a,b,hab,hb,?_⟩
    rintro ⟨e,T⟩ cell
    change separates (n+n+j) (pos e) ∧ ¬ separates (n+n+j) (neg T) at cell
    change (separates a (pos e) ∧ ¬ separates a (neg T)) ∨
      (separates b (pos e) ∧ ¬ separates b (neg T))
    rcases op with union | prod
    · have step (P : Fin (n+n) → Prop) :
          separates (n+n+j) P ↔ separates a P ∧ separates b P := by
        simp only [separates, union, Finset.mem_union]
        constructor
        · intro h
          exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
        · rintro ⟨ha,hb'⟩ t (ht|ht)
          · exact ha t ht
          · exact hb' t ht
      rw [step,step] at cell
      tauto
    · have step (P : Fin (n+n) → Prop) :
          separates (n+n+j) P ↔ separates a P ∨ separates b P := by
        unfold separates
        rw [prod]
        exact product_rule _ _ _ P
      rw [step,step] at cell
      tauto
  · rintro ⟨⟨p,l⟩,T⟩ ⟨edge,small⟩
    constructor
    · intro t ht
      rcases cover t ht p l edge with hp | hl
      · exact ⟨_,hp,Or.inl rfl⟩
      · exact ⟨_,hl,Or.inr rfl⟩
    · intro all
      obtain ⟨t,ht,points,lines⟩ := witness T small
      obtain ⟨i,hi,hit⟩ := all t ht
      rcases hit with ⟨u,rfl,hu⟩ | ⟨v,rfl,hv⟩
      · exact hu ((points u).mp hi)
      · exact (lines v).mp hi hv
