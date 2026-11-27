import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5108_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (s : ℕ),
      (A.Nonempty ∨ ∃ a b : Fin n, G.Adj a b) →
      (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
      s + 1 = A.card + G.edgeSet.ncard + T.card →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (s : ℕ),
      (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n) (Z : Finset ℕ),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) → G.Adj u v →
        (∀ j ∈ Z, j < C.size ∧ ∃ p : ℕ, (p < n + j ∨ n + C.size ≤ p) ∧ ∀ x : Fin n → Bool,
          have w : List Bool := C.wires (List.ofFn (Function.update (Function.update x u false) v false));
          w.getD (n + j) false = w.getD p false) →
        Z.card < 7) →
      ¬G.Colorable 2 → (∀ a ∉ A, (G.neighborSet a).ncard = 3) →
      (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) →
      (∀ a b : Fin n, G.Adj a b → a ∉ A) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s → (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → s ≤ t) →
      (∀ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
        s + 1 < A.card + G.edgeSet.ncard + T.card) →
      ∃ u v : Fin n, G.Adj u v ∧ ∃ t : ℕ, t + 7 ≤ s ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update (Function.update x u false) v false)) t) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →               ∀ (x11 : ℕ),                 PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 →                   (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo x13 →                         x13.size ≤ x11 →                           (∀ (x16 : Fin x1 → Bool), x13.eval (List.ofFn x16) = x4 x16) →                             ∀ (x17 x18 : Fin x1),                               x2.Adj x17 x18 →                                 ∀ (x20 : Finset ℕ),                                   (∀ x21 ∈ x20, x21 < x13.size) →                                     (∀ x22 ∈ x20,                                         ∃ (x24 : ℕ),                                           (x24 < x1 + x22 ∨ x1 + x13.size ≤ x24) ∧                                             ∀ (x25 : Fin x1 → Bool),                                               have x26 : List Bool := x13.wires (List.ofFn (Function.update (Function.update x25 x17 Bool.false) x18 Bool.false));                                               x26.getD (x1 + x22) Bool.false = x26.getD x24 Bool.false) →                                       x20.card < (7 : ℕ)) →                     ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ∉ x3 ∧ x15 ∉ x3 ∧ x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  classical
  intro n G A f hnon hdeg hgirth hiso hedge hfun s hsize H
  have hex : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n f t := ⟨s, hsize⟩
  obtain ⟨m, hm, hmin⟩ : ∃ m, PEqualNP.MetaComplexity.HasCircuitSize n f m ∧
      ∀ t, PEqualNP.MetaComplexity.HasCircuitSize n f t → m ≤ t :=
    ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min' hex ht⟩
  have hms : m ≤ s := hmin s hsize
  by_cases hstar : ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧
      A.card + G.edgeSet.ncard + T.card ≤ m + 1
  · obtain ⟨T, hT, hcard⟩ := hstar
    have hin : ∃ u v, G.Adj u v ∧ u ∈ T ∧ v ∈ T := by
      by_contra hno
      push Not at hno
      apply hnon
      refine ⟨SimpleGraph.Coloring.mk (fun a => if a ∈ T then (0 : Fin 2) else 1) ?_⟩
      intro a b hab
      by_cases ha : a ∈ T
      · have hb : b ∉ T := hno a b hab ha
        simp [ha, hb]
      · have hb : b ∈ T := (hT a b hab).resolve_left ha
        simp [ha, hb]
    obtain ⟨u, v, huv, huT, hvT⟩ := hin
    have hne : u ≠ v := huv.ne
    have huA : u ∉ A := hiso u v huv
    have hvA : v ∉ A := hiso v u huv.symm
    let G' : SimpleGraph (Fin n) :=
      { Adj := fun a b => G.Adj a b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v
        symm := ⟨fun a b h => ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩⟩
        loopless := ⟨fun a h => G.irrefl h.1⟩ }
    have hAdj : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v :=
      fun a b => Iff.rfl
    have hspec : ∀ x : Fin n → Bool,
        f (Function.update (Function.update x u false) v false) = true ↔
          (∃ a ∈ A, x a = true) ∨ ∃ a b : Fin n, G'.Adj a b ∧ x a = true ∧ x b = true := by
      intro x
      have key : ∀ a : Fin n, Function.update (Function.update x u false) v false a = true ↔
          (x a = true ∧ a ≠ u ∧ a ≠ v) := by
        intro a
        by_cases hav : a = v
        · subst hav
          simp
        · by_cases hau : a = u
          · subst hau
            simp [Function.update_of_ne hav]
          · simp [hav, hau]
      rw [hfun]
      constructor
      · rintro (⟨a, ha, hx⟩ | ⟨a, b, hab, hxa, hxb⟩)
        · exact Or.inl ⟨a, ha, ((key a).1 hx).1⟩
        · obtain ⟨ka, kau, kav⟩ := (key a).1 hxa
          obtain ⟨kb, kbu, kbv⟩ := (key b).1 hxb
          exact Or.inr ⟨a, b, ⟨hab, kau, kav, kbu, kbv⟩, ka, kb⟩
      · rintro (⟨a, ha, hx⟩ | ⟨a, b, ⟨hab, k1, k2, k3, k4⟩, hxa, hxb⟩)
        · exact Or.inl ⟨a, ha, (key a).2 ⟨hx, fun e => huA (e ▸ ha), fun e => hvA (e ▸ ha)⟩⟩
        · exact Or.inr ⟨a, b, hab, (key a).2 ⟨hxa, k1, k2⟩, (key b).2 ⟨hxb, k3, k4⟩⟩
    have hcover : ∀ a b : Fin n, G'.Adj a b → a ∈ (T.erase u).erase v ∨ b ∈ (T.erase u).erase v := by
      rintro a b ⟨hab, k1, k2, k3, k4⟩
      rcases hT a b hab with h | h
      · exact Or.inl (Finset.mem_erase.2 ⟨k2, Finset.mem_erase.2 ⟨k1, h⟩⟩)
      · exact Or.inr (Finset.mem_erase.2 ⟨k4, Finset.mem_erase.2 ⟨k3, h⟩⟩)
    have hTc : ((T.erase u).erase v).card + 2 = T.card := by
      have e1 := Finset.card_erase_add_one huT
      have e2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨hne.symm, hvT⟩ : v ∈ T.erase u)
      omega
    have two : ∀ p q : Fin n, G.Adj p q → p ∉ A →
        ∃ a b : Fin n, a ≠ b ∧ G.Adj p a ∧ G.Adj p b ∧ a ≠ q ∧ b ≠ q := by
      intro p q hpq hp
      have h3 := hdeg p hp
      have h2 : (G.neighborSet p \ {q}).ncard = 2 := by
        rw [Set.ncard_sdiff_singleton_of_mem (show q ∈ G.neighborSet p from hpq), h3]
      obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.1 h2
      have ha : a ∈ G.neighborSet p \ {q} := by rw [hset]; simp
      have hb : b ∈ G.neighborSet p \ {q} := by rw [hset]; simp
      exact ⟨a, b, hab, ha.1, hb.1, ha.2, hb.2⟩
    obtain ⟨a, b, hab, hua, hub, hav, hbv⟩ := two u v huv huA
    obtain ⟨c, d, hcd, hvc, hvd, hcu, hdu⟩ := two v u huv.symm hvA
    have hau : a ≠ u := hua.ne'
    have hbu : b ≠ u := hub.ne'
    have hcv : c ≠ v := hvc.ne'
    have hdv : d ≠ v := hvd.ne'
    have hE : G'.edgeSet.ncard + 5 ≤ G.edgeSet.ncard := by
      let F : Finset (Sym2 (Fin n)) := {s(u, v), s(u, a), s(u, b), s(v, c), s(v, d)}
      have hF : F.card = 5 := by
        have n1 : s(u, v) ∉ ({s(u, a), s(u, b), s(v, c), s(v, d)} : Finset (Sym2 (Fin n))) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
          tauto
        have n2 : s(u, a) ∉ ({s(u, b), s(v, c), s(v, d)} : Finset (Sym2 (Fin n))) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
          tauto
        have n3 : s(u, b) ∉ ({s(v, c), s(v, d)} : Finset (Sym2 (Fin n))) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
          tauto
        have n4 : s(v, c) ∉ ({s(v, d)} : Finset (Sym2 (Fin n))) := by
          simp only [Finset.mem_singleton, Sym2.eq_iff]
          tauto
        simp only [F]
        rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
          Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_singleton]
      have hFG : ∀ e ∈ F, e ∈ G.edgeSet ∧ e ∉ G'.edgeSet := by
        intro e he
        simp only [F, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl
        · exact ⟨huv, fun h => h.2.1 rfl⟩
        · exact ⟨hua, fun h => h.2.1 rfl⟩
        · exact ⟨hub, fun h => h.2.1 rfl⟩
        · exact ⟨hvc, fun h => h.2.2.1 rfl⟩
        · exact ⟨hvd, fun h => h.2.2.1 rfl⟩
      have hsub : G'.edgeSet ∪ (F : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
        intro e he
        rcases he with he | he
        · induction e using Sym2.ind with
          | _ p q => exact he.1
        · exact (hFG e he).1
      have hdis : Disjoint G'.edgeSet (F : Set (Sym2 (Fin n))) := by
        rw [Set.disjoint_left]
        intro e he heF
        exact (hFG e heF).2 he
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _), Set.ncard_coe_finset, hF] at hle
      exact hle
    by_cases hpos : A.Nonempty ∨ ∃ p q : Fin n, G'.Adj p q
    · have hk : 1 ≤ A.card + G'.edgeSet.ncard + ((T.erase u).erase v).card := by
        rcases hpos with hA | ⟨p, q, hpq⟩
        · have := hA.card_pos
          omega
        · have : 0 < G'.edgeSet.ncard :=
            (Set.ncard_pos (Set.toFinite _)).2 ⟨s(p, q), hpq⟩
          omega
      have hc := h1 n G' A ((T.erase u).erase v)
        (fun x => f (Function.update (Function.update x u false) v false))
        (A.card + G'.edgeSet.ncard + ((T.erase u).erase v).card - 1) hpos hcover (by omega) hspec
      exact ⟨u, v, huA, hvA, huv, _, by omega, hc⟩
    · exfalso
      push Not at hpos
      have haA : a ∉ A := hiso a u hua.symm
      have h3 := hdeg a haA
      have hsub : G.neighborSet a ⊆ ({u, v} : Set (Fin n)) := by
        intro w hw
        by_contra hw2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw2
        exact hpos.2 a w ⟨hw, hau, hav, hw2.1, hw2.2⟩
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair hne] at hle
      omega
  · push Not at hstar
    obtain ⟨u, v, huv, t, ht, hc⟩ := h2 n G A f m
      (fun C u v Z hC hCs hCe huv hZ =>
        H C hC (hCs.trans hms) hCe u v huv Z (fun j hj => (hZ j hj).1) (fun j hj => (hZ j hj).2))
      hnon hdeg hgirth hiso hfun hm hmin (fun T hT => hstar T hT)
    exact ⟨u, v, hiso u v huv, hiso v u huv.symm, huv, t, by omega, hc⟩
