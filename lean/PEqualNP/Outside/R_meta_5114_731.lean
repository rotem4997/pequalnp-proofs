import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5114_731
    (strip : ∀ (n m : ℕ) (A : Finset (Fin n)) (F : (Fin n → Bool) → Bool)
        (r : Fin n → Fin m) (s : ℕ),
        (∃ x y, F x = false ∧ F y = true) →
        (∀ x y, (∀ i ∉ A, x i = y i) → F x = F y) →
        HasCircuitSize n (fun x => decide (∃ a ∈ A, x a = true) || F x) s →
        ∃ k, k + A.card ≤ s ∧ HasCircuitSize m (fun y => F (fun i => y (r i))) k)
    (cubicCore : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (F : (Fin n → Bool) → Bool),
        G.Colorable 2 →
        (∀ v, (G.neighborSet v).ncard = 3) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∃ i j, G.Adj i j) →
        (∀ x, F x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
        ∀ s, HasCircuitSize n F s → 2 * n ≤ s + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → x3.card + x2.edgeSet.ncard + (Finset.univ \ x3).card / (2 : ℕ) ≤ x11 + (1 : ℕ) := by
  intro n G A f color degree girth isolated edge spec s size
  classical
  let E (x : Fin n → Bool) := decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
  have eqF : f = fun x => decide (∃ a ∈ A, x a = true) || E x := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.or_eq_true, E, decide_eq_true_eq] using spec x
  obtain ⟨a, b, ab⟩ := edge
  let U := {v : Fin n // v ∉ A}
  let m := Fintype.card U
  let emb : Fin m ↪ Fin n :=
    ⟨fun v => ((Fintype.equivFin U).symm v).val,
      fun _ _ h => (Fintype.equivFin U).symm.injective (Subtype.ext h)⟩
  let back (i : Fin n) : Fin m :=
    if hi : i ∉ A then Fintype.equivFin U ⟨i, hi⟩ else Fintype.equivFin U ⟨a, isolated a b ab⟩
  have inU (v : Fin m) : emb v ∉ A := ((Fintype.equivFin U).symm v).property
  have sectionBack (v : Fin m) : back (emb v) = v := by
    simp only [back, dite_eq_left (inU v)]
    exact (Fintype.equivFin U).apply_symm_apply v
  have sectionEmb (i : Fin n) (hi : i ∉ A) : emb (back i) = i := by
    change ((Fintype.equivFin U).symm (back i)).val = i
    simp [back, hi]
  let H : SimpleGraph (Fin m) := G.comap emb
  let hom : H →g G := ⟨emb, fun h => h⟩
  have degH (v : Fin m) : (H.neighborSet v).ncard = 3 := by
    rw [← degree (emb v) (inU v)]
    apply Set.ncard_congr (fun q _ => emb q) (fun _ h => h)
      (fun _ _ _ _ h => emb.injective h)
    intro z hz
    change G.Adj (emb v) z at hz
    have rev := sectionEmb z (isolated _ _ hz.symm)
    refine ⟨back z, ?_, rev⟩
    change G.Adj (emb v) (emb (back z))
    rwa [rev]
  have girthH (v : Fin m) (w : H.Walk v v) (cycle : w.IsCycle) : 7 ≤ w.length := by
    have injective : Function.Injective hom := emb.injective
    simpa using girth (emb v) (w.map hom) (cycle.map injective)
  have edgeH : ∃ i j, H.Adj i j := by
    refine ⟨back a, back b, ?_⟩
    change G.Adj (emb (back a)) (emb (back b))
    rwa [sectionEmb _ (isolated _ _ ab), sectionEmb _ (isolated _ _ ab.symm)]
  let pure (y : Fin m → Bool) := E (fun i => y (back i))
  have pureSpec (y : Fin m → Bool) :
      pure y = true ↔ ∃ i j, H.Adj i j ∧ y i = true ∧ y j = true := by
    simp only [pure, E, decide_eq_true_eq]
    constructor
    · rintro ⟨i, j, ij, onI, onJ⟩
      refine ⟨back i, back j, ?_, onI, onJ⟩
      change G.Adj (emb (back i)) (emb (back j))
      rwa [sectionEmb _ (isolated _ _ ij), sectionEmb _ (isolated _ _ ij.symm)]
    · rintro ⟨i, j, ij, onI, onJ⟩
      exact ⟨emb i, emb j, ij, by rwa [sectionBack], by rwa [sectionBack]⟩
  have some : E (fun _ => true) = true := by
    exact decide_eq_true ⟨a, b, ab, rfl, rfl⟩
  have none : E (fun _ => false) = false := by simp [E]
  have independent (x y : Fin n → Bool) (agree : ∀ i ∉ A, x i = y i) : E x = E y := by
    apply Bool.eq_iff_iff.mpr
    simp only [E, decide_eq_true_eq]
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    apply and_congr_right
    intro ij
    rw [agree i (isolated i j ij), agree j (isolated j i ij.symm)]
  have withOr := eqF ▸ size
  obtain ⟨k, budget, model⟩ := strip n m A E back s ⟨_, _, none, some⟩ independent withOr
  have main := cubicCore m H pure (SimpleGraph.Colorable.of_hom hom color)
    degH girthH edgeH pureSpec k model
  letI : DecidableRel G.Adj := Classical.decRel _
  have inside : ∀ i ∈ A, G.degree i = 0 := by
    intro i hi
    exact (G.degree_eq_zero i).2 (fun j ij => isolated i j ij hi)
  have outside : ∀ i ∈ Aᶜ, G.degree i = 3 := by
    intro i hi
    rw [← G.ncard_neighborSet]
    exact degree i (Finset.mem_compl.1 hi)
  have sum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl inside, Finset.sum_congr rfl outside] at sum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at sum
  have edgeCount : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have cards : m = (Finset.univ \ A).card := by
    change Fintype.card {v : Fin n // v ∉ A} = _
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  have compl : Aᶜ = Finset.univ \ A := by ext v; simp
  rw [compl, ← cards, ← edgeCount] at sum
  omega
