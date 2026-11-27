import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4461_556
    (monotoneCase :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I A B : Finset (Fin n)),
        Disjoint A B → A ∪ B = Finset.univ \ I → A.card = B.card → 3 ≤ A.card →
        (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
        (∀ v ∉ I, (G.neighborSet v).ncard = 3) →
        (∀ v (p : G.Walk v v), p.IsCycle → 8 ≤ p.length) →
        ∀ C : Circuit, IsMinimalCircuit n C → AndOrOnly C →
          circuitFun n C = graphFun G ∅ → C.size + 1 < 4 * A.card →
          ∃ u v : Fin n, u ∉ I ∧ v ∉ I ∧ u ≠ v ∧ ¬ G.Adj u v ∧
            ∃ t : ℕ, t + 8 ≤ C.size ∧
              HasCircuitSize n (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) t)
    (hasNotCase :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I A B : Finset (Fin n)),
        Disjoint A B → A ∪ B = Finset.univ \ I → A.card = B.card → 3 ≤ A.card →
        (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
        (∀ v ∉ I, (G.neighborSet v).ncard = 3) →
        (∀ v (p : G.Walk v v), p.IsCycle → 8 ≤ p.length) →
        ∀ C : Circuit, IsMinimalCircuit n C → (∃ g ∈ C.gates, g.op = GateOp.not) →
          circuitFun n C = graphFun G ∅ → C.size + 1 < 4 * A.card →
          ∃ u v : Fin n, u ∉ I ∧ v ∉ I ∧ u ≠ v ∧ ¬ G.Adj u v ∧
            ∃ t : ℕ, t + 8 ≤ C.size ∧
              HasCircuitSize n (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) t) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x10 → x10 < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x4 ∧ x14 ∉ x4 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15) := by
  classical
  intro n G hdec I hcol hdeg hgirth hnoI hedge s hs hslt
  obtain ⟨col⟩ := hcol
  let A : Finset (Fin n) := Finset.univ.filter fun v => v ∉ I ∧ col v = 0
  let B : Finset (Fin n) := Finset.univ.filter fun v => v ∉ I ∧ col v = 1
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    have h0 : col v = 0 := (Finset.mem_filter.mp hvA).2.2
    have h1 : col v = 1 := (Finset.mem_filter.mp hvB).2.2
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hunion : A ∪ B = Finset.univ \ I := by
    ext v
    simp only [A, B, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      have hc : col v = 0 ∨ col v = 1 := by
        have := (col v).isLt; omega
      rcases hc with h0 | h1
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
  have hbip : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v huv
    have hu : u ∉ I := hnoI u v huv
    have hv : v ∉ I := hnoI v u huv.symm
    have hne : col u ≠ col v := col.valid huv
    have hcu : col u = 0 ∨ col u = 1 := by have := (col u).isLt; omega
    have hcv : col v = 0 ∨ col v = 1 := by have := (col v).isLt; omega
    rcases hcu with hu0 | hu1 <;> rcases hcv with hv0 | hv1
    · exact (hne (hu0.trans hv0.symm)).elim
    · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hu0⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hv1⟩⟩
    · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hu1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hv0⟩⟩
    · exact (hne (hu1.trans hv1.symm)).elim
  have hcard_nbr : ∀ v ∉ I, (Finset.univ.filter fun w => G.Adj v w).card = 3 := by
    intro v hv
    have h3 := hdeg v hv
    have hset : (G.neighborSet v) = ↑(Finset.univ.filter fun w => G.Adj v w) := by
      ext w; simp [SimpleGraph.mem_neighborSet]
    rw [hset, Set.ncard_coe_finset] at h3
    exact h3
  have hAeqB : A.card = B.card := by
    have hsumA : ∑ u ∈ A, (B.filter fun v => G.Adj u v).card = 3 * A.card := by
      have hterm : ∀ u ∈ A, (B.filter fun v => G.Adj u v).card = 3 := by
        intro u huA
        have huI : u ∉ I := (Finset.mem_filter.mp huA).2.1
        have hEq : B.filter (fun v => G.Adj u v) = Finset.univ.filter (fun v => G.Adj u v) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro huv
          rcases hbip u v huv with ⟨_, hvB⟩ | ⟨huB, _⟩
          · exact hvB
          · exact (Finset.disjoint_left.mp hdisj huA huB).elim
        rw [hEq, hcard_nbr u huI]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    have hsumB : ∑ v ∈ B, (A.filter fun u => G.Adj u v).card = 3 * B.card := by
      have hterm : ∀ v ∈ B, (A.filter fun u => G.Adj u v).card = 3 := by
        intro v hvB
        have hvI : v ∉ I := (Finset.mem_filter.mp hvB).2.1
        have hEq : A.filter (fun u => G.Adj u v) = Finset.univ.filter (fun u => G.Adj v u) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; exact h.2.symm
          · intro hvu
            rcases hbip v u hvu with ⟨hvA, _⟩ | ⟨_, huA⟩
            · exact (Finset.disjoint_left.mp hdisj hvA hvB).elim
            · exact ⟨huA, hvu.symm⟩
        rw [hEq, hcard_nbr v hvI]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    have hdouble : ∑ u ∈ A, (B.filter fun v => G.Adj u v).card =
        ∑ v ∈ B, (A.filter fun u => G.Adj u v).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    omega
  have hA3 : 3 ≤ A.card := by
    obtain ⟨u0, v0, huv0⟩ := hedge
    have huA_or_B := hbip u0 v0 huv0
    have hB3 : 3 ≤ B.card := by
      rcases huA_or_B with ⟨huA, _⟩ | ⟨_, hvA⟩
      · have hsub : Finset.univ.filter (fun w => G.Adj u0 w) ⊆ B := by
          intro w hw
          have hadj := (Finset.mem_filter.mp hw).2
          rcases hbip u0 w hadj with ⟨_, hwB⟩ | ⟨huB, _⟩
          · exact hwB
          · exact (Finset.disjoint_left.mp hdisj huA huB).elim
        have := Finset.card_le_card hsub
        rw [hcard_nbr u0 (Finset.mem_filter.mp huA).2.1] at this
        exact this
      · have hsub : Finset.univ.filter (fun w => G.Adj v0 w) ⊆ B := by
          intro w hw
          have hadj := (Finset.mem_filter.mp hw).2
          rcases hbip v0 w hadj with ⟨_, hwB⟩ | ⟨hvB, _⟩
          · exact hwB
          · exact (Finset.disjoint_left.mp hdisj hvA hvB).elim
        have := Finset.card_le_card hsub
        rw [hcard_nbr v0 (Finset.mem_filter.mp hvA).2.1] at this
        exact this
    omega
  have hgirth8 : ∀ v (p : G.Walk v v), p.IsCycle → 8 ≤ p.length := by
    intro v p hp
    have h7 := hgirth v p hp
    have hcol_walk : ∀ {a b : Fin n} (w : G.Walk a b),
        (col a = col b ↔ Even w.length) := by
      intro a b w
      induction w with
      | nil => simp
      | @cons a b c hab w ih =>
        simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one]
        have hne : col a ≠ col b := col.valid hab
        have hca : col a = 0 ∨ col a = 1 := by have := (col a).isLt; omega
        have hcb : col b = 0 ∨ col b = 1 := by have := (col b).isLt; omega
        have hcc : col c = 0 ∨ col c = 1 := by have := (col c).isLt; omega
        rw [← ih]
        rcases hca with ha | ha <;> rcases hcb with hb | hb <;> rcases hcc with hc | hc <;>
          simp [ha, hb, hc] at hne ⊢
    have heven : Even p.length := (hcol_walk p).mp rfl
    obtain ⟨k, hk⟩ := heven
    omega
  have hsumAB : A.card + B.card = n - I.card := by
    have h1 := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hex : ∃ t : ℕ, HasCircuitSize n (graphFun G ∅) t := ⟨s, hs⟩
  obtain ⟨C, hfan, hCbound, hCeval⟩ := Nat.find_spec hex
  have hCs : C.size ≤ s := hCbound.trans (Nat.find_min' hex hs)
  have hmin : IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro D hDfan hDeq
    have hDsize : HasCircuitSize n (graphFun G ∅) D.size := by
      refine ⟨D, hDfan, le_rfl, ?_⟩
      intro x
      exact (congrFun hDeq x).trans (hCeval x)
    exact hCbound.trans (Nat.find_min' hex hDsize)
  have hCfun : circuitFun n C = graphFun G ∅ := funext hCeval
  have hCsize : C.size + 1 < 4 * A.card := by omega
  by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨u, v, hu, hv, hne, hna, t, ht, hHas⟩ :=
      hasNotCase n G I A B hdisj hunion hAeqB hA3 hbip hdeg hgirth8 C hmin hnot hCfun hCsize
    exact ⟨u, v, hu, hv, hne, hna, t, by omega, hHas⟩
  · have hAO : AndOrOnly C := by
      intro g hg
      rcases (hfan g hg).1 with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · exact (hnot ⟨g, hg, hn⟩).elim
    obtain ⟨u, v, hu, hv, hne, hna, t, ht, hHas⟩ :=
      monotoneCase n G I A B hdisj hunion hAeqB hA3 hbip hdeg hgirth8 C hmin hAO hCfun hCsize
    exact ⟨u, v, hu, hv, hne, hna, t, by omega, hHas⟩
