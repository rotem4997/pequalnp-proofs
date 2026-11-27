import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1710_3
    (bipartite : ∃ a : ℕ, ∀ (m n : ℕ) (R : Fin m → Fin n → Prop) [(i : Fin m) → (j : Fin n) → Decidable (R i j)],
      (∀ i, (Finset.univ.filter (R i)).card = 0 ∨ 3 ≤ (Finset.univ.filter (R i)).card) →
      (∀ j, (Finset.univ.filter (Function.swap R j)).card = 0 ∨ 3 ≤ (Finset.univ.filter (Function.swap R j)).card) →
      (∀ i k u v, R i u → R k u → R i v → R k v → i = k ∨ u = v) →
      ∀ D : Circuit, Monotone2 D →
      (∀ (x : Fin m → Bool) (y : Fin n → Bool),
        D.eval (List.ofFn x ++ List.ofFn y) = decide (∃ i j, R i j ∧ x i = true ∧ y j = true)) →
      ∑ i, (Finset.univ.filter (R i)).card ≤ a * (D.size + 1))
    (liftCircuit : ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ b * (C.size + 1) ∧
        ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ y v = true)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨a, hA⟩ := bipartite
  obtain ⟨b, hB⟩ := liftCircuit
  refine ⟨a*b, ?_⟩
  intro n G inst hd hg C hm hf
  obtain ⟨D,hD,hs,hxy⟩ := hB n G hd hg C hm (fun x => congrFun hf x)
  have row (u : Fin n) : (Finset.univ.filter (G.Adj u)).card = G.degree u := by
    change _ = (G.neighborFinset u).card
    congr 1
    ext v
    simp
  have col (u : Fin n) : (Finset.univ.filter fun v => G.Adj v u).card = G.degree u := by
    rw [← row]
    congr 1
    ext v
    simp [G.adj_comm]
  have hrect : ∀ i k : Fin n, i ≠ k →
      (Finset.univ.filter fun j => G.Adj i j ∧ G.Adj k j).card ≤ 1 := by
    intro i k hik
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨hiu,hku⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨hiv,hkv⟩ := (Finset.mem_filter.mp hv).2
    by_contra huv
    -- The common-neighbor argument follows the four-cycle construction in L_meta_1733.
    let cycle := SimpleGraph.Walk.cons hiu (SimpleGraph.Walk.cons hku.symm
      (SimpleGraph.Walk.cons hkv (SimpleGraph.Walk.cons hiv.symm SimpleGraph.Walk.nil)))
    have hc : cycle.IsCycle := by
      have h1 := G.ne_of_adj hiu
      have h2 := G.ne_of_adj hku
      have h3 := G.ne_of_adj hiv
      have h4 := G.ne_of_adj hkv
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, h1, h2, h3, h4, hik, huv, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm hik, Ne.symm huv]
      · simp [Sym2.eq_iff, h1, h2, h3, h4, hik, huv, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm hik, Ne.symm huv]
    have bad := hg i cycle hc
    simp [cycle] at bad
  have rectangle (i k u v : Fin n) (h1 : G.Adj i u) (h2 : G.Adj k u)
      (h3 : G.Adj i v) (h4 : G.Adj k v) : i = k ∨ u = v := by
    by_cases h : i = k
    · exact Or.inl h
    · exact Or.inr (Finset.card_le_one.mp (hrect i k h) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1,h2⟩) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3,h4⟩))
  have hcount := hA n n G.Adj (fun i => by simpa only [row] using hd i)
      (fun j => by simpa only [Function.swap, col] using hd j) rectangle D hD hxy
  simp only [row, G.sum_degrees_eq_twice_card_edges] at hcount
  calc
    G.edgeFinset.card ≤ 2 * G.edgeFinset.card := by omega
    _ ≤ a * (D.size + 1) := hcount
    _ ≤ a * (b * (C.size + 1)) := Nat.mul_le_mul_left a hs
    _ = (a*b) * (C.size + 1) := (Nat.mul_assoc _ _ _).symm
