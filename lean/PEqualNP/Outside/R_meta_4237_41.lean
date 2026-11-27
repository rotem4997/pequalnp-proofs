import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- A maximum cut of the selected edges keeps at least half the edges incident to every vertex.
-- The remaining circuit bound is needed only for bipartite sets of unowned edges.
theorem PEqualNP.Outside.R_meta_4237_41
    (maxcut : ∀ (n : ℕ) (S : Finset (Sym2 (Fin n))),
      (∀ v : Fin n, s(v,v) ∉ S) →
      ∃ (T : Finset (Sym2 (Fin n))) (f : Fin n → Bool), T ⊆ S ∧
        (∀ u v : Fin n, s(u,v) ∈ T → f u ≠ f v) ∧ S.card ≤ 2*T.card ∧
        ∀ v : Fin n, (S.filter (fun e => v ∈ e)).card ≤ 2*(T.filter (fun e => v ∈ e)).card)
    (crossing : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (W : G.Walk v v), W.IsCycle → 5 ≤ W.length) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∀ (T : Finset (Sym2 (Fin n))) (f : Fin n → Bool),
        T ⊆ (G.edgeFinset.filter fun e => ¬∃ p q : Fin n, e = s(p,q) ∧
          ∃ j : Fin C.gates.length, Owns n C j p q ∧
            ∀ a b : Fin n, gateVal n C j (pairInput a b) = true → G.Adj a b) →
        (∀ u v, s(u,v) ∈ T → f u ≠ f v) →
        (∀ v : Fin n, (T.filter (fun e => v ∈ e)).card = 0 ∨ d < (T.filter (fun e => v ∈ e)).card) →
        T.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ) (x2 : ℕ), ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj], (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) → (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) → ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 → PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ → ∀ x11 ⊆ {x12 ∈ x4.edgeFinset | ¬∃ (x13 : Fin x3) (x14 : Fin x3), x12 = s(x13, x14) ∧ ∃ (x15 : Fin x8.gates.length), PEqualNP.EdgeOwnership.Owns x3 x8 (↑x15) x13 x14 ∧ ∀ (x16 x17 : Fin x3), PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x15) (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true → x4.Adj x16 x17}, (∀ (x13 : Fin x3), {x14 ∈ x11 | x13 ∈ x14}.card = (0 : ℕ) ∨ x1 < {x14 ∈ x11 | x13 ∈ x14}.card) → x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  obtain ⟨d, c, bound⟩ := crossing
  refine ⟨2*d, 2*c, ?_⟩
  intro n G _ degree girth C ao computes S badS high
  have noLoop (v : Fin n) : s(v,v) ∉ S := by
    intro h
    have ed := (Finset.mem_filter.mp (badS h)).1
    exact G.loopless.irrefl v (G.mem_edgeFinset.mp ed)
  obtain ⟨T,f,sub,cross,half,degs⟩ := maxcut n S noLoop
  have keeps (v : Fin n) : (T.filter (fun e => v ∈ e)).card = 0 ∨ d < (T.filter (fun e => v ∈ e)).card := by
    have inc : (T.filter (fun e => v ∈ e)).card ≤ (S.filter (fun e => v ∈ e)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ sub)
    have h := degs v
    rcases high v with hz | hd
    · left
      omega
    · right
      omega
  have hb := bound n G degree girth C ao computes T f (fun _ he => badS (sub he)) cross keeps
  calc
    S.card ≤ 2*T.card := half
    _ ≤ 2*(c*(C.size+1)) := Nat.mul_le_mul_left _ hb
    _ = (2*c)*(C.size+1) := (Nat.mul_assoc _ _ _).symm
