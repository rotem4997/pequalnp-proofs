import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.NotPremium

-- Only edges accepted on their own two endpoints are counted. Soundness on
-- every input excludes positives on independent sets even when only some edges are detected.
-- In a record circuit one cannot preserve the number of accepted edges
-- with fewer gates. Force an AND accepting a nonedge pair to false and charge the lost edges
-- against the gates saved by computing the remaining pair outputs.
theorem PEqualNP.Outside.R_meta_1710_1
  (clean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ C : Circuit, Monotone2 C →
    (∀ u : Fin n, circuitFun n C (pairInput u u) = false) →
    (∀ j : ℕ, ¬ ((gateAt C j).op = GateOp.and ∧
      ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true)) →
    (G.edgeFinset.filter (fun e => circuitFun n C (fun v => decide (v ∈ e)) = true)).card ≤ C.size)
  (price : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    let safe := fun C : Circuit => ∀ x, circuitFun n C x = true → graphFun G ∅ x = true
    let hits := fun C : Circuit => G.edgeFinset.filter (fun e => circuitFun n C (fun v => decide (v ∈ e)) = true)
    let bad := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = GateOp.and ∧
      ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
    ∀ C : Circuit, Monotone2 C → safe C →
    (∀ B : Circuit, Monotone2 B → safe B → B.size < C.size → (hits B).card < (hits C).card) →
    (∃ j : ℕ, bad C j) →
    ∃ j : ℕ, bad C j ∧ ∃ D : Circuit, Monotone2 D ∧ safe D ∧ D.size < C.size ∧
      hits D = hits ⟨replaceByConst C.gates j false, C.output⟩ ∧
      (hits C).card ≤ (hits D).card + k * (C.size - D.size)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k, hprice⟩ := price
  refine ⟨k+1, ?_⟩
  intro n G inst hd hg D hmon hfun
  let safe := fun C : Circuit => ∀ x, circuitFun n C x = true → graphFun G ∅ x = true
  let hits := fun C : Circuit => G.edgeFinset.filter (fun e => circuitFun n C (fun v => decide (v ∈ e)) = true)
  let bad := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = GateOp.and ∧
      ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
  have rejects (C : Circuit) (hs : safe C) (u : Fin n) : circuitFun n C (pairInput u u) = false := by
    cases hv : circuitFun n C (pairInput u u) with
    | false => rfl
    | true =>
      have h := hs _ hv
      change (decide (∃ v ∈ (∅ : Finset (Fin n)), pairInput u u v = true) ||
        decide (∃ a b : Fin n, G.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true)) = true at h
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq] at h
      obtain ⟨a,b,hab,ha,hb⟩ := h
      change decide (a=u ∨ a=u) = true at ha
      change decide (b=u ∨ b=u) = true at hb
      simp only [or_self,decide_eq_true_eq] at ha hb
      subst a
      subst b
      exact (G.loopless.irrefl _ hab).elim
  have bound : ∀ t : ℕ, ∀ C : Circuit, C.size = t → Monotone2 C → safe C →
      (hits C).card ≤ (k+1) * (C.size+1) := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro C hsize hC hs
      by_cases record : ∀ B : Circuit, Monotone2 B → safe B → B.size < C.size → (hits B).card < (hits C).card
      · by_cases dirty : ∃ j : ℕ, bad C j
        · obtain ⟨j, hj, E, hE, hsafe, hlt, hpin, hloss⟩ := hprice n G hd hg C hC hs record dirty
          have prev := ih E.size (hsize ▸ hlt) E rfl hE hsafe
          have diff : (E.size+1) + (C.size-E.size) = C.size+1 := by omega
          calc
            (hits C).card ≤ (hits E).card + k * (C.size-E.size) := hloss
            _ ≤ (k+1) * (E.size+1) + (k+1) * (C.size-E.size) :=
              Nat.add_le_add prev (Nat.mul_le_mul_right _ (Nat.le_succ k))
            _ = (k+1) * (C.size+1) := by rw [← Nat.mul_add, diff]
        · have hclean := clean n G hg C hC (rejects C hs) (fun j hj => dirty ⟨j,hj⟩)
          have scaled := Nat.mul_le_mul_right (C.size+1) (show 1 ≤ k+1 by omega)
          exact (hclean.trans (Nat.le_succ C.size)).trans (by simpa only [one_mul] using scaled)
      · push Not at record
        obtain ⟨E, hE, hsafe, hlt, hGE⟩ := record
        exact hGE.trans ((ih E.size (hsize ▸ hlt) E rfl hE hsafe).trans
          (Nat.mul_le_mul_left _ (by omega)))
  have safeD : safe D := by
    intro x hx
    change (decide (∃ v ∈ (∅ : Finset (Fin n)), x v = true) ||
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    exact (congrFun hfun x).symm.trans hx
  have allhit : hits D = G.edgeFinset := by
    apply Finset.filter_eq_self.mpr
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := G.mem_edgeFinset.mp he
      rw [hfun]
      apply decide_eq_true
      exact ⟨u, v, huv, by simp, by simp⟩
  have h := bound D.size D rfl hmon safeD
  simpa only [allhit] using h
