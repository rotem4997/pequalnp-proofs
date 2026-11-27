import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count distinct gates exposed to one pinned input and the first forced constant.
-- A sole binary reader with two distinct raw inputs is excluded separately.
theorem PEqualNP.Outside.R_meta_1971_1
    (propagate : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ),
    let reads (a : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
    let near (v : Fin n) (j : ℕ) :=
      (Finset.range C.gates.length).filter fun k =>
        k ≠ j ∧ (reads v.val (gateAt C k) = true ∨
          j < k ∧ reads (n+j) (gateAt C k) = true)
    FanInTwo C → (j < C.gates.length ∧ reads v.val (gateAt C j) = true ∧
      (gateAt C j).op ≠ .or ∧ 3 ≤ (near v j).card) →
    (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠
      circuitFun n C (Function.update y v false)) →
    ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s)
    (noRaw : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (v : Fin n),
    let reads (a : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
    let readers (v : Fin n) := C.gates.filter (reads v.val)
    v ∉ A → (G.neighborSet v).ncard = 3 →
    (∀ a (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) →
    (∀ u w, G.Adj u w → u ∉ A) → (∃ u w, G.Adj u w) →
    IsMinimalCircuit n C → circuitFun n C = graphFun G A →
    (readers v).length ≤ 1 →
    ∀ g ∈ readers v, ∀ p : Fin n, p ≠ v →
      g.inputs.Perm [v.val,p.val] → g.op ≠ .and ∧ g.op ≠ .or)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    let f := graphFun G A
    let reads (a : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
    let near (v : Fin n) (j : ℕ) :=
      (Finset.range C.gates.length).filter fun k =>
        k ≠ j ∧ (reads v.val (gateAt C k) = true ∨
          j < k ∧ reads (n+j) (gateAt C k) = true)
    let readers (v : Fin n) := C.gates.filter (reads v.val)
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    7 ≤ G.egirth →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → circuitFun n C = f →
    (∀ v ∉ A, (readers v).length ≤ 3 ∧
      ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
    (∃ v ∉ A, (readers v).length ≤ 1 ∧ (∀ g ∈ readers v, ∀ p : Fin n, p ≠ v →
      g.inputs.Perm [v.val,p.val] → g.op ≠ .and ∧ g.op ≠ .or)) →
    (¬ (∃ v ∉ A, ∃ j : ℕ, j < C.gates.length ∧ reads v.val (gateAt C j) = true ∧
      (gateAt C j).op ≠ .or ∧ 3 ≤ (near v j).card)) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A,
      let r := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      r.length ≤ 3 ∧ (r.length = 3 → ∀ g ∈ r, g.op = .or)) →
    (∃ v ∉ A, (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s := by
  classical
  intro n G A f C degree girth unmarked edge description fan computes minSize readBound few
  let reads (a : ℕ) (g : Gate) :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
  let near (v : Fin n) (j : ℕ) :=
    (Finset.range C.gates.length).filter fun k =>
      k ≠ j ∧ (reads v.val (gateAt C k) = true ∨
        j < k ∧ reads (n+j) (gateAt C k) = true)
  have same : graphFun G A = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ f x = true
    rw [description x]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  by_cases hit : ∃ v ∉ A, ∃ j : ℕ, j < C.gates.length ∧ reads v.val (gateAt C j) = true ∧
      (gateAt C j).op ≠ .or ∧ 3 ≤ (near v j).card
  · obtain ⟨v,vm,j,jlt,rin,nonOr,many⟩ := hit
    have degree' (z : Fin n) (hz : z ∉ A) : (G.neighborFinset z).card = 3 := by
      change G.degree z = 3
      rw [← G.ncard_neighborSet]
      exact degree z hz
    obtain ⟨a,ha⟩ := Finset.card_pos.mp
      (show 0 < (G.neighborFinset v).card by rw [degree' v vm]; decide)
    have va := (G.mem_neighborFinset v a).mp ha
    have am := unmarked a v va.symm
    have hmem : v ∈ G.neighborFinset a := (G.mem_neighborFinset a v).mpr va.symm
    have enough : 0 < ((G.neighborFinset a).erase v).card := by
      rw [Finset.card_erase_of_mem hmem,degree' a am]
      decide
    obtain ⟨b,hb⟩ := Finset.card_pos.mp enough
    obtain ⟨bv,hb'⟩ := Finset.mem_erase.mp hb
    have ab := (G.mem_neighborFinset a b).mp hb'
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a ∨ i = b)
    have x0 : f (Function.update x v false) = false := by
      have hx : Function.update x v false = x := Function.update_eq_self _ _
      rw [hx]
      apply Bool.eq_false_iff.mpr
      intro fail
      rw [description x] at fail
      simp [x] at fail
    have y1 : f (Function.update y v false) = true := by
      apply (description _).mpr
      right
      exact ⟨a,b,ab,by simp [Function.update_of_ne va.ne.symm,y],
        by simp [Function.update_of_ne bv,y]⟩
    obtain ⟨s,hs,D⟩ := propagate n C v j fan ⟨jlt,rin,nonOr,many⟩
      ⟨x,y,by rw [computes,x0,y1]; decide⟩
    exact ⟨v,vm,s,hs,by simpa only [computes] using D⟩
  · have least : IsMinimalCircuit n C := by
      refine ⟨fan,?_⟩
      intro D kind value
      apply minSize D.size
      exact ⟨D,kind,le_rfl,fun x => congrFun (value.trans computes) x⟩
    have wide : 7 ≤ G.egirth := by
      apply SimpleGraph.le_egirth.mpr
      intro v p hc
      exact_mod_cast girth v p hc
    obtain ⟨v,vm,unique⟩ := few
    have reasonable := noRaw n G A C v vm (degree v vm) girth unmarked edge least
      (computes.trans same.symm) unique
    have result := residual n G A C degree wide unmarked edge least (computes.trans same.symm)
      readBound ⟨v,vm,unique,reasonable⟩ hit
    rwa [same] at result
