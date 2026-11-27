import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4461_812
    (oneReader : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v∉A, 2≤G.degree v) → 5≤G.egirth → (∃ i j,G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ → C.size < 2 * (n-A.card) - 1 →
      ∃ v ∉ A, ∃ (j : ℕ) (g : Gate) (b : ℕ),
          C.gates[j]? = some g ∧
          C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] ∧
          (g.op=.and ∨ g.op=.or) ∧ n≤b ∧ b<n+j ∧
          (g.inputs=[v.val,b] ∨ g.inputs=[b,v.val]))
    (pinned : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      G.Colorable 2 → (∀ v∉A,(G.neighborSet v).ncard=3) →
      (∀ v (w : G.Walk v v),w.IsCycle → 7≤w.length) →
      (∀ i j,G.Adj i j → i∉A) → (∃ i j,G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ → C.size < 2 * (n-A.card) - 1 →
      (∃ v ∉ A, ∃ (j : ℕ) (g : Gate) (b : ℕ),
          C.gates[j]? = some g ∧
          C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] ∧
          (g.op=.and ∨ g.op=.or) ∧ n≤b ∧ b<n+j ∧
          (g.inputs=[v.val,b] ∨ g.inputs=[b,v.val])) →
      ∃ u v,u∉A ∧ v∉A ∧ u≠v ∧ ¬G.Adj u v ∧ ∃ t,t+8≤C.size ∧
        HasCircuitSize n (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x10 → x10 < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x4 ∧ x14 ∉ x4 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  intro n G dec A color degree cycles isolated edge s small deficit
  classical
  obtain ⟨D,fan,sz,df⟩ := small
  let P (k : ℕ) := ∃ C : Circuit, FanInTwo C ∧ circuitFun n C = graphFun G ∅ ∧ C.size=k
  have ex : ∃ k,P k := ⟨D.size,D,fan,funext df,rfl⟩
  obtain ⟨C,hf,cf,sc⟩ := Nat.find_spec ex
  have minC : IsMinimalCircuit n C := ⟨hf,fun E ef ec => by
    rw [sc]
    exact Nat.find_min' ex ⟨E,ef,ec.trans cf,rfl⟩⟩
  have le : C.size ≤ s := (minC.2 D fan ((funext df).trans cf.symm)).trans sz
  have short : C.size<2*(n-A.card)-1 := le.trans_lt deficit
  have gd : ∀ v∉A,2≤G.degree v := fun v hv => by
    have eq := degree v hv
    rw [SimpleGraph.ncard_neighborSet] at eq
    omega
  have gr : 5≤G.egirth := SimpleGraph.le_egirth.mpr fun v w cyc => by
    exact_mod_cast (show 5≤w.length by have := cycles v w cyc; omega)
  obtain ⟨u,v,hu,hv,uv,free,t,saved,computed⟩ :=
    pinned n G A C color degree cycles isolated edge minC cf short
      (oneReader n G A C gd gr edge minC cf short)
  exact ⟨u,v,hu,hv,uv,free,t,saved.trans le,computed⟩
