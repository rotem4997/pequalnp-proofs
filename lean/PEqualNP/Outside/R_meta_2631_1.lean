import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2631_1
    (cascade :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
        let f := graphFun G A
        let eff (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
        let readers (v : Fin n) := C.gates.filter fun g => (eff g).contains v.val
        let later (i : ℕ) := (C.gates.drop (i + 1)).filter fun g => (eff g).contains (n + i)
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u v, G.Adj u v → u ∉ A) →
        (∃ u v, G.Adj u v) →
        FanInTwo C →
        circuitFun n C = f →
        (∀ s, HasCircuitSize n f s → C.size ≤ s) →
        (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
          ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
        (∃ v ∉ A, ∃ i g, C.gates[i]? = some g ∧ g.op = .and ∧ (eff g).contains v.val ∧
          ((∀ h ∈ readers v, h.op ≠ .or) ∨ 2 ≤ (later i).length ∨ ∃ h ∈ later i, h.op ≠ .or)) →
        ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (normal :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
        let f := graphFun G A
        let eff (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
        let readers (v : Fin n) := C.gates.filter fun g => (eff g).contains v.val
        let later (i : ℕ) := (C.gates.drop (i + 1)).filter fun g => (eff g).contains (n + i)
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u v, G.Adj u v → u ∉ A) →
        (∃ u v, G.Adj u v) →
        FanInTwo C →
        circuitFun n C = f →
        (∀ s, HasCircuitSize n f s → C.size ≤ s) →
        (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
          ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
        (∃ v ∉ A, (readers v).length = 2 ∧ ∃ g ∈ readers v, g.op = .and) →
        (∀ v ∉ A, ∀ i g, C.gates[i]? = some g → g.op = .and → (eff g).contains v.val →
          (∃ h ∈ readers v, h.op = .or) ∧ (later i).length ≤ 1 ∧ ∀ h ∈ later i, h.op = .or) →
        ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G _ A C
  dsimp only
  intro hdeg hgirth hA hedge hfan hcomp hmin hread hand
  let eff (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
  let readers (v : Fin n) := C.gates.filter fun g => (eff g).contains v.val
  let later (i : ℕ) := (C.gates.drop (i + 1)).filter fun g => (eff g).contains (n + i)
  by_cases hcas :
      ∃ v ∉ A, ∃ i g, C.gates[i]? = some g ∧ g.op = .and ∧ (eff g).contains v.val ∧
        ((∀ h ∈ readers v, h.op ≠ .or) ∨ 2 ≤ (later i).length ∨ ∃ h ∈ later i, h.op ≠ .or)
  · exact cascade n G A C hdeg hgirth hA hedge hfan hcomp hmin hread hcas
  · refine normal n G A C hdeg hgirth hA hedge hfan hcomp hmin hread hand ?_
    intro v hv i g hget hop hcont
    refine ⟨?_, ?_, ?_⟩
    · by_contra hno
      exact hcas ⟨v, hv, i, g, hget, hop, hcont, Or.inl fun h hh hhor => hno ⟨h, hh, hhor⟩⟩
    · by_contra hlt
      exact hcas ⟨v, hv, i, g, hget, hop, hcont, Or.inr (Or.inl (Nat.lt_of_not_le hlt))⟩
    · intro h hh
      by_contra hne
      exact hcas ⟨v, hv, i, g, hget, hop, hcont, Or.inr (Or.inr ⟨h, hh, hne⟩)⟩
