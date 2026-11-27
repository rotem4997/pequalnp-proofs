import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2631_731
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
    (privateCase : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;   have x8 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x8 : Fin x1) => List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).contains ↑x8) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (∀ (x11 : Fin x1) (x12 : x2.Walk x11 x11), x12.IsCycle → (7 : ℕ) ≤ x12.length) → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x16 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x16 → x5.size ≤ x16) → (∀ x17 ∉ x4, (2 : ℕ) ≤ (x8 x17).length ∧ (x8 x17).length ≤ (3 : ℕ) ∧ ((x8 x17).length = (3 : ℕ) → ∀ x20 ∈ x8 x17, x20.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ v ∉ x4, ∃ (p j : ℕ) (a g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[p]? = some a ∧ x5.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ v.val ∈ x7 g ∧ x1+p ∈ x7 g ∧ (∀ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), x5.gates[k]? = some h → x1+p ∈ x7 h → k=j)) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20)
    (normal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let O := GateOp.or
      let e (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
      let R (a w : ℕ) := (C.gates.drop a).filter fun g => (e g).contains w
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ v ∉ A, let T := R 0 v.val; T.length = 2 ∨ T.length = 3 ∧ ∀ g ∈ T, g.op = O) →
      (∃ v ∉ A, ∃ g ∈ R 0 v.val, g.op = .and) →
      (∀ v ∉ A, ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g → g.op = .and → v.val ∈ e g →
        (∃ h ∈ R 0 v.val, h.op = O) ∧ (R (i+1) (n+i)).map Gate.op <+: [O] ∧
          ∀ p < C.size, n+p ∈ e g → ∃ k ≠ i, ∃ h : Gate, C.gates[k]? = some h ∧ n+p ∈ e h) →
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
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
  · by_cases hp : ∃ v ∉ A, ∃ (p i : ℕ) (a g : Gate), C.gates[p]? = some a ∧ C.gates[i]? = some g ∧
          g.op = .and ∧ v.val ∈ eff g ∧ n+p ∈ eff g ∧
          (∀ (k : ℕ) (h : Gate), C.gates[k]? = some h → n+p ∈ eff h → k=i)
    · exact privateCase n G A C hdeg hgirth hA hedge hfan hcomp hmin hread hp
    · have ismin : IsMinimalCircuit n C := by
        refine ⟨hfan,?_⟩
        intro D hD eqD
        exact hmin D.size ⟨D,hD,le_rfl,fun x => congrFun (eqD.trans hcomp) x⟩
      apply normal n G A C hdeg hgirth hA ismin hcomp
      · intro v hv
        obtain ⟨l,u,t⟩ := hread v hv
        change 2 ≤ (readers v).length at l
        change (readers v).length ≤ 3 at u
        change (readers v).length = 2 ∨ (readers v).length = 3 ∧ ∀ g ∈ readers v, g.op = .or
        by_cases two : (readers v).length = 2
        · exact Or.inl two
        · have three : (readers v).length = 3 := by omega
          exact Or.inr ⟨three,t three⟩
      · obtain ⟨v,hv,_,g,rg,ag⟩ := hand
        exact ⟨v,hv,g,rg,ag⟩
      · intro v hv i g hget hop hcont
        have contains : (eff g).contains v.val := by simpa [eff] using hcont
        have hNoOr : ∃ h ∈ readers v, h.op = .or := by
          by_contra hno
          exact hcas ⟨v,hv,i,g,hget,hop,contains,Or.inl fun h hh ho => hno ⟨h,hh,ho⟩⟩
        have few : (later i).length ≤ 1 := by
          by_contra hlt
          exact hcas ⟨v,hv,i,g,hget,hop,contains,Or.inr (Or.inl (Nat.lt_of_not_le hlt))⟩
        have onlyOr (h) (hh : h ∈ later i) : h.op = .or := by
          by_contra ne
          exact hcas ⟨v,hv,i,g,hget,hop,contains,Or.inr (Or.inr ⟨h,hh,ne⟩)⟩
        refine ⟨hNoOr,?_,?_⟩
        · change (later i).map Gate.op <+: [.or]
          cases e : later i with
          | nil => simp
          | cons h t =>
            have op : h.op = .or := onlyOr h (by simp [e])
            have et : t = [] := by
              cases t with
              | nil => rfl
              | cons h' t' => simp [e] at few
            simp [et,op]
        · intro p plt pin
          change p < C.gates.length at plt
          obtain ⟨a, ha⟩ : ∃ a : Gate, C.gates[p]? = some a := ⟨C.gates[p],by simp [plt]⟩
          by_contra! none
          apply hp
          refine ⟨v,hv,p,i,a,g,ha,hget,hop,hcont,pin,?_⟩
          intro k h hk rh
          by_contra ne
          exact none k ne h hk rh
