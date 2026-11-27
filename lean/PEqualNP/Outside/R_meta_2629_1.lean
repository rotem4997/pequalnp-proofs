import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2629_1
  (normalise : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
    (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
    ∃ D : Circuit,
      D.gates = C.gates.map (fun g => ⟨g.op,g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩) ∧
      D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (∀ pre g post, D.gates = pre ++ g :: post →
        (g.op = .not ∧ ∃ a < n + pre.length, g.inputs = [a]) ∨
        ((g.op = .and ∨ g.op = .or) ∧ ∃ a < n + pre.length,
          ∃ b < n + pre.length, a ≠ b ∧ g.inputs = [a,b])))
  (clean_case : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    let f := PEqualNP.MetaComplexity.NestedCover.graphFun G A
    let readers (v : Fin n) := C.gates.filter fun g => g.inputs.contains v.val
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → circuitFun n C = f →
    (∀ pre g post, C.gates = pre ++ g :: post →
      (g.op = .not ∧ ∃ a < n + pre.length, g.inputs = [a]) ∨
      ((g.op = .and ∨ g.op = .or) ∧ ∃ a < n + pre.length,
        ∃ b < n + pre.length, a ≠ b ∧ g.inputs = [a,b])) →
    (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
      ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
    (∃ v ∉ A, (readers v).length = 2 ∧ ∃ g ∈ readers v, g.op = .not) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  intro n G dec A C f readers hdeg hgirth hmarked hedge hfan heval hmin hreads hnot
  have hm : IsMinimalCircuit n C := by
    refine ⟨hfan,?_⟩
    intro E hE he
    exact hmin E.size ⟨E,hE,le_rfl,fun x => congrFun (he.trans heval) x⟩
  have hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
    obtain ⟨u,v,huv⟩ := hedge
    refine ⟨fun _ => false,fun _ => true,?_⟩
    rw [heval]
    change PEqualNP.MetaComplexity.NestedCover.graphFun G A (fun _ => false) ≠
      PEqualNP.MetaComplexity.NestedCover.graphFun G A (fun _ => true)
    change (decide (∃ a ∈ A, (false : Bool) = true) ||
      decide (∃ a b, G.Adj a b ∧ (false : Bool) = true ∧ (false : Bool) = true)) ≠
      (decide (∃ a ∈ A, (true : Bool) = true) ||
      decide (∃ a b, G.Adj a b ∧ (true : Bool) = true ∧ (true : Bool) = true))
    simp [show ∃ a b, G.Adj a b from ⟨u,v,huv⟩]
  obtain ⟨D,hmap,hsize,he,hshape⟩ := normalise n C hm hnc
  let cut : Gate → Gate := fun g => ⟨g.op,g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩
  let rd (v : Fin n) := D.gates.filter fun g => g.inputs.contains v.val
  have hrd (v : Fin n) : (rd v).map Gate.op = (readers v).map Gate.op := by
    change (List.filter _ D.gates).map Gate.op = _
    rw [hmap,List.filter_map,List.map_map]
    rfl
  have hlen (v : Fin n) : (rd v).length = (readers v).length := by
    simpa only [List.length_map] using congrArg List.length (hrd v)
  have hlegal : FanInTwo D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (hmap ▸ hg)
    have hf := hfan a ha
    refine ⟨hf.1,?_⟩
    simp only [List.length_take]
    exact (Nat.min_le_right _ _).trans hf.2
  have hmD : IsMinimalCircuit n D := by
    refine ⟨hlegal,?_⟩
    intro E hE hEq
    rw [hsize]
    exact hm.2 E hE (hEq.trans he)
  have hrD : ∀ v ∉ A, 2 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧
      ((rd v).length = 3 → ∀ g ∈ rd v, g.op = .or) := by
    intro v hv
    obtain ⟨lo,hi,all⟩ := hreads v hv
    refine ⟨by simpa [hlen] using lo,by simpa [hlen] using hi,?_⟩
    intro hl g hg
    have hmop : g.op ∈ (readers v).map Gate.op := by
      rw [← hrd v]
      exact List.mem_map.mpr ⟨g,hg,rfl⟩
    obtain ⟨a,ha,haop⟩ := List.mem_map.mp hmop
    exact haop ▸ all (by simpa [hlen] using hl) a ha
  have hnD : ∃ v ∉ A, (rd v).length = 2 ∧ ∃ g ∈ rd v, g.op = .not := by
    obtain ⟨v,hv,hl,g,hg,hgn⟩ := hnot
    have hnop : GateOp.not ∈ (rd v).map Gate.op := by
      rw [hrd v]
      exact List.mem_map.mpr ⟨g,hg,hgn⟩
    obtain ⟨a,ha,haop⟩ := List.mem_map.mp hnop
    exact ⟨v,hv,by simpa [hlen] using hl,a,ha,haop⟩
  obtain ⟨v,hv,s,hs,hc⟩ := clean_case n G A D hdeg hgirth hmarked hedge hmD
    (he.trans heval) hshape hrD hnD
  exact ⟨v,hv,s,by simpa [hsize] using hs,hc⟩
