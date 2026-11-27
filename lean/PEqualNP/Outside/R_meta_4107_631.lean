import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4107_631
    (eliminate : ∀ (n : ℕ) (C : Circuit) (z : Fin n) (S : Finset ℕ),
      FanInTwo C → ReadsBack n C →
      (∀ g ∈ C.gates, g.op = .not → g.inputs.length = 1) →
      circuitFun n C (Function.update (fun _ => false) z false) = false →
      (∀ j ∈ S, j < C.size ∧ ∃ w ∈ (gateAt C j).inputs, ∃ b : Bool,
        ∀ x : Fin n → Bool,
          (C.wires (List.ofFn (Function.update x z false))).getD w false = b) →
      ∃ s, s + S.card ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x z false)) s)
    (few : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g => g.inputs.contains (↑v : ℕ)
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = f → ReadsBack n C →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧
        (g.op = .not → g.inputs.length = 1) ∧ (g.op ≠ .not → g.inputs.length = 2)) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length = 2 ∧ ∃ g ∈ readers v, g.op = .not) →
      (∀ z ∉ A, ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧ ∃ w ∈ (gateAt C j).inputs, ∃ b : Bool,
          ∀ x : Fin n → Bool,
            (C.wires (List.ofFn (Function.update x z false))).getD w false = b) →
        S.card ≤ 3) →
      ∃ z ∉ A, ∃ s, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x z false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : List PEqualNP.CircuitLowerBounds.Gate) (x15 : PEqualNP.CircuitLowerBounds.Gate) (x16 : List PEqualNP.CircuitLowerBounds.Gate), x5.gates = x14 ++ x15 :: x16 → (x15.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x18 < x1 + x14.length, x15.inputs = [x18]) ∨ (x15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x18 < x1 + x14.length, ∃ x19 < x1 + x14.length, x18 ≠ x19 ∧ x15.inputs = [x18, x19]) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  intro n G dec A C f readers hdeg hgirth hmarked hedge hmin heval hshape hreads hnot
  have hback : ReadsBack n C := by
    intro j hj w hw
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hlen : (C.gates.take j).length = j := by
      simp [Nat.min_eq_left (Nat.le_of_lt hj)]
    have hgate : gateAt C j = C.gates[j] := List.getD_eq_getElem C.gates _ hj
    rw [hgate] at hw
    rcases hshape _ _ _ hsplit with ⟨_, a, ha, hin⟩ | ⟨_, a, ha, b, hb, _, hin⟩
    · rw [hin] at hw
      simp at hw
      omega
    · rw [hin] at hw
      simp at hw
      rcases hw with hw | hw <;> omega
  have harity : ∀ g ∈ C.gates, g.inputs.Nodup ∧
      (g.op = .not → g.inputs.length = 1) ∧ (g.op ≠ .not → g.inputs.length = 2) := by
    intro g hg
    obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hg
    rcases hshape _ _ _ hsplit with ⟨hop, a, _, hin⟩ | ⟨hop, a, _, b, _, hab, hin⟩
    · simp [hop, hin]
    · have hn : g.op ≠ .not := by rcases hop with h | h <;> simp [h]
      simp [hn, hin, hab]
  let forced (z : Fin n) (S : Finset ℕ) : Prop :=
    ∀ j ∈ S, j < C.size ∧ ∃ w ∈ (gateAt C j).inputs, ∃ b : Bool,
      ∀ x : Fin n → Bool,
        (C.wires (List.ofFn (Function.update x z false))).getD w false = b
  by_cases h : ∃ z ∉ A, ∃ S : Finset ℕ, 4 ≤ S.card ∧ forced z S
  · obtain ⟨z, hz, S, hcard, hconst⟩ := h
    have hzero : circuitFun n C (Function.update (fun _ => false) z false) = false := by
      have hup : Function.update (fun _ : Fin n => false) z false = fun _ => false := by
        funext i
        by_cases hi : i = z <;> simp [Function.update, hi]
      rw [heval, hup]
      change (decide (∃ a ∈ A, (false : Bool) = true) ||
        decide (∃ a b, G.Adj a b ∧ (false : Bool) = true ∧ (false : Bool) = true)) = false
      simp
    obtain ⟨s, hs, hcofactor⟩ := eliminate n C z S hmin.1 hback
      (fun g hg => (harity g hg).2.1) hzero hconst
    exact ⟨z, hz, s, by omega, by simpa only [heval] using hcofactor⟩
  · apply few n G A C hdeg hgirth hmarked hedge hmin heval hback harity hreads hnot
    intro z hz S hconst
    by_contra hcard
    exact h ⟨z, hz, S, by omega, hconst⟩
