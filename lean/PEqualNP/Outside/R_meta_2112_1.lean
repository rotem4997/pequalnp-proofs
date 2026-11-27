import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The deleted vertex has three neighbors. Involutions of the remaining graph
-- send any of those neighbors to vertex four. Keep the index of the unique
-- gate reading that input when renaming the circuit wires.
theorem PEqualNP.Outside.R_meta_2112_1
    (renameInput : ∀ (C : Circuit) (p : Fin 9 → Fin 9) (v : Fin 9) (k : Fin C.size),
      (∀ i, p (p i) = i) → FanInTwo C →
      (C.gates.get k).op ≠ GateOp.or →
      (∀ j : Fin C.size, v.val ∈ (C.gates.get j).inputs ↔ j = k) →
      ∃ (D : Circuit) (l : Fin D.size), FanInTwo D ∧ D.size = C.size ∧
        (∀ x : Fin 9 → Bool, circuitFun 9 D x = circuitFun 9 C (fun i => x (p i))) ∧
        (D.gates.get l).op ≠ GateOp.or ∧
        ∀ j : Fin D.size, (p v).val ∈ (D.gates.get j).inputs ↔ j = l)
    (canonical : ∀ (D : Circuit) (l : Fin D.size), FanInTwo D → D.size ≤ 15 →
      (D.gates.get l).op ≠ GateOp.or →
      (∀ j : Fin D.size, 4 ∈ (D.gates.get j).inputs ↔ j = l) →
      circuitFun 9 D ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  classical
  intro f readers admissible C hC hw
  obtain ⟨v, hv, k, hk, hop⟩ := hw
  obtain ⟨hmin, hsize, hfun, _, hdeg⟩ := hC
  obtain ⟨_, hle, htwo⟩ := hdeg v hv
  have hone : (readers C v).card = 1 := by
    have hpos := Finset.card_pos.mpr ⟨k, hk⟩
    have hne : (readers C v).card ≠ 2 := fun h => hop (htwo h k hk)
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  have heq : k = a := Finset.mem_singleton.mp (ha ▸ hk)
  subst a
  have hreader (j : Fin C.size) : v.val ∈ (C.gates.get j).inputs ↔ j = k := by
    have hm : j ∈ readers C v ↔ v.val ∈ (C.gates.get j).inputs := by simp [readers]
    rw [← hm, ha, Finset.mem_singleton]
  have useMap (p : Fin 9 → Fin 9) (hi : ∀ i, p (p i) = i) (hv4 : p v = 4)
      (hsym : ∀ x : Fin 9 → Bool, f (fun i => x (p i)) = f x) : False := by
    obtain ⟨D, l, hfan, hsz, hval, hgate, hread⟩ :=
      renameInput C p v k hi hmin.1 hop hreader
    rw [hv4] at hread
    apply canonical D l hfan (hsz.trans_le hsize) hgate hread
    funext x
    rw [hval, hfun]
    exact hsym x
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h
  · subst v
    exact useMap id (fun _ => rfl) rfl (fun _ => rfl)
  · subst v
    let p : Fin 9 → Fin 9 := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
    apply useMap p (by decide) (by decide)
    intro x
    dsimp [f, p, Matrix.cons_val_succ, Matrix.cons_val_zero]
    ac_rfl
  · subst v
    let p : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
    apply useMap p (by decide) (by decide)
    intro x
    dsimp [f, p, Matrix.cons_val_succ, Matrix.cons_val_zero]
    ac_rfl
