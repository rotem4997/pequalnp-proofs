import Mathlib.Data.Fin.Tuple.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Set a singly read input to false. If exactly two gates disappear, look for
-- a surviving wire true on all rising pairs. This is the control of a sole
-- AND, or the other input to an AND that consumes the sole NOT.
-- The last child concerns only an optimal eight-input circuit, not a pair
-- of nine-input executions or an unspecified completion of such a circuit.
theorem PEqualNP.Outside.R_meta_2112_532
    (binary : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → circuitFun 9 C = F →
        13 + C.gates.countP (fun g => g.op.eval [false,false]) ≤ C.size)
    (trim : ∀ (n : ℕ) (C : Circuit) (v : Fin (n+1)) (j : Fin C.size),
      let f := fun (b : Bool) (x : Fin n → Bool) => circuitFun (n+1) C (v.insertNth (α := fun _ => Bool) b x)
      IsMinimalCircuit (n+1) C → C.gates.countP (fun g => g.op.eval [false,false]) ≤ 2 →
      (∀ i : Fin C.size, ∀ w ∈ (C.gates.get i).inputs, w < n+1+i.val) →
      (∀ i : Fin C.size, v.val ∈ (C.gates.get i).inputs ↔ i = j) → (C.gates.get j).op ≠ .or →
      (∃ x y, f false x ≠ f false y) → (∃ x, f false x = false ∧ f true x = true) →
      ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = f false ∧ D.size + 2 ≤ C.size ∧
        (D.size + 3 ≤ C.size ∨ ∃ w : ℕ, ∀ x, f false x = false → f true x = true →
          (D.wires (List.ofFn x)).getD w false = true))
    (floorBound : have F : (Fin 9 → Bool) → Bool := fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ v ∈ [(4 : Fin 9), (6 : Fin 9), (7 : Fin 9)], ∀ D : Circuit, FanInTwo D →
        (circuitFun 8 D = fun x : Fin 8 → Bool => F (v.insertNth false x)) → 13 ≤ D.size)
    (separate : have F : (Fin 9 → Bool) → Bool := fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ v ∈ [(4 : Fin 9), (6 : Fin 9), (7 : Fin 9)], ∀ D : Circuit, FanInTwo D → D.size = 13 →
        (circuitFun 8 D = fun x : Fin 8 → Bool => F (v.insertNth false x)) →
        ∀ w : ℕ, ∃ x : Fin 8 → Bool,
          F (v.insertNth false x) = false ∧
          F (v.insertNth true x) = true ∧ (D.wires (List.ofFn x)).getD w false = false) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  classical
  intro target readers admissible C eligible bad
  obtain ⟨minimal, small, computes, normal, restricted⟩ := eligible
  obtain ⟨v, hv, j, hj, hop⟩ := bad
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have hF : circuitFun 9 C = F := by
    rw [computes]
    funext x
    simp [target, F, List.any_cons, Bool.or_assoc, Fin.ofNat]
  have hb := binary C minimal.1 hF
  have back (i : Fin C.size) := (normal i).1
  have unique (i : Fin C.size) : v.val ∈ (C.gates.get i).inputs ↔ i = j := by
    have hmem (k : Fin C.size) : k ∈ readers C v ↔ v.val ∈ (C.gates.get k).inputs := by simp [readers]
    have hc : (readers C v).card ≤ 1 := by
      by_contra more
      have hle := (restricted v hv).2.1
      exact hop ((restricted v hv).2.2 (by omega) j hj)
    constructor
    · exact fun h => Finset.card_le_one.mp hc i ((hmem i).2 h) j hj
    · rintro rfl
      exact (hmem i).1 hj
  let ins (v : Fin 9) (b : Bool) (x : Fin 8 → Bool) := v.insertNth (α := fun _ => Bool) b x
  let probe (v : Fin 9) (i : Fin 8) := decide (i.val = (if v = 4 then 0 else if v = 6 then 1 else 2))
  have samples : ∀ z ∈ ([4,6,7] : List (Fin 9)),
      F (ins z false (fun _ => false)) ≠ F (ins z false (fun _ => true)) ∧
      F (ins z false (probe z)) = false ∧ F (ins z true (probe z)) = true := by decide +kernel
  obtain ⟨different, off, on⟩ := samples v hv
  obtain ⟨D, legal, eq, saved, structural⟩ := trim 8 C v j minimal (by omega) back unique hop
    ⟨_, _, by simpa only [hF] using different⟩ ⟨_, by simpa only [hF] using off, by simpa only [hF] using on⟩
  rw [hF] at eq structural
  have floor := floorBound v hv D legal eq
  rcases structural with extra | ⟨w, hw⟩
  · omega
  · obtain ⟨x, low, high, no⟩ := separate v hv D legal (by omega) eq w
    exact Bool.noConfusion ((hw x low high).symm.trans no)
