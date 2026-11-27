import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem PEqualNP.Outside.R_meta_4035_452
    (hTrace : let f := (fun x : Fin 10 → Bool =>
      (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))));
    let r := (fun (g : Gate) (i : ℕ) =>
      (g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs));
    let w := (fun b : Bool => b :: true :: List.replicate 8 false ++ [!b]);
    ∀ C : Circuit, FanInTwo C →
      (∀ x, C.eval (List.ofFn x ++ [!x 0]) = f x) →
      (∀ j : Fin C.size, ¬ r (C.gates.get j) 0) →
      (∃ j : Fin C.size, r (C.gates.get j) 10) ∧
      ∃ j : Fin C.size, (C.gates.get j).op = .not ∧
        (C.wires (w false)).getD (11 + j.val) false = false ∧
        (C.wires (w true)).getD (11 + j.val) false = true)
    (hNormalize : let f := (fun x : Fin 10 → Bool =>
      (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))));
    ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      (∀ x, C.eval (List.ofFn x ++ [!x 0]) = f x) →
      (C.size < 18 ∨ C.output ≠ 28 ∨ ∃ j : Fin C.size,
        (C.gates.get j).op = .not ∧ (C.gates.get j).inputs.head? = some 10) →
      HasCircuitSize 10 f 18)
    (hOrdinary : ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (hCore : let f := (fun x : Fin 10 → Bool =>
      (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))));
    let r := (fun (g : Gate) (i : ℕ) =>
      (g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs));
    let w := (fun b : Bool => b :: true :: List.replicate 8 false ++ [!b]);
    ∀ C : Circuit, FanInTwo C → C.size = 18 → C.output = 28 →
      (∀ x, C.eval (List.ofFn x ++ [!x 0]) = f x) →
      (∀ j : Fin C.size, ¬ r (C.gates.get j) 0) →
      (∃ a b : Fin C.size, ∀ j : Fin C.size, r (C.gates.get j) 10 ↔ j = a ∨ j = b) →
      (∀ j : Fin C.size, r (C.gates.get j) 10 → (C.gates.get j).op ≠ .not) →
      (∃ j : Fin C.size, (C.gates.get j).op = .not ∧
        (C.wires (w false)).getD (11 + j.val) false = false ∧
        (C.wires (w true)).getD (11 + j.val) false = true) →
      False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  let target := (fun x : Fin 10 → Bool =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  let f := (fun x : Fin 10 → Bool =>
      (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))))
  let r := (fun (g : Gate) (i : ℕ) =>
      (g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs))
  intro C model size computes nozero alleged
  have equiv (x : Fin 10 → Bool) : f x = target x := by
    change ((((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) ||
      false)))))) = _
    simp only [Bool.or_false, target]
    ac_rfl
  have computes' (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [!x 0]) = f x :=
    (computes x).trans (equiv x).symm
  have lower : ¬ HasCircuitSize 10 f 18 := by
    rintro ⟨D, model, size, yes⟩
    exact hOrdinary ⟨D, model, size, fun x => (yes x).trans (equiv x)⟩
  have zero (j : Fin C.size) : ¬ r (C.gates.get j) 0 := by
    rintro (⟨op, hin⟩ | ⟨op, hin⟩)
    · exact (nozero j).1 op hin
    · exact (nozero j).2 op hin
  have residual : ¬ (C.size < 18 ∨ C.output ≠ 28 ∨ ∃ j : Fin C.size,
      (C.gates.get j).op = .not ∧ (C.gates.get j).inputs.head? = some 10) :=
    fun easy => lower (hNormalize C model size computes' easy)
  push Not at residual
  have exactSize : C.size = 18 := by omega
  have binaryOnly (j : Fin C.size) (hr : r (C.gates.get j) 10) : (C.gates.get j).op ≠ .not := by
    intro hn
    rcases hr with ⟨_,head⟩ | ⟨notNot,_⟩
    · exact residual.2.2 j hn head
    · exact notNot hn
  obtain ⟨present, turns⟩ := hTrace C model computes' zero
  obtain ⟨a,b,orig⟩ := alleged
  have cover (j : Fin C.size) (hr : r (C.gates.get j) 10) : j = a ∨ j = b := by
    rcases hr with ⟨op, hi⟩ | ⟨op, hi⟩
    · exact (orig j).1 op hi
    · exact (orig j).2 op hi
  classical
  have actual : ∃ a' b' : Fin C.size,
      ∀ j : Fin C.size, r (C.gates.get j) 10 ↔ j = a' ∨ j = b' := by
    by_cases ha : r (C.gates.get a) 10
    · by_cases hb : r (C.gates.get b) 10
      · refine ⟨a,b,fun j => ⟨cover j, ?_⟩⟩
        rintro (rfl | rfl)
        · exact ha
        · exact hb
      · refine ⟨a,a,fun j => ?_⟩
        constructor
        · intro hj
          rcases cover j hj with rfl | rfl
          · exact Or.inl rfl
          · exact (hb hj).elim
        · rintro (rfl | rfl) <;> exact ha
    · obtain ⟨q,hq⟩ := present
      have hb : r (C.gates.get b) 10 := by
        rcases cover q hq with rfl | rfl
        · exact (ha hq).elim
        · exact hq
      refine ⟨b,b,fun j => ?_⟩
      constructor
      · intro hj
        rcases cover j hj with rfl | rfl
        · exact (ha hj).elim
        · exact Or.inl rfl
      · rintro (rfl | rfl) <;> exact hb
  exact hCore C model exactSize residual.2.1 computes' zero actual binaryOnly turns
