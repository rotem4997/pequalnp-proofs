import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4482_286
    (one : let f : (Fin 9 → Bool) → Bool := fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun t => x (Fin.ofNat 9 (t/10)) && x (Fin.ofNat 9 (t % 10)); ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, gs.length ≤ 7 → (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∀ B : Finset (Fin 9), B.card ≤ 5 → ∀ z : ℕ, let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨(⟨.or,[0,2]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs,0⟩; ∃ x y : Fin 9 → Bool, f x ≠ f y ∧ (∀ i∈B, x i = y i) ∧ (C.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn y)).getD z false)
    (many : let f : (Fin 9 → Bool) → Bool := fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun t => x (Fin.ofNat 9 (t/10)) && x (Fin.ofNat 9 (t % 10)); ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, gs.length ≤ 7 → (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∀ O : Finset ℕ, O.card ≤ 6 → (∃ a∈O,∃ b∈O,10≤a ∧ 10≤b ∧ a≠b) → let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨(⟨.or,[0,2]⟩ : PEqualNP.CircuitLowerBounds.Gate)::gs,0⟩; ∃ x : Fin 9 → Bool,∃ v : Fin 9, f x ≠ f (Function.update x v true) ∧ ∀ u∈O, (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn (Function.update x v true))).getD u false) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate),   x2.length = (7 : ℕ) →     (∀ (x4 : ℕ) (x5 : x4 < x2.length), (x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x2[x4].inputs.length ≤ (2 : ℕ) ∧ ∀ x6 ∈ x2[x4].inputs, x6 < (10 : ℕ) + x4 ∨ x6 = (17 : ℕ)) →       have x5 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (2 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };       ∀ x6 ⊆ (Finset.range (17 : ℕ)).erase (9 : ℕ), x6.card ≤ (6 : ℕ) → (∃ x9 ∈ x6, (10 : ℕ) ≤ x9) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x6, (x5.wires (List.ofFn x10)).getD x12 Bool.false = (x5.wires (List.ofFn x11)).getD x12 Bool.false := by
  classical
  dsimp only at one many ⊢
  intro gs len valid O sub cap used
  have legal : ∀ g∈gs,(g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op=PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length≤2 := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨(valid i hi).1,(valid i hi).2.1⟩
  by_cases several : ∃ a∈O,∃ b∈O,10≤a ∧ 10≤b ∧ a≠b
  · obtain ⟨x,v,diff,same⟩ := many gs (by omega) legal O cap several
    exact ⟨x,Function.update x v true,diff,same⟩
  obtain ⟨z,hz,large⟩ := used
  let B := Finset.univ.filter (fun i : Fin 9 => i.val∈O)
  have Raw (i : Fin 9) : i∈B ↔ i.val∈O := by simp [B]
  have bb : (B.image Fin.val)⊆O.erase z := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_erase.mpr ⟨by have := i.isLt; omega,(Raw i).mp hi⟩
  have hc := Finset.card_le_card bb
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
  have er := Finset.card_erase_add_one hz
  obtain ⟨x,y,diff,obs,wire⟩ := one gs (by omega) legal B (by omega) z
  refine ⟨x,y,diff,?_⟩
  intro u hu
  by_cases eq : u=z
  · exact eq.symm ▸ wire
  have ru := Finset.mem_erase.mp (sub hu)
  have small : u<9 := by
    by_contra! high
    exact several ⟨u,hu,z,hz,by omega,large,eq⟩
  let j : Fin 9 := ⟨u,small⟩
  have agree := obs j ((Raw j).mpr hu)
  have read (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 9 → Bool) :
      (C.wires (List.ofFn a)).getD u false = a j := by
    let next := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
    have preserved (rest : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (hw : u<w.length) :
        (rest.foldl next w).getD u false = w.getD u false := by
      induction rest generalizing w with
      | nil => rfl
      | cons g rest ih =>
        change (rest.foldl next (next w g)).getD u false=w.getD u false
        rw [ih (next w g) (by simp [next]; omega)]
        exact List.getD_append _ _ _ _ hw
    change (C.gates.foldl next (List.ofFn a)).getD u false = _
    rw [preserved C.gates _ (by simpa using small)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,small,↓reduceDIte,Option.getD_some,j]
  rw [read,read]
  exact agree
