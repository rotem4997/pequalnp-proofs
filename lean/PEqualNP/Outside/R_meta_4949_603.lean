import PEqualNP.Defs

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_4949_603
    (compile : (let F := (Fin 40 × Fin 13) → Bool
    let m := fun (a : List F) (x : Fin 40 × Fin 13) => a.all fun k => k x
    ∀ (D : List F) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C → ∃ V o : List F,
      (∀ i : Fin V.length, ∃ a b : List F,
        (∀ k ∈ a ++ b, k ∈ ((fun _ => false) :: D) ++ V.take i.val) ∧
        V.get i = fun x => m a x || m b x) ∧ V.length = {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧
      (∀ k ∈ o, k ∈ ((fun _ => false) :: D) ++ V) ∧ ∀ x, m o x = C.eval (D.map fun k => k x)))
    (exclude : (let F := (Fin 40 × Fin 13) → Bool
    let m := fun (a : List F) (x : Fin 40 × Fin 13) => a.all fun k => k x
    let num := fun (r : ℕ) => (([32678607657645063, 77760804915549219, 95792838600631367, 152142863240631393, 307662261176120457, 618489937847936275] : List ℕ).getD (r/6) 0 >>> (10*(r % 6))) % 1024
    let inc := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
    let col := fun (k : Fin 26) (x : Fin 40 × Fin 13) =>
      let j := x.2
      let r := x.1.val
      if r < 4 then
        let b := Fin.ofNat 13 (([0,1,3,9] : List ℕ).getD r 0)
        decide (k = Fin.castAdd 13 (j+b) ∨ k = Fin.natAdd 13 j)
      else
        let ps := Finset.univ.filter fun p : Fin 13 => (num (r-4)).testBit (p-j).val
        decide ((∃ p ∈ ps, k = Fin.castAdd 13 p) ∨
          ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ p ∈ ps, ¬inc p l)
    let D := List.ofFn col
    ∀ V o : List F, (∀ i : Fin V.length, ∃ a b : List F,
        (∀ k ∈ a ++ b, k ∈ ((fun _ => false) :: D) ++ V.take i.val) ∧
        V.get i = fun x => m a x || m b x) → (∀ k ∈ o, k ∈ ((fun _ => false) :: D) ++ V) →
      (∀ x : Fin 40 × Fin 13, m o x = decide (x.1.val < 4)) → 51 ≤ V.length)) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) →       (∀ (x4 : ℕ) (x5 : Fin (13 : ℕ)),           (x4 ∈               have x6 : List ℕ :=                 have x6 : List ℕ :=                   have x6 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];                   (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x6;                 have x7 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x6;                 (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x7;               have x7 : List ℕ :=                 have x7 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x6;                 (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x7;               have x8 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x7;               (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x8) →             have x7 : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | x4.testBit ↑(x7 - x5) = Bool.true};             (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ ∀ x10 ∈ x7, ¬(x10 = x9 ∨ x10 = x9 + (1 : Fin (13 : ℕ)) ∨ x10 = x9 + (3 : Fin (13 : ℕ)) ∨ x10 = x9 + (9 : Fin (13 : ℕ))))) = Bool.false) →         (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hc hp hn
  let num := fun (r : ℕ) => (([32678607657645063, 77760804915549219, 95792838600631367, 152142863240631393, 307662261176120457, 618489937847936275] : List ℕ).getD (r/6) 0 >>> (10*(r % 6))) % 1024
  let inc := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let col := fun (k : Fin 26) (x : Fin 40 × Fin 13) =>
      let j := x.2
      let r := x.1.val
      if r < 4 then
        let b := Fin.ofNat 13 (([0,1,3,9] : List ℕ).getD r 0)
        decide (k = Fin.castAdd 13 (j+b) ∨ k = Fin.natAdd 13 j)
      else
        let ps := Finset.univ.filter fun p : Fin 13 => (num (r-4)).testBit (p-j).val
        decide ((∃ p ∈ ps, k = Fin.castAdd 13 p) ∨
          ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ p ∈ ps, ¬inc p l)
  let D := List.ofFn col
  obtain ⟨V,o,hV,hL,hO,hE⟩ := compile D C hc
  rw [←hL]
  apply exclude V o hV hO
  intro x
  rw [hE]
  rcases x with ⟨r,j⟩
  have hinput : (D.map fun k => k (r,j)) = List.ofFn (fun k => col k (r,j)) := by simp [D]
  rw [hinput]
  change PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => col k (r,j)) = decide (r.val<4)
  by_cases hr : r.val < 4
  · simp only [col, hr, if_true, decide_true]
    let off := fun (i : Fin 4) => Fin.ofNat 13 (([0,1,3,9] : List ℕ).getD i.val 0)
    have hi : ∀ (i : Fin 4) (j : Fin 13), inc (j+off i) j := by decide +kernel
    exact hp (j+off ⟨r.val,hr⟩) j (hi ⟨r.val,hr⟩ j)
  · simp only [col, hr, if_false, decide_false]
    let S : List ℕ := [7, 13, 19, 21, 25, 29, 35, 37, 39, 41, 67, 69, 71, 73, 77, 81, 83, 85, 97, 101, 105, 131, 133, 135, 137, 141, 195, 201, 265, 273, 275, 281, 297, 329, 337, 549]
    have hM : ∀ i : Fin 36, num i.val ∈ S := by decide +kernel
    let i : Fin 36 := ⟨r.val-4,by have := r.isLt; omega⟩
    exact hn (num i.val) j (hM i)
