import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_2828_1
    (normalize :
      let signed (C : PEqualNP.MetaComplexity.BinaryCircuit) : Prop :=
        ∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
      let ordered (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) : Prop :=
        ∀ j : Fin C.size, (C.gates.get j).left < (C.gates.get j).right ∧
          (C.gates.get j).right < n + j.val
      ∀ (n : ℕ) (C : BinaryCircuit) (p : Bool), signed C →
        ∃ (D : BinaryCircuit) (s : Bool), D.size ≤ C.size ∧ signed D ∧ ordered n D ∧
          (D.size = 0 ∨ D.output = n + D.size - 1) ∧
          ∀ w : List Bool, w.length = n →
            (D.eval w != s) = (C.eval (w ++ [false]) != p))
    (withPrefed :
      let signed (C : PEqualNP.MetaComplexity.BinaryCircuit) : Prop :=
        ∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
      let ordered (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) : Prop :=
        ∀ j : Fin C.size, (C.gates.get j).left < (C.gates.get j).right ∧
          (C.gates.get j).right < n + j.val
      let target (x : Fin 9 → Bool) : Bool :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit) (s : Bool) (h : 0 < D.size),
        signed D → ordered 10 D → D.output = 10 + D.size - 1 →
        (D.gates.get ⟨0, h⟩).right = 9 →
        (∀ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [x 0 || x 1]) != s) = target x) →
        14 ≤ D.size)
    (withoutPrefed :
      let signed (C : PEqualNP.MetaComplexity.BinaryCircuit) : Prop :=
        ∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
      let ordered (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) : Prop :=
        ∀ j : Fin C.size, (C.gates.get j).left < (C.gates.get j).right ∧
          (C.gates.get j).right < n + j.val
      let target (x : Fin 9 → Bool) : Bool :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit) (s : Bool) (h : 0 < D.size),
        signed D → ordered 10 D → D.output = 10 + D.size - 1 →
        (D.gates.get ⟨0, h⟩).right < 9 →
        (∀ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [x 0 || x 1]) != s) = target x) →
        14 ≤ D.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C p hSigned hEval
  obtain ⟨D, s, hSize, hShape, hOrdered, hOutput, hTransfer⟩ := normalize 10 C p hSigned
  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]
  let target (x : Fin 9 → Bool) : Bool :=
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have form (x : Fin 9 → Bool) : target x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
       x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
       x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    simp only [target, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] <;> rfl
  have hCorrect (x : Fin 9 → Bool) : (D.eval (row x) != s) = target x :=
    (hTransfer (row x) (by simp [row])).trans ((hEval x).trans (form x).symm)
  have nonempty : D.size ≠ 0 := by
    intro hz
    have hlen : D.gates.length = 0 := hz
    have hnil : D.gates = [] := List.eq_nil_of_length_eq_zero hlen
    have hRead (x : Fin 9 → Bool) : D.eval (row x) = (row x).getD D.output false := by
      change (D.gates.foldl (fun w g => w ++
        [g.op (w.getD g.left false) (w.getD g.right false)]) (row x)).getD D.output false = _
      rw [hnil]
      rfl
    have tracks (x : Fin 9 → Bool) : ((row x).getD D.output false != s) = target x := by
      rw [← hRead x]
      exact hCorrect x
    let z : Fin 9 → Bool := fun _ => false
    let a : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 3)
    let b : Fin 9 → Bool := fun i => decide (i = 5 ∨ i = 7)
    by_cases inside : D.output < 10
    · have fails : ∀ (j : Fin 10) (q : Bool),
          ((row z).getD j.val false != q) ≠ target z ∨
          ((row a).getD j.val false != q) ≠ target a ∨
          ((row b).getD j.val false != q) ≠ target b := by decide +kernel
      rcases fails ⟨D.output, inside⟩ s with bad | bad | bad
      · exact bad (tracks z)
      · exact bad (tracks a)
      · exact bad (tracks b)
    · have absent (x : Fin 9 → Bool) : (row x).getD D.output false = false := by
        have h : (row x).length ≤ D.output := by simpa [row] using Nat.le_of_not_gt inside
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
      cases s
      · have bad := tracks a
        rw [absent, show target a = true by decide +kernel] at bad
        exact Bool.noConfusion bad
      · have bad := tracks z
        rw [absent, show target z = false by decide +kernel] at bad
        exact Bool.noConfusion bad
  have hPos : 0 < D.size := Nat.pos_of_ne_zero nonempty
  have last := hOutput.resolve_left nonempty
  have rightBound : (D.gates.get ⟨0, hPos⟩).right < 10 := (hOrdered ⟨0, hPos⟩).2
  by_cases prefed : (D.gates.get ⟨0, hPos⟩).right = 9
  · exact (withPrefed D s hPos hShape hOrdered last prefed hCorrect).trans hSize
  · have raw : (D.gates.get ⟨0, hPos⟩).right < 9 := by omega
    exact (withoutPrefed D s hPos hShape hOrdered last raw hCorrect).trans hSize
