import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3239_73
    (h1 : ∀ C : PEqualNP.MetaComplexity.BinaryCircuit, C.size ≤ 13 →
    (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) → (∀ g : PEqualNP.MetaComplexity.BinaryGate, C.gates[0]? = some g →
      (∃ b : Bool, g.op = fun u v => (u == false) && (v == b)) ∧
      (let p := fun i : Nat => [1,0,5,8,6,2,4,7,3].getD i i; [g.left,g.right] ≤ [p g.left,p g.right])) →
    ∃ (cs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24), cs.length = C.size ∧ (∀ c ∈ cs.head?.toList, c.2.2.1 = false ∧
      (let p := fun i : Nat => [1,0,5,8,6,2,4,7,3].getD i i; [c.1.val,c.2.1.val] ≤ [p c.1.val,p c.2.1.val])) ∧
    ∀ w : List Bool, w.length = 11 → w.getD 10 false = false →
      (cs.foldl (fun (v : List Bool) c => v ++ [(v.getD c.1.val false == c.2.2.1) && (v.getD c.2.1.val false == c.2.2.2)]) w).getD o.val false = C.eval w)
    (h2 : ∀ (cs : List (Fin 24 × Fin 24 × Bool × Bool)), cs.length ≤ 13 → (∀ c ∈ cs.head?.toList, c.2.2.1 = false ∧
      (let p := fun i : Nat => [1,0,5,8,6,2,4,7,3].getD i i; [c.1.val,c.2.1.val] ≤ [p c.1.val,p c.2.1.val])) →
    ∀ (o : Fin 24) (p : Bool), ∃ r : Fin 512,
      let x := fun i : Fin 9 => (BitVec.ofNat 9 r.val).getLsbD i.val
      let w := List.ofFn x ++ [x 0 || x 1,false]
      ((cs.foldl (fun (v : List Bool) c => v ++ [(v.getD c.1.val false == c.2.2.1) && (v.getD c.2.1.val false == c.2.2.2)]) w).getD o.val false != p) ≠ (([0xffeafaeaffeaf8c8,0xffeefeeeffeefccc,0xfffffffffffaf8f8,0xfffffffffffefcfc,0xffffffffffeaffc8,0xffffffffffffffff,0xfffffffffffafff8,0xffffffffffffffff] : List Nat).getD (r.val / 64) 0).testBit (r.val % 64)) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C p ops canonical computes
  by_contra h
  have small : C.size ≤ 13 := by omega
  obtain ⟨cs,o,length,bounded,agree⟩ := h1 C small ops canonical
  obtain ⟨r,different⟩ := h2 cs (length.trans_le small) bounded o p
  let x := fun i : Fin 9 => (BitVec.ofNat 9 r.val).getLsbD i.val
  let w := List.ofFn x ++ [x 0 || x 1,false]
  have hz : w.getD 10 false = false := by
    rw [show w = List.ofFn x ++ [x 0 || x 1,false] from rfl,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
    simp
  have hx := agree w (by simp [w]) hz
  have truth : ∀ r : Fin 512, (let x := fun i : Fin 9 => (BitVec.ofNat 9 r.val).getLsbD i.val; (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = (([0xffeafaeaffeaf8c8,0xffeefeeeffeefccc,0xfffffffffffaf8f8,0xfffffffffffefcfc,0xffffffffffeaffc8,0xffffffffffffffff,0xfffffffffffafff8,0xffffffffffffffff] : List Nat).getD (r.val / 64) 0).testBit (r.val % 64) := by decide +kernel
  exact different ((congrArg (fun v : Bool => v != p) hx).trans ((computes x).trans (truth r)))
