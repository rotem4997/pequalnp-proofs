import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2056_773
    (suffix : ∃ (op : GateOp) (a b : Fin 26) (D : Circuit),
      (op = GateOp.and ∨ op = GateOp.or) ∧
      (a, b) ∈ ([(0, 1), (0, 13), (0, 15)] : List (Fin 26 × Fin 26)) ∧
      Monotone2 D ∧ D.size ≤ 62 ∧
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
      let read := fun s t => D.eval (List.ofFn (vec s t) ++ [op.eval [vec s t a, vec s t b]])
      (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
        ∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false)
    (prepend : ∀ (n k : ℕ) (a b : Fin n) (op : GateOp) (D : Circuit),
      (op = GateOp.and ∨ op = GateOp.or) → Monotone2 D → D.size ≤ k →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k + 1 ∧
        ∀ x : Fin n → Bool,
          C.eval (List.ofFn x) = D.eval (List.ofFn x ++ [op.eval [x a, x b]])) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  obtain ⟨op, a, b, D, allowedOp, _, monotoneD, sizeD, tests⟩ := suffix
  obtain ⟨C, monotoneC, sizeC, eval⟩ := prepend 26 62 a b op D allowedOp monotoneD sizeD
  refine ⟨C, monotoneC, sizeC, ?_⟩
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
  let read := fun s t => D.eval (List.ofFn (vec s t) ++ [op.eval [vec s t a, vec s t b]])
  change (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false) at tests
  change (∀ p l : Fin 13, near p l → C.eval (List.ofFn (vec {p} {l})) = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 →
      C.eval (List.ofFn (vec s (off s))) = false ∧ C.eval (List.ofFn (vec (off s) s)) = false)
  constructor
  · intro p l h
    rw [eval]
    exact tests.1 p l h
  · intro s h
    rw [eval, eval]
    exact tests.2 s h
