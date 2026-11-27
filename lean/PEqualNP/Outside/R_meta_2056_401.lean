import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2056_401
    (core :
      let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ e p l
      let v := fun s t : Finset (Fin 13) => List.ofFn fun i : Fin 26 =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      ∃ (D : Circuit) (a b : ℕ) (q : Bool),
        Monotone2 D ∧ D.size ≤ 62 ∧ a < b ∧
        let read := fun w s t => (D.wires (v s t)).getD w false
        let f := fun s t => (if q then GateOp.and else GateOp.or).eval [read a s t, read b s t]
        (∀ p l, e p l → f {p} {l} = true) ∧
        (∀ s, s.card ≤ 3 → f s (off s) = false ∧ f (off s) s = false))
    (finish : ∀ (n : ℕ) (D : Circuit), Monotone2 D → ∀ (q : Bool) (a b : ℕ),
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 1 ∧
        ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          (if q then GateOp.and else GateOp.or).eval
            [(D.wires (List.ofFn x)).getD a false, (D.wires (List.ofFn x)).getD b false]) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false
  := by
  let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ e p l
  let vec := fun s t : Finset (Fin 13) => fun i : Fin 26 =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  obtain ⟨D,a,b,q,hD,sz,_,edges,blanks⟩ := core
  obtain ⟨C,hC,hsize,heval⟩ := finish 26 D hD q a b
  refine ⟨C,hC,by omega,?_⟩
  change (∀ p l, e p l → C.eval (List.ofFn (vec {p} {l})) = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 →
      C.eval (List.ofFn (vec s (off s))) = false ∧ C.eval (List.ofFn (vec (off s) s)) = false
  constructor
  · intro p l h
    rw [heval]
    exact edges p l h
  · intro s hs
    constructor
    · rw [heval]
      exact (blanks s hs).1
    · rw [heval]
      exact (blanks s hs).2
