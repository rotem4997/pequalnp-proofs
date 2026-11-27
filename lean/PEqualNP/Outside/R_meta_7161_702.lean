import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_7161_702 :
    (
    let op := fun (q a b : Bool) => if q then a && b else a || b
    let next := fun (w : List Bool) (g : Bool × Nat × Nat) =>
      w ++ [op g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
    ∃ (k : Fin 67) (gs : List (Bool × Nat × Nat)) (i j : Nat) (q : Bool),
      gs.length ≤ 60 ∧ i < j ∧
      let t := (([2017922699736712193, 441671626652736513, 6638618254218693153, 7503322576947584545, 6499004535333270561, 7363708858196368433, 3805861441631761457, 3810365110013228241, 6488900985896903953, 15856501444234255373, 11249178357772656141, 16005122499714817565, 12978587003030151709, 7506700330288881197, 12983090672552486957, 3755758131261415951, 57377075175983] : List Nat).getD (k.val / 4) 0) >>> (16*(k.val % 4))
      ∀ s u : Finset (Fin 13),
        let x := PEqualNP.GenericRejection.incidenceInput s u
        let a := next x (t.testBit 15,0,t % 16)
        let w := gs.foldl next (next a (t.testBit 14,t / 16 % 32,t / 512 % 32))
        op q (w.getD i false) (w.getD j false) =
          PEqualNP.GenericRejection.incidenceFun
            (fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 =>
              (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)) s u) →
    (let op := fun (q a b : Bool) => if q then a && b else a || b
    let next := fun (w : List Bool) (g : Bool × Nat × Nat) =>
      w ++ [op g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
    ∀ gs : List (Bool × Nat × Nat), ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = gs.length ∧
      ∀ x : List Bool, C.wires x = gs.foldl next x) →
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ) (x7 : Bool),   PEqualNP.MetaComplexity.Monotone2 x4 ∧     x4.size ≤ (62 : ℕ) ∧       x5 < x6 ∧         have x8 : ℕ → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 x10 : Finset (Fin (13 : ℕ))) => (x4.wires (x3 x9 x10)).getD x8 Bool.false;         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => (if x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [x8 x5 x9 x10, x8 x6 x9 x10];         (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x2 x10) = Bool.false ∧ x9 (x2 x10) x10 = Bool.false) := by

  intro suffix realize
  obtain ⟨k,gs,i,j,q,hlen,hij,h⟩ := suffix
  let t := (([2017922699736712193, 441671626652736513, 6638618254218693153, 7503322576947584545, 6499004535333270561, 7363708858196368433, 3805861441631761457, 3810365110013228241, 6488900985896903953, 15856501444234255373, 11249178357772656141, 16005122499714817565, 12978587003030151709, 7506700330288881197, 12983090672552486957, 3755758131261415951, 57377075175983] : List Nat).getD (k.val / 4) 0) >>> (16*(k.val % 4))
  obtain ⟨C,hm,hsize,hw⟩ := realize
    ((t.testBit 15,0,t % 16) :: (t.testBit 14,t / 16 % 32,t / 512 % 32) :: gs)
  have hc : C.size ≤ 62 := by simp only [List.length_cons] at hsize; omega
  let E := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
  let bank := fun l : Fin 13 => Finset.univ.filter fun p => E p l
  let bits := fun s u : Finset (Fin 13) => List.ofFn fun z : Fin 26 =>
    if z.val < 13 then decide (Fin.ofNat 13 z.val ∈ s) else decide (Fin.ofNat 13 z.val ∈ u)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬E p l
  have splitInput (s u : Finset (Fin 13)) :
      bits s u = PEqualNP.GenericRejection.incidenceInput s u := by
    rfl
  let f := fun s u => (if q = true then PEqualNP.CircuitLowerBounds.GateOp.and
    else PEqualNP.CircuitLowerBounds.GateOp.or).eval
    [(C.wires (bits s u)).getD i false,(C.wires (bits s u)).getD j false]
  have bin (a b : Bool) :
      (if q = true then PEqualNP.CircuitLowerBounds.GateOp.and
       else PEqualNP.CircuitLowerBounds.GateOp.or).eval [a,b] =
        (if q then a && b else a || b) := by
    cases q <;> cases a <;> cases b <;> rfl
  have heval (s u) : f s u = PEqualNP.GenericRejection.incidenceFun bank s u := by
    unfold f
    rw [bin, splitInput, hw]
    exact h s u
  have correct (s u) : f s u = true ↔ ∃ p ∈ s, ∃ l ∈ u, E p l := by
    rw [heval]
    change (decide (∃ p ∈ s, ∃ l ∈ u, p ∈ bank l)) = true ↔ _
    simp [bank]
  refine ⟨C,i,j,q,hm,hc,hij,?_⟩
  change (∀ p l : Fin 13, E p l → f {p} {l} = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 → f s (off s) = false ∧ f (off s) s = false
  constructor
  · intro p l hp
    exact (correct _ _).2 ⟨p,by simp,l,by simp,hp⟩
  · intro s _
    constructor <;> apply Bool.eq_false_iff.mpr <;> intro he
    · obtain ⟨p,hp,l,hl,hedge⟩ := (correct _ _).1 he
      exact (Finset.mem_filter.1 hl).2 p hp hedge
    · obtain ⟨p,hp,l,hl,hedge⟩ := (correct _ _).1 he
      exact (Finset.mem_filter.1 hp).2 l hl (by simpa [E,Nat.add_comm] using hedge)
