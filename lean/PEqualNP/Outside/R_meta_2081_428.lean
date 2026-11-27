import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2081_428
    (sparse : let z := fun (x : Fin 13 → Bool) (j : Fin 13) => !(x j || x (j+1) || x (j+3) || x (j+9))
      ∀ x : Fin 13 → Bool, (List.ofFn (x)).count true ≤ 3 ∨
        (List.ofFn (z x)).count true ≤ 3)
    (candidate : let z := fun (x : Fin 13 → Bool) (j : Fin 13) => !(x j || x (j+1) || x (j+3) || x (j+9))
      let input := fun p l : Fin 13 → Bool => List.ofFn (Fin.addCases p l)
      let one := fun p i : Fin 13 => decide (i=p)
      ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ p l, z (one p) l = false → C.eval (input (one p) (one l)) = true) ∧
        (∀ y : Fin 13 → Bool, (List.ofFn (y)).count true ≤ 3 →
          C.eval (input y (z y)) = false ∧
          C.eval (input (fun p => !(y p || y (p-1) || y (p-3) || y (p-9))) y) = false) ∧
        ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       C.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := C.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 C.output = Bool.false) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  dsimp only at sparse candidate ⊢
  obtain ⟨C, hs, hlegal, hnodup, hpos, htest, htrace⟩ := candidate
  refine ⟨C, hs, hlegal, hnodup, ?_, ?_, htrace⟩
  · intro p l hp
    apply hpos
    rcases hp with h | h | h | h <;> subst p <;> simp
  intro x hmax
  let z : Fin 13 → Bool := fun j => !(x j || x (j+1) || x (j+3) || x (j+9))
  change C.eval (List.ofFn (Fin.addCases x z)) = false
  rcases sparse x with hsmall | hsmall
  · exact (htest x hsmall).1
  · have recover : (fun p => !(z p || z (p-1) || z (p-3) || z (p-9))) = x := by
      funext p
      cases hp : x p with
      | true =>
        have h0 : z p = false := by simp [z,hp]
        have h1 : z (p-1) = false := by simp [z,hp]
        have h3 : z (p-3) = false := by simp [z,hp]
        have h9 : z (p-9) = false := by simp [z,hp]
        simp [h0,h1,h3,h9]
      | false =>
        obtain ⟨l, hpl, hl⟩ := hmax p hp
        change z l = true at hl
        rcases hpl with h | h | h | h <;> subst p <;> simp [hl]
    have ok := (htest z hsmall).2
    rw [recover] at ok
    exact ok
