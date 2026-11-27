import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fix the gate count and the output wire while preserving both evaluation and line degree.
theorem PEqualNP.Outside.R_meta_4582_634
    (normalize :
    ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
      (∀ p : Fin 13, circuitFun 26 C (fun i => Fin.addCases
        (fun q : Fin 13 => decide (q = p)) (fun q : Fin 13 => decide (q = p)) i) = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size = 63 ∧ D.output = 88 ∧
        (∀ b ∈ D.gates.zipIdx, ∀ a ∈ b.1.inputs, a < 26 + b.2 ∨ a = 89) ∧
        (∀ x, circuitFun 26 D x = circuitFun 26 C x) ∧
        ∀ marked : Finset ℕ, D.lineDeg 26 marked = C.lineDeg 26 marked)
    (lower :
    let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false; have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x8 : ℕ := x7.lineDeg (26 : ℕ) (Finset.range (13 : ℕ));   have x9 : ℕ := x7.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));   (2 : ℕ) ≤ Min.min x8 x9 ∧ (3 : ℕ) ≤ Max.max x8 x9; have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x9 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 fun (x10 : Fin (26 : ℕ)) => x9.testBit ↑x10) = Bool.true; ∀ D : Circuit, Monotone2 D → D.size = 63 → D.output = 88 →
      (∀ b ∈ D.gates.zipIdx, ∀ a ∈ b.1.inputs, a < 26 + b.2 ∨ a = 89) →
      x6 D → x7 D → x8 D → False) :
    let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false; have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x8 : ℕ := x7.lineDeg (26 : ℕ) (Finset.range (13 : ℕ));   have x9 : ℕ := x7.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));   (2 : ℕ) ≤ Min.min x8 x9 ∧ (3 : ℕ) ≤ Max.max x8 x9; have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x9 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 fun (x10 : Fin (26 : ℕ)) => x9.testBit ↑x10) = Bool.true; ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → x6 x9 → x7 x9 → x8 x9 → (64 : ℕ) ≤ x9.size := by
  intro V S I E G ok degree accepted C mono good hard hit
  by_contra! short
  have diagonal (p : Fin 13) : circuitFun 26 C (fun i => Fin.addCases
      (fun q : Fin 13 => decide (q = p)) (fun q : Fin 13 => decide (q = p)) i) = true := by
    have hp := good.1 p p (show I p p from Or.inl rfl)
    change (circuitFun 26 C fun i => Fin.addCases
      (fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13))))
      (fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) i) = true at hp
    simpa only [Finset.mem_singleton] using hp
  obtain ⟨D, dm, ds, dout, inputs, eval, deg⟩ := normalize C mono (by omega) diagonal
  apply lower D dm ds dout inputs
  · change (∀ p l, I p l → E D {p} {l} = true) ∧ ∀ P T, G P T → E D P T = false
    have hEval (P T : S) : E D P T = E C P T := eval _
    exact ⟨fun p l hp => (hEval {p} {l}).trans (good.1 p l hp),
      fun P T hPT => (hEval P T).trans (good.2 P T hPT)⟩
  · change 2 ≤ min (D.lineDeg 26 (Finset.range 13)) (D.lineDeg 26 (Finset.Ico 13 26)) ∧
      3 ≤ max (D.lineDeg 26 (Finset.range 13)) (D.lineDeg 26 (Finset.Ico 13 26))
    rw [deg, deg]
    exact hard
  · obtain ⟨m, hm, he⟩ := hit
    exact ⟨m, hm, (eval _).trans he⟩
