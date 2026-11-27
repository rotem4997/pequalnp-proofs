import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Choose an inclusion-minimal violation of the activation bound.
-- Every nonempty set of activated gates must then reach many selected pairs.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3686_691
    (minimal : ∀ (E G : Type) [DecidableEq E] [DecidableEq G]
      (gs : Finset G) (active : G → E → Bool) (k : ℕ)
      (S : Finset E),
      let seen := fun A : Finset E => gs.filter (fun g => ∃ e ∈ A, active g e = true)
      k * (seen S).card < S.card →
      ∃ A ⊆ S,
        A.card = k * (seen A).card + 1 ∧
        ∀ B ⊆ seen A, B.Nonempty →
          k * B.card < (A.filter (fun e => ∃ g ∈ B, active g e = true)).card)
    (obstruction : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      IsMinimalMonoCircuit (N+N) C →
      (∀ T : Finset (Fin N), T.card ≤ q →
        C.eval (List.ofFn (Fin.append (fun p => decide ¬ ∃ l ∈ T, I p l)
          (fun l => decide (l ∈ T)))) = false) →
      let D : Circuit := ⟨C.gates.map (fun g =>
        if g.op.eval [] = true ∧ g.inputs.length = 2 ∧ (g.inputs.all fun w =>
          decide (0 < (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD w 0)) = true
        then ⟨GateOp.or, []⟩ else g), C.output⟩
      let positive := fun e : Σ _ : Fin N, Fin N => pairInput (Fin.castAdd N e.2) (Fin.natAdd N e.1)
      let active := fun (g : Fin C.size) e =>
        !(C.wires (List.replicate (N+N) false)).getD (N+N+g.val) false &&
          gateVal (N+N) C g.val (positive e)
      ∀ S : Finset (Σ _ : Fin N, Fin N),
        (∀ e ∈ S, I e.2 e.1 ∧ C.eval (List.ofFn (positive e)) = true ∧
          D.eval (List.ofFn (positive e)) = false) →
        let G := Finset.univ.filter (fun g => ∃ e ∈ S, active g e = true)
        S.card = 44 * G.card + 1 →
        (∀ g ∈ G, 44 < (S.filter (fun e => active g e = true)).card) → False) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 = (x1 * x1 + x1).succ →     (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →       (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →         PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →           have x10 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x10 : Finset (Fin x2)) (x11 : Fin (x2 + x2)) => Fin.addCases (fun (x12 : Fin x2) => Decidable.decide ¬∃ x13 ∈ x10, x3 x12 x13) (fun (x12 : Fin x2) => Decidable.decide (x12 ∈ x10)) x11;           (∀ (x11 : Finset (Fin x2)), x11.card ≤ x1 → x5.eval (List.ofFn (x10 x11)) = Bool.false) →             have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };             have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x13) (Fin.natAdd x2 x14);             ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ x5.eval (List.ofFn (x13 x16 x15)) = Bool.true ∧ x12.eval (List.ofFn (x13 x16 x15)) = Bool.false) → (22 : ℕ) * Fintype.card { x16 : Fin x2 // (x14 x16).Nonempty } < ∑ x16 : Fin x2, (x14 x16).card → ∑ x17 : Fin x2, (x14 x17).card ≤ (44 : ℕ) * Fintype.card { x17 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x17) Bool.false = Bool.false ∧ ∃ (x18 : Fin x2), ∃ x19 ∈ x14 x18, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 (↑x17) (x13 x19 x18) = Bool.true } := by
  classical
  intro q n I inst C _horder hline hunique hmin
  dsimp only
  intro hfalse T hT _hdense
  let E := Σ _ : Fin n, Fin n
  let S : Finset E := Finset.univ.sigma T
  let positive : E → Fin (n+n) → Bool := fun e =>
    pairInput (Fin.castAdd n e.2) (Fin.natAdd n e.1)
  let active : Fin C.size → E → Bool := fun g e =>
    !(C.wires (List.replicate (n+n) false)).getD (n+n+g.val) false &&
      gateVal (n+n) C g.val (positive e)
  let seen : Finset E → Finset (Fin C.size) := fun A =>
    Finset.univ.filter (fun g => ∃ e ∈ A, active g e = true)
  have hSsize : S.card = ∑ l, (T l).card := Finset.card_sigma _ _
  have hSeen :
      Fintype.card {g : Fin C.size //
        (C.wires (List.replicate (n+n) false)).getD (n+n+g.val) false = false ∧
        ∃ l, ∃ p ∈ T l, gateVal (n+n) C g.val
          (pairInput (Fin.castAdd n p) (Fin.natAdd n l)) = true} = (seen S).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext g
    constructor
    · intro h
      obtain ⟨hz, l, p, hp, hval⟩ := (Finset.mem_filter.mp h).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ g, ⟨l, p⟩,
        Finset.mem_sigma.mpr ⟨Finset.mem_univ l, hp⟩, ?_⟩
      simpa only [active, positive, Bool.and_eq_true, Bool.not_eq_true'] using And.intro hz hval
    · intro h
      obtain ⟨e, he, hval⟩ := (Finset.mem_filter.mp h).2
      have hp := (Finset.mem_sigma.mp he).2
      simp only [active, Bool.and_eq_true, Bool.not_eq_true', positive] at hval
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, hval.1, e.1, e.2, hp, hval.2⟩
  rw [← hSsize, hSeen]
  by_contra! hfail
  obtain ⟨A, hsub, hsize, hgroups⟩ :=
    @minimal E (Fin C.size) _ _ Finset.univ active 44 S hfail
  refine obstruction q n I C hline hunique hmin hfalse A ?_ hsize ?_
  · intro e he
    exact hT e.1 e.2 (Finset.mem_sigma.mp (hsub he)).2
  · intro g hg
    have bound := hgroups {g} (Finset.singleton_subset_iff.mpr hg) (Finset.singleton_nonempty g)
    simp only [Finset.card_singleton, Nat.mul_one] at bound
    convert bound using 2
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton, exists_eq_left, active, positive]
