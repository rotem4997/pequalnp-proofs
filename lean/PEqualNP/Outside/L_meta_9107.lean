import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9107

open PEqualNP.CircuitLowerBounds

private def appendGate (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

/-- Tracing one output slot back through a two-input gate adds at most one required wire. -/
private theorem wireSupport (gs : List Gate)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) (n : ℕ) (T : Finset ℕ) :
    ∃ U : Finset ℕ, U.card ≤ T.card+gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ U, x.getD i false = y.getD i false) →
        ∀ i ∈ T, (gs.foldl appendGate x).getD i false = (gs.foldl appendGate y).getD i false := by
  induction gs generalizing n T with
  | nil => exact ⟨T, by simp, fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨U, hcard, hU⟩ := ih (fun g' hg' => fan g' (List.mem_cons_of_mem _ hg')) (n+1) T
    let V := if n ∈ U then U.erase n ∪ g.inputs.toFinset else U
    have hcardV : V.card ≤ U.card+1 := by
      by_cases hn : n ∈ U
      · simp only [V, ite_eq_left hn]
        have hc := Finset.card_union_le (U.erase n) g.inputs.toFinset
        have he := Finset.card_erase_of_mem hn
        have hpos := Finset.card_pos.mpr ⟨n,hn⟩
        have hi := g.inputs.toFinset_card_le
        have hg := fan g (List.mem_cons_self ..)
        omega
      · simp [V,hn]
    refine ⟨V, by simp only [List.length_cons]; omega, ?_⟩
    intro x y hx hy hxy
    apply hU (appendGate x g) (appendGate y g) (by simp [appendGate,hx]) (by simp [appendGate,hy])
    intro i hi
    rcases lt_trichotomy i n with h | rfl | h
    · have mem : i ∈ V := by
        by_cases hn : n ∈ U
        · simp only [V, ite_eq_left hn]
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h.ne,hi⟩)
        · simpa [V,hn] using hi
      simpa only [appendGate, List.getD_append _ _ _ _ (hx ▸ h : i < x.length),
        List.getD_append _ _ _ _ (hy ▸ h : i < y.length)] using hxy i mem
    · have eq : g.inputs.map (fun i => x.getD i false) = g.inputs.map (fun i => y.getD i false) := by
        apply List.map_congr_left
        intro j hj
        apply hxy
        simp [V,hi,hj]
      simp only [appendGate, List.getD_append_right _ _ _ _ (le_of_eq hx),
        List.getD_append_right _ _ _ _ (le_of_eq hy), hx, hy, Nat.sub_self, List.getD_cons_zero, eq]
    · rw [List.getD_eq_default _ _ (by simp [appendGate,hx]; omega),
          List.getD_eq_default _ _ (by simp [appendGate,hy]; omega)]

/-- Every sensitive input belongs to any determining set for the output. -/
theorem sensitive_size_bound {n : ℕ} (C : Circuit)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (sens : ∀ i : Fin n, ∃ x : Fin n → Bool,
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x i false))) :
    n ≤ C.size + 1 := by
  classical
  obtain ⟨U, card, agree⟩ := wireSupport C.gates fan n {C.output}
  have all : Finset.range n ⊆ U := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    let i : Fin n := ⟨k, hkn⟩
    by_contra habs
    obtain ⟨x, hx⟩ := sens i
    apply hx
    apply agree _ _ (by simp) (by simp) _ _ (Finset.mem_singleton_self _)
    intro j hj
    by_cases hjn : j < n
    · have hne : (⟨j,hjn⟩ : Fin n) ≠ i := by
        intro h
        have eq : j = k := congrArg Fin.val h
        exact habs (eq ▸ hj)
      simp [List.getD_eq_getElem?_getD, hjn, Function.update_of_ne hne]
    · simp [List.getD_eq_getElem?_getD, hjn]
  have h := Finset.card_le_card all
  simpa only [Finset.card_range, Finset.card_singleton, Nat.add_comm 1,
    Circuit.size] using h.trans card

private abbrev incident (x : Fin 14 → Bool) : Prop :=
  ∃ (p l : Fin 7), (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

private def diagonalInput (i k : Fin 14) : Bool := decide (i.val % 7 = k.val % 7)

/-- The diagonal edge through each input witnesses its sensitivity. -/
theorem fano_size_bound (C : Circuit) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (computes : ∀ x, C.eval (List.ofFn x) = true ↔ incident x) :
    13 ≤ C.size := by
  have diag : ∀ i : Fin 14,
      incident (diagonalInput i) ∧ ¬incident (Function.update (diagonalInput i) i false) := by
    decide
  have h := sensitive_size_bound C fan (fun i : Fin 14 => by
    refine ⟨diagonalInput i, ?_⟩
    intro same
    exact (diag i).2 ((computes _).1 (same ▸ (computes _).2 (diag i).1)))
  omega

end PEqualNP.Outside.L_meta_9107

theorem PEqualNP.Outside.L_meta_9107 :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∃ x5 ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (11 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (8 : ℕ))], PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5.1, x5.2] : PEqualNP.CircuitLowerBounds.Gate }) → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7)) [((0 : ℕ), (7 : ℕ))] → (¬∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x8) → False := by
  intro C _ ao _ _ computes _ alone
  have lower := PEqualNP.Outside.L_meta_9107.fano_size_bound C
    (fun g hg => (ao.2.2 g hg).le) computes
  have index : 1 < C.gates.length := by
    change 13 ≤ C.gates.length at lower
    omega
  exact alone ⟨C.gates[1], List.getElem?_eq_getElem index⟩
