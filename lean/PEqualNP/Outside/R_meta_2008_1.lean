import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Evaluate each wire on the grid of point and line assignments.
Only marked steps may use an unrestricted intersection. The geometry
is tested on incident singleton pairs and one negative per sparse line set. -/
theorem PEqualNP.Outside.R_meta_2008_1
  (compile : ∀ (N : ℕ) (C : Circuit) (marked : Finset ℕ),
    Monotone2 C → (∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i) → (∀ i g, C.gates[i]? = some g → g.op = GateOp.and → i ∉ marked →
      ¬((∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
          (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
          (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) ∨
        (∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
          (C.wires (List.replicate N false ++ List.ofFn x)).getD w false ≠
          (C.wires (List.replicate N true ++ List.ofFn x)).getD w false))) →
    ∃ V : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)), (∀ p : Fin N, V p.val = {z | z.1 p = true} ∧ V (N + p.val) = {z | z.2 p = true}) ∧
    (∀ i < C.size, ∃ a < N + N + i, ∃ b < N + N + i,
      let W := V (N + N + i)
      W = V a ∪ V b ∨ W = V a ∨ W = ∅ ∨
        (W = V a ∩ V b ∧ (i ∈ marked ∨ ∃ A B : Set (Fin N → Bool),
          V a = A ×ˢ Set.univ ∧ V b = Set.univ ×ˢ B))) ∧
    ∀ P L, (P,L) ∈ V C.output ↔ circuitFun (N+N) C (Fin.append P L) = true)
  (gridLower : ∀ (q N : ℕ) (Inc : Fin N → Fin N → Prop) [DecidableRel Inc],
    100 < q → N = q ^ 2 + q + 1 →
    (∀ l, Fintype.card {p : Fin N // Inc p l} = q + 1) →
    (∀ p r, p ≠ r → ∃! l, Inc p l ∧ Inc r l) →
    ∀ (s o : ℕ) (marked : Finset ℕ) (V : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))), o < N+N+s →
    (∀ p : Fin N, V p.val = {z | z.1 p = true} ∧ V (N + p.val) = {z | z.2 p = true}) →
    (∀ i < s, ∃ a < N + N + i, ∃ b < N + N + i,
      let W := V (N + N + i)
      W = V a ∪ V b ∨ W = V a ∨ W = ∅ ∨
        (W = V a ∩ V b ∧ (i ∈ marked ∨ ∃ A B : Set (Fin N → Bool),
          V a = A ×ˢ Set.univ ∧ V b = Set.univ ×ˢ B))) →
    (∀ p l, Inc p l → ((fun u => decide (u=p)), (fun v => decide (v=l))) ∈ V o) →
    (∀ L : Fin N → Bool, Fintype.card {l : Fin N // L l = true} ≤ q →
      ((fun p => decide (¬∃ l, Inc p l ∧ L l = true)), L) ∉ V o) →
    100 * marked.card < N*q → N*q ≤ 100*s) :
  ∀ (q N : ℕ) (Inc : Fin N → Fin N → Prop) [DecidableRel Inc] (C : Circuit),
    100 < q → N = q ^ 2 + q + 1 →
    (∀ l, Fintype.card {p : Fin N // Inc p l} = q + 1) →
    (∀ p r, p ≠ r → ∃! l, Inc p l ∧ Inc r l) →
    Monotone2 C → C.output < N + N + C.size →
    (∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i) →
    (∀ p l, Inc p l →
      circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true) →
    (∀ x, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬∃ p l, Inc p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) →
    ∀ marked : Finset ℕ,
      (∀ i g, C.gates[i]? = some g → g.op = GateOp.and → i ∉ marked →
        ¬((∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
              (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
              (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) ∨
          (∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
              (C.wires (List.replicate N false ++ List.ofFn x)).getD w false ≠
              (C.wires (List.replicate N true ++ List.ofFn x)).getD w false))) →
      100 * marked.card < N * q → N * q ≤ 100 * C.size := by
  intro q N Inc inst C hq hN hd hu hm ho hw hy hn marked hmarked hsmall
  obtain ⟨V, hbase, hstep, hout⟩ := compile N C marked hm hw hmarked
  apply gridLower q N Inc hq hN hd hu C.size C.output marked V ho hbase hstep _ _ hsmall
  · intro p l hp
    apply (hout _ _).2
    have hx : Fin.append (fun u => decide (u=p)) (fun v => decide (v=l)) =
        (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) := by
      funext z
      refine Fin.addCases (fun a => ?_) (fun b => ?_) z
      · have hne : Fin.castAdd N a ≠ Fin.natAdd N l := by
          intro e
          have hv := congrArg Fin.val e
          change a.val = N + l.val at hv
          omega
        simp only [Fin.append_left, hne, or_false, Fin.castAdd_inj]
      · have hne : Fin.natAdd N b ≠ Fin.castAdd N p := by
          intro e
          have hv := congrArg Fin.val e
          change N + b.val = p.val at hv
          omega
        have hiff : Fin.natAdd N b = Fin.natAdd N l ↔ b=l := by
          constructor
          · intro e
            apply Fin.ext
            have hv := congrArg Fin.val e
            change N+b.val=N+l.val at hv
            omega
          · rintro rfl
            rfl
        simp only [Fin.append_right, hne, false_or, hiff]
    rw [hx]
    exact hy p l hp
  · intro L hL hacc
    let P (p : Fin N) := decide (¬∃ l, Inc p l ∧ L l = true)
    have hnone : ¬ ∃ p l, Inc p l ∧ Fin.append P L (Fin.castAdd N p) = true ∧
        Fin.append P L (Fin.natAdd N l) = true := by
      rintro ⟨p,l,hi,hp,hl⟩
      rw [Fin.append_left] at hp
      rw [Fin.append_right] at hl
      exact (of_decide_eq_true hp) ⟨l,hi,hl⟩
    have hz := hn (Fin.append P L) (by simpa only [Fin.append_right] using hL) hnone
    have ht := (hout P L).1 hacc
    simp [ht] at hz
