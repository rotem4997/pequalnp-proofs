import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_582_317
    (coreSearch :
      let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      ∃ (D : Circuit) (op : GateOp) (a b : ℕ) (m : ℕ × ℕ),
        Monotone2 D ∧ D.size ≤ 25 ∧
        14 ≤ a ∧ a < b ∧ b < 14 + D.size ∧
        ((op = .or ∧ m ∈ ([(129,130),(129,260),(129,544)] : List (ℕ × ℕ)))
          ∨ (op = .and ∧ m ∈ ([(127,244),(127,432),(127,3716),(127,16256),(244,314),(244,432),
            (244,792),(244,1290),(244,3716),(244,7426),(432,660),(432,1220),(432,1548)]
          : List (ℕ × ℕ)))) ∧
        let read := fun (w : ℕ) (x : Fin 14 → Bool) => (D.wires (List.ofFn x)).getD w false
        let X := fun i : Fin 14 => m.1.testBit i.val
        let Y := fun i : Fin 14 => m.2.testBit i.val
        let F := fun x => op.eval [read a x, read b x]
        read a X ≠ read b X ∧ read a X = read b Y ∧ read b X = read a Y ∧
        (∀ x, Minimal P x → (op = .or ∧ (x = X ∨ x = Y)) ∨ F x = true) ∧
        (∀ x, Maximal (fun z => ¬ P z) x → (op = .and ∧ (x = X ∨ x = Y)) ∨ F x = false))
    (finish : ∀ (n : ℕ) (D : Circuit), Monotone2 D → ∀ (op : GateOp),
      (op = .and ∨ op = .or) → ∀ a b : ℕ,
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 1 ∧
        ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          op.eval [(D.wires (List.ofFn x)).getD a false, (D.wires (List.ofFn x)).getD b false])
    (boundary : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ P : (Fin n → Bool) → Prop,
      (∀ x, Minimal P x → C.eval (List.ofFn x) = true) →
      (∀ x, Maximal (fun z => ¬ P z) x → C.eval (List.ofFn x) = false) →
      ∀ x, C.eval (List.ofFn x) = true ↔ P x) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
  obtain ⟨D, op, a, b, m, mono, size, _, _, _, anchor, different, cross₁, cross₂, yes, no⟩ := coreSearch
  have kind : op = .and ∨ op = .or := anchor.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)
  obtain ⟨C, hC, budget, val⟩ := finish 14 D mono op kind a b
  let read := fun (w : ℕ) (x : Fin 14 → Bool) => (D.wires (List.ofFn x)).getD w false
  let X := fun i : Fin 14 => m.1.testBit i.val
  let Y := fun i : Fin 14 => m.2.testBit i.val
  have opposite : read a X ≠ read b X := different
  have swap₁ : read a Y = read b X := cross₂.symm
  have swap₂ : read b Y = read a X := cross₁.symm
  have mix (u v : Bool) (h : u ≠ v) :
      GateOp.or.eval [u,v] = true ∧ GateOp.and.eval [u,v] = false := by
    cases u <;> cases v <;> first | exact False.elim (h rfl) | exact ⟨rfl, rfl⟩
  have incidence : ∀ u v : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD u.val 0).testBit v.val = true ↔
      (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) := by decide
  refine ⟨C, hC, by omega, ?_⟩
  suffices solved : ∀ x, C.eval (List.ofFn x) = true ↔ P x by
    intro x
    simpa only [P, incidence] using solved x
  apply boundary 14 C hC P
  · intro x hx
    rw [val]
    rcases yes x hx with ⟨rfl, hx | hx⟩ | ok
    · subst x
      exact (mix _ _ opposite).1
    · subst x
      exact (mix _ _ (show read a Y ≠ read b Y by rw [swap₁, swap₂]; exact Ne.symm opposite)).1
    · exact ok
  · intro x hx
    rw [val]
    rcases no x hx with ⟨rfl, hx | hx⟩ | ok
    · subst x
      exact (mix _ _ opposite).2
    · subst x
      exact (mix _ _ (show read a Y ≠ read b Y by rw [swap₁, swap₂]; exact Ne.symm opposite)).2
    · exact ok
