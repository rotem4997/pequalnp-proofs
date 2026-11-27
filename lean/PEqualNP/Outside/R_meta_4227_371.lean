import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4227_371
    (hmono : ∀ C : Circuit, Monotone2 C → Monotone (fun x : Fin 42 → Bool => C.eval (List.ofFn x)))
    (hcert :
      let E := fun u v : Fin 42 => u.val < 21 ∧ 21 < v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack 42 C ∧ C.output < 42 + C.size ∧ C.size ≤ 118 ∧
        (∀ i : Fin 42, i.val ∈ ([0, 1, 4, 14] : List ℕ) →
          ∃ g ∈ C.gates, i.val ∈ g.inputs) ∧
        (∀ u v, E u v → C.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true) ∧
        (∀ s : Finset (Fin 42), (∀ v ∈ s, 21 < v.val) →
          (∀ v : Fin 42, 21 < v.val → (∀ u, E u v → ∃ w ∈ s, E u w) → v ∈ s) →
          C.eval (List.ofFn (fun i => decide (i.val = 21 ∨ i ∈ s ∨
            (i.val < 21 ∧ ∀ v ∈ s, ¬ E i v)))) = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (42 : ℕ) x1 ∧ x1.output < (42 : ℕ) + x1.size ∧ x1.size ≤ (118 : ℕ) ∧ (∀ (x2 : Fin (42 : ℕ)), ↑x2 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (14 : ℕ)] → ∃ x4 ∈ x1.gates, ↑x2 ∈ x4.inputs) ∧ ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) < ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  let E (u v : Fin 42) := u.val < 21 ∧ 21 < v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  obtain ⟨C, hC, hback, hout, hsize, hreads, hpositive, hnegative⟩ := hcert
  refine ⟨C, hC, hback, hout, hsize, hreads, ?_⟩
  have mono := hmono C hC
  intro x
  change C.eval (List.ofFn x) = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true
  constructor
  · intro hx
    by_contra hno
    let active := Finset.univ.filter (fun v : Fin 42 => 21 < v.val ∧ x v = true)
    let closed := Finset.univ.filter
      (fun v : Fin 42 => 21 < v.val ∧ ∀ u, E u v → ∃ w ∈ active, E u w)
    have active_mem {v : Fin 42} : v ∈ active ↔ 21 < v.val ∧ x v = true := by
      simp [active]
    have closed_mem {v : Fin 42} :
        v ∈ closed ↔ 21 < v.val ∧ ∀ u, E u v → ∃ w ∈ active, E u w := by
      simp [closed]
    have sub {v : Fin 42} (hv : v ∈ active) : v ∈ closed :=
      closed_mem.mpr ⟨(active_mem.mp hv).1, fun u hu => ⟨v, hv, hu⟩⟩
    have satClosed (v : Fin 42) (hv : 21 < v.val)
        (h : ∀ u, E u v → ∃ w ∈ closed, E u w) : v ∈ closed := by
      apply closed_mem.mpr
      refine ⟨hv, fun u hu => ?_⟩
      obtain ⟨w, hw, huw⟩ := h u hu
      exact (closed_mem.mp hw).2 u huw
    have rejectsAbove (y : Fin 42 → Bool) (hy : C.eval (List.ofFn y) = false) (hxy : x ≤ y) : False := by
      have hle := mono hxy
      change C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) at hle
      rw [hx, hy] at hle
      exact (by decide : ¬ true ≤ false) hle
    refine rejectsAbove _ (hnegative closed (fun v hv => (closed_mem.mp hv).1) satClosed) ?_
    intro i
    cases hi : x i
    · exact Bool.false_le _
    · apply le_of_eq
      symm
      apply decide_eq_true
      rcases lt_trichotomy i.val 21 with hp | he | hl
      · refine Or.inr (Or.inr ⟨hp, ?_⟩)
        intro v hv hev
        obtain ⟨w, hw, hew⟩ := (closed_mem.mp hv).2 i hev
        exact hno ⟨i, w, hew, hi, (active_mem.mp hw).2⟩
      · exact Or.inl he
      · exact Or.inr (Or.inl (sub (active_mem.mpr ⟨hl, hi⟩)))
  · rintro ⟨u, v, huv, hu, hv⟩
    have acceptsBelow (y : Fin 42 → Bool) (hy : C.eval (List.ofFn y) = true) (hyx : y ≤ x) :
        C.eval (List.ofFn x) = true := by
      have hle := mono hyx
      change C.eval (List.ofFn y) ≤ C.eval (List.ofFn x) at hle
      rw [hy] at hle
      exact Bool.eq_true_of_true_le hle
    refine acceptsBelow _ (hpositive u v huv) ?_
    intro i
    by_cases hi : i = u ∨ i = v
    · obtain rfl | rfl := hi <;> simp [hu, hv]
    · simp [hi]
