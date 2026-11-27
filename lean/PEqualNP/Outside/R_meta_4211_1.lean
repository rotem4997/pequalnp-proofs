import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- Separate circuit surgery from the finite order-3 lower bound.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4211_1
    (hBuild :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 62 →
        ∀ (a b : Fin (26 + C.size)), a ≠ b →
          ∀ (T : Set (Fin 26 → Bool)) (f : (Fin 26 → Bool) → Bool),
            (∀ x ∈ T, (Circuit.wireOn C x a.val || Circuit.wireOn C x b.val) = f x) →
            ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 63 ∧
              ∀ x ∈ T, circuitFun 26 D x = f x)
    (hLower :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 63 →
        (∀ (p l : Fin 13),
          (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset, p = l + d) →
          circuitFun 26 C
            (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l)) = true) →
        (∀ (m : ℕ),
          m ∈ [8191, 7668, 6624, 5584, 3492, 1408, 7492, 7316, 6272, 7472, 4176,
            2084, 6144, 5120, 4160, 2304, 2052, 4112, 4096, 0] →
          ∀ (c : Fin 13),
            let X : Finset (Fin 13) :=
              Finset.univ.filter fun p => m.testBit (p - c).val = true
            circuitFun 26 C
              (fun z => decide ((∃ p ∈ X, z = Fin.castAdd 13 p) ∨
                ∃ l : Fin 13, z = Fin.natAdd 13 l ∧ ∀ p ∈ X,
                  ¬ ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset,
                    p = l + d)) = false) →
        False) :
    have x1 : Finset (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].toFinset; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) (x5 : Fin (26 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (13 : ℕ) x3 ∨ x5 = Fin.natAdd (13 : ℕ) x4); have x4 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : Finset (Fin (13 : ℕ))) (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x6 ∈ x4, x5 = Fin.castAdd (13 : ℕ) x6) ∨ ∃ (x6 : Fin (13 : ℕ)), x5 = Fin.natAdd (13 : ℕ) x6 ∧ ∀ x7 ∈ x4, ¬∃ x9 ∈ x1, x7 = x6 + x9); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Fin (26 : ℕ) → Bool) => (x5.wires (List.ofFn x7)).getD x6 Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x6 →     x6.size ≤ (62 : ℕ) →       ∀ (x9 x10 : Fin ((26 : ℕ) + x6.size)),         x9 ≠ x10 →           (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x3 x12 x13), x5 x6 (↑x10) (x3 x12 x13)] = Bool.true) →             (∀ (x13 : ℕ) (x14 : Fin (13 : ℕ)),                 x13 ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset →                   have x16 : Finset (Fin (13 : ℕ)) := {x16 : Fin (13 : ℕ) | x13.testBit ↑(x16 - x14) = Bool.true};                   PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x4 x16), x5 x6 (↑x10) (x4 x16)] = Bool.false) →               False := by
  intro x1 x2 x3 x4 x5 C hmon hsize a b hab hinc hfalse
  let D : Finset (Fin 13) := x1
  let M (m : ℕ) (c : Fin 13) : Finset (Fin 13) :=
    Finset.univ.filter fun p => m.testBit (p - c).val = true
  let masks : List ℕ :=
    [8191, 7668, 6624, 5584, 3492, 1408, 7492, 7316, 6272, 7472, 4176,
      2084, 6144, 5120, 4160, 2304, 2052, 4112, 4096, 0]
  let Y (U : Finset (Fin 13)) : Finset (Fin 13) :=
    {l | ∀ p ∈ U, ¬ ∃ d ∈ D, p = l + d}
  let f (u : Fin 26 → Bool) : Bool :=
    incidenceFun (fun l => {p | x2 p l}) (Finset.univ.filter fun p => u (Fin.castAdd 13 p))
      (Finset.univ.filter fun l => u (Fin.natAdd 13 l))
  let T : Set (Fin 26 → Bool) :=
    {u | (∃ p l : Fin 13, x2 p l ∧ u = x3 p l) ∨
      ∃ m ∈ masks, ∃ c : Fin 13, u = x4 (M m c)}
  have or_eq (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
    cases u <;> cases v <;> rfl
  have hinc' : ∀ p l : Fin 13, x2 p l →
      (Circuit.wireOn C (x3 p l) a.val || Circuit.wireOn C (x3 p l) b.val) = true := by
    intro p l h
    have h' := hinc p l h
    rw [or_eq] at h'
    change ((C.wires (List.ofFn (x3 p l))).getD a.val false ||
      (C.wires (List.ofFn (x3 p l))).getD b.val false) = true
    exact h'
  have hfalse' : ∀ m ∈ masks, ∀ c : Fin 13,
      (Circuit.wireOn C (x4 (M m c)) a.val || Circuit.wireOn C (x4 (M m c)) b.val) = false := by
    intro m hm c
    have h := hfalse m c (by simpa [masks] using hm)
    dsimp only at h
    change GateOp.or.eval
      [x5 C a.val (x4 (M m c)),
       x5 C b.val (x4 (M m c))] = false at h
    simp only [or_eq, x5] at h
    change ((C.wires (List.ofFn (x4 (M m c)))).getD a.val false ||
      (C.wires (List.ofFn (x4 (M m c)))).getD b.val false) = false
    exact h
  have f_inc : ∀ p l : Fin 13, x2 p l → f (x3 p l) = true := by
    intro p l h
    have hx : (Finset.univ.filter fun q => x3 p l (Fin.castAdd 13 q)) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      simp [x3, Fin.ext_iff, Fin.natAdd_eq_addNat]
      omega
    have hy : (Finset.univ.filter fun r => x3 p l (Fin.natAdd 13 r)) = {l} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      simp [x3, Fin.ext_iff, Fin.natAdd_eq_addNat]
      omega
    dsimp only [f]
    rw [hx, hy]
    change decide (∃ p' ∈ ({p} : Finset (Fin 13)),
      ∃ l' ∈ ({l} : Finset (Fin 13)), p' ∈ {q | x2 q l'}) = true
    apply decide_eq_true
    exact ⟨p, by simp, l, by simp, h⟩
  have f_false : ∀ m : ℕ, ∀ c : Fin 13, f (x4 (M m c)) = false := by
    intro m c
    have hx : (Finset.univ.filter fun q => x4 (M m c) (Fin.castAdd 13 q)) = M m c := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [x4]
      simp only [decide_eq_true_eq, Finset.mem_univ, true_and]
      change ((∃ p ∈ M m c, Fin.castAdd 13 q = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, Fin.castAdd 13 q = Fin.natAdd 13 l ∧ ∀ p ∈ M m c,
          ¬ ∃ d ∈ x1, p = l + d) ↔ q ∈ M m c
      constructor
      · rintro (⟨p, hp, hqp⟩ | ⟨l, hl, hql⟩)
        · have hqp' : q = p := Fin.ext (by simpa using congrArg Fin.val hqp)
          simpa [hqp'] using hp
        · have hv := congrArg Fin.val hl
          change q.val = 13 + l.val at hv
          omega
      · intro hq
        exact Or.inl ⟨q, hq, rfl⟩
    have hy : (Finset.univ.filter fun r => x4 (M m c) (Fin.natAdd 13 r)) = Y (M m c) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [x4]
      simp only [decide_eq_true_eq]
      change ((∃ p ∈ M m c, Fin.natAdd 13 r = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, Fin.natAdd 13 r = Fin.natAdd 13 l ∧ ∀ p ∈ M m c,
          ¬ ∃ d ∈ x1, p = l + d) ↔ r ∈ Y (M m c)
      constructor
      · rintro (⟨p, hp, hpr⟩ | ⟨l, hl, hlr⟩)
        · have hv := congrArg Fin.val hpr
          change 13 + r.val = p.val at hv
          omega
        · have hlr' : r = l := Fin.ext (by simpa using congrArg Fin.val hl)
          simpa [Y, hlr'] using hlr
      · intro hr
        have hr' : ∀ p ∈ M m c, ¬ ∃ d ∈ x1, p = r + d := by
          simpa [Y, D] using hr
        exact Or.inr ⟨r, rfl, hr'⟩
    dsimp only [f, incidenceFun]
    rw [hx, hy]
    apply decide_eq_false
    rintro ⟨p, hp, l, hl, hpl⟩
    have hl' : ∀ p ∈ M m c, ¬ ∃ d ∈ D, p = l + d := by
      simpa [Y, D] using hl
    exact hl' p hp (by simpa [D] using hpl)
  have hpair : ∀ u ∈ T,
      (Circuit.wireOn C u a.val || Circuit.wireOn C u b.val) = f u := by
    intro u hu
    rcases hu with ⟨p, l, hpl, rfl⟩ | ⟨m, hm, c, rfl⟩
    · rw [hinc' p l hpl]
      exact (f_inc p l hpl).symm
    · rw [hfalse' m hm c]
      exact (f_false m c).symm
  obtain ⟨E, hEmon, hEsize, hE⟩ := hBuild C hmon hsize a b hab T f hpair
  apply hLower E hEmon hEsize
  · intro p l hpl
    have hu : x3 p l ∈ T := Or.inl ⟨p, l, hpl, rfl⟩
    have he := hE (x3 p l) hu
    rw [he, f_inc p l hpl]
  · intro m hm c
    have hu : x4 (M m c) ∈ T := Or.inr ⟨m, hm, c, rfl⟩
    have he := hE (x4 (M m c)) hu
    let G : Fin 26 → Bool := fun z =>
      decide ((∃ p ∈ Finset.univ.filter fun p : Fin 13 => m.testBit (p - c).val = true,
        z = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, z = Fin.natAdd 13 l ∧
          ∀ p ∈ Finset.univ.filter fun p : Fin 13 => m.testBit (p - c).val = true,
            ¬ ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset, p = l + d)
    change circuitFun 26 E G = false
    have hin : x4 (M m c) = G := by
      funext z
      dsimp only [G, x4, M]
    rw [← hin]
    apply Eq.trans he
    exact f_false m c
