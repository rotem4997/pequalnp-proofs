import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_18383_726
    (compact : ∀ (n m : ℕ) (C : Circuit) (p : Fin n → Option (Fin m)), IsAO2 n C →
      let top := C.wires (List.ofFn (fun i => (p i).isSome))
      ∃ D : Circuit, IsAO2 m D ∧
        D.size ≤ (C.gates.filter (fun g => g.inputs.all (fun i => top.getD i false))).length ∧
        ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => (p i).elim false x)))
    (fixed : ∀ C : Circuit, IsAO2 26 C → (∀ x : Fin 26 → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
      (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ p ≠ 0 ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) → 59 ≤ C.size) :
    ∀ (x1 : Fin (26 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), x1 = (0 : Fin (26 : ℕ)) ∨ x1 = (13 : Fin (26 : ℕ)) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x6 ≠ x1 ∧ Fin.natAdd (13 : ℕ) x7 ≠ x1 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (59 : ℕ) ≤ x2.size := by
  intro s C hs ao spec
  let I (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let P : Fin 13 → Fin 26 := Fin.castAdd 13
  let L : Fin 13 → Fin 26 := Fin.natAdd 13
  rcases hs with rfl | rfl
  · apply fixed C ao
    intro x
    rw [spec]
    have hp : ∀ p : Fin 13, P p ≠ 0 ↔ p ≠ 0 := by decide +kernel
    have hl : ∀ l : Fin 13, L l ≠ 0 := by decide +kernel
    constructor
    · rintro ⟨p,l,h,hp',_,a,b⟩
      exact ⟨p,l,h,(hp p).mp hp',a,b⟩
    · rintro ⟨p,l,h,hp',a,b⟩
      exact ⟨p,l,h,(hp p).mpr hp',hl l,a,b⟩
  · let π : Fin 26 → Option (Fin 26) := Fin.addCases (motive := fun _ => Option (Fin 26))
          (fun p : Fin 13 => some (L (-p)))
          (fun l : Fin 13 => if l = 0 then none else some (P (-l)))
    have dual : ∀ p l : Fin 13, I p l ↔ I (-l) (-p) := by decide +kernel
    have hP : ∀ p : Fin 13, P p ≠ 13 ∧ π (P p) = some (L (-p)) := by decide +kernel
    have hL : ∀ l : Fin 13, L l ≠ 13 ↔ l ≠ 0 := by decide +kernel
    have alive : ∀ l : Fin 13, l ≠ 0 → π (L l) = some (P (-l)) := by decide +kernel
    obtain ⟨D,aoD,sizeD,evalD⟩ := compact 26 26 C π ao
    refine Nat.le_trans (m := D.size) ?_ (le_trans sizeD (List.length_filter_le ..))
    apply fixed D aoD
    intro x
    rw [evalD,spec]
    constructor
    · rintro ⟨p,l,h,_,notL,a,b⟩
      have nz := (hL l).mp notL
      change (π (P p)).elim false x = true at a
      change (π (L l)).elim false x = true at b
      rw [(hP p).2] at a
      rw [alive l nz] at b
      exact ⟨-l,-p,(dual p l).mp h,neg_ne_zero.mpr nz,b,a⟩
    · rintro ⟨p,l,h,nz,a,b⟩
      refine ⟨-l,-p,(dual p l).mp h,(hP _).1,(hL _).mpr (neg_ne_zero.mpr nz),?_,?_⟩
      · change (π (P (-l))).elim false x = true
        simpa only [(hP _).2,neg_neg,Option.elim_some] using b
      · change (π (L (-p))).elim false x = true
        simpa only [alive _ (neg_ne_zero.mpr nz),neg_neg,Option.elim_some] using a
