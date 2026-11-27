import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4043_271
    (projection : ∀ (C : Circuit) (p : Fin 26 → Option (Fin 25)), Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧ ∀ y : Fin 25 → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn fun i => (p i).elim false y))
    (fixed : ∀ D : Circuit, Monotone2 D →
      (∀ y : Fin 25 → Bool, D.eval (List.ofFn y) = true ↔
        ∃ (a : Fin 12) (b : Fin 13), (a.succ = b ∨ a.succ = b+1 ∨ a.succ = b+3 ∨ a.succ = b+9) ∧
          y (Fin.castAdd 13 a) = true ∧ y (Fin.natAdd 12 b) = true) → 58 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  intro C v mono computes
  let left (i : Fin 13) : Option (Fin 25) := Fin.cases none (fun j : Fin 12 => some (Fin.castAdd 13 j)) i
  let right (i : Fin 13) : Option (Fin 25) := some (Fin.natAdd 12 i)
  let adj (a b : Fin 13) := a = b ∨ a = b+1 ∨ a = b+3 ∨ a = b+9
  let shift (z : Fin 26) : Fin 13 := Fin.ofNat 13 z.val
  let f (z : Fin 26) (a b : Fin 13) : Fin 13 × Fin 13 :=
    if z.val < 13 then (a-shift z,b-shift z) else (shift z-b,shift z-a)
  let inv (z : Fin 26) (a b : Fin 13) : Fin 13 × Fin 13 :=
    if z.val < 13 then (a+shift z,b+shift z) else (shift z-b,shift z-a)
  let p (z i : Fin 26) : Option (Fin 25) := Fin.addCases (motive := fun _ => Option (Fin 25))
    (fun a : Fin 13 => if z.val < 13 then left (a-shift z) else right (shift z-a))
    (fun b : Fin 13 => if z.val < 13 then right (b-shift z) else left (shift z-b)) i
  have removed : ∀ z, p z z = none := by decide +kernel
  have back : ∀ z a b, f z (inv z a b).1 (inv z a b).2 = (a,b) := by decide +kernel
  have preserves : ∀ z a b, adj a b ↔ adj (f z a b).1 (f z a b).2 := by decide +kernel
  have ends : ∀ z a b,
      (p z (Fin.castAdd 13 a) = left (f z a b).1 ∧ p z (Fin.natAdd 13 b) = right (f z a b).2) ∨
      (p z (Fin.castAdd 13 a) = right (f z a b).2 ∧ p z (Fin.natAdd 13 b) = left (f z a b).1) := by
    decide +kernel
  obtain ⟨D,hd,size,ev⟩ := projection C (p v) mono
  rw [← size]
  apply fixed D hd
  intro y
  let read (a : Option (Fin 25)) := a.elim false y
  have off : read (p v v) = false := by rw [removed]; rfl
  rw [ev,computes _ off]
  have signal (a b : Fin 13) :
      (read (p v (Fin.castAdd 13 a)) = true ∧ read (p v (Fin.natAdd 13 b)) = true) ↔
      (read (left (f v a b).1) = true ∧ read (right (f v a b).2) = true) := by
    rcases ends v a b with ⟨h,j⟩ | ⟨h,j⟩
    · rw [h,j]
    · rw [h,j,and_comm]
  constructor
  · rintro ⟨a,b,ha,hab⟩
    have edge := (preserves v a b).mp ha
    have values := (signal a b).mp hab
    obtain ⟨u,w,h⟩ : ∃ u w, f v a b = (u,w) := ⟨_,_,rfl⟩
    rw [h] at edge values
    change adj u w at edge
    change read (left u) = true ∧ read (right w) = true at values
    revert edge values
    refine Fin.cases ?_ (fun i => ?_) u
    · intro _ vals; exact False.elim (Bool.noConfusion vals.1)
    · intro edge vals; exact ⟨i,w,edge,vals.1,vals.2⟩
  · rintro ⟨i,w,edge,hi,hw⟩
    let a := (inv v i.succ w).1
    let b := (inv v i.succ w).2
    have h : f v a b = (i.succ,w) := back v i.succ w
    refine ⟨a,b,(preserves v a b).mpr ?_,(signal a b).mpr ?_⟩
    · rw [h]; exact edge
    · rw [h]; exact ⟨hi,hw⟩
