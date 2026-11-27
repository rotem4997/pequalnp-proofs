import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- A point or line deletion removes four of the 52 edges.
-- All 26 possible single-vertex deletions are isomorphic.
-- On a point deletion translate both coordinates. On a line deletion
-- also exchange the two parts and negate the coordinates.
set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_2389_375
    (deletion : ∀ C : Circuit, IsAO2 26 C → C.size ≤ 63 →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      ∃ (v : Fin 26) (D : Circuit), IsAO2 26 D ∧ D.size + 5 ≤ C.size ∧
        ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ Fin.castAdd 13 p ≠ v ∧ Fin.natAdd 13 l ≠ v ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (smaller : ∀ D : Circuit, IsAO2 26 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ p ≠ 0 ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) → 59 ≤ D.size)
    (rename : ∀ (C : Circuit) (f : Fin 26 → Fin 26), IsAO2 26 C →
      ∃ D : Circuit, IsAO2 26 D ∧ D.size = C.size ∧
        ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  intro C model eqn
  by_contra! small
  obtain ⟨v,D,dm,budget,sem⟩ := deletion C model (by omega) eqn
  let pt := (Fin.castAdd 13 : Fin 13 → Fin 26)
  let ln := (Fin.natAdd 13 : Fin 13 → Fin 26)
  let inc := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let tag := fun w : Fin 26 => Fin.ofNat 13 w.val
  let f := fun w i : Fin 26 =>
    if w.val < 13 then
      if i.val < 13 then pt (tag i - tag w) else ln (tag i - tag w)
    else if i.val < 13 then ln (tag w - tag i) else pt (tag w - tag i)
  let u := fun (w : Fin 26) (p l : Fin 13) => if w.val < 13 then p - tag w else tag w - l
  let z := fun (w : Fin 26) (p l : Fin 13) => if w.val < 13 then l - tag w else tag w - p
  let backP := fun (w : Fin 26) (p l : Fin 13) => if w.val < 13 then p + tag w else tag w - l
  let backL := fun (w : Fin 26) (p l : Fin 13) => if w.val < 13 then l + tag w else tag w - p
  let endpoints := fun (w : Fin 26) (p l a b : Fin 13) =>
    (f w (pt p) = pt a ∧ f w (ln l) = ln b) ∨ (f w (pt p) = ln b ∧ f w (ln l) = pt a)
  have forward : ∀ (w : Fin 26) (p l : Fin 13), inc p l → pt p ≠ w → ln l ≠ w →
      inc (u w p l) (z w p l) ∧ u w p l ≠ 0 ∧ endpoints w p l (u w p l) (z w p l) := by
    dsimp only [inc,pt,ln,endpoints,u,z,f,tag]
    decide +kernel
  have inverse : ∀ (w : Fin 26) (a b : Fin 13), inc a b → a ≠ 0 →
      inc (backP w a b) (backL w a b) ∧ pt (backP w a b) ≠ w ∧ ln (backL w a b) ≠ w ∧
        endpoints w (backP w a b) (backL w a b) a b := by
    dsimp only [inc,pt,ln,endpoints,backP,backL,f,tag]
    decide +kernel
  obtain ⟨D',dm',sz,eval⟩ := rename D (f v) dm
  have h := smaller D' dm' (by
    intro x
    rw [eval,sem]
    constructor
    · rintro ⟨p,l,hi,hp,hl,xp,xl⟩
      obtain ⟨inc',ne,hits⟩ := forward v p l hi hp hl
      refine ⟨_,_,inc',ne,?_⟩
      change x (f v (pt p)) = true at xp
      change x (f v (ln l)) = true at xl
      rcases hits with ⟨a,b⟩|⟨a,b⟩
      · rw [a] at xp
        rw [b] at xl
        exact ⟨xp,xl⟩
      · rw [a] at xp
        rw [b] at xl
        exact ⟨xl,xp⟩
    · rintro ⟨a,b,hi,hn,xa,xb⟩
      obtain ⟨inc',np,nl,hits⟩ := inverse v a b hi hn
      refine ⟨_,_,inc',np,nl,?_⟩
      change x (pt a) = true at xa
      change x (ln b) = true at xb
      rcases hits with ⟨h1,h2⟩|⟨h1,h2⟩
      · exact ⟨h1.symm ▸ xa,h2.symm ▸ xb⟩
      · exact ⟨h1.symm ▸ xb,h2.symm ▸ xa⟩)
  omega
