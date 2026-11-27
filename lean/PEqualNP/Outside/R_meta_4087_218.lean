import Mathlib
import PEqualNP.Defs

open Finset PEqualNP.HeptadCover PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4087_218
    (gluing : ∀ C : Circuit, Monotone2 C → ∃ D : Circuit, Monotone2 D ∧ D.size≤C.size+5 ∧
      ∀ w : List Bool, w.length=70 → D.eval w =
        (C.eval w || (w.getD 25 false && ((w.getD 12 false || w.getD 0 false) ||
          (w.getD 2 false || w.getD 8 false)))))
    (candidate : ∃ (rot : Fin 9 → Fin 3) (C : Circuit), Monotone2 C ∧ C.size≤13 ∧
  ∀ (P L : Finset (Fin 13)) (w : List Bool), w.length=70 →
  (∀ i : Fin 13, w.getD i.val false=decide (i∈P) ∧ w.getD (13+i.val) false=decide (i∈L)) →
  (∀ j : Fin 9, let k : Fin 13 := if rot j=0 then 1 else if rot j=1 then 3 else 9
                let z (u : Fin 13) := (Fin.ofNat 13 j.val)+u∈P
                let f (i : ℕ) := w.getD (26+(5*j.val-1)+i) false
                f 0=decide (z 0 ∨ z k) ∧ f 1=decide (z (3*k) ∨ z (9*k)) ∧ f 2=(f 0 || f 1)) →
  ((∃ l : Fin 13, (l=9 ∨ l=10 ∨ l=11) ∧ L={l} ∧ ∃ p∈singerLines3 l, P={p}) → C.eval w=true) ∧
  ((∀ p∈P, ∀ l∈L, p∉singerLines3 l) → (∀ l, (P∩singerLines3 l).card≤2) →
    (∀ p, (L.filter (fun l => p∈singerLines3 l)).card≤2) → C.eval w=false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool → Prop := fun (x2 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : List Bool) =>   x5.length = (70 : ℕ) ∧     (∀ (x6 : Fin (13 : ℕ)), x5.getD (↑x6) Bool.false = Decidable.decide (x6 ∈ x3) ∧ x5.getD ((13 : ℕ) + ↑x6) Bool.false = Decidable.decide (x6 ∈ x4)) ∧       ∀ (x6 : Fin (9 : ℕ)),         have x7 : Fin (13 : ℕ) := (x2 x6).2.1;         have x8 : Fin (13 : ℕ) := if (x2 x6).2.2 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if (x2 x6).2.2 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ));         let x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => if (x2 x6).1 = Bool.true then x7 + x9 ∈ x3 else x7 - x9 ∈ x4;         have x10 : ℕ := (26 : ℕ) + ((5 : ℕ) * ↑x6 - (1 : ℕ));         x5.getD x10 Bool.false = Decidable.decide (x9 (0 : Fin (13 : ℕ)) ∨ x9 x8) ∧ x5.getD (x10 + (1 : ℕ)) Bool.false = Decidable.decide (x9 ((3 : Fin (13 : ℕ)) * x8) ∨ x9 ((9 : Fin (13 : ℕ)) * x8)) ∧ x5.getD (x10 + (2 : ℕ)) Bool.false = (x5.getD x10 Bool.false || x5.getD (x10 + (1 : ℕ)) Bool.false); ∃ (x3 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (18 : ℕ) ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))) (x7 : List Bool), x2 x3 x5 x6 x7 → ((∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x5 = {x9} ∧ x6 = {x10} ∧ x9 - x10 ∈ x1 ∧ ¬∃ (x11 : Fin (9 : ℕ)), if (x3 x11).1 = Bool.true then (x3 x11).2.1 = x10 else (x3 x11).2.1 = x9) → x4.eval x7 = Bool.true) ∧ ((∀ x9 ∈ x5, ∀ x11 ∈ x6, x9 - x11 ∉ x1) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x5 | x11 - x10 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x6 | x11 - x12 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval x7 = Bool.false) := by
  obtain ⟨rot,C,mono,size,patch⟩ := candidate
  obtain ⟨D,md,sd,extend⟩ := gluing C mono
  let seeds (j : Fin 9) : Bool × Fin 13 × Fin 3 := (true,(Fin.ofNat 13 j.val),rot j)
  let dif : Finset (Fin 13) := {0,1,3,9}
  have geo : ∀ p l : Fin 13, p∈singerLines3 l ↔ p-l∈dif := by decide +kernel
  have line12 : ∀ p : Fin 13, p∈singerLines3 12 ↔ p=12 ∨ p=0 ∨ p=2 ∨ p=8 := by decide
  dsimp only
  refine ⟨seeds,D,md,by omega,?_⟩
  intro P L w h
  obtain ⟨len,raw,sem⟩ := h
  obtain ⟨pos,neg⟩ := patch P L w len raw (fun j => by simpa [seeds] using sem j)
  have r12 : w.getD 25 false=decide ((12 : Fin 13)∈L) := (raw 12).2
  rw [extend w len,r12,(show w.getD 12 false=_ from (raw 12).1),
    (show w.getD 0 false=_ from (raw 0).1),(show w.getD 2 false=_ from (raw 2).1),
    (show w.getD 8 false=_ from (raw 8).1)]
  constructor
  · rintro ⟨p,l,rfl,rfl,edge,free⟩
    have ge : 9≤l.val := by
      by_contra! lt
      exact free ⟨⟨l.val,lt⟩,by simp [seeds,Fin.ofNat,Nat.mod_eq_of_lt l.isLt]⟩
    have cases' : l∈({9,10,11} : Finset (Fin 13)) ∨ l=12 := by
      have enum : ∀ (i : Fin 13), (9 ≤ i.val) → (i∈({9,10,11} : Finset (Fin 13)) ∨ i=12) := by decide
      exact enum l ge
    have inc := (geo p l).2 edge
    rcases cases' with small|rfl
    · simp [pos ⟨l,by simpa using small,rfl,p,inc,rfl⟩]
    · rcases (line12 p).1 inc with rfl|rfl|rfl|rfl <;> simp
  · intro no left right
    have bad : C.eval w=false := neg (fun p hp l hl inc => no p hp l hl ((geo p l).1 inc))
      (fun l => by
        have eq : P∩singerLines3 l = P.filter (fun p => p-l∈dif) := by ext p; simp [geo]
        rw [eq]; exact left l)
      (fun p => by simpa only [geo] using right p)
    rw [bad,Bool.false_or]
    by_cases inL : (12 : Fin 13)∈L
    · have notP {i : Fin 13} (mem : i∈singerLines3 12) : i∉P :=
        fun hp => no i hp 12 inL ((geo i 12).1 mem)
      simp [notP ((line12 12).2 (by simp)),notP ((line12 0).2 (by simp)),
        notP ((line12 2).2 (by simp)),notP ((line12 8).2 (by simp))]
    · simp [inL]
