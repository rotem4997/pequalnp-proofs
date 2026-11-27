import Mathlib
import PEqualNP.Defs

-- A rectangle covers pairs of a positive incidence test and a rejected maximal independent input.
-- Reusing an earlier rectangle shares the corresponding wire.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_4197_267
    (certificate : let inc := fun p l : Fin 21 => p-l ∈ ([0,1,4,14,16] : List (Fin 21))
      let off := fun (B : Fin 21 → Bool) (l : Fin 21) => !(B l || B (l+1) || B (l+4) || B (l+14) || B (l+16))
      ∃ s ≤ 124, ∃ R : ℕ → Set ((Fin 21 × Fin 21) × (Fin 21 → Bool)),
        (∀ p : Fin 21, ∀ z ∈ R p.val, z.1.1 = p ∧ z.2 p = false) ∧
        (∀ l : Fin 21, ∀ z ∈ R (21+l.val), z.1.2 = l ∧ off z.2 l = false) ∧
        (∀ j < s, (∀ x ∈ R (42+j), ∀ y ∈ R (42+j), (x.1,y.2) ∈ R (42+j)) ∧
           ∃ a < 42+j, ∃ b < 42+j, R (42+j) ⊆ R a ∪ R b) ∧
        ∃ o < 42+s, ∀ p l, inc p l → ∀ B : Fin 21 → Bool,
          (∀ v, B v=false → ∃ w, inc v w ∧ off B w=true) → ((p,l),B) ∈ R o)
    (synthesize : ∀ (n s : ℕ) (α β : Type)
      (P : α → Fin n → Bool) (B : β → Fin n → Bool) (R : ℕ → Set (α × β)),
      (∀ i : Fin n, ∀ z ∈ R i.val, P z.1 i = true ∧ B z.2 i = false) →
      (∀ j < s,
        (∀ x ∈ R (n+j), ∀ y ∈ R (n+j), (x.1,y.2) ∈ R (n+j)) ∧
        ∃ a < n+j, ∃ b < n+j, R (n+j) ⊆ R a ∪ R b) →
      ∀ o < n+s, ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ z ∈ R o,
        C.eval (List.ofFn (P z.1)) = true ∧ C.eval (List.ofFn (B z.2)) = false) :
    have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (124 : ℕ) ∧ (∀ (x4 x5 : Fin (21 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧ ∀ (x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (21 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false := by
  let near (p l : Fin 21) := p-l ∈ ([0,1,4,14,16] : List (Fin 21))
  let off (B : Fin 21 → Bool) (l : Fin 21) := !(B l || B (l+1) || B (l+4) || B (l+14) || B (l+16))
  have rel : ∀ p l : Fin 21, near p l ↔ (p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16) := by
    decide +kernel
  let P : (Fin 21 × Fin 21) → Fin 42 → Bool := fun e z => Fin.addCases (fun i => decide (i=e.1)) (fun j => decide (j=e.2)) z
  let B : (Fin 21 → Bool) → Fin 42 → Bool := fun v z => Fin.addCases v (off v) z
  obtain ⟨s,hs,R,points,lines,joins,o,inside,full⟩ := certificate
  have raw : ∀i : Fin 42,∀z∈R i.val, P z.1 i=true ∧ B z.2 i=false := by
    intro i
    refine Fin.addCases (m:=21) (n:=21)
      (motive:=fun k=>∀z∈R k.val,P z.1 k=true ∧ B z.2 k=false) (fun p => ?_) (fun l => ?_) i
    · intro z hz
      obtain ⟨eq,h⟩ := points p z hz
      simpa only [P,B,Fin.addCases_left,decide_eq_true_eq] using And.intro eq.symm h
    · intro z hz
      obtain ⟨eq,h⟩ := lines l z hz
      simpa only [P,B,Fin.addCases_right,decide_eq_true_eq] using And.intro eq.symm h
  obtain ⟨C,hm,size,both⟩ := synthesize 42 s (Fin 21 × Fin 21) (Fin 21 → Bool) P B R raw joins o inside
  refine ⟨C,hm,size.trans hs,?_,?_⟩
  · intro p l hp
    exact (both ((p,l), fun _ => true)
      (full p l ((rel p l).mpr hp) (fun _ => true) (by simp))).1
  · intro v closed
    have c : ∀ p, v p=false → ∃ l, near p l ∧ off v l=true := by
      intro p hp
      obtain ⟨l,e,absent⟩ := closed p hp
      exact ⟨l,(rel p l).mpr e,absent⟩
    exact (both ((0,0),v) (full 0 0 ((rel 0 0).mpr (Or.inl rfl)) v c)).2
