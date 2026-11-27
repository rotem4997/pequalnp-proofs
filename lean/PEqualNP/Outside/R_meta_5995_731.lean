import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5995_731
    (erase :
      ∀ (n : ℕ) (C : Circuit) (j p : ℕ) (y : List Bool),
        y.length = n → j < C.gates.length → p < n+j →
        ((C.wires y).getD (n+j) false = (C.wires y).getD p false ∨
          (C.output ≠ n+j ∧ ∀ g ∈ C.gates.drop (j+1), n+j ∉ g.inputs)) →
        (eraseGate n C j p).eval y = C.eval y ∧ (eraseGate n C j p).size + 1 = C.size)
    (pin : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)))
    (certificate :
      let I := fun p l : Fin 13 => (p-l).val ∈ ([0,1,3,9] : List ℕ)
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 63 →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        ∃ (v : Fin 26) (k : ℕ) (D : ℕ → Circuit), D 0 = C ∧ IsAO2 26 (D k) ∧ 4 ≤ k ∧
          (k = 4 → ∃ x : Fin 26 → Bool, (D k).eval (List.ofFn x) ≠
            (D k).eval (List.ofFn (Function.update x v false))) ∧
          ∀ i < k, let H := D i; ∃ j p : ℕ, j < H.size ∧ p < 26+j ∧
            D (i+1) = eraseGate 26 H j p ∧
            ((∀ x : Fin 26 → Bool, let w := H.wires (List.ofFn (Function.update x v false));
              w.getD (26+j) false = w.getD p false) ∨
              (H.output ≠ 26+j ∧ ∀ g ∈ H.gates.drop (j+1), 26+j ∉ g.inputs))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x1.size ≤ (63 : ℕ) → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → ∃ (x5 : Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size + (5 : ℕ) ≤ x1.size ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x8 ≠ x5 ∧ Fin.natAdd (13 : ℕ) x9 ≠ x5 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true := by
  intro C model cap correct
  let pt := (Fin.castAdd 13 : Fin 13 → Fin 26)
  let ln := (Fin.natAdd 13 : Fin 13 → Fin 26)
  let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let I' := fun p l : Fin 13 => (p-l).val ∈ ([0,1,3,9] : List ℕ)
  have incidences : ∀ p l : Fin 13, I p l ↔ I' p l := by decide +kernel
  have compressed (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, I' p l ∧ x (pt p) = true ∧ x (ln l) = true := by
    rw [correct]
    constructor
    · rintro ⟨p,l,h,xp,xl⟩
      exact ⟨p,l,(incidences p l).1 h,xp,xl⟩
    · rintro ⟨p,l,h,xp,xl⟩
      exact ⟨p,l,(incidences p l).2 h,xp,xl⟩
  obtain ⟨v,k,D,initial,last,lower,stillUses,trace⟩ := certificate C model cap compressed
  let upd (x : Fin 26 → Bool) := Function.update x v false
  have pinSpec (x : Fin 26 → Bool) : C.eval (List.ofFn (upd x)) = true ↔
      ∃ p l : Fin 13, I p l ∧ pt p ≠ v ∧ ln l ≠ v ∧ x (pt p) = true ∧ x (ln l) = true := by
    rw [correct]
    constructor
    · rintro ⟨p,l,h, hp,hl⟩
      have pn : pt p ≠ v := by
        intro eq
        change Function.update x v false (pt p) = true at hp
        rw [eq,Function.update_self] at hp
        contradiction
      have ln' : ln l ≠ v := by
        intro eq
        change Function.update x v false (ln l) = true at hl
        rw [eq,Function.update_self] at hl
        contradiction
      change Function.update x v false (pt p) = true at hp
      change Function.update x v false (ln l) = true at hl
      rw [Function.update_of_ne pn] at hp
      rw [Function.update_of_ne ln'] at hl
      exact ⟨p,l,h,pn,ln',hp,hl⟩
    · rintro ⟨p,l,h,pn,ln',hp,hl⟩
      refine ⟨p,l,h,?_,?_⟩
      · change Function.update x v false (pt p) = true
        rwa [Function.update_of_ne pn]
      · change Function.update x v false (ln l) = true
        rwa [Function.update_of_ne ln']
  have replay (i : ℕ) (hi : i ≤ k) :
      (D i).size + i = C.size ∧
      ∀ x : Fin 26 → Bool, (D i).eval (List.ofFn (upd x)) = C.eval (List.ofFn (upd x)) := by
    induction i with
    | zero => exact ⟨by rw [initial,Nat.add_zero],fun _ => by rw [initial]⟩
    | succ i ih =>
      have small : i < k := by omega
      obtain ⟨prevSize,prevEval⟩ := ih small.le
      obtain ⟨j,p,present,backwards,moved,mode⟩ := trace i small
      have replayOne (x : Fin 26 → Bool) :
          (D (i+1)).eval (List.ofFn (upd x)) = (D i).eval (List.ofFn (upd x)) ∧
            (D (i+1)).size + 1 = (D i).size := by
        rw [moved]
        apply erase 26 (D i) j p _ (by simp) present backwards
        exact mode.elim (fun equal => Or.inl (equal x)) Or.inr
      exact ⟨by have h := (replayOne (fun _ => false)).2; omega,
        fun x => (replayOne x).1.trans (prevEval x)⟩
  obtain ⟨finalSize,finalEval⟩ := replay k le_rfl
  have edgeOutside : ∀ a : Fin 26, ∃ p l : Fin 13, I p l ∧ pt p ≠ a ∧ ln l ≠ a := by decide +kernel
  obtain ⟨p,l,e,pn,ln'⟩ := edgeOutside v
  let off : Fin 26 → Bool := fun _ => false
  let on : Fin 26 → Bool := fun j => decide (j=pt p ∨ j=ln l)
  have zero : C.eval (List.ofFn (upd off)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨a,b,_,_,_,h',_⟩ := (pinSpec off).1 h
    exact Bool.false_ne_true h'
  have one : C.eval (List.ofFn (upd on)) = true := by
    apply (pinSpec on).2
    exact ⟨p,l,e,pn,ln',by simp [on],by simp [on]⟩
  have different : ∃ x y : Fin 26 → Bool,
      (D k).eval (List.ofFn (upd x)) ≠ (D k).eval (List.ofFn (upd y)) := by
    refine ⟨off,on,?_⟩
    rw [finalEval,finalEval,zero,one]
    decide
  obtain ⟨E,em,sz,shrinks,eval⟩ := pin 26 v (D k).size (D k) rfl last different
  have enough : E.size + 5 ≤ C.size := by
    by_cases four : k = 4
    · have gain := shrinks (stillUses four)
      omega
    · omega
  refine ⟨v,E,em,enough,fun x => ?_⟩
  rw [eval x,finalEval x]
  exact pinSpec x
