import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option synthInstance.maxSize 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1884_412
  (pivotal : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k → ¬ (a = true ∧ b = true ∧ ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD j.val 0).testBit k.val) = true) → ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool, (decide (∃ p l : Fin 10, Function.update x i z p = true ∧ Function.update x i z l = true ∧ ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val) = true)) = z)
  (core : ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool),
    FanInTwo C → C.size ≤ 18 →
    let F := fun x : Fin 10 → Bool => C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])
    let A := (fun (p l : Fin 10) => (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val)
    Monotone F → (∀ π : Fin 10 ≃ Fin 10, (∀ i j, A (π i) (π j) = A i j) → ∀ x : Fin 10 → Bool, F (x ∘ π) = F x) → (∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k → ¬ (a = true ∧ b = true ∧ A j k = true) → ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool, F (Function.update x i z) = z) →
    ∃ t : Fin 3, F (fun i : Fin 10 => (([3, 50, 116] : List ℕ).getD t.val 0).testBit i.val) ≠ decide (t.val = 0)) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  let P := (fun (x : Fin 10 → Bool) => decide (∃ p l : Fin 10, x p = true ∧ x l = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val = true))
  let E := (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))
  let A := (fun (p l : Fin 10) => (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val)
  have bridge : ∀ x : Fin 10 → Bool, P x = E x := by
    let edges : List (Fin 10 × Fin 10) :=
      [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    have graph : ∀ p l : Fin 10,
        ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val = true) ↔
          (p,l) ∈ edges ∨ (l,p) ∈ edges := by
      dsimp only [edges]
      decide +kernel
    intro x
    have via : P x = edges.any (fun e => x e.1 && x e.2) := by
      apply Bool.eq_iff_iff.mpr
      change (decide (∃ p l : Fin 10, x p = true ∧ x l = true ∧
        ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val = true)) = true) ↔ _
      simp only [decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨p, l, hp, hl, h⟩
        rcases (graph p l).mp h with h | h
        · exact ⟨(p,l), h, hp, hl⟩
        · exact ⟨(l,p), h, hl, hp⟩
      · rintro ⟨⟨p,l⟩, h, hp, hl⟩
        exact ⟨p,l,hp,hl,(graph p l).mpr (Or.inl h)⟩
    rw [via]
    simp [edges, E, Bool.or_assoc]

  have table : ∀ t : Fin 3, P (fun i : Fin 10 => (([3, 50, 116] : List ℕ).getD t.val 0).testBit i.val) = decide (t.val = 0) := by
    dsimp only [P]
    decide +kernel
  intro C σ u hC hn
  let F := fun x : Fin 10 → Bool => C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])
  change ∃ x : Fin 10 → Bool, F x ≠ E x
  by_contra fail
  have equal (x : Fin 10 → Bool) : F x = P x := by
    rw [bridge]
    by_contra diff
    exact fail ⟨x, diff⟩
  have mono : Monotone F := by
    intro x y hxy
    rw [equal, equal]
    apply Bool.le_iff_imp.mpr
    intro hx
    obtain ⟨i,j,hi,hj,he⟩ := of_decide_eq_true hx
    exact decide_eq_true ⟨i, j, Bool.le_iff_imp.mp (hxy i) hi, Bool.le_iff_imp.mp (hxy j) hj, he⟩
  have invariant : ∀ π : Fin 10 ≃ Fin 10, (∀ i j, A (π i) (π j) = A i j) → ∀ x : Fin 10 → Bool, F (x ∘ π) = F x := by
    intro π aut x
    rw [equal, equal]
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ i j, x (π i) = true ∧ x (π j) = true ∧ A i j = true) = true) ↔
      (decide (∃ i j, x i = true ∧ x j = true ∧ A i j = true) = true)
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,hi,hj,he⟩
      exact ⟨π i, π j, hi, hj, (aut i j).trans he⟩
    · rintro ⟨i,j,hi,hj,he⟩
      obtain ⟨k,rfl⟩ := π.surjective i
      obtain ⟨l,rfl⟩ := π.surjective j
      exact ⟨k,l,hi,hj,(aut k l).symm.trans he⟩
  have rigid : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k → ¬ (a = true ∧ b = true ∧ ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD j.val 0).testBit k.val) = true) → ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool, F (Function.update x i z) = z := by
    intro i j k a b hij hik hjk pins
    obtain ⟨x,hj,hk,hz⟩ := pivotal i j k a b hij hik hjk pins
    exact ⟨x,hj,hk,fun z => (equal _).trans (hz z)⟩
  obtain ⟨t,diff⟩ := core C σ u hC hn mono invariant rigid
  exact diff ((equal _).trans (table t))
