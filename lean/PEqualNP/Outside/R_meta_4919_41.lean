import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Seven selected points leave at most five lines disjoint from them.
-- A candidate for the cached circuit is tested on the 105 flags and on maximal
-- negative rows. The small side bound limits enumeration of those rows.
theorem PEqualNP.Outside.R_meta_4919_41
    (geometry : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
      let f := fun (x : Fin 42 → Bool) => ∃ u v, E u v ∧ x u = true ∧ x v = true
      let small := (fun (x : Fin 42 → Bool) =>
        (List.finRange 21).countP (fun p => x (Fin.castAdd 21 p)) ≤ 6 ∨
        (List.finRange 21).countP (fun l => x (Fin.natAdd 21 l)) ≤ 5)
      ∀ x, ¬ f x → small x)
    (monotonicity : let B := (fun (x : Fin 42 → Bool) =>
        let L := fun (j : Fin 7) (d : Nat) => x (Fin.ofNat 42 (21 + (3*j.val + d) % 21));
        (List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20))
      ∀ C : Circuit, Monotone2 C → Monotone (fun x => C.eval (B x)))
    (boundary : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
      let f := fun (x : Fin 42 → Bool) => ∃ u v, E u v ∧ x u = true ∧ x v = true
      let B := (fun (x : Fin 42 → Bool) =>
        let L := fun (j : Fin 7) (d : Nat) => x (Fin.ofNat 42 (21 + (3*j.val + d) % 21));
        (List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20))
      let small := (fun (x : Fin 42 → Bool) =>
        (List.finRange 21).countP (fun p => x (Fin.castAdd 21 p)) ≤ 6 ∨
        (List.finRange 21).countP (fun l => x (Fin.natAdd 21 l)) ≤ 5)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 110 ∧
        (∀ u v, E u v → C.eval (B (fun k => decide (k = u ∨ k = v))) = true) ∧
        (∀ x, Maximal (fun y => ¬ f y) x → small x → C.eval (B x) = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (110 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.eval               (have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));               (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) =             Bool.true ↔           ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  classical
  let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
  let f := fun (x : Fin 42 → Bool) => ∃ u v, E u v ∧ x u = true ∧ x v = true
  let B := (fun (x : Fin 42 → Bool) =>
        let L := fun (j : Fin 7) (d : Nat) => x (Fin.ofNat 42 (21 + (3*j.val + d) % 21));
        (List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20))
  let small := (fun (x : Fin 42 → Bool) =>
        (List.finRange 21).countP (fun p => x (Fin.castAdd 21 p)) ≤ 6 ∨
        (List.finRange 21).countP (fun l => x (Fin.natAdd 21 l)) ≤ 5)
  change ∀ x, ¬ f x → small x at geometry
  change ∀ C : Circuit, Monotone2 C → Monotone (fun x => C.eval (B x)) at monotonicity
  change ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 110 ∧
    (∀ u v, E u v → C.eval (B (fun k => decide (k = u ∨ k = v))) = true) ∧
    (∀ x, Maximal (fun y => ¬ f y) x → small x → C.eval (B x) = false) at boundary
  obtain ⟨C,hC,size,flags,neg⟩ := boundary
  refine ⟨C,hC,size,?_⟩
  intro x
  change C.eval (B x) = true ↔ f x
  have mono := monotonicity C hC
  constructor
  · intro hx
    by_contra hn
    obtain ⟨y,hxy,hm⟩ := Finite.exists_le_maximal (p := fun z => ¬ f z) hn
    have hy := neg y hm (geometry y hm.1)
    have le : C.eval (B x) ≤ C.eval (B y) := mono hxy
    have impossible : C.eval (B y) = true := (Bool.le_iff_imp.mp le) hx
    rw [hy] at impossible
    contradiction
  · rintro ⟨u,v,e,hu,hv⟩
    have hxy : (fun k : Fin 42 => decide (k = u ∨ k = v)) ≤ x := by
      intro k
      by_cases h : k = u ∨ k = v
      · rcases h with rfl | rfl <;> simp_all
      · simp [h]
    have hval := flags u v e
    have le : C.eval (B (fun k => decide (k = u ∨ k = v))) ≤ C.eval (B x) := mono hxy
    exact (Bool.le_iff_imp.mp le) hval
