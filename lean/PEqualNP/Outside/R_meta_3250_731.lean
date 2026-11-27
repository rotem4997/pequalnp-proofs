import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3250_731
    (cofactor : ∀ (A : Type) [DecidableEq A] (E : List (A × A)) (v : A),
      (∀ e ∈ E, e.1 ≠ e.2) → ∀ (x : A → Bool), x v = false → ∀ b : Bool,
      (E.any fun e => Function.update x v b e.1 && Function.update x v b e.2) =
        ((E.any fun e => x e.1 && x e.2) ||
        (b && E.any fun e => (decide (e.1 = v) && x e.2) || (decide (e.2 = v) && x e.1))))
    (lower :
      let E := ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).map
        (fun c => (Fin.ofNat 9 (c/9), Fin.ofNat 9 c))
      let pack := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
      ∀ (v : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (cut i : ℕ) (d : Bool),
      v ≠ 0 → v ≠ 6 → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      10 ≤ i → i < cut → cut ≤ 10+C.size →
      (∀ g ∈ C.gates.take (cut-10), v.val ∉ g.inputs) →
      ∃ x : Fin 9 → Bool, x v = false ∧
        let edge := E.any fun e => x e.1 && x e.2
        let touch := E.any fun e => (decide (e.1 = v) && x e.2) || (decide (e.2 = v) && x e.1)
        let target := fun b => edge || (b && touch)
        let row := fun b => pack (Function.update x v b)
        let sel := fun b => (C.wires (row b)).getD i false
        C.eval (row d) ≠ target d ∨
        (C.eval (row (!d)) ≠ target (!d) ∧ sel (!d) = !d) ∨
        (edge = false ∧ touch = true ∧ sel false = d)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  let E := ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).map
    (fun c => (Fin.ofNat 9 (c/9), Fin.ofNat 9 c))
  let f (x : Fin 9 → Bool) := E.any fun e => x e.1 && x e.2
  let pack (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
  dsimp only
  intro v C cut i d h0 h6 fan size lo early hi avoid guard
  change ∃ x : Fin 9 → Bool, C.eval ((pack x).set v.val
    (if d = true then x v || (C.wires (pack x)).getD i false
     else x v && (C.wires (pack x)).getD i false)) ≠ f x
  have fixed (x : Fin 9 → Bool) : (pack x).set v.val (x v) = pack x := by
    have h : v.val < (pack x).length := by have := v.isLt; simp [pack]; omega
    have read : (pack x)[v.val] = x v := by
      unfold pack
      rw [List.getElem_append_left (by simpa only [List.length_ofFn] using v.isLt), List.getElem_ofFn]
    rw [← read]
    exact List.set_getElem_self h
  have loopless : ∀ e ∈ E, e.1 ≠ e.2 := by decide
  obtain ⟨x, hx, fail⟩ := lower v C cut i d h0 h6 fan size lo early hi avoid
  let edge := E.any fun e => x e.1 && x e.2
  let touch := E.any fun e => (decide (e.1 = v) && x e.2) || (decide (e.2 = v) && x e.1)
  let row := fun b => pack (Function.update x v b)
  let sel := fun b => (C.wires (row b)).getD i false
  have spec (b : Bool) : f (Function.update x v b) = (edge || (b && touch)) :=
    cofactor (Fin 9) E v loopless x hx b
  change C.eval (row d) ≠ (edge || (d && touch)) ∨
    (C.eval (row (!d)) ≠ (edge || ((!d) && touch)) ∧ sel (!d) = !d) ∨
    (edge = false ∧ touch = true ∧ sel false = d) at fail
  rcases fail with bad | ⟨bad,neutral⟩ | ⟨noEdge,meets,wrong⟩
  · refine ⟨Function.update x v d, ?_⟩
    rw [spec]
    have mask : (if d = true then Function.update x v d v || sel d
        else Function.update x v d v && sel d) = Function.update x v d v := by
      cases d <;> simp
    change C.eval ((row d).set v.val _) ≠ _
    rw [mask, fixed]
    exact bad
  · refine ⟨Function.update x v (!d), ?_⟩
    rw [spec]
    have mask : (if d = true then Function.update x v (!d) v || sel (!d)
        else Function.update x v (!d) v && sel (!d)) = Function.update x v (!d) v := by
      rw [neutral]
      cases d <;> simp
    change C.eval ((row (!d)).set v.val _) ≠ _
    rw [mask, fixed]
    exact bad
  · have diff : f (Function.update x v false) ≠ f (Function.update x v true) := by
      rw [spec, spec, noEdge, meets]; decide
    have h := guard x diff
    change sel false = !d at h
    rw [wrong] at h
    cases d <;> contradiction
