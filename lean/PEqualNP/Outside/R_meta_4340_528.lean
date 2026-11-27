import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4340_528
    (excluded :
      let labels : List ℕ := [1,2,4,5,8,12,13,15,16,23,27,28,34,35,38,46,47,57,58,67,68]
      let code (a b : Fin 9) := 10 * min a.val b.val + max a.val b.val
      let usable (C : Circuit) := ∃ (a b : Fin 9) (g : Gate), code a b ∈ labels ∧
        g ∈ C.gates ∧ g.op = .or ∧ (g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val])
      let edges : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
      let target (x : Fin 9 → Bool) := edges.any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (a b : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 14 →
        (code a b ∈ labels ∨ usable C) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x a || x b]) ≠ target x)
    (remaining :
      let labels : List ℕ := [1,2,4,5,8,12,13,15,16,23,27,28,34,35,38,46,47,57,58,67,68]
      let code (a b : Fin 9) := 10 * min a.val b.val + max a.val b.val
      let usable (C : Circuit) := ∃ (a b : Fin 9) (g : Gate), code a b ∈ labels ∧
        g ∈ C.gates ∧ g.op = .or ∧ (g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val])
      let edges : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
      let target (x : Fin 9 → Bool) := edges.any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ p ∈ ([(0,3),(0,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit,
        FanInTwo C → C.size ≤ 14 →
        (∀ g ∈ C.gates, (∀ w ∈ g.inputs, w < 9) → g.op ≠ .and ∧ g.op ≠ .not) →
        ¬usable C → ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠ target x) :
∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  intro p member C fan small raw
  let labels : List ℕ := [1,2,4,5,8,12,13,15,16,23,27,28,34,35,38,46,47,57,58,67,68]
  let code (a b : Fin 9) := 10 * min a.val b.val + max a.val b.val
  let usable (D : Circuit) := ∃ (a b : Fin 9) (g : Gate), code a b ∈ labels ∧
        g ∈ D.gates ∧ g.op = .or ∧ (g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val])
  have eq : (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
        x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) =
      (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) := by
    funext x
    revert x
    decide +kernel
  by_cases easy : code p.1 p.2 ∈ labels ∨ usable C
  · obtain ⟨x,off⟩ := excluded p.1 p.2 C fan small easy
    exact ⟨x,fun same => off (same.trans (congrFun eq x))⟩
  · have hard : p ∈ ([(0,3),(0,6)] : List (Fin 9 × Fin 9)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact False.elim (easy (Or.inl (by decide +kernel)))
      · exact False.elim (easy (Or.inl (by decide +kernel)))
      · simp
      · exact False.elim (easy (Or.inl (by decide +kernel)))
      · simp
      · exact False.elim (easy (Or.inl (by decide +kernel)))
    obtain ⟨x,off⟩ := remaining p hard C fan small raw (fun u => easy (Or.inr u))
    exact ⟨x,fun same => off (same.trans (congrFun eq x))⟩
