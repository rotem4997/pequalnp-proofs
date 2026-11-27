import Mathlib
import PEqualNP.Defs

open PEqualNP.AndCount

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_909_2
  (realize : ∀ (n k : ℕ) (N : Finset (Finset (Fin n)))
      (P : Fin k → Finset (Fin n)) (Z : Fin k → Fin 2 → Finset (Finset (Fin n)))
      (H : Fin k → Finset (Finset (Fin n))),
    let U := (Finset.univ : Finset (Fin k))
    let safe := fun i => Z i 0 ∪ Z i 1
    (∀ i t, t ∈ H i → ∀ b, (∃ v ∈ P i, v ∈ t ∧ ∀ x ∈ Z i b, v ∉ x) ∨
      ∃ j < i, t ∈ H j ∧ Z i b ⊆ safe j) →
    ∃ C : AndCountCircuit n, C.WellFormed ∧ C.size = k ∧
      (let W := (Finset.univ : Finset (Fin C.size))
       ∀ v, (W.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤
        (U.filter (fun i => v ∈ P i)).card) ∧ (∀ x ∈ N, C.eval x = false) ∧
      ∀ i, N ⊆ safe i → ∀ t ∈ H i, ∀ x, t ⊆ x → C.eval x = true)
  (search : let V := (Finset.univ : Finset (Fin 10))
    let bit := fun (m : ℕ) (v : Fin 10) => m.testBit v.val
    let N := (([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ).map (fun m : ℕ => V.filter (fun v => bit m v = true))).toFinset
    ∃ (P : Fin 6 → Finset (Fin 10)) (Z : Fin 6 → Fin 2 → Finset (Finset (Fin 10)))
      (H : Fin 6 → Finset (Finset (Fin 10))),
      let safe := fun i => Z i 0 ∪ Z i 1
      let U := (Finset.univ : Finset (Fin 6))
      (∀ v, (U.filter (fun i => v ∈ P i)).card ≤ 2) ∧
      (∀ i, Disjoint (Z i 0) (Z i 1) ∧ safe i ⊆ N) ∧
      (∀ i t, t ∈ H i → ∀ b, (∃ v ∈ P i, v ∈ t ∧ ∀ x ∈ Z i b, v ∉ x) ∨
        ∃ j < i, t ∈ H j ∧ Z i b ⊆ safe j) ∧
      ∀ x ∈ N, ∀ w : Fin 10, w ∉ x → ∃ i, N ⊆ safe i ∧ ∃ t ∈ H i, t ⊆ insert w x) :
  ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true) := by
  have geometry : ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
      ∀ I : Finset (Fin 10),
      (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      I ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ).map (fun m =>
        Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)) := by
    intro G hG
    subst G
    simp only [SimpleGraph.fromRel_adj, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    decide +kernel

  let N := (([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ).map (fun m : ℕ => Finset.univ.filter (fun v : Fin 10 => m.testBit v.val = true))).toFinset
  obtain ⟨P,Z,H,budget,_,sides,hits⟩ := search
  obtain ⟨C,wf,size,reads,zeros,ones⟩ := realize 10 6 N P Z H sides
  intro G hG
  refine ⟨C,wf,size.le,fun v => (reads v).trans (budget v),?_⟩
  intro I ind dom
  have mem : I ∈ N := List.mem_toFinset.mpr (geometry G hG I ind dom)
  refine ⟨zeros I mem,?_⟩
  intro w hw
  obtain ⟨i,good,t,ht,sub⟩ := hits I mem w hw
  exact ones i good t ht _ sub
