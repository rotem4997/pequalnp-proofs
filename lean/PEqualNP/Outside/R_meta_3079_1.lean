import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- A duplicate or unavailable operand gives a 14-gate circuit.
-- Pinning vertex four covers the nonexceptional pairs that use it.
-- Reflect the remaining pairs into a fixed list of representatives.
-- Bit 9*a+b is set exactly for the listed representative of each pair.
theorem PEqualNP.Outside.R_meta_3079_1
    (normalize :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    let minor := (fun x : Fin 8 → Bool => f ((Fin.insertNth (4 : Fin (8+1)) false) x))

    let agrees (a b o : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)) :=
      ∀ m < 512,
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
        let wires := ((1, a, b) :: tail).foldl (fun w g =>
          w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
            else if g.1.val = 1 then read w g.2.1 || read w g.2.2
            else !read w g.2.1]) (List.ofFn x ++ [x 0 || x 4])
        wires.getD o.val false = f x
    let reps (a b : Fin 26) :=
      a.val < 9 ∧ b.val < 9 ∧ (2305843017923426382 : ℕ).testBit (9*a.val+b.val) = true
    ∀ (a b o : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
      a.val ≠ 9 → b.val ≠ 9 → a.val ≠ 25 → b.val ≠ 25 → agrees a b o tail →
      PEqualNP.MetaComplexity.HasCircuitSize 9 f 14 ∨
      PEqualNP.MetaComplexity.HasCircuitSize 8 minor 12 ∨
      ∃ a b o tail, tail.length ≤ 13 ∧ reps a b ∧ agrees a b o tail)
    (lower9 :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 f 14)
    (lower8 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (exclude :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))

    let agrees (a b o : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)) :=
      ∀ m < 512,
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
        let wires := ((1, a, b) :: tail).foldl (fun w g =>
          w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
            else if g.1.val = 1 then read w g.2.1 || read w g.2.2
            else !read w g.2.1]) (List.ofFn x ++ [x 0 || x 4])
        wires.getD o.val false = f x
    let reps (a b : Fin 26) :=
      a.val < 9 ∧ b.val < 9 ∧ (2305843017923426382 : ℕ).testBit (9*a.val+b.val) = true
    ∀ (a b o : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
      reps a b → ¬ agrees a b o tail) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b out tail small no9 a25 b25 _
  by_contra missing
  obtain short | short | ⟨u,v,o,gs,l,rep,ok⟩ :=
    normalize a b out tail small no9.1 no9.2 a25 b25 (by
      intro m hm
      by_contra wrong
      exact missing ⟨m,hm,wrong⟩)
  · exact lower9 short
  · apply lower8
    have same : (fun x : Fin 8 → Bool => (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) ((Fin.insertNth (4 : Fin (8+1)) false) x)) = (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) := by
      funext x
      have embedEq : (Fin.insertNth (4 : Fin (8+1)) false) x = (fun (x : Fin 8 → Bool) (i : Fin 9) =>
      if i.val = 4 then false else x (Fin.ofNat 8 (i.val - (if i.val < 4 then 0 else 1)))) x := by
        funext i
        fin_cases i <;> rfl
      rw [embedEq]
      simp only [List.any_cons,List.any_nil]
      change ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && false) || ((false && x 0) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))) = _
      simp only [Bool.or_false,Bool.false_or,Bool.false_and,Bool.and_false,Bool.or_assoc]
    rw [same] at short
    exact short
  · exact exclude u v o gs l rep ok
