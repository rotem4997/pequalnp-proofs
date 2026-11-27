import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_1866_1
    (h_transport : ∀ (p : Fin 9 → Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : List Bool), a.length = b.length → 9 ≤ b.length → (∀ i, a.getD (if h : i < 9 then (p ⟨i,h⟩).val else i) false = b.getD i false) → (⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (fun i => (if h : i < 9 then (p ⟨i,h⟩).val else i))⟩), (if h : C.output < 9 then (p ⟨C.output,h⟩).val else C.output)⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval a = C.eval b)
    (h_canonical : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (pins : List (Fin 11)), pins ∈ ([[],[0],[0,1],[0,2],[0,4],[0,6],[1],[1,2],[1,4],[1,5],[1,6],[1,7],[1,8],[1,9],[4],[4,6],[4,9],[6],[6,7],[6,9],[9],[10]] : List (List (Fin 11))) → PEqualNP.MetaComplexity.FanInTwo D → (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 && x 3]; D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun i => w.getD i.val false)]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 14 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C pins fan hp computes
  let perm (k : Fin 4) : Fin 9 → Fin 9 :=
    ![![0,1,2,3,4,5,6,7,8],
      ![3,8,5,0,4,2,6,7,1],
      ![0,5,8,3,4,1,7,6,2],
      ![3,2,1,0,4,8,7,6,5]] k

  let representatives : List (List (Fin 11)) :=
    [[],[0],[0,1],[0,2],[0,4],[0,6],[1],[1,2],[1,4],[1,5],[1,6],[1,7],[1,8],[1,9],[4],[4,6],[4,9],[6],[6,7],[6,9],[9],[10]]

  let edgeF (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  let value (pins : List (Fin 11)) (x : Fin 9 → Bool) : Bool :=
    let w := List.ofFn x ++ [x 0 && x 3]
    (pins.map fun i => w.getD i.val false).all id

  have prefix_fixed (k : Fin 4) (x : Fin 9 → Bool) :
      (x (perm k 0) && x (perm k 3)) = (x 0 && x 3) := by
    fin_cases k <;> simp [perm, Bool.and_comm]

  have edge_fixed (k : Fin 4) (x : Fin 9 → Bool) :
      edgeF (fun i => x (perm k i)) = edgeF x := by
    fin_cases k <;> dsimp [perm, edgeF] <;> ac_rfl

  have normal_form (pins : List (Fin 11)) (hp : pins.length ≤ 2) :
      ∃ (k : Fin 4) (q : List (Fin 11)), q ∈ representatives ∧
        ∀ x : Fin 9 → Bool, value q x = value pins (fun i => x (perm k i)) := by
    rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨0,[],by decide,?_⟩
      intro x
      simp [value, perm, List.ofFn_succ]
    · fin_cases a
      · refine ⟨0,[0],by decide,?_⟩
        intro x
        cases h0 : x 0 <;>
          simp [value, perm, List.ofFn_succ, h0]
      · refine ⟨0,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨3,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨1,[0],by decide,?_⟩
        intro x
        cases h0 : x 0 <;>
          simp [value, perm, List.ofFn_succ, h0]
      · refine ⟨0,[4],by decide,?_⟩
        intro x
        cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h4]
      · refine ⟨2,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨0,[6],by decide,?_⟩
        intro x
        cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h6]
      · refine ⟨2,[6],by decide,?_⟩
        intro x
        cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h6]
      · refine ⟨1,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
    · fin_cases a <;> fin_cases b
      · refine ⟨0,[0],by decide,?_⟩
        intro x
        cases h0 : x 0 <;>
          simp [value, perm, List.ofFn_succ, h0]
      · refine ⟨0,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨0,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[0,4],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h0, h4]
      · refine ⟨2,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨0,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨2,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨2,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨0,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨0,[1,2],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h1, h2]
      · refine ⟨3,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨0,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨0,[1,5],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h5 : x 5 <;>
          simp [value, perm, List.ofFn_succ, h1, h5]
      · refine ⟨0,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨0,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨0,[1,8],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h8 : x 8 <;>
          simp [value, perm, List.ofFn_succ, h1, h8]
      · refine ⟨0,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨0,[1,2],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h1, h2]
      · refine ⟨3,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨3,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨3,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨2,[1,8],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h8 : x 8 <;>
          simp [value, perm, List.ofFn_succ, h1, h8]
      · refine ⟨3,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨3,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨1,[1,5],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h5 : x 5 <;>
          simp [value, perm, List.ofFn_succ, h1, h5]
      · refine ⟨3,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨3,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨3,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨1,[0],by decide,?_⟩
        intro x
        cases h0 : x 0 <;>
          simp [value, perm, List.ofFn_succ, h0]
      · refine ⟨1,[0,4],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h0, h4]
      · refine ⟨1,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨1,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨3,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨1,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[0,4],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h0, h4]
      · refine ⟨0,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨3,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨1,[0,4],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h0, h4]
      · refine ⟨0,[4],by decide,?_⟩
        intro x
        cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h4]
      · refine ⟨2,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨0,[4,6],by decide,?_⟩
        intro x
        cases h4 : x 4 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h4, h6]
      · refine ⟨2,[4,6],by decide,?_⟩
        intro x
        cases h4 : x 4 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h4, h6]
      · refine ⟨1,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨0,[4,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h0, h3, h4]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨2,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨0,[1,5],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h5 : x 5 <;>
          simp [value, perm, List.ofFn_succ, h1, h5]
      · refine ⟨2,[1,8],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h8 : x 8 <;>
          simp [value, perm, List.ofFn_succ, h1, h8]
      · refine ⟨1,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨2,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨2,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨2,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨2,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨1,[1,2],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h1, h2]
      · refine ⟨2,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨0,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨3,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨1,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨0,[4,6],by decide,?_⟩
        intro x
        cases h4 : x 4 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h4, h6]
      · refine ⟨2,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨0,[6],by decide,?_⟩
        intro x
        cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h6]
      · refine ⟨0,[6,7],by decide,?_⟩
        intro x
        cases h6 : x 6 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h6, h7]
      · refine ⟨1,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨0,[6,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h3, h6]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨2,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨0,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨3,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨3,[0,6],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h6]
      · refine ⟨2,[4,6],by decide,?_⟩
        intro x
        cases h4 : x 4 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h4, h6]
      · refine ⟨2,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨0,[6,7],by decide,?_⟩
        intro x
        cases h6 : x 6 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h6, h7]
      · refine ⟨2,[6],by decide,?_⟩
        intro x
        cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h6]
      · refine ⟨1,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨2,[6,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h3, h6]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨2,[0,2],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h0, h2]
      · refine ⟨0,[1,8],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h8 : x 8 <;>
          simp [value, perm, List.ofFn_succ, h1, h8]
      · refine ⟨1,[1,5],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h5 : x 5 <;>
          simp [value, perm, List.ofFn_succ, h1, h5]
      · refine ⟨1,[0,1],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h0, h1]
      · refine ⟨1,[1,4],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h1, h4]
      · refine ⟨1,[1,2],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h2 : x 2 <;>
          simp [value, perm, List.ofFn_succ, h1, h2]
      · refine ⟨1,[1,6],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h1, h6]
      · refine ⟨1,[1,7],by decide,?_⟩
        intro x
        cases h1 : x 1 <;> cases h7 : x 7 <;>
          simp [value, perm, List.ofFn_succ, h1, h7]
      · refine ⟨1,[1],by decide,?_⟩
        intro x
        cases h1 : x 1 <;>
          simp [value, perm, List.ofFn_succ, h1]
      · refine ⟨1,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨3,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[4,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;> cases h4 : x 4 <;>
          simp [value, perm, List.ofFn_succ, h0, h3, h4]
      · refine ⟨2,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[6,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h3, h6]
      · refine ⟨2,[6,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;> cases h6 : x 6 <;>
          simp [value, perm, List.ofFn_succ, h0, h3, h6]
      · refine ⟨1,[1,9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h1, h3]
      · refine ⟨0,[9],by decide,?_⟩
        intro x
        cases h0 : x 0 <;> cases h3 : x 3 <;>
          simp [value, perm, List.ofFn_succ, h0, h3]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
      · refine ⟨0,[10],by decide,?_⟩
        intro x
        simp [value, perm, List.ofFn_succ]
    · simp at hp


  obtain ⟨k,q,hq,heq⟩ := normal_form pins hp
  let p := perm k
  let rename (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else i
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op,g.inputs.map rename⟩), rename C.output⟩
  have hf : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hh := fan g' hg'
    simpa using hh
  have hs : D.size = C.size := by exact List.length_map _
  rw [← hs]
  apply h_canonical D q hq hf
  intro x
  let a := (List.ofFn x ++ [x 0 && x 3]) ++ [value q x]
  let b := (List.ofFn (fun i => x (p i)) ++ [x (p 0) && x (p 3)]) ++
    [value pins (fun i => x (p i))]
  have hlen : a.length = b.length := by simp [a,b]
  have hn : 9 ≤ b.length := by simp [b]
  have base (z : Fin 9 → Bool) (j : Fin 9) (u v : Bool) :
      ((List.ofFn z ++ [u]) ++ [v]).getD j.val false = z j := by
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hread : ∀ i, a.getD (rename i) false = b.getD i false := by
    intro i
    by_cases hi : i < 9
    · have hr : rename i = (p ⟨i,hi⟩).val := by simp [rename,hi]
      rw [hr]
      exact (base x ⟨(p ⟨i,hi⟩).val, (p ⟨i,hi⟩).isLt⟩ _ _).trans
        (base (fun j => x (p j)) ⟨i,hi⟩ _ _).symm
    · have hr : rename i = i := by simp [rename,hi]
      rw [hr]
      by_cases h9 : i = 9
      · subst i
        simp [a,b,List.getD_eq_getElem?_getD,p,prefix_fixed]
      · by_cases h10 : i = 10
        · subst i
          simpa [a,b,List.getD_eq_getElem?_getD,p] using heq x
        · rw [List.getD_eq_default _ _ (by simp [a]; omega),
            List.getD_eq_default _ _ (by simp [b]; omega)]
  have hv := h_transport p C a b hlen hn hread
  change D.eval a = edgeF x
  rw [hv]
  exact (computes (fun i => x (p i))).trans (edge_fixed k x)
