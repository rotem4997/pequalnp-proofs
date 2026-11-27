import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5829_2
    (h670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (h4031 : ¬ PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ))) (18 : ℕ))
    (h4035 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7))
    (hBoth : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u i0 i1 : Fin D.gates.length),
      (PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 17 ∧ u.val < 16 ∧ u ≠ i0 ∧ i0 ≠ i1 ∧ i0.val < 16) →
      have rd := fun (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains i;
      have f := fun x : Fin 10 → Bool => have v := Fin.ofNat 10; (List.range 5).any fun a => x (v a) && (x (v ((a + 1) % 5)) || x (v (a + 5))) || x (v (a + 5)) && x (v (5 + (a + 2) % 5));
      have w := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x ++ [!x 0])).getD i false;
      (∀ j : Fin D.gates.length, (rd (D.gates.get j) 0 = true ↔ j = i0) ∧ (rd (D.gates.get j) 10 = true ↔ j = i1)) →
      (∃ y0, y0 < 11 + i0.val ∧ y0 ≠ 0 ∧ D.gates.get i0 = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, y0]⟩) →
      (∃ y1, y1 < 11 + i1.val ∧ y1 ≠ 10 ∧ D.gates.get i1 = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, y1]⟩) →
      (∀ k : Fin 10, 0 < k.val → D.gates.countP (fun g => rd g k.val) ≤ 3 ∧ ∀ i : Fin D.gates.length, rd (D.gates.get i) k.val = true → (D.gates.get i).op.eval [true, false] = false → D.gates.countP (fun h => rd h k.val || rd h (11 + i.val)) ≤ 3) →
      (∀ c : Bool, ∃ x, w x (11 + u.val) = c ∧ w x 27 = !c) →
      ¬ ∀ x : Fin 10 → Bool, (w x (11 + u.val) || w x 27) = f x) :
    (∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x1] : PEqualNP.CircuitLowerBounds.Gate };       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));       have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;       (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 ((10 : ℕ) + ↑x3) = Bool.true ∧ x9 x10 ((10 : ℕ) + ↑x4) = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x11 ((10 : ℕ) + ↑x4) = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x12 ((10 : ℕ) + ↑x4) = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x13 ((10 : ℕ) + ↑x4) = Bool.false) := by
  intro x1 C0 u0 v0 hfan0 hsize0 gSeed fP w0 hLeft0 hRight0 hSound0
  by_contra hUncov0
  -- Basic local definitions (no match, no GateOp.eval in simp)
  let rd : Gate → ℕ → Bool := fun g i =>
    (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains i
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have eval_nil : ∀ (n : ℕ) (x : List Bool), ({ gates := [], output := n } : Circuit).eval x = x.getD n false := fun _ _ => rfl
  have rd_and : ∀ xs i, rd ⟨.and, xs⟩ i = (xs.take 2).contains i := fun _ _ => rfl
  have rd_or : ∀ xs i, rd ⟨.or, xs⟩ i = (xs.take 2).contains i := fun _ _ => rfl
  have rd_not : ∀ xs i, rd ⟨.not, xs⟩ i = (xs.take 1).contains i := fun _ _ => rfl
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have stepLen : ∀ (ws : List Bool) (g : Gate), (step ws g).length = ws.length + 1 := fun ws g => by
    simp only [step, List.length_append, List.length_singleton]
  have stepDef : ∀ (ws : List Bool) (g : Gate),
      step ws g = ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)] := fun _ _ => rfl
  have runLen : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      dsimp only [step]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have retain : ∀ (gs : List Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons, ih (step ws g) i (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact List.getD_append ws _ false i hi
  let fList : (Fin 10 → Bool) → Bool := fun x =>
    let v := Fin.ofNat 10
    (List.range 5).any fun a =>
      x (v a) && (x (v ((a + 1) % 5)) || x (v (a + 5))) ||
      x (v (a + 5)) && x (v (5 + (a + 2) % 5))
  have pc10 : ∀ x : Fin 10 → Bool, fList x = fP x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    have h1 : fList x = ((x 0 && (x 1 || x 5) || x 5 && x 7) || ((x 1 && (x 2 || x 6) || x 6 && x 8) ||
        ((x 2 && (x 3 || x 7) || x 7 && x 9) || ((x 3 && (x 4 || x 8) || x 8 && x 5) ||
        ((x 4 && (x 0 || x 9) || x 9 && x 6) || false))))) := rfl
    rw [h1]
    dsimp only [fP]
    simp only [Bool.and_or_distrib_left, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true]
    constructor <;> (intro h; simp only [or_assoc] at h ⊢; rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h])
  have fPZero : fP (fun _ => false) = false := by decide
  have fPUnit : ∀ k : Fin 10, fP (fun i => decide (i = k)) = false := by decide
  have fPEdge01 : fP (fun i : Fin 10 => decide (i = 0 ∨ i = 1)) = true := by decide
  have exactPair0 : ∀ x : Fin 10 → Bool, (w0 x (10 + u0.val) || w0 x (10 + v0.val)) = fP x := by
    intro x
    cases h : fP x with
    | false =>
      obtain ⟨h1, h2⟩ := hSound0 x h
      simp [h1, h2]
    | true =>
      cases h1 : w0 x (10 + u0.val) <;> cases h2 : w0 x (10 + v0.val)
      · exact False.elim (hUncov0 ⟨x, h, h1, h2⟩)
      · rfl
      · rfl
      · rfl
  -- Petersen automorphisms (10 rows sending k ↦ 9)
  let f670 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  have f670Zero : f670 (fun _ => false) = false := by decide
  let aut9 : Fin 10 → Fin 10 → Fin 10 := fun k i =>
    Fin.ofNat 10 ((([[9,4,0,1,6,7,3,5,2,8], [4,9,6,1,0,3,7,8,2,5], [0,4,9,6,1,5,3,7,8,2],
      [0,1,6,9,4,5,2,8,7,3], [4,0,1,6,9,3,5,2,8,7], [4,0,1,2,3,9,5,6,7,8],
      [0,4,3,2,1,5,9,8,7,6], [0,1,6,8,5,4,2,9,3,7], [0,1,2,7,5,4,6,3,9,8],
      [0,1,2,3,4,5,6,7,8,9]] : List (List ℕ)).getD k.val []).getD i.val 0)
  let inv9 : Fin 10 → Fin 10 → Fin 10 := fun k i =>
    Fin.ofNat 10 ((([[2,3,8,6,1,7,4,5,9,0], [4,3,8,5,0,9,2,6,7,1], [0,4,9,6,1,5,3,7,8,2],
      [0,1,6,9,4,5,2,8,7,3], [1,2,7,5,0,6,3,9,8,4], [1,2,3,4,0,6,7,8,9,5],
      [0,4,3,2,1,5,9,8,7,6], [0,1,6,8,5,4,2,9,3,7], [0,1,2,7,5,4,6,3,9,8],
      [0,1,2,3,4,5,6,7,8,9]] : List (List ℕ)).getD k.val []).getD i.val 0)
  let edges10 : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let pAdj : Fin 10 → Fin 10 → Bool := fun i j =>
    edges10.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)
  have aut9Fix : ∀ k : Fin 10, aut9 k k = 9 := by decide
  have aut9Left : ∀ k i : Fin 10, inv9 k (aut9 k i) = i := by decide
  have aut9Right : ∀ k i : Fin 10, aut9 k (inv9 k i) = i := by decide
  have aut9Inj : ∀ k i j : Fin 10, aut9 k i = aut9 k j → i = j := fun k i j h => by
    rw [← aut9Left k i, h, aut9Left k j]
  have aut9Surj : ∀ k j : Fin 10, ∃ i : Fin 10, aut9 k i = j := fun k j => ⟨inv9 k j, aut9Right k j⟩
  have pAdjSymm : ∀ i j : Fin 10, pAdj i j = pAdj j i := by
    intro i j
    dsimp only [pAdj]
    congr 1; funext e; exact Bool.or_comm _ _
  have aut9Edge : ∀ k : Fin 10, ∀ e ∈ edges10, pAdj (aut9 k e.1) (aut9 k e.2) = true := by decide
  have inv9Edge : ∀ k : Fin 10, ∀ e ∈ edges10, pAdj (inv9 k e.1) (inv9 k e.2) = true := by decide
  have aut9Adj : ∀ k i j : Fin 10, pAdj (aut9 k i) (aut9 k j) = pAdj i j := by
    intro k i j
    have hdir : ∀ (fn : Fin 10 → Fin 10), (∀ e ∈ edges10, pAdj (fn e.1) (fn e.2) = true) →
        ∀ a c : Fin 10, pAdj a c = true → pAdj (fn a) (fn c) = true := by
      intro fn hfn a c hac
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hac
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfn e he
      · rw [pAdjSymm]; exact hfn e he
    have hiff : pAdj (aut9 k i) (aut9 k j) = true ↔ pAdj i j = true := by
      constructor
      · intro h
        have h' := hdir (inv9 k) (inv9Edge k) (aut9 k i) (aut9 k j) h
        rwa [aut9Left, aut9Left] at h'
      · exact hdir (aut9 k) (aut9Edge k) i j
    exact Bool.eq_iff_iff.mpr hiff
  have inv9Adj : ∀ k i j : Fin 10, pAdj (inv9 k i) (inv9 k j) = pAdj i j := by
    intro k i j
    have h := aut9Adj k (inv9 k i) (inv9 k j)
    rw [aut9Right, aut9Right] at h
    exact h.symm
  have fP_iff : ∀ x : Fin 10 → Bool, fP x = true ↔ ∃ i j : Fin 10, pAdj i j = true ∧ x i = true ∧ x j = true := by
    intro x
    have hlist : fP x = edges10.any (fun e => x e.1 && x e.2) := by
      change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) =
        ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) ||
        ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) ||
        ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
      simp only [Bool.or_false, Bool.or_assoc]
    rw [hlist, List.any_eq_true]
    constructor
    · rintro ⟨e, he, hxy⟩
      simp only [Bool.and_eq_true] at hxy
      exact ⟨e.1, e.2, List.any_eq_true.mpr ⟨e, he, by simp⟩, hxy.1, hxy.2⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hij
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e, he, by simp [hi, hj]⟩
      · exact ⟨e, he, by simp [hi, hj]⟩
  let edges9 : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  have f670_iff : ∀ y : Fin 9 → Bool, f670 y = true ↔
      ∃ i j : Fin 9, pAdj (Fin.castSucc i) (Fin.castSucc j) = true ∧ y i = true ∧ y j = true := by
    intro y
    have hlist : f670 y = edges9.any (fun e => y e.1 && y e.2) := by
      change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) ||
        (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) ||
        (y 6 && y 8) || (y 8 && y 5)) =
        ((y 0 && y 1) || ((y 1 && y 2) || ((y 2 && y 3) || ((y 3 && y 4) || ((y 4 && y 0) ||
        ((y 0 && y 5) || ((y 1 && y 6) || ((y 2 && y 7) || ((y 3 && y 8) || ((y 5 && y 7) ||
        ((y 6 && y 8) || ((y 8 && y 5) || false))))))))))))
      simp only [Bool.or_false, Bool.or_assoc]
    rw [hlist, List.any_eq_true]
    constructor
    · rintro ⟨e, he, hxy⟩
      simp only [Bool.and_eq_true] at hxy
      have hp : ∀ e' ∈ edges9, pAdj (Fin.castSucc e'.1) (Fin.castSucc e'.2) = true := by decide
      exact ⟨e.1, e.2, hp e he, hxy.1, hxy.2⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hij
      have h10to9 : ∀ e' ∈ edges10, e'.1 = 9 ∨ e'.2 = 9 ∨
          edges9.any (fun d => Fin.castSucc d.1 == e'.1 && Fin.castSucc d.2 == e'.2) = true := by decide
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      have hne9 : ∀ k : Fin 9, Fin.castSucc k ≠ (9 : Fin 10) := fun k hk => by
        have := congrArg Fin.val hk; simp at this; omega
      have hhas : edges9.any (fun d => Fin.castSucc d.1 == e.1 && Fin.castSucc d.2 == e.2) = true := by
        rcases h10to9 e he with h1 | h2 | h3
        · rcases hm with ⟨h1', _⟩ | ⟨h1', _⟩
          · exact absurd (h1'.symm.trans h1) (hne9 i)
          · exact absurd (h1'.symm.trans h1) (hne9 j)
        · rcases hm with ⟨_, h2'⟩ | ⟨_, h2'⟩
          · exact absurd (h2'.symm.trans h2) (hne9 j)
          · exact absurd (h2'.symm.trans h2) (hne9 i)
        · exact h3
      obtain ⟨d, hd, hdm⟩ := List.any_eq_true.mp hhas
      simp only [Bool.and_eq_true, beq_iff_eq] at hdm
      refine ⟨d, hd, ?_⟩
      rcases hm with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · have hd1 : d.1 = i := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.1.trans h1'))
        have hd2 : d.2 = j := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.2.trans h2'))
        simp [hd1, hd2, hi, hj]
      · have hd1 : d.1 = j := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.1.trans h1'))
        have hd2 : d.2 = i := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.2.trans h2'))
        simp [hd1, hd2, hi, hj]
  have aut9Match : ∀ (k : Fin 10) (y : Fin 9 → Bool),
      fP (fun i : Fin 10 => if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)) = f670 y := by
    intro k y
    have hiff : fP (fun i : Fin 10 => if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)) = true ↔ f670 y = true := by
      rw [fP_iff (fun i : Fin 10 => if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)), f670_iff y]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        have hik : i ≠ k := by intro h; simp [h] at hi
        have hjk : j ≠ k := by intro h; simp [h] at hj
        have hi9 : (aut9 k i).val < 9 := by
          have hne : aut9 k i ≠ 9 := fun h => hik (aut9Inj k i k (h.trans (aut9Fix k).symm))
          have hlt := (aut9 k i).isLt
          have : (aut9 k i).val ≠ 9 := fun hv => hne (Fin.ext hv)
          omega
        have hj9 : (aut9 k j).val < 9 := by
          have hne : aut9 k j ≠ 9 := fun h => hjk (aut9Inj k j k (h.trans (aut9Fix k).symm))
          have hlt := (aut9 k j).isLt
          have : (aut9 k j).val ≠ 9 := fun hv => hne (Fin.ext hv)
          omega
        refine ⟨⟨(aut9 k i).val, hi9⟩, ⟨(aut9 k j).val, hj9⟩, ?_, ?_, ?_⟩
        · have hci : Fin.castSucc (⟨(aut9 k i).val, hi9⟩ : Fin 9) = aut9 k i := Fin.ext rfl
          have hcj : Fin.castSucc (⟨(aut9 k j).val, hj9⟩ : Fin 9) = aut9 k j := Fin.ext rfl
          rw [hci, hcj, aut9Adj]; exact hij
        · simpa [hik, Fin.ofNat, Nat.mod_eq_of_lt hi9] using hi
        · simpa [hjk, Fin.ofNat, Nat.mod_eq_of_lt hj9] using hj
      · rintro ⟨i, j, hij, hi, hj⟩
        obtain ⟨a, ha⟩ := aut9Surj k (Fin.castSucc i)
        obtain ⟨c, hc⟩ := aut9Surj k (Fin.castSucc j)
        have hak : a ≠ k := by
          intro h; subst h; rw [aut9Fix] at ha
          have : i.val = 9 := (congrArg Fin.val ha).symm
          omega
        have hck : c ≠ k := by
          intro h; subst h; rw [aut9Fix] at hc
          have : j.val = 9 := (congrArg Fin.val hc).symm
          omega
        refine ⟨a, c, ?_, ?_, ?_⟩
        · rw [← aut9Adj k, ha, hc]; exact hij
        · simp only [hak, ↓reduceIte, ha, Fin.val_castSucc]
          have : Fin.ofNat 9 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
          rw [this]; exact hi
        · simp only [hck, ↓reduceIte, hc, Fin.val_castSucc]
          have : Fin.ofNat 9 j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
          rw [this]; exact hj
    exact Bool.eq_iff_iff.mpr hiff
  let aut0 : Fin 10 → Fin 10 → Fin 10 := fun k i => inv9 0 (aut9 k i)
  let inv0 : Fin 10 → Fin 10 → Fin 10 := fun k i => inv9 k (aut9 0 i)
  have aut0Fix : ∀ k : Fin 10, aut0 k k = 0 := fun k => by
    dsimp only [aut0]; rw [aut9Fix k, ← aut9Fix 0, aut9Left 0 0]
  have aut0Left : ∀ k i : Fin 10, inv0 k (aut0 k i) = i := fun k i => by
    dsimp only [aut0, inv0]; rw [aut9Right 0, aut9Left k]
  have aut0Right : ∀ k i : Fin 10, aut0 k (inv0 k i) = i := fun k i => by
    dsimp only [aut0, inv0]; rw [aut9Right k, aut9Left 0]
  have aut0Adj : ∀ k i j : Fin 10, pAdj (aut0 k i) (aut0 k j) = pAdj i j := fun k i j => by
    dsimp only [aut0]; rw [inv9Adj, aut9Adj]
  have aut0Match : ∀ (k : Fin 10) (y : Fin 10 → Bool), fP (fun i => y (aut0 k i)) = fP y := by
    intro k y
    have hiff : fP (fun i => y (aut0 k i)) = true ↔ fP y = true := by
      rw [fP_iff (fun i => y (aut0 k i)), fP_iff y]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        exact ⟨aut0 k i, aut0 k j, (aut0Adj k i j).trans hij, hi, hj⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨inv0 k i, inv0 k j, ?_, ?_, ?_⟩
        · rw [← aut0Adj k, aut0Right, aut0Right]; exact hij
        · rw [aut0Right]; exact hi
        · rw [aut0Right]; exact hj
    exact Bool.eq_iff_iff.mpr hiff
  -- Constant/copy propagation simplifier engine (zero match)
  let evalV : List Bool → Sum Bool ℕ → Bool := fun ws s =>
    Sum.casesOn s (fun c => c) (fun j => ws.getD j false)
  let simpGate : ℕ → List (Sum Bool ℕ) → List Gate → Gate → Sum Bool ℕ × List Gate :=
    fun n env acc g =>
      GateOp.casesOn g.op
        (List.casesOn g.inputs (.inl true, acc) fun a l =>
          List.casesOn l (env.getD a (.inl false), acc) fun c l2 =>
            List.casesOn l2
              (Sum.casesOn (env.getD a (.inl false))
                (fun ba => Bool.casesOn ba (.inl false, acc) (env.getD c (.inl false), acc))
                (fun wa => Sum.casesOn (env.getD c (.inl false))
                  (fun bc => Bool.casesOn bc (.inl false, acc) (.inr wa, acc))
                  (fun wc => if wa = wc then (.inr wa, acc) else (.inr (n + acc.length), acc ++ [⟨.and, [wa, wc]⟩]))))
              (fun _ _ => (.inl false, acc)))
        (List.casesOn g.inputs (.inl false, acc) fun a l =>
          List.casesOn l (env.getD a (.inl false), acc) fun c l2 =>
            List.casesOn l2
              (Sum.casesOn (env.getD a (.inl false))
                (fun ba => Bool.casesOn ba (env.getD c (.inl false), acc) (.inl true, acc))
                (fun wa => Sum.casesOn (env.getD c (.inl false))
                  (fun bc => Bool.casesOn bc (.inr wa, acc) (.inl true, acc))
                  (fun wc => if wa = wc then (.inr wa, acc) else (.inr (n + acc.length), acc ++ [⟨.or, [wa, wc]⟩]))))
              (fun _ _ => (.inl false, acc)))
        (List.casesOn g.inputs (.inl true, acc) fun a _ =>
          Sum.casesOn (env.getD a (.inl false))
            (fun c => (.inl (!c), acc))
            (fun wa => (.inr (n + acc.length), acc ++ [⟨.not, [wa]⟩])))
        (fun _ => (.inl false, acc))
        (.inl false, acc)
  let simpStep : ℕ → (List (Sum Bool ℕ) × List Gate) → Gate → (List (Sum Bool ℕ) × List Gate) :=
    fun n st g => (st.1 ++ [(simpGate n st.1 st.2 g).1], (simpGate n st.1 st.2 g).2)
  have simpStep_envLen : ∀ n st g, (simpStep n st g).1.length = st.1.length + 1 := fun _ st _ => by
    simp only [simpStep, List.length_append, List.length_cons, List.length_nil]
  have simpStep_envPrefix : ∀ n st g i, i < st.1.length →
      (simpStep n st g).1.getD i (.inl false) = st.1.getD i (.inl false) := fun _ st _ i hi =>
    List.getD_append st.1 _ (.inl false) i hi
  have simpStep_lenLe : ∀ n st g, (simpStep n st g).2.length ≤ st.2.length + 1 := by
    intro n st g
    rcases g with ⟨op, inputs⟩
    cases op with
    | not =>
      cases inputs with
      | nil => exact Nat.le_succ _
      | cons a _ =>
        dsimp only [simpStep, simpGate]
        cases st.1.getD a (.inl false) with
        | inl _ => exact Nat.le_succ _
        | inr _ => simp only [List.length_append, List.length_cons, List.length_nil]; omega
    | and =>
      cases inputs with
      | nil => exact Nat.le_succ _
      | cons a l =>
        cases l with
        | nil => exact Nat.le_succ _
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact Nat.le_succ _
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact Nat.le_succ _
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact Nat.le_succ _
                · simp only [heq, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
          | cons _ _ => exact Nat.le_succ _
    | or =>
      cases inputs with
      | nil => exact Nat.le_succ _
      | cons a l =>
        cases l with
        | nil => exact Nat.le_succ _
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact Nat.le_succ _
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact Nat.le_succ _
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact Nat.le_succ _
                · simp only [heq, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
          | cons _ _ => exact Nat.le_succ _
    | mod _ => exact Nat.le_succ _
    | maj => exact Nat.le_succ _
  have simpStep_fan : ∀ n st g, FanInTwo ⟨st.2, 0⟩ → FanInTwo ⟨(simpStep n st g).2, 0⟩ := by
    intro n st g hst
    rcases g with ⟨op, inputs⟩
    have hadd : ∀ op' is, op' ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → is.length ≤ 2 →
        FanInTwo ⟨st.2 ++ [⟨op', is⟩], 0⟩ := by
      intro op' is hop his h hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hst h hm
      · obtain rfl := List.mem_singleton.mp hm
        exact ⟨hop, his⟩
    cases op with
    | not =>
      cases inputs with
      | nil => exact hst
      | cons a _ =>
        dsimp only [simpStep, simpGate]
        cases st.1.getD a (.inl false) with
        | inl _ => exact hst
        | inr wa => exact hadd .not [wa] (Or.inr (Or.inr rfl)) (by simp)
    | and =>
      cases inputs with
      | nil => exact hst
      | cons a l =>
        cases l with
        | nil => exact hst
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact hst
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact hst
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact hst
                · simp only [heq, ↓reduceIte]; exact hadd .and [wa, wc] (Or.inl rfl) (by simp)
          | cons _ _ => exact hst
    | or =>
      cases inputs with
      | nil => exact hst
      | cons a l =>
        cases l with
        | nil => exact hst
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact hst
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact hst
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact hst
                · simp only [heq, ↓reduceIte]; exact hadd .or [wa, wc] (Or.inr (Or.inl rfl)) (by simp)
          | cons _ _ => exact hst
    | mod _ => exact hst
    | maj => exact hst
  -- Normalized gate predicate (ReadsBack, strictly binary AND/OR with distinct inputs, unary NOT)
  let NormGate : ℕ → Gate → Prop := fun k g =>
    (g.op = .not ∧ ∃ a, a < k ∧ g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < k ∧ b < k ∧ a ≠ b ∧ g.inputs = [a, b])
  let NormList : ℕ → List Gate → Prop := fun n gs =>
    ∀ j g, gs[j]? = some g → NormGate (n + j) g
  have simpStep_norm : ∀ n st g,
      NormList n st.2 →
      (∀ s ∈ st.1, ∀ j, s = .inr j → j < n + st.2.length) →
      NormList n (simpStep n st g).2 := by
    intro n st g hnorm hbdd
    have hvalBdd : ∀ a j, st.1.getD a (.inl false) = .inr j → j < n + st.2.length := by
      intro a j hj
      by_cases ha : a < st.1.length
      · rw [List.getD_eq_getElem _ _ ha] at hj
        exact hbdd _ (List.getElem_mem ha) j hj
      · rw [List.getD_eq_default _ _ (by omega)] at hj; cases hj
    have haddN : ∀ g', NormGate (n + st.2.length) g' → NormList n (st.2 ++ [g']) := by
      intro g' hg' j h hj
      by_cases hlt : j < st.2.length
      · rw [List.getElem?_append_left hlt] at hj
        exact hnorm j h hj
      · have heq : j = st.2.length := by
          have hjlt : j < (st.2 ++ [g']).length := (List.getElem?_eq_some_iff.mp hj).1
          simp only [List.length_append, List.length_singleton] at hjlt; omega
        subst heq
        rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hj
        cases hj; exact hg'
    rcases g with ⟨op, inputs⟩
    cases op with
    | not =>
      cases inputs with
      | nil => exact hnorm
      | cons a _ =>
        dsimp only [simpStep, simpGate]
        cases ha : st.1.getD a (.inl false) with
        | inl _ => exact hnorm
        | inr wa => exact haddN ⟨.not, [wa]⟩ (Or.inl ⟨rfl, wa, hvalBdd a wa ha, rfl⟩)
    | and =>
      cases inputs with
      | nil => exact hnorm
      | cons a l =>
        cases l with
        | nil => exact hnorm
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact hnorm
            | inr wa =>
              cases hc : st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact hnorm
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact hnorm
                · simp only [heq, ↓reduceIte]
                  exact haddN ⟨.and, [wa, wc]⟩
                    (Or.inr ⟨Or.inl rfl, wa, wc, hvalBdd a wa ha, hvalBdd c wc hc, heq, rfl⟩)
          | cons _ _ => exact hnorm
    | or =>
      cases inputs with
      | nil => exact hnorm
      | cons a l =>
        cases l with
        | nil => exact hnorm
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact hnorm
            | inr wa =>
              cases hc : st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact hnorm
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact hnorm
                · simp only [heq, ↓reduceIte]
                  exact haddN ⟨.or, [wa, wc]⟩
                    (Or.inr ⟨Or.inr rfl, wa, wc, hvalBdd a wa ha, hvalBdd c wc hc, heq, rfl⟩)
          | cons _ _ => exact hnorm
    | mod _ => exact hnorm
    | maj => exact hnorm
  -- Soundness of simpStep for arbitrary base list `base` of length `n`
  have simpStep_sound : ∀ (n : ℕ) (st : List (Sum Bool ℕ) × List Gate) (g : Gate)
      (base orig : List Bool),
      base.length = n →
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      orig.length = st.1.length →
      (∀ s ∈ st.1, ∀ j, s = .inr j → j < n + st.2.length) →
      (∀ i < st.1.length, evalV (st.2.foldl step base) (st.1.getD i (.inl false)) = orig.getD i false) →
      (∀ s ∈ (simpStep n st g).1, ∀ j, s = .inr j → j < n + (simpStep n st g).2.length) ∧
      (∀ i < (simpStep n st g).1.length,
        evalV ((simpStep n st g).2.foldl step base) ((simpStep n st g).1.getD i (.inl false)) =
        (step orig g).getD i false) := by
    intro n st g base orig hbase hop hglen hlen hbdd htr
    have htrAll : ∀ a, evalV (st.2.foldl step base) (st.1.getD a (.inl false)) = orig.getD a false := by
      intro a
      by_cases ha : a < st.1.length
      · exact htr a ha
      · rw [List.getD_eq_default st.1 _ (by omega), List.getD_eq_default orig _ (by omega)]
    have hwsLen : (st.2.foldl step base).length = n + st.2.length := by
      rw [runLen, hbase]
    have hvalBdd : ∀ a j, st.1.getD a (.inl false) = .inr j → j < n + st.2.length := by
      intro a j hj
      by_cases ha : a < st.1.length
      · rw [List.getD_eq_getElem _ _ ha] at hj
        exact hbdd _ (List.getElem_mem ha) j hj
      · rw [List.getD_eq_default _ _ (by omega)] at hj; cases hj
    have hpush : ∀ (val : Sum Bool ℕ) (acc' : List Gate)
        (hext : acc' = st.2 ∨ ∃ g', acc' = st.2 ++ [g'])
        (hvb : ∀ j, val = .inr j → j < n + acc'.length)
        (hve : evalV (acc'.foldl step base) val = g.op.eval (g.inputs.map fun i => orig.getD i false)),
        (∀ s ∈ st.1 ++ [val], ∀ j, s = .inr j → j < n + acc'.length) ∧
        (∀ i < (st.1 ++ [val]).length,
          evalV (acc'.foldl step base) ((st.1 ++ [val]).getD i (.inl false)) = (step orig g).getD i false) := by
      intro val acc' hext hvb hve
      have haccLe : st.2.length ≤ acc'.length := by
        rcases hext with rfl | ⟨g', rfl⟩
        · exact le_rfl
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hkeep : ∀ s, (∀ j, s = .inr j → j < n + st.2.length) →
          evalV (acc'.foldl step base) s = evalV (st.2.foldl step base) s := by
        intro s hs
        cases s with
        | inl c => rfl
        | inr j =>
          rcases hext with rfl | ⟨g', rfl⟩
          · rfl
          · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            exact List.getD_append _ _ false j (by rw [hwsLen]; exact hs j rfl)
      constructor
      · intro s hs j hj
        rcases List.mem_append.mp hs with hs | hs
        · exact lt_of_lt_of_le (hbdd s hs j hj) (Nat.add_le_add_left haccLe n)
        · obtain rfl := List.mem_singleton.mp hs
          exact hvb j hj
      · intro i hi
        by_cases hilt : i < st.1.length
        · rw [List.getD_append _ _ _ _ hilt, List.getD_append orig _ _ _ (by omega)]
          rw [hkeep _ (hvalBdd i), htr i hilt]
        · have hiEq : i = st.1.length := by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega
          subst hiEq
          rw [List.getD_append_right st.1 _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          dsimp only [step]
          rw [List.getD_append_right orig _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
          exact hve
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil =>
        exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h) rfl
      | cons a l =>
        cases l with
        | nil =>
          exact hpush (st.1.getD a (.inl false)) st.2 (Or.inl rfl) (hvalBdd a)
            (by simpa [eval_and] using htrAll a)
        | cons c l2 =>
          cases l2 with
          | nil =>
            have hgoal : GateOp.and.eval ([a, c].map fun i => orig.getD i false) =
                (evalV (st.2.foldl step base) (st.1.getD a (.inl false)) &&
                 evalV (st.2.foldl step base) (st.1.getD c (.inl false))) := by
              simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true,
                htrAll a, htrAll c]
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba =>
              cases ba with
              | false =>
                exact hpush (.inl false) st.2 (Or.inl rfl) (fun _ h => by cases h)
                  (by rw [hgoal, ha]; rfl)
              | true =>
                exact hpush (st.1.getD c (.inl false)) st.2 (Or.inl rfl) (hvalBdd c)
                  (by rw [hgoal, ha]; simp only [evalV, Bool.true_and])
            | inr wa =>
              cases hc : st.1.getD c (.inl false) with
              | inl bc =>
                cases bc with
                | false =>
                  exact hpush (.inl false) st.2 (Or.inl rfl) (fun _ h => by cases h)
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.and_false])
                | true =>
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj)) (by rw [hgoal, ha, hc]; simp only [evalV, Bool.and_true])
              | inr wc =>
                by_cases heq : wa = wc
                · subst heq; simp only [↓reduceIte]
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj))
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.and_self])
                · simp only [heq, ↓reduceIte]
                  exact hpush (.inr (n + st.2.length)) (st.2 ++ [⟨.and, [wa, wc]⟩]) (Or.inr ⟨_, rfl⟩)
                    (fun j hj => by cases hj; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                    (by
                      rw [hgoal, ha, hc, List.foldl_append, List.foldl_cons, List.foldl_nil]
                      dsimp only [evalV, step]
                      rw [List.getD_append_right _ _ _ _ hwsLen.le, hwsLen, Nat.sub_self, List.getD_cons_zero]
                      simp only [eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true])
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil =>
        exact hpush (.inl false) st.2 (Or.inl rfl) (fun _ h => by cases h) rfl
      | cons a l =>
        cases l with
        | nil =>
          exact hpush (st.1.getD a (.inl false)) st.2 (Or.inl rfl) (hvalBdd a)
            (by simpa [eval_or] using htrAll a)
        | cons c l2 =>
          cases l2 with
          | nil =>
            have hgoal : GateOp.or.eval ([a, c].map fun i => orig.getD i false) =
                (evalV (st.2.foldl step base) (st.1.getD a (.inl false)) ||
                 evalV (st.2.foldl step base) (st.1.getD c (.inl false))) := by
              simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                htrAll a, htrAll c]
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba =>
              cases ba with
              | true =>
                exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h)
                  (by rw [hgoal, ha]; rfl)
              | false =>
                exact hpush (st.1.getD c (.inl false)) st.2 (Or.inl rfl) (hvalBdd c)
                  (by rw [hgoal, ha]; simp only [evalV, Bool.false_or])
            | inr wa =>
              cases hc : st.1.getD c (.inl false) with
              | inl bc =>
                cases bc with
                | true =>
                  exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h)
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.or_true])
                | false =>
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj)) (by rw [hgoal, ha, hc]; simp only [evalV, Bool.or_false])
              | inr wc =>
                by_cases heq : wa = wc
                · subst heq; simp only [↓reduceIte]
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj))
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.or_self])
                · simp only [heq, ↓reduceIte]
                  exact hpush (.inr (n + st.2.length)) (st.2 ++ [⟨.or, [wa, wc]⟩]) (Or.inr ⟨_, rfl⟩)
                    (fun j hj => by cases hj; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                    (by
                      rw [hgoal, ha, hc, List.foldl_append, List.foldl_cons, List.foldl_nil]
                      dsimp only [evalV, step]
                      rw [List.getD_append_right _ _ _ _ hwsLen.le, hwsLen, Nat.sub_self, List.getD_cons_zero]
                      simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false])
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil =>
        exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h) rfl
      | cons a l =>
        have hgoal : GateOp.not.eval ((a :: l).map fun i => orig.getD i false) =
            !(evalV (st.2.foldl step base) (st.1.getD a (.inl false))) := by
          simp only [List.map_cons, eval_not, List.headD_cons, htrAll a]
        dsimp only [simpStep, simpGate]
        cases ha : st.1.getD a (.inl false) with
        | inl ba =>
          exact hpush (.inl (!ba)) st.2 (Or.inl rfl) (fun _ h => by cases h)
            (by rw [hgoal, ha])
        | inr wa =>
          exact hpush (.inr (n + st.2.length)) (st.2 ++ [⟨.not, [wa]⟩]) (Or.inr ⟨_, rfl⟩)
            (fun j hj => by cases hj; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
            (by
              rw [hgoal, ha, List.foldl_append, List.foldl_cons, List.foldl_nil]
              dsimp only [evalV, step]
              rw [List.getD_append_right _ _ _ _ hwsLen.le, hwsLen, Nat.sub_self, List.getD_cons_zero]
              simp only [eval_not, List.map_cons, List.headD_cons])
  have simpFold : ∀ (n : ℕ) (ls : List Gate) (s0 : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ ls, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      FanInTwo ⟨s0.2, 0⟩ →
      (∀ s ∈ s0.1, ∀ j, s = .inr j → j < n + s0.2.length) →
      let sf := ls.foldl (simpStep n) s0
      FanInTwo ⟨sf.2, 0⟩ ∧
      sf.1.length = s0.1.length + ls.length ∧
      sf.2.length ≤ s0.2.length + ls.length ∧
      (∀ i < s0.1.length, sf.1.getD i (.inl false) = s0.1.getD i (.inl false)) ∧
      (∀ s ∈ sf.1, ∀ j, s = .inr j → j < n + sf.2.length) ∧
      (NormList n s0.2 → NormList n sf.2) ∧
      (∀ (base orig : List Bool), base.length = n → orig.length = s0.1.length →
        (∀ i < s0.1.length, evalV (s0.2.foldl step base) (s0.1.getD i (.inl false)) = orig.getD i false) →
        ∀ i < sf.1.length, evalV (sf.2.foldl step base) (sf.1.getD i (.inl false)) = (ls.foldl step orig).getD i false) := by
    intro n ls
    induction ls with
    | nil =>
      intro s0 _ hf hb
      refine ⟨hf, by simp, by simp, fun _ _ => rfl, hb, fun hn => hn, fun _ _ _ _ ht => ht⟩
    | cons g ls ih =>
      intro s0 hlf hf hb
      obtain ⟨hop, hgl⟩ := hlf g List.mem_cons_self
      have hf1 := simpStep_fan n s0 g hf
      have hlen1 := simpStep_lenLe n s0 g
      have hbd1 : ∀ s ∈ (simpStep n s0 g).1, ∀ j, s = .inr j → j < n + (simpStep n s0 g).2.length :=
        (simpStep_sound n s0 g (List.replicate n false)
          (s0.1.map (evalV (s0.2.foldl step (List.replicate n false))))
          (by simp) hop hgl (by simp) hb
          (fun i hi => by
            rw [List.getD_eq_getElem s0.1 _ hi, List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map])).1
      obtain ⟨hf2, hlen2, hsz2, hpref2, hbd2, hnorm2, htr2⟩ :=
        ih (simpStep n s0 g) (fun h hh => hlf h (List.mem_cons_of_mem _ hh)) hf1 hbd1
      refine ⟨hf2, ?_, ?_, ?_, hbd2, ?_, ?_⟩
      · rw [List.foldl_cons, hlen2, simpStep_envLen]; simp; omega
      · rw [List.foldl_cons]; simp only [List.length_cons]; omega
      · intro i hi
        rw [List.foldl_cons, hpref2 i (by rw [simpStep_envLen]; omega), simpStep_envPrefix n s0 g i hi]
      · intro hn0
        exact hnorm2 (simpStep_norm n s0 g hn0 hb)
      · intro base orig hbase horig ht i hi
        rw [List.foldl_cons] at hi ⊢
        obtain ⟨_, ht1⟩ := simpStep_sound n s0 g base orig hbase hop hgl horig hb ht
        exact htr2 base (step orig g) hbase (by simp [step, simpStep_envLen, horig]) ht1 i hi
  let isConst : List (Sum Bool ℕ) → ℕ → Bool := fun env i =>
    Sum.casesOn (env.getD i (.inl false)) (fun _ => true) (fun _ => false)
  have simpStep_dropConst : ∀ n st g i,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      rd g i = true → isConst st.1 i = true →
      (simpStep n st g).2.length = st.2.length := by
    intro n st g i hop hglen hrd hc
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_and] at hrd
            dsimp only [simpStep, simpGate]
            rcases hrd with rfl | rfl
            · cases ha : st.1.getD i (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ => dsimp only [isConst] at hc; rw [ha] at hc; cases hc
            · cases ha : st.1.getD a (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ =>
                cases hi : st.1.getD i (.inl false) with
                | inl bi => cases bi <;> rfl
                | inr _ => dsimp only [isConst] at hc; rw [hi] at hc; cases hc
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_or] at hrd
            dsimp only [simpStep, simpGate]
            rcases hrd with rfl | rfl
            · cases ha : st.1.getD i (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ => dsimp only [isConst] at hc; rw [ha] at hc; cases hc
            · cases ha : st.1.getD a (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ =>
                cases hi : st.1.getD i (.inl false) with
                | inl bi => cases bi <;> rfl
                | inr _ => dsimp only [isConst] at hc; rw [hi] at hc; cases hc
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil => rfl
      | cons a l =>
        simp [rd_not] at hrd
        subst hrd
        dsimp only [simpStep, simpGate]
        cases ha : st.1.getD i (.inl false) with
        | inl _ => rfl
        | inr _ => dsimp only [isConst] at hc; rw [ha] at hc; cases hc
  have simpStep_makesConst : ∀ n st g i,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      rd g i = true → g.op.eval [true, false] = false →
      st.1.getD i (.inl false) = .inl false →
      isConst (simpStep n st g).1 st.1.length = true := by
    intro n st g i hop hglen hrd handnot hfalse
    have hlast : ∀ v, (st.1 ++ [v]).getD st.1.length (.inl false) = v := fun v => by
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil => dsimp only [simpStep, simpGate, isConst]; rw [hlast]
      | cons a l =>
        cases l with
        | nil =>
          simp [rd_and] at hrd; subst hrd
          dsimp only [simpStep, simpGate, isConst]; rw [hlast, hfalse]
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_and] at hrd
            dsimp only [simpStep, simpGate, isConst]; rw [hlast]
            rcases hrd with rfl | rfl
            · rw [hfalse]
            · cases st.1.getD a (.inl false) with
              | inl ba => cases ba <;> (try rfl); rw [hfalse]
              | inr _ => rw [hfalse]
          | cons _ _ => simp at hglen
    · rw [eval_or] at handnot; cases handnot
    · cases inputs with
      | nil => dsimp only [simpStep, simpGate, isConst]; rw [hlast]
      | cons a l =>
        simp [rd_not] at hrd; subst hrd
        dsimp only [simpStep, simpGate, isConst]; rw [hlast, hfalse]
  have simpStep_makesConstTrueOr : ∀ n st g i,
      g.op = .or → g.inputs.length ≤ 2 →
      rd g i = true → st.1.getD i (.inl false) = .inl true →
      isConst (simpStep n st g).1 st.1.length = true := by
    intro n st g i hop hglen hrd htrue
    have hlast : ∀ v, (st.1 ++ [v]).getD st.1.length (.inl false) = v := fun v => by
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rcases g with ⟨op, inputs⟩
    subst hop
    cases inputs with
    | nil => dsimp only [simpStep, simpGate, isConst]; rw [hlast]
    | cons a l =>
      cases l with
      | nil =>
        simp [rd_or] at hrd; subst hrd
        dsimp only [simpStep, simpGate, isConst]; rw [hlast, htrue]
      | cons c l2 =>
        cases l2 with
        | nil =>
          simp [rd_or] at hrd
          dsimp only [simpStep, simpGate, isConst]; rw [hlast]
          rcases hrd with rfl | rfl
          · rw [htrue]
          · cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> (try rfl); rw [htrue]
            | inr _ => rw [htrue]
        | cons _ _ => simp at hglen
  have countFold : ∀ (n : ℕ) (P : Gate → Bool) (gs : List Gate) (s0 : List (Sum Bool ℕ) × List Gate),
      (∀ g s, g ∈ gs → s.1.length ≥ s0.1.length →
        (∀ i < s0.1.length, s.1.getD i (.inl false) = s0.1.getD i (.inl false)) →
        P g = true → (simpStep n s g).2.length = s.2.length) →
      (gs.foldl (simpStep n) s0).2.length + gs.countP P ≤ s0.2.length + gs.length := by
    intro n P gs
    induction gs with
    | nil => intro s0 _; simp
    | cons g gs ih =>
      intro s0 hdrop
      rw [List.foldl_cons, List.countP_cons, List.length_cons]
      have h1 : (gs.foldl (simpStep n) (simpStep n s0 g)).2.length + gs.countP P ≤
          (simpStep n s0 g).2.length + gs.length := by
        apply ih (simpStep n s0 g)
        intro g' s hg' hlen' hpref' hP'
        apply hdrop g' s (List.mem_cons_of_mem _ hg') (by rw [simpStep_envLen] at hlen'; omega)
        · intro i hi
          rw [hpref' i (by rw [simpStep_envLen]; omega), simpStep_envPrefix n s0 g i hi]
        · exact hP'
      cases hPg : P g with
      | true =>
        have h0 := hdrop g s0 List.mem_cons_self le_rfl (fun _ _ => rfl) hPg
        simp only [h0, ↓reduceIte] at h1 ⊢
        omega
      | false =>
        have h0 := simpStep_lenLe n s0 g
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
  -- Generalized cascade counter: kills gates matching Q (constant under s0) OR reading `s0.1.length + a.length`
  have countFoldGenCascade : ∀ (n : ℕ) (Q : Gate → Bool) (a : List Gate) (g0 : Gate) (c : List Gate)
      (s0 : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ a ++ g0 :: c, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g s, g ∈ a ++ g0 :: c → s.1.length ≥ s0.1.length →
        (∀ i < s0.1.length, s.1.getD i (.inl false) = s0.1.getD i (.inl false)) →
        Q g = true → (simpStep n s g).2.length = s.2.length) →
      Q g0 = true →
      isConst (simpStep n (a.foldl (simpStep n) s0) g0).1 (s0.1.length + a.length) = true →
      ((a ++ g0 :: c).foldl (simpStep n) s0).2.length +
        (a ++ g0 :: c).countP (fun h => Q h || rd h (s0.1.length + a.length)) ≤
        s0.2.length + (a ++ g0 :: c).length := by
    intro n Q a g0 c s0 hfanAll hQdrop hQg0 hconst0
    rw [List.foldl_append, List.foldl_cons, List.countP_append, List.countP_cons, List.length_append, List.length_cons]
    have hpre : ∀ (ls : List Gate) (s : List (Sum Bool ℕ) × List Gate),
        (ls.foldl (simpStep n) s).1.length = s.1.length + ls.length ∧
        ∀ i < s.1.length, (ls.foldl (simpStep n) s).1.getD i (.inl false) = s.1.getD i (.inl false) := by
      intro ls
      induction ls with
      | nil => intro s; exact ⟨by simp, fun _ _ => rfl⟩
      | cons g ls ih =>
        intro s
        rw [List.foldl_cons]
        obtain ⟨hl, hp⟩ := ih (simpStep n s g)
        refine ⟨by rw [hl, simpStep_envLen]; simp; omega, fun i hi => ?_⟩
        rw [hp i (by rw [simpStep_envLen]; omega), simpStep_envPrefix n s g i hi]
    have hA : (a.foldl (simpStep n) s0).2.length + a.countP (fun h => Q h || rd h (s0.1.length + a.length)) ≤
        s0.2.length + a.length := by
      have hgen : ∀ (k : ℕ) (ls : List Gate) (s : List (Sum Bool ℕ) × List Gate),
          (∀ g ∈ ls, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
          (∀ g s', g ∈ ls → s'.1.length ≥ s.1.length →
            (∀ i < s.1.length, s'.1.getD i (.inl false) = s.1.getD i (.inl false)) →
            Q g = true → (simpStep n s' g).2.length = s'.2.length) →
          s.1.length + ls.length ≤ k →
          (ls.foldl (simpStep n) s).2.length + ls.countP (fun h => Q h || rd h k) ≤ s.2.length + ls.length := by
        intro k ls
        induction ls with
        | nil => intro s _ _ _; simp
        | cons g ls ih =>
          intro s hlf hqd hle
          rw [List.foldl_cons, List.countP_cons, List.length_cons]
          have h1 := ih (simpStep n s g) (fun h hh => hlf h (List.mem_cons_of_mem _ hh))
            (fun h s' hh hl hp hqh =>
              hqd h s' (List.mem_cons_of_mem _ hh) (by rw [simpStep_envLen] at hl; omega)
                (fun i hi => by rw [hp i (by rw [simpStep_envLen]; omega), simpStep_envPrefix n s g i hi]) hqh)
            (by rw [simpStep_envLen]; simp at hle; omega)
          cases hP : (Q g || rd g k) with
          | true =>
            obtain ⟨hop, hgl⟩ := hlf g List.mem_cons_self
            have hd : (simpStep n s g).2.length = s.2.length := by
              rcases Bool.or_eq_true_iff.mp hP with h1' | h2'
              · exact hqd g s List.mem_cons_self le_rfl (fun _ _ => rfl) h1'
              · have hkge : s.1.length ≤ k := by simp at hle; omega
                exact simpStep_dropConst n s g k hop hgl h2'
                  (by dsimp only [isConst]; rw [List.getD_eq_default _ _ hkge])
            simp only [hd, ↓reduceIte] at h1 ⊢
            omega
          | false =>
            have h0 := simpStep_lenLe n s g
            simp only [Bool.false_eq_true, ↓reduceIte]
            omega
      exact hgen (s0.1.length + a.length) a s0
        (fun g hg => hfanAll g (List.mem_append_left _ hg))
        (fun g s' hg => hQdrop g s' (List.mem_append_left _ hg))
        le_rfl
    let s1 := a.foldl (simpStep n) s0
    have hs1Len : s1.1.length = s0.1.length + a.length := (hpre a s0).1
    have hg0Drop : (simpStep n s1 g0).2.length = s1.2.length :=
      hQdrop g0 s1 (List.mem_append_right _ List.mem_cons_self) (by omega) (hpre a s0).2 hQg0
    have hC : (c.foldl (simpStep n) (simpStep n s1 g0)).2.length +
        c.countP (fun h => Q h || rd h (s0.1.length + a.length)) ≤
        (simpStep n s1 g0).2.length + c.length := by
      apply countFold n (fun h => Q h || rd h (s0.1.length + a.length)) c (simpStep n s1 g0)
      intro g s hg hlen' hpref hP
      obtain ⟨hop, hgl⟩ := hfanAll g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
      rcases Bool.or_eq_true_iff.mp hP with h1' | h2'
      · apply hQdrop g s (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
          (by rw [simpStep_envLen, hs1Len] at hlen'; omega)
        · intro i hi
          rw [hpref i (by rw [simpStep_envLen, hs1Len]; omega), simpStep_envPrefix n s1 g0 i (by omega), (hpre a s0).2 i hi]
        · exact h1'
      · exact simpStep_dropConst n s g (s0.1.length + a.length) hop hgl h2'
          (by
            have hlt : s0.1.length + a.length < (simpStep n s1 g0).1.length := by rw [simpStep_envLen, hs1Len]; omega
            dsimp only [isConst]
            rw [hpref (s0.1.length + a.length) hlt]
            exact hconst0)
    have hPg0 : (Q g0 || rd g0 (s0.1.length + a.length)) = true := by simp [hQg0]
    simp only [hPg0, ↓reduceIte]
    dsimp only [s1] at hg0Drop hC
    omega
  -- Extract HasCircuitSize from simpFold
  have toCircuit : ∀ (n : ℕ) (gs : List Gate) (s0 : List (Sum Bool ℕ) × List Gate) (outIdx : ℕ)
      (target : (Fin n → Bool) → Bool) (origOf : (Fin n → Bool) → List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      FanInTwo ⟨s0.2, 0⟩ →
      (∀ s ∈ s0.1, ∀ j, s = .inr j → j < n + s0.2.length) →
      (∀ y : Fin n → Bool, (origOf y).length = s0.1.length) →
      (∀ y : Fin n → Bool, ∀ i < s0.1.length,
        evalV (s0.2.foldl step (List.ofFn y)) (s0.1.getD i (.inl false)) = (origOf y).getD i false) →
      (∀ y : Fin n → Bool, (gs.foldl step (origOf y)).getD outIdx false = target y) →
      target (fun _ => false) = false →
      HasCircuitSize n target (gs.foldl (simpStep n) s0).2.length := by
    intro n gs s0 outIdx target origOf hgsf hs0f hs0b horigL horigT hEval htar0
    obtain ⟨hff, hflen, _, _, _, _, htr⟩ := simpFold n gs s0 hgsf hs0f hs0b
    let sf := gs.foldl (simpStep n) s0
    have hOutEval : ∀ y : Fin n → Bool,
        evalV (sf.2.foldl step (List.ofFn y)) (sf.1.getD outIdx (.inl false)) = target y := by
      intro y
      by_cases hout : outIdx < sf.1.length
      · exact (htr (List.ofFn y) (origOf y) (by simp) (horigL y) (horigT y) outIdx hout).trans (hEval y)
      · rw [List.getD_eq_default sf.1 _ (by omega)]
        dsimp only [evalV]
        have hlenG : (gs.foldl step (origOf y)).length = sf.1.length := by
          rw [runLen, horigL y, hflen]
        have he := hEval y
        rw [List.getD_eq_default _ _ (by omega)] at he
        exact he
    cases hout : sf.1.getD outIdx (.inl false) with
    | inl c =>
      cases c with
      | true =>
        have hb := hOutEval (fun _ => false)
        rw [hout, htar0] at hb
        cases hb
      | false =>
        refine ⟨⟨[], n⟩, (fun _ h => by cases h), Nat.zero_le _, fun y => ?_⟩
        have hy := hOutEval y
        rw [hout] at hy
        dsimp only [evalV] at hy
        rw [eval_nil, List.getD_eq_default _ _ (by simp)]
        exact hy
    | inr wOut =>
      refine ⟨⟨sf.2, wOut⟩, hff, le_rfl, fun y => ?_⟩
      have hy := hOutEval y
      rw [hout] at hy
      exact hy
  -- Handle x1 = 10 immediately (wire 10 = constant true -> <= 18-gate Petersen circuit -> h4031)
  by_cases hx1 : x1.val < 10
  swap
  · have hx1eq : x1.val = 10 := by have := x1.isLt; omega
    let C18 : Circuit := ⟨C0.gates ++ [⟨.or, [10 + u0.val, 10 + v0.val]⟩], 11 + C0.size⟩
    have hC18fan : FanInTwo C18 := by
      intro g hg
      rcases List.mem_append.mp hg with hm | hm
      · exact hfan0 g hm
      · obtain rfl := List.mem_singleton.mp hm
        exact ⟨Or.inr (Or.inl rfl), by simp⟩
    let env0 : List (Sum Bool ℕ) := (List.range 10).map Sum.inr ++ [.inl true]
    have henv0Len : env0.length = 11 := by simp [env0]
    have henv0Bdd : ∀ s ∈ env0, ∀ j, s = .inr j → j < 10 + ([] : List Gate).length := by
      intro s hs j hj
      rcases List.mem_append.mp hs with h1 | h2
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
        cases hj; simp at hk; omega
      · obtain rfl := List.mem_singleton.mp h2; cases hj
    have hseed10 : ∀ x : Fin 10 → Bool,
        ({ gates := [gSeed], output := 0 } : Circuit).wires (List.ofFn x) = List.ofFn x ++ [true] := by
      intro x
      change List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD x1.val false]] = _
      rw [eval_not, List.headD_cons, List.getD_eq_default _ _ (by simp [hx1eq])]
      rfl
    have htr0 : ∀ y : Fin 10 → Bool, ∀ i < env0.length,
        evalV (([] : List Gate).foldl step (List.ofFn y)) (env0.getD i (.inl false)) =
        (List.ofFn y ++ [true]).getD i false := by
      intro y i hi
      simp only [List.foldl_nil]
      by_cases h10 : i < 10
      · have hl : i < ((List.range 10).map (Sum.inr : ℕ → Sum Bool ℕ)).length := by simp [h10]
        rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range]
        dsimp only [evalV]
        rw [List.getD_append _ _ _ _ (by simp [h10])]
      · have hiEq : i = 10 := by simp [env0] at hi; omega
        subst hiEq
        dsimp only [env0]
        rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp [evalV]
    have hEval18 : ∀ y : Fin 10 → Bool,
        (C18.gates.foldl step (List.ofFn y ++ [true])).getD (11 + C0.size) false = fP y := by
      intro y
      dsimp only [C18]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (C0.gates.foldl step (List.ofFn y ++ [true])).length = 11 + C0.size := by
        rw [runLen]; change (List.ofFn y ++ [true]).length + C0.gates.length = 11 + C0.gates.length; simp
      dsimp only [step]
      rw [List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self, List.getD_cons_zero]
      simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have hw : ∀ k, (C0.gates.foldl step (List.ofFn y ++ [true])).getD k false = w0 y k := fun k => by
        dsimp only [w0]; rw [hseed10 y]; rfl
      rw [hw, hw]
      exact exactPair0 y
    have hhas := toCircuit 10 C18.gates (env0, []) (11 + C0.size) fP (fun y => List.ofFn y ++ [true])
      hC18fan (fun _ h => by cases h) henv0Bdd (fun _ => by simp [henv0Len]) htr0 hEval18 fPZero
    have hszLe : (C18.gates.foldl (simpStep 10) (env0, [])).2.length ≤ 18 := by
      have h1 := (simpFold 10 C18.gates (env0, []) hC18fan (fun _ h => by cases h) henv0Bdd).2.2.1
      have hcl : C18.gates.length ≤ 18 := by
        dsimp only [C18]; simp only [List.length_append, List.length_singleton]
        change C0.gates.length + 1 ≤ 18; change C0.gates.length ≤ 17 at hsize0; omega
      simp at h1; omega
    obtain ⟨E, hEf, hEs, hEe⟩ := hhas
    exact h4031 ⟨E, hEf, hEs.trans hszLe, hEe⟩
  -- Now x1.val < 10. Set up seed0 and general helper lemmas on `List.ofFn x ++ [!x 0]`.
  let seed0 : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0]
  have seed0Len : ∀ x, (seed0 x).length = 11 := fun x => by simp [seed0]
  have rd_iff_4035 : ∀ (g : Gate) (i : ℕ),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      (rd g i = true ↔ (g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs)) := by
    intro g i hop hgl
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rw [rd_and, List.take_of_length_le hgl]
      simp
    · rw [rd_or, List.take_of_length_le hgl]
      simp
    · rw [rd_not]
      cases inputs with
      | nil => simp
      | cons a l => simp [eq_comm]
  -- If no gate in gs reads wire 10, changing wire 10 preserves all wires != 10
  have invisible10 : ∀ (gs : List Gate) (xs ys : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ gs, rd g 10 = false) →
      xs.length = ys.length → 10 < xs.length →
      (∀ j, j ≠ 10 → xs.getD j false = ys.getD j false) →
      ∀ j, j ≠ 10 → (gs.foldl step xs).getD j false = (gs.foldl step ys).getD j false := by
    intro gs
    induction gs with
    | nil => intro xs ys _ _ _ _ h j hj; exact h j hj
    | cons g gs ih =>
      intro xs ys hfan hrd hlen h10 h j hj
      rw [List.foldl_cons, List.foldl_cons]
      obtain ⟨hop, hgl⟩ := hfan g List.mem_cons_self
      have hrdg : rd g 10 = false := hrd g List.mem_cons_self
      have hev : g.op.eval (g.inputs.map fun k => xs.getD k false) =
          g.op.eval (g.inputs.map fun k => ys.getD k false) := by
        rcases g with ⟨op, inputs⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with rfl | rfl | rfl
        · rw [rd_and, List.take_of_length_le hgl] at hrdg
          have hnot : 10 ∉ inputs := by intro hm; rw [List.contains_iff_mem.mpr hm] at hrdg; cases hrdg
          congr 1; exact List.map_congr_left fun k hk => h k (fun heq => hnot (heq ▸ hk))
        · rw [rd_or, List.take_of_length_le hgl] at hrdg
          have hnot : 10 ∉ inputs := by intro hm; rw [List.contains_iff_mem.mpr hm] at hrdg; cases hrdg
          congr 1; exact List.map_congr_left fun k hk => h k (fun heq => hnot (heq ▸ hk))
        · rw [rd_not] at hrdg
          cases inputs with
          | nil => rfl
          | cons a l =>
            have hne : a ≠ 10 := by intro heq; subst heq; simp at hrdg
            simp only [List.map_cons, eval_not, List.headD_cons, h a hne]
      apply ih (step xs g) (step ys g)
        (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hrd g' (List.mem_cons_of_mem _ hg'))
        (by simp [step, hlen]) (by simp [step]; omega)
        (fun k hk => by
          dsimp only [step]
          rw [hev]
          by_cases hlt : k < xs.length
          · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega), h k hk]
          · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen])
        j hj
  -- If C (size <= 18) computes fP on seed0 and never reads wire 10, contradict h4031
  have noRead10_elim : ∀ (C : Circuit), FanInTwo C → C.size ≤ 18 →
      (∀ x : Fin 10 → Bool, C.eval (seed0 x) = fP x) →
      (∀ g ∈ C.gates, rd g 10 = false) → False := by
    intro C hCf hCs hCe hno10
    have houtNe10 : C.output ≠ 10 := by
      intro h10
      have h0 := hCe (fun _ => false)
      change (C.gates.foldl step (seed0 (fun _ => false))).getD C.output false = fP (fun _ => false) at h0
      rw [h10, retain C.gates _ 10 (by rw [seed0Len]; omega), fPZero] at h0
      simp [seed0] at h0
    let env0 : List (Sum Bool ℕ) := (List.range 10).map Sum.inr ++ [.inl false]
    have henv0Bdd : ∀ s ∈ env0, ∀ j, s = .inr j → j < 10 + ([] : List Gate).length := by
      intro s hs j hj
      rcases List.mem_append.mp hs with h1 | h2
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1; cases hj; simp at hk; omega
      · obtain rfl := List.mem_singleton.mp h2; cases hj
    have htr0 : ∀ y : Fin 10 → Bool, ∀ i < env0.length,
        evalV (([] : List Gate).foldl step (List.ofFn y)) (env0.getD i (.inl false)) =
        (List.ofFn y ++ [false]).getD i false := by
      intro y i hi
      simp only [List.foldl_nil]
      by_cases h10 : i < 10
      · have hl : i < ((List.range 10).map (Sum.inr : ℕ → Sum Bool ℕ)).length := by simp [h10]
        rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range]
        dsimp only [evalV]; rw [List.getD_append _ _ _ _ (by simp [h10])]
      · have hiEq : i = 10 := by simp [env0] at hi; omega
        subst hiEq; dsimp only [env0]
        rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp [evalV]
    have hEv : ∀ y : Fin 10 → Bool,
        (C.gates.foldl step (List.ofFn y ++ [false])).getD C.output false = fP y := by
      intro y
      have hinv := invisible10 C.gates (List.ofFn y ++ [false]) (seed0 y) hCf hno10
        (by simp [seed0]) (by simp) (fun j hj => by
          by_cases h10 : j < 10
          · simp only [seed0]; rw [List.getD_append _ _ _ _ (by simp [h10]), List.getD_append _ _ _ _ (by simp [h10])]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [seed0]; omega)])
        C.output houtNe10
      exact hinv.trans (hCe y)
    have hhas := toCircuit 10 C.gates (env0, []) C.output fP (fun y => List.ofFn y ++ [false])
      hCf (fun _ h => by cases h) henv0Bdd (fun _ => by simp [env0]) htr0 hEv fPZero
    have hszLe : (C.gates.foldl (simpStep 10) (env0, [])).2.length ≤ 18 := by
      have h1 := (simpFold 10 C.gates (env0, []) hCf (fun _ h => by cases h) henv0Bdd).2.2.1
      simp at h1; change C.gates.length ≤ 18 at hCs; omega
    obtain ⟨E, hEf, hEs, hEe⟩ := hhas
    exact h4031 ⟨E, hEf, hEs.trans hszLe, hEe⟩
  -- Restricting x 0 = false (and wire 10 = true) on any circuit C computing fP from seed0
  let env0_x0 : List (Sum Bool ℕ) :=
    (List.finRange 10).map (fun i : Fin 10 => if i = 0 then .inl false else .inr (aut9 0 i).val) ++ [.inl true]
  have henv0x0_len : env0_x0.length = 11 := by simp [env0_x0]
  have henv0x0_0 : env0_x0.getD 0 (.inl false) = .inl false := by
    have hl : 0 < ((List.finRange 10).map (fun i : Fin 10 => if i = 0 then Sum.inl false else .inr (aut9 0 i).val)).length := by simp
    rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_finRange]
    simp
  have henv0x0_10 : env0_x0.getD 10 (.inl false) = .inl true := by
    rw [List.getD_append_right _ _ _ _ (by simp)]; simp
  have henv0x0_bdd : ∀ s ∈ env0_x0, ∀ j, s = .inr j → j < 9 + ([] : List Gate).length := by
    intro s hs j hj
    rcases List.mem_append.mp hs with h1 | h2
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h1
      by_cases hi : i = 0
      · simp [hi] at hj
      · simp only [hi, ↓reduceIte, Sum.inr.injEq] at hj; subst hj
        have hne : aut9 0 i ≠ 9 := fun h => hi (aut9Inj 0 i 0 (h.trans (aut9Fix 0).symm))
        have hlt := (aut9 0 i).isLt
        have hnv : (aut9 0 i).val ≠ 9 := fun hv => hne (Fin.ext hv)
        simp; omega
    · obtain rfl := List.mem_singleton.mp h2; cases hj
  have elim0_size : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (seed0 x) = fP x) →
      16 ≤ (C.gates.foldl (simpStep 9) (env0_x0, [])).2.length := by
    intro C hCf hCe
    let xOf : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i =>
      if i = 0 then false else y (Fin.ofNat 9 (aut9 0 i).val)
    have htr0 : ∀ y : Fin 9 → Bool, ∀ i < env0_x0.length,
        evalV (([] : List Gate).foldl step (List.ofFn y)) (env0_x0.getD i (.inl false)) =
        (seed0 (xOf y)).getD i false := by
      intro y i hi
      simp only [List.foldl_nil]
      by_cases h10 : i < 10
      · have hl : i < ((List.finRange 10).map (fun k : Fin 10 => if k = 0 then Sum.inl false else .inr (aut9 0 k).val)).length := by simp [h10]
        rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_finRange]
        simp only [Fin.cast_mk, seed0]
        rw [List.getD_append _ _ _ _ (by simp [h10]), List.getD_eq_getElem _ _ (by simp [h10]), List.getElem_ofFn]
        dsimp only [xOf]
        by_cases h0 : (⟨i, h10⟩ : Fin 10) = 0
        · simp [h0, evalV]
        · simp only [h0, ↓reduceIte]
          dsimp only [evalV]
          have hne : aut9 0 ⟨i, h10⟩ ≠ 9 := fun h => h0 (aut9Inj 0 ⟨i, h10⟩ 0 (h.trans (aut9Fix 0).symm))
          have hlt := (aut9 0 ⟨i, h10⟩).isLt
          have hnv : (aut9 0 ⟨i, h10⟩).val ≠ 9 := fun hv => hne (Fin.ext hv)
          have hlt9 : (aut9 0 ⟨i, h10⟩).val < 9 := by omega
          rw [List.getD_eq_getElem _ _ (by simp [hlt9]), List.getElem_ofFn]
          congr 1; exact Fin.ext (Nat.mod_eq_of_lt hlt9).symm
      · have hiEq : i = 10 := by rw [henv0x0_len] at hi; omega
        subst hiEq
        rw [henv0x0_10]
        simp only [seed0]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [evalV, xOf]
    have hEv : ∀ y : Fin 9 → Bool, (C.gates.foldl step (seed0 (xOf y))).getD C.output false = f670 y := fun y =>
      (hCe (xOf y)).trans (aut9Match 0 y)
    have hhas := toCircuit 9 C.gates (env0_x0, []) C.output f670 (fun y => seed0 (xOf y))
      hCf (fun _ h => by cases h) henv0x0_bdd (fun y => by rw [seed0Len, henv0x0_len]) htr0 hEv f670Zero
    by_contra! hlt16
    obtain ⟨E, hEf, hEs, hEe⟩ := hhas
    exact h670 ⟨E, hEf, by omega, hEe⟩
  have elim0_bound : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (seed0 x) = fP x) →
      C.gates.countP (fun g => rd g 0 || rd g 10) + 16 ≤ C.size := by
    intro C hCf hCe
    have h16 := elim0_size C hCf hCe
    have hcf := countFold 9 (fun g => rd g 0 || rd g 10) C.gates (env0_x0, [])
      (fun g s hg _ hpref hP => by
        obtain ⟨hop, hgl⟩ := hCf g hg
        rcases Bool.or_eq_true_iff.mp hP with h0 | h10
        · exact simpStep_dropConst 9 s g 0 hop hgl h0
            (by dsimp only [isConst]; rw [hpref 0 (by rw [henv0x0_len]; omega), henv0x0_0])
        · exact simpStep_dropConst 9 s g 10 hop hgl h10
            (by dsimp only [isConst]; rw [hpref 10 (by rw [henv0x0_len]; omega), henv0x0_10]))
    change C.gates.countP (fun g => rd g 0 || rd g 10) + 16 ≤ C.gates.length
    simp only [List.length_nil, Nat.zero_add] at hcf
    omega
  -- Cover at most 2 elements in a nonempty list
  have countP_le2_cover : ∀ {α : Type} (L : List α) (P : α → Bool),
      0 < L.length → L.countP P ≤ 2 →
      ∃ a b : Fin L.length, ∀ j : Fin L.length, P (L.get j) = true → j = a ∨ j = b := by
    intro α L P hpos hle
    let idxs : List (Fin L.length) := (List.finRange L.length).filter (fun j => P (L.get j))
    have hlenEq : idxs.length = L.countP P := by
      have hmap : L = (List.finRange L.length).map (fun j => L.get j) := by
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        simp
      conv_rhs => rw [hmap]
      rw [List.countP_map, List.countP_eq_length_filter]
      rfl
    have hmem : ∀ j : Fin L.length, P (L.get j) = true → j ∈ idxs := fun j hj =>
      List.mem_filter.mpr ⟨List.mem_finRange j, hj⟩
    cases h1 : idxs with
    | nil =>
      refine ⟨⟨0, hpos⟩, ⟨0, hpos⟩, fun j hj => ?_⟩
      have hm := hmem j hj; rw [h1] at hm; cases hm
    | cons a l1 =>
      cases h2 : l1 with
      | nil =>
        refine ⟨a, a, fun j hj => ?_⟩
        have hm := hmem j hj; rw [h1, h2] at hm
        exact Or.inl (List.mem_singleton.mp hm)
      | cons b l2 =>
        cases h3 : l2 with
        | nil =>
          refine ⟨a, b, fun j hj => ?_⟩
          have hm := hmem j hj; rw [h1, h2, h3] at hm
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact Or.inl rfl
          · exact Or.inr (List.mem_singleton.mp hm')
        | cons c l3 =>
          rw [h1, h2, h3] at hlenEq
          simp at hlenEq
          omega
  -- Close any C (size <= 18) computing fP on seed0 with no gate reading 0 via h4035
  have closeNoRead0 : ∀ (C : Circuit), FanInTwo C → C.size ≤ 18 →
      (∀ x : Fin 10 → Bool, C.eval (seed0 x) = fP x) →
      (∀ g ∈ C.gates, rd g 0 = false) → False := by
    intro C hCf hCs hCe hno0
    have hb := elim0_bound C hCf hCe
    have hpos : 0 < C.gates.length := by change 0 < C.size; omega
    have hle2 : C.gates.countP (fun g => rd g 10) ≤ 2 := by
      have hle : C.gates.countP (fun g => rd g 10) ≤ C.gates.countP (fun g => rd g 0 || rd g 10) := by
        apply List.countP_mono_left
        intro g _ h; simp [h]
      omega
    obtain ⟨a, b, hab⟩ := countP_le2_cover C.gates (fun g => rd g 10) hpos hle2
    apply h4035 C hCf hCs hCe
    · intro j
      have hgj := hCf (C.gates.get j) (List.get_mem _ _)
      have h0 := hno0 (C.gates.get j) (List.get_mem _ _)
      have hiff := rd_iff_4035 (C.gates.get j) 0 hgj.1 hgj.2
      constructor
      · intro hop hhd
        have ht : rd (C.gates.get j) 0 = true := hiff.mpr (Or.inl ⟨hop, hhd⟩)
        rw [h0] at ht; cases ht
      · intro hop hmem
        have ht : rd (C.gates.get j) 0 = true := hiff.mpr (Or.inr ⟨hop, hmem⟩)
        rw [h0] at ht; cases ht
    · refine ⟨a, b, fun j => ?_⟩
      have hgj := hCf (C.gates.get j) (List.get_mem _ _)
      have hiff := rd_iff_4035 (C.gates.get j) 10 hgj.1 hgj.2
      exact ⟨fun hop hhd => hab j (hiff.mpr (Or.inl ⟨hop, hhd⟩)),
             fun hop hmem => hab j (hiff.mpr (Or.inr ⟨hop, hmem⟩))⟩
  -- Replace gate g at position a.length in (a ++ g :: c) by `rep` (constant or earlier wire), dropping size by >= 1
  have replaceGate : ∀ (a c : List Gate) (g : Gate) (out : ℕ) (rep : Sum Bool ℕ),
      FanInTwo ⟨a ++ g :: c, out⟩ →
      (∀ j, rep = .inr j → j < 11 + a.length) →
      (∀ x : Fin 10 → Bool, evalV (a.foldl step (seed0 x)) rep =
        g.op.eval (g.inputs.map fun i => (a.foldl step (seed0 x)).getD i false)) →
      (∀ x : Fin 10 → Bool, (Circuit.mk (a ++ g :: c) out).eval (seed0 x) = fP x) →
      ∃ C' : Circuit, FanInTwo C' ∧ C'.size ≤ a.length + c.length ∧
        ∀ x : Fin 10 → Bool, C'.eval (seed0 x) = fP x := by
    intro a c g out rep hCf hrepB hrepE hCe
    let envA : List (Sum Bool ℕ) := (List.range (11 + a.length)).map Sum.inr ++ [rep]
    have haFan : FanInTwo ⟨a, 0⟩ := fun h hh => hCf h (List.mem_append_left _ hh)
    have hcFan : ∀ h ∈ c, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2 :=
      fun h hh => hCf h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
    have henvB : ∀ s ∈ envA, ∀ j, s = .inr j → j < 11 + a.length := by
      intro s hs j hj
      rcases List.mem_append.mp hs with h1 | h2
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1; cases hj; simp at hk; exact hk
      · obtain rfl := List.mem_singleton.mp h2; exact hrepB j hj
    obtain ⟨hff, hflen, hfsz, _, _, _, htr⟩ := simpFold 11 c (envA, a) hcFan haFan henvB
    let sf := c.foldl (simpStep 11) (envA, a)
    have hbaseTr : ∀ x : Fin 10 → Bool, ∀ i < envA.length,
        evalV (a.foldl step (seed0 x)) (envA.getD i (.inl false)) =
        (step (a.foldl step (seed0 x)) g).getD i false := by
      intro x i hi
      have halen : (a.foldl step (seed0 x)).length = 11 + a.length := by rw [runLen, seed0Len]
      by_cases hlt : i < 11 + a.length
      · have hl : i < ((List.range (11 + a.length)).map (Sum.inr : ℕ → Sum Bool ℕ)).length := by simp [hlt]
        rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range]
        dsimp only [evalV]
        rw [stepDef, List.getD_append _ _ _ _ (by omega)]
      · have hiEq : i = 11 + a.length := by simp [envA] at hi; omega
        subst hiEq
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
        dsimp only [step]
        rw [List.getD_append_right _ _ _ _ halen.le, halen, Nat.sub_self, List.getD_cons_zero]
        exact hrepE x
    have hOutEv : ∀ x : Fin 10 → Bool,
        evalV (sf.2.foldl step (seed0 x)) (sf.1.getD out (.inl false)) = fP x := by
      intro x
      have hfull : (c.foldl step (step (a.foldl step (seed0 x)) g)).getD out false = fP x := by
        have h := hCe x
        change ((a ++ g :: c).foldl step (seed0 x)).getD out false = fP x at h
        rwa [List.foldl_append, List.foldl_cons] at h
      have hstepLen : (step (a.foldl step (seed0 x)) g).length = envA.length := by
        change ((a.foldl step (seed0 x)) ++ [_]).length = envA.length
        rw [List.length_append, List.length_singleton, runLen, seed0Len]
        simp [envA]
      by_cases hout : out < sf.1.length
      · exact (htr (seed0 x) (step (a.foldl step (seed0 x)) g) (seed0Len x)
          hstepLen (hbaseTr x) out hout).trans hfull
      · rw [List.getD_eq_default sf.1 _ (by omega)]
        dsimp only [evalV]
        have hlenC : (c.foldl step (step (a.foldl step (seed0 x)) g)).length = sf.1.length := by
          rw [runLen, hstepLen, hflen]
        rw [List.getD_eq_default _ _ (by omega)] at hfull
        exact hfull
    cases hout : sf.1.getD out (.inl false) with
    | inl b =>
      have h0 := hOutEv (fun _ => false)
      have h1 := hOutEv (fun i => decide (i = 0 ∨ i = 1))
      rw [hout, fPZero] at h0
      rw [hout, fPEdge01] at h1
      dsimp only [evalV] at h0 h1
      rw [h0] at h1; cases h1
    | inr wOut =>
      exact ⟨⟨sf.2, wOut⟩, hff, hfsz, fun x => by have h := hOutEv x; rw [hout] at h; exact h⟩
  -- Universal closer: NO FanInTwo circuit of size <= 17 computes fP on seed0
  have close17 : ∀ (C : Circuit), FanInTwo C → C.size ≤ 17 →
      (∀ x : Fin 10 → Bool, C.eval (seed0 x) = fP x) → False := by
    intro C hCf hCs hCe
    have hb := elim0_bound C hCf hCe
    have hle1 : C.gates.countP (fun g => rd g 0 || rd g 10) ≤ 1 := by omega
    by_cases hno10 : ∀ g ∈ C.gates, rd g 10 = false
    · exact noRead10_elim C hCf (by omega) hCe hno10
    · by_cases hno0 : ∀ g ∈ C.gates, rd g 0 = false
      · exact closeNoRead0 C hCf (by omega) hCe hno0
      · push Not at hno10 hno0
        obtain ⟨g1, hg1m, hg1r⟩ := hno10
        obtain ⟨g0, hg0m, hg0r⟩ := hno0
        have hg1t : rd g1 10 = true := Bool.eq_true_of_not_eq_false hg1r
        have hg0t : rd g0 0 = true := Bool.eq_true_of_not_eq_false hg0r
        -- Since countP <= 1, g0 and g1 must be at the same index, so one gate reads both 0 and 10
        obtain ⟨i0, hi0lt, hi0eq⟩ := List.getElem_of_mem hg0m
        obtain ⟨i1, hi1lt, hi1eq⟩ := List.getElem_of_mem hg1m
        have heqIdx : i0 = i1 := by
          by_contra hne
          have htwo : 2 ≤ C.gates.countP (fun g => rd g 0 || rd g 10) := by
            let P : Gate → Bool := fun g => rd g 0 || rd g 10
            have hmap : C.gates = (List.finRange C.gates.length).map (fun j => C.gates.get j) :=
              List.ext_getElem (by simp) (fun _ _ _ => by simp)
            rw [hmap, List.countP_map, List.countP_eq_length_filter]
            let Lf := (List.finRange C.gates.length).filter (fun j => P (C.gates.get j))
            have hm0 : (⟨i0, hi0lt⟩ : Fin C.gates.length) ∈ Lf :=
              List.mem_filter.mpr ⟨List.mem_finRange _, by simp [P, hi0eq, hg0t]⟩
            have hm1 : (⟨i1, hi1lt⟩ : Fin C.gates.length) ∈ Lf :=
              List.mem_filter.mpr ⟨List.mem_finRange _, by simp [P, hi1eq, hg1t]⟩
            have hneF : (⟨i0, hi0lt⟩ : Fin C.gates.length) ≠ ⟨i1, hi1lt⟩ := fun h => hne (congrArg Fin.val h)
            have hnd : Lf.Nodup := (List.nodup_finRange _).filter _
            have h2 : ({⟨i0, hi0lt⟩, ⟨i1, hi1lt⟩} : Finset (Fin C.gates.length)).card ≤ Lf.toFinset.card :=
              Finset.card_le_card (fun z hz => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rw [List.mem_toFinset]; rcases hz with rfl | rfl <;> assumption)
            rw [Finset.card_pair hneF, List.toFinset_card_of_nodup hnd] at h2
            exact h2
          omega
        subst heqIdx
        have hgeq : g0 = g1 := hi0eq.symm.trans hi1eq
        subst hgeq
        obtain ⟨a, c, hsplit⟩ := List.append_of_mem hg0m
        have hCf' : FanInTwo ⟨a ++ g0 :: c, C.output⟩ := by rwa [← hsplit]
        have hCe' : ∀ x, (Circuit.mk (a ++ g0 :: c) C.output).eval (seed0 x) = fP x := by rwa [← hsplit]
        obtain ⟨hop, hgl⟩ := hCf g0 hg0m
        have hconst : ∃ b : Bool, ∀ x : Fin 10 → Bool,
            g0.op.eval (g0.inputs.map fun i => (a.foldl step (seed0 x)).getD i false) = b := by
          have hw0 : ∀ x, (a.foldl step (seed0 x)).getD 0 false = x 0 := fun x => by
            rw [retain a _ 0 (by rw [seed0Len]; omega)]
            simp only [seed0]; rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
          have hw10 : ∀ x, (a.foldl step (seed0 x)).getD 10 false = !x 0 := fun x => by
            rw [retain a _ 10 (by rw [seed0Len]; omega)]
            simp only [seed0]; rw [List.getD_append_right _ _ _ _ (by simp)]; simp
          rcases g0 with ⟨op, inputs⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with rfl | rfl | rfl
          · cases inputs with
            | nil => simp [rd_and] at hg0t
            | cons p l =>
              cases l with
              | nil => simp [rd_and] at hg0t hg1t; omega
              | cons q l2 =>
                cases l2 with
                | nil =>
                  simp [rd_and] at hg0t hg1t
                  refine ⟨false, fun x => ?_⟩
                  simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rcases hg0t with rfl | rfl <;> rcases hg1t with hq | hq
                  · cases hq
                  · subst hq; rw [hw0, hw10]; cases x 0 <;> rfl
                  · subst hq; rw [hw0, hw10]; cases x 0 <;> rfl
                  · cases hq
                | cons _ _ => simp at hgl
          · cases inputs with
            | nil => simp [rd_or] at hg0t
            | cons p l =>
              cases l with
              | nil => simp [rd_or] at hg0t hg1t; omega
              | cons q l2 =>
                cases l2 with
                | nil =>
                  simp [rd_or] at hg0t hg1t
                  refine ⟨true, fun x => ?_⟩
                  simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rcases hg0t with rfl | rfl <;> rcases hg1t with hq | hq
                  · cases hq
                  · subst hq; rw [hw0, hw10]; cases x 0 <;> rfl
                  · subst hq; rw [hw0, hw10]; cases x 0 <;> rfl
                  · cases hq
                | cons _ _ => simp at hgl
          · cases inputs with
            | nil => simp [rd_not] at hg0t
            | cons p _ => simp [rd_not] at hg0t hg1t; omega
        obtain ⟨b, hbEq⟩ := hconst
        obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a c g0 C.output (.inl b) hCf' (fun _ h => by cases h)
          (fun x => (hbEq x).symm) hCe'
        have hC's16 : C'.size ≤ 16 := by
          have hlenS : C.gates.length = a.length + c.length + 1 := by
            rw [hsplit]; simp only [List.length_append, List.length_cons]; omega
          change C.gates.length ≤ 17 at hCs; omega
        have hb' := elim0_bound C' hC'f hC'e
        have hzero : C'.gates.countP (fun g => rd g 0 || rd g 10) = 0 := by omega
        have hno10' : ∀ g ∈ C'.gates, rd g 10 = false := by
          intro g hg
          by_contra hne
          have ht : rd g 10 = true := Bool.eq_true_of_not_eq_false hne
          have hpos : 0 < C'.gates.countP (fun g => rd g 0 || rd g 10) :=
            List.countP_pos_iff.mpr ⟨g, hg, by simp [ht]⟩
          omega
        exact noRead10_elim C' hC'f (by omega) hC'e hno10'
  -- Step 1: Permute C0 inputs via aut0 sending x1 ↦ 0 so wire 10 becomes !x 0
  let k0 : Fin 10 := ⟨x1.val, hx1⟩
  let pin : ℕ → ℕ := fun i => if h : i < 10 then (aut0 k0 ⟨i, h⟩).val else i
  let renGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map pin⟩
  let D0 : Circuit := ⟨C0.gates.map renGate, 0⟩
  have hD0fan : FanInTwo D0 := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hgl⟩ := hfan0 h hh
    exact ⟨hop, by simp [renGate, hgl]⟩
  have hD0sz : D0.size ≤ 17 := by
    change (C0.gates.map renGate).length ≤ 17; rw [List.length_map]; exact hsize0
  have htrans : ∀ (gs : List Gate) (xs ys : List Bool),
      xs.length = ys.length → 10 ≤ xs.length →
      (∀ i, xs.getD i false = ys.getD (pin i) false) →
      ∀ i, (gs.foldl step xs).getD i false = ((gs.map renGate).foldl step ys).getD (pin i) false := by
    intro gs
    induction gs with
    | nil => intro xs ys _ _ h i; exact h i
    | cons g gs ih =>
      intro xs ys hlen h10 h i
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hout : g.op.eval (g.inputs.map fun j => xs.getD j false) =
          (renGate g).op.eval ((renGate g).inputs.map fun j => ys.getD j false) := by
        dsimp only [renGate]
        congr 1; simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left fun j _ => h j
      apply ih (step xs g) (step ys (renGate g)) (by simp [step, hlen]) (by simp [step]; omega)
      intro j
      dsimp only [step]
      rw [hout]
      by_cases hlt : j < xs.length
      · have hpinLt : pin j < ys.length := by
          by_cases hj10 : j < 10
          · simp only [pin, hj10, ↓reduceDIte]; have := (aut0 k0 ⟨j, hj10⟩).isLt; omega
          · simp only [pin, hj10, ↓reduceDIte]; omega
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hpinLt, h j]
      · have hj10 : ¬ j < 10 := by omega
        simp only [pin, hj10, ↓reduceDIte]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]
  have hD0wire : ∀ (y : Fin 10 → Bool) (i : ℕ), 10 ≤ i →
      (D0.gates.foldl step (seed0 y)).getD i false = w0 (fun j => y (aut0 k0 j)) i := by
    intro y i hi
    have hseedY : ({ gates := [gSeed], output := 0 } : Circuit).wires (List.ofFn (fun j => y (aut0 k0 j))) =
        List.ofFn (fun j => y (aut0 k0 j)) ++ [!y 0] := by
      change List.ofFn (fun j => y (aut0 k0 j)) ++
        [GateOp.not.eval [(List.ofFn (fun j => y (aut0 k0 j))).getD k0.val false]] = _
      rw [eval_not, List.headD_cons, List.getD_eq_getElem _ _ (by simp [k0.isLt]), List.getElem_ofFn, aut0Fix k0]
    have hinit : ∀ j, (List.ofFn (fun p => y (aut0 k0 p)) ++ [!y 0]).getD j false =
        (seed0 y).getD (pin j) false := by
      intro j
      by_cases hj10 : j < 10
      · simp only [pin, hj10, ↓reduceDIte, seed0]
        rw [List.getD_append _ _ _ _ (by simp [hj10]), List.getD_append _ _ _ _ (by simp [(aut0 k0 ⟨j, hj10⟩).isLt]),
          List.getD_eq_getElem _ _ (by simp [hj10]), List.getD_eq_getElem _ _ (by simp [(aut0 k0 ⟨j, hj10⟩).isLt]),
          List.getElem_ofFn, List.getElem_ofFn]
      · simp only [pin, hj10, ↓reduceDIte, seed0]
        rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
        simp
    have ht := htrans C0.gates (List.ofFn (fun p => y (aut0 k0 p)) ++ [!y 0]) (seed0 y)
      (by simp [seed0]) (by simp) hinit i
    have hpinI : pin i = i := by simp [pin, show ¬ i < 10 by omega]
    rw [hpinI] at ht
    dsimp only [D0, w0]
    rw [hseedY]
    exact ht.symm
  -- Step 2: Normalize D0 via simpFold 11 from identity init
  let idEnv : List (Sum Bool ℕ) := (List.range 11).map Sum.inr
  have hidBdd : ∀ s ∈ idEnv, ∀ j, s = .inr j → j < 11 + ([] : List Gate).length := by
    intro s hs j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs; cases hj; simp at hk; exact hk
  obtain ⟨hD1f, hD1elen, hD1sz, _, hD1bdd, hD1norm, hD1tr⟩ :=
    simpFold 11 D0.gates (idEnv, []) hD0fan (fun _ h => by cases h) hidBdd
  let sf1 := D0.gates.foldl (simpStep 11) (idEnv, [])
  let D1 : Circuit := ⟨sf1.2, 0⟩
  have hD1norm' : NormList 11 D1.gates := hD1norm (fun _ _ h => by cases h)
  have hD1sz17 : D1.size ≤ 17 := by
    change sf1.2.length ≤ 17; dsimp only [sf1]; simp at hD1sz; change D0.gates.length ≤ 17 at hD0sz; omega
  have hD1eval : ∀ (y : Fin 10 → Bool) (i : ℕ), 10 ≤ i →
      evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD i (.inl false)) = w0 (fun j => y (aut0 k0 j)) i := by
    intro y i hi
    have hbase : ∀ k < idEnv.length,
        evalV (([] : List Gate).foldl step (seed0 y)) (idEnv.getD k (.inl false)) = (seed0 y).getD k false := by
      intro k hk
      simp only [List.foldl_nil]
      rw [List.getD_eq_getElem _ _ hk]
      simp only [idEnv, List.getElem_map, List.getElem_range]; rfl
    by_cases hilt : i < sf1.1.length
    · exact (hD1tr (seed0 y) (seed0 y) (seed0Len y) (by simp [seed0, idEnv]) hbase i hilt).trans (hD0wire y i hi)
    · rw [List.getD_eq_default sf1.1 _ (by omega)]
      dsimp only [evalV]
      have hlen0 : (D0.gates.foldl step (seed0 y)).length = sf1.1.length := by
        rw [runLen, seed0Len, hD1elen]; simp [idEnv]
      have h0 := hD0wire y i hi
      rw [List.getD_eq_default _ _ (by omega)] at h0
      exact h0
  have hLeft1 : ∃ y, evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD (10 + u0.val) (.inl false)) = true ∧
      evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD (10 + v0.val) (.inl false)) = false := by
    obtain ⟨x, hx1', hx2'⟩ := hLeft0
    refine ⟨fun j => x (inv0 k0 j), ?_, ?_⟩
    · rw [hD1eval _ _ (by omega)]
      have heq : (fun j => x (inv0 k0 (aut0 k0 j))) = x := funext (fun j => by rw [aut0Left])
      rw [heq]; exact hx1'
    · rw [hD1eval _ _ (by omega)]
      have heq : (fun j => x (inv0 k0 (aut0 k0 j))) = x := funext (fun j => by rw [aut0Left])
      rw [heq]; exact hx2'
  have hRight1 : ∃ y, evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD (10 + u0.val) (.inl false)) = false ∧
      evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD (10 + v0.val) (.inl false)) = true := by
    obtain ⟨x, hx1', hx2'⟩ := hRight0
    refine ⟨fun j => x (inv0 k0 j), ?_, ?_⟩
    · rw [hD1eval _ _ (by omega)]
      have heq : (fun j => x (inv0 k0 (aut0 k0 j))) = x := funext (fun j => by rw [aut0Left])
      rw [heq]; exact hx1'
    · rw [hD1eval _ _ (by omega)]
      have heq : (fun j => x (inv0 k0 (aut0 k0 j))) = x := funext (fun j => by rw [aut0Left])
      rw [heq]; exact hx2'
  have hCov1 : ∀ y : Fin 10 → Bool,
      (evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD (10 + u0.val) (.inl false)) ||
       evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD (10 + v0.val) (.inl false))) = fP y := by
    intro y
    rw [hD1eval y _ (by omega), hD1eval y _ (by omega), exactPair0, aut0Match]
  -- Extract concrete wire indices u1, v1 in [11, 11 + D1.size)
  have hExtractWire : ∀ (idx : ℕ),
      (∃ y, evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD idx (.inl false)) = true) →
      (∀ y, fP y = false → evalV (D1.gates.foldl step (seed0 y)) (sf1.1.getD idx (.inl false)) = false) →
      ∃ w : ℕ, sf1.1.getD idx (.inl false) = .inr w ∧ 11 ≤ w ∧ w < 11 + D1.size := by
    intro idx hex hzero
    cases hs : sf1.1.getD idx (.inl false) with
    | inl c =>
      cases c with
      | false => obtain ⟨y, hy⟩ := hex; rw [hs] at hy; cases hy
      | true => have h0 := hzero (fun _ => false) fPZero; rw [hs] at h0; cases h0
    | inr w =>
      have hwLt : w < 11 + D1.size := by
        by_cases hlt : idx < sf1.1.length
        · rw [List.getD_eq_getElem _ _ hlt] at hs
          exact hD1bdd _ (List.getElem_mem hlt) w hs
        · rw [List.getD_eq_default _ _ (by omega)] at hs; cases hs
      have hwGe11 : 11 ≤ w := by
        by_contra! hwlt11
        by_cases hw10 : w = 10
        · subst hw10
          have h0 := hzero (fun _ => false) fPZero
          rw [hs] at h0; dsimp only [evalV] at h0
          rw [retain D1.gates _ 10 (by rw [seed0Len]; omega)] at h0
          simp [seed0] at h0
        · have hwlt10 : w < 10 := by omega
          let eW : Fin 10 → Bool := fun j => decide (j = ⟨w, hwlt10⟩)
          have h0 := hzero eW (fPUnit ⟨w, hwlt10⟩)
          rw [hs] at h0; dsimp only [evalV] at h0
          rw [retain D1.gates _ w (by rw [seed0Len]; omega)] at h0
          simp only [seed0] at h0
          rw [List.getD_append _ _ _ _ (by simp [hwlt10]), List.getD_eq_getElem _ _ (by simp [hwlt10]),
            List.getElem_ofFn] at h0
          simp [eW] at h0
      exact ⟨w, rfl, hwGe11, hwLt⟩
  obtain ⟨u1, hu1Eq, hu1Ge, hu1Lt⟩ := hExtractWire (10 + u0.val)
    (by obtain ⟨y, h1, _⟩ := hLeft1; exact ⟨y, h1⟩)
    (fun y hy => (Bool.or_eq_false_iff.mp ((hCov1 y).trans hy)).1)
  obtain ⟨v1, hv1Eq, hv1Ge, hv1Lt⟩ := hExtractWire (10 + v0.val)
    (by obtain ⟨y, _, h2⟩ := hRight1; exact ⟨y, h2⟩)
    (fun y hy => (Bool.or_eq_false_iff.mp ((hCov1 y).trans hy)).2)
  have huv1Ne : u1 ≠ v1 := by
    rintro rfl
    obtain ⟨y, h1, h2⟩ := hLeft1
    rw [hu1Eq] at h1; rw [hv1Eq] at h2; rw [h1] at h2; cases h2
  -- Order u2 < v2 and trim D1 to D2 of size v2 - 10 <= 17
  let u2 := min u1 v1
  let v2 := max u1 v1
  have hu2Ge : 11 ≤ u2 := le_min hu1Ge hv1Ge
  have huv2 : u2 < v2 := by
    rcases lt_or_gt_of_ne huv1Ne with h | h
    · simpa [u2, v2, min_eq_left h.le, max_eq_right h.le] using h
    · simpa [u2, v2, min_eq_right h.le, max_eq_left h.le] using h
  have hv2Lt : v2 < 11 + D1.size := max_lt hu1Lt hv1Lt
  let D2 : Circuit := ⟨D1.gates.take (v2 - 10), 0⟩
  have hD2sz : D2.size = v2 - 10 := by
    change (D1.gates.take (v2 - 10)).length = v2 - 10
    rw [List.length_take]; change min (v2 - 10) D1.gates.length = v2 - 10
    change v2 < 11 + D1.gates.length at hv2Lt; omega
  have hD2sz17 : D2.size ≤ 17 := by omega
  have hD2fan : FanInTwo D2 := fun g hg => hD1f g (List.mem_of_mem_take hg)
  have hD2norm : NormList 11 D2.gates := by
    intro j g hj
    have hlt : j < D2.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have hlt2 : j < v2 - 10 := by change j < D2.size at hlt; omega
    rw [List.getElem?_take_of_lt hlt2] at hj
    exact hD1norm' j g hj
  have hD2wire : ∀ (y : Fin 10 → Bool) (i : ℕ), i ≤ v2 →
      (D2.gates.foldl step (seed0 y)).getD i false = (D1.gates.foldl step (seed0 y)).getD i false := by
    intro y i hi
    have hsp : D1.gates = D2.gates ++ D1.gates.drop (v2 - 10) := (List.take_append_drop (v2 - 10) D1.gates).symm
    conv_rhs => rw [hsp, List.foldl_append]
    have hlen : (D2.gates.foldl step (seed0 y)).length = 11 + D2.size := by rw [runLen, seed0Len]; rfl
    exact (retain (D1.gates.drop (v2 - 10)) _ i (by omega)).symm
  have hCov2 : ∀ y : Fin 10 → Bool,
      ((D2.gates.foldl step (seed0 y)).getD u2 false || (D2.gates.foldl step (seed0 y)).getD v2 false) = fP y := by
    intro y
    rw [hD2wire y u2 huv2.le, hD2wire y v2 le_rfl]
    have hc := hCov1 y
    rw [hu1Eq, hv1Eq] at hc
    dsimp only [evalV] at hc
    rcases le_total u1 v1 with h | h
    · dsimp only [u2, v2]; rw [min_eq_left h, max_eq_right h]; exact hc
    · dsimp only [u2, v2]; rw [min_eq_right h, max_eq_left h, Bool.or_comm]; exact hc
  have hIncomp2 : ∀ c : Bool, ∃ y : Fin 10 → Bool,
      (D2.gates.foldl step (seed0 y)).getD u2 false = c ∧
      (D2.gates.foldl step (seed0 y)).getD v2 false = !c := by
    intro c
    have hL : ∃ y, (D1.gates.foldl step (seed0 y)).getD u1 false = true ∧
        (D1.gates.foldl step (seed0 y)).getD v1 false = false := by
      obtain ⟨y, h1, h2⟩ := hLeft1; rw [hu1Eq] at h1; rw [hv1Eq] at h2; exact ⟨y, h1, h2⟩
    have hR : ∃ y, (D1.gates.foldl step (seed0 y)).getD u1 false = false ∧
        (D1.gates.foldl step (seed0 y)).getD v1 false = true := by
      obtain ⟨y, h1, h2⟩ := hRight1; rw [hu1Eq] at h1; rw [hv1Eq] at h2; exact ⟨y, h1, h2⟩
    rcases le_total u1 v1 with h | h
    · cases c with
      | true =>
        obtain ⟨y, h1, h2⟩ := hL
        exact ⟨y, by rw [hD2wire y u2 huv2.le]; dsimp only [u2]; rw [min_eq_left h]; exact h1,
                  by rw [hD2wire y v2 le_rfl]; dsimp only [v2]; rw [max_eq_right h]; exact h2⟩
      | false =>
        obtain ⟨y, h1, h2⟩ := hR
        exact ⟨y, by rw [hD2wire y u2 huv2.le]; dsimp only [u2]; rw [min_eq_left h]; exact h1,
                  by rw [hD2wire y v2 le_rfl]; dsimp only [v2]; rw [max_eq_right h]; exact h2⟩
    · cases c with
      | true =>
        obtain ⟨y, h1, h2⟩ := hR
        exact ⟨y, by rw [hD2wire y u2 huv2.le]; dsimp only [u2]; rw [min_eq_right h]; exact h2,
                  by rw [hD2wire y v2 le_rfl]; dsimp only [v2]; rw [max_eq_left h]; exact h1⟩
      | false =>
        obtain ⟨y, h1, h2⟩ := hL
        exact ⟨y, by rw [hD2wire y u2 huv2.le]; dsimp only [u2]; rw [min_eq_right h]; exact h2,
                  by rw [hD2wire y v2 le_rfl]; dsimp only [v2]; rw [max_eq_left h]; exact h1⟩
  -- Build combined C = D2 ++ [OR(u2, v2)] of size D2.size + 1 <= 18
  let topG : Gate := ⟨.or, [u2, v2]⟩
  let C : Circuit := ⟨D2.gates ++ [topG], 11 + D2.size⟩
  have hCfan : FanInTwo C := by
    intro g hg
    rcases List.mem_append.mp hg with hm | hm
    · exact hD2fan g hm
    · obtain rfl := List.mem_singleton.mp hm; exact ⟨Or.inr (Or.inl rfl), by simp [topG]⟩
  have hCsz : C.size = D2.size + 1 := by
    change (D2.gates ++ [topG]).length = D2.gates.length + 1; simp
  have hCeval : ∀ y : Fin 10 → Bool, C.eval (seed0 y) = fP y := by
    intro y
    change ((D2.gates ++ [topG]).foldl step (seed0 y)).getD (11 + D2.size) false = fP y
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (D2.gates.foldl step (seed0 y)).length = 11 + D2.size := by rw [runLen, seed0Len]; rfl
    dsimp only [step, topG]
    rw [List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self, List.getD_cons_zero]
    simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    exact hCov2 y
  -- If D2.size <= 16, C.size <= 17 -> instant close17!
  by_cases hD2lt17 : D2.size ≤ 16
  · exact close17 C hCfan (by omega) hCeval
  have hD2eq17 : D2.size = 17 := by omega
  have hv2eq27 : v2 = 27 := by omega
  have hCeq18 : C.size = 18 := by omega
  have htopNo0 : rd topG 0 = false := by
    dsimp only [topG]; rw [rd_or]; simp; omega
  have htopNo10 : rd topG 10 = false := by
    dsimp only [topG]; rw [rd_or]; simp; omega
  -- If no gate reads 10 -> noRead10_elim; if no gate reads 0 -> closeNoRead0
  by_cases hno10 : ∀ g ∈ D2.gates, rd g 10 = false
  · exact noRead10_elim C hCfan (by omega) hCeval (fun g hg => by
      rcases List.mem_append.mp hg with h1 | h2
      · exact hno10 g h1
      · obtain rfl := List.mem_singleton.mp h2; exact htopNo10)
  by_cases hno0 : ∀ g ∈ D2.gates, rd g 0 = false
  · exact closeNoRead0 C hCfan (by omega) hCeval (fun g hg => by
      rcases List.mem_append.mp hg with h1 | h2
      · exact hno0 g h1
      · obtain rfl := List.mem_singleton.mp h2; exact htopNo0)
  push Not at hno10 hno0
  obtain ⟨g0, hg0m, hg0ne⟩ := hno0
  obtain ⟨g1, hg1m, hg1ne⟩ := hno10
  have hg0r0 : rd g0 0 = true := Bool.eq_true_of_not_eq_false hg0ne
  have hg1r10 : rd g1 10 = true := Bool.eq_true_of_not_eq_false hg1ne
  obtain ⟨i0, hi0lt, hi0eq⟩ := List.getElem_of_mem hg0m
  obtain ⟨i1, hi1lt, hi1eq⟩ := List.getElem_of_mem hg1m
  have hi017 : i0 < 17 := by change i0 < D2.size at hi0lt; omega
  have hi117 : i1 < 17 := by change i1 < D2.size at hi1lt; omega
  -- Case i0 = i1: single gate reads both 0 and 10 -> constant -> replaceGate -> close17
  by_cases hiEq : i0 = i1
  · subst hiEq
    have hgeq : g0 = g1 := hi0eq.symm.trans hi1eq
    subst hgeq
    obtain ⟨a, c, hsplit⟩ := List.append_of_mem hg0m
    have hCsp : C.gates = a ++ g0 :: (c ++ [topG]) := by
      dsimp only [C]; rw [hsplit, List.append_assoc, List.cons_append]
    have hCfan' : FanInTwo ⟨a ++ g0 :: (c ++ [topG]), C.output⟩ := by rwa [← hCsp]
    have hCe' : ∀ x, (Circuit.mk (a ++ g0 :: (c ++ [topG])) C.output).eval (seed0 x) = fP x := by rwa [← hCsp]
    have hnorm0 := hD2norm i0 g0 (by rw [List.getElem?_eq_getElem hi0lt, hi0eq])
    have hw0a : ∀ x, (a.foldl step (seed0 x)).getD 0 false = x 0 := fun x => by
      rw [retain a _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    have hw10a : ∀ x, (a.foldl step (seed0 x)).getD 10 false = !x 0 := fun x => by
      rw [retain a _ 10 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append_right _ _ _ _ (by simp)]; simp
    have hconst : ∃ b : Bool, ∀ x : Fin 10 → Bool,
        g0.op.eval (g0.inputs.map fun i => (a.foldl step (seed0 x)).getD i false) = b := by
      rcases g0 with ⟨op, inputs⟩
      rcases hnorm0 with ⟨rfl, p, _, rfl⟩ | ⟨hop, p, q, _, _, _, rfl⟩
      · simp [rd_not] at hg0r0 hg1r10; omega
      · rcases hop with rfl | rfl
        · simp [rd_and] at hg0r0 hg1r10
          refine ⟨false, fun x => ?_⟩
          simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases hg0r0 with rfl | rfl <;> rcases hg1r10 with hq | hq
          · cases hq
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · cases hq
        · simp [rd_or] at hg0r0 hg1r10
          refine ⟨true, fun x => ?_⟩
          simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rcases hg0r0 with rfl | rfl <;> rcases hg1r10 with hq | hq
          · cases hq
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · cases hq
    obtain ⟨b, hbEq⟩ := hconst
    obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a (c ++ [topG]) g0 C.output (.inl b) hCfan'
      (fun _ h => by cases h) (fun x => (hbEq x).symm) hCe'
    have hlenS : a.length + (c ++ [topG]).length = 17 := by
      have h1 : C.gates.length = a.length + (c ++ [topG]).length + 1 := by
        rw [hCsp]; simp only [List.length_append, List.length_cons]; omega
      change C.gates.length = 18 at hCeq18; omega
    exact close17 C' hC'f (by omega) hC'e
  -- Now i0 ≠ i1! By elim0_bound, countP (rd 0 || rd 10) C.gates <= 2, so i0, i1 are the UNIQUE readers!
  have hcnt2 : C.gates.countP (fun g => rd g 0 || rd g 10) ≤ 2 := by
    have hb := elim0_bound C hCfan hCeval; omega
  have huniq : ∀ j g, C.gates[j]? = some g → (rd g 0 || rd g 10) = true → j = i0 ∨ j = i1 := by
    intro j g hj hP
    by_contra hne
    push Not at hne
    have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjeq : C.gates[j] = g := (List.getElem?_eq_some_iff.mp hj).2
    have hi0ltC : i0 < C.gates.length := by dsimp only [C]; simp; omega
    have hi1ltC : i1 < C.gates.length := by dsimp only [C]; simp; omega
    let P : Gate → Bool := fun h => rd h 0 || rd h 10
    have hthree : 3 ≤ C.gates.countP P := by
      have hmap : C.gates = (List.finRange C.gates.length).map (fun k => C.gates.get k) :=
        List.ext_getElem (by simp) (fun _ _ _ => by simp)
      rw [hmap, List.countP_map, List.countP_eq_length_filter]
      let Lf := (List.finRange C.gates.length).filter (fun k => P (C.gates.get k))
      have hm0 : (⟨i0, hi0ltC⟩ : Fin C.gates.length) ∈ Lf :=
        List.mem_filter.mpr ⟨List.mem_finRange _, by
          dsimp only [P]; change rd C.gates[i0] 0 || rd C.gates[i0] 10 = true
          have : C.gates[i0] = g0 := by dsimp only [C]; rw [List.getElem_append_left hi0lt]; exact hi0eq
          simp [this, hg0r0]⟩
      have hm1 : (⟨i1, hi1ltC⟩ : Fin C.gates.length) ∈ Lf :=
        List.mem_filter.mpr ⟨List.mem_finRange _, by
          dsimp only [P]; change rd C.gates[i1] 0 || rd C.gates[i1] 10 = true
          have : C.gates[i1] = g1 := by dsimp only [C]; rw [List.getElem_append_left hi1lt]; exact hi1eq
          simp [this, hg1r10]⟩
      have hmj : (⟨j, hjlt⟩ : Fin C.gates.length) ∈ Lf :=
        List.mem_filter.mpr ⟨List.mem_finRange _, by
          dsimp only [P]; change rd C.gates[j] 0 || rd C.gates[j] 10 = true; rw [hjeq]; exact hP⟩
      let S : Finset (Fin C.gates.length) := {⟨i0, hi0ltC⟩, ⟨i1, hi1ltC⟩, ⟨j, hjlt⟩}
      have hcardS : S.card = 3 := by
        have h01 : (⟨i0, hi0ltC⟩ : Fin C.gates.length) ≠ ⟨i1, hi1ltC⟩ := fun h => hiEq (congrArg Fin.val h)
        have h0j : (⟨i0, hi0ltC⟩ : Fin C.gates.length) ≠ ⟨j, hjlt⟩ := fun h => hne.1 (congrArg Fin.val h).symm
        have h1j : (⟨i1, hi1ltC⟩ : Fin C.gates.length) ≠ ⟨j, hjlt⟩ := fun h => hne.2 (congrArg Fin.val h).symm
        rw [Finset.card_insert_of_notMem (by simp [h01, h0j]), Finset.card_pair h1j]
      have hnd : Lf.Nodup := (List.nodup_finRange _).filter _
      have hle : S.card ≤ Lf.toFinset.card := Finset.card_le_card (fun z hz => by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
        rw [List.mem_toFinset]; rcases hz with rfl | rfl | rfl <;> assumption)
      rw [hcardS, List.toFinset_card_of_nodup hnd] at hle
      exact hle
    dsimp only [P] at hthree; omega
  -- Helper: split list at index k
  have splitAt : ∀ (L : List Gate) (k : ℕ) (g : Gate), L[k]? = some g →
      L = L.take k ++ g :: L.drop (k + 1) ∧ (L.take k).length = k := by
    intro L k g hk
    have hlt : k < L.length := (List.getElem?_eq_some_iff.mp hk).1
    have heq : L[k] = g := (List.getElem?_eq_some_iff.mp hk).2
    refine ⟨?_, by rw [List.length_take, Nat.min_eq_left hlt.le]⟩
    calc L = L.take k ++ L.drop k := (List.take_append_drop k L).symm
      _ = L.take k ++ L[k] :: L.drop (k + 1) := by rw [List.drop_eq_getElem_cons hlt]
      _ = L.take k ++ g :: L.drop (k + 1) := by rw [heq]
  have hC0get : C.gates[i0]? = some g0 := by
    dsimp only [C]; rw [List.getElem?_append_left hi0lt, List.getElem?_eq_getElem hi0lt, hi0eq]
  have hC1get : C.gates[i1]? = some g1 := by
    dsimp only [C]; rw [List.getElem?_append_left hi1lt, List.getElem?_eq_getElem hi1lt, hi1eq]
  -- Helper: if a gate at idx in C becomes constant under env0_x0, NO gate j ∉ {i0, i1} reads 11 + idx!
  have noThirdReader : ∀ (idx : ℕ) (g : Gate), C.gates[idx]? = some g →
      (rd g 0 || rd g 10) = true →
      isConst (simpStep 9 ((C.gates.take idx).foldl (simpStep 9) (env0_x0, [])) g).1 (11 + idx) = true →
      ∀ j h, C.gates[j]? = some h → j ≠ i0 → j ≠ i1 → rd h (11 + idx) = false := by
    intro idx g hget hP hconst j h hj hne0 hne1
    by_contra hne
    have hrdh : rd h (11 + idx) = true := Bool.eq_true_of_not_eq_false hne
    obtain ⟨hsp, htlen⟩ := splitAt C.gates idx g hget
    have hcas := countFoldGenCascade 9 (fun q => rd q 0 || rd q 10)
      (C.gates.take idx) g (C.gates.drop (idx + 1)) (env0_x0, [])
      (by rwa [← hsp])
      (fun q s hq _ hpref hQ => by
        obtain ⟨hop, hgl⟩ := hCfan q (by rwa [hsp])
        rcases Bool.or_eq_true_iff.mp hQ with h0 | h10
        · exact simpStep_dropConst 9 s q 0 hop hgl h0
            (by dsimp only [isConst]; rw [hpref 0 (by rw [henv0x0_len]; omega), henv0x0_0])
        · exact simpStep_dropConst 9 s q 10 hop hgl h10
            (by dsimp only [isConst]; rw [hpref 10 (by rw [henv0x0_len]; omega), henv0x0_10]))
      hP (by rw [henv0x0_len, htlen]; exact hconst)
    rw [← hsp, henv0x0_len, htlen] at hcas
    have h16 := elim0_size C hCfan hCeval
    simp only [List.length_nil, Nat.zero_add] at hcas
    change C.gates.length = 18 at hCeq18
    have hle2 : C.gates.countP (fun q => (rd q 0 || rd q 10) || rd q (11 + idx)) ≤ 2 := by omega
    -- Yet i0, i1, j are 3 distinct elements satisfying the predicate!
    have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjeq : C.gates[j] = h := (List.getElem?_eq_some_iff.mp hj).2
    have hi0ltC : i0 < C.gates.length := by omega
    have hi1ltC : i1 < C.gates.length := by omega
    let Q3 : Gate → Bool := fun q => (rd q 0 || rd q 10) || rd q (11 + idx)
    have hthree : 3 ≤ C.gates.countP Q3 := by
      have hmap : C.gates = (List.finRange C.gates.length).map (fun k => C.gates.get k) :=
        List.ext_getElem (by simp) (fun _ _ _ => by simp)
      rw [hmap, List.countP_map, List.countP_eq_length_filter]
      let Lf := (List.finRange C.gates.length).filter (fun k => Q3 (C.gates.get k))
      have hm0 : (⟨i0, hi0ltC⟩ : Fin C.gates.length) ∈ Lf :=
        List.mem_filter.mpr ⟨List.mem_finRange _, by
          dsimp only [Q3]; change (rd C.gates[i0] 0 || rd C.gates[i0] 10) || rd C.gates[i0] (11 + idx) = true
          have : C.gates[i0] = g0 := (List.getElem?_eq_some_iff.mp hC0get).2
          simp [this, hg0r0]⟩
      have hm1 : (⟨i1, hi1ltC⟩ : Fin C.gates.length) ∈ Lf :=
        List.mem_filter.mpr ⟨List.mem_finRange _, by
          dsimp only [Q3]; change (rd C.gates[i1] 0 || rd C.gates[i1] 10) || rd C.gates[i1] (11 + idx) = true
          have : C.gates[i1] = g1 := (List.getElem?_eq_some_iff.mp hC1get).2
          simp [this, hg1r10]⟩
      have hmj : (⟨j, hjlt⟩ : Fin C.gates.length) ∈ Lf :=
        List.mem_filter.mpr ⟨List.mem_finRange _, by
          dsimp only [Q3]; change (rd C.gates[j] 0 || rd C.gates[j] 10) || rd C.gates[j] (11 + idx) = true
          rw [hjeq]; simp [hrdh]⟩
      let S : Finset (Fin C.gates.length) := {⟨i0, hi0ltC⟩, ⟨i1, hi1ltC⟩, ⟨j, hjlt⟩}
      have hcardS : S.card = 3 := by
        have h01 : (⟨i0, hi0ltC⟩ : Fin C.gates.length) ≠ ⟨i1, hi1ltC⟩ := fun h => hiEq (congrArg Fin.val h)
        have h0j : (⟨i0, hi0ltC⟩ : Fin C.gates.length) ≠ ⟨j, hjlt⟩ := fun h => hne0 (congrArg Fin.val h).symm
        have h1j : (⟨i1, hi1ltC⟩ : Fin C.gates.length) ≠ ⟨j, hjlt⟩ := fun h => hne1 (congrArg Fin.val h).symm
        rw [Finset.card_insert_of_notMem (by simp [h01, h0j]), Finset.card_pair h1j]
      have hnd : Lf.Nodup := (List.nodup_finRange _).filter _
      have hle : S.card ≤ Lf.toFinset.card := Finset.card_le_card (fun z hz => by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
        rw [List.mem_toFinset]; rcases hz with rfl | rfl | rfl <;> assumption)
      rw [hcardS, List.toFinset_card_of_nodup hnd] at hle
      exact hle
    dsimp only [Q3] at hthree; omega
  -- Helper: delete a completely unread gate at index idx in C (size 18) -> close17!
  have deadGateClose : ∀ (C' : Circuit) (idx : ℕ) (g : Gate),
      FanInTwo C' → C'.size ≤ 18 → (∀ x, C'.eval (seed0 x) = fP x) →
      C'.gates[idx]? = some g → C'.output ≠ 11 + idx →
      (∀ j h, C'.gates[j]? = some h → idx < j → rd h (11 + idx) = false) → False := by
    intro C' idx g hC'f hC's hC'e hget houtNe hdead
    obtain ⟨hsp, htlen⟩ := splitAt C'.gates idx g hget
    let a := C'.gates.take idx
    let c := C'.gates.drop (idx + 1)
    -- Replacing wire (11 + idx) with false preserves evaluation of c at C'.output!
    have hinv : ∀ (ls : List Gate) (xs ys : List Bool) (k : ℕ),
        (∀ h ∈ ls, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2) →
        (∀ h ∈ ls, rd h k = false) →
        xs.length = ys.length → k < xs.length →
        (∀ j, j ≠ k → xs.getD j false = ys.getD j false) →
        ∀ j, j ≠ k → (ls.foldl step xs).getD j false = (ls.foldl step ys).getD j false := by
      intro ls
      induction ls with
      | nil => intro xs ys k _ _ _ _ h j hj; exact h j hj
      | cons h0 ls ih =>
        intro xs ys k hfl hrdl hlen hk h j hj
        rw [List.foldl_cons, List.foldl_cons]
        obtain ⟨hop, hgl⟩ := hfl h0 List.mem_cons_self
        have hrd0 := hrdl h0 List.mem_cons_self
        have hev : h0.op.eval (h0.inputs.map fun m => xs.getD m false) =
            h0.op.eval (h0.inputs.map fun m => ys.getD m false) := by
          rcases h0 with ⟨op, inputs⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with rfl | rfl | rfl
          · rw [rd_and, List.take_of_length_le hgl] at hrd0
            have hn : k ∉ inputs := fun hm => by rw [List.contains_iff_mem.mpr hm] at hrd0; cases hrd0
            congr 1; exact List.map_congr_left fun m hm => h m (fun heq => hn (heq ▸ hm))
          · rw [rd_or, List.take_of_length_le hgl] at hrd0
            have hn : k ∉ inputs := fun hm => by rw [List.contains_iff_mem.mpr hm] at hrd0; cases hrd0
            congr 1; exact List.map_congr_left fun m hm => h m (fun heq => hn (heq ▸ hm))
          · rw [rd_not] at hrd0
            cases inputs with
            | nil => rfl
            | cons p _ =>
              have hne : p ≠ k := fun heq => by subst heq; simp at hrd0
              simp only [List.map_cons, eval_not, List.headD_cons, h p hne]
        apply ih (step xs h0) (step ys h0) k
          (fun h' hh' => hfl h' (List.mem_cons_of_mem _ hh'))
          (fun h' hh' => hrdl h' (List.mem_cons_of_mem _ hh'))
          (by simp [step, hlen]) (by simp [step]; omega)
          (fun m hm => by
            dsimp only [step]; rw [hev]
            by_cases hlt : m < xs.length
            · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega), h m hm]
            · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen])
          j hj
    -- Build C'' with gate idx replaced by constant false (same eval on all x!)
    let gFalse : Gate := ⟨.or, []⟩
    have hC''f : FanInTwo ⟨a ++ gFalse :: c, C'.output⟩ := by
      intro h hh
      rcases List.mem_append.mp hh with h1 | h2
      · exact hC'f h (by rw [hsp]; exact List.mem_append_left _ h1)
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact ⟨Or.inr (Or.inl rfl), by simp [gFalse]⟩
        · exact hC'f h (by rw [hsp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h3))
    have hC''e : ∀ x, (Circuit.mk (a ++ gFalse :: c) C'.output).eval (seed0 x) = fP x := by
      intro x
      change ((a ++ gFalse :: c).foldl step (seed0 x)).getD C'.output false = fP x
      rw [List.foldl_append, List.foldl_cons]
      have horig := hC'e x
      change (C'.gates.foldl step (seed0 x)).getD C'.output false = fP x at horig
      rw [hsp, List.foldl_append, List.foldl_cons] at horig
      have hcFan : ∀ h ∈ c, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2 :=
        fun h hh => hC'f h (by rw [hsp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hh))
      have hcNoRead : ∀ h ∈ c, rd h (11 + idx) = false := by
        intro h hh
        obtain ⟨k, hklt, hkeq⟩ := List.getElem_of_mem hh
        have hgetK : C'.gates[idx + 1 + k]? = some h := by
          have hklt' : idx + 1 + k < C'.gates.length := by
            have : c.length = C'.gates.length - (idx + 1) := List.length_drop
            omega
          rw [List.getElem?_eq_getElem hklt']
          congr 1
          have hd : c[k] = C'.gates[idx + 1 + k] := List.getElem_drop
          exact hd.symm.trans hkeq
        exact hdead (idx + 1 + k) h hgetK (by omega)
      have halen : (a.foldl step (seed0 x)).length = 11 + idx := by rw [runLen, seed0Len, htlen]
      have heq := hinv c (step (a.foldl step (seed0 x)) gFalse) (step (a.foldl step (seed0 x)) g) (11 + idx)
        hcFan hcNoRead (by rw [stepLen, stepLen]) (by rw [stepLen, halen]; omega)
        (fun j hj => by
          by_cases hlt : j < 11 + idx
          · exact (List.getD_append _ _ false j (by omega)).trans (List.getD_append _ _ false j (by omega)).symm
          · exact (List.getD_eq_default _ _ (by rw [stepLen, halen]; omega)).trans (List.getD_eq_default _ _ (by rw [stepLen, halen]; omega)).symm)
        C'.output houtNe
      exact heq.trans horig
    obtain ⟨C'', hC''f', hC''s', hC''e'⟩ := replaceGate a c gFalse C'.output (.inl false) hC''f
      (fun _ h => by cases h) (fun _ => rfl) hC''e
    have hlenS : a.length + c.length ≤ 17 := by
      have : C'.gates.length = a.length + c.length + 1 := by
        dsimp only [a, c]; conv_lhs => rw [hsp]
        simp only [List.length_append, List.length_cons]; omega
      change C'.gates.length ≤ 18 at hC's; omega
    exact close17 C'' hC''f' (by omega) hC''e'
  -- Step 3: Force g0 = OR(0, y0) or OR(y0, 0), and g1 = AND(10, y1) or AND(y1, 10)
  have hnorm0 : NormGate (11 + i0) g0 := hD2norm i0 g0 (by rw [List.getElem?_eq_getElem hi0lt, hi0eq])
  have hnorm1 : NormGate (11 + i1) g1 := hD2norm i1 g1 (by rw [List.getElem?_eq_getElem hi1lt, hi1eq])
  have hg0No10 : rd g0 10 = false := by
    -- Wait: could g0 also read 10? We already ruled out i0 = i1, and if g0 read 10 too, we'd have a constant gate!
    by_contra hne
    have hg0r10 : rd g0 10 = true := Bool.eq_true_of_not_eq_false hne
    obtain ⟨hsp, htlen⟩ := splitAt C.gates i0 g0 hC0get
    let a := C.gates.take i0
    let c := C.gates.drop (i0 + 1)
    have hCf' : FanInTwo ⟨a ++ g0 :: c, C.output⟩ := by rwa [← hsp]
    have hCe' : ∀ x, (Circuit.mk (a ++ g0 :: c) C.output).eval (seed0 x) = fP x := by rwa [← hsp]
    have hw0a : ∀ x, (a.foldl step (seed0 x)).getD 0 false = x 0 := fun x => by
      rw [retain a _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    have hw10a : ∀ x, (a.foldl step (seed0 x)).getD 10 false = !x 0 := fun x => by
      rw [retain a _ 10 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append_right _ _ _ _ (by simp)]; simp
    have hconst : ∃ b : Bool, ∀ x, g0.op.eval (g0.inputs.map fun i => (a.foldl step (seed0 x)).getD i false) = b := by
      rcases g0 with ⟨op, inputs⟩
      rcases hnorm0 with ⟨rfl, p, _, rfl⟩ | ⟨hop, p, q, _, _, _, rfl⟩
      · simp [rd_not] at hg0r0 hg0r10; omega
      · rcases hop with rfl | rfl
        · simp [rd_and] at hg0r0 hg0r10
          refine ⟨false, fun x => ?_⟩
          simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases hg0r0 with rfl | rfl <;> rcases hg0r10 with hq | hq
          · cases hq
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · cases hq
        · simp [rd_or] at hg0r0 hg0r10
          refine ⟨true, fun x => ?_⟩
          simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rcases hg0r0 with rfl | rfl <;> rcases hg0r10 with hq | hq
          · cases hq
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · cases hq
    obtain ⟨b, hbEq⟩ := hconst
    obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a c g0 C.output (.inl b) hCf' (fun _ h => by cases h)
      (fun x => (hbEq x).symm) hCe'
    have hlenS : a.length + c.length = 17 := by
      have : C.gates.length = a.length + c.length + 1 := by dsimp only [a, c]; (conv_lhs => rw [hsp]); simp only [List.length_append, List.length_cons]; omega
      change C.gates.length = 18 at hCeq18; omega
    exact close17 C' hC'f (by omega) hC'e
  have hg1No0 : rd g1 0 = false := by
    by_contra hne
    have hg1r0 : rd g1 0 = true := Bool.eq_true_of_not_eq_false hne
    obtain ⟨hsp, htlen⟩ := splitAt C.gates i1 g1 hC1get
    let a := C.gates.take i1
    let c := C.gates.drop (i1 + 1)
    have hCf' : FanInTwo ⟨a ++ g1 :: c, C.output⟩ := by rwa [← hsp]
    have hCe' : ∀ x, (Circuit.mk (a ++ g1 :: c) C.output).eval (seed0 x) = fP x := by rwa [← hsp]
    have hw0a : ∀ x, (a.foldl step (seed0 x)).getD 0 false = x 0 := fun x => by
      rw [retain a _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    have hw10a : ∀ x, (a.foldl step (seed0 x)).getD 10 false = !x 0 := fun x => by
      rw [retain a _ 10 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append_right _ _ _ _ (by simp)]; simp
    have hconst : ∃ b : Bool, ∀ x, g1.op.eval (g1.inputs.map fun i => (a.foldl step (seed0 x)).getD i false) = b := by
      rcases g1 with ⟨op, inputs⟩
      rcases hnorm1 with ⟨rfl, p, _, rfl⟩ | ⟨hop, p, q, _, _, _, rfl⟩
      · simp [rd_not] at hg1r0 hg1r10; omega
      · rcases hop with rfl | rfl
        · simp [rd_and] at hg1r0 hg1r10
          refine ⟨false, fun x => ?_⟩
          simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases hg1r0 with rfl | rfl <;> rcases hg1r10 with hq | hq
          · cases hq
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · cases hq
        · simp [rd_or] at hg1r0 hg1r10
          refine ⟨true, fun x => ?_⟩
          simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rcases hg1r0 with rfl | rfl <;> rcases hg1r10 with hq | hq
          · cases hq
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · subst hq; rw [hw0a, hw10a]; cases x 0 <;> rfl
          · cases hq
    obtain ⟨b, hbEq⟩ := hconst
    obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a c g1 C.output (.inl b) hCf' (fun _ h => by cases h)
      (fun x => (hbEq x).symm) hCe'
    have hlenS : a.length + c.length = 17 := by
      have : C.gates.length = a.length + c.length + 1 := by dsimp only [a, c]; (conv_lhs => rw [hsp]); simp only [List.length_append, List.length_cons]; omega
      change C.gates.length = 18 at hCeq18; omega
    exact close17 C' hC'f (by omega) hC'e
  -- Analyze g0: must be OR(0, y0) or OR(y0, 0) with y0 < 11 + i0, y0 ≠ 0, y0 ≠ 10
  have hg0Form : ∃ y0, y0 < 11 + i0 ∧ y0 ≠ 0 ∧ y0 ≠ 10 ∧ (g0 = ⟨.or, [0, y0]⟩ ∨ g0 = ⟨.or, [y0, 0]⟩) := by
    rcases g0 with ⟨op0, ins0⟩
    rcases hnorm0 with ⟨rfl, p, _, rfl⟩ | ⟨hop0, p, q, hpLt, hqLt, hpqNe, rfl⟩
    · -- g0 = NOT(0) = wire 10 -> replaceGate with .inr 10 -> close17!
      simp [rd_not] at hg0r0; subst hg0r0
      obtain ⟨hsp, htlen⟩ := splitAt C.gates i0 ⟨.not, [0]⟩ hC0get
      let a := C.gates.take i0
      let c := C.gates.drop (i0 + 1)
      have hCf' : FanInTwo ⟨a ++ ⟨.not, [0]⟩ :: c, C.output⟩ := by rwa [← hsp]
      have hCe' : ∀ x, (Circuit.mk (a ++ ⟨.not, [0]⟩ :: c) C.output).eval (seed0 x) = fP x := by rwa [← hsp]
      obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a c ⟨.not, [0]⟩ C.output (.inr 10) hCf'
        (fun j hj => by cases hj; omega)
        (fun x => by
          dsimp only [evalV]
          simp only [List.map_cons, List.map_nil, eval_not, List.headD_cons]
          rw [retain a _ 10 (by rw [seed0Len]; omega), retain a _ 0 (by rw [seed0Len]; omega)]
          simp only [seed0]
          rw [List.getD_append_right (List.ofFn x) _ _ _ (by simp), List.getD_append (List.ofFn x) _ _ _ (by simp),
            List.getD_eq_getElem (List.ofFn x) _ (by simp), List.getElem_ofFn]; simp)
        hCe'
      have hlenS : a.length + c.length = 17 := by
        have : C.gates.length = a.length + c.length + 1 := by dsimp only [a, c]; (conv_lhs => rw [hsp]); simp only [List.length_append, List.length_cons]; omega
        change C.gates.length = 18 at hCeq18; omega
      exact (close17 C' hC'f (by omega) hC'e).elim
    · rcases hop0 with rfl | rfl
      · -- g0 = AND(p, q) with 0 ∈ {p, q} -> becomes constant false under env0_x0!
        have hconst0 : isConst (simpStep 9 ((C.gates.take i0).foldl (simpStep 9) (env0_x0, [])) ⟨.and, [p, q]⟩).1 (11 + i0) = true := by
          have hsub : ∀ h ∈ C.gates.take i0, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2 :=
            fun h hh => hCfan h (List.mem_of_mem_take hh)
          have hsf := simpFold 9 (C.gates.take i0) (env0_x0, []) hsub (fun _ h => by cases h) henv0x0_bdd
          have htlen : (C.gates.take i0).length = i0 := by
            rw [List.length_take, Nat.min_eq_left]; change i0 ≤ C.gates.length; change C.gates.length = 18 at hCeq18; omega
          have hlen1 : ((C.gates.take i0).foldl (simpStep 9) (env0_x0, [])).1.length = 11 + i0 := by
            rw [hsf.2.1, henv0x0_len, htlen]
          have hget0 : ((C.gates.take i0).foldl (simpStep 9) (env0_x0, [])).1.getD 0 (.inl false) = .inl false := by
            rw [hsf.2.2.2.1 0 (by rw [henv0x0_len]; omega), henv0x0_0]
          rw [← hlen1]
          exact simpStep_makesConst 9 _ ⟨.and, [p, q]⟩ 0 (Or.inl rfl) (by simp) hg0r0 rfl hget0
        have hno3 := noThirdReader i0 ⟨.and, [p, q]⟩ hC0get (by simp [hg0r0]) hconst0
        by_cases hg1r : rd g1 (11 + i0) = true
        · -- g1 reads 10 AND 11 + i0! Extract y0 (the other input of g0)
          have hy0Ex : ∃ y0, y0 < 11 + i0 ∧ (p = 0 ∧ q = y0 ∨ p = y0 ∧ q = 0) := by
            simp [rd_and] at hg0r0
            rcases hg0r0 with rfl | rfl
            · exact ⟨q, hqLt, Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨p, hpLt, Or.inr ⟨rfl, rfl⟩⟩
          obtain ⟨y0, hy0Lt, hy0pq⟩ := hy0Ex
          have hi0lti1 : i0 < i1 := by
            rcases g1 with ⟨op1, ins1⟩
            rcases hnorm1 with ⟨rfl, r, hrLt, rfl⟩ | ⟨hop1, r, s, hrLt, hsLt, _, rfl⟩
            · simp [rd_not] at hg1r10 hg1r; omega
            · rcases hop1 with rfl | rfl
              · simp [rd_and] at hg1r; rcases hg1r with rfl | rfl <;> omega
              · simp [rd_or] at hg1r; rcases hg1r with rfl | rfl <;> omega
          -- Check op of g1 (cannot be NOT since it reads 10 and 11+i0)
          rcases g1 with ⟨op1, ins1⟩
          rcases hnorm1 with ⟨rfl, r, _, rfl⟩ | ⟨hop1, r, s, _, _, _, rfl⟩
          · simp [rd_not] at hg1r10 hg1r; omega
          · rcases hop1 with rfl | rfl
            · -- g1 = AND(10, 11+i0) or AND(11+i0, 10) -> evaluates to false!
              obtain ⟨hsp1, htlen1⟩ := splitAt C.gates i1 ⟨.and, [r, s]⟩ hC1get
              let a1 := C.gates.take i1
              let c1 := C.gates.drop (i1 + 1)
              have hCf1 : FanInTwo ⟨a1 ++ ⟨.and, [r, s]⟩ :: c1, C.output⟩ := by rwa [← hsp1]
              have hCe1 : ∀ x, (Circuit.mk (a1 ++ ⟨.and, [r, s]⟩ :: c1) C.output).eval (seed0 x) = fP x := by rwa [← hsp1]
              have hvalF : ∀ x : Fin 10 → Bool,
                  GateOp.and.eval ([r, s].map fun k => (a1.foldl step (seed0 x)).getD k false) = false := by
                intro x
                simp [rd_and] at hg1r10 hg1r
                simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have h10v : (a1.foldl step (seed0 x)).getD 10 false = !x 0 := by
                  rw [retain a1 _ 10 (by rw [seed0Len]; omega)]; simp [seed0]
                have h0v : (a1.foldl step (seed0 x)).getD (11 + i0) false =
                    (x 0 && (a1.foldl step (seed0 x)).getD y0 false) := by
                  have ha1sp : a1 = C.gates.take i0 ++ ⟨.and, [p, q]⟩ :: (a1.drop (i0 + 1)) := by
                    have hgi0 : a1[i0]? = some ⟨.and, [p, q]⟩ := by
                      dsimp only [a1]; rw [List.getElem?_take_of_lt hi0lti1]; exact hC0get
                    have hsp' := (splitAt a1 i0 ⟨.and, [p, q]⟩ hgi0).1
                    rwa [List.take_take, Nat.min_eq_left hi0lti1.le] at hsp'
                  have ha0len : ((C.gates.take i0).foldl step (seed0 x)).length = 11 + i0 := by
                    rw [runLen, seed0Len, List.length_take, Nat.min_eq_left]; change i0 ≤ C.gates.length; change C.gates.length = 18 at hCeq18; omega
                  have hret0 : (a1.foldl step (seed0 x)).getD (11 + i0) false =
                      ((step ((C.gates.take i0).foldl step (seed0 x)) ⟨.and, [p, q]⟩)).getD (11 + i0) false := by
                    conv_lhs => rw [ha1sp, List.foldl_append, List.foldl_cons]
                    exact retain _ _ (11 + i0) (by rw [stepLen, ha0len]; omega)
                  have hrety : (a1.foldl step (seed0 x)).getD y0 false =
                      ((C.gates.take i0).foldl step (seed0 x)).getD y0 false := by
                    conv_lhs => rw [ha1sp, List.foldl_append, List.foldl_cons]
                    rw [retain _ _ y0 (by rw [stepLen, ha0len]; omega)]
                    exact List.getD_append _ _ false y0 (by omega)
                  have hretx0 : ((C.gates.take i0).foldl step (seed0 x)).getD 0 false = x 0 := by
                    rw [retain _ _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
                    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
                  rw [hret0, hrety]
                  dsimp only [step]
                  rw [List.getD_append_right _ _ _ _ ha0len.le, ha0len, Nat.sub_self, List.getD_cons_zero]
                  simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rcases hy0pq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · rw [hretx0]
                  · rw [hretx0, Bool.and_comm]
                rcases hg1r10 with rfl | rfl <;> rcases hg1r with hq' | hq'
                · omega
                · subst hq'; rw [h10v, h0v]; cases x 0 <;> simp
                · subst hq'; rw [h10v, h0v]; cases x 0 <;> simp
                · omega
              obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a1 c1 ⟨.and, [r, s]⟩ C.output (.inl false) hCf1
                (fun _ h => by cases h) (fun x => (hvalF x).symm) hCe1
              have hlenS : a1.length + c1.length = 17 := by
                have : C.gates.length = a1.length + c1.length + 1 := by dsimp only [a1, c1]; (conv_lhs => rw [hsp1]); simp only [List.length_append, List.length_cons]; omega
                change C.gates.length = 18 at hCeq18; omega
              exact (close17 C' hC'f (by omega) hC'e).elim
            · -- g1 = OR(10, 11+i0) or OR(11+i0, 10) -> rewire g1 := OR(10, y0), then gate i0 is dead -> deadGateClose!
              obtain ⟨hsp1, htlen1⟩ := splitAt C.gates i1 ⟨.or, [r, s]⟩ hC1get
              let a1 := C.gates.take i1
              let c1 := C.gates.drop (i1 + 1)
              let g1' : Gate := ⟨.or, [10, y0]⟩
              let C1 : Circuit := ⟨a1 ++ g1' :: c1, C.output⟩
              have hC1f : FanInTwo C1 := by
                intro h hh
                rcases List.mem_append.mp hh with h1 | h2
                · exact hCfan h (by rw [hsp1]; exact List.mem_append_left _ h1)
                · rcases List.mem_cons.mp h2 with rfl | h3
                  · exact ⟨Or.inr (Or.inl rfl), by simp [g1']⟩
                  · exact hCfan h (by rw [hsp1]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h3))
              have hC1s : C1.size ≤ 18 := by
                change (a1 ++ g1' :: c1).length ≤ 18
                have : C.gates.length = a1.length + c1.length + 1 := by dsimp only [a1, c1]; (conv_lhs => rw [hsp1]); simp only [List.length_append, List.length_cons]; omega
                simp only [List.length_append, List.length_cons]; change C.gates.length = 18 at hCeq18; omega
              have hC1e : ∀ x, C1.eval (seed0 x) = fP x := by
                intro x
                have horig := hCeval x
                change (C.gates.foldl step (seed0 x)).getD C.output false = fP x at horig
                rw [hsp1, List.foldl_append, List.foldl_cons] at horig
                change ((a1 ++ g1' :: c1).foldl step (seed0 x)).getD C.output false = fP x
                rw [List.foldl_append, List.foldl_cons]
                have hstepEq : step (a1.foldl step (seed0 x)) g1' = step (a1.foldl step (seed0 x)) ⟨.or, [r, s]⟩ := by
                  rw [stepDef, stepDef]; dsimp only [g1']; congr 2
                  simp [rd_or] at hg1r10 hg1r
                  simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have h10v : (a1.foldl step (seed0 x)).getD 10 false = !x 0 := by
                    rw [retain a1 _ 10 (by rw [seed0Len]; omega)]; simp [seed0]
                  have h0v : (a1.foldl step (seed0 x)).getD (11 + i0) false =
                      (x 0 && (a1.foldl step (seed0 x)).getD y0 false) := by
                    have ha1sp : a1 = C.gates.take i0 ++ ⟨.and, [p, q]⟩ :: (a1.drop (i0 + 1)) := by
                      have hgi0 : a1[i0]? = some ⟨.and, [p, q]⟩ := by
                        dsimp only [a1]; rw [List.getElem?_take_of_lt hi0lti1]; exact hC0get
                      have hsp' := (splitAt a1 i0 ⟨.and, [p, q]⟩ hgi0).1
                      rwa [List.take_take, Nat.min_eq_left hi0lti1.le] at hsp'
                    have ha0len : ((C.gates.take i0).foldl step (seed0 x)).length = 11 + i0 := by
                      rw [runLen, seed0Len, List.length_take, Nat.min_eq_left]; change i0 ≤ C.gates.length; change C.gates.length = 18 at hCeq18; omega
                    have hret0 : (a1.foldl step (seed0 x)).getD (11 + i0) false =
                        ((step ((C.gates.take i0).foldl step (seed0 x)) ⟨.and, [p, q]⟩)).getD (11 + i0) false := by
                      conv_lhs => rw [ha1sp, List.foldl_append, List.foldl_cons]
                      exact retain _ _ (11 + i0) (by rw [stepLen, ha0len]; omega)
                    have hrety : (a1.foldl step (seed0 x)).getD y0 false =
                        ((C.gates.take i0).foldl step (seed0 x)).getD y0 false := by
                      conv_lhs => rw [ha1sp, List.foldl_append, List.foldl_cons]
                      rw [retain _ _ y0 (by rw [stepLen, ha0len]; omega)]
                      exact List.getD_append _ _ false y0 (by omega)
                    have hretx0 : ((C.gates.take i0).foldl step (seed0 x)).getD 0 false = x 0 := by
                      rw [retain _ _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
                      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
                    rw [hret0, hrety]
                    dsimp only [step]
                    rw [List.getD_append_right _ _ _ _ ha0len.le, ha0len, Nat.sub_self, List.getD_cons_zero]
                    simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rcases hy0pq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rw [hretx0]
                    · rw [hretx0, Bool.and_comm]
                  rcases hg1r10 with rfl | rfl <;> rcases hg1r with hq' | hq'
                  · omega
                  · subst hq'; rw [h10v, h0v]; cases x 0 <;> simp
                  · subst hq'; rw [h10v, h0v]; cases x 0 <;> simp
                  · omega
                rw [hstepEq]; exact horig
              have hC1get0 : C1.gates[i0]? = some ⟨.and, [p, q]⟩ := by
                dsimp only [C1]
                rw [List.getElem?_append_left (by rw [htlen1]; exact hi0lti1)]
                dsimp only [a1]; rw [List.getElem?_take_of_lt hi0lti1]; exact hC0get
              exact (deadGateClose C1 i0 ⟨.and, [p, q]⟩ hC1f hC1s hC1e hC1get0
                (by dsimp only [C1, C]; omega)
                (fun j h hj hlt => by
                  by_cases hj1 : j = i1
                  · subst hj1
                    dsimp only [C1] at hj
                    rw [List.getElem?_append_right (by rw [htlen1]), htlen1, Nat.sub_self] at hj
                    cases hj; dsimp only [g1']; rw [rd_or]; simp; omega
                  · have hCj : C.gates[j]? = some h := by
                      rw [hsp1]
                      by_cases hlt1 : j < i1
                      · rw [List.getElem?_append_left (by rw [htlen1]; exact hlt1)]
                        dsimp only [C1] at hj
                        rwa [List.getElem?_append_left (by rw [htlen1]; exact hlt1)] at hj
                      · have hgt1 : i1 < j := by omega
                        dsimp only [C1] at hj
                        rw [List.getElem?_append_right (by rw [htlen1]; omega)] at hj ⊢
                        have hsub : j - a1.length = (j - a1.length - 1) + 1 := by
                          have ha1l : a1.length = i1 := htlen1; omega
                        rw [hsub] at hj ⊢; exact hj
                    exact hno3 j h hCj (by omega) hj1)).elim
        · -- g1 does not read 11 + i0 either -> gate i0 is completely dead in C -> deadGateClose!
          exact (deadGateClose C i0 ⟨.and, [p, q]⟩ hCfan (by omega) hCeval hC0get
            (by dsimp only [C]; omega)
            (fun j h hj hlt => by
              by_cases hj1 : j = i1
              · subst hj1; rw [hC1get] at hj; cases hj
                exact Bool.eq_false_iff.mpr hg1r
              · exact hno3 j h hj (by omega) hj1)).elim
      · -- g0 = OR(p, q): SUCCESS! Extract y0!
        simp [rd_or] at hg0r0
        have hpNo10 : p ≠ 10 := by intro h; subst h; simp [rd_or] at hg0No10
        have hqNo10 : q ≠ 10 := by intro h; subst h; simp [rd_or] at hg0No10
        rcases hg0r0 with rfl | rfl
        · exact ⟨q, hqLt, hpqNe.symm, hqNo10, Or.inl rfl⟩
        · exact ⟨p, hpLt, hpqNe, hpNo10, Or.inr rfl⟩
  obtain ⟨y0, hy0Lt, hy0Ne0, hy0Ne10, hg0Eq⟩ := hg0Form
  -- Analyze g1: must be AND(10, y1) or AND(y1, 10) with y1 < 11 + i1, y1 ≠ 0, y1 ≠ 10
  have hg1Form : ∃ y1, y1 < 11 + i1 ∧ y1 ≠ 0 ∧ y1 ≠ 10 ∧ (g1 = ⟨.and, [10, y1]⟩ ∨ g1 = ⟨.and, [y1, 10]⟩) := by
    rcases g1 with ⟨op1, ins1⟩
    rcases hnorm1 with ⟨rfl, r, _, rfl⟩ | ⟨hop1, r, s, hrLt, hsLt, hrsNe, rfl⟩
    · -- g1 = NOT(10) = wire 0 -> replaceGate with .inr 0 -> close17!
      simp [rd_not] at hg1r10; subst hg1r10
      obtain ⟨hsp, htlen⟩ := splitAt C.gates i1 ⟨.not, [10]⟩ hC1get
      let a := C.gates.take i1
      let c := C.gates.drop (i1 + 1)
      have hCf' : FanInTwo ⟨a ++ ⟨.not, [10]⟩ :: c, C.output⟩ := by rwa [← hsp]
      have hCe' : ∀ x, (Circuit.mk (a ++ ⟨.not, [10]⟩ :: c) C.output).eval (seed0 x) = fP x := by rwa [← hsp]
      obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a c ⟨.not, [10]⟩ C.output (.inr 0) hCf'
        (fun j hj => by cases hj; omega)
        (fun x => by
          dsimp only [evalV]
          simp only [List.map_cons, List.map_nil, eval_not, List.headD_cons]
          rw [retain a _ 10 (by rw [seed0Len]; omega), retain a _ 0 (by rw [seed0Len]; omega)]
          simp only [seed0]
          rw [List.getD_append (List.ofFn x) _ _ 0 (by simp), List.getD_append_right (List.ofFn x) _ _ 10 (by simp),
            List.getD_eq_getElem (List.ofFn x) _ (by simp), List.getElem_ofFn]; simp)
        hCe'
      have hlenS : a.length + c.length = 17 := by
        have : C.gates.length = a.length + c.length + 1 := by dsimp only [a, c]; (conv_lhs => rw [hsp]); simp only [List.length_append, List.length_cons]; omega
        change C.gates.length = 18 at hCeq18; omega
      exact (close17 C' hC'f (by omega) hC'e).elim
    · rcases hop1 with rfl | rfl
      · -- g1 = AND(r, s): SUCCESS! Extract y1!
        simp [rd_and] at hg1r10
        have hrNo0 : r ≠ 0 := by intro h; subst h; simp [rd_and] at hg1No0
        have hsNo0 : s ≠ 0 := by intro h; subst h; simp [rd_and] at hg1No0
        rcases hg1r10 with rfl | rfl
        · exact ⟨s, hsLt, hsNo0, hrsNe.symm, Or.inl rfl⟩
        · exact ⟨r, hrLt, hrNo0, hrsNe, Or.inr rfl⟩
      · -- g1 = OR(r, s) with 10 ∈ {r, s} -> becomes constant true under env0_x0!
        have hconst1 : isConst (simpStep 9 ((C.gates.take i1).foldl (simpStep 9) (env0_x0, [])) ⟨.or, [r, s]⟩).1 (11 + i1) = true := by
          have hsub : ∀ h ∈ C.gates.take i1, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2 :=
            fun h hh => hCfan h (List.mem_of_mem_take hh)
          have hsf := simpFold 9 (C.gates.take i1) (env0_x0, []) hsub (fun _ h => by cases h) henv0x0_bdd
          have htlen : (C.gates.take i1).length = i1 := by
            rw [List.length_take, Nat.min_eq_left]; change i1 ≤ C.gates.length; change C.gates.length = 18 at hCeq18; omega
          have hlen1 : ((C.gates.take i1).foldl (simpStep 9) (env0_x0, [])).1.length = 11 + i1 := by
            rw [hsf.2.1, henv0x0_len, htlen]
          have hget10 : ((C.gates.take i1).foldl (simpStep 9) (env0_x0, [])).1.getD 10 (.inl false) = .inl true := by
            rw [hsf.2.2.2.1 10 (by rw [henv0x0_len]; omega), henv0x0_10]
          rw [← hlen1]
          exact simpStep_makesConstTrueOr 9 _ ⟨.or, [r, s]⟩ 10 rfl (by simp) hg1r10 hget10
        have hno3 := noThirdReader i1 ⟨.or, [r, s]⟩ hC1get (by simp [hg1r10]) hconst1
        by_cases hg0r : rd g0 (11 + i1) = true
        · -- g0 = OR(0, 11+i1) or OR(11+i1, 0), so g0 = x 0 || (!x 0 || ...) = true!
          have hy0Eq : y0 = 11 + i1 := by
            rcases hg0Eq with h | h <;> (rw [h, rd_or] at hg0r; simp at hg0r; omega)
          have hi1lti0 : i1 < i0 := by omega
          obtain ⟨hsp0, htlen0⟩ := splitAt C.gates i0 g0 hC0get
          let a0 := C.gates.take i0
          let c0 := C.gates.drop (i0 + 1)
          have hCf0 : FanInTwo ⟨a0 ++ g0 :: c0, C.output⟩ := by rwa [← hsp0]
          have hCe0 : ∀ x, (Circuit.mk (a0 ++ g0 :: c0) C.output).eval (seed0 x) = fP x := by rwa [← hsp0]
          have hvalT : ∀ x : Fin 10 → Bool,
              g0.op.eval (g0.inputs.map fun k => (a0.foldl step (seed0 x)).getD k false) = true := by
            intro x
            have hx0v : (a0.foldl step (seed0 x)).getD 0 false = x 0 := by
              rw [retain a0 _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
              rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
            have h1v : (a0.foldl step (seed0 x)).getD (11 + i1) false =
                (!x 0 || (a0.foldl step (seed0 x)).getD (if r = 10 then s else r) false) := by
              have ha0sp : a0 = C.gates.take i1 ++ ⟨.or, [r, s]⟩ :: (a0.drop (i1 + 1)) := by
                have hgi1 : a0[i1]? = some ⟨.or, [r, s]⟩ := by
                  dsimp only [a0]; rw [List.getElem?_take_of_lt hi1lti0]; exact hC1get
                have hsp' := (splitAt a0 i1 ⟨.or, [r, s]⟩ hgi1).1
                rwa [List.take_take, Nat.min_eq_left hi1lti0.le] at hsp'
              have ha1len : ((C.gates.take i1).foldl step (seed0 x)).length = 11 + i1 := by
                rw [runLen, seed0Len, List.length_take, Nat.min_eq_left]; change i1 ≤ C.gates.length; change C.gates.length = 18 at hCeq18; omega
              have hret1 : (a0.foldl step (seed0 x)).getD (11 + i1) false =
                  ((step ((C.gates.take i1).foldl step (seed0 x)) ⟨.or, [r, s]⟩)).getD (11 + i1) false := by
                conv_lhs => rw [ha0sp, List.foldl_append, List.foldl_cons]
                exact retain _ _ (11 + i1) (by rw [stepLen, ha1len]; omega)
              have hret10 : ((C.gates.take i1).foldl step (seed0 x)).getD 10 false = !x 0 := by
                rw [retain _ _ 10 (by rw [seed0Len]; omega)]; simp [seed0]
              have hretOther : ∀ w, w < 11 + i1 →
                  (a0.foldl step (seed0 x)).getD w false = ((C.gates.take i1).foldl step (seed0 x)).getD w false := by
                intro w hw
                conv_lhs => rw [ha0sp, List.foldl_append, List.foldl_cons]
                rw [retain _ _ w (by rw [stepLen, ha1len]; omega)]
                exact List.getD_append _ _ false w (by omega)
              rw [hret1, stepDef]
              rw [List.getD_append_right _ _ _ _ ha1len.le, ha1len, Nat.sub_self, List.getD_cons_zero]
              simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              simp [rd_or] at hg1r10
              rcases hg1r10 with rfl | rfl
              · simp only [↓reduceIte, hret10, hretOther s hsLt]
              · have hrne : r ≠ 10 := hrsNe
                simp only [hrne, ↓reduceIte, hret10, hretOther r hrLt]
                exact Bool.or_comm _ _
            rcases hg0Eq with h | h <;> rw [h]
            · simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                hx0v, hy0Eq, h1v]
              cases x 0 <;> simp
            · simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                hx0v, hy0Eq, h1v]
              cases x 0 <;> simp
          obtain ⟨C', hC'f, hC's, hC'e⟩ := replaceGate a0 c0 g0 C.output (.inl true) hCf0
            (fun _ h => by cases h) (fun x => (hvalT x).symm) hCe0
          have hlenS : a0.length + c0.length = 17 := by
            have : C.gates.length = a0.length + c0.length + 1 := by dsimp only [a0, c0]; (conv_lhs => rw [hsp0]); simp only [List.length_append, List.length_cons]; omega
            change C.gates.length = 18 at hCeq18; omega
          exact (close17 C' hC'f (by omega) hC'e).elim
        · -- g0 does not read 11 + i1 either -> gate i1 is completely dead in C -> deadGateClose!
          exact (deadGateClose C i1 ⟨.or, [r, s]⟩ hCfan (by omega) hCeval hC1get
            (by dsimp only [C]; omega)
            (fun j h hj hlt => by
              by_cases hj0 : j = i0
              · subst hj0; rw [hC0get] at hj; cases hj
                exact Bool.eq_false_iff.mpr hg0r
              · exact hno3 j h hj hj0 (by omega))).elim
  obtain ⟨y1, hy1Lt, hy1Ne0, hy1Ne10, hg1Eq⟩ := hg1Form
  -- Step 4: Commute inputs of gate i0 to [0, y0] and gate i1 to [10, y1] -> D3!
  let normG : ℕ × Gate → Gate := fun p =>
    if p.1 = i0 then ⟨.or, [0, y0]⟩ else if p.1 = i1 then ⟨.and, [10, y1]⟩ else p.2
  let D3 : Circuit := ⟨((List.finRange D2.gates.length).map fun j => normG (j.val, D2.gates.get j)), 0⟩
  have hD3len : D3.gates.length = 17 := by
    dsimp only [D3]; simp only [List.length_map, List.length_finRange]; exact hD2eq17
  have hD3get : ∀ j (hj : j < 17),
      D3.gates[j]? = some (if j = i0 then ⟨.or, [0, y0]⟩ else if j = i1 then ⟨.and, [10, y1]⟩ else D2.gates[j]'(by change j < D2.size; omega)) := by
    intro j hj
    have hj3 : j < D3.gates.length := by omega
    rw [List.getElem?_eq_getElem hj3]
    congr 1
    dsimp only [D3]
    rw [List.getElem_map, List.getElem_finRange]
    rfl
  have hD3evalEq : ∀ (y : Fin 10 → Bool) (k : ℕ), k ≤ 17 →
      (D3.gates.take k).foldl step (seed0 y) = (D2.gates.take k).foldl step (seed0 y) := by
    intro y k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hle
      have hk17 : k < 17 := by omega
      have htk3 : D3.gates.take (k + 1) = D3.gates.take k ++ [D3.gates[k]'(by omega)] :=
        List.take_succ_eq_append_getElem (by omega)
      have htk2 : D2.gates.take (k + 1) = D2.gates.take k ++ [D2.gates[k]'(by change k < D2.size; omega)] :=
        List.take_succ_eq_append_getElem (by change k < D2.size; omega)
      rw [htk3, htk2, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
        List.foldl_nil, List.foldl_nil, ih (by omega)]
      dsimp only [step]
      congr 2
      have h3g : D3.gates[k]'(by omega) =
          if k = i0 then ⟨.or, [0, y0]⟩ else if k = i1 then ⟨.and, [10, y1]⟩ else D2.gates[k]'(by change k < D2.size; omega) := by
        have h := hD3get k hk17; rw [List.getElem?_eq_getElem (by omega)] at h; exact Option.some.inj h
      rw [h3g]
      by_cases hk0 : k = i0
      · subst hk0; simp only [↓reduceIte, hi0eq]
        rcases hg0Eq with h | h
        · rw [h]
        · rw [h]; simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]; exact Bool.or_comm _ _
      · simp only [hk0, ↓reduceIte]
        by_cases hk1 : k = i1
        · subst hk1; simp only [↓reduceIte, hi1eq]
          rcases hg1Eq with h | h
          · rw [h]
          · rw [h]; simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]; exact Bool.and_comm _ _
        · simp only [hk1, ↓reduceIte]
  have hD3wires : ∀ y : Fin 10 → Bool, D3.wires (seed0 y) = D2.gates.foldl step (seed0 y) := fun y => by
    have h := hD3evalEq y 17 le_rfl
    have h3 : D3.gates.take 17 = D3.gates := List.take_of_length_le (by omega)
    have h2 : D2.gates.take 17 = D2.gates := List.take_of_length_le (by change D2.size ≤ 17; omega)
    rw [h3, h2] at h; exact h
  have hD3fan : FanInTwo D3 := by
    intro g hg
    obtain ⟨j, hjlt, hjeq⟩ := List.getElem_of_mem hg
    have hj17 : j < 17 := by omega
    have h := hD3get j hj17
    rw [List.getElem?_eq_getElem hjlt, hjeq] at h
    have hgEq := (Option.some.inj h).symm
    subst hgEq
    by_cases hj0 : j = i0
    · simp only [hj0, ↓reduceIte]; exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · simp only [hj0, ↓reduceIte]
      by_cases hj1 : j = i1
      · simp only [hj1, ↓reduceIte]; exact ⟨Or.inl rfl, by simp⟩
      · simp only [hj1, ↓reduceIte]; exact hD2fan _ (List.getElem_mem _)
  -- Verify i0 < 16 and i0 + 1 ≠ u2 - 10 (evaluating on e_0!)
  let e0 : Fin 10 → Bool := fun j => decide (j = 0)
  have hD3g0True : (D3.wires (seed0 e0)).getD (11 + i0) false = true := by
    have h3g : D3.gates[i0]? = some ⟨.or, [0, y0]⟩ := by
      have h := hD3get i0 hi017; simp only [↓reduceIte] at h; exact h
    obtain ⟨hsp, htlen⟩ := splitAt D3.gates i0 ⟨.or, [0, y0]⟩ h3g
    change (D3.gates.foldl step (seed0 e0)).getD (11 + i0) false = true
    rw [hsp, List.foldl_append, List.foldl_cons]
    have halen : ((D3.gates.take i0).foldl step (seed0 e0)).length = 11 + i0 := by rw [runLen, seed0Len, htlen]
    rw [retain _ _ (11 + i0) (by rw [stepLen, halen]; omega)]
    dsimp only [step]
    rw [List.getD_append_right _ _ _ _ halen.le, halen, Nat.sub_self, List.getD_cons_zero]
    simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have h0v : ((D3.gates.take i0).foldl step (seed0 e0)).getD 0 false = true := by
      rw [retain _ _ 0 (by rw [seed0Len]; omega)]; simp only [seed0]
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    rw [h0v]; rfl
  have he0Off : (D3.wires (seed0 e0)).getD u2 false = false ∧ (D3.wires (seed0 e0)).getD 27 false = false := by
    have hc := hCov2 e0
    rw [← hD3wires e0, hv2eq27, fPUnit 0] at hc
    exact Bool.or_eq_false_iff.mp hc
  have hi0Lt16 : i0 < 16 := by
    by_contra! hge16
    have hi016 : i0 = 16 := by omega
    subst hi016
    rw [he0Off.2] at hD3g0True; cases hD3g0True
  let uFin : Fin 16 := ⟨u2 - 11, by omega⟩
  have huFinVal : 11 + uFin.val = u2 := by dsimp only [uFin]; omega
  have hi0NeU : uFin ≠ ⟨i0, hi0Lt16⟩ := by
    intro h
    have h1 : 11 + i0 = u2 := by
      have hv := congrArg Fin.val h; dsimp only [uFin] at hv; omega
    rw [h1, he0Off.1] at hD3g0True; cases hD3g0True
  -- Step 5: Prove degree + cascade <= 3 for every k : Fin 10 with 0 < k.val via h670!
  have hDegCasc : ∀ k : Fin 10, 0 < k.val →
      D3.gates.countP (fun g => rd g k.val) ≤ 3 ∧
      ∀ i : Fin D3.gates.length, rd (D3.gates.get i) k.val = true → (D3.gates.get i).op.eval [true, false] = false →
        D3.gates.countP (fun h => rd h k.val || rd h (11 + i.val)) ≤ 3 := by
    intro k hkPos
    have hkNe0 : k ≠ 0 := fun h => by subst h; simp at hkPos
    -- Full 19-gate circuit on 10 inputs: [NOT(0)] ++ D3.gates ++ [OR(u2, 27)]
    let fullGs : List Gate := ⟨.not, [0]⟩ :: (D3.gates ++ [⟨.or, [u2, 27]⟩])
    have hFullFan : ∀ g ∈ fullGs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg1
      · exact ⟨Or.inr (Or.inr rfl), by simp⟩
      · rcases List.mem_append.mp hg1 with h1 | h2
        · exact hD3fan g h1
        · obtain rfl := List.mem_singleton.mp h2; exact ⟨Or.inr (Or.inl rfl), by simp⟩
    let envK : List (Sum Bool ℕ) :=
      (List.finRange 10).map (fun i : Fin 10 => if i = k then .inl false else .inr (aut9 k i).val)
    have henvKLen : envK.length = 10 := by simp [envK]
    have henvKBdd : ∀ s ∈ envK, ∀ j, s = .inr j → j < 9 + ([] : List Gate).length := by
      intro s hs j hj
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
      by_cases hik : i = k
      · simp [hik] at hj
      · simp only [hik, ↓reduceIte, Sum.inr.injEq] at hj; subst hj
        have hne : aut9 k i ≠ 9 := fun h => hik (aut9Inj k i k (h.trans (aut9Fix k).symm))
        have hlt := (aut9 k i).isLt
        have hnv : (aut9 k i).val ≠ 9 := fun hv => hne (Fin.ext hv)
        simp; omega
    have henvKk : envK.getD k.val (.inl false) = .inl false := by
      have hl : k.val < envK.length := by rw [henvKLen]; exact k.isLt
      rw [List.getD_eq_getElem _ _ hl]; simp [envK]
    let xOfK : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i =>
      if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)
    have htrK : ∀ y : Fin 9 → Bool, ∀ i < envK.length,
        evalV (([] : List Gate).foldl step (List.ofFn y)) (envK.getD i (.inl false)) =
        (List.ofFn (xOfK y)).getD i false := by
      intro y i hi
      simp only [List.foldl_nil]
      have h10 : i < 10 := by rw [henvKLen] at hi; exact hi
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simp [h10]), List.getElem_ofFn]
      dsimp only [envK, xOfK]
      rw [List.getElem_map, List.getElem_finRange]
      simp only [Fin.cast_mk]
      by_cases hik : (⟨i, h10⟩ : Fin 10) = k
      · simp [hik, evalV]
      · simp only [hik, ↓reduceIte]
        dsimp only [evalV]
        have hne : aut9 k ⟨i, h10⟩ ≠ 9 := fun h => hik (aut9Inj k ⟨i, h10⟩ k (h.trans (aut9Fix k).symm))
        have hlt := (aut9 k ⟨i, h10⟩).isLt
        have hnv : (aut9 k ⟨i, h10⟩).val ≠ 9 := fun hv => hne (Fin.ext hv)
        have hlt9 : (aut9 k ⟨i, h10⟩).val < 9 := by omega
        rw [List.getD_eq_getElem _ _ (by simp [hlt9]), List.getElem_ofFn]
        congr 1; exact Fin.ext (Nat.mod_eq_of_lt hlt9).symm
    have hFullEval : ∀ y : Fin 9 → Bool, (fullGs.foldl step (List.ofFn (xOfK y))).getD 28 false = f670 y := by
      intro y
      dsimp only [fullGs]
      rw [List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hst0 : step (List.ofFn (xOfK y)) ⟨.not, [0]⟩ = seed0 (xOfK y) := by
        dsimp only [step, seed0]
        simp only [List.map_cons, List.map_nil, eval_not, List.headD_cons]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      rw [hst0]
      have hlen : (D3.gates.foldl step (seed0 (xOfK y))).length = 28 := by
        rw [runLen, seed0Len, hD3len]
      dsimp only [step]
      rw [List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self, List.getD_cons_zero]
      simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h32 := hD3wires (xOfK y)
      change D3.gates.foldl step (seed0 (xOfK y)) = D2.gates.foldl step (seed0 (xOfK y)) at h32
      rw [h32, ← hv2eq27]
      exact (hCov2 (xOfK y)).trans (aut9Match k y)
    have hFull16 : 16 ≤ (fullGs.foldl (simpStep 9) (envK, [])).2.length := by
      have hhas := toCircuit 9 fullGs (envK, []) 28 f670 (fun y => List.ofFn (xOfK y))
        hFullFan (fun _ h => by cases h) henvKBdd (fun _ => by simp [henvKLen]) htrK hFullEval f670Zero
      by_contra! hlt16
      obtain ⟨E, hEf, hEs, hEe⟩ := hhas
      exact h670 ⟨E, hEf, by omega, hEe⟩
    -- After stepping gate 0 = NOT(0), state s1 has s1.1.length = 11, s1.2.length <= 1, s1.1[k] = .inl false
    let s1 := simpStep 9 (envK, []) ⟨.not, [0]⟩
    have hs1Len : s1.1.length = 11 :=
      (simpStep_envLen 9 (envK, []) ⟨.not, [0]⟩).trans (by dsimp only; rw [henvKLen])
    have hs1Sz : s1.2.length ≤ 1 := simpStep_lenLe 9 (envK, []) ⟨.not, [0]⟩
    have hs1k : s1.1.getD k.val (.inl false) = .inl false := by
      rw [simpStep_envPrefix 9 (envK, []) ⟨.not, [0]⟩ k.val (by rw [henvKLen]; exact k.isLt), henvKk]
    have hFullStep : (fullGs.foldl (simpStep 9) (envK, [])).2.length ≤
        (D3.gates.foldl (simpStep 9) s1).2.length + 1 := by
      dsimp only [fullGs]
      rw [List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact simpStep_lenLe 9 (D3.gates.foldl (simpStep 9) s1) ⟨.or, [u2, 27]⟩
    have hD315 : 15 ≤ (D3.gates.foldl (simpStep 9) s1).2.length := by omega
    constructor
    · have hcf := countFold 9 (fun g => rd g k.val) D3.gates s1
        (fun g s hg _ hpref hP => by
          obtain ⟨hop, hgl⟩ := hD3fan g hg
          exact simpStep_dropConst 9 s g k.val hop hgl hP
            (by dsimp only [isConst]; rw [hpref k.val (by rw [hs1Len]; omega), hs1k]))
      omega
    · intro i hrdk hnotor
      let g := D3.gates.get i
      have hgi : D3.gates[i.val]? = some g := by rw [List.getElem?_eq_getElem i.isLt]; rfl
      obtain ⟨hsp, htlen⟩ := splitAt D3.gates i.val g hgi
      have hcas := countFoldGenCascade 9 (fun h => rd h k.val)
        (D3.gates.take i.val) g (D3.gates.drop (i.val + 1)) s1
        (by rwa [← hsp])
        (fun h s hh _ hpref hP => by
          obtain ⟨hop, hgl⟩ := hD3fan h (by rwa [hsp])
          exact simpStep_dropConst 9 s h k.val hop hgl hP
            (by dsimp only [isConst]; rw [hpref k.val (by rw [hs1Len]; omega), hs1k]))
        hrdk
        (by
          have hsub : ∀ h ∈ D3.gates.take i.val, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2 :=
            fun h hh => hD3fan h (List.mem_of_mem_take hh)
          have hs1f : FanInTwo ⟨s1.2, 0⟩ := simpStep_fan 9 (envK, []) ⟨.not, [0]⟩ (fun _ h => by cases h)
          have hs1b : ∀ s ∈ s1.1, ∀ j, s = .inr j → j < 9 + s1.2.length :=
            (simpStep_sound 9 (envK, []) ⟨.not, [0]⟩ (List.replicate 9 false)
              (envK.map (evalV (List.replicate 9 false)))
              (by simp) (Or.inr (Or.inr rfl)) (by simp) (by simp) henvKBdd
              (fun j hj => by simp only [List.foldl_nil]; rw [List.getD_eq_getElem envK _ hj, List.getD_eq_getElem _ _ (by simp [hj])]; conv_rhs => rw [List.getElem_map])).1
          have hsf := simpFold 9 (D3.gates.take i.val) s1 hsub hs1f hs1b
          have hlen' : ((D3.gates.take i.val).foldl (simpStep 9) s1).1.length = s1.1.length + (D3.gates.take i.val).length := hsf.2.1
          have hgetk : ((D3.gates.take i.val).foldl (simpStep 9) s1).1.getD k.val (.inl false) = .inl false := by
            rw [hsf.2.2.2.1 k.val (by rw [hs1Len]; omega), hs1k]
          rw [← hlen']
          obtain ⟨hop, hgl⟩ := hD3fan g (by rw [hsp]; exact List.mem_append_right _ List.mem_cons_self)
          exact simpStep_makesConst 9 _ g k.val hop hgl hrdk hnotor hgetk)
      rw [← hsp, hs1Len, htlen] at hcas
      omega
  -- Step 6: Invoke hBoth!
  let uFin3 : Fin D3.gates.length := ⟨u2 - 11, by omega⟩
  let i0Fin3 : Fin D3.gates.length := ⟨i0, by omega⟩
  let i1Fin3 : Fin D3.gates.length := ⟨i1, by omega⟩
  have huFin3Val : 11 + uFin3.val = u2 := by dsimp only [uFin3]; omega
  have huNeI0 : uFin3 ≠ i0Fin3 := fun h => by
    have hv := congrArg Fin.val h; dsimp only [uFin3, i0Fin3] at hv
    have h1 : 11 + i0 = u2 := by omega
    rw [h1, he0Off.1] at hD3g0True; cases hD3g0True
  have hi0NeI1 : i0Fin3 ≠ i1Fin3 := fun h => hiEq (congrArg Fin.val h)
  apply hBoth D3 uFin3 i0Fin3 i1Fin3
    ⟨hD3fan, hD3len, by dsimp only [uFin3]; omega, huNeI0, hi0NeI1, hi0Lt16⟩
  · -- Unique readers of 0 and 10 in D3
    intro j
    change (rd (D3.gates.get j) 0 = true ↔ j = i0Fin3) ∧ (rd (D3.gates.get j) 10 = true ↔ j = i1Fin3)
    have hj17 : j.val < 17 := by have := j.isLt; omega
    have h3g := hD3get j.val hj17
    rw [List.getElem?_eq_getElem j.isLt] at h3g
    have hgeq : D3.gates.get j = (if j.val = i0 then ⟨.or, [0, y0]⟩ else if j.val = i1 then ⟨.and, [10, y1]⟩ else D2.gates[j.val]'(by change j.val < D2.size; omega)) :=
      Option.some.inj h3g
    have heqI0 : (j = i0Fin3) ↔ (j.val = i0) := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    have heqI1 : (j = i1Fin3) ↔ (j.val = i1) := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    rw [heqI0, heqI1]
    by_cases hj0 : j.val = i0
    · rw [hgeq]; simp only [hj0, ↓reduceIte]
      constructor
      · simp [rd_or]
      · simp [rd_or, hiEq, hy0Ne10.symm]
    · by_cases hj1 : j.val = i1
      · rw [hgeq]; simp only [hj0, ↓reduceIte]; simp only [hj1, ↓reduceIte]
        constructor
        · simp [rd_and, Ne.symm hiEq, hy1Ne0.symm]
        · simp [rd_and]
      · rw [hgeq]; simp only [hj0, hj1, ↓reduceIte]
        have hCj : C.gates[j.val]? = some (D2.gates[j.val]'(by change j.val < D2.size; omega)) := by
          dsimp only [C]; rw [List.getElem?_append_left (by change j.val < D2.size; omega),
            List.getElem?_eq_getElem (by change j.val < D2.size; omega)]
        constructor
        · constructor
          · intro h0
            rcases huniq j.val _ hCj (by simp [h0]) with h | h <;> contradiction
          · intro h; contradiction
        · constructor
          · intro h10
            rcases huniq j.val _ hCj (by simp [h10]) with h | h <;> contradiction
          · intro h; contradiction
  · refine ⟨y0, hy0Lt, hy0Ne0, ?_⟩
    have h := hD3get i0 hi017
    rw [List.getElem?_eq_getElem i0Fin3.isLt] at h
    simp only [↓reduceIte] at h
    exact Option.some.inj h
  · refine ⟨y1, hy1Lt, hy1Ne10, ?_⟩
    have h := hD3get i1 hi117
    rw [List.getElem?_eq_getElem i1Fin3.isLt] at h
    simp only [Ne.symm hiEq, ↓reduceIte] at h
    exact Option.some.inj h
  · exact hDegCasc
  · intro c
    obtain ⟨y, h1, h2⟩ := hIncomp2 c
    refine ⟨y, ?_, ?_⟩
    · change (D3.wires (seed0 y)).getD (11 + uFin3.val) false = c
      rw [hD3wires y, huFin3Val]; exact h1
    · change (D3.wires (seed0 y)).getD 27 false = !c
      rw [hD3wires y, ← hv2eq27]; exact h2
  · intro y
    change ((D3.wires (seed0 y)).getD (11 + uFin3.val) false || (D3.wires (seed0 y)).getD 27 false) = fList y
    rw [hD3wires y, huFin3Val, ← hv2eq27, pc10 y]
    exact hCov2 y

