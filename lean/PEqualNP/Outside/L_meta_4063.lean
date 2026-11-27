import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4063

open PEqualNP.CircuitLowerBounds

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem gateVal_mono (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ)
    (x y : Fin 11 → Bool) (hxy : ∀ i, x i ≤ y i) :
    PEqualNP.EdgeOwnership.gateVal 11 C j x ≤ PEqualNP.EdgeOwnership.gateVal 11 C j y := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact hxy _
  exact getD_le (fold_le C.gates hC _ _ h0) (11 + j)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem keyBool : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool, (b0 && b9) = false → (b0 && b10) = false → (b1 && b4) = false → (b1 && b8) = false → (b2 && b5) = false → (b2 && b10) = false → (b3 && b6) = false → (b3 && b7) = false → (b4 && b8) = false → (b4 && b10) = false → (b5 && b8) = false → (b5 && b9) = false → (b6 && b7) = false → (b6 && b10) = false → (b7 && b9) = false → (b8 && b9) = false →
    ∃ m ∈ ([15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] : List ℕ), ∀ i : Fin 11, (![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] : Fin 11 → Bool) i ≤ m.testBit i := by
  decide

end PEqualNP.Outside.L_meta_4063

open PEqualNP.Outside.L_meta_4063 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_4063 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ), PEqualNP.EdgeOwnership.AndOrOnly x3 → (∀ x6 ∈ x2, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false) → PEqualNP.TopForm.BelowF x1 x3 x4 := by
  intro G L C j hC hL x hx
  by_contra hF
  have hF' : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false := by
    simpa using hF
  have e : ∀ a b : Fin 11, G.Adj a b → (x a && x b) = false := by
    intro a b hab
    cases ha : x a <;> cases hb : x b
    all_goals first
      | rfl
      | (exfalso
         simp only [PEqualNP.MetaComplexity.NestedCover.graphFun] at hF'
         simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists, not_and] at hF'
         exact absurd hb (by simp [hF'.2 a b hab ha]))
  obtain ⟨m, hm, hle⟩ := keyBool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
    (e 0 9 (by decide))
    (e 0 10 (by decide))
    (e 1 4 (by decide))
    (e 1 8 (by decide))
    (e 2 5 (by decide))
    (e 2 10 (by decide))
    (e 3 6 (by decide))
    (e 3 7 (by decide))
    (e 4 8 (by decide))
    (e 4 10 (by decide))
    (e 5 8 (by decide))
    (e 5 9 (by decide))
    (e 6 7 (by decide))
    (e 6 10 (by decide))
    (e 7 9 (by decide))
    (e 8 9 (by decide))
  have hle' : ∀ i : Fin 11, x i ≤ (fun i : Fin 11 => m.testBit i) i := by
    intro i
    have h1 := hle i
    fin_cases i <;> exact h1
  have h2 := gateVal_mono C hC j _ _ hle'
  rw [hL m hm, hx] at h2
  exact absurd h2 (by decide)
