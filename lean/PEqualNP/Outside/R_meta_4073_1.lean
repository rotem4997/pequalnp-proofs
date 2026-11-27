import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4073_1
    (small : ¬ HasCircuitSize 10 (fun x =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (onlyInputNot : ∀ (C : Circuit) (u : ℕ), FanInTwo C → C.size = 17 → 11 ≤ u → u < 27 →
      (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
      let w := fun (r : ℕ) (i : ℕ) =>
        (C.wires (List.ofFn (fun j : Fin 10 => r.testBit j.val) ++ [!(r.testBit 0)])).getD i false
      (∃ r ∈ ([6,12,24,66,132,160,264,288,320,528,576,640,3,13,17,33,133,265,321,577,641] : List ℕ),
        (w r u && w r 27) = false) ∨
      (∃ r ∈ ([50,104,116,138,200,208,276,402,548,554,770,772,69,201,385,521,773] : List ℕ),
        (w r u && w r 27) = true))
    (extraNot : ∀ (C : Circuit) (u : ℕ), FanInTwo C → C.size = 17 → 11 ≤ u → u < 27 →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      ¬ (∀ x : Fin 10 → Bool,
        let w := (C.wires (List.ofFn x ++ [!x 0])).getD
        (w u false && w 27 false) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))) :
    ∀ (C : Circuit) (a b : ℕ), FanInTwo C → C.size ≤ 17 →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      let w := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x ++ [!x 0])).getD i false
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      (∀ x, f x = true → w x a = true ∧ w x b = true) →
      ∃ x, f x = false ∧ w x a = true ∧ w x b = true := by
  intro C a b hC hsize f w hab hba hpos
  by_contra hneg
  have exactPair (x : Fin 10 → Bool) : (w x a && w x b) = f x := by
    cases hx : f x
    · cases hA : w x a <;> cases hB : w x b <;> try rfl
      exact (hneg ⟨x, hx, hA, hB⟩).elim
    · obtain ⟨hA, hB⟩ := hpos x hx
      simp [hA, hB]
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have lengthRun (gs : List Gate) (ws : List Bool) :
      (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).length = _
      rw [ih]
      simp [step]
      omega
  have retain (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl step ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).getD i false = ws.getD i false
      rw [ih _ (by simpa [step] using Nat.lt_succ_of_lt hi)]
      exact List.getD_append _ _ _ _ hi
  have bound (i : ℕ) (h : ∀ x, f x = true → w x i = true) : 11 ≤ i ∧ i < 11 + C.size := by
    let x := fun j : Fin 10 => (3 : ℕ).testBit j.val
    let y := fun j : Fin 10 => (640 : ℕ).testBit j.val
    have hx : w x i = true := h x (by decide)
    have hy : w y i = true := h y (by decide)
    have len (z : Fin 10 → Bool) : (List.ofFn z ++ [!z 0]).length = 11 := by simp
    have hlo : 11 ≤ i := by
      by_contra! hi
      have readX := retain C.gates (List.ofFn x ++ [!x 0]) i (by rwa [len])
      have readY := retain C.gates (List.ofFn y ++ [!y 0]) i (by rwa [len])
      change _ = (_ : List Bool).getD i false at readX readY
      change (C.gates.foldl step _).getD i false = true at hx hy
      rw [readX] at hx
      rw [readY] at hy
      have incompatible : ∀ j : Fin 11,
          ¬ ((List.ofFn x ++ [!x 0]).getD j false = true ∧
             (List.ofFn y ++ [!y 0]).getD j false = true) := by decide
      exact incompatible ⟨i, hi⟩ ⟨hx, hy⟩
    refine ⟨hlo, ?_⟩
    by_contra! hi
    change (C.gates.foldl step _).getD i false = true at hx
    rw [List.getD_eq_default _ _ (by rw [lengthRun, len]; exact hi)] at hx
    exact Bool.false_ne_true hx
  have ha := bound a (fun x hx => (hpos x hx).1)
  have hb := bound b (fun x hx => (hpos x hx).2)
  have hab' : a ≠ b := by
    rintro rfl
    obtain ⟨x, h₁, h₂⟩ := hab
    rw [h₁] at h₂
    contradiction
  let u := min a b
  let v := max a b
  have huv : u < v := by
    rcases lt_or_gt_of_ne hab' with h | h
    · simpa [u, v, min_eq_left h.le, max_eq_right h.le] using h
    · simpa [u, v, min_eq_right h.le, max_eq_left h.le] using h
  have hu : 11 ≤ u := le_min ha.1 hb.1
  have hv : v < 11 + C.size := max_lt ha.2 hb.2
  have evalPair (x : Fin 10 → Bool) : (w x u && w x v) = f x := by
    rcases le_total a b with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using exactPair x
    · simpa [u, v, min_eq_right h, max_eq_left h, Bool.and_comm] using exactPair x
  have last : v = 27 := by
    by_contra hv'
    have hvlt : v < 27 := by omega
    let gs := C.gates.take (v - 10)
    have hgs : gs.length = v - 10 := by
      have hz : v - 10 ≤ C.size := by omega
      change v - 10 ≤ C.gates.length at hz
      simp [gs, List.length_take, Nat.min_eq_left hz]
    let front : Gate := ⟨GateOp.not, [0]⟩
    let final : Gate := ⟨GateOp.and, [u, v]⟩
    let D : Circuit := ⟨front :: (gs ++ [final]), 11 + gs.length⟩
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ front :: (gs ++ [final]) at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [front]
      rcases List.mem_append.mp hg with hg | hg
      · exact hC g (List.mem_of_mem_take hg)
      · obtain rfl := List.mem_singleton.mp hg
        simp [final]
    have short : D.size ≤ 18 := by
      change (front :: (gs ++ [final])).length ≤ 18
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    refine small ⟨D, legal, short, ?_⟩
    intro x
    let xs := List.ofFn x ++ [!x 0]
    let ws := gs.foldl step xs
    have plen : ws.length = 11 + gs.length := by simp [ws, xs, lengthRun]
    have prep : step (List.ofFn x) front = xs := by
      have first : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
      change List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]] = xs
      rw [first]
      rfl
    have result (i : ℕ) (h : i ≤ v) : ws.getD i false = w x i := by
      have hi : i < ws.length := by omega
      have split : C.gates = gs ++ C.gates.drop (v - 10) := (List.take_append_drop _ _).symm
      change ws.getD i false = (C.gates.foldl step xs).getD i false
      rw [split, List.foldl_append]
      exact (retain _ _ _ hi).symm
    change (((gs ++ [final]).foldl step (step (List.ofFn x) front)).getD (11 + gs.length) false) = f x
    rw [prep, List.foldl_append]
    change (step ws final).getD (11 + gs.length) false = f x
    rw [← plen]
    have atEnd : (step ws final).getD ws.length false = (ws.getD u false && ws.getD v false) := by
      change (ws ++ [GateOp.and.eval [ws.getD u false, ws.getD v false]]).getD ws.length false = _
      rw [List.getD_append_right _ _ _ _ le_rfl]
      simp only [Nat.sub_self]
      cases (ws.getD u false) <;> cases (ws.getD v false) <;> rfl
    rw [atEnd, result _ huv.le, result _ le_rfl]
    exact evalPair x
  have size17 : C.size = 17 := by omega
  have hu' : u < 27 := by omega
  have eval27 (x : Fin 10 → Bool) : (w x u && w x 27) = f x := by simpa [last] using evalPair x
  by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
  · exact extraNot C u hC size17 hu hu' hnot eval27
  have hmono : ∀ g ∈ C.gates, g.op ≠ GateOp.not := fun g hg he => hnot ⟨g, hg, he⟩
  rcases onlyInputNot C u hC size17 hu hu' hmono with ⟨r, hr, hw⟩ | ⟨r, hr, hw⟩
  · have good : ∀ r : ℕ, r ∈ ([6,12,24,66,132,160,264,288,320,528,576,640,3,13,17,33,133,265,321,577,641] : List ℕ) →
        f (fun j => r.testBit j.val) = true := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have bad := (eval27 (fun j => r.testBit j.val)).trans (good r hr)
    change (w (fun j => r.testBit j.val) u && w (fun j => r.testBit j.val) 27) = false at hw
    rw [hw] at bad
    contradiction
  · have good : ∀ r : ℕ, r ∈ ([50,104,116,138,200,208,276,402,548,554,770,772,69,201,385,521,773] : List ℕ) →
        f (fun j => r.testBit j.val) = false := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have bad := (eval27 (fun j => r.testBit j.val)).trans (good r hr)
    change (w (fun j => r.testBit j.val) u && w (fun j => r.testBit j.val) 27) = true at hw
    rw [hw] at bad
    contradiction
