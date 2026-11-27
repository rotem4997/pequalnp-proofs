import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each of the three degree-two vertices has an isomorphic deletion graph.
-- With vertex four off, the tail computes its eight-input edge function.
-- With it on, the same tail must add the disjunction of its two neighbors.
theorem PEqualNP.Outside.R_meta_1675_403
    (readBound : ∀ (D : Circuit), FanInTwo D → D.size ≤ 15 → circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
    ∀ v ∈ ([4,6,7] : List ℕ), D.gates.countP (fun g : Gate => g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2)
    (cofactors : let H := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
    let w := fun (x : Fin 8 → Bool) (b : Bool) => List.ofFn ((4 : Fin 9).insertNth b x) ++ [x 0 || x 3]
    ∀ (D : Circuit), FanInTwo D → D.size ≤ 14 →
      (∀ v ∈ ([4,6,7] : List ℕ), D.gates.countP (fun g : Gate => g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2) →
      (∀ x, D.eval (w x false) = H x) → ∃ x, D.eval (w x true) ≠ (H x || x 0 || x 3)) : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro circuit fan first correct
  by_contra insufficient
  have sizeLimit : circuit.size ≤ 15 := by omega
  have allReads := readBound circuit fan sizeLimit correct
  let target := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 3]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have extend (gs : List Gate) (w : List Bool) :
      ∃ extra, run gs w = w ++ extra ∧ extra.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g rest ih =>
      obtain ⟨extra, heq, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
      change run rest (step w g) = _
      rw [heq]
      simp [step, List.append_assoc]
  obtain ⟨gs, out⟩ := circuit
  cases gs with
  | nil =>
    have h := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ false (by simp)] at h
    contradiction
  | cons g rest =>
    have firstValue (x : Fin 9 → Bool) :
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 3) := by
      let w := List.ofFn x
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨extra, heq, _⟩ := extend rest (w ++ [value])
      have h := first x
      change (run rest (w ++ [value])).getD 9 false = _ at h
      rw [heq, List.getD_append _ _ false 9 (by simp [w]),
        List.getD_append_right w [value] false 9 (by simp [w])] at h
      simpa [value, w] using h
    have computes (x : Fin 9 → Bool) : (run rest (seed x)).getD out false = target x := by
      have h := congrFun correct x
      change (run rest (List.ofFn x ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD out false = target x at h
      rw [firstValue] at h
      exact h
    let C : Circuit := ⟨rest,out⟩
    have ok : FanInTwo C := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    have small : C.size ≤ 14 := by
      change (g :: rest).length ≤ 15 at sizeLimit
      change rest.length ≤ 14
      simp only [List.length_cons] at sizeLimit
      omega
    have tailReads (v : ℕ) (hv : v ∈ ([4,6,7] : List ℕ)) :
        C.gates.countP (fun g : Gate => g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2 := by
      have bound := allReads v hv
      change (g :: rest).countP (fun g : Gate => g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2 at bound
      change rest.countP _ ≤ 2
      simp only [List.countP_cons] at bound
      split at bound <;> omega
    let H := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
    let w (x : Fin 8 → Bool) (b : Bool) := List.ofFn ((4 : Fin 9).insertNth b x) ++ [x 0 || x 3]
    have runAt (x : Fin 8 → Bool) (b : Bool) : C.eval (w x b) = target ((4 : Fin 9).insertNth b x) := by
      exact computes ((4 : Fin 9).insertNth b x)
    have off (x : Fin 8 → Bool) : C.eval (w x false) = H x := by
      rw [runAt]
      change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && false || false && x 0 ||
        x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
        x 5 && x 7 || x 7 && x 4) = H x
      simp [H]
    obtain ⟨x, bad⟩ := cofactors C ok small tailReads off
    apply bad
    rw [runAt]
    change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && true || true && x 0 ||
      x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
      x 5 && x 7 || x 7 && x 4) = (H x || x 0 || x 3)
    simp only [H, Bool.and_true, Bool.true_and]
    ac_rfl
