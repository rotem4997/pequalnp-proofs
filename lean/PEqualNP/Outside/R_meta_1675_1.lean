import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Replacing the extra signal by any raw input gives the settled fourteen-gate case.
-- All ten sources of a putative suffix are essential. Its live minimum therefore has
-- at most five repeated reads and unary negations combined.
theorem PEqualNP.Outside.R_meta_1675_1
    (duplicate : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → ∀ p : Fin 9, ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (compact : ∀ C : Circuit, FanInTwo C →
      (∀ p : Fin 10, ∃ x y : Fin 10 → Bool, (∀ j, j ≠ p → x j = y j) ∧ circuitFun 10 C x ≠ circuitFun 10 C y) →
      ∃ D : Circuit, FanInTwo D ∧ circuitFun 10 D = circuitFun 10 C ∧ D.size ≤ C.size ∧
        (D.output ≤ 10+D.size ∧ (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 10+D.size)) ∧ (∀ i < 10+D.size, i ∈ (D.output :: D.gates.flatMap Gate.inputs)) ∧ (9 + (D.gates.filter (fun g => g.op.eval [false] && !(g.op.eval [true]))).length + (∑ i ∈ Finset.range (10+D.size), ((D.output :: D.gates.flatMap Gate.inputs).count i - 1)) ≤ D.size))
    (once : let target := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ D : Circuit, FanInTwo D → D.size = 14 →
      (D.output ≤ 10+D.size ∧ (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 10+D.size)) →
      (∀ i < 10+D.size, i ∈ (D.output :: D.gates.flatMap Gate.inputs)) →
      (9 + (D.gates.filter (fun g => g.op.eval [false] && !(g.op.eval [true]))).length + (∑ i ∈ Finset.range (10+D.size), ((D.output :: D.gates.flatMap Gate.inputs).count i - 1)) ≤ D.size) →
      (D.output :: D.gates.flatMap Gate.inputs).count 9 = 1 →
      (∀ p : Fin 9, ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p]) ≠ target x) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) ≠ target x)
    (reused : let target := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ D : Circuit, FanInTwo D → D.size = 14 →
      (D.output ≤ 10+D.size ∧ (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 10+D.size)) →
      (∀ i < 10+D.size, i ∈ (D.output :: D.gates.flatMap Gate.inputs)) →
      (9 + (D.gates.filter (fun g => g.op.eval [false] && !(g.op.eval [true]))).length + (∑ i ∈ Finset.range (10+D.size), ((D.output :: D.gates.flatMap Gate.inputs).count i - 1)) ≤ D.size) →
      2 ≤ (D.output :: D.gates.flatMap Gate.inputs).count 9 →
      (∀ p : Fin 9, ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p]) ≠ target x) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) ≠ target x)
    : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro circuit fan first correct
  by_contra insufficient
  have sizeLimit : circuit.size ≤ 15 := by omega
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
    let ext (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.snoc x b
    have toList (x : Fin 9 → Bool) (b : Bool) : List.ofFn (ext x b) = List.ofFn x ++ [b] := by
      rw [List.ofFn_succ']
      simp [ext,List.concat_eq_append]
      change (Fin.snoc x b : Fin 10 → Bool) (Fin.last 9) = b
      simp only [Fin.snoc_last]
    have correctC (x : Fin 9 → Bool) : circuitFun 10 C (ext x (x 0 || x 3)) = target x := by
      change C.eval (List.ofFn (ext x _)) = _
      rw [toList]
      exact computes x
    let bits (w : ℕ) (i : Fin 9) := w.testBit i.val
    let low : Fin 9 → ℕ := ![10,1,2,5,1,1,2,4,8]
    let high : Fin 9 → ℕ := ![11,3,6,13,17,33,66,132,264]
    have pairs : ∀ p : Fin 9, let x := bits (low p); let y := bits (high p)
        (∀ j : Fin 10, j ≠ p.castSucc → ext x (x 0 || x 3) j = ext y (y 0 || y 3) j) ∧
        target x ≠ target y := by decide
    have essential (p : Fin 10) : ∃ x y : Fin 10 → Bool, (∀ j, j ≠ p → x j = y j) ∧
        circuitFun 10 C x ≠ circuitFun 10 C y := by
      refine Fin.lastCases ?_ (fun i => ?_) p
      · obtain ⟨x,hx⟩ := duplicate C ok small 0
        refine ⟨ext x (x 0),ext x (x 0 || x 3),?_,?_⟩
        · intro j
          refine Fin.lastCases (by simp) (fun k _ => ?_) j
          simp [ext]
        · rw [correctC]
          change C.eval (List.ofFn (ext x (x 0))) ≠ _
          rwa [toList]
      · obtain ⟨agree,diff⟩ := pairs i
        exact ⟨_,_,agree,fun h => diff ((correctC _).symm.trans (h.trans (correctC _)))⟩
    obtain ⟨D,okD,equal,sizeD,clipped,live,budget⟩ := compact C ok essential
    have smallD := sizeD.trans small
    have actual (x : Fin 9 → Bool) : D.eval (seed x) = target x := by
      have h := (congrFun equal (ext x (x 0 || x 3))).trans (correctC x)
      change D.eval (List.ofFn (ext x (x 0 || x 3))) = target x at h
      rwa [toList] at h
    -- A shorter suffix would still fit the raw budget after explicitly paying for the OR.
    have exactSize : D.size = 14 := by
      by_contra neq
      have shorter : D.size+1 ≤ 14 := by omega
      let up (i : ℕ) := if i<9 then i else i+1
      let mapped (g : Gate) : Gate := ⟨g.op,g.inputs.map up⟩
      let anchor : Gate := ⟨.or,[0,3]⟩
      let E : Circuit := ⟨anchor :: D.gates.map mapped,up D.output⟩
      have legalE : FanInTwo E := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl|hg
        · simp [anchor]
        · obtain ⟨h,m,rfl⟩ := List.mem_map.mp hg
          simpa [mapped] using okD h m
      have sizeE : E.size ≤ 14 := by
        change (anchor :: D.gates.map mapped).length ≤ 14
        change D.gates.length + 1 ≤ 14 at shorter
        simpa only [List.length_cons,List.length_map] using shorter
      obtain ⟨x,bad⟩ := duplicate E legalE sizeE 0
      let w := List.ofFn x
      let u := w ++ [x 0]
      have read (tail : List Bool) (i : ℕ) :
          (u ++ tail).getD (up i) false = (w ++ tail).getD i false := by
        by_cases valid : i<9
        · simp only [up,ite_eq_left valid]
          rw [List.getD_append u tail false i (by simp [u,w]; omega),
            List.getD_append w tail false i (by simpa [w] using valid)]
          exact List.getD_append w [x 0] false i (by simpa [w] using valid)
        · simp only [up,ite_eq_right valid]
          rw [List.getD_append_right u tail false (i+1) (by simp [u,w]; omega),
            List.getD_append_right w tail false i (by simp [w]; omega)]
          simp [u,w]
      have track (gs : List Gate) (tail : List Bool) : ∃ t,
          run (gs.map mapped) (u ++ tail) = u ++ t ∧ run gs (w ++ tail) = w ++ t := by
        induction gs generalizing tail with
        | nil => exact ⟨tail,rfl,rfl⟩
        | cons h gs ih =>
          let b := h.op.eval (h.inputs.map fun i => (w ++ tail).getD i false)
          have vals : ((mapped h).inputs.map fun i => (u ++ tail).getD i false) =
              h.inputs.map (fun i => (w ++ tail).getD i false) := by
            simp only [mapped,List.map_map]
            apply List.map_congr_left
            intro i _
            exact read tail i
          simp only [List.map_cons,run,List.foldl_cons,step,vals,List.append_assoc]
          exact ih (tail ++ [b])
      have ax : anchor.op.eval (anchor.inputs.map fun i => u.getD i false) = (x 0 || x 3) := by
        change (u.getD 0 false || (u.getD 3 false || false)) = (x 0 || x 3)
        simp [u,w,List.getD_eq_getElem?_getD]
      obtain ⟨t,he,hd⟩ := track D.gates [x 0 || x 3]
      apply bad
      change (run (D.gates.map mapped) (u ++ [anchor.op.eval (anchor.inputs.map fun i => u.getD i false)])).getD (up D.output) false = target x
      have ad := actual x
      change (run D.gates (w ++ [x 0 || x 3])).getD D.output false = target x at ad
      rwa [ax,he,read,← hd]
    have copies := duplicate D okD smallD
    let pins := D.output :: D.gates.flatMap Gate.inputs
    have pos : 0 < pins.count 9 := List.count_pos_iff.mpr (live 9 (by omega))
    by_cases single : pins.count 9 = 1
    · obtain ⟨x,hx⟩ := once D okD exactSize clipped live budget single copies
      exact hx (actual x)
    · obtain ⟨x,hx⟩ := reused D okD exactSize clipped live budget (show 2 ≤ pins.count 9 by omega) copies
      exact hx (actual x)
