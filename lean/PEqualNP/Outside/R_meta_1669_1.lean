import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1669_1
    (h_and : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (pins : List (Fin 11)),
      PEqualNP.MetaComplexity.FanInTwo D → pins.length ≤ 2 →
      (∀ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 3]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun i => w.getD i.val false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 14 ≤ D.size)
    (h_or : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (pins : List (Fin 11)),
      PEqualNP.MetaComplexity.FanInTwo D → pins.length ≤ 2 →
      (∀ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 3]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (pins.map fun i => w.getD i.val false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 14 ≤ D.size)
    (h_not : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (pins : List (Fin 11)),
      PEqualNP.MetaComplexity.FanInTwo D → pins.length ≤ 2 →
      (∀ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 3]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (pins.map fun i => w.getD i.val false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 14 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C basis first computes
  obtain ⟨gs,out⟩ := C
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have kept (l : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (l.foldl step w).getD i false = w.getD i false := by
    induction l generalizing w with
    | nil => rfl
    | cons g l ih =>
      change (l.foldl step (step w g)).getD i false = _
      rw [ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  cases gs with
  | nil =>
    have bad := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at bad
    rw [List.getD_eq_default _ _ (by simp)] at bad
    contradiction
  | cons a tail =>
    have wire (x : Fin 9 → Bool) :
        step (List.ofFn x) a = List.ofFn x ++ [x 0 && x 3] := by
      have h := first x
      change (tail.foldl step (step (List.ofFn x) a)).getD 9 false = _ at h
      rw [kept tail _ 9 (by simp [step])] at h
      simp only [step, List.getD_append_right _ _ _ _ (by simp : (List.ofFn x).length ≤ 9),
        List.length_ofFn, Nat.sub_self] at h
      change _ ++ [_] = _ ++ [_]
      have val : a.op.eval (a.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 3) := h
      rw [val]
    cases tail with
    | nil =>
      have impossible : ∀ k : Fin 11, ¬ (∀ x : Fin 9 → Bool,
          (List.ofFn x ++ [x 0 && x 3]).getD k.val false =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) := by
        intro k eq
        let u : Fin 9 → Bool := ![false,true,true,false,false,false,false,false,false]
        let v : Fin 9 → Bool := ![false,false,false,false,false,true,false,true,false]
        have hu : (List.ofFn u ++ [u 0 && u 3]).getD k.val false = true := eq u
        have hv : (List.ofFn v ++ [v 0 && v 3]).getD k.val false = true := eq v
        have disjoint : ∀ j : Fin 11,
            ((List.ofFn u ++ [u 0 && u 3]).getD j.val false &&
            (List.ofFn v ++ [v 0 && v 3]).getD j.val false) = false := by
          dsimp only [u,v]
          decide
        have bad := disjoint k
        rw [hu,hv] at bad
        contradiction
      let k : Fin 11 := ⟨min out 10, by omega⟩
      exfalso
      apply impossible k
      intro x
      have h := congrFun computes x
      change (step (List.ofFn x) a).getD out false = _ at h
      rw [wire] at h
      by_cases small : out ≤ 10
      · simpa [k,Nat.min_eq_left small] using h
      · rw [List.getD_eq_default _ _ (by simp; omega)] at h
        simpa [k, Nat.min_eq_right (by omega : 10 ≤ out), List.getD_eq_default] using h
    | cons b rest =>
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨rest,out⟩
      have hb := basis b (by simp)
      have hd : PEqualNP.MetaComplexity.FanInTwo D := by
        intro g hg
        exact basis g (by simp [D] at hg ⊢; tauto)
      let clip (i : ℕ) : Fin 11 := ⟨min i 10, by omega⟩
      let pins := b.inputs.map clip
      have hp : pins.length ≤ 2 := by simpa [pins] using hb.2
      have eval (x : Fin 9 → Bool) :
          let w := List.ofFn x ++ [x 0 && x 3]
          D.eval (w ++ [b.op.eval (pins.map fun i => w.getD i.val false)]) =
            ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
        let w := List.ofFn x ++ [x 0 && x 3]
        have norm (i : ℕ) : w.getD (clip i).val false = w.getD i false := by
          by_cases h : i ≤ 10
          · simp [clip, Nat.min_eq_left h]
          · rw [List.getD_eq_default _ _ (by simp [w,clip,Nat.min_eq_right (by omega : 10 ≤ i)]),
                List.getD_eq_default _ _ (by simp [w]; omega)]
        have eq : pins.map (fun i => w.getD i.val false) =
            b.inputs.map (fun i => w.getD i false) := by
          simp only [pins, List.map_map, Function.comp_def, norm]
        have h := congrFun computes x
        change (rest.foldl step (step (step (List.ofFn x) a) b)).getD out false = _ at h
        rw [wire] at h
        change D.eval (w ++ [b.op.eval (pins.map fun i => w.getD i.val false)]) = _
        rw [eq]
        exact h
      have ops : b.op = .and ∨ b.op = .or ∨ b.op = .not := by simpa using hb.1
      have bound : 14 ≤ D.size := by
        rcases ops with e | e | e
        · exact h_and D pins hd hp (by simpa only [e] using eval)
        · exact h_or D pins hd hp (by simpa only [e] using eval)
        · exact h_not D pins hd hp (by simpa only [e] using eval)
      change 14 ≤ rest.length at bound
      change 16 ≤ (a :: b :: rest).length
      simp only [List.length_cons]
      omega
