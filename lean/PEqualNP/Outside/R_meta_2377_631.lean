import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Bypassing an OR by a unary AND retains the wire numbering.
-- Each pin has an incidence edge on which it is false, its sibling is true, and bypass loses the output.
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_2377_631
    (prune :
      let cost := fun D : Circuit =>
      ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.or} : Set _).ncard
      let bypass := fun (D : Circuit) (j w : ℕ) =>
      ({D with gates := D.gates.set j ⟨GateOp.and, [w]⟩} : Circuit)
      ∀ (n : ℕ) (D : Circuit) (j : Fin D.gates.length) (w : ℕ),
        Monotone2 D → (D.gates.get j).op = GateOp.or → w ∈ (D.gates.get j).inputs →
        let B := bypass D j.val w
        Monotone2 B ∧ cost B < cost D ∧
        (∀ x : Fin n → Bool, B.eval (List.ofFn x) = true → D.eval (List.ofFn x) = true) ∧
        (∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
          B.eval (List.ofFn x) = true → B.eval (List.ofFn y) = true))
    (bound :
      let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧
      (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let cost := fun D : Circuit =>
      ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.or} : Set _).ncard
      let bypass := fun (D : Circuit) (j w : ℕ) =>
      ({D with gates := D.gates.set j ⟨GateOp.and, [w]⟩} : Circuit)
      let computes := fun D : Circuit => ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true
      let row := fun (u v z : Fin 42) => decide (z = u ∨ z = v)
      let critical := fun D : Circuit => ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
      ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
        (bypass D j.val w).eval (List.ofFn (row u v)) = false
        ∧ (let pre := ({D with gates := D.gates.take j.val} : Circuit).wires (List.ofFn (row u v))
           pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true)
      ∀ C, Monotone2 C → computes C → critical C → 104 ≤ cost C) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  classical
  intro C hm hf
  let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧
      (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let cost := fun D : Circuit =>
      ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.or} : Set _).ncard
  let bypass := fun (D : Circuit) (j w : ℕ) =>
      ({D with gates := D.gates.set j ⟨GateOp.and, [w]⟩} : Circuit)
  let computes := fun D : Circuit => ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true
  let row := fun (u v z : Fin 42) => decide (z = u ∨ z = v)
  let critical := fun D : Circuit => ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
      ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
        (bypass D j.val w).eval (List.ofFn (row u v)) = false
  have key : ∀ (u v : Fin 42), ((u.val, v.val) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ))) ↔ (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) := by decide +kernel
  have hfm : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧ x u = true ∧ x v = true := by
    intro x
    have hiff := hf x
    constructor
    · intro he
      rcases (hiff.mp he) with ⟨u, v, huv, hxu, hxv⟩
      exact ⟨u, v, (key u v).mp huv, hxu, hxv⟩
    · intro hm
      rcases hm with ⟨u, v, hmod, hxu, hxv⟩
      exact (hiff.mpr ⟨u, v, (key u v).mpr hmod, hxu, hxv⟩)
  have local_witness (D : Circuit) (j : Fin D.gates.length) (pin : ℕ)
      (op : (D.gates.get j).op = GateOp.or) (member : pin ∈ (D.gates.get j).inputs)
      (x : List Bool)
      (changed : ({D with gates := D.gates.set j.val ⟨GateOp.and,[pin]⟩} : Circuit).eval x ≠ D.eval x) :
      let pre := ({D with gates := D.gates.take j.val} : Circuit).wires x
      pre.getD pin false = false ∧ ∃ w ∈ (D.gates.get j).inputs, pre.getD w false = true := by
    let pre := ({D with gates := D.gates.take j.val} : Circuit).wires x
    let g := D.gates.get j
    have split : D.gates.take j.val ++ g :: D.gates.drop (j.val+1) = D.gates := by
      simp [g,List.get_eq_getElem,List.getElem_cons_drop,List.take_append_drop]
    have different : pre.getD pin false ≠ g.op.eval (g.inputs.map fun i => pre.getD i false) := by
      intro eqv
      apply changed
      change ((D.gates.set j.val _).foldl _ x).getD _ _ = (D.gates.foldl _ x).getD _ _
      conv_rhs => rw [← split]
      rw [List.set_eq_take_append_cons_drop,if_pos j.isLt]
      let finish := fun b : Bool =>
        (({D with gates := D.gates.drop (j.val+1)} : Circuit).wires (pre ++ [b])).getD D.output false
      have head : GateOp.and.eval ([pin].map fun i => pre.getD i false) = pre.getD pin false := by
        change (pre.getD pin false && true) = pre.getD pin false
        exact Bool.and_true _
      simp only [List.foldl_append, List.foldl_cons]
      exact congrArg finish (head.trans eqv)
    have fires : pre.getD pin false = true → g.op.eval (g.inputs.map fun i => pre.getD i false) = true := by
      intro yes
      rw [show g.op = GateOp.or from op]
      exact List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨pin,member,yes⟩,rfl⟩
    have off : pre.getD pin false = false := by
      cases h : pre.getD pin false
      · rfl
      · exact False.elim (different (h.trans (fires h).symm))
    have on : g.op.eval (g.inputs.map fun i => pre.getD i false) = true := by
      cases h : g.op.eval (g.inputs.map fun i => pre.getD i false)
      · exact False.elim (different (off.trans h.symm))
      · rfl
    rw [show g.op = GateOp.or from op] at on
    obtain ⟨bit,hbit,bitEq⟩ := List.any_eq_true.mp on
    obtain ⟨w,mem,hw⟩ := List.mem_map.mp hbit
    exact ⟨off,w,mem,hw.trans bitEq⟩
  have lower : ∀ s, ∀ D : Circuit, cost D = s → Monotone2 D → computes D → 104 ≤ s := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro D hs mono calcD
      by_cases hcrit : critical D
      · rw [← hs]
        apply bound D mono calcD
        intro j op w mem
        obtain ⟨u,v,uv,lost⟩ := hcrit j op w mem
        have accepts := (calcD (row u v)).mpr
          ⟨u,v,uv,by simp [row],by simp [row]⟩
        have diff : (bypass D j.val w).eval (List.ofFn (row u v)) ≠ D.eval (List.ofFn (row u v)) := by
          rw [lost, accepts]
          decide
        exact ⟨u,v,uv,lost,local_witness D j w op mem _ diff⟩
      · change ¬ (∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
            ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
              (bypass D j.val w).eval (List.ofFn (row u v)) = false) at hcrit
        push_neg at hcrit
        obtain ⟨j, op, w, mem, preserve⟩ := hcrit
        obtain ⟨monB, small, below, increasing⟩ := prune 42 D j w mono op mem
        let B := bypass D j.val w
        have good : computes B := by
          intro x
          constructor
          · intro yes
            exact (calcD x).mp (below x yes)
          · rintro ⟨u,v,uv,xu,xv⟩
            have survives : B.eval (List.ofFn (row u v)) = true := by
              simpa [B] using preserve u v uv
            apply increasing (row u v) x _ survives
            intro i hi
            have hi' : i = u ∨ i = v := of_decide_eq_true hi
            rcases hi' with rfl | rfl
            · exact xu
            · exact xv
        have saved : cost B < cost D := small
        have lt : cost B < s := saved.trans_le hs.le
        exact (ih (cost B) lt B rfl monB good).trans (Nat.le_of_lt lt)
  exact lower (cost C) C rfl hm hfm
