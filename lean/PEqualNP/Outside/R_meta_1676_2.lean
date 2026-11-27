import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1676_2
    (monotoneRows : ∀ D : Circuit, Monotone2 D →
      (∀ r ∈ ([3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402] : List ℕ),
        let x : Fin 9 → Bool := fun i => r.testBit i.val
        D.eval (List.ofFn x ++ [x 0 || x 4]) = decide (r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ))) →
      15 ≤ D.size)
    (firstNot : ∀ P D : Circuit, Monotone2 P → FanInTwo D →
      (∀ x : Fin 9 → Bool,
        let w := P.wires (List.ofFn x ++ [x 0 || x 4])
        D.eval (w ++ [!(w.getD P.output false)]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ P.size + D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hC first correct
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have lengthOf (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  cases C with
  | mk gates out =>
    cases gates with
    | nil =>
      have h := first (fun _ => true)
      change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
      have hn : (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = false := by decide
      rw [hn] at h
      contradiction
    | cons g gs =>
      let D : Circuit := ⟨gs,out⟩
      have hh (x : Fin 9 → Bool) :
          step (List.ofFn x) g = List.ofFn x ++ [x 0 || x 4] := by
        have hv := first x
        change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at hv
        rw [keep] at hv
        · have hs (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
            simp [List.getD_eq_getElem?_getD]
          have hx := hs (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))
          rw [List.length_ofFn] at hx
          change (List.ofFn x ++ [_]).getD 9 false = _ at hv
          rw [hx] at hv
          simp only [step, hv]
        · simp [step]
      have hw (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
        have he := congrFun correct x
        change (gs.foldl step (step (List.ofFn x) g)).getD out false = _ at he
        rw [hh] at he
        exact he
      have split (ls : List Gate) :
          (∀ h ∈ ls, h.op ≠ GateOp.not) ∨
          ∃ pre h post, ls = pre ++ h :: post ∧ h.op = GateOp.not ∧ ∀ v ∈ pre, v.op ≠ GateOp.not := by
        induction ls with
        | nil => exact Or.inl (by simp)
        | cons z zs ih =>
          by_cases hz : z.op = GateOp.not
          · exact Or.inr ⟨[],z,zs,rfl,hz,by simp⟩
          rcases ih with ih | ⟨pre,h,post,rfl,hop,hpre⟩
          · exact Or.inl (by simpa [hz] using ih)
          · exact Or.inr ⟨z :: pre,h,post,rfl,hop,by simpa [hz] using hpre⟩
      have mono (ls : List Gate) (o : ℕ) (sub : ∀ v ∈ ls, v ∈ gs) (hn : ∀ v ∈ ls, v.op ≠ GateOp.not) :
          Monotone2 ⟨ls,o⟩ := by
        intro v hv
        obtain ⟨hops, hlen⟩ := hC v (List.mem_cons_of_mem _ (sub v hv))
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops ⊢
        exact ⟨hops.elim Or.inl (fun h => Or.inr (h.resolve_right (hn v hv))), hlen⟩
      rcases split gs with hn | ⟨pre,N,post,hgs,hop,hpre⟩
      · have hbound := monotoneRows D (mono gs out (fun _ h => h) hn) (by
          intro r hr
          dsimp only
          rw [hw]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        change 15 ≤ gs.length at hbound
        change 16 ≤ (g :: gs).length
        simp; omega
      · let P : Circuit := ⟨pre, N.inputs.headD (10 + pre.length)⟩
        let Q : Circuit := ⟨post, out⟩
        have hm : Monotone2 P := mono pre _ (by intro v hv; simp [hgs, hv]) hpre
        have hf : FanInTwo Q := by
          intro v hv
          change v ∈ post at hv
          exact hC v (by change v ∈ g :: gs; simp [hgs, hv])
        have hbound := firstNot P Q hm hf (by
          intro x
          dsimp only
          let raw := List.ofFn x ++ [x 0 || x 4]
          let w := pre.foldl step raw
          have hl : w.length = 10 + pre.length := by simp [w, raw, lengthOf]
          have hv : N.op.eval (N.inputs.map fun i => w.getD i false) = !(w.getD P.output false) := by
            rw [hop]
            change (!((N.inputs.map fun i => w.getD i false).headD false)) =
              !(w.getD (N.inputs.headD (10 + pre.length)) false)
            cases hi : N.inputs with
            | nil => simp [← hl, List.getD_eq_getElem?_getD]
            | cons i is => rfl
          have eqn := hw x
          change (gs.foldl step raw).getD out false = _ at eqn
          rw [hgs, List.foldl_append, List.foldl_cons] at eqn
          change (post.foldl step (w ++ [N.op.eval (N.inputs.map fun i => w.getD i false)])).getD out false = _ at eqn
          rw [hv] at eqn
          exact eqn)
        change 14 ≤ pre.length + post.length at hbound
        change 16 ≤ (g :: gs).length
        simp [hgs]; omega
