import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the specified first gate and expose the input and output of the sole NOT.
-- The two monotone circuits on either side have thirteen gates between them.
theorem PEqualNP.Outside.R_meta_2046_731
    (early : ∀ P Q : Circuit, Monotone2 P → Monotone2 Q →
      P.size + Q.size = 13 → P.size ≤ 6 →
      ∃ x : Fin 9 → Bool,
        let w := P.wires (List.ofFn x ++ [x 0 && x 2])
        Q.eval (w ++ [!(w.getD P.output false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (late : ∀ P Q : Circuit, Monotone2 P → Monotone2 Q →
      P.size + Q.size = 13 → Q.size ≤ 6 →
      ∃ x : Fin 9 → Bool,
        let w := P.wires (List.ofFn x ++ [x 0 && x 2])
        Q.eval (w ++ [!(w.getD P.output false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) := by
  intro C hC first sz count correct
  let isNot : Gate → Bool := fun g => GateOp.rec false false true (fun _ => false) false g.op
  change C.gates.countP isNot = 1 at count
  have isNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
    cases g with
    | mk op ins => cases op <;> simp [isNot]
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
          step (List.ofFn x) g = List.ofFn x ++ [x 0 && x 2] := by
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
      have hw (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 && x 2]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
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
      have firstNotFree : g.op ≠ GateOp.not := by
        intro hg
        let x : Fin 9 → Bool := fun _ => false
        have eqn := hh x
        have readFalse (i : ℕ) : (List.ofFn x).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          split <;> rfl
        have gateTrue : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = true := by
          rw [hg]
          cases h : g.inputs with
          | nil => rfl
          | cons i rest =>
            change (!( (List.ofFn x).getD i false)) = true
            rw [readFalse]; rfl
        change List.ofFn x ++ [_] = List.ofFn x ++ [false] at eqn
        have clash := List.append_cancel_left eqn
        rw [gateTrue] at clash
        cases clash
      have headCount : isNot g = false := by
        simpa using Bool.eq_false_iff.mpr (fun h => firstNotFree ((isNot_iff g).mp h))
      change (g :: gs).countP isNot = 1 at count
      simp [List.countP_cons, headCount] at count
      rcases split gs with hn | ⟨pre,N,post,hgs,hop,hpre⟩
      · have hz : gs.countP isNot = 0 := List.countP_eq_zero.mpr (by
          intro v hv h
          exact hn v hv ((isNot_iff v).mp h))
        omega
      · have hn : isNot N = true := (isNot_iff N).mpr hop
        rw [hgs, List.countP_append, List.countP_cons] at count
        simp [hn] at count
        have postZero : post.countP isNot = 0 := by omega
        have noNotPost := List.countP_eq_zero.mp postZero
        let P : Circuit := ⟨pre, N.inputs.headD (10 + pre.length)⟩
        let Q : Circuit := ⟨post, out⟩
        have hm : Monotone2 P := mono pre _ (by intro v hv; simp [hgs, hv]) hpre
        have hmQ : Monotone2 Q := mono post _ (by intro v hv; simp [hgs, hv])
          (by intro v hv h; exact noNotPost v hv ((isNot_iff v).mpr h))
        have total : P.size + Q.size = 13 := by
          change (g :: gs).length = 15 at sz
          change pre.length + post.length = 13
          simp [hgs] at sz
          omega
        obtain ⟨x, mismatch⟩ := (by
          by_cases low : P.size ≤ 6
          · exact early P Q hm hmQ total low
          · exact late P Q hm hmQ total (by omega) :
          ∃ x : Fin 9 → Bool, let w := P.wires (List.ofFn x ++ [x 0 && x 2])
                              Q.eval (w ++ [!(w.getD P.output false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
        apply mismatch

        let raw := List.ofFn x ++ [x 0 && x 2]
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
        exact eqn
