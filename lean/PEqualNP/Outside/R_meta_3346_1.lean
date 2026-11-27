import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3346_1
    (emptyCase : ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 4 || x 6, true]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (pairCase : ∀ i j : Fin 11,
      11 * i.val + j.val ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 24, 26, 27, 29, 31, 32, 48, 50, 51, 53, 54, 84, 86, 87, 108, 109, 120] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 4 || x 6]
        D.eval (w ++ [w.getD i.val false && w.getD j.val false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (16 : ℕ) ≤ x1.size := by
  let F : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let reps : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 24, 26, 27, 29, 31, 32, 48, 50, 51, 53, 54, 84, 86, 87, 108, 109, 120]
  let perm : Fin 4 → Fin 9 → Fin 9 :=
    ![![0,1,2,3,4,5,6,7,8], ![1,0,5,8,6,2,4,7,3],
      ![3,8,5,0,4,2,6,7,1], ![8,3,2,1,6,5,4,7,0]]
  let move : Fin 4 → ℕ → ℕ := fun p j => if h : j < 9 then (perm p ⟨j,h⟩).val else j
  let mf : Fin 4 → Fin 11 → Fin 11 := fun p i =>
    ⟨move p i.val, by dsimp [move]; split <;> omega⟩
  have move_small (p : Fin 4) (i : ℕ) (hi : i < 9) : move p i < 9 := by
    simp only [move, dite_eq_left hi]
    exact (perm p ⟨i,hi⟩).isLt
  have move_large (p : Fin 4) (i : ℕ) (hi : 9 ≤ i) : move p i = i := by
    simp [move, show ¬i < 9 by omega]
  have graph_sym : ∀ (p : Fin 4) (x : Fin 9 → Bool), F (x ∘ perm p) = F x := by
    intro p x
    fin_cases p <;> dsimp [F, perm, Function.comp_def] <;> ac_rfl
  have or_sym : ∀ (p : Fin 4) (x : Fin 9 → Bool),
      (x (perm p 4) || x (perm p 6)) = (x 4 || x 6) := by
    intro p x
    fin_cases p <;> simp [perm, Bool.or_comm]
  have orbit : ∀ i j : Fin 11, ∃ p : Fin 4,
      11 * (mf p i).val + (mf p j).val ∈ reps ∨
      11 * (mf p j).val + (mf p i).val ∈ reps := by
    decide +kernel
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserves (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hj
      · simp [step]
        omega
  have transport (p : Fin 4) (gs : List Gate) : ∀ W W' : List Bool,
      W.length = W'.length → 11 ≤ W.length →
      (∀ j, W'.getD (move p j) false = W.getD j false) →
      ∀ j,
        ((gs.map fun g => Gate.mk g.op (g.inputs.map (move p))).foldl step W').getD
          (move p j) false = (gs.foldl step W).getD j false := by
    induction gs with
    | nil => intro W W' _ _ hw j; exact hw j
    | cons g gs ih =>
      intro W W' hl hlen hw j
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [step, hl]
      · simp [step]
        omega
      · have hv : g.op.eval ((g.inputs.map (move p)).map fun i => W'.getD i false) =
            g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          exact List.map_congr_left fun i _ => hw i
        intro k
        dsimp only [step]
        rw [hv]
        by_cases hk : k < W.length
        · have hk' : move p k < W'.length := by
            by_cases h : k < 9
            · have := move_small p k h
              omega
            · rw [move_large p k (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hk', List.getD_append _ _ _ _ hk]
          exact hw k
        · rw [move_large p k (by omega)]
          by_cases he : k = W.length
          · subst k
            simp [hl]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
  have seed_move (p : Fin 4) (x : Fin 9 → Bool) (i : ℕ) :
      (seed x).getD (move p i) false = (seed (x ∘ perm p)).getD i false := by
    by_cases hi : i < 9
    · have hm := move_small p i hi
      simp only [seed]
      rw [List.getD_append _ _ _ _ (by simpa using hm),
          List.getD_append _ _ _ _ (by simpa using hi)]
      rw [List.getD_eq_getElem _ _ (by simpa using hm),
          List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_ofFn, Function.comp_apply, move, dite_eq_left hi]
    · rw [move_large p i (by omega)]
      by_cases he : i = 9
      · subst i
        change (x 4 || x 6) = (x (perm p 4) || x (perm p 6))
        exact (or_sym p x).symm
      · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
            List.getD_eq_default _ _ (by simp [seed]; omega)]
  have pairImpossible (i j : Fin 11) (D : Circuit) (hD : FanInTwo D) (hs : D.size ≤ 13) :
      ∃ x : Fin 9 → Bool, D.eval (seed x ++
        [(seed x).getD i.val false && (seed x).getD j.val false]) ≠ F x := by
    obtain ⟨p, hp⟩ := orbit i j
    let E : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map (move p)⟩), move p D.output⟩
    have hE : FanInTwo E := by
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hD q hq).1, by simpa using (hD q hq).2⟩
    have hEs : E.size ≤ 13 := by
      change (D.gates.map (fun g => Gate.mk g.op (g.inputs.map (move p)))).length ≤ 13
      change D.gates.length ≤ 13 at hs
      simpa only [List.length_map] using hs
    have contra : ∃ x : Fin 9 → Bool,
        E.eval (seed x ++ [(seed x).getD (move p i.val) false &&
          (seed x).getD (move p j.val) false]) ≠ F x := by
      rcases hp with hp | hp
      · exact pairCase (mf p i) (mf p j) hp E hE hEs
      · obtain ⟨x, hx⟩ := pairCase (mf p j) (mf p i) hp E hE hEs
        refine ⟨x, ?_⟩
        rw [Bool.and_comm ((seed x).getD (move p i.val) false)
          ((seed x).getD (move p j.val) false)]
        exact hx
    obtain ⟨x, hx⟩ := contra
    refine ⟨x ∘ perm p, ?_⟩
    intro computes
    apply hx
    change ((D.gates.map fun g => Gate.mk g.op (g.inputs.map (move p))).foldl step
      (seed x ++ [(seed x).getD (move p i.val) false &&
        (seed x).getD (move p j.val) false])).getD (move p D.output) false = F x
    rw [transport p D.gates
      (seed (x ∘ perm p) ++ [(seed (x ∘ perm p)).getD i.val false &&
        (seed (x ∘ perm p)).getD j.val false])
      (seed x ++ [(seed x).getD (move p i.val) false &&
        (seed x).getD (move p j.val) false]) (by simp [seed]) (by simp [seed])]
    · exact computes.trans (graph_sym p x)
    · intro k
      by_cases hk : k < 10
      · have hm : move p k < 10 := by
          by_cases hk9 : k < 9
          · exact lt_trans (move_small p k hk9) (by decide)
          · rw [move_large p k (by omega)]
            exact hk
        rw [List.getD_append (seed x) _ _ _ (by simpa [seed] using hm),
            List.getD_append (seed (x ∘ perm p)) _ _ _ (by simpa [seed] using hk)]
        exact seed_move p x k
      · rw [move_large p k (by omega)]
        by_cases he : k = 10
        · subst k
          simp only [seed_move]
          simp [seed]
        · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
              List.getD_eq_default _ _ (by simp [seed]; omega)]
  intro C hfan hfirst hfun hand
  by_contra small
  have hsize : C.size ≤ 15 := by omega
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil => simp at hand
  | cons g0 rest =>
    cases rest with
    | nil => simp at hand
    | cons g1 gs =>
      have hop : g1.op = GateOp.and := by simpa using hand
      let D : Circuit := ⟨gs, out⟩
      have hD : FanInTwo D := fun g hg =>
        hfan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
      have hDs : D.size ≤ 13 := by
        change (g0 :: g1 :: gs).length ≤ 15 at hsize
        simp only [List.length_cons] at hsize
        change gs.length ≤ 13
        omega
      have hlen : g1.inputs.length ≤ 2 := (hfan g1 (by simp)).2
      have h0 (x : Fin 9 → Bool) :
          g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
        have h := hfirst x
        change ((g1 :: gs).foldl step (step (List.ofFn x) g0)).getD 9 false = _ at h
        rw [preserves _ _ _ (by simp [step])] at h
        simpa [step] using h
      have computes (x : Fin 9 → Bool) :
          D.eval (seed x ++ [GateOp.and.eval (g1.inputs.map fun i => (seed x).getD i false)]) = F x := by
        have h := congrFun hfun x
        change (gs.foldl step (step (step (List.ofFn x) g0) g1)).getD out false = F x at h
        change (gs.foldl step (seed x ++ [GateOp.and.eval
          (g1.inputs.map fun i => (seed x).getD i false)])).getD out false = F x
        simpa only [step, h0, hop] using h
      let clamp : ℕ → Fin 11 := fun i => ⟨min i 10, by omega⟩
      have hc (x : Fin 9 → Bool) (i : ℕ) :
          (seed x).getD (clamp i).val false = (seed x).getD i false := by
        by_cases hi : i < 10
        · simp [clamp, min_eq_left (by omega : i ≤ 10)]
        · rw [show (clamp i).val = 10 by simp [clamp, min_eq_right (by omega : 10 ≤ i)],
            List.getD_eq_default _ _ (by simp [seed]),
            List.getD_eq_default _ _ (by simp [seed]; omega)]
      have evalAndNil : GateOp.and.eval [] = true := rfl
      have evalAndCons (b : Bool) (bs : List Bool) :
          GateOp.and.eval (b :: bs) = (b && GateOp.and.eval bs) := rfl
      cases hp : g1.inputs with
      | nil =>
        obtain ⟨x, hx⟩ := emptyCase D hD hDs
        apply hx
        simpa only [hp, List.map_nil, evalAndNil, seed, F, List.append_assoc, List.cons_append, List.nil_append] using computes x
      | cons a pins =>
        cases pins with
        | nil =>
          obtain ⟨x, hx⟩ := pairImpossible (clamp a) (clamp a) D hD hDs
          apply hx
          simp only [hc, Bool.and_self]
          simpa only [hp, List.map_cons, List.map_nil, evalAndCons, evalAndNil, Bool.and_true] using computes x
        | cons b pins =>
          cases pins with
          | cons c tail => simp [hp] at hlen
          | nil =>
            obtain ⟨x, hx⟩ := pairImpossible (clamp a) (clamp b) D hD hDs
            apply hx
            simp only [hc]
            simpa only [hp, List.map_cons, List.map_nil, evalAndCons, evalAndNil, Bool.and_true] using computes x
