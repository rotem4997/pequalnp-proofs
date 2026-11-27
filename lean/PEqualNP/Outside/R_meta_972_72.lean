import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Remove forward references and relabel the lines for the single-level bound.
-- The first premise is the checked single-level result L_meta_1751.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_972_72
    (depthOne :
      have S : Finset (Fin 13) := {0, 1, 3, 9}
      have accepts : Circuit → Prop := fun D =>
        (∀ p l : Fin 13, p - l ∈ S → D.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q : Finset (Fin 13), Q.card = 4 →
          (∀ l : Fin 13, (Q.filter fun p => p - l ∈ S).card ≤ 2) → D.eval
          (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ S))) = false
      have hasNested : Circuit → Prop := fun D =>
        ∃ i j : ℕ, (gateAt D i).op = GateOp.and ∧
          (gateAt D j).op = GateOp.and ∧ InCone 26 D i j
      ∀ D : Circuit, Monotone2 D → ReadsBack 26 D → accepts D → ¬ hasNested D → 64 ≤ D.size)
    (nested :
      have S : Finset (Fin 13) := {0, 1, 3, 9}
      have computesIncidence : Circuit → Prop := fun D =>
        ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
          p - l ∈ S ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ D : Circuit, Monotone2 D → ReadsBack 26 D → computesIncidence D →
        (∀ F : Circuit, Monotone2 F → ReadsBack 26 F → computesIncidence F → D.size ≤ F.size) →
        (∃ i j : ℕ, (gateAt D i).op = GateOp.and ∧
          (gateAt D j).op = GateOp.and ∧ InCone 26 D i j) → 64 ≤ D.size)
    : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C monotone computes
  let goal (x : Fin 26 → Bool) := decide (∃ p l : Fin 13,
    (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  let edges : List (ℕ × ℕ) := ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ))
  have table : ∀ u v : Fin 26, (u.val, v.val) ∈ edges ↔
      u.val < 13 ∧ 13 ≤ v.val ∧
        ((Fin.ofNat 13 u.val).val + (Fin.ofNat 13 v.val).val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
    decide +kernel
  have value (x : Fin 26 → Bool) : C.eval (List.ofFn x) = goal x := by
    rw [Bool.eq_iff_iff, computes]
    change (∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) ↔ goal x = true
    simp only [goal, decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, edge, hu, hv⟩
      obtain ⟨low, high, inc⟩ := (table u v).mp edge
      have point : Fin.castAdd 13 (Fin.ofNat 13 u.val) = u := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt low
      have line : Fin.natAdd 13 (Fin.ofNat 13 v.val) = v := by
        apply Fin.ext
        change 13 + v.val % 13 = v.val
        have bv := v.isLt
        omega
      exact ⟨Fin.ofNat 13 u.val, Fin.ofNat 13 v.val, inc, by rwa [point], by rwa [line]⟩
    · rintro ⟨p, l, inc, hp, hl⟩
      have locp : Fin.ofNat 13 (Fin.castAdd 13 p).val = p := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt p.isLt
      have locl : Fin.ofNat 13 (Fin.natAdd 13 l).val = l := by
        apply Fin.ext
        change (13 + l.val) % 13 = l.val
        have bl := l.isLt
        omega
      refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, (table _ _).mpr ⟨p.isLt, by simp, ?_⟩, hp, hl⟩
      simpa only [locp, locl] using inc
  let fix (m : ℕ) (g : Gate) : Gate :=
    if g.op.eval [] = true ∧ ∃ i ∈ g.inputs, m ≤ i then ⟨.or, []⟩
    else ⟨g.op, g.inputs.filter fun i => decide (i < m)⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (w : List Bool) (pins : List ℕ) :
      step w (fix w.length ⟨.or, pins⟩) = step w ⟨.or, pins⟩ := by
    have empty : GateOp.or.eval [] = false := rfl
    have ops : fix w.length ⟨.or, pins⟩ = ⟨.or, pins.filter fun i => decide (i < w.length)⟩ := by
      simp [fix, empty]
    rw [ops]
    change w ++ [((pins.filter fun i => decide (i < w.length)).map
      (fun i => w.getD i false)).any id] = w ++ [(pins.map fun i => w.getD i false).any id]
    congr 2
    rw [Bool.eq_iff_iff]
    simp only [List.any_map, Function.comp_apply, id_eq, List.any_eq_true, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨member, _⟩, hit⟩
      exact ⟨i, member, hit⟩
    · rintro ⟨i, member, hit⟩
      refine ⟨i, ⟨member, ?_⟩, hit⟩
      by_contra! bad
      rw [List.getD_eq_default _ _ bad] at hit
      cases hit
  have keepAnd (w : List Bool) (pins : List ℕ) :
      step w (fix w.length ⟨.and, pins⟩) = step w ⟨.and, pins⟩ := by
    have empty : GateOp.and.eval [] = true := rfl
    by_cases bad : ∃ i ∈ pins, w.length ≤ i
    · have ops : fix w.length ⟨.and, pins⟩ = ⟨.or, []⟩ := by simp [fix, empty, bad]
      rw [ops]
      change w ++ [false] = w ++ [(pins.map fun i => w.getD i false).all id]
      congr 2
      obtain ⟨i, member, invalid⟩ := bad
      symm
      cases h : (pins.map fun i => w.getD i false).all id
      · rfl
      · have hi := List.all_eq_true.mp h (w.getD i false) (List.mem_map_of_mem member)
        change w.getD i false = true at hi
        rw [List.getD_eq_default _ _ invalid] at hi
        cases hi
    · have eq : (pins.filter fun i => decide (i < w.length)) = pins := by
        apply List.filter_eq_self.mpr
        intro i member
        exact decide_eq_true (lt_of_not_ge fun invalid => bad ⟨i, member, invalid⟩)
      have ops : fix w.length ⟨.and, pins⟩ = ⟨.and, pins⟩ := by simp [fix, empty, bad, eq]
      rw [ops]
  have stepEq (w : List Bool) (g : Gate) (op : g.op = .and ∨ g.op = .or) :
      step w (fix w.length g) = step w g := by
    obtain ⟨op', pins⟩ := g
    change op' = .and ∨ op' = .or at op
    rcases op with rfl | rfl
    · exact keepAnd w pins
    · exact keep w pins
  have wiresEq (gs : List Gate) (w : List Bool)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      (gs.mapIdx (fun i g => fix (w.length + i) g)).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons, Nat.add_zero,
        stepEq w g (ops g (List.mem_cons_self))]
      have index : (fun i h => fix (w.length + (i + 1)) h) =
          fun i h => fix ((step w g).length + i) h := by
        funext i h
        simp only [step, List.length_append, List.length_singleton]
        congr 1
        omega
      rw [index]
      exact ih (step w g) (fun h hm => ops h (List.mem_cons_of_mem g hm))
  let D : Circuit := ⟨C.gates.mapIdx (fun i g => fix (26 + i) g), C.output⟩
  have dmono : Monotone2 D := by
    intro g member
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp member
    obtain ⟨op, len⟩ := monotone C.gates[i] (List.getElem_mem hi)
    dsimp only [fix]
    split
    · simp
    · exact ⟨op, (List.length_filter_le _ _).trans len⟩
  have back : ReadsBack 26 D := by
    intro j hj i hi
    have old : j < C.gates.length := by simpa only [D, List.length_mapIdx] using hj
    change i ∈ (D.gates.getD j ⟨.or, []⟩).inputs at hi
    rw [List.getD_eq_getElem D.gates _ hj] at hi
    simp only [D, List.getElem_mapIdx] at hi
    dsimp only [fix] at hi
    split at hi
    · simp at hi
    · exact decide_eq_true_eq.mp (List.mem_filter.mp hi).2
  have dvalue (x : Fin 26 → Bool) : D.eval (List.ofFn x) = goal x := by
    have outputSame := congrArg (fun ws : List Bool => ws.getD C.output false)
      (wiresEq C.gates (List.ofFn x) (fun g hg => (monotone g hg).1))
    change ((C.gates.mapIdx fun i g => fix (26+i) g).foldl step (List.ofFn x)).getD C.output false = goal x
    rw [List.length_ofFn] at outputSame
    exact outputSame.trans (value x)
  let flip (i : ℕ) := if 13 < i ∧ i < 26 then 39 - i else i
  have flipLt (i m : ℕ) (hm : 26 ≤ m) : flip i < m ↔ i < m := by
    unfold flip
    split <;> omega
  have fixed (i : ℕ) (hi : 26 ≤ i) : flip i = i := by
    simp [flip, show ¬ (13 < i ∧ i < 26) by omega]
  let perm (i : Fin 26) : Fin 26 := ⟨flip i.val, (flipLt i.val 26 (by decide)).2 i.isLt⟩
  have left (p : Fin 13) : perm (Fin.castAdd 13 p) = Fin.castAdd 13 p := by
    apply Fin.ext
    change flip p.val = p.val
    simp [flip, show ¬ (13 < p.val) by omega]
  have rightValue : ∀ l : Fin 13,
      (if 13 < 13 + l.val ∧ 13 + l.val < 26 then 39 - (13 + l.val) else 13 + l.val) =
        (Fin.natAdd 13 (-l)).val := by
    decide +kernel
  have right (l : Fin 13) : perm (Fin.natAdd 13 l) = Fin.natAdd 13 (-l) := Fin.ext (rightValue l)
  have incidence : ∀ p l : Fin 13,
      (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
        p - (-l) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    decide +kernel
  let reindex (g : Gate) : Gate := ⟨g.op, g.inputs.map flip⟩
  let E : Circuit := ⟨D.gates.map reindex, flip D.output⟩
  have maps (gs : List Gate) (w z : List Bool) (len : w.length = z.length)
      (hw : 26 ≤ w.length) (rel : ∀ i, z.getD (flip i) false = w.getD i false) :
      ∀ i, ((gs.map reindex).foldl step z).getD (flip i) false = (gs.foldl step w).getD i false := by
    induction gs generalizing w z with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (step w g) (step z (reindex g))
      · simpa only [step, List.length_append, List.length_singleton] using congrArg (· + 1) len
      · simp only [step, List.length_append, List.length_singleton]
        omega
      · have values : (g.inputs.map flip).map (fun i => z.getD i false) =
            g.inputs.map (fun i => w.getD i false) := by
          rw [List.map_map]
          exact List.map_congr_left (fun i _ => rel i)
        intro i
        change (z ++ [g.op.eval ((g.inputs.map flip).map fun j => z.getD j false)]).getD (flip i) false =
          (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD i false
        rw [values]
        by_cases hi : i < w.length
        · have hz : flip i < z.length := by rw [← len]; exact (flipLt i w.length hw).2 hi
          rw [List.getD_append _ _ _ _ hz, List.getD_append _ _ _ _ hi]
          exact rel i
        · rw [fixed i (by omega), List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), len]
  have emono : Monotone2 E := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    obtain ⟨op, count⟩ := dmono j hj
    exact ⟨op, by simpa only [reindex, List.length_map] using count⟩
  have eback : ReadsBack 26 E := by
    intro j hj i hi
    have hd : j < D.gates.length := by simpa only [E, List.length_map] using hj
    change i ∈ (E.gates.getD j ⟨.or, []⟩).inputs at hi
    rw [List.getD_eq_getElem E.gates _ hj] at hi
    simp only [E, List.getElem_map, reindex] at hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    have pin : k ∈ (gateAt D j).inputs := by
      change k ∈ (D.gates.getD j ⟨.or, []⟩).inputs
      rwa [List.getD_eq_getElem D.gates _ hd]
    exact (flipLt _ _ (by omega)).2 (back j hd k pin)
  have evalue (x : Fin 26 → Bool) : E.eval (List.ofFn x) = decide (∃ p l : Fin 13,
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
    have rel (i : ℕ) : (List.ofFn x).getD (flip i) false =
        (List.ofFn (x ∘ perm)).getD i false := by
      by_cases hi : i < 26
      · have hflip := (flipLt i 26 (by decide)).2 hi
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hflip),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getElem_ofFn]
        rfl
      · rw [fixed i (by omega), List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi),
          List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]
    have he : E.eval (List.ofFn x) = D.eval (List.ofFn (x ∘ perm)) := maps D.gates
      (List.ofFn (x ∘ perm)) (List.ofFn x) (by simp only [List.length_ofFn])
      (by simp only [List.length_ofFn]; omega) rel D.output
    rw [he, dvalue, Bool.eq_iff_iff]
    simp only [goal, decide_eq_true_eq, Function.comp_apply, left, right, incidence]
    constructor
    · rintro ⟨p, l, hp, hx, hy⟩
      exact ⟨p, -l, hp, hx, hy⟩
    · rintro ⟨p, l, hp, hx, hy⟩
      exact ⟨p, -l, by simpa only [neg_neg] using hp, hx, by simpa only [neg_neg] using hy⟩
  have sameSize : E.size = C.size := by
    change (D.gates.map reindex).length = C.gates.length
    rw [List.length_map]
    exact List.length_mapIdx
  let computesIncidence (F : Circuit) :=
    ∀ x : Fin 26 → Bool, F.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  have eComputes : computesIncidence E := by
    intro x
    rw [evalue, decide_eq_true_eq]
  classical
  have existsSize : ∃ n : ℕ, ∃ F : Circuit,
      Monotone2 F ∧ ReadsBack 26 F ∧ computesIncidence F ∧ F.size = n :=
    ⟨E.size, E, emono, eback, eComputes, rfl⟩
  obtain ⟨F, fmono, fback, fvalue, fsize⟩ := Nat.find_spec existsSize
  have smallest (G : Circuit) (mono : Monotone2 G) (reads : ReadsBack 26 G)
      (value : computesIncidence G) : F.size ≤ G.size := by
    rw [fsize]
    exact Nat.find_min' existsSize ⟨G, mono, reads, value, rfl⟩
  rw [← sameSize]
  apply Nat.le_trans _ (smallest E emono eback eComputes)
  by_cases nest : ∃ i j : ℕ,
      (gateAt F i).op = GateOp.and ∧ (gateAt F j).op = GateOp.and ∧ InCone 26 F i j
  · exact nested F fmono fback fvalue smallest nest
  · apply depthOne F fmono fback _ nest
    constructor
    · intro p l inc
      rw [← List.ofFn_fin_append]
      exact (fvalue _).2 ⟨p, l, inc, by simp only [Fin.append_left, decide_true],
        by simp only [Fin.append_right, decide_true]⟩
    · intro S _ _
      rw [← List.ofFn_fin_append]
      apply Bool.eq_false_iff.mpr
      intro accepted
      obtain ⟨p, l, inc, hp, hl⟩ := (fvalue _).1 accepted
      rw [Fin.append_left, decide_eq_true_eq] at hp
      rw [Fin.append_right, decide_eq_true_eq] at hl
      exact hl p hp inc
