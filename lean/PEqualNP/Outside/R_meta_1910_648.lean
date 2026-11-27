import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1910_648
    (earlier4 : ∀ (t : List Gate) (o : ℕ), FanInTwo (Circuit.mk t o) →
      (∀ x : Fin 9 → Bool, (Circuit.mk t o).eval (List.ofFn x ++ [x 4 || x 6]) = (fun x : Fin 9 → Bool => ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) x) →
      (∃ a b : Fin t.length, a < b ∧ (let g := t.get a; g.inputs[0]? = some 4 ∨ g.op ≠ GateOp.not ∧ 4 ∈ g.inputs) ∧ (let g := t.get b; g.inputs[0]? = some 6 ∨ g.op ≠ GateOp.not ∧ 6 ∈ g.inputs) ∧
        (∀ i : Fin t.length, (let g := t.get i; g.inputs[0]? = some 4 ∨ g.op ≠ GateOp.not ∧ 4 ∈ g.inputs) → i = a) ∧
        (∀ i : Fin t.length, (let g := t.get i; g.inputs[0]? = some 6 ∨ g.op ≠ GateOp.not ∧ 6 ∈ g.inputs) → i = b)) → 15 ≤ t.length)
    (earlier6 : ∀ (t : List Gate) (o : ℕ), FanInTwo (Circuit.mk t o) →
      (∀ x : Fin 9 → Bool, (Circuit.mk t o).eval (List.ofFn x ++ [x 4 || x 6]) = (fun x : Fin 9 → Bool => ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) x) →
      (∃ a b : Fin t.length, a < b ∧ (let g := t.get a; g.inputs[0]? = some 6 ∨ g.op ≠ GateOp.not ∧ 6 ∈ g.inputs) ∧ (let g := t.get b; g.inputs[0]? = some 4 ∨ g.op ≠ GateOp.not ∧ 4 ∈ g.inputs) ∧
        (∀ i : Fin t.length, (let g := t.get i; g.inputs[0]? = some 6 ∨ g.op ≠ GateOp.not ∧ 6 ∈ g.inputs) → i = a) ∧
        (∀ i : Fin t.length, (let g := t.get i; g.inputs[0]? = some 4 ∨ g.op ≠ GateOp.not ∧ 4 ∈ g.inputs) → i = b)) → 15 ≤ t.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  intro C hf first computes uniqueRead
  obtain ⟨gates, out⟩ := C
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserve (t : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
      (t.foldl step w).getD j false = w.getD j false := by
    induction t generalizing w with
    | nil => rfl
    | cons g t ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  cases gates with
  | nil =>
    have h := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ _ (by simp)] at h
    contradiction
  | cons g t =>
    let D := Circuit.mk t out
    let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
    have headVal (x : Fin 9 → Bool) : step (List.ofFn x) g = start x := by
      have h := first x
      change (t.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
      rw [preserve _ _ _ (by simp [step])] at h
      have idx : (List.ofFn x).length = 9 := by simp
      change (_ ++ [_]).getD 9 false = _ at h
      rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq idx), idx] at h
      change List.ofFn x ++ [_] = List.ofFn x ++ [_]
      exact congrArg (fun b => List.ofFn x ++ [b]) (by simpa using h)
    have evalEq (x : Fin 9 → Bool) :
        (Circuit.mk (g :: t) out).eval (List.ofFn x) = D.eval (start x) := by
      change (t.foldl step (step (List.ofFn x) g)).getD out false = _
      rw [headVal]
      rfl
    have basis : FanInTwo D := fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have evalF (x : Fin 9 → Bool) :
        D.eval (start x) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) := by
      rw [← evalEq]
      have h := congrFun computes x
      refine h.trans ?_
      simp [List.any_cons, Bool.or_assoc, Fin.ofNat]
    let rd (v : Nat) (q : Gate) := q.inputs[0]? = some v ∨ q.op ≠ GateOp.not ∧ v ∈ q.inputs
    obtain ⟨a, ha, ua⟩ := uniqueRead 4 (by simp)
    obtain ⟨b, hb, ub⟩ := uniqueRead 6 (by simp)
    change rd 4 (t.get a) at ha
    change rd 6 (t.get b) at hb
    change ∀ i : Fin t.length, rd 4 (t.get i) → i = a at ua
    change ∀ i : Fin t.length, rd 6 (t.get i) → i = b at ub
    have distinct : a ≠ b := by
      intro same
      have paired (q : Gate) (hq : q ∈ t) : rd 4 q ↔ rd 6 q := by
        obtain ⟨i, eq⟩ := List.mem_iff_get.mp hq
        subst q
        constructor
        · intro h
          simpa only [ua i h, same] using hb
        · intro h
          simpa only [ub i h, ← same] using ha
      let X : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
      let Y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 6)
      let sw (i : Nat) := if i = 4 then 6 else if i = 6 then 4 else i
      have gateEq (q : Gate) (hq : q ∈ t) (u v : List Bool)
          (rel : ∀ i, u.getD i false = v.getD (sw i) false) :
          q.op.eval (q.inputs.map fun i => u.getD i false) =
          q.op.eval (q.inputs.map fun i => v.getD i false) := by
        have pair := paired q hq
        obtain ⟨hop, len⟩ := basis q hq
        change q.op = .and ∨ q.op = .or ∨ q.op = .not at hop
        obtain ⟨op, ins⟩ := q
        cases ins with
        | nil => rfl
        | cons i rest =>
          cases rest with
          | nil =>
            have hi : i ≠ 4 ∧ i ≠ 6 := by
              simp [rd] at pair
              grind
            have e := rel i
            simp only [sw, if_neg hi.1, if_neg hi.2] at e
            exact congrArg (fun bit => op.eval [bit]) e
          | cons j rest =>
            cases rest with
            | cons k r => simp at len
            | nil =>
              simp only at hop
              have unchanged (a : Nat) (h4 : a ≠ 4) (h6 : a ≠ 6) :
                  u.getD a false = v.getD a false := by simpa only [sw, if_neg h4, if_neg h6] using rel a
              have four : u.getD 4 false = v.getD 6 false := rel 4
              have six : u.getD 6 false = v.getD 4 false := rel 6
              rcases hop with h | h | h <;> subst op
              · change (u.getD i false && (u.getD j false && true)) = (v.getD i false && (v.getD j false && true))
                simp only [Bool.and_true, Bool.or_false]
                simp [rd] at pair
                have shape : (i = 4 ∧ j = 6) ∨ (i = 6 ∧ j = 4) ∨ (i ≠ 4 ∧ i ≠ 6 ∧ j ≠ 4 ∧ j ≠ 6) := by grind
                rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨i4,i6,j4,j6⟩
                · rw [four,six,Bool.and_comm (v.getD 6 false)]
                · rw [four,six,Bool.and_comm (v.getD 6 false)]
                · rw [unchanged i i4 i6, unchanged j j4 j6]
              · change (u.getD i false || (u.getD j false || false)) = (v.getD i false || (v.getD j false || false))
                simp only [Bool.and_true, Bool.or_false]
                simp [rd] at pair
                have shape : (i = 4 ∧ j = 6) ∨ (i = 6 ∧ j = 4) ∨ (i ≠ 4 ∧ i ≠ 6 ∧ j ≠ 4 ∧ j ≠ 6) := by grind
                rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨i4,i6,j4,j6⟩
                · rw [four,six,Bool.or_comm (v.getD 6 false)]
                · rw [four,six,Bool.or_comm (v.getD 6 false)]
                · rw [unchanged i i4 i6, unchanged j j4 j6]
              · simp [rd] at pair
                have hi : i ≠ 4 ∧ i ≠ 6 := by grind
                exact congrArg Bool.not (unchanged i hi.1 hi.2)
      have lift (l : List Gate) (sub : ∀ q ∈ l, q ∈ t) (u v : List Bool)
          (len : u.length = v.length) (base : 6 < u.length)
          (rel : ∀ i, u.getD i false = v.getD (sw i) false) :
          ∀ i, (l.foldl step u).getD i false = (l.foldl step v).getD (sw i) false := by
        induction l generalizing u v with
        | nil => exact rel
        | cons q qs ih =>
          apply ih (fun r hr => sub r (List.mem_cons_of_mem _ hr)) (step u q) (step v q)
              (by simp [step,len]) (by simp [step]; omega)
          intro i
          by_cases lo : i < u.length
          · have lo' : sw i < v.length := by
              dsimp [sw]
              split
              · omega
              · split <;> omega
            simpa only [step, List.getD_append _ _ _ _ lo, List.getD_append _ _ _ _ lo'] using rel i
          · have fix : sw i = i := by simp [sw, show i ≠ 4 by omega, show i ≠ 6 by omega]
            rw [fix]
            simp only [step, List.getD_append_right _ _ _ _ (show u.length ≤ i by omega),
              List.getD_append_right _ _ _ _ (show v.length ≤ i by omega),
              gateEq q (sub q (by simp)) u v rel, len]
      have startRel : ∀ i, (start X).getD i false = (start Y).getD (sw i) false := by
        intro i
        by_cases small : i < 10
        · interval_cases i <;> decide
        · have fix : sw i = i := by simp [sw, show i ≠ 4 by omega, show i ≠ 6 by omega]
          rw [fix, List.getD_eq_default _ _ (by simp [start]; omega),
            List.getD_eq_default _ _ (by simp [start]; omega)]
      have fix : sw out = out := by
        let z : Fin 9 → Bool := fun i => decide (i = 4 ∨ i = 6)
        have e := congrFun computes z
        change (List.foldl step (List.ofFn z) (g :: t)).getD out false = false at e
        by_cases h4 : out = 4
        · rw [h4, preserve _ _ _ (by simp)] at e
          contradiction
        by_cases h6 : out = 6
        · rw [h6, preserve _ _ _ (by simp)] at e
          contradiction
        simp [sw,h4,h6]
      have eq := lift t (fun _ h => h) (start X) (start Y) (by simp [start]) (by simp [start]) startRel out
      rw [fix] at eq
      change D.eval (start X) = D.eval (start Y) at eq
      rw [evalF, evalF] at eq
      exact (by decide : ¬ (([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun e => X (Fin.ofNat 9 (e / 9)) && X (Fin.ofNat 9 (e % 9))) =
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun e => Y (Fin.ofNat 9 (e / 9)) && Y (Fin.ofNat 9 (e % 9))))) eq
    have bound : 15 ≤ t.length := by
      rcases lt_or_gt_of_ne distinct with left | right
      · exact earlier4 t out basis evalF ⟨a,b,left,ha,hb,ua,ub⟩
      · exact earlier6 t out basis evalF ⟨b,a,right,hb,ha,ub,ua⟩
    change 16 ≤ (g :: t).length
    simpa using bound
