import PEqualNP.Defs
import Mathlib.Data.List.GetD

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- The stabilizer of the fixed nonedge reduces the ordered operands to monomial masks.
-- A mask of 1024 denotes false. Eliminate aliases and constant-true wire 11.
-- The remaining cases separate features that imply a Petersen edge from features
-- that can also occur on independent sets. The suffix reads only earlier wires.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4813_620
    (hImplies : ∀ (m : Nat) (C : Circuit),
      m ∈ [3,17,66,24,264,320,7,13,1024] → FanInTwo C → C.size ≤ 17 →
      ReadsBack 12 C → 12 ≤ C.output → C.output < 12 + C.size →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      ∃ x : Fin 10 → Bool,
        C.eval (List.ofFn x ++ [x 0 && x 2,
          decide (m < 1024) && (List.finRange 10).all (fun i => !m.testBit i.val || x i)]) ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),
          (7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (hIndependent : ∀ (m : Nat) (C : Circuit),
      m ∈ [9,65,257,10,258,40,72,136,520,768,69,261] → FanInTwo C → C.size ≤ 17 →
      ReadsBack 12 C → 12 ≤ C.output → C.output < 12 + C.size →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      ∃ x : Fin 10 → Bool,
        C.eval (List.ofFn x ++ [x 0 && x 2,
          decide (m < 1024) && (List.finRange 10).all (fun i => !m.testBit i.val || x i)]) ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),
          (7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  let p (k : Fin 4) (i : Fin 10) : Fin 10 :=
    (![![0,1,2,3,4,5,6,7,8,9], ![0,1,2,7,5,4,6,3,9,8],
       ![2,1,0,4,3,7,6,5,9,8], ![2,1,0,5,7,3,6,4,8,9]] : Fin 4 → Fin 10 → Fin 10) k i

  let reps : List ℕ :=
    [0,1024,1,2,8,64,256,3,5,9,17,65,257,10,66,258,24,40,72,136,264,520,320,768,7,13,69,261]

  let feature (m : ℕ) (x : Fin 10 → Bool) : Bool :=
    decide (m < 1024) && (List.finRange 10).all (fun i => !m.testBit i.val || x i)

  let originalSecond (xs : List (Fin 12)) (x : Fin 10 → Bool) : Bool :=
    GateOp.and.eval (xs.map fun i => (List.ofFn x ++ [x 0 && x 2]).getD i.val false)

  let joinMasks (a b : ℕ) : ℕ := if a < 1024 ∧ b < 1024 then a ||| b else 1024

  let wireMask (k : Fin 4) (i : Fin 12) : ℕ :=
    if h : i.val < 10 then 2 ^ (p k ⟨i.val, h⟩).val
    else if i.val = 10 then joinMasks (2 ^ (p k 0).val) (2 ^ (p k 2).val)
    else 1024

  have feature_pow (v : Fin 10) (x : Fin 10 → Bool) : feature (2 ^ v.val) x = x v := by
    have hlt : 2 ^ v.val < 1024 := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) v.isLt
    apply Bool.eq_iff_iff.mpr
    simp only [feature, hlt, decide_true, Bool.true_and, List.all_eq_true, List.mem_finRange,
      true_implies, Nat.testBit_two_pow]
    constructor
    · intro h
      simpa using h v
    · intro h i
      by_cases e : v = i
      · subst i
        simp [h]
      · have hne : v.val ≠ i.val := fun hv => e (Fin.ext hv)
        simp [hne]

  have feature_join (a b : ℕ) (x : Fin 10 → Bool) :
      feature (joinMasks a b) x = (feature a x && feature b x) := by
    by_cases ha : a < 1024
    · by_cases hb : b < 1024
      · have hab : a ||| b < 1024 := Nat.or_lt_two_pow (n := 10) ha hb
        simp only [joinMasks, ha, hb, and_self, ite_true, feature, hab, decide_true, Bool.true_and]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, Nat.testBit_or]
        constructor
        · intro h
          constructor <;> intro i <;> have hi := h i <;>
            cases ea : a.testBit i.val <;> cases eb : b.testBit i.val <;> simp_all
        · rintro ⟨hl, hr⟩ i
          have hi := hl i
          have hj := hr i
          cases ea : a.testBit i.val <;> cases eb : b.testBit i.val <;> simp_all
      · simp [joinMasks, feature, hb]
    · simp [joinMasks, feature, ha]

  have wire_correct (k : Fin 4) (a : Fin 12) (x : Fin 10 → Bool) :
      (List.ofFn (x ∘ p k) ++ [(x ∘ p k) 0 && (x ∘ p k) 2]).getD a.val false =
        feature (wireMask k a) x := by
    by_cases ha : a.val < 10
    · have ha' : a.val < (List.ofFn (x ∘ p k)).length := by simpa only [List.length_ofFn] using ha
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ha', List.getElem?_ofFn]
      simp only [wireMask, ha, dite_true, Option.getD_some, feature_pow, Function.comp_apply]
    · by_cases h10 : a.val = 10
      · simp [wireMask, h10, feature_join, feature_pow, List.getD_eq_getElem?_getD]
      · have hlt := a.isLt
        have h11 : a.val = 11 := by omega
        simp [wireMask, h11, feature, List.getD_eq_getElem?_getD]

  have singleton_cover : ∀ a : Fin 12, ∃ k : Fin 4, wireMask k a ∈ reps := by
    decide +kernel

  have pair_cover : ∀ a b : Fin 12, ∃ k : Fin 4,
      joinMasks (wireMask k a) (wireMask k b) ∈ reps := by
    decide +kernel

  have cover (xs : List (Fin 12)) (hxs : xs.length ≤ 2) :
      ∃ k : Fin 4, ∃ m ∈ reps, ∀ x : Fin 10 → Bool,
        originalSecond xs (x ∘ p k) = feature m x := by
    cases xs with
    | nil =>
      refine ⟨0, 0, by decide, ?_⟩
      intro x
      change true = feature 0 x
      simp [feature, List.all_eq_true]
    | cons a tail =>
      cases tail with
      | nil =>
        obtain ⟨k, hk⟩ := singleton_cover a
        refine ⟨k, wireMask k a, hk, ?_⟩
        intro x
        change ((List.ofFn (x ∘ p k) ++ [(x ∘ p k) 0 && (x ∘ p k) 2]).getD
            a.val false && true) = feature (wireMask k a) x
        rw [Bool.and_true, wire_correct]
      | cons b tail =>
        cases tail with
        | nil =>
          obtain ⟨k, hk⟩ := pair_cover a b
          refine ⟨k, joinMasks (wireMask k a) (wireMask k b), hk, ?_⟩
          intro x
          change ((List.ofFn (x ∘ p k) ++ [(x ∘ p k) 0 && (x ∘ p k) 2]).getD a.val false &&
            ((List.ofFn (x ∘ p k) ++ [(x ∘ p k) 0 && (x ∘ p k) 2]).getD b.val false && true)) = _
          rw [Bool.and_true]
          rw [wire_correct k a x, wire_correct k b x, feature_join]
        | cons c tail => simp at hxs
  let petersen (x : Fin 10 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
    (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

  let edgePairs : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
      (5,7),(7,9),(9,6),(6,8),(8,5)]

  have f_eq_any (x : Fin 10 → Bool) :
      petersen x = edgePairs.any (fun pair => x pair.1 && x pair.2) := by
    simp [petersen, edgePairs, List.any]
    ac_rfl

  have featureOne (k : Fin 4) (x : Fin 10 → Bool) :
      (x (p k 0) && x (p k 2)) = (x 0 && x 2) := by
    fin_cases k <;> simp [p, Matrix.cons_val, Bool.and_comm]

  have f_invariant (k : Fin 4) (x : Fin 10 → Bool) :
      petersen (x ∘ p k) = petersen x := by
    fin_cases k <;> simp [petersen, p, Matrix.cons_val] <;> ac_rfl

  let rename (perm : Fin 10 → Fin 10) (i : ℕ) : ℕ :=
    if h : i < 10 then (perm ⟨i, h⟩).val else i

  let renameGate (perm : Fin 10 → Fin 10) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (rename perm)⟩

  let renameCircuit (perm : Fin 10 → Fin 10) (C : Circuit) : Circuit :=
    ⟨C.gates.map (renameGate perm), rename perm C.output⟩

  have size_rename (perm : Fin 10 → Fin 10) (C : Circuit) :
      (renameCircuit perm C).size = C.size := by
    change (C.gates.map (renameGate perm)).length = C.gates.length
    exact List.length_map (renameGate perm)

  have legal_rename (perm : Fin 10 → Fin 10) (C : Circuit) (h : FanInTwo C) :
      FanInTwo (renameCircuit perm C) := by
    intro g hg
    obtain ⟨before, mem, rfl⟩ := List.mem_map.mp hg
    simpa only [renameGate, List.length_map] using h before mem

  let related (perm : Fin 10 → Fin 10) (old new : List Bool) : Prop :=
    10 ≤ old.length ∧ old.length = new.length ∧
      ∀ i, old.getD i false = new.getD (rename perm i) false

  have related_append (perm : Fin 10 → Fin 10) (old new : List Bool)
      (h : related perm old new) (b : Bool) :
      related perm (old ++ [b]) (new ++ [b]) := by
    obtain ⟨lower, lengths, same⟩ := h
    refine ⟨by simp; omega, by simpa using lengths, ?_⟩
    intro i
    by_cases raw : i < 10
    · have renamed : rename perm i < 10 := by
        simp only [rename, dite_eq_left raw]
        exact (perm ⟨i, raw⟩).isLt
      rw [List.getD_append _ _ _ _ (by omega : i < old.length),
        List.getD_append _ _ _ _ (by omega : rename perm i < new.length)]
      exact same i
    · have renamed : rename perm i = i := dite_eq_right raw
      rw [renamed]
      by_cases prev : i < old.length
      · rw [List.getD_append _ _ _ _ prev, List.getD_append _ _ _ _ (by omega : i < new.length)]
        simpa only [renamed] using same i
      · rw [List.getD_append_right _ _ _ _ (by omega : old.length ≤ i),
          List.getD_append_right _ _ _ _ (by omega : new.length ≤ i), lengths]

  have related_fold (perm : Fin 10 → Fin 10) (gs : List Gate)
      (old new : List Bool) (h : related perm old new) :
      related perm ((Circuit.mk gs 0).wires old)
        ((Circuit.mk (gs.map (renameGate perm)) 0).wires new) := by
    induction gs generalizing old new with
    | nil => exact h
    | cons g gs ih =>
      let oldValue := g.op.eval (g.inputs.map (fun i => old.getD i false))
      let newValue := g.op.eval (g.inputs.map (fun i => new.getD (rename perm i) false))
      have eq : oldValue = newValue := by
        exact congrArg g.op.eval (List.map_congr_left (fun i _ => h.2.2 i))
      change related perm ((Circuit.mk gs 0).wires (old ++ [oldValue]))
        ((Circuit.mk (gs.map (renameGate perm)) 0).wires
          (new ++ [(renameGate perm g).op.eval ((renameGate perm g).inputs.map
            (fun i => new.getD i false))]))
      simp only [renameGate, List.map_map]
      change related perm ((Circuit.mk gs 0).wires (old ++ [oldValue]))
        ((Circuit.mk (gs.map (renameGate perm)) 0).wires (new ++ [newValue]))
      rw [eq]
      exact ih _ _ (related_append perm old new h newValue)

  have related_init (perm : Fin 10 → Fin 10) (x : Fin 10 → Bool) :
      related perm (List.ofFn (x ∘ perm)) (List.ofFn x) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases raw : i < 10
    · have hi : rename perm i < 10 := by
        simp only [rename, dite_eq_left raw]
        exact (perm ⟨i, raw⟩).isLt
      rw [List.getD_eq_getElem _ _ (by simpa using raw),
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn, List.getElem_ofFn]
      simp [rename, raw]
    · have renamed : rename perm i = i := dite_eq_right raw
      rw [renamed, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have eval_rename (perm : Fin 10 → Fin 10) (C : Circuit) (x : Fin 10 → Bool)
      (first second : Bool) :
      C.eval (List.ofFn (x ∘ perm) ++ [first, second]) =
        (renameCircuit perm C).eval (List.ofFn x ++ [first, second]) := by
    have h := related_append perm _ _ (related_init perm x) first
    have h' := related_append perm _ _ h second
    have evals := (related_fold perm C.gates _ _ h').2.2 C.output
    change C.eval ((List.ofFn (x ∘ perm) ++ [first]) ++ [second]) =
      (renameCircuit perm C).eval ((List.ofFn x ++ [first]) ++ [second]) at evals
    simpa only [List.append_assoc, List.singleton_append] using evals
  let wire (slot target index : ℕ) : ℕ :=
    if index = slot then target else index

  let gate (slot target : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wire slot target)⟩

  let circuit (slot target : ℕ) (C : Circuit) : Circuit :=
    ⟨C.gates.map (gate slot target), wire slot target C.output⟩

  have size_circuit (slot target : ℕ) (C : Circuit) :
      (circuit slot target C).size = C.size := by
    change (C.gates.map (gate slot target)).length = C.gates.length
    exact List.length_map (gate slot target)

  have fan_circuit (slot target : ℕ) (C : Circuit) (fan : FanInTwo C) :
      FanInTwo (circuit slot target C) := by
    intro g hg
    obtain ⟨prev, mem, rfl⟩ := List.mem_map.mp hg
    change prev.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (prev.inputs.map (wire slot target)).length ≤ 2
    exact ⟨(fan prev mem).1, (List.length_map (wire slot target)).le.trans (fan prev mem).2⟩

  let BankAgrees (slot target : ℕ) (prior current : List Bool) : Prop :=
    prior.length = current.length ∧ slot < prior.length ∧
    ∀ i, prior.getD i false = current.getD (wire slot target i) false

  let step (values : List Bool) (g : Gate) : List Bool :=
    values ++ [g.op.eval (g.inputs.map fun i => values.getD i false)]

  have step_agrees {slot target : ℕ} (earlier : target < slot)
      (g : Gate) {prior current : List Bool} (agree : BankAgrees slot target prior current) :
      BankAgrees slot target (step prior g) (step current (gate slot target g)) := by
    obtain ⟨sameLength, present, lookup⟩ := agree
    have equalOutput : g.op.eval (g.inputs.map fun i => prior.getD i false) =
        (gate slot target g).op.eval
          ((gate slot target g).inputs.map fun i => current.getD i false) := by
      change g.op.eval (g.inputs.map fun i => prior.getD i false) =
        g.op.eval ((g.inputs.map (wire slot target)).map fun i => current.getD i false)
      simp only [List.map_map, Function.comp_def, lookup]
    refine ⟨by simp [step, sameLength], by simp [step]; omega, ?_⟩
    intro i
    by_cases within : i < prior.length
    · have mappedWithin : wire slot target i < current.length := by
        by_cases eq : i = slot <;> simp [wire, eq] <;> omega
      unfold step
      rw [List.getD_append _ _ _ _ within, List.getD_append _ _ _ _ mappedWithin]
      exact lookup i
    · have neq : i ≠ slot := by omega
      have keeps : wire slot target i = i := by simp [wire, neq]
      unfold step
      rw [keeps, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt within),
        List.getD_append_right _ _ _ _ (sameLength ▸ Nat.le_of_not_gt within),
        equalOutput, sameLength]

  have fold_agrees {slot target : ℕ} (earlier : target < slot)
      (gs : List Gate) {prior current : List Bool} (agree : BankAgrees slot target prior current) :
      BankAgrees slot target (gs.foldl step prior)
        ((gs.map (gate slot target)).foldl step current) := by
    induction gs generalizing prior current with
    | nil => exact agree
    | cons g gs ih =>
      simpa only [List.map_cons, List.foldl_cons] using ih (step_agrees earlier g agree)

  have eval_remap {slot target : ℕ} (earlier : target < slot) (C : Circuit)
      {prior current : List Bool} (agree : BankAgrees slot target prior current) :
      C.eval prior = (circuit slot target C).eval current :=
    (fold_agrees earlier C.gates agree).2.2 C.output

  have eval_alias_last (C : Circuit) (base : List Bool) (target : ℕ)
      (earlier : target < base.length) (replacement : Bool) :
      C.eval (base ++ [base.getD target false]) =
        (circuit base.length target C).eval (base ++ [replacement]) := by
    apply eval_remap earlier C
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases atLast : i = base.length
    · subst i
      rw [show wire base.length target base.length = target by simp [wire],
        List.getD_append _ _ _ _ earlier]
      simp
    · have keep : wire base.length target i = i := by simp [wire, atLast]
      rw [keep]
      by_cases prior : i < base.length
      · rw [List.getD_append _ _ _ _ prior, List.getD_append _ _ _ _ prior]
      · have miss : base.length + 1 ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simpa using miss),
          List.getD_eq_default _ _ (by simpa using miss)]

  have eval_alias_eleven (C : Circuit) (base : List Bool) (length : base.length = 11)
      (target : ℕ) (earlier : target < 11) :
      C.eval (base ++ [base.getD target false]) =
        (circuit 11 target C).eval (base ++ [false]) := by
    simpa only [length] using
      eval_alias_last C base target (by simpa [length] using earlier) false
  let clean (n : ℕ) (g : Gate) : Gate :=
    GateOp.rec (motive := fun _ => Gate)
      (if g.inputs.all (fun i => decide (i < n)) then g else ⟨.or, []⟩)
      ⟨.or, g.inputs.filter (fun i => decide (i < n))⟩
      ⟨.not, (g.inputs.take 1).filter (fun i => decide (i < n))⟩
      (fun _ => g)
      g
      g.op

  have clean_ports (n : ℕ) (g : Gate) (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp)) :
      ∀ i ∈ (clean n g).inputs, i < n := by
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp at h
    · change ∀ i ∈ (if inputs.all (fun i => decide (i < n)) then
        (⟨.and, inputs⟩ : Gate) else ⟨.or, []⟩).inputs, i < n
      split
      · rename_i good
        exact fun i hi => of_decide_eq_true (List.all_eq_true.mp good i hi)
      · simp
    · simp [clean]
    · simp [clean]

  have clean_legal (n : ℕ) (g : Gate)
      (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (clean n g).op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧
        (clean n g).inputs.length ≤ 2 := by
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, length⟩ := h
    cases op <;> simp at hop
    · dsimp [clean]
      split <;> simp [length]
    · exact ⟨by simp [clean], (List.length_filter_le _ _).trans length⟩
    · exact ⟨by simp [clean], (List.length_filter_le _ _).trans
        ((List.length_take_le' _ _).trans length)⟩

  have clean_or (w : List Bool) (inputs : List ℕ) :
      (inputs.filter (fun i => decide (i < w.length))).any (fun i => w.getD i false) =
        inputs.any (fun i => w.getD i false) := by
    induction inputs with
    | nil => rfl
    | cons i rest ih =>
      by_cases hi : i < w.length
      · simp only [List.filter_cons, decide_eq_true hi, ite_true, List.any_cons, ih]
      · have noWire := List.getD_eq_default w false (by omega : w.length ≤ i)
        simp only [List.filter_cons, decide_eq_false hi, Bool.false_eq_true, ite_false, List.any_cons, ih, noWire, Bool.false_or]

  have clean_value (w : List Bool) (g : Gate)
      (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp)) :
      (clean w.length g).op.eval ((clean w.length g).inputs.map (fun i => w.getD i false)) =
        g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp at h
    · dsimp [clean]
      split
      · rfl
      · rename_i bad
        obtain ⟨i, hi, unavail⟩ := List.all_eq_false.mp (Bool.eq_false_of_not_eq_true bad)
        have none : w.length ≤ i := by simpa using unavail
        change false = (inputs.map (fun i => w.getD i false)).all id
        symm
        apply List.all_eq_false.mpr
        have inMap : w.getD i false ∈ inputs.map (fun j => w.getD j false) :=
          List.mem_map_of_mem hi
        rw [List.getD_eq_default w false none] at inMap
        exact ⟨false, inMap, by decide⟩
    · change ((inputs.filter (fun i => decide (i < w.length))).map
        (fun i => w.getD i false)).any id = (inputs.map (fun i => w.getD i false)).any id
      simpa only [List.any_map, Function.id_comp] using clean_or w inputs
    · cases inputs with
      | nil => rfl
      | cons i rest =>
        change Bool.not ((([i].filter (fun j => decide (j < w.length))).map
          (fun j => w.getD j false)).headD false) = Bool.not (w.getD i false)
        by_cases hi : i < w.length
        · simp only [List.filter_cons, List.filter_nil, decide_eq_true hi, ite_true,
            List.map_cons, List.headD_cons]
        · simp only [List.filter_cons, List.filter_nil, decide_eq_false hi, Bool.false_eq_true,
            ite_false, List.map_nil, List.headD_nil, List.getD_eq_default w false (by omega : w.length ≤ i)]

  let cleanGates (n : ℕ) (gs : List Gate) : List Gate :=
    (gs.zipIdx n).map (fun t => clean t.2 t.1)

  let cleanCircuit (n : ℕ) (C : Circuit) : Circuit :=
    ⟨cleanGates n C.gates, C.output⟩

  have clean_size (n : ℕ) (C : Circuit) : (cleanCircuit n C).size = C.size := by
    change ((C.gates.zipIdx n).map (fun t => clean t.2 t.1)).length = C.gates.length
    rw [List.length_map, List.length_zipIdx]

  have clean_fanIn (n : ℕ) (C : Circuit) (h : FanInTwo C) :
      FanInTwo (cleanCircuit n C) := by
    intro g hg
    obtain ⟨⟨old, idx⟩, mem, rfl⟩ := List.mem_map.mp hg
    have oldMem : old ∈ C.gates := by
      rw [(List.mem_zipIdx mem).2.2]
      exact List.getElem_mem _
    exact clean_legal idx old (h old oldMem)

  have clean_readsBack (n : ℕ) (C : Circuit) (h : FanInTwo C) :
      ReadsBack n (cleanCircuit n C) := by
    intro j hj
    have jlt : j < C.gates.length := by simpa [cleanCircuit, cleanGates] using hj
    change ∀ i ∈ ((cleanCircuit n C).gates.getD j ⟨.or, []⟩).inputs, i < n+j
    rw [show (cleanCircuit n C).gates.getD j ⟨.or, []⟩ = clean (n + j) C.gates[j] from by
      simp [cleanCircuit, cleanGates, jlt, List.getElem_zipIdx]]
    exact clean_ports (n+j) _ (h _ (List.getElem_mem _)).1

  have clean_wires (gs : List Gate) (w : List Bool)
      (legal : FanInTwo (Circuit.mk gs 0)) :
      (Circuit.mk (cleanGates w.length gs) 0).wires w = (Circuit.mk gs 0).wires w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      let b := g.op.eval (g.inputs.map (fun i => w.getD i false))
      delta Circuit.wires
      simp only [cleanGates, List.zipIdx_cons, List.map_cons, List.foldl_cons]
      rw [clean_value w g (legal g (List.mem_cons_self ..)).1]
      change (Circuit.mk (cleanGates (w.length + 1) rest) 0).wires (w ++ [b]) =
        (Circuit.mk rest 0).wires (w ++ [b])
      rw [← show (w ++ [b]).length = w.length + 1 by simp]
      exact ih _ (fun g hg => legal g (List.mem_cons_of_mem _ hg))

  have clean_eval (n : ℕ) (C : Circuit) (legal : FanInTwo C)
      (w : List Bool) (width : w.length = n) :
      (cleanCircuit n C).eval w = C.eval w := by
    subst n
    exact congrArg (fun ws => ws.getD C.output false)
      (clean_wires C.gates w (fun _ hg => legal _ hg))
  let gate (j : ℕ) (g : Gate) : Gate :=
    GateOp.rec (motive := fun _ => Gate)
      ⟨.and, g.inputs.filter (· != j)⟩
      (if j ∈ g.inputs then ⟨.and, []⟩ else g)
      (if g.inputs.head? = some j then ⟨.or, []⟩ else g)
      (fun _ => g) g g.op

  let replace (j : ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (gate j), C.output⟩

  have size_replace (j : ℕ) (C : Circuit) : (replace j C).size = C.size := by
    change (C.gates.map (gate j)).length = C.gates.length
    exact List.length_map (gate j)

  have output_replace (j : ℕ) (C : Circuit) : (replace j C).output = C.output := rfl

  let Good (g : Gate) : Prop :=
    g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have gate_good (j : ℕ) (g : Gate) (h : Good g) : Good (gate j g) := by
    rcases g with ⟨op, ins⟩
    cases op with
    | and =>
      refine ⟨by simp [gate], ?_⟩
      exact (List.length_filter_le (· != j) ins).trans h.2
    | or =>
      by_cases hj : j ∈ ins
      · simp [gate, Good, hj]
      · simpa only [gate, hj, ite_false] using h
    | not =>
      by_cases hj : ins.head? = some j
      · simp [gate, Good, hj]
      · simpa only [gate, hj, ite_false] using h
    | mod m => simp [Good] at h
    | maj => simp [Good] at h

  have fan_replace (j : ℕ) (C : Circuit) (h : FanInTwo C) : FanInTwo (replace j C) := by
    intro g hg
    change g ∈ C.gates.map (gate j) at hg
    obtain ⟨g', hmem, rfl⟩ := List.mem_map.mp hg
    exact gate_good j g' (h g' hmem)

  let readGate (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have filter_and (j : ℕ) (new old : List Bool) (htrue : old.getD j false = true)
      (hoff : ∀ i, i ≠ j → new.getD i false = old.getD i false) (ins : List ℕ) :
      ((ins.filter (· != j)).map (fun i => new.getD i false)).all id =
        (ins.map (fun i => old.getD i false)).all id := by
    induction ins with
    | nil => rfl
    | cons a tail ih =>
      by_cases e : a = j
      · subst a
        rw [List.filter_cons_of_neg (p := fun i : ℕ => i != j) (a := j) (by simp)]
        simp only [List.map_cons, List.all_cons, id_eq, htrue, Bool.true_and, ih]
      · rw [List.filter_cons_of_pos (p := fun i : ℕ => i != j) (a := a) (by simp [e])]
        simp only [List.map_cons, List.all_cons, id_eq, hoff a e, ih]

  have readGate_correct (j : ℕ) (new old : List Bool) (htrue : old.getD j false = true)
      (hoff : ∀ i, i ≠ j → new.getD i false = old.getD i false) (g : Gate) (h : Good g) :
      readGate new (gate j g) = readGate old g := by
    rcases g with ⟨op, ins⟩
    cases op with
    | and => exact filter_and j new old htrue hoff ins
    | or =>
      by_cases hj : j ∈ ins
      · have hyes : (ins.map (fun i => old.getD i false)).any id = true := by
          rw [List.any_map, List.any_eq_true]
          exact ⟨j, hj, htrue⟩
        have hg : gate j ⟨.or, ins⟩ = ⟨.and, []⟩ := ite_eq_left hj
        rw [hg]
        change true = (ins.map (fun i => old.getD i false)).any id
        exact hyes.symm
      · have hmap : ins.map (fun i => new.getD i false) = ins.map (fun i => old.getD i false) :=
          List.map_congr_left (fun i hi => hoff i (fun e => hj (e ▸ hi)))
        have hg : gate j ⟨.or, ins⟩ = ⟨.or, ins⟩ := ite_eq_right hj
        rw [hg]
        change (ins.map (fun i => new.getD i false)).any id =
          (ins.map (fun i => old.getD i false)).any id
        rw [hmap]
    | not =>
      cases ins with
      | nil => rfl
      | cons a tail =>
        by_cases e : a = j
        · subst a
          have hg : gate j ⟨.not, j :: tail⟩ = ⟨.or, []⟩ := ite_eq_left rfl
          rw [hg]
          change false = Bool.not (old.getD j false)
          exact (congrArg Bool.not htrue).symm
        · have hne : (a :: tail).head? ≠ some j := by simpa using e
          have hg : gate j ⟨.not, a :: tail⟩ = ⟨.not, a :: tail⟩ := ite_eq_right hne
          rw [hg]
          change Bool.not (new.getD a false) = Bool.not (old.getD a false)
          rw [hoff a e]
    | mod m => simp [Good] at h
    | maj => simp [Good] at h

  have getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false =
        if i < w.length then w.getD i false else if i = w.length then b else false := by
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : i < w.length
    · rw [List.getElem?_append_left hi]
      simp only [hi, ite_true, List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by omega : w.length ≤ i), List.getElem?_singleton]
      by_cases he : i = w.length
      · subst i
        simp
      · have hz : i - w.length ≠ 0 := by omega
        simp [hi, he, hz]

  let Agree (j : ℕ) (new old : List Bool) : Prop :=
    new.length = old.length ∧ j < old.length ∧ old.getD j false = true ∧
      ∀ i, i ≠ j → new.getD i false = old.getD i false

  have agree_snoc {j : ℕ} {new old : List Bool} (h : Agree j new old) (b : Bool) :
      Agree j (new ++ [b]) (old ++ [b]) := by
    rcases h with ⟨hlen, hj, ht, hoff⟩
    refine ⟨by simp [hlen], by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
    · simpa only [getD_snoc, hj, ite_true] using ht
    · intro i hi
      by_cases hbound : i < old.length
      · simpa only [getD_snoc, hlen, hbound, ite_true] using hoff i hi
      · simp only [getD_snoc, hlen, hbound, ite_false]

  let step (w : List Bool) (g : Gate) : List Bool := w ++ [readGate w g]

  have fold_agree (j : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Good g)
      (new old : List Bool) (h : Agree j new old) :
      Agree j ((gs.map (gate j)).foldl step new) (gs.foldl step old) := by
    induction gs generalizing new old with
    | nil => exact h
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ ?_
      have he := readGate_correct j new old h.2.2.1 h.2.2.2 g (hgs g (by simp))
      simpa only [step, he] using agree_snoc h (readGate old g)

  have eval_replace (j : ℕ) (C : Circuit) (xs : List Bool) (hxs : xs.length = j)
      (hout : C.output ≠ j) (hfan : FanInTwo C) :
      (replace j C).eval (xs ++ [false]) = C.eval (xs ++ [true]) := by
    have initial : Agree j (xs ++ [false]) (xs ++ [true]) := by
      refine ⟨by simp, by simp [hxs], ?_, ?_⟩
      · rw [getD_snoc, hxs]
        simp
      · intro i hi
        simp only [getD_snoc, hxs, hi, ite_false]
    have terminal := fold_agree j C.gates hfan (xs ++ [false]) (xs ++ [true]) initial
    exact terminal.2.2.2 C.output hout
  let first (x : Fin 10 → Bool) : Bool := x 0 && x 2

  let support (m : Nat) : Finset (Fin 10) := Finset.univ.filter fun i => m.testBit i.val

  let seed (f : (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool) : List Bool :=
    (List.ofFn x ++ [first x]) ++ [f x]

  let single (v : Fin 10) (i : Fin 10) : Bool := decide (i = v)

  let pair (u v : Fin 10) (i : Fin 10) : Bool := decide (i = u ∨ i = v)

  let effectiveInputs (gate : Gate) : List Nat :=
    GateOp.rec (motive := fun _ => List Nat) gate.inputs gate.inputs (gate.inputs.take 1)
      (fun _ => gate.inputs) gate.inputs gate.op

  have eval_effective (gate : Gate) (w : List Bool) :
      gate.op.eval (gate.inputs.map fun i => w.getD i false) =
        gate.op.eval ((effectiveInputs gate).map fun i => w.getD i false) := by
    rcases gate with ⟨op, inputs⟩
    cases op <;> try rfl
    cases inputs <;> rfl

  have monomial_true (m : Nat) (x : Fin 10 → Bool) :
      feature m x = true ↔ m < 1024 ∧ ∀ i ∈ support m, x i = true := by
    simp only [feature, Bool.and_eq_true, decide_eq_true_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h i hi
      have hb : m.testBit i.val = true := (Finset.mem_filter.mp hi).2
      have hv := List.all_eq_true.mp h i (by simp)
      simpa [hb] using hv
    · intro h
      apply List.all_eq_true.mpr
      intro i _
      cases hb : m.testBit i.val with
      | false => simp
      | true => simpa [hb] using h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)

  have support_in_pair {m : Nat} {u v : Fin 10} (h : feature m (pair u v) = true) :
      support m ⊆ {u, v} := by
    intro i hi
    have hv := ((monomial_true m (pair u v)).mp h).2 i hi
    simpa [pair] using hv

  have monomial_single_eq_pair {m : Nat} {u v : Fin 10} (hu : u ∉ support m) :
      feature m (single v) = feature m (pair u v) := by
    rw [Bool.eq_iff_iff, monomial_true, monomial_true]
    apply and_congr_right
    intro _
    have hsame : ∀ i ∈ support m, single v i = pair u v i := by
      intro i hi
      have hd : i ≠ u := fun he => hu (he ▸ hi)
      simp [single, pair, hd]
    exact ⟨fun h i hi => (hsame i hi).symm.trans (h i hi),
      fun h i hi => (hsame i hi).trans (h i hi)⟩

  have monomial_split {m : Nat} {u v : Fin 10}
      (h : feature m (single v) ≠ feature m (pair u v)) :
      m < 1024 ∧ u ∈ support m ∧ support m ⊆ {u, v} := by
    have hp : feature m (pair u v) = true := by
      cases hpair : feature m (pair u v) with
      | true => rfl
      | false =>
        have hs : feature m (single v) = true := by
          cases hs : feature m (single v) <;> simp_all
        obtain ⟨hm, hsx⟩ := (monomial_true m (single v)).mp hs
        have href := (monomial_true m (pair u v)).mpr ⟨hm, fun i hi => by
          have hv : i = v := by simpa [single] using hsx i hi
          simp [pair, hv]⟩
        rw [hpair] at href
        contradiction
    exact ⟨((monomial_true m (pair u v)).mp hp).1,
      Classical.byContradiction (fun hu => h (monomial_single_eq_pair hu)), support_in_pair hp⟩

  let neighborA (u : Fin 10) : Fin 10 :=
    ([1, 0, 1, 2, 0, 0, 1, 2, 3, 4] : List (Fin 10)).getD u.val 0

  let neighborB (u : Fin 10) : Fin 10 :=
    ([4, 2, 3, 4, 3, 7, 8, 5, 5, 6] : List (Fin 10)).getD u.val 0

  let Separates (u v : Fin 10) : Prop :=
    petersen (single v) = false ∧ petersen (pair u v) = true ∧ first (single v) = first (pair u v)

  have two_neighbors : ∀ u : Fin 10,
      Separates u (neighborA u) ∧ Separates u (neighborB u) ∧ neighborA u ≠ neighborB u := by
    unfold Separates
    decide +kernel

  have single_false : ∀ i : Fin 10, petersen (single i) = false := by decide +kernel

  have feature_agrees_or_singleton (m : Nat) (u : Fin 10) :
      (∃ v, Separates u v ∧ feature m (single v) = feature m (pair u v)) ∨
        (m < 1024 ∧ support m = {u}) := by
    classical
    obtain ⟨h1, h2, hd⟩ := two_neighbors u
    by_cases hA : feature m (single (neighborA u)) = feature m (pair u (neighborA u))
    · exact Or.inl ⟨neighborA u, h1, hA⟩
    by_cases hB : feature m (single (neighborB u)) = feature m (pair u (neighborB u))
    · exact Or.inl ⟨neighborB u, h2, hB⟩
    obtain ⟨hm, hu, ha⟩ := monomial_split hA
    obtain ⟨_, _, hb⟩ := monomial_split hB
    right
    refine ⟨hm, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hu)⟩
    intro i hi
    have hia := Finset.mem_insert.mp (ha hi)
    have hib := Finset.mem_insert.mp (hb hi)
    simp only [Finset.mem_singleton] at hia hib ⊢
    rcases hia with hia | hia
    · exact hia
    · rcases hib with hib | hib
      · exact hib
      · exact (hd (hia.symm.trans hib)).elim

  have seed_length (f : (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool) :
      (seed f x).length = 12 := by simp [seed]

  have seed_raw (f : (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool) (i : Fin 10) :
      (seed f x).getD i.val false = x i := by
    unfold seed
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

  have seed_first (f : (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool) :
      (seed f x).getD 10 false = first x := by
    unfold seed
    rw [List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp

  have seed_second (f : (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool) :
      (seed f x).getD 11 false = f x := by
    unfold seed
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

  have wires_length (gs : List Gate) (x : List Bool) :
      ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil =>
      change x.length = x.length + 0
      exact (Nat.add_zero x.length).symm
    | cons g gs ih =>
      let y := x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]
      change ((⟨gs, 0⟩ : Circuit).wires y).length = _
      rw [ih]
      simp [y]
      omega

  have prefix_wires (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
      ((⟨gs, 0⟩ : Circuit).wires x).getD i false = x.getD i false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      let y := x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]
      change ((⟨gs, 0⟩ : Circuit).wires y).getD i false = _
      have hiy : i < y.length := by simp [y]; omega
      rw [ih y hiy]
      exact List.getD_append _ _ _ _ hi

  have output_is_generated (m : Nat) (D : Circuit)
      (computes : ∀ x, D.eval (seed (feature m) x) = petersen x) :
      12 ≤ D.output ∧ D.output < 12 + D.size := by
    have before : ∀ x, D.output < 12 → D.eval (seed (feature m) x) =
        (seed (feature m) x).getD D.output false := fun x h =>
      prefix_wires D.gates _ _ (by simpa only [seed_length] using h)
    constructor
    · by_contra! hout
      by_cases raw : D.output < 10
      · let u : Fin 10 := ⟨D.output, raw⟩
        have he := computes (single u)
        rw [before (single u) hout] at he
        change (seed (feature m) (single u)).getD u.val false = petersen (single u) at he
        rw [seed_raw, single_false] at he
        simp [single] at he
      by_cases fstOut : D.output = 10
      · have he := computes (pair 0 1)
        rw [before (pair 0 1) hout, fstOut, seed_first] at he
        exact (by decide : first (pair 0 1) ≠ petersen (pair 0 1)) he
      · have sndOut : D.output = 11 := by omega
        have hf (x : Fin 10 → Bool) : feature m x = petersen x := by
          rw [← seed_second (feature m) x, ← sndOut, ← before x hout, computes]
        have ha : feature m (pair 0 1) = true := (hf _).trans (by decide)
        have hb : feature m (pair 2 3) = true := (hf _).trans (by decide)
        have hh : feature m (fun _ => false) = true := by
          refine (monomial_true m _).mpr ⟨((monomial_true m _).mp ha).1, ?_⟩
          intro i hi
          have hai := support_in_pair ha hi
          have hbi := support_in_pair hb hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hai hbi
          rcases hai with h0 | h1
          · subst i; exact ((by decide : ¬ ((0 : Fin 10) = 2 ∨ (0 : Fin 10) = 3)) hbi).elim
          · subst i; exact ((by decide : ¬ ((1 : Fin 10) = 2 ∨ (1 : Fin 10) = 3)) hbi).elim
        rw [hf] at hh
        exact (by decide : petersen (fun _ => false) ≠ true) hh
    · by_contra! h
      have hfalse : D.eval (seed (feature m) (pair 0 1)) = false := by
        change (D.wires (seed (feature m) (pair 0 1))).getD D.output false = false
        apply List.getD_eq_default
        change ((⟨D.gates, 0⟩ : Circuit).wires (seed (feature m) (pair 0 1))).length ≤ D.output
        rw [wires_length, seed_length]
        exact h
      have he := computes (pair 0 1)
      rw [hfalse] at he
      exact (by decide : false ≠ petersen (pair 0 1)) he

  let Agree (exc : Nat → Prop) (x y : List Bool) : Prop :=
    x.length = y.length ∧ ∀ i, ¬ exc i → x.getD i false = y.getD i false

  have agree_append {exc : Nat → Prop} {x y : List Bool} (h : Agree exc x y)
      (a b : Bool) (hab : ¬ exc x.length → a = b) : Agree exc (x ++ [a]) (y ++ [b]) := by
    have hlen : x.length = y.length := h.1
    refine ⟨by simp [h.1], ?_⟩
    intro i hi
    by_cases hlt : i < x.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (h.1 ▸ hlt)]
      exact h.2 i hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ← h.1]
      by_cases he : i = x.length
      · rw [he, Nat.sub_self, hab (he ▸ hi)]
      · have hbound : 1 ≤ i - x.length := by omega
        rw [List.getD_eq_default _ _ (by simpa using hbound),
          List.getD_eq_default _ _ (by simpa using hbound)]

  have agree_fold {exc : Nat → Prop} (gs : List Gate)
      (avoids : ∀ g ∈ gs, ∀ i ∈ effectiveInputs g, ¬ exc i)
      {x y : List Bool} (h : Agree exc x y) :
      Agree exc ((⟨gs, 0⟩ : Circuit).wires x) ((⟨gs, 0⟩ : Circuit).wires y) := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      let val (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have he : val x = val y := by
        unfold val
        rw [eval_effective, eval_effective]
        apply congrArg g.op.eval
        exact List.map_congr_left fun i hi => h.2 i (avoids g (by simp) i hi)
      change Agree exc ((⟨gs, 0⟩ : Circuit).wires (x ++ [val x]))
        ((⟨gs, 0⟩ : Circuit).wires (y ++ [val y]))
      exact ih (fun g' h' => avoids g' (List.mem_cons_of_mem _ h')) (agree_append h _ _ (fun _ => he))

  have seeds_agree (f : (Fin 10 → Bool) → Bool) (u v : Fin 10) (exc : Nat → Prop)
      (hu : exc u.val) (hFirst : first (single v) = first (pair u v))
      (hSecond : ¬exc 11 → f (single v) = f (pair u v)) :
      Agree exc (seed f (single v)) (seed f (pair u v)) := by
    have raw : Agree exc (List.ofFn (single v)) (List.ofFn (pair u v)) := by
      refine ⟨by simp, ?_⟩
      intro i hi
      by_cases hlt : i < 10
      · let j : Fin 10 := ⟨i, hlt⟩
        have hj : j ≠ u := by
          intro he
          have he' : i = u.val := congrArg Fin.val he
          exact hi (he'.symm ▸ hu)
        rw [List.getD_eq_getElem _ _ (by simpa using hlt),
          List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn, List.getElem_ofFn]
        change single v j = pair u v j
        simp [single, pair, hj]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact agree_append (agree_append raw _ _ (fun _ => hFirst)) _ _
      (fun h => hSecond (by simpa using h))

  have effective_reader_of_agreement (f : (Fin 10 → Bool) → Bool) (D : Circuit)
      (computes : ∀ x, D.eval (seed f x) = petersen x) (u v : Fin 10) (exc : Nat → Prop)
      (hu : exc u.val) (hout : ¬exc D.output) (hSep : Separates u v)
      (hSecond : ¬exc 11 → f (single v) = f (pair u v)) :
      ∃ g ∈ D.gates, ∃ i ∈ effectiveInputs g, exc i := by
    by_contra! avoids
    have hseed := seeds_agree f u v exc hu hSep.2.2 hSecond
    have hwires := agree_fold D.gates avoids hseed
    have he := hwires.2 D.output hout
    change D.eval (seed f (single v)) = D.eval (seed f (pair u v)) at he
    rw [computes, computes, hSep.1, hSep.2.1] at he
    contradiction

  have all_raw_inputs_effective (m : Nat) (D : Circuit)
      (computes : ∀ x, D.eval (seed (feature m) x) = petersen x)
      (hcount : (support m).card ≠ 1) (u : Fin 10) :
      ∃ g ∈ D.gates, u.val ∈ effectiveInputs g := by
    have hout := (output_is_generated m D computes).1
    rcases feature_agrees_or_singleton m u with ⟨v, hv, hfeat⟩ | ⟨_, hs⟩
    · obtain ⟨g, hg, i, hi, rfl⟩ := effective_reader_of_agreement (feature m) D computes u v
        (fun i => i = u.val) rfl (by have := u.isLt; omega) hv (fun _ => hfeat)
      exact ⟨g, hg, hi⟩
    · exact (hcount (by simp [hs])).elim
  let impliesGraph : List Nat := [3,17,66,24,264,320,7,13,1024]
  let independent : List Nat := [9,65,257,10,258,40,72,136,520,768,69,261]
  let aliases : List Nat := [1,2,8,64,256,5]

  have m_partition (m : Nat) (hm : m ∈ reps) :
      m ∈ impliesGraph ++ independent ∨ (m ∈ aliases ∨ m = 0) := by
    have coverMasks : reps.all (fun t => decide (t ∈ (impliesGraph ++ independent) ++ (aliases ++ [0]))) =
        true := by decide +kernel
    rcases List.mem_append.mp (of_decide_eq_true (List.all_eq_true.mp coverMasks m hm)) with useful | rest
    · exact Or.inl useful
    · exact Or.inr (by simpa only [List.mem_append, List.mem_singleton] using rest)

  have rawAlias (i : Fin 10) (x : Fin 10 → Bool) :
      feature (2 ^ i.val) x = (List.ofFn x ++ [x 0 && x 2]).getD i.val false := by
    rw [feature_pow, List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have firstAlias (x : Fin 10 → Bool) :
      feature 5 x = (List.ofFn x ++ [x 0 && x 2]).getD 10 false := by
    have hm : joinMasks (2 ^ (0 : Fin 10).val) (2 ^ (2 : Fin 10).val) = 5 := by
      decide +kernel
    rw [← hm, feature_join, feature_pow, feature_pow]
    simp
  have aliasValue (m : Nat) (hm : m ∈ aliases) :
      ∃ i : Fin 11, ∀ x : Fin 10 → Bool,
        feature m x = (List.ofFn x ++ [x 0 && x 2]).getD i.val false := by
    simp only [aliases, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rawAlias 0⟩
    · exact ⟨1, rawAlias 1⟩
    · exact ⟨3, rawAlias 3⟩
    · exact ⟨6, rawAlias 6⟩
    · exact ⟨8, rawAlias 8⟩
    · exact ⟨10, firstAlias⟩

  have eliminate (D : Circuit) (m : Nat) (hm : m ∈ impliesGraph ++ independent)
      (legal : FanInTwo D) (small : D.size ≤ 17)
      (computes : ∀ x, D.eval (seed (feature m) x) = petersen x) : False := by
    let T := cleanCircuit 12 D
    have legalT : FanInTwo T := clean_fanIn _ _ legal
    have smallT : T.size ≤ 17 := by
      rwa [clean_size]
    have backT : ReadsBack 12 T := clean_readsBack _ _ legal
    have computesT : ∀ x, T.eval (seed (feature m) x) = petersen x := by
      intro x
      rw [clean_eval 12 D legal _ (seed_length (feature m) x)]
      exact computes x
    have outputT := output_is_generated m T computesT
    have properMasks : (impliesGraph ++ independent).all
        (fun t => decide ((support t).card ≠ 1)) = true := by decide +kernel
    have supportM : (support m).card ≠ 1 :=
      of_decide_eq_true (List.all_eq_true.mp properMasks m hm)
    have readsT (i : Fin 10) : ∃ g ∈ T.gates, i.val ∈ g.inputs := by
      obtain ⟨g, hg, hread⟩ := all_raw_inputs_effective m T computesT supportM i
      refine ⟨g, hg, ?_⟩
      cases hop : g.op <;> simp only [effectiveInputs, hop] at hread
      · exact hread
      · exact hread
      · exact List.mem_of_mem_take hread
      · exact hread
      · exact hread
    have agrees (x : Fin 10 → Bool) :
        T.eval (List.ofFn x ++ [x 0 && x 2, feature m x]) =
          edgePairs.any (fun e => x e.1 && x e.2) := by
      rw [← f_eq_any]
      simpa only [seed, first, List.append_assoc, List.singleton_append] using computesT x
    rcases List.mem_append.mp hm with hp | hn
    · obtain ⟨x, different⟩ := hImplies m T hp legalT smallT backT
        outputT.1 outputT.2 readsT
      exact different (agrees x)
    · obtain ⟨x, different⟩ := hIndependent m T hn legalT smallT backT
        outputT.1 outputT.2 readsT
      exact different (agrees x)

  intro C xs legal small width
  by_contra! absent
  have computes (x : Fin 10 → Bool) :
      C.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [originalSecond xs x]) = petersen x :=
    Classical.not_not.mp (absent x)
  obtain ⟨k, m, hm, normalized⟩ := cover xs width
  let R := renameCircuit (p k) C
  have legalR : FanInTwo R := legal_rename _ _ legal
  have smallR : R.size ≤ 17 := by rwa [size_rename]
  have computesR (x : Fin 10 → Bool) : R.eval (seed (feature m) x) = petersen x := by
    have old := computes (x ∘ p k)
    rw [normalized x, show ((x ∘ p k) 0 && (x ∘ p k) 2) = (x 0 && x 2) from featureOne k x,
      f_invariant k x] at old
    have moved := eval_rename (p k) C x (x 0 && x 2) (feature m x)
    calc
      R.eval (seed (feature m) x) = R.eval (List.ofFn x ++ [x 0 && x 2, feature m x]) := by
        simp only [seed, first, List.append_assoc, List.singleton_append]
      _ = C.eval (List.ofFn (x ∘ p k) ++ [x 0 && x 2, feature m x]) := moved.symm
      _ = petersen x := by simpa only [List.append_assoc, List.singleton_append] using old
  rcases m_partition m hm with hp | ha | hzero
  · exact eliminate R m hp legalR smallR computesR
  · obtain ⟨i, hi⟩ := aliasValue m ha
    let S := circuit 11 i.val R
    have legalS : FanInTwo S := fan_circuit _ _ _ legalR
    have smallS : S.size ≤ 17 := by rwa [size_circuit]
    apply eliminate S 1024 (by decide) legalS smallS
    intro x
    have before : R.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [feature m x]) = petersen x :=
      computesR x
    rw [hi x, eval_alias_eleven R _ (by simp) i.val i.isLt] at before
    exact before
  · subst m
    let S := replace 11 R
    have legalS : FanInTwo S := fan_replace _ _ legalR
    have smallS : S.size ≤ 17 := by rwa [size_replace]
    have hOut : R.output ≠ 11 := by
      have generated := (output_is_generated 0 R computesR).1
      omega
    apply eliminate S 1024 (by decide) legalS smallS
    intro x
    have hx : feature 0 x = true := by simp [feature, List.all_eq_true]
    have before : R.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [feature 0 x]) = petersen x :=
      computesR x
    rw [hx, ← eval_replace 11 R _ (by simp) hOut legalR] at before
    exact before
