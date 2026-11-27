import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3509_40
    (binary : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) →
      13 ≤ D.gates.countP (fun g => !(g.op.eval [] && !g.op.eval [true])))
    (total : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) → 15 ≤ D.size)
    (hard : ∀ (a b : Fin 9) (C : Circuit), a.val * 10 + b.val ∈ [13, 15, 17, 18, 26, 28, 36, 67] →
      FanInTwo C → C.size = 13 → C.output = 23 →
      C.gates.countP (fun g => g.op.eval [] && !g.op.eval [true]) ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) → False) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∉ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False := by
  have getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp

  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩

  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (relGate n m π g).op.eval
        ((relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
    intro w
    simp only [step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        unfold wmap
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : wmap n m π w = W'.length := by
        unfold wmap
        split
        · omega
        · omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ wmap n m π w := by
        unfold wmap
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)

  let target (x : Fin 9 → Bool) : Bool := (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))

  let code (a b : Fin 9) : ℕ := a.val * 10 + b.val

  let canonicalPairs : List ℕ := [13, 15, 17, 18, 26, 28, 36, 67]

  let σ (t : Bool) (i : Fin 9) : Fin 9 :=
    if t then (![0, 5, 8, 3, 4, 1, 7, 6, 2] : Fin 9 → Fin 9) i else i

  have orbit :
      ∀ a b : Fin 9, a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
        code a b ∉ [12, 21, 23, 32, 16, 61, 27, 72, 38, 83, 57, 75, 68, 86, 58, 85] →
        ∃ t : Bool, code (σ t a) (σ t b) ∈ canonicalPairs ∨
          code (σ t b) (σ t a) ∈ canonicalPairs := by decide +revert +kernel

  have target_sym : ∀ t (x : Fin 9 → Bool), target (x ∘ σ t) = target x := by decide +revert +kernel

  have seed_sym : ∀ t : Bool, σ t 0 = 0 ∧ σ t 4 = 4 := by decide +revert +kernel

  let bits (a b : Fin 9) (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [x 0 || x 4, x a || x b]

  have readRaw (x : Fin 9 → Bool) (i : Fin 9) (tail : List Bool) :
      (List.ofFn x ++ tail).getD i.val false = x i := by
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    exact List.getElem_ofFn ..

  have appendGate (x : Fin 9 → Bool) (a b : Fin 9) (tail : List Bool) :
      step (List.ofFn x ++ tail) ⟨.or, [a.val, b.val]⟩ =
        (List.ofFn x ++ tail) ++ [x a || x b] := by
    simp only [step, List.map_cons, List.map_nil, readRaw]
    cases x a <;> cases x b <;> rfl

  have prefixEval (a b : Fin 9) (C : Circuit) (x : Fin 9 → Bool) :
      (⟨⟨.or, [0, 4]⟩ :: ⟨.or, [a.val, b.val]⟩ :: C.gates, C.output⟩ : Circuit).eval
          (List.ofFn x) = C.eval (bits a b x) := by
    change (C.gates.foldl step (step (step (List.ofFn x) ⟨.or, [0, 4]⟩)
      ⟨.or, [a.val, b.val]⟩)).getD C.output false = _
    have h0 := appendGate x 0 4 []
    simp only [List.append_nil] at h0
    change step (List.ofFn x) ⟨.or, [0, 4]⟩ = List.ofFn x ++ [x 0 || x 4] at h0
    rw [h0, appendGate, List.append_assoc]
    rfl

  have relBits (a b : Fin 9) (t : Bool) (x : Fin 9 → Bool) :
      Rel 9 9 (σ t) (bits a b (x ∘ σ t)) (bits (σ t a) (σ t b) x) := by
    refine ⟨by simp [bits], by simp [bits], ?_⟩
    intro w
    by_cases h : w < 9
    · let i : Fin 9 := ⟨w, h⟩
      change (bits (σ t a) (σ t b) x).getD (wmap 9 9 (σ t) w) false =
        (bits a b (x ∘ σ t)).getD i.val false
      have map : wmap 9 9 (σ t) w = (σ t i).val := dite_eq_left h
      rw [map]
      simp only [bits, readRaw, Function.comp_apply]
    · have map : wmap 9 9 (σ t) w = w := by
        unfold wmap
        rw [dite_eq_right h]
        omega
      rw [map]
      have bound : 9 ≤ w := by omega
      unfold bits
      rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using bound),
        List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using bound)]
      simp only [List.length_ofFn, Function.comp_apply, (seed_sym t).1, (seed_sym t).2]

  let isNot (g : Gate) : Bool :=
    g.op.eval [] && !g.op.eval [true]

  have countComplement (L : List Gate) :
      L.countP (fun g => !isNot g) + L.countP (isNot) =
        L.length := by
    induction L with
    | nil => rfl
    | cons g L ih =>
      simp only [List.countP_cons, List.length_cons]
      cases h : isNot g <;> simp [h] <;> omega

  have liftInput (x : Fin 9 → Bool) :
      Rel 9 10 (Fin.castAdd 1) (List.ofFn x) (List.ofFn x ++ [false]) := by
    refine ⟨by simp, by simp, ?_⟩
    intro j
    by_cases hj : j < 9
    · unfold wmap
      rw [dite_eq_left hj]
      change (List.ofFn x ++ [false]).getD j false = (List.ofFn x).getD j false
      exact List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hj)
    · unfold wmap
      rw [dite_eq_right hj]
      have hleft : (List.ofFn x ++ [false]).length ≤ j - 9 + 10 := by simp
      have hright : (List.ofFn x).length ≤ j := by simpa using Nat.le_of_not_gt hj
      rw [List.getD_eq_default _ _ hleft, List.getD_eq_default _ _ hright]

  have renamedFan (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) (hfan : FanInTwo C) :
      FanInTwo (relabel n m π C) := by
    intro g hg
    change g ∈ C.gates.map (relGate n m π) at hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    simpa only [relGate, List.length_map] using hfan q hq

  have wireCount (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, List.length_cons]
      simp only [step, List.length_append, List.length_singleton]
      omega

  have prefixStable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

  have combinedBounds
      (binary : ∀ D : Circuit, FanInTwo D →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = target x) →
        13 ≤ D.gates.countP (fun g => !isNot g))
      (total : ∀ D : Circuit, FanInTwo D →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) = target x) → 15 ≤ D.size) :
      ∀ (a b : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (bits a b x) = target x) →
        C.size = 13 ∧ C.output = 23 ∧ C.gates.countP (isNot) ≤ 2 := by
    have installed (a b : Fin 9) (C : Circuit) (hfan : FanInTwo C)
        (heval : ∀ x : Fin 9 → Bool, C.eval (bits a b x) = target x) :
        15 ≤ C.size + 2 ∧ 13 ≤ C.gates.countP (fun g => !isNot g) + 2 := by
      let D : Circuit := ⟨⟨.or, [0, 4]⟩ :: ⟨.or, [a.val, b.val]⟩ :: C.gates, C.output⟩
      have hD : FanInTwo D := by
        intro g hg
        change g ∈ ⟨.or, [0, 4]⟩ :: ⟨.or, [a.val, b.val]⟩ :: C.gates at hg
        rcases List.mem_cons.mp hg with rfl | hg
        · simp
        rcases List.mem_cons.mp hg with rfl | hg
        · simp
        exact hfan g hg
      have computes (x : Fin 9 → Bool) : D.eval (List.ofFn x) = target x :=
        (prefixEval a b C x).trans (heval x)
      let E := relabel 9 10 (Fin.castAdd 1) D
      have floor := total E (renamedFan 9 10 (Fin.castAdd 1) D hD) (by
        intro x
        exact ((rel_fold 9 10 (Fin.castAdd 1) D.gates _ _ (liftInput x)).2.2 D.output).trans
          (computes x))
      have bin := binary D hD computes
      have fsize : E.size = C.size + 2 := by
        change ((⟨.or, [0, 4]⟩ :: ⟨.or, [a.val, b.val]⟩ :: C.gates).map
          (relGate 9 10 (Fin.castAdd 1))).length = C.gates.length + 2
        simp only [List.length_map, List.length_cons]
      constructor
      · omega
      · change 13 ≤ (⟨.or, [0, 4]⟩ :: ⟨.or, [a.val, b.val]⟩ :: C.gates).countP
          (fun g => !isNot g) at bin
        have orCount (xs : List ℕ) : (!isNot ⟨.or, xs⟩) = true := rfl
        simp only [List.countP_cons, orCount, ite_true] at bin
        omega
    intro a b C hfan small computes
    obtain ⟨totalFloor, binFloor⟩ := installed a b C hfan computes
    have card : C.size = 13 := by omega
    have last : C.output = 23 := by
      by_contra wrong
      rcases lt_or_gt_of_ne wrong with early | late
      · let k := C.output + 1 - 11
        let D : Circuit := ⟨C.gates.take k, C.output⟩
        have bound : k ≤ 12 := by dsimp [k]; omega
        have kLen : k ≤ C.gates.length := by
          change C.gates.length = 13 at card
          omega
        have smallD : D.size ≤ 12 := by
          change (C.gates.take k).length ≤ 12
          rw [List.length_take, Nat.min_eq_left kLen]
          exact bound
        have legalD : FanInTwo D := by
          intro g gMem
          exact hfan g (List.mem_of_mem_take gMem)
        have evalD (x : Fin 9 → Bool) : D.eval (bits a b x) = target x := by
          rw [← computes x]
          change ((C.gates.take k).foldl step (bits a b x)).getD C.output false =
            (C.gates.foldl step (bits a b x)).getD C.output false
          conv_rhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
          apply (prefixStable _ _ _ ?_).symm
          rw [wireCount, List.length_take, Nat.min_eq_left kLen]
          have start : (bits a b x).length = 11 := by simp [bits]
          dsimp [k]
          omega
        have := (installed a b D legalD evalD).1
        omega
      · let x : Fin 9 → Bool := fun _ => true
        have h := computes x
        change (C.gates.foldl step (bits a b x)).getD C.output false = target x at h
        have len : (C.gates.foldl step (bits a b x)).length ≤ C.output := by
          rw [wireCount]
          change C.gates.length = 13 at card
          simp [bits, card]
          omega
        rw [List.getD_eq_default _ _ len] at h
        cases h
    refine ⟨card, last, ?_⟩
    have eq := countComplement C.gates
    change C.gates.length = 13 at card
    omega

  have canonicalize
      (bounded : ∀ (a b : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (bits a b x) = target x) →
        C.size = 13 ∧ C.output = 23 ∧ C.gates.countP (isNot) ≤ 2)
      (hard : ∀ (a b : Fin 9) (C : Circuit), code a b ∈ canonicalPairs → FanInTwo C →
        C.size = 13 → C.output = 23 → C.gates.countP (isNot) ≤ 2 →
        (∀ x : Fin 9 → Bool, C.eval (bits a b x) = target x) → False) :
      ∀ (a b : Fin 9) (C : Circuit), a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
        code a b ∉ [12, 21, 23, 32, 16, 61, 27, 72, 38, 83, 57, 75, 68, 86, 58, 85] →
        FanInTwo C → C.size ≤ 13 → (∀ x : Fin 9 → Bool, C.eval (bits a b x) = target x) →
        False := by
    intro a b C a0 a4 b0 b4 ab nonedge hfan size hEq
    obtain ⟨t, orient⟩ := orbit a b a0 a4 b0 b4 ab nonedge
    let D := relabel 9 9 (σ t) C
    have hD := renamedFan 9 9 (σ t) C hfan
    have card : D.size = C.size := by
      change (C.gates.map (relGate 9 9 (σ t))).length = C.gates.length
      simp only [List.length_map]
    have ev (x : Fin 9 → Bool) : D.eval (bits (σ t a) (σ t b) x) = target x :=
      ((rel_fold 9 9 (σ t) C.gates _ _ (relBits a b t x)).2.2 C.output).trans
        ((hEq (x ∘ σ t)).trans (target_sym t x))
    obtain ⟨exactSize, last, nots⟩ := bounded (σ t a) (σ t b) D hD (card ▸ size) ev
    rcases orient with forward | reverse
    · exact hard _ _ D forward hD exactSize last nots ev
    · have flip (x : Fin 9 → Bool) : bits (σ t b) (σ t a) x = bits (σ t a) (σ t b) x := by
        simp only [bits, Bool.or_comm (x (σ t b)) (x (σ t a))]
      exact hard _ _ D reverse hD exactSize last nots (by intro x; rw [flip]; exact ev x)
  exact canonicalize (combinedBounds binary total) hard
