import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- If the third gate ignores the second one, commute them and use the posted second-OR case.
-- Otherwise a counterexample leaves at most twelve gates after the negation and disjunction.
-- Graph symmetry and repeated signal values leave 64 ordered choices of the two signals.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2750_1
    (secondOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x3 : Fin (9 : ℕ) →
        Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) ||
          x3 (4 : Fin (9 : ℕ)))) →
        (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) →
        Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
          x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
          x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
          x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
          x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
          x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
          x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
          x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
          x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
          x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
          x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
          x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
        Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →
        (16 : ℕ) ≤ x1.size)
    (afterImp : ∀ (D : Circuit) (a b : Fin 11), FanInTwo D →
      a.val ∉ ([5,7,8] : List ℕ) →
      (a.val ∈ ([1,2,6] : List ℕ) ∨ b.val ∉ ([5,7,8] : List ℕ)) →
      (a.val = 10 → b.val = 10) → (b.val = 9 → a.val ∉ ([0,4] : List ℕ)) →
      (∀ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        let v := !(w.getD a.val false)
        D.eval ((w ++ [v]) ++ [v || w.getD b.val false]) =
          (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
            x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) → 13 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x3 : Fin (9 : ℕ) →
        Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) ||
          x3 (4 : Fin (9 : ℕ)))) →
        (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) →
        Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
          x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
          x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
          x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
          x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
          x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
          x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
          x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
          x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
          x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
          x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
          x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
        Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not →
        Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x1.gates[(2 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →
        (16 : ℕ) ≤ x1.size := by
  let F := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let W (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let signal (x : Fin 9 → Bool) (a : Fin 11) := (W x).getD a.val false
  let inputs (x : Fin 9 → Bool) (a b : Fin 11) :=
    let v := !(signal x a)
    (W x ++ [v]) ++ [v || signal x b]
  let val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let ok (g : Gate) := g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2
  let ren (p : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map p⟩
  have model (p : ℕ → ℕ) (gs : List Gate) (h : ∀ g ∈ gs, ok g) :
      ∀ g ∈ gs.map (ren p), ok g := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact ⟨(h q hq).1, by simpa [ren] using (h q hq).2⟩
  have follow (n : ℕ) (p : ℕ → ℕ) (inRange : ∀ i < n, p i < n)
      (fixed : ∀ i, n ≤ i → p i = i) (gs : List Gate) (u v : List Bool)
      (enough : n ≤ u.length) (len : u.length = v.length)
      (agree : ∀ i, v.getD (p i) false = u.getD i false) :
      ∀ i, ((Circuit.mk (gs.map (ren p)) 0).wires v).getD (p i) false =
        ((Circuit.mk gs 0).wires u).getD i false := by
    induction gs generalizing u v with
    | nil => exact agree
    | cons g gs ih =>
      have hv : val (ren p g) v = val g u := by
        change g.op.eval ((g.inputs.map p).map _) = g.op.eval (g.inputs.map _)
        rw [List.map_map]
        exact congrArg g.op.eval (List.map_congr_left fun i _ => agree i)
      apply ih (u ++ [val g u]) (v ++ [val (ren p g) v]) (by simp; omega) (by simp [len])
      intro i
      by_cases hi : i < u.length
      · have hp : p i < v.length := by
          by_cases h : i < n
          · have := inRange i h
            omega
          · rw [fixed i (by omega)]
            omega
        rw [List.getD_append _ _ _ _ hp, List.getD_append _ _ _ _ hi, agree]
      · rw [fixed i (by omega), List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len, hv]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      ((Circuit.mk gs 0).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (w ++ [val g w])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]
  have encoded (x : Fin 9 → Bool) : F x =
      (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) ||
      (x 8 && x 5)) = (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) ||
      ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) ||
      ((x 5 && x 7) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))
    simp only [Bool.or_false, Bool.or_assoc]
  let π : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let ρ : Fin 11 → Fin 11 := ![0,5,8,3,4,1,7,6,2,9,10]
  let perm (i : ℕ) := if h : i < 9 then (π ⟨i,h⟩).val else i
  have graph (x : Fin 9 → Bool) : F (x ∘ π) = F x := by
    change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) ||
      (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) ||
      (x 8 && x 5))
    simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  have sigPerm (x : Fin 9 → Bool) (i : Fin 11) : signal (x ∘ π) i = signal x (ρ i) := by
    fin_cases i <;> rfl
  have finitePairs (P : Fin 11 → Fin 11 → Prop) [DecidableRel P]
      (h : (List.finRange 11).all (fun a => (List.finRange 11).all (fun b => decide (P a b))) = true) :
      ∀ a b, P a b := by
    intro a b
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h a (by simp)) b (by simp))
  have cov : ∀ a b : Fin 11,
      (a.val ∉ ([5,7,8] : List ℕ) ∧ (a.val ∈ ([1,2,6] : List ℕ) ∨ b.val ∉ ([5,7,8] : List ℕ))) ∨
      ((ρ a).val ∉ ([5,7,8] : List ℕ) ∧ ((ρ a).val ∈ ([1,2,6] : List ℕ) ∨ (ρ b).val ∉ ([5,7,8] : List ℕ))) := by
    refine @finitePairs _ (fun a b => ?_) ?_
    · infer_instance
    · decide +kernel
  have permInputs (x : Fin 9 → Bool) (a b : Fin 11) (i : ℕ) :
      (inputs x (ρ a) (ρ b)).getD (perm i) false = (inputs (x ∘ π) a b).getD i false := by
    have rawInput (y : Fin 9 → Bool) (c d : Fin 11) (j : Fin 9) :
        (inputs y c d).getD j.val false = y j := by
      fin_cases j <;> rfl
    by_cases h : i < 9
    · let j : Fin 9 := ⟨i,h⟩
      simp only [perm, dite_eq_left h]
      change (inputs x (ρ a) (ρ b)).getD (π j).val false = (inputs (x ∘ π) a b).getD j.val false
      rw [rawInput, rawInput, Function.comp_apply]
    · have same : perm i = i := by simp [perm, h]
      rw [same]
      by_cases k : i < 12
      · have hi : i = 9 ∨ i = 10 ∨ i = 11 := by omega
        rcases hi with rfl | rfl | rfl
        · rfl
        · change (!(signal x (ρ a))) = !(signal (x ∘ π) a)
          rw [sigPerm]
        · change (!(signal x (ρ a)) || signal x (ρ b)) = (!(signal (x ∘ π) a) || signal (x ∘ π) b)
          rw [sigPerm, sigPerm]
      · rw [List.getD_eq_default _ _ (by simp [inputs, W]; omega),
          List.getD_eq_default _ _ (by simp [inputs, W]; omega)]
  -- A missing source makes the negation true. Negating an endpoint and OR-ing with
  -- the first wire gives the same constant as OR-ing with that endpoint.
  let partner (a b : Fin 11) : Fin 11 :=
    if a = 10 then 10 else if b = 9 ∧ (a = 0 ∨ a = 4) then a else b
  have normalized : ∀ a b : Fin 11,
      (a.val ∈ ([1,2,6] : List ℕ) ∨ b.val ∉ ([5,7,8] : List ℕ)) →
      (a.val ∈ ([1,2,6] : List ℕ) ∨ (partner a b).val ∉ ([5,7,8] : List ℕ)) ∧
      (a.val = 10 → (partner a b).val = 10) ∧
      ((partner a b).val = 9 → a.val ∉ ([0,4] : List ℕ)) := by
    refine @finitePairs _ (fun a b => ?_) ?_
    · infer_instance
    · decide +kernel
  have sameSignal (x : Fin 9 → Bool) (a b : Fin 11) :
      (!(signal x a) || signal x (partner a b)) = (!(signal x a) || signal x b) := by
    by_cases h : a = 10
    · subst a
      rfl
    · by_cases k : b = 9 ∧ (a = 0 ∨ a = 4)
      · rcases k with ⟨rfl, rfl | rfl⟩
        · change ((!x 0) || x 0) = ((!x 0) || (x 0 || x 4))
          cases x 0 <;> rfl
        · change ((!x 4) || x 4) = ((!x 4) || (x 0 || x 4))
          cases x 4 <;> cases x 0 <;> rfl
      · simp [partner, h, k]
  have canonical (D : Circuit) (a b : Fin 11) (fan : FanInTwo D)
      (ha : a.val ∉ ([5,7,8] : List ℕ))
      (hb : a.val ∈ ([1,2,6] : List ℕ) ∨ b.val ∉ ([5,7,8] : List ℕ))
      (computes : ∀ x, D.eval (inputs x a b) = F x) : 13 ≤ D.size := by
    obtain ⟨hrep, hfalse, hor⟩ := normalized a b hb
    apply afterImp D a (partner a b) fan ha hrep hfalse hor
    intro x
    have eq : inputs x a (partner a b) = inputs x a b :=
      congrArg (fun v => (W x ++ [!(signal x a)]) ++ [v]) (sameSignal x a b)
    exact ((congrArg D.eval eq).trans (computes x)).trans (encoded x)
  have bounded (D : Circuit) (a b : Fin 11) (fan : FanInTwo D)
      (computes : ∀ x, D.eval (inputs x a b) = F x) : 13 ≤ D.size := by
    rcases cov a b with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact canonical D a b fan ha hb computes
    · let E := Circuit.mk (D.gates.map (ren perm)) (perm D.output)
      have hfan : FanInTwo E := model perm D.gates fan
      have heval (x : Fin 9 → Bool) : E.eval (inputs x (ρ a) (ρ b)) = F x := by
        have small (i : ℕ) (hi : i < 12) : perm i < 12 := by
          by_cases h : i < 9
          · simp only [perm, dite_eq_left h]
            have := (π ⟨i,h⟩).isLt
            omega
          · simp [perm,h,hi]
        have fixed (i : ℕ) (hi : 12 ≤ i) : perm i = i := by
          simp [perm, show ¬ i < 9 by omega]
        exact (follow 12 perm small fixed D.gates (inputs (x ∘ π) a b) (inputs x (ρ a) (ρ b))
          (by simp [inputs, W]) (by simp [inputs, W]) (permInputs x a b) D.output).trans
            ((computes (x ∘ π)).trans (graph x))
      have h := canonical E (ρ a) (ρ b) hfan ha hb heval
      change 13 ≤ (D.gates.map (ren perm)).length at h
      change 13 ≤ D.gates.length
      simpa only [List.length_map] using h
  rintro ⟨gates, out⟩ fan first computes second third
  rcases gates with _ | ⟨g,tail₁⟩
  · cases second
  rcases tail₁ with _ | ⟨neg,tail₂⟩
  · cases second
  rcases tail₂ with _ | ⟨disj,tail⟩
  · cases third
  have nOp : neg.op = .not := Option.some.inj second
  have oOp : disj.op = .or := Option.some.inj third
  have good (h) (hh : h ∈ g :: neg :: disj :: tail) : ok h := fan h hh
  have goodTail (h) (hh : h ∈ tail) : ok h := good h (by simp [hh])
  have gval (x : Fin 9 → Bool) : val g (List.ofFn x) = (x 0 || x 4) := by
    have h := first x
    change ((Circuit.mk (neg :: disj :: tail) 0).wires (List.ofFn x ++ [val g (List.ofFn x)])).getD 9 false = _ at h
    rw [keep _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)] at h
    simpa using h
  let cap (i : ℕ) : Fin 11 := ⟨min i 10, by omega⟩
  have readCap (x : Fin 9 → Bool) (i : ℕ) : signal x (cap i) = (W x).getD i false := by
    by_cases h : i < 10
    · change (W x).getD (min i 10) false = _
      rw [Nat.min_eq_left (by omega)]
    · change (W x).getD (min i 10) false = _
      rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by simp [W]),
          List.getD_eq_default _ _ (by simp [W]; omega)]
  let a := cap (neg.inputs.headD 10)
  have negValue (x : Fin 9 → Bool) : val neg (W x) = !(signal x a) := by
    change neg.op.eval (neg.inputs.map _) = !(signal x (cap (neg.inputs.headD 10)))
    rw [nOp, readCap]
    cases h : neg.inputs with
    | nil => rfl
    | cons i is => rfl
  have getPush (x : Fin 9 → Bool) (v : Bool) (i : ℕ) :
      (W x ++ [v]).getD i false = if i = 10 then v else (W x).getD i false := by
    by_cases h : i < 10
    · rw [List.getD_append _ _ _ _ (by simp [W]; omega), ite_eq_right (by omega)]
    · by_cases he : i = 10
      · subst i
        rw [ite_eq_left rfl, List.getD_append_right _ _ _ _ (by simp [W])]
        simp [W]
      · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp [W]; omega),
            List.getD_eq_default _ _ (by simp [W]; omega)]
  have lastWire (x : Fin 9 → Bool) (v : Bool) : (W x ++ [v]).getD 10 false = v := by
    rw [getPush x v 10, ite_eq_left rfl]
  have missing (x : Fin 9 → Bool) : (W x).getD 10 false = false :=
    List.getD_eq_default _ _ (by simp [W])
  have tailValue (x : Fin 9 → Bool) :
      (Circuit.mk tail out).eval ((W x ++ [!(signal x a)]) ++ [val disj (W x ++ [!(signal x a)])]) = F x := by
    have h := congrFun computes x
    change (Circuit.mk tail out).eval
      (((List.ofFn x ++ [val g (List.ofFn x)]) ++ [val neg (List.ofFn x ++ [val g (List.ofFn x)])]) ++
        [val disj ((List.ofFn x ++ [val g (List.ofFn x)]) ++ [val neg (List.ofFn x ++ [val g (List.ofFn x)])])]) = _ at h
    rw [gval] at h
    change (Circuit.mk tail out).eval ((W x ++ [val neg (W x)]) ++ [val disj (W x ++ [val neg (W x)])]) = _ at h
    rwa [negValue] at h
  -- Wire ten is the output of the NOT gate. All higher indices are missing at that point.
  by_cases used : 10 ∈ disj.inputs
  · have lengthO : disj.inputs.length ≤ 2 := (good disj (by simp)).2
    have dependent : ∃ b : Fin 11, ∀ x, val disj (W x ++ [!(signal x a)]) =
        (!(signal x a) || signal x b) := by
      change ∃ b, ∀ x, disj.op.eval (disj.inputs.map _) = _
      rw [oOp]
      cases ls : disj.inputs with
      | nil => simp [ls] at used
      | cons i is =>
        cases is with
        | nil =>
          have eq : 10 = i := by simpa [ls] using used
          subst i
          refine ⟨cap 10, fun x => ?_⟩
          change ((W x ++ [!(signal x a)]).getD 10 false || false) = _
          rw [lastWire, readCap x 10, missing]
        | cons j rest =>
          have hlen : rest = [] := by
            rw [ls] at lengthO
            simp only [List.length_cons] at lengthO
            apply List.length_eq_zero_iff.mp
            omega
          subst rest
          have opts : 10 = i ∨ 10 = j := by simpa [ls] using used
          have two (x : Fin 9 → Bool) (k : ℕ) :
              (!(signal x a) || (W x ++ [!(signal x a)]).getD k false) =
              (!(signal x a) || signal x (cap k)) := by
            rw [readCap x k, getPush x _ k]
            by_cases hk : k = 10
            · subst k
              rw [ite_eq_left rfl, missing]
              simp
            · rw [ite_eq_right hk]
          rcases opts with rfl | rfl
          · refine ⟨cap j, fun x => ?_⟩
            change ((W x ++ [!(signal x a)]).getD 10 false ||
              ((W x ++ [!(signal x a)]).getD j false || false)) = _
            simpa only [lastWire, Bool.or_false] using two x j
          · refine ⟨cap i, fun x => ?_⟩
            change ((W x ++ [!(signal x a)]).getD i false ||
              ((W x ++ [!(signal x a)]).getD 10 false || false)) = _
            rw [lastWire, Bool.or_false, Bool.or_comm]
            exact two x i
    obtain ⟨b,hb⟩ := dependent
    have h := bounded ⟨tail,out⟩ a b goodTail (fun x => by
      simpa only [inputs, ← hb x] using tailValue x)
    change 13 ≤ tail.length at h
    change 16 ≤ (g :: neg :: disj :: tail).length
    simp only [List.length_cons]
    omega
  · let swap (i : ℕ) := if i = 10 then 11 else if i = 11 then 10 else i
    let k := neg.inputs.headD 10
    let neg' : Gate := ⟨.not, [if k < 10 then k else 11]⟩
    let D : Circuit := ⟨g :: disj :: neg' :: tail.map (ren swap), swap out⟩
    have altOr (x : Fin 9 → Bool) (v : Bool) : val disj (W x ++ [v]) = val disj (W x) := by
      apply congrArg disj.op.eval
      apply List.map_congr_left
      intro i hi
      have hne : i ≠ 10 := by
        intro e
        exact used (e ▸ hi)
      rw [getPush x v i, ite_eq_right hne]
    have altNeg (x : Fin 9 → Bool) (v : Bool) : val neg' (W x ++ [v]) = !(signal x a) := by
      change (!((W x ++ [v]).getD (if k < 10 then k else 11) false)) = !(signal x (cap k))
      rw [readCap]
      by_cases h : k < 10
      · rw [ite_eq_left h, getPush, ite_eq_right (by omega)]
      · rw [ite_eq_right h, List.getD_eq_default _ _ (by simp [W]), List.getD_eq_default _ _ (by simp [W]; omega)]
    have validD : FanInTwo D := by
      intro h hh
      change h ∈ g :: disj :: neg' :: tail.map (ren swap) at hh
      simp only [List.mem_cons] at hh
      rcases hh with rfl | rfl | rfl | ht
      · exact good _ (by simp)
      · exact good _ (by simp)
      · exact ⟨by simp [neg'], by change 1 ≤ 2; decide⟩
      · exact model swap tail goodTail _ ht
    have firstD (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) := by
      change ((Circuit.mk (disj :: neg' :: tail.map (ren swap)) 0).wires
        (List.ofFn x ++ [val g (List.ofFn x)])).getD 9 false = _
      rw [gval, keep _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
      simp
    have pSmall (i : ℕ) (hi : i < 12) : swap i < 12 := by
      by_cases h : i = 10
      · simp [swap,h]
      · by_cases k : i = 11 <;> simp [swap,h,k,hi]
    have pFixed (i : ℕ) (hi : 12 ≤ i) : swap i = i := by simp [swap, show i ≠ 10 by omega, show i ≠ 11 by omega]
    have permState (x : Fin 9 → Bool) (v w : Bool) (i : ℕ) :
        ((W x ++ [w]) ++ [v]).getD (swap i) false = ((W x ++ [v]) ++ [w]).getD i false := by
      by_cases hi : i < 10
      · simp only [swap, ite_eq_right (show i ≠ 10 by omega), ite_eq_right (show i ≠ 11 by omega)]
        rw [List.getD_append (W x ++ [w]) [v] false i (by simp [W]; omega),
            List.getD_append (W x ++ [v]) [w] false i (by simp [W]; omega)]
        simp only [getPush x w i, getPush x v i, ite_eq_right (show i ≠ 10 by omega)]
      · by_cases hj : 12 ≤ i
        · rw [pFixed i hj, List.getD_eq_default _ _ (by simp [W]; omega),
            List.getD_eq_default _ _ (by simp [W]; omega)]
        · have hcases : i = 10 ∨ i = 11 := by omega
          rcases hcases with rfl | rfl <;> rfl
    have evalD (x : Fin 9 → Bool) : D.eval (List.ofFn x) = F x := by
      change (Circuit.mk (tail.map (ren swap)) (swap out)).eval
        (((List.ofFn x ++ [val g (List.ofFn x)]) ++ [val disj (List.ofFn x ++ [val g (List.ofFn x)])]) ++
        [val neg' ((List.ofFn x ++ [val g (List.ofFn x)]) ++ [val disj (List.ofFn x ++ [val g (List.ofFn x)])])]) = _
      rw [gval]
      change (Circuit.mk (tail.map (ren swap)) (swap out)).eval
        ((W x ++ [val disj (W x)]) ++ [val neg' (W x ++ [val disj (W x)])]) = _
      rw [altNeg]
      have hh := follow 12 swap pSmall pFixed tail
        ((W x ++ [!(signal x a)]) ++ [val disj (W x)])
        ((W x ++ [val disj (W x)]) ++ [!(signal x a)])
        (by simp [W]) (by simp [W]) (permState x _ _) out
      have ho := tailValue x
      rw [altOr] at ho
      exact hh.trans ho
    have sizeD := secondOr D validD firstD (funext evalD) (congrArg some oOp)
    change 16 ≤ (g :: disj :: neg' :: tail.map (ren swap)).length at sizeD
    change 16 ≤ (g :: neg :: disj :: tail).length
    simpa using sizeD
