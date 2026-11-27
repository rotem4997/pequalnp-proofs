import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each vertex deletion is one of two eight-input problems. The gate budget
-- charges the two initial gates separately on each slice.
-- The compaction induction below adapts the wire simulation in R_meta_1673_2.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_2758_481
    (full : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 15 ≤ D.size)
    (degreeThree : ∀ s : ℕ, HasCircuitSize 8 (fun y : Fin 8 → Bool => ([(0,1),(0,5),(1,2),(1,6),(2,3),(2,7),(4,6),(4,7),(5,7)] : List (Fin 8 × Fin 8)).any (fun e => y e.1 && y e.2)) s → 12 ≤ s)
    (degreeTwo : ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) || (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)) 12)
    (rigid : ∀ (neg : Bool) (p : Fin 10) (C : Circuit), FanInTwo C → C.size = 13 →
      let input := (fun x : Fin 9 → Bool => let u := List.ofFn x ++ [!x 0]; u ++ [(if neg then !x 0 else x 0) || u.getD p.val false])
      (∀ (v : Fin 9) (S : Finset ℕ),
        (∀ j ∈ S, j < 13 ∧
          ((∃ b : Bool, ∀ x, x v = false → (C.wires (input x)).getD (11+j) false = b) ∨
           (∃ i < 11+j, ∀ x, x v = false →
              (C.wires (input x)).getD (11+j) false = (C.wires (input x)).getD i false))) →
        S.card + (if v = 0 then 2 else if p.val = 0 ∨ p.val = 9 ∨ p = v.castSucc then 1 else 0) +
          (if v = 4 ∨ v = 6 ∨ v = 7 then 13 else 12) ≤ 15) →
      ∃ x, C.eval (input x) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins plen valid marked C fan budget
  obtain ⟨a,b,rfl⟩ : ∃ a b : ℕ, pins = [a,b] := by
    cases pins with
    | nil => simp at plen
    | cons a t =>
      cases t with
      | nil => simp at plen
      | cons b t =>
        have ht : t.length = 0 := by simpa using plen
        exact ⟨a,b,by rw [List.length_eq_zero_iff.mp ht]⟩
  let pre := fun x : Fin 9 → Bool => List.ofFn x ++ [!x 0]
  have get0 (x : Fin 9 → Bool) : (pre x).getD 0 false = x 0 := by
    rw [List.getD_append _ _ _ _ (by simp)]
    exact List.getD_eq_getElem _ _ (by simp) |>.trans (List.getElem_ofFn _)
  have get9 (x : Fin 9 → Bool) : (pre x).getD 9 false = !x 0 := by simp [pre]
  obtain ⟨neg,p,hpins⟩ : ∃ (neg : Bool) (p : Fin 10), ∀ x,
      GateOp.or.eval ([a,b].map fun i => (pre x).getD i false) =
        ((if neg then !x 0 else x 0) || (pre x).getD p.val false) := by
    have ha := valid a (by simp)
    have hb := valid b (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at marked
    rcases marked with (h|h)|(h|h)
    · exact ⟨false,⟨b,hb⟩,fun x => by change ((pre x).getD a false || ((pre x).getD b false || false)) = _; rw [← h,get0]; simp⟩
    · exact ⟨false,⟨a,ha⟩,fun x => by change ((pre x).getD a false || ((pre x).getD b false || false)) = _; rw [← h,get0]; simp [Bool.or_comm]⟩
    · exact ⟨true,⟨b,hb⟩,fun x => by change ((pre x).getD a false || ((pre x).getD b false || false)) = _; rw [← h,get9]; simp⟩
    · exact ⟨true,⟨a,ha⟩,fun x => by change ((pre x).getD a false || ((pre x).getD b false || false)) = _; rw [← h,get9]; simp [Bool.or_comm]⟩
  let input := (fun x : Fin 9 → Bool => let u := List.ofFn x ++ [!x 0]; u ++ [(if neg then !x 0 else x 0) || u.getD p.val false])
  by_contra! bad
  let fst : Gate := ⟨.not,[0]⟩
  let snd : Gate := ⟨.or,[a,b]⟩
  let D : Circuit := ⟨fst::snd::C.gates,C.output⟩
  let F := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have initial (x) : step (step (List.ofFn x) fst) snd = input x := by
    have rd : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp)]; exact List.getElem_ofFn _
    have hn : step (List.ofFn x) fst = pre x := by
      change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
      rw [rd]
    rw [hn]
    change pre x ++ [GateOp.or.eval ([a,b].map _)] = _
    rw [hpins]
  have wires (x) : D.wires (List.ofFn x) = C.wires (input x) := by
    change C.gates.foldl step (step (step (List.ofFn x) fst) snd) = _
    rw [initial]; rfl
  have hFan : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|ht
    · simp [fst]
    rcases List.mem_cons.mp ht with rfl|ht
    · simp [snd]
    exact fan g ht
  have agree (x) : C.eval (input x) = F x := by
    have hc := Classical.not_not.mp (bad x)
    change C.eval (pre x ++ [GateOp.or.eval ([a,b].map _)]) = _ at hc
    rw [hpins] at hc
    exact hc
  have same : circuitFun 9 D = F := by
    funext x
    change (D.wires (List.ofFn x)).getD C.output false = _
    rw [wires]; exact agree x
  have total := full D hFan same
  change 15 ≤ C.gates.length + 2 at total
  change C.gates.length ≤ 13 at budget
  have exactSize : C.gates.length = 13 := by omega
  have dlen : D.gates.length = 15 := by change C.gates.length + 2 = 15; omega
  refine (rigid neg p C fan exactSize ?_).elim fun x h => h (agree x)
  intro v S hS
  let penalty := if v = 4 ∨ v = 6 ∨ v = 7 then 13 else 12
  let credit := if v = 0 then 2 else if p.val = 0 ∨ p.val = 9 ∨ p = v.castSucc then 1 else 0
  let removable (k : ℕ) :=
    (∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → (D.wires (List.ofFn x)).getD (9+k) false = b) ∨
    (∃ i < 9+k, ∀ x : Fin 9 → Bool, x v = false →
      (D.wires (List.ofFn x)).getD (9+k) false = (D.wires (List.ofFn x)).getD i false)
  have eliminate (T : Finset ℕ) (hT : ∀ j ∈ T, j < D.gates.length ∧ removable j) :
      T.card + penalty ≤ 15 := by
    let H := if v = 4 ∨ v = 6 ∨ v = 7 then (fun y : Fin 8 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) || (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)) else (fun y : Fin 8 → Bool => ([(0,1),(0,5),(1,2),(1,6),(2,3),(2,7),(4,6),(4,7),(5,7)] : List (Fin 8 × Fin 8)).any (fun e => y e.1 && y e.2))
    have lower (s : ℕ) (hs : HasCircuitSize 8 H s) : penalty ≤ s := by
      by_cases low : v = 4 ∨ v = 6 ∨ v = 7
      · simp only [penalty,if_pos low]
        by_contra! h
        obtain ⟨E,he,hsize,hh⟩ := hs
        apply degreeTwo
        exact ⟨E,he,by omega,by simpa [H,low] using hh⟩
      · simpa [penalty,low] using degreeThree s (by simpa [H,low] using hs)
    obtain ⟨τ,hτ⟩ : ∃ τ : Fin 9 → Fin 8, ∀ y : Fin 8 → Bool,
        F (fun i => if i = v then false else y (τ i)) = H y := by
      fin_cases v
      · exact ⟨![0, 0, 1, 2, 3, 4, 5, 6, 7], by decide +kernel⟩
      · exact ⟨![0, 0, 4, 7, 5, 1, 3, 6, 2], by decide +kernel⟩
      · exact ⟨![1, 0, 0, 4, 6, 2, 5, 3, 7], by decide +kernel⟩
      · exact ⟨![2, 1, 0, 0, 3, 7, 6, 5, 4], by decide +kernel⟩
      · exact ⟨![0, 1, 2, 3, 0, 4, 5, 6, 7], by decide +kernel⟩
      · exact ⟨![0, 1, 2, 7, 5, 0, 6, 3, 4], by decide +kernel⟩
      · exact ⟨![1, 0, 4, 7, 5, 2, 0, 6, 3], by decide +kernel⟩
      · exact ⟨![1, 2, 3, 7, 5, 0, 6, 0, 4], by decide +kernel⟩
      · exact ⟨![1, 2, 7, 4, 6, 0, 3, 5, 0], by decide +kernel⟩
    let X : (Fin 8 → Bool) → Fin 9 → Bool := fun y i => if i = v then false else y (τ i)
    have hXv (y) : X y v = false := by simp [X]
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
    have last (w : List Bool) (b : Bool) (n : ℕ) (hn : w.length = n) :
        (w ++ [b]).getD n false = b := by
      subst hn
      simp [List.getD_eq_getElem?_getD]
    have beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    have getOf (n : ℕ) (y : Fin n → Bool) (m : Fin n) : (List.ofFn y).getD m.val false = y m := by
      simp [List.getD_eq_getElem?_getD]
    let W : (Fin 8 → Bool) → List Bool := fun y => D.wires (List.ofFn (X y))
    let N : List Gate → (Fin 8 → Bool) → List Bool := fun gs y => gs.foldl step (List.ofFn y)
    have hNlen (gs y) : (N gs y).length = 8 + gs.length := by simp [N, lengthOf]
    have hWlen (y) : (W y).length = 9 + D.gates.length := by
      change (D.gates.foldl step (List.ofFn (X y))).length = _
      simp [lengthOf]
    have keepN (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < 8 + gs.length) (y) :
        (N (gs ++ [g]) y).getD i false = (N gs y).getD i false := by
      simp only [N, List.foldl_append]
      exact keep [g] _ i (by simpa [lengthOf] using hi)
    have newN (gs : List Gate) (g : Gate) (y) :
        (N (gs ++ [g]) y).getD (8 + gs.length) false =
          g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
      simp only [N, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact last _ _ _ (by simp [lengthOf])
    have gateW (k : ℕ) (hk : k < D.gates.length) (y) :
        (W y).getD (9 + k) false =
          (D.gates[k]).op.eval ((D.gates[k]).inputs.map fun i =>
            if i < 9 + k then (W y).getD i false else false) := by
      have hsplit : D.gates = D.gates.take k ++ D.gates[k] :: D.gates.drop (k + 1) := by simp
      let P := (D.gates.take k).foldl step (List.ofFn (X y))
      have hP : P.length = 9 + k := by simp [P, lengthOf]; omega
      have hW : W y = (D.gates.drop (k + 1)).foldl step (step P D.gates[k]) := by
        change D.gates.foldl step (List.ofFn (X y)) = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hlow (i : ℕ) (hi : i < 9 + k) : (W y).getD i false = P.getD i false := by
        rw [hW, keep _ _ _ (by simp [step]; omega)]
        simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hP ▸ hi)]
      rw [hW, keep _ _ _ (by simp [step]; omega)]
      have h1 : (step P D.gates[k]).getD (9 + k) false =
          (D.gates[k]).op.eval ((D.gates[k]).inputs.map fun i => P.getD i false) :=
        last _ _ _ hP
      rw [h1, ← hW]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with hi
      · exact (hlow i hi).symm
      · exact beyond _ _ (by omega)
    let Good : List Gate → ℕ → Prop := fun gs i =>
      (∃ b : Bool, ∀ y, (W y).getD i false = b) ∨
      (∃ i' < 8 + gs.length, ∀ y, (W y).getD i false = (N gs y).getD i' false)
    have main (k : ℕ) (hk : k ≤ D.gates.length) : ∃ gs : List Gate,
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2) ∧
        gs.length + (T.filter (· < k)).card ≤ k ∧ ∀ i < 9 + k, Good gs i := by
      induction k with
      | zero =>
        refine ⟨[], by simp, by simp, fun i hi => ?_⟩
        have hi9 : i < 9 := by omega
        have hval (y) : (W y).getD i false = X y ⟨i, hi9⟩ := by
          change (D.gates.foldl step (List.ofFn (X y))).getD i false = _
          rw [keep _ _ _ (by simpa using hi9)]
          exact getOf 9 (X y) ⟨i, hi9⟩
        by_cases hiv : (⟨i, hi9⟩ : Fin 9) = v
        · exact Or.inl ⟨false, fun y => by rw [hval, hiv, hXv]⟩
        · refine Or.inr ⟨(τ ⟨i, hi9⟩).val, by simp, fun y => ?_⟩
          rw [hval]
          simp only [N, List.foldl_nil, getOf, X, if_neg hiv]
      | succ k ih =>
        have hk' : k < D.gates.length := by omega
        obtain ⟨gs, hfan, hcount, hgood⟩ := ih (by omega)
        have hfilter : (T.filter (· < k + 1)).card ≤ (T.filter (· < k)).card + 1 := by
          have hsub : T.filter (· < k + 1) ⊆ insert k (T.filter (· < k)) := by
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_insert] at ha ⊢
            rcases Nat.lt_succ_iff_lt_or_eq.mp ha.2 with h | h
            · exact Or.inr ⟨ha.1, h⟩
            · exact Or.inl h
          exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        by_cases hG : Good gs (9 + k)
        · refine ⟨gs, hfan, by omega, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (9 + k) + 1 by omega) with h | h
          · exact hgood i h
          · exact h ▸ hG
        have notConst (b : Bool) : ¬ ∀ y, (W y).getD (9 + k) false = b :=
          fun h => hG (Or.inl ⟨b, h⟩)
        have notAlias (i : ℕ) (hi : i < 9 + k) :
            ¬ ∀ y, (W y).getD (9 + k) false = (W y).getD i false := by
          intro h
          rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
          · exact hG (Or.inl ⟨b, fun y => (h y).trans (hb y)⟩)
          · exact hG (Or.inr ⟨i', hi', fun y => (h y).trans (hb y)⟩)
        have hkS : k ∉ T := by
          intro hmem
          rcases (hT k hmem).2 with ⟨b, hb⟩ | ⟨i, hi, hb⟩
          · exact notConst b fun y => hb (X y) (hXv y)
          · exact notAlias i hi fun y => hb (X y) (hXv y)
        have hfilter' : T.filter (· < k + 1) = T.filter (· < k) := by
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
            · exact h
            · exact absurd (h ▸ h1) hkS
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by omega⟩
        let val : ℕ → (Fin 8 → Bool) → Bool := fun i y =>
          if i < 9 + k then (W y).getD i false else false
        have valCases (i : ℕ) : (∃ b : Bool, ∀ y, val i y = b) ∨
            (i < 9 + k ∧ ∃ i' < 8 + gs.length, ∀ y, val i y = (N gs y).getD i' false) := by
          by_cases hi : i < 9 + k
          · rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
            · exact Or.inl ⟨b, fun y => by simp only [val, if_pos hi]; exact hb y⟩
            · exact Or.inr ⟨hi, i', hi', fun y => by simp only [val, if_pos hi]; exact hb y⟩
          · exact Or.inl ⟨false, fun y => by simp only [val, if_neg hi]⟩
        have notVal (i : ℕ) : ¬ ∀ y, (W y).getD (9 + k) false = val i y := by
          intro h
          by_cases hi : i < 9 + k
          · exact notAlias i hi fun y => by rw [h y]; simp only [val, if_pos hi]
          · exact notConst false fun y => by rw [h y]; simp only [val, if_neg hi]
        have build : ∃ g : Gate, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2) ∧ ∀ y, (W y).getD (9 + k) false =
              g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
          have hgate := gateW k hk'
          obtain ⟨hop, hlen⟩ := hFan _ (List.getElem_mem hk')
          generalize D.gates[k] = g at hgate hop hlen
          obtain ⟨op, ins⟩ := g
          have hg (y) : (W y).getD (9 + k) false = op.eval (ins.map fun i => val i y) := hgate y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
          · exact absurd (fun y => hg y) (notConst (op.eval []))
          · rcases hop with rfl | rfl | rfl
            · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot]) (notVal a)
            · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot]) (notVal a)
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst (!b))
              · exact ⟨⟨.not, [a']⟩, by simp, fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, ha']⟩
          · rcases hop with rfl | rfl | rfl
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst false)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal c)
              rcases valCases c with ⟨b, hb⟩ | ⟨_, c', _, hc'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst false)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal a)
              exact ⟨⟨.and, [a', c']⟩, by simp, fun y => by
                rw [hg y]; simp [evalAnd, evalOr, evalNot, ha', hc']⟩
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal c)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst true)
              rcases valCases c with ⟨b, hb⟩ | ⟨_, c', _, hc'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal a)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst true)
              exact ⟨⟨.or, [a', c']⟩, by simp, fun y => by
                rw [hg y]; simp [evalAnd, evalOr, evalNot, ha', hc']⟩
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst (!b))
              · exact ⟨⟨.not, [a']⟩, by simp, fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, ha']⟩
          · simp at hlen
        obtain ⟨g, hgfan, hgval⟩ := build
        refine ⟨gs ++ [g], ?_, ?_, fun i hi => ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h | h
          · exact hfan g' h
          · rw [List.mem_singleton.mp h]; exact hgfan
        · rw [hfilter']; simp; omega
        · rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (9 + k) + 1 by omega) with h | h
          · rcases hgood i h with ⟨b, hb⟩ | ⟨i', hi', hb⟩
            · exact Or.inl ⟨b, hb⟩
            · exact Or.inr ⟨i', by simp; omega, fun y => by rw [keepN gs g i' hi', hb y]⟩
          · subst h
            exact Or.inr ⟨8 + gs.length, by simp, fun y => by rw [newN, hgval y]⟩
    obtain ⟨gs, hfan, hcount, hgood⟩ := main D.gates.length le_rfl
    have hall : T.filter (· < D.gates.length) = T :=
      Finset.filter_true_of_mem fun j hj => (hT j hj).1
    rw [hall] at hcount
    have hout (y) : (W y).getD D.output false = H y := by
      rw [← hτ y]
      exact congrFun same (X y)
    have nonconst (b : Bool) : ¬ ∀ y, (W y).getD D.output false = b := by
      intro h
      have h0 : H (fun _ => false) = b := (hout fun _ => false).symm.trans (h fun _ => false)
      have h1 : H (fun _ => true) = b := (hout fun _ => true).symm.trans (h fun _ => true)
      have h2 : H (fun _ => false) = false := by dsimp only [H]; split <;> decide
      have h3 : H (fun _ => true) = true := by dsimp only [H]; split <;> decide
      rw [h2] at h0
      rw [h3] at h1
      exact absurd (h0.trans h1.symm) (by decide)
    have hsize : D.size = D.gates.length := rfl
    by_cases ho : D.output < 9 + D.gates.length
    · rcases hgood D.output ho with ⟨b, hb⟩ | ⟨o, _, hb⟩
      · exact (nonconst b hb).elim
      · have := lower gs.length ⟨⟨gs, o⟩, hfan, le_rfl, fun y =>
          (hb y).symm.trans (hout y)⟩
        omega
    · exact (nonconst false fun y => beyond _ _ (by rw [hWlen]; omega)).elim
  let tail := S.image (fun j => j+2)
  have tailCard : tail.card = S.card := Finset.card_image_of_injective _ (fun _ _ e => by omega)
  have tailOK (j : ℕ) (hj : j ∈ tail) : j < D.gates.length ∧ removable j := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨ks,h⟩ := hS k hk
    refine ⟨by omega, ?_⟩
    dsimp only [removable]
    simp only [wires,show 9+(k+2) = 11+k by omega]
    exact h
  have neither (j : ℕ) (hj : j < 2) : j ∉ tail := by
    intro h
    obtain ⟨k,_,e⟩ := Finset.mem_image.mp h
    omega
  have evalWire (i : ℕ) (hi : i < 11) (x) :
      (D.wires (List.ofFn x)).getD i false = (input x).getD i false := by
    rw [wires]
    change (C.gates.foldl step (input x)).getD i false = _
    have keep (gs : List Gate) (w : List Bool) (hw : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hw
    exact keep _ _ (by simpa [input] using hi)
  have initialRaw (i : Fin 9) (x) : (D.wires (List.ofFn x)).getD i.val false = x i := by
    rw [evalWire _ (by omega)]
    change ((pre x) ++ [_]).getD i.val false = _
    rw [List.getD_append _ _ _ _ (by simp [pre]; omega)]
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]; exact List.getElem_ofFn _
  have zeroVal (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 0 false = x 0 := initialRaw 0 x
  have firstVal (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = !x 0 := by
    rw [evalWire _ (by decide)]
    change ((pre x) ++ [_]).getD 9 false = _
    rw [List.getD_append _ _ _ _ (by simp [pre]),get9]
  have secondVal (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 10 false =
      ((if neg then !x 0 else x 0) || (pre x).getD p.val false) := by
    rw [evalWire _ (by decide)]
    simp [input,pre,List.getD_eq_getElem?_getD,List.getElem?_append]
  have pinVal (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD p.val false = (pre x).getD p.val false := by
    rw [evalWire _ (by omega)]
    exact List.getD_append _ _ _ _ (by simp [pre])
  have marker (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD (if neg then 9 else 0) false =
      (if neg then !x 0 else x 0) := by
    cases neg
    · exact initialRaw 0 x
    · exact firstVal x
  have rem1 (h : v = 0 ∨ p.val = 0 ∨ p.val = 9 ∨ p = v.castSucc) : removable 1 := by
    dsimp only [removable]
    rcases h with hv | h0 | h9 | hv
    · subst v
      cases neg
      · exact Or.inr ⟨p.val,by omega,fun x hx => by rw [secondVal,pinVal,hx]; simp⟩
      · exact Or.inl ⟨true,fun x hx => by rw [secondVal,hx]; simp⟩
    · cases neg
      · exact Or.inr ⟨0,by decide,fun x _ => by rw [secondVal,h0,get0,zeroVal]; simp⟩
      · exact Or.inl ⟨true,fun x _ => by rw [secondVal,h0,get0]; cases x 0 <;> rfl⟩
    · cases neg
      · exact Or.inl ⟨true,fun x _ => by rw [secondVal,h9,get9]; cases x 0 <;> rfl⟩
      · exact Or.inr ⟨9,by decide,fun x _ => by rw [secondVal,h9,get9,firstVal]; simp⟩
    · refine Or.inr ⟨if neg then 9 else 0, by cases neg <;> decide, fun x hx => ?_⟩
      have ep : (pre x).getD p.val false = x v := by
        have e : p.val = v.val := congrArg Fin.val hv
        rw [← pinVal,e,initialRaw]
      rw [secondVal,marker,ep,hx,Bool.or_false]
  change S.card + credit + penalty ≤ 15
  by_cases hv : v = 0
  · have r0 : removable 0 := Or.inl ⟨true,fun x hx => by
      change (D.wires _).getD 9 false = true
      rw [firstVal,← hv,hx]; rfl⟩
    have h := eliminate (insert 0 (insert 1 tail)) (by
      intro j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | rfl | ht
      · exact ⟨by omega,r0⟩
      · exact ⟨by omega,rem1 (Or.inl hv)⟩
      · exact tailOK _ ht)
    have n0 : 0 ∉ insert 1 tail := by simp [neither 0 (by decide)]
    rw [Finset.card_insert_of_notMem n0,Finset.card_insert_of_notMem (neither 1 (by decide)),tailCard] at h
    simp only [credit,if_pos hv]; omega
  · by_cases hp : p.val = 0 ∨ p.val = 9 ∨ p = v.castSucc
    · have h := eliminate (insert 1 tail) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | ht
        · exact ⟨by omega,rem1 (Or.inr hp)⟩
        · exact tailOK _ ht)
      rw [Finset.card_insert_of_notMem (neither 1 (by decide)),tailCard] at h
      simpa only [credit,if_neg hv,if_pos hp] using h
    · have h := eliminate tail tailOK
      simpa only [credit,if_neg hv,if_neg hp,tailCard,Nat.add_zero] using h
