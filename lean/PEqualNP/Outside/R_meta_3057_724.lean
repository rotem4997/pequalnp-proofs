import Mathlib
import PEqualNP.Defs

-- The input relabeling proof is adapted from visez, upstream L-meta-1664.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3057_724
    (lowBound : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 → ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x 4)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (degBound : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     x1 = [] ∨ x1.headD (10 : ℕ) = (0 : ℕ) ∨ (9 : ℕ) ≤ x1.headD (10 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (coreBound : ∀ j : Fin 9, j=1 ∨ j=2 ∨ j=3 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0),!(x j)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (512 : ℕ)),             have x7 : Fin (9 : ℕ) → Bool := fun (x7 : Fin (9 : ℕ)) => Decidable.decide (↑x6 / (2 : ℕ) ^ (↑x7 % (9 : ℕ)) % (2 : ℕ) = (1 : ℕ));             have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];             x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x9.1 && x7 x9.2 := by
  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩

  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit) : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
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

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)

  have rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
      Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
    refine ⟨by simp, by simp; omega, ?_⟩
    intro w
    unfold wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
  let X := Fin 9 → Bool
  let edge (x : X) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  let pair (x : X) (a b : Fin 9) : Fin 11 → Bool := fun w =>
    if h : w.val < 9 then x ⟨w.val,h⟩ else if w.val = 9 then !(x a) else !(x b)

  have ofPair (x : X) (a b : Fin 9) :
      List.ofFn (pair x a b) = List.ofFn x ++ [!(x a), !(x b)] := by rfl

  let move (p : Fin 9 → Fin 9) (swap : Bool) (u : Fin 11) : Fin 11 :=
    if h : u.val < 9 then ⟨(p ⟨u.val,h⟩).val, by have := (p ⟨u.val,h⟩).isLt; omega⟩
    else if swap then if u.val = 9 then 10 else 9 else u

  let disproved (a b : Fin 9) : Prop := ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : X, C.eval (List.ofFn (pair x a b)) ≠ edge x

  have transport (p : Fin 9 → Fin 9) (swap : Bool) (a b c d : Fin 9)
      (iso : ∀ x, edge (x ∘ p) = edge x)
      (align : ∀ x, pair x c d ∘ move p swap = pair (x ∘ p) a b)
      (lower : disproved c d) : disproved a b := by
    intro C good sz
    let q := move p swap
    let C' := relabel 11 11 q C
    have legal : PEqualNP.MetaComplexity.FanInTwo C' := by
      intro g hg
      obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg
      exact ⟨(good g0 h0).1,by simpa [relGate] using (good g0 h0).2⟩
    have small : C'.size ≤ 13 := by
      change (C.gates.map (relGate 11 11 q)).length ≤ 13
      rw [List.length_map]
      exact sz
    obtain ⟨x,h⟩ := lower C' legal small
    refine ⟨x ∘ p, ?_⟩
    have e := (rel_fold 11 11 q C.gates _ _ (rel_init 11 11 q (pair x c d))).2.2 C.output
    change C'.eval (List.ofFn (pair x c d)) = C.eval (List.ofFn (pair x c d ∘ move p swap)) at e
    rw [align] at e
    simpa only [iso,← e] using h

  let firstFour : Prop := ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
    ∃ x : X, D.eval (List.ofFn x ++ [!(x 4)]) ≠ edge x

  have fromFour (bound : firstFour) (j : Fin 9) : disproved 4 j := by
    intro D legal sz
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨⟨.not,[j.val]⟩ :: D.gates, D.output⟩
    have g : PEqualNP.MetaComplexity.FanInTwo C := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | h
      · simp
      · exact legal _ h
    have small : C.size ≤ 14 := by
      change D.gates.length+1 ≤ 14
      change D.gates.length ≤ 13 at sz
      omega
    obtain ⟨x,bad⟩ := bound C g small
    refine ⟨x,?_⟩
    have hj : (List.ofFn x ++ [!(x 4)]).getD j.val false = x j := by
      rw [List.getD_append _ _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp : j.val < (List.ofFn x).length), List.getElem_ofFn]
    have e : C.eval (List.ofFn x ++ [!(x 4)]) = D.eval (List.ofFn (pair x 4 j)) := by
      change (D.gates.foldl step ((List.ofFn x ++ [!(x 4)]) ++ [!((List.ofFn x ++ [!(x 4)]).getD j.val false)])).getD D.output false =
        (D.gates.foldl step (List.ofFn (pair x 4 j))).getD D.output false
      rw [hj,ofPair]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    simpa only [e] using bad

  have canonical (low : firstFour)
      (core : ∀ j : Fin 9, j=1 ∨ j=2 ∨ j=3 → disproved 0 j) :
      ∀ j : Fin 9, j ≠ 0 → disproved 0 j := by
    intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact core 1 (by decide)
    · exact core 2 (by decide)
    · exact core 3 (by decide)
    · let p : Fin 9 → Fin 9 := ![0,1,2,3,4,5,6,7,8]
      apply transport p true 0 4 4 0
      · intro x
        simp only [edge,Function.comp_apply,p]
        decide +revert +kernel
      · intro x
        funext i
        fin_cases i <;> rfl
      · exact fromFour low 0
    · let p : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
      apply transport p false 0 5 0 1
      · intro x
        simp only [edge,Function.comp_apply,p]
        decide +revert +kernel
      · intro x
        funext i
        fin_cases i <;> rfl
      · exact core 1 (by decide)
    · let p : Fin 9 → Fin 9 := ![1,0,5,8,6,2,4,7,3]
      apply transport p true 0 6 4 1
      · intro x
        simp only [edge,Function.comp_apply,p]
        decide +revert +kernel
      · intro x
        funext i
        fin_cases i <;> rfl
      · exact fromFour low 1
    · let p : Fin 9 → Fin 9 := ![1,2,3,8,6,0,7,4,5]
      apply transport p true 0 7 4 1
      · intro x
        simp only [edge,Function.comp_apply,p]
        decide +revert +kernel
      · intro x
        funext i
        fin_cases i <;> rfl
      · exact fromFour low 1
    · let p : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
      apply transport p false 0 8 0 2
      · intro x
        simp only [edge,Function.comp_apply,p]
        decide +revert +kernel
      · intro x
        funext i
        fin_cases i <;> rfl
      · exact core 2 (by decide)
  let bits (m : Fin 512) : Fin 9 → Bool := fun i => decide (m.val / 2^(i.val % 9) % 2 = 1)

  have rows (x : Fin 9 → Bool) : ∃ m : Fin 512, bits m = x := by
    let v := BitVec.ofBoolListLE (List.ofFn x)
    let m : Fin 512 := ⟨v.toNat, by simpa only [List.length_ofFn] using v.isLt⟩
    refine ⟨m,?_⟩
    funext i
    dsimp only [bits]
    rw [Nat.mod_eq_of_lt i.isLt,← Nat.testBit_eq_decide_div_mod_eq]
    change v.getLsbD i.val = x i
    rw [show v = BitVec.ofBoolListLE (List.ofFn x) from rfl, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem _ _ (by simp : i.val < (List.ofFn x).length),List.getElem_ofFn]

  let es : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

  have edge_any (x : Fin 9 → Bool) : es.any (fun z => x z.1 && x z.2) = edge x := by
    simp only [es,edge,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  have all := canonical lowBound (by
    intro j hj C good sz
    obtain ⟨x,h⟩ := coreBound j hj C good sz
    exact ⟨x,by simpa only [ofPair,edge] using h⟩)
  intro ls len C legal small
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [!(x 0)]
  let input (x : Fin 9 → Bool) := w x ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (ls.map fun i => (w x).getD i false)]
  have existsRow : ∃ x, C.eval (input x) ≠ edge x := by
    by_cases d : ls = [] ∨ ls.headD 10 = 0 ∨ 9 ≤ ls.headD 10
    · exact degBound ls len d C legal small
    · cases ls with
      | nil => simp at d
      | cons k tail =>
        simp only [List.headD_cons,List.cons_ne_nil,false_or,not_or] at d
        let j : Fin 9 := ⟨k,by omega⟩
        obtain ⟨x,hx⟩ := all j (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega) C legal small
        refine ⟨x,?_⟩
        have hj : (w x).getD k false = x j := by
          rw [show w x = (List.ofFn x ++ [!(x 0)]) from rfl, List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]
        change C.eval (w x ++ [!((w x).getD k false)]) ≠ edge x
        rw [hj]
        simpa only [ofPair,w,List.append_assoc,List.cons_append,List.nil_append] using hx
  obtain ⟨x,miss⟩ := existsRow
  obtain ⟨m,hm⟩ := rows x
  refine ⟨m,?_⟩
  change C.eval (input (bits m)) ≠ es.any (fun z => bits m z.1 && bits m z.2)
  rw [hm,edge_any]
  exact miss
