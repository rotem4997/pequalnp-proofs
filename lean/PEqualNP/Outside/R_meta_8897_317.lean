import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_8897_317
    (degreeOne : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x6 ∨ x9 = Fin.natAdd (13 : ℕ) x7)) = Bool.true) → ∃ (x7 : Finset (Fin (13 : ℕ))) (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∈ x7, ∀ x11 ∈ x8, ¬x1 x9 x11) ∧ (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x7 | x1 x10 x9}.card ≤ (2 : ℕ)) ∧ (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x8 | x1 x9 x10}.card ≤ (2 : ℕ)) ∧ (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x9 : Fin (26 : ℕ)) => Fin.addCases (fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x7)) (fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x8)) x9) = Bool.true)
    (exactTwo : ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C →
      C.lineDeg 26 (Finset.range 13) = 2 → 64 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size := by
  let pg (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

  let pc (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (pg σ), σ C.output⟩

  have key_getD {α : Type} (d : α) (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i)
      (init init' : List α) (hl : init.length = n) (hl' : init'.length = n)
      (hi : ∀ i, i < n → init'.getD (σ i) d = init.getD i d) (t0 : List α) (i : ℕ) :
      (init' ++ t0).getD (σ i) d = (init ++ t0).getD i d := by
    by_cases h : i < n
    · have e1 : (init' ++ t0).getD (σ i) d = init'.getD (σ i) d :=
        List.getD_append init' t0 d (σ i) (by rw [hl']; exact hσ1 i h)
      have e2 : (init ++ t0).getD i d = init.getD i d :=
        List.getD_append init t0 d i (by rw [hl]; exact h)
      rw [e1, e2]
      exact hi i h
    · have h' : n ≤ i := Nat.le_of_not_lt h
      have e1 : (init' ++ t0).getD i d = t0.getD (i - init'.length) d :=
        List.getD_append_right init' t0 d i (by rw [hl']; exact h')
      have e2 : (init ++ t0).getD i d = t0.getD (i - init.length) d :=
        List.getD_append_right init t0 d i (by rw [hl]; exact h')
      rw [hσ2 i h', e1, e2, hl, hl']

  have perm_fold {α : Type} (d : α) (S : Gate → List α → α) (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i)
      (hS : ∀ (g : Gate) (acc acc' : List α), (∀ i, acc'.getD (σ i) d = acc.getD i d) →
        S (pg σ g) acc' = S g acc)
      (init init' : List α) (hl : init.length = n) (hl' : init'.length = n)
      (hi : ∀ i, i < n → init'.getD (σ i) d = init.getD i d) (gs : List Gate) (t0 : List α) :
      ∃ t, gs.foldl (fun acc g => acc ++ [S g acc]) (init ++ t0) = init ++ t ∧
        (gs.map (pg σ)).foldl (fun acc g => acc ++ [S g acc]) (init' ++ t0) = init' ++ t := by
    induction gs generalizing t0 with
    | nil => exact ⟨t0, rfl, rfl⟩
    | cons g gs ih =>
      obtain ⟨t, h1, h2⟩ := ih (t0 ++ [S g (init ++ t0)])
      refine ⟨t, ?_, ?_⟩
      · simp only [List.foldl_cons]
        rw [List.append_assoc]
        exact h1
      · simp only [List.map_cons, List.foldl_cons]
        rw [hS g (init ++ t0) (init' ++ t0) (key_getD d σ n hσ1 hσ2 init init' hl hl' hi t0),
          List.append_assoc]
        exact h2

  have pc_eval (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i) (C : Circuit)
      (x x' : List Bool) (hl : x.length = n) (hl' : x'.length = n)
      (hi : ∀ i, i < n → x'.getD (σ i) false = x.getD i false) :
      (pc σ C).eval x' = C.eval x := by
    have hS : ∀ (g : Gate) (acc acc' : List Bool),
        (∀ i, acc'.getD (σ i) false = acc.getD i false) →
        (pg σ g).op.eval ((pg σ g).inputs.map fun i => acc'.getD i false) =
          g.op.eval (g.inputs.map fun i => acc.getD i false) := by
      intro g acc acc' h
      show g.op.eval ((g.inputs.map σ).map fun i => acc'.getD i false) = _
      rw [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => h i)
    obtain ⟨t, h1, h2⟩ := perm_fold false
      (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)) σ n hσ1 hσ2 hS x x' hl hl' hi
      C.gates []
    rw [List.append_nil] at h1 h2
    have e1 : C.wires x = x ++ t := h1
    have e2 : (pc σ C).wires x' = x' ++ t := h2
    unfold Circuit.eval
    rw [e1, e2]
    exact key_getD false σ n hσ1 hσ2 x x' hl hl' hi t C.output

  have init_getD (n : ℕ) (m : Finset ℕ) (i : ℕ) (h : i < n) :
      ((List.range n).map fun i => if i ∈ m then 1 else 0).getD i 0 = if i ∈ m then 1 else 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
    rfl

  have pc_deg (σ : ℕ → ℕ) (n : ℕ)
      (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i) (C : Circuit)
      (m m' : Finset ℕ) (hmk : ∀ i, i < n → (i ∈ m ↔ σ i ∈ m')) :
      (pc σ C).lineDeg n m' = C.lineDeg n m := by
    have hS : ∀ (g : Gate) (acc acc' : List ℕ),
        (∀ i, acc'.getD (σ i) 0 = acc.getD i 0) →
        (pg σ g).lineDegree acc' = g.lineDegree acc := by
      intro g acc acc' h
      have hmm : ((pg σ g).inputs.map fun i => acc'.getD i 0) =
          (g.inputs.map fun i => acc.getD i 0) := by
        show ((g.inputs.map σ).map fun i => acc'.getD i 0) = _
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => h i)
      unfold Gate.lineDegree
      rw [hmm]
    have hi : ∀ i, i < n →
        ((List.range n).map fun i => if i ∈ m' then 1 else 0).getD (σ i) 0 =
          ((List.range n).map fun i => if i ∈ m then 1 else 0).getD i 0 := by
      intro i h
      rw [init_getD n m' (σ i) (hσ1 i h), init_getD n m i h]
      by_cases hm : i ∈ m
      · rw [ite_eq_left hm, ite_eq_left ((hmk i h).mp hm)]
      · rw [ite_eq_right hm, ite_eq_right (fun h' => hm ((hmk i h).mpr h'))]
    have hl : ((List.range n).map fun i => if i ∈ m then 1 else 0).length = n := by simp
    have hl' : ((List.range n).map fun i => if i ∈ m' then 1 else 0).length = n := by simp
    obtain ⟨t, h1, h2⟩ := perm_fold 0 (fun g dd => g.lineDegree dd) σ n hσ1 hσ2 hS _ _ hl hl' hi
      C.gates []
    rw [List.append_nil] at h1 h2
    have e1 : C.lineDegrees n m = ((List.range n).map fun i => if i ∈ m then 1 else 0) ++ t := h1
    have e2 : (pc σ C).lineDegrees n m' =
        ((List.range n).map fun i => if i ∈ m' then 1 else 0) ++ t := h2
    unfold Circuit.lineDeg
    rw [e1, e2]
    exact key_getD 0 σ n hσ1 hσ2 _ _ hl hl' hi t C.output

  have pc_mono (σ : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (pc σ C) := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := h g0 hg0
    refine ⟨h0.1, ?_⟩
    show (g0.inputs.map σ).length ≤ 2
    rw [List.length_map]
    exact h0.2

  have pc_size (σ : ℕ → ℕ) (C : Circuit) : (pc σ C).size = C.size := by
    exact List.length_map _

  let sw (i : ℕ) : ℕ :=
    if i < 13 then 13 + (13 - i) % 13 else if i < 26 then (26 - i) % 13 else i

  have sw_lt (i : ℕ) (h : i < 26) : sw i < 26 := by
    unfold sw; split_ifs <;> omega

  have sw_ge (i : ℕ) (h : 26 ≤ i) : sw i = i := by
    unfold sw; split_ifs <;> omega

  let dualIn (x : Fin 26 → Bool) : Fin 26 → Bool := fun k => x ⟨sw k.val, sw_lt k.val k.isLt⟩

  have dual_eval (C : Circuit) (x : Fin 26 → Bool) :
      circuitFun 26 (pc sw C) x = circuitFun 26 C (dualIn x) := by
    show (pc sw C).eval (List.ofFn x) = C.eval (List.ofFn (dualIn x))
    refine pc_eval sw 26 sw_lt sw_ge C (List.ofFn (dualIn x)) (List.ofFn x) (by simp) (by simp) ?_
    intro i h
    simp only [List.getD, List.getElem?_ofFn, dite_eq_left (sw_lt i h), dite_eq_left h, Option.getD_some, dualIn]

  have sw_mark_rev (i : ℕ) (h : i < 26) :
      (i ∈ Finset.Ico 13 26 ↔ sw i ∈ Finset.range 13) := by
    rw [Finset.mem_range, Finset.mem_Ico]
    unfold sw
    split_ifs <;> omega

  have dual_deg_rev (C : Circuit) (D : ℕ) :
      HasLineDegree 26 (Finset.range 13) (pc sw C) D ↔
      HasLineDegree 26 (Finset.Ico 13 26) C D := by
    unfold HasLineDegree
    rw [pc_deg sw 26 sw_lt sw_ge C (Finset.Ico 13 26) (Finset.range 13) sw_mark_rev]

  have sw_cast : ∀ q : Fin 13,
      sw (Fin.castAdd 13 q : Fin 26).val = (Fin.natAdd 13 (-q) : Fin 26).val := by unfold sw; decide

  have sw_nat : ∀ l : Fin 13,
      sw (Fin.natAdd 13 l : Fin 26).val = (Fin.castAdd 13 (-l) : Fin 26).val := by unfold sw; decide

  have dualIn_cast (z : Fin 26 → Bool) (q : Fin 13) :
      dualIn z (Fin.castAdd 13 q) = z (Fin.natAdd 13 (-q)) := by
    show z ⟨sw (Fin.castAdd 13 q : Fin 26).val, _⟩ = _
    exact congrArg z (Fin.ext (sw_cast q))

  have dualIn_nat (z : Fin 26 → Bool) (l : Fin 13) :
      dualIn z (Fin.natAdd 13 l) = z (Fin.castAdd 13 (-l)) := by
    show z ⟨sw (Fin.natAdd 13 l : Fin 26).val, _⟩ = _
    exact congrArg z (Fin.ext (sw_nat l))



  let turn (T : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter (fun p => -p ∈ T)

  let vec (X Y : Finset (Fin 13)) : Fin 26 → Bool :=
    Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

  have vecInput (X Y : Finset (Fin 13)) : List.ofFn (vec X Y) = incidenceInput X Y := by
    exact List.ofFn_fin_append _ _

  have flipVec (X Y : Finset (Fin 13)) : dualIn (vec X Y) = vec (turn Y) (turn X) := by
    funext i
    refine Fin.addCases (m := 13) (n := 13) (fun u => ?_) (fun v => ?_) i
    · rw [dualIn_cast]
      simp only [vec,Fin.append_left,Fin.append_right,turn,Finset.mem_filter,Finset.mem_univ,true_and]
    · rw [dualIn_nat]
      simp only [vec,Fin.append_left,Fin.append_right,turn,Finset.mem_filter,Finset.mem_univ,true_and]

  have flipInc : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ -l ∈ singerLines3 (-p) := by
    decide +kernel

  let I (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  have memI : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ I p l := by unfold I; decide +kernel
  have singletonVec (p l : Fin 13) :
      vec {p} {l} = fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) := by
    funext i
    unfold vec
    revert p l i
    decide +kernel
  have memTurn (T : Finset (Fin 13)) (p : Fin 13) : p ∈ turn T ↔ -p ∈ T := by simp [turn]

  have flipValue (X Y : Finset (Fin 13)) :
      incidenceFun singerLines3 (turn Y) (turn X) = incidenceFun singerLines3 X Y := by
    unfold incidenceFun
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,memTurn]
    constructor
    · rintro ⟨p,hp,l,hl,hi⟩
      exact ⟨-l,hl,-p,hp,(flipInc p l).mp hi⟩
    · rintro ⟨p,hp,l,hl,hi⟩
      exact ⟨-l,by simpa using hl,-p,by simpa using hp,(flipInc p l).mp hi⟩

  have dualComputes (C : Circuit) (h : ComputesIncidence singerLines3 C) :
      ComputesIncidence singerLines3 (pc sw C) := by
    intro X Y
    rw [←vecInput]
    change circuitFun 26 (pc sw C) (vec X Y) = _
    rw [dual_eval,flipVec]
    change C.eval (List.ofFn (vec (turn Y) (turn X))) = _
    rw [vecInput,h,flipValue]

  have lower (C : Circuit) (hm : Monotone2 C) (hc : ComputesIncidence singerLines3 C)
      (hd : HasLineDegree 26 (Finset.range 13) C 2) : 64 ≤ C.size := by
    unfold HasLineDegree at hd
    by_cases h2 : C.lineDeg 26 (Finset.range 13) = 2
    · exact exactTwo C hm hc h2
    by_contra! small
    have h1 : HasLineDegree 26 (Finset.range 13) C 1 := by
      unfold HasLineDegree
      omega
    obtain ⟨X,Y,hApart,_,_,hot⟩ := degreeOne C hm (by omega) h1 (by
      intro p l hinc
      rw [←singletonVec]
      change C.eval (List.ofFn (vec {p} {l})) = true
      rw [vecInput,hc]
      change decide (∃ u ∈ ({p} : Finset _), ∃ v ∈ ({l} : Finset _), u ∈ singerLines3 v) = true
      simpa using (memI p l).mpr hinc)
    have cold : incidenceFun singerLines3 X Y = false := by
      unfold incidenceFun
      apply decide_eq_false
      rintro ⟨p,hp,l,hl,hi⟩
      exact hApart p hp l hl ((memI p l).mp hi)
    change C.eval (List.ofFn (vec X Y)) = true at hot
    rw [vecInput,hc,cold] at hot
    contradiction
  intro C hm hc hd
  rcases hd with h | h
  · have hs := lower (pc sw C) (pc_mono sw C hm)
      (dualComputes C hc) ((dual_deg_rev C 2).mpr h)
    simpa only [pc_size] using hs
  · exact lower C hm hc h
