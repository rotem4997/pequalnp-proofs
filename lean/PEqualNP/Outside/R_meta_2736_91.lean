import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first hypothesis is the checked nine-input bound L_meta_2317.
-- The graph symmetries, input relabeling and removal of a redundant second gate are proved below.
-- The last hypothesis has sixteen representatives for a binary OR that supplies a new signal.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2736_91
    (ordinary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (binaryCases : ∀ (C : Circuit) (a b : Fin 11), FanInTwo C →
      11*a.val+b.val ∈ ([1,2,3,4,6,13,15,16,17,18,19,20,50,53,73,75] : List ℕ) →
      let f := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let pre := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 && x 3]
      let read4 := fun (g : Gate) => g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4
      (∀ x, C.eval (pre x ++ [(pre x).getD a.val false || (pre x).getD b.val false]) = f x) →
      (if a==4 || b==4 then 1 else 0) + C.gates.countP read4 ≤ 2 → 14 ≤ C.size) :
have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => x2.inputs.head? == Option.some (4 : ℕ) || x2.op.eval [Bool.true, Bool.true] && x2.inputs.contains (4 : ℕ)) x1.gates; have x2 : PEqualNP.CircuitLowerBounds.Circuit → List (Fin (11 : ℕ)) → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin (11 : ℕ))) => { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2.gates, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x3 →     x4.length ≤ (2 : ℕ) →       (∀ (x7 : Fin (9 : ℕ) → Bool),           have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ))];           x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : Fin (11 : ℕ)) => x8.getD (↑x9) Bool.false) x4)]) = (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →         x1 (x2 x3 x4) ≤ (2 : ℕ) → (14 : ℕ) ≤ x3.size := by
  -- Renumber raw wires while preserving the evaluation and the uses of input four.
  let mapGate (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map σ⟩
  let rewired (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate σ),σ C.output⟩

  have fan {C : Circuit} (σ : ℕ → ℕ) (h : FanInTwo C) : FanInTwo (rewired σ C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h a ha).1,by simpa [mapGate] using (h a ha).2⟩

  have run {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (gs : List Gate) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires y).getD (σ i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map (fun i => x.getD i false))
      have same : (mapGate σ g).op.eval ((mapGate σ g).inputs.map (fun i => y.getD i false)) = b := by
        simp only [b,mapGate,List.map_map,Function.comp_def,agree]
      change ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires (y++[_])).getD (σ i) false =
        ((Circuit.mk gs 0).wires (x++[b])).getD i false
      rw [same]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i<x.length
      · have hsi : σ i<y.length := by
          by_cases hr : i<cut
          · have := raw i hr; omega
          · rw [later i (by omega)]; omega
        rw [List.getD_append _ _ _ _ hsi, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [later i (by omega), List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]

  have evalMap {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (C : Circuit) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      (rewired σ C).eval y = C.eval x :=
    run σ raw later C.gates x y len lo agree C.output

  let rawMap (p : Fin 9 → Fin 9) (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else i
  let reader (g : Gate) := g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4

  have renameInputs : ∀ (C : Circuit) (p : Fin 9 → Fin 9), (∀ i, p i = 4 ↔ i = 4) → FanInTwo C →
        let read4 := fun (g : Gate) => g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4
        ∃ B : Circuit, FanInTwo B ∧ B.size = C.size ∧ B.gates.countP read4 = C.gates.countP read4 ∧
          ∀ (x : Fin 9 → Bool) (a b : Bool),
            B.eval (List.ofFn x ++ [a,b]) = C.eval (List.ofFn (x ∘ p) ++ [a,b]) := by
    intro C p fixed mono
    let σ := rawMap p
    refine ⟨rewired σ C,fan σ mono,?_,?_,?_⟩
    · change (C.gates.map (mapGate σ)).length = C.gates.length
      exact List.length_map (mapGate σ)
    · change (C.gates.map (mapGate σ)).countP reader = C.gates.countP reader
      have eq4 (i : ℕ) : σ i = 4 ↔ i=4 := by
        by_cases hi : i<9
        · change (rawMap p i = 4) ↔ i=4
          simp only [rawMap,dite_eq_left hi]
          have hp := fixed (⟨i,hi⟩ : Fin 9)
          constructor
          · intro h; exact congrArg Fin.val (hp.mp (Fin.ext h))
          · intro h; exact congrArg Fin.val (hp.mpr (Fin.ext h))
        · simp [σ,rawMap,hi]
      have has (l : List ℕ) : (l.map σ).contains 4 = l.contains 4 := by
        apply Bool.eq_iff_iff.mpr
        simp [eq4]
      have hd (l : List ℕ) : ((l.map σ).head? == some 4) = (l.head? == some 4) := by
        cases l with
        | nil => rfl
        | cons i l => apply Bool.eq_iff_iff.mpr; simpa using eq4 i
      have hr (g : Gate) : reader (mapGate σ g) = reader g := by
        unfold reader mapGate
        dsimp only
        rw [hd,has]
      simp [List.countP_map,Function.comp_def,hr]
    · intro x a b
      have small (i : ℕ) (hi : i<9) : σ i < 9 := by simp [σ,rawMap,hi]
      have late (i : ℕ) (hi : 9 ≤ i) : σ i=i := by simp [σ,rawMap,Nat.not_lt.mpr hi]
      apply evalMap σ small late C _ _ (by simp) (by simp)
      intro i
      by_cases h : i<9
      · have h1 : σ i < (List.ofFn x).length := by simpa using small i h
        have h2 : i < (List.ofFn (x ∘ p)).length := by simpa using h
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2]
        simp only [List.getElem_ofFn,Function.comp_apply]
        congr 1
        apply Fin.ext
        exact dite_eq_left h
      · have hn : 9 ≤ i := by omega
        rw [late i hn, List.getD_append_right _ _ _ _ (by simpa using hn),
          List.getD_append_right _ _ _ _ (by simpa using hn)]
        simp
  -- A second OR that reproduces a wire adds no power beyond the checked ordinary bound.
  let redirect (a : Fin 11) (i : ℕ) : ℕ :=
    if i=9 then 10 else if i=10 then (if a.val<9 then a.val else if a.val=9 then 10 else 9) else i

  let and03 : Gate := ⟨.and,[0,3]⟩

  have redundant : ∀ (C : Circuit) (a : Fin 11), FanInTwo C →
        let f := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
        let pre := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 && x 3]
        (∀ x, C.eval (pre x ++ [(pre x).getD a.val false]) = f x) → 14 ≤ C.size := by
    intro C a hf
    let f := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
    let pre (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 3]
    change (∀ x, C.eval (pre x ++ [(pre x).getD a.val false]) = f x) → 14 ≤ C.size
    intro correct
    let σ := redirect a
    let A := rewired σ C
    let B : Circuit := ⟨and03 :: A.gates,A.output⟩
    have hb : FanInTwo B := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | h
      · exact ⟨Or.inl rfl,by decide⟩
      · exact fan σ hf g h
    have small (i : ℕ) (hi : i < 11) : σ i < 11 := by
      unfold σ redirect
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    have large (i : ℕ) (hi : 11 ≤ i) : σ i = i := by simp [σ,redirect,show i≠9 by omega,show i≠10 by omega]
    have same (x : Fin 9 → Bool) : B.eval (List.ofFn x ++ [false]) = f x := by
      let u := pre x ++ [(pre x).getD a.val false]
      let v := (List.ofFn x ++ [false]) ++ [x 0 && x 3]
      have hlen : u.length = 11 := by simp [u,pre]
      have vlen : v.length = 11 := by simp [v]
      have wireEq (i : ℕ) : v.getD (σ i) false = u.getD i false := by
        by_cases hi : i < 11
        · interval_cases i <;> fin_cases a <;> rfl
        · rw [large i (by omega), List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hr := evalMap σ small large C u v (hlen.trans vlen.symm) hlen.ge wireEq
      have hand : and03.op.eval (and03.inputs.map (fun i => (List.ofFn x ++ [false]).getD i false)) = (x 0 && x 3) := by
        change (x 0 && (x 3 && true)) = _
        simp
      change A.eval ((List.ofFn x ++ [false]) ++ [and03.op.eval (and03.inputs.map (fun i => (List.ofFn x ++ [false]).getD i false))]) = _
      rw [hand]
      exact hr.trans (correct x)
    have bound := ordinary B hb (fun x => by
      have h := same x
      simpa only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using h)
    have sizeB : B.size=C.size+1 := by
      change (and03 :: C.gates.map (mapGate σ)).length = C.gates.length+1
      simp
    omega
  -- Four permutations preserve the edge set, the first conjunction and the marked input.
  -- Each row below certifies the representative for one ordered pair of available wire indices.
  let F : (Fin 9 → Bool) → Bool := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let orbitPre (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 3]
  let wire (x : Fin 9 → Bool) (i : Fin 11) := (orbitPre x).getD i.val false
  let π : Fin 4 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],
    ![0,5,8,3,4,1,7,6,2],
    ![3,2,1,0,4,8,7,6,5],
    ![3,8,5,0,4,2,6,7,1]]
  let reps : List ℕ := [1, 2, 3, 4, 6, 13, 15, 16, 17, 18, 19, 20, 50, 53, 73, 75]
  have fixed : ∀ t i, π t i=4 ↔ i=4 := by decide +kernel
  have first (t : Fin 4) (x : Fin 9 → Bool) : (x (π t 0) && x (π t 3)) = (x 0 && x 3) := by
    fin_cases t
    · change (x 0 && x 3) = (x 0 && x 3)
      ac_rfl
    · change (x 0 && x 3) = (x 0 && x 3)
      ac_rfl
    · change (x 3 && x 0) = (x 0 && x 3)
      ac_rfl
    · change (x 3 && x 0) = (x 0 && x 3)
      ac_rfl
  have graph (t : Fin 4) (x : Fin 9 → Bool) : F (x ∘ π t) = F x := by
    fin_cases t <;> simp only [F,List.any_cons,List.any_nil,Bool.or_false]
    · change ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5))))))))))))
      ac_rfl
    · change ((x 0 && x 5) || ((x 5 && x 8) || ((x 8 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 1) || ((x 5 && x 7) || ((x 8 && x 6) || ((x 3 && x 2) || ((x 1 && x 6) || ((x 7 && x 2) || (x 2 && x 1)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5))))))))))))
      ac_rfl
    · change ((x 3 && x 2) || ((x 2 && x 1) || ((x 1 && x 0) || ((x 0 && x 4) || ((x 4 && x 3) || ((x 3 && x 8) || ((x 2 && x 7) || ((x 1 && x 6) || ((x 0 && x 5) || ((x 8 && x 6) || ((x 7 && x 5) || (x 5 && x 8)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5))))))))))))
      ac_rfl
    · change ((x 3 && x 8) || ((x 8 && x 5) || ((x 5 && x 0) || ((x 0 && x 4) || ((x 4 && x 3) || ((x 3 && x 2) || ((x 8 && x 6) || ((x 5 && x 7) || ((x 0 && x 1) || ((x 2 && x 7) || ((x 6 && x 1) || (x 1 && x 2)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5))))))))))))
      ac_rfl
  have represent (i j : Fin 11) : ∃ (t : Fin 4) (a b : Fin 11),
      (a=b ∨ 11*a.val+b.val∈reps) ∧ (i==4 || j==4) = (a==4 || b==4) ∧
      ∀ x, (wire (x ∘ π t) i || wire (x ∘ π t) j) = (wire x a || wire x b) := by
    fin_cases i <;> fin_cases j
    · refine ⟨0,0,0,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 0) = (x 0 || x 0)
      cases x 0 <;> rfl
    · refine ⟨0,0,1,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 1) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨0,0,2,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 2) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨0,0,3,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 3) = (x 0 || x 3)
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,0,4,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 4) = (x 0 || x 4)
      cases x 0 <;> cases x 4 <;> rfl
    · refine ⟨1,0,1,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 1) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨0,0,6,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 6) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨1,0,6,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 6) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨1,0,2,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 2) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨0,0,0,by decide,rfl,fun x => ?_⟩
      change (x 0 || (x 0 && x 3)) = (x 0 || x 0)
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,0,0,by decide,rfl,fun x => ?_⟩
      change (x 0 || false) = (x 0 || x 0)
      cases x 0 <;> rfl
    · refine ⟨0,0,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 0) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨0,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,1,2,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 2) = (x 1 || x 2)
      cases x 1 <;> cases x 2 <;> rfl
    · refine ⟨2,0,2,by decide,rfl,fun x => ?_⟩
      change (x 2 || x 0) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨0,1,4,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 4) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨0,1,5,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 5) = (x 1 || x 5)
      cases x 1 <;> cases x 5 <;> rfl
    · refine ⟨0,1,6,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 6) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨0,1,7,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 7) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨0,1,8,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 8) = (x 1 || x 8)
      cases x 1 <;> cases x 8 <;> rfl
    · refine ⟨0,1,9,by decide,rfl,fun x => ?_⟩
      change (x 1 || (x 0 && x 3)) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨0,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || false) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,0,2,by decide,rfl,fun x => ?_⟩
      change (x 2 || x 0) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨0,1,2,by decide,rfl,fun x => ?_⟩
      change (x 2 || x 1) = (x 1 || x 2)
      cases x 1 <;> cases x 2 <;> rfl
    · refine ⟨2,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨2,0,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 0) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨2,1,4,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 4) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨1,1,8,by decide,rfl,fun x => ?_⟩
      change (x 8 || x 1) = (x 1 || x 8)
      cases x 1 <;> cases x 8 <;> rfl
    · refine ⟨2,1,7,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 7) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨2,1,6,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 6) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨2,1,5,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 5) = (x 1 || x 5)
      cases x 1 <;> cases x 5 <;> rfl
    · refine ⟨2,1,9,by decide,rfl,fun x => ?_⟩
      change (x 1 || (x 3 && x 0)) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨2,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || false) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,0,3,by decide,rfl,fun x => ?_⟩
      change (x 3 || x 0) = (x 0 || x 3)
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨2,0,2,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 2) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨2,0,1,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 1) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨2,0,0,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 0) = (x 0 || x 0)
      cases x 0 <;> rfl
    · refine ⟨2,0,4,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 4) = (x 0 || x 4)
      cases x 0 <;> cases x 4 <;> rfl
    · refine ⟨3,0,2,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 2) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨3,0,6,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 6) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨2,0,6,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 6) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨3,0,1,by decide,rfl,fun x => ?_⟩
      change (x 0 || x 1) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨2,0,0,by decide,rfl,fun x => ?_⟩
      change (x 0 || (x 3 && x 0)) = (x 0 || x 0)
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨2,0,0,by decide,rfl,fun x => ?_⟩
      change (x 0 || false) = (x 0 || x 0)
      cases x 0 <;> rfl
    · refine ⟨0,0,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 0) = (x 0 || x 4)
      cases x 0 <;> cases x 4 <;> rfl
    · refine ⟨0,1,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 1) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨2,1,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 1) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨2,0,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 0) = (x 0 || x 4)
      cases x 0 <;> cases x 4 <;> rfl
    · refine ⟨0,4,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 4) = (x 4 || x 4)
      cases x 4 <;> rfl
    · refine ⟨1,1,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 1) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨0,4,6,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 6) = (x 4 || x 6)
      cases x 4 <;> cases x 6 <;> rfl
    · refine ⟨1,4,6,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 6) = (x 4 || x 6)
      cases x 4 <;> cases x 6 <;> rfl
    · refine ⟨3,1,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || x 1) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨0,4,9,by decide,rfl,fun x => ?_⟩
      change (x 4 || (x 0 && x 3)) = (x 4 || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> cases x 4 <;> rfl
    · refine ⟨0,4,4,by decide,rfl,fun x => ?_⟩
      change (x 4 || false) = (x 4 || x 4)
      cases x 4 <;> rfl
    · refine ⟨1,0,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 0) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨0,1,5,by decide,rfl,fun x => ?_⟩
      change (x 5 || x 1) = (x 1 || x 5)
      cases x 1 <;> cases x 5 <;> rfl
    · refine ⟨1,1,8,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 8) = (x 1 || x 8)
      cases x 1 <;> cases x 8 <;> rfl
    · refine ⟨3,0,2,by decide,rfl,fun x => ?_⟩
      change (x 2 || x 0) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨1,1,4,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 4) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨1,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨1,1,7,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 7) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨1,1,6,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 6) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨1,1,2,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 2) = (x 1 || x 2)
      cases x 1 <;> cases x 2 <;> rfl
    · refine ⟨1,1,9,by decide,rfl,fun x => ?_⟩
      change (x 1 || (x 0 && x 3)) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨1,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || false) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,0,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 0) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨0,1,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 1) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨2,1,7,by decide,rfl,fun x => ?_⟩
      change (x 7 || x 1) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨3,0,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 0) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨0,4,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 4) = (x 4 || x 6)
      cases x 4 <;> cases x 6 <;> rfl
    · refine ⟨1,1,7,by decide,rfl,fun x => ?_⟩
      change (x 7 || x 1) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨0,6,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 6) = (x 6 || x 6)
      cases x 6 <;> rfl
    · refine ⟨0,6,7,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 7) = (x 6 || x 7)
      cases x 6 <;> cases x 7 <;> rfl
    · refine ⟨3,1,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 1) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨0,6,9,by decide,rfl,fun x => ?_⟩
      change (x 6 || (x 0 && x 3)) = (x 6 || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> cases x 6 <;> rfl
    · refine ⟨0,6,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || false) = (x 6 || x 6)
      cases x 6 <;> rfl
    · refine ⟨1,0,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 0) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨0,1,7,by decide,rfl,fun x => ?_⟩
      change (x 7 || x 1) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨2,1,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 1) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨2,0,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 0) = (x 0 || x 6)
      cases x 0 <;> cases x 6 <;> rfl
    · refine ⟨1,4,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 4) = (x 4 || x 6)
      cases x 4 <;> cases x 6 <;> rfl
    · refine ⟨1,1,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 1) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨0,6,7,by decide,rfl,fun x => ?_⟩
      change (x 7 || x 6) = (x 6 || x 7)
      cases x 6 <;> cases x 7 <;> rfl
    · refine ⟨1,6,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || x 6) = (x 6 || x 6)
      cases x 6 <;> rfl
    · refine ⟨3,1,7,by decide,rfl,fun x => ?_⟩
      change (x 7 || x 1) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨1,6,9,by decide,rfl,fun x => ?_⟩
      change (x 6 || (x 0 && x 3)) = (x 6 || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> cases x 6 <;> rfl
    · refine ⟨1,6,6,by decide,rfl,fun x => ?_⟩
      change (x 6 || false) = (x 6 || x 6)
      cases x 6 <;> rfl
    · refine ⟨1,0,2,by decide,rfl,fun x => ?_⟩
      change (x 2 || x 0) = (x 0 || x 2)
      cases x 0 <;> cases x 2 <;> rfl
    · refine ⟨0,1,8,by decide,rfl,fun x => ?_⟩
      change (x 8 || x 1) = (x 1 || x 8)
      cases x 1 <;> cases x 8 <;> rfl
    · refine ⟨2,1,5,by decide,rfl,fun x => ?_⟩
      change (x 5 || x 1) = (x 1 || x 5)
      cases x 1 <;> cases x 5 <;> rfl
    · refine ⟨3,0,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 0) = (x 0 || x 1)
      cases x 0 <;> cases x 1 <;> rfl
    · refine ⟨3,1,4,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 4) = (x 1 || x 4)
      cases x 1 <;> cases x 4 <;> rfl
    · refine ⟨1,1,2,by decide,rfl,fun x => ?_⟩
      change (x 2 || x 1) = (x 1 || x 2)
      cases x 1 <;> cases x 2 <;> rfl
    · refine ⟨3,1,6,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 6) = (x 1 || x 6)
      cases x 1 <;> cases x 6 <;> rfl
    · refine ⟨3,1,7,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 7) = (x 1 || x 7)
      cases x 1 <;> cases x 7 <;> rfl
    · refine ⟨3,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨3,1,9,by decide,rfl,fun x => ?_⟩
      change (x 1 || (x 3 && x 0)) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨3,1,1,by decide,rfl,fun x => ?_⟩
      change (x 1 || false) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,0,0,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || x 0) = (x 0 || x 0)
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,1,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || x 1) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨2,1,9,by decide,rfl,fun x => ?_⟩
      change ((x 3 && x 0) || x 1) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨2,0,0,by decide,rfl,fun x => ?_⟩
      change ((x 3 && x 0) || x 0) = (x 0 || x 0)
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,4,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || x 4) = (x 4 || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> cases x 4 <;> rfl
    · refine ⟨1,1,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || x 1) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨0,6,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || x 6) = (x 6 || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> cases x 6 <;> rfl
    · refine ⟨1,6,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || x 6) = (x 6 || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> cases x 6 <;> rfl
    · refine ⟨3,1,9,by decide,rfl,fun x => ?_⟩
      change ((x 3 && x 0) || x 1) = (x 1 || (x 0 && x 3))
      cases x 0 <;> cases x 1 <;> cases x 3 <;> rfl
    · refine ⟨0,9,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || (x 0 && x 3)) = ((x 0 && x 3) || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,9,9,by decide,rfl,fun x => ?_⟩
      change ((x 0 && x 3) || false) = ((x 0 && x 3) || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,0,0,by decide,rfl,fun x => ?_⟩
      change (false || x 0) = (x 0 || x 0)
      cases x 0 <;> rfl
    · refine ⟨0,1,1,by decide,rfl,fun x => ?_⟩
      change (false || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨2,1,1,by decide,rfl,fun x => ?_⟩
      change (false || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨2,0,0,by decide,rfl,fun x => ?_⟩
      change (false || x 0) = (x 0 || x 0)
      cases x 0 <;> rfl
    · refine ⟨0,4,4,by decide,rfl,fun x => ?_⟩
      change (false || x 4) = (x 4 || x 4)
      cases x 4 <;> rfl
    · refine ⟨1,1,1,by decide,rfl,fun x => ?_⟩
      change (false || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,6,6,by decide,rfl,fun x => ?_⟩
      change (false || x 6) = (x 6 || x 6)
      cases x 6 <;> rfl
    · refine ⟨1,6,6,by decide,rfl,fun x => ?_⟩
      change (false || x 6) = (x 6 || x 6)
      cases x 6 <;> rfl
    · refine ⟨3,1,1,by decide,rfl,fun x => ?_⟩
      change (false || x 1) = (x 1 || x 1)
      cases x 1 <;> rfl
    · refine ⟨0,9,9,by decide,rfl,fun x => ?_⟩
      change (false || (x 0 && x 3)) = ((x 0 && x 3) || (x 0 && x 3))
      cases x 0 <;> cases x 3 <;> rfl
    · refine ⟨0,10,10,by decide,rfl,fun x => ?_⟩
      change (false || false) = (false || false)
      rfl
  have listPair (s : List (Fin 11)) (h : s.length ≤ 2) : ∃ i j : Fin 11,
      s.contains 4 = (i==4 || j==4) ∧ ∀ y, (s.map (wire y)).any id = (wire y i || wire y j) := by
    cases s with
    | nil => exact ⟨10,10,rfl,by intro y; rfl⟩
    | cons i l =>
      cases l with
      | nil =>
        refine ⟨i,10,?_,?_⟩
        · fin_cases i <;> rfl
        · intro y
          change (wire y i || false) = (wire y i || false)
          rfl
      | cons j l =>
        have emp : l = [] := by simpa using h
        subst l
        refine ⟨i,j,?_,?_⟩
        · fin_cases i <;> fin_cases j <;> rfl
        · intro y
          simp [List.map_cons,List.any_cons]

  have orbits : ∀ (s : List (Fin 11)), s.length ≤ 2 →
        let f := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
        let orbitPre := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 && x 3]
        ∃ (p : Fin 9 → Fin 9) (a b : Fin 11),
          (a=b ∨ 11*a.val+b.val ∈ ([1,2,3,4,6,13,15,16,17,18,19,20,50,53,73,75] : List ℕ)) ∧
          (∀ i, p i = 4 ↔ i = 4) ∧ s.contains 4 = (a==4 || b==4) ∧
          ∀ x, (x (p 0) && x (p 3)) = (x 0 && x 3) ∧ f (x ∘ p) = f x ∧
            (s.map (fun i => (orbitPre (x ∘ p)).getD i.val false)).any id = ((orbitPre x).getD a.val false || (orbitPre x).getD b.val false) := by
    intro s h
    obtain ⟨i,j,four,read⟩ := listPair s h
    obtain ⟨t,a,b,co,also,value⟩ := represent i j
    exact ⟨π t,a,b,co,fixed t,four.trans also,fun x =>
      ⟨first t x,graph t x,(read (x ∘ π t)).trans (value x)⟩⟩
  intro score prepend C s mono arity correct budget
  let f := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let pre := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 && x 3]
  let read4 := fun (g : Gate) => g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4
  have spec (x : Fin 9 → Bool) : C.eval (pre x ++ [(s.map (fun i => (pre x).getD i.val false)).any id]) = f x := by
    have h := correct x
    change C.eval (pre x ++ [(s.map (fun i => (pre x).getD i.val false)).any id]) = _ at h
    simpa only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using h
  obtain ⟨p,a,b,indices,fixed,four,agree⟩ := orbits s arity
  obtain ⟨B,bmono,sz,readers,run⟩ := renameInputs C p fixed mono
  have fx (x : Fin 9 → Bool) : B.eval (pre x ++ [(pre x).getD a.val false || (pre x).getD b.val false]) = f x := by
    obtain ⟨first,fp,extra⟩ := agree x
    have hb := run x (x 0 && x 3) ((pre x).getD a.val false || (pre x).getD b.val false)
    have hc := spec (x ∘ p)
    change B.eval (List.ofFn x ++ [x 0 && x 3,_]) = _ at hb
    change C.eval (List.ofFn (x ∘ p) ++ [(x (p 0) && x (p 3)),_]) = f (x ∘ p) at hc
    change (List.map _ s).any id = _ at extra
    change f (x ∘ p) = f x at fp
    rw [first,extra,fp] at hc
    exact hb.trans hc
  rw [← sz]
  rcases indices with rfl | canonical
  · apply redundant B a bmono
    intro x
    simpa only [Bool.or_self] using fx x
  · apply binaryCases B a b bmono canonical fx
    change (if a==4 || b==4 then 1 else 0) + B.gates.countP read4 ≤ 2
    change ((⟨.and,[0,3]⟩ : Gate) :: ⟨.or,s.map Fin.val⟩ :: C.gates).countP read4 ≤ 2 at budget
    have count : read4 ⟨.or,s.map Fin.val⟩ = s.contains 4 := by
      cases s with
      | nil => rfl
      | cons i l =>
        cases l with
        | nil => fin_cases i <;> rfl
        | cons j l =>
          have empty : l = [] := by simpa using arity
          subst l
          fin_cases i <;> fin_cases j <;> rfl
    change B.gates.countP read4 = C.gates.countP read4 at readers
    simp only [List.countP_cons] at budget
    rw [readers,← four]
    change (if s.contains 4 then 1 else 0) + C.gates.countP read4 ≤ 2
    have skip : read4 ⟨.and,[0,3]⟩ = false := by decide
    rw [skip,count] at budget
    split <;> simp_all <;> omega
