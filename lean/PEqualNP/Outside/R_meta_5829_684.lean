import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5829_684
    (variableSeed : let F := fun x : Fin 10 → Bool => (List.finRange 5).any fun j =>
        (x (Fin.castAdd 5 j) && (x (Fin.castAdd 5 (j+1)) || x (Fin.natAdd 5 j))) ||
        (x (Fin.natAdd 5 j) && x (Fin.natAdd 5 (j+2)));
      ∀ (D : Circuit) (u v : Fin 18), 0 < u → u < v → D.size = v.val → FanInTwo D →
        let W := fun (k : Fin 18) (x : Fin 10 → Bool) =>
          (D.wires (List.ofFn x ++ [!(x 0)])).getD (10+k.val) false;
        (∀ x, (W u x || W v x) = F x) → W u ≤ W v ∨ W v ≤ W u)
    (constantSeed : let F := fun x : Fin 10 → Bool => (List.finRange 5).any fun j =>
        (x (Fin.castAdd 5 j) && (x (Fin.castAdd 5 (j+1)) || x (Fin.natAdd 5 j))) ||
        (x (Fin.natAdd 5 j) && x (Fin.natAdd 5 (j+2)));
      ∀ (D : Circuit) (u v : Fin 18), 0 < u → u < v → D.size = v.val → FanInTwo D →
        let W := fun (k : Fin 18) (x : Fin 10 → Bool) =>
          (D.wires (List.ofFn x ++ [true])).getD (10+k.val) false;
        (∀ x, (W u x || W v x) = F x) → W u ≤ W v ∨ W v ≤ W u) :
    (∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x1] : PEqualNP.CircuitLowerBounds.Gate };       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));       have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;       (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 ((10 : ℕ) + ↑x3) = Bool.true ∧ x9 x10 ((10 : ℕ) + ↑x4) = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x11 ((10 : ℕ) + ↑x4) = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x12 ((10 : ℕ) + ↑x4) = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x13 ((10 : ℕ) + ↑x4) = Bool.false) := by
  classical
  intro a C u v legal budget
  dsimp only
  intro leftOnly rightOnly sound
  by_contra uncovered
  let F := fun x : Fin 10 → Bool => (List.finRange 5).any fun j =>
    (x (Fin.castAdd 5 j) && (x (Fin.castAdd 5 (j+1)) || x (Fin.natAdd 5 j))) ||
    (x (Fin.natAdd 5 j) && x (Fin.natAdd 5 (j+2)))
  let seed : Gate := ⟨.not,[a.val]⟩
  let source (x : Fin 10 → Bool) := (⟨[seed],0⟩ : Circuit).wires (List.ofFn x)
  let A (x : Fin 10 → Bool) := (C.wires (source x)).getD (10+u.val) false
  let B (x : Fin 10 → Bool) := (C.wires (source x)).getD (10+v.val) false
  let edges : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
  let FList (x : Fin 10 → Bool) := edges.any (fun p => x p.1 && x p.2)
  have targetEq : ∀ x : Fin 10 → Bool, F x = FList x := by
    dsimp only [F,FList,edges]
    decide +kernel
  have explicitEq : ∀ x : Fin 10 → Bool,
      ((((((((((((((x 0 && x 1 || x 1 && x 2) || x 2 && x 3) || x 3 && x 4) ||
      x 4 && x 0) || x 0 && x 5) || x 1 && x 6) || x 2 && x 7) || x 3 && x 8) ||
      x 4 && x 9) || x 5 && x 7) || x 7 && x 9) || x 9 && x 6) || x 6 && x 8) || x 8 && x 5) = F x := by
    dsimp only [F]
    decide +kernel
  change ∃ x, A x = true ∧ B x = false at leftOnly
  change ∃ x, A x = false ∧ B x = true at rightOnly
  simp only [explicitEq] at sound uncovered
  change ∀ x, F x = false → A x = false ∧ B x = false at sound
  change ¬ ∃ x, F x = true ∧ A x = false ∧ B x = false at uncovered
  have covers (x : Fin 10 → Bool) : (A x || B x) = F x := by
    cases hf : F x with
    | false => obtain ⟨hA,hB⟩ := sound x hf; simp [hA,hB]
    | true =>
      cases hA : A x <;> cases hB : B x <;> simp_all only [Bool.or_false,Bool.or_true]
      exact (uncovered ⟨x,hf,hA,hB⟩).elim
  let ord (p : Fin 10 × Fin 10) := if p.1 ≤ p.2 then p else (p.2,p.1)
  let codes : List ℕ := [9876543210,7895623401,8956734012,6598710432,5987604321,9547068321,4590738612,5608179432,9064175832,954716832]
  let ren (a i : Fin 10) : Fin 10 :=
    Fin.ofNat 10 ((codes.getD a.val 0) / 10^i.val)
  have certificate : ∀ a : Fin 10,
      ren a a = 0 ∧ (List.ofFn (ren a)).Nodup ∧
      (edges.map fun p => ord (ren a p.1,ren a p.2)).Perm edges := by
    dsimp only [ren,ord,codes,edges]
    decide +kernel
  let m (i : Fin 10) := if h : a.val < 10 then ren ⟨a.val,h⟩ i else i
  let signal (x : Fin 10 → Bool) := if a.val < 10 then !(x 0) else true
  have perm : (edges.map fun p => ord (m p.1,m p.2)).Perm edges := by
    by_cases h : a.val < 10
    · simpa only [m,dite_eq_left h] using (certificate ⟨a.val,h⟩).2.2
    · simp only [m,dite_eq_right h]
      have fixed : (edges.map ord).Perm edges := by dsimp only [edges,ord]; decide +kernel
      exact fixed
  have distinct : (List.ofFn m).Nodup := by
    by_cases h : a.val < 10
    · simpa only [m,dite_eq_left h] using (certificate ⟨a.val,h⟩).2.1
    · simp only [m,dite_eq_right h]
      exact List.nodup_ofFn.mpr (fun _ _ e => e)
  have mInj : Function.Injective m := List.nodup_ofFn.mp distinct
  have mSurj : Function.Surjective m := Finite.surjective_of_injective mInj
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective m ⟨mInj,mSurj⟩
  have associates (x : Fin 10 → Bool) : ∃ y : Fin 10 → Bool, (fun j => y (m j)) = x := by
    refine ⟨fun j => x (e.symm j), ?_⟩
    funext j
    change x (e.symm (e j)) = x j
    rw [e.symm_apply_apply]
  have graph (y : Fin 10 → Bool) : F (fun j => y (m j)) = F y := by
    rw [targetEq (fun j => y (m j)),targetEq y]
    have point (p : Fin 10 × Fin 10) :
        (y (ord (m p.1,m p.2)).1 && y (ord (m p.1,m p.2)).2) = (y (m p.1) && y (m p.2)) := by
      unfold ord
      split
      · rfl
      · exact Bool.and_comm _ _
    change edges.any (fun p => y (m p.1) && y (m p.2)) = edges.any (fun p => y p.1 && y p.2)
    have hp : (edges.map fun p => ord (m p.1,m p.2)).Perm edges := perm
    calc
      _ = (edges.map fun p => ord (m p.1,m p.2)).any (fun p => y p.1 && y p.2) := by
        simp only [List.any_map,Function.comp_def,point]
      _ = _ := hp.any_eq
  let pin (i : ℕ) : ℕ := if hi : i < 10 then (m ⟨i,hi⟩).val else i
  have pinHigh {i : ℕ} (h : 10 ≤ i) : pin i = i := dite_eq_right (Nat.not_lt.mpr h)
  let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map pin⟩
  let D : Circuit := ⟨C.gates.map rename,C.output⟩
  have dLegal : FanInTwo D := by
    intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    simpa [rename] using legal h hh
  have evalLen (gs : List Gate) (xs : List Bool) :
      (Circuit.wires ⟨gs,0⟩ xs).length = xs.length+gs.length := by
    induction gs generalizing xs with
    | nil =>
      change xs.length = xs.length + 0
      omega
    | cons h hs ih =>
      change (Circuit.wires ⟨hs,0⟩ (xs ++ [h.op.eval (h.inputs.map fun i => xs.getD i false)])).length = _
      rw [ih]
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
  have preserve (gs : List Gate) (xs : List Bool) (j : ℕ) (hj : j < xs.length) :
      (Circuit.wires ⟨gs,0⟩ xs).getD j false = xs.getD j false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change (Circuit.wires ⟨gs,0⟩ (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).getD j false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hj]
  have prefixValue (n j : ℕ) (xs : List Bool) (hj : j < xs.length + (D.gates.take n).length) :
      (Circuit.wires ⟨D.gates.take n,0⟩ xs).getD j false = (D.wires xs).getD j false := by
    have decompose :
        D.wires xs = Circuit.wires ⟨D.gates.drop n,0⟩ (Circuit.wires ⟨D.gates.take n,0⟩ xs) := by
      let step (ws : List Bool) (g : Gate) :=
        ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
      change D.gates.foldl step xs = (D.gates.drop n).foldl step ((D.gates.take n).foldl step xs)
      rw [← List.foldl_append, List.take_append_drop]
    have within : j < (Circuit.wires ⟨D.gates.take n,0⟩ xs).length := by rwa [evalLen]
    rw [decompose, preserve (D.gates.drop n) _ _ within]
  have readInput (x : Fin 10 → Bool) (i : Fin 10) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn ..
  have seedVal (y : Fin 10 → Bool) :
      source (fun i => y (m i)) = List.ofFn (fun i => y (m i)) ++ [signal y] := by
    change List.ofFn (fun i => y (m i)) ++
      [!((List.ofFn (fun i => y (m i))).getD a.val false)] = _
    by_cases h : a.val < 10
    · have read := readInput (fun i => y (m i)) ⟨a.val,h⟩
      change (List.ofFn (fun i => y (m i))).getD a.val false = y (m ⟨a.val,h⟩) at read
      rw [read, show m ⟨a.val,h⟩ = 0 from (dite_eq_left h).trans (certificate ⟨a.val,h⟩).1]
      simp [signal,h]
    · have outside : (List.ofFn (fun i => y (m i))).length ≤ a.val := by simp; omega
      rw [List.getD_eq_default _ _ outside]
      simp [signal,h]
  have transport (gs : List Gate) (l r : List Bool) (same : l.length = r.length)
      (long : 10 ≤ l.length) (reads : ∀ i, l.getD i false = r.getD (pin i) false) (i : ℕ) :
      (Circuit.wires ⟨gs,0⟩ l).getD i false =
        (Circuit.wires ⟨gs.map rename,0⟩ r).getD (pin i) false := by
    induction gs generalizing l r with
    | nil => exact reads i
    | cons h hs ih =>
      let out := h.op.eval (h.inputs.map fun j => l.getD j false)
      have outEq : out = h.op.eval ((rename h).inputs.map fun j => r.getD j false) := by
        simp only [out,rename,List.map_map,Function.comp_def,reads]
      change (Circuit.wires ⟨hs,0⟩ (l ++ [out])).getD i false =
        (Circuit.wires ⟨hs.map rename,0⟩
          (r ++ [h.op.eval ((rename h).inputs.map fun j => r.getD j false)])).getD (pin i) false
      rw [← outEq]
      apply ih _ _ (by simp [same]) (by simp; omega)
      intro j
      by_cases before : j < l.length
      · have inside : pin j < r.length := by
          by_cases hi : j < 10
          · simpa only [pin,dite_eq_left hi,← same] using Nat.lt_of_lt_of_le (m ⟨j,hi⟩).isLt long
          · rw [pinHigh (by omega),← same]; exact before
        rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ inside,reads]
      · rw [pinHigh (by omega),List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),same]
  let W (i : Fin 18) (x : Fin 10 → Bool) :=
    (D.wires (List.ofFn x ++ [signal x])).getD (10+i.val) false
  have wire (i : Fin 18) (y : Fin 10 → Bool) :
      (C.wires (source (fun j => y (m j)))).getD (10+i.val) false = W i y := by
    have same : (source (fun j => y (m j))).length = (List.ofFn y ++ [signal y]).length := by
      simp [seedVal]
    have reads (j : ℕ) :
        (source (fun p => y (m p))).getD j false =
          (List.ofFn y ++ [signal y]).getD (pin j) false := by
      rw [seedVal]
      by_cases hj : j < 10
      · rw [show pin j = (m ⟨j,hj⟩).val from dite_eq_left hj]
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hj),
          List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using (m ⟨j,hj⟩).isLt)]
        change (List.ofFn (fun p => y (m p))).getD (⟨j,hj⟩ : Fin 10).val false =
          (List.ofFn y).getD (m ⟨j,hj⟩).val false
        rw [readInput,readInput]
      · have high : 10 ≤ j := by omega
        rw [pinHigh high,List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using high),
          List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using high),
          List.length_ofFn,List.length_ofFn]
    have t := transport C.gates _ _ same (by rw [seedVal]; simp) reads (10+i.val)
    rw [pinHigh (by omega : 10 ≤ 10+i.val)] at t
    exact t
  have hCover (x : Fin 10 → Bool) : (W u x || W v x) = F x := by
    rw [← wire u,← wire v,← graph x]
    exact covers (fun j => x (m j))
  obtain ⟨xL,hLa,hLb⟩ := leftOnly
  obtain ⟨xR,hRa,hRb⟩ := rightOnly
  obtain ⟨yL,mapL⟩ := associates xL
  obtain ⟨yR,mapR⟩ := associates xR
  have hLu : W u yL = true := by rw [← wire,mapL]; exact hLa
  have hLv : W v yL = false := by rw [← wire,mapL]; exact hLb
  have hRu : W u yR = false := by rw [← wire,mapR]; exact hRa
  have hRv : W v yR = true := by rw [← wire,mapR]; exact hRb
  have hReal (i : Fin 18) (y : Fin 10 → Bool) (hit : W i y = true) : i.val ≤ D.size := by
    by_contra! h
    have len : (D.wires (List.ofFn y ++ [signal y])).length = 11 + D.size := by
      change (Circuit.wires ⟨D.gates,0⟩ (List.ofFn y ++ [signal y])).length = 11 + D.size
      rw [evalLen]
      change (List.ofFn y ++ [signal y]).length + D.gates.length = 11 + D.gates.length
      simp
    change (D.wires (List.ofFn y ++ [signal y])).getD (10+i.val) false = true at hit
    rw [List.getD_eq_default _ _ (by omega)] at hit
    contradiction
  have different : u ≠ v := fun h => by simp [h,hLv] at hLu
  have positiveTap (i : Fin 18) (selector : u = i ∨ v = i) : 0 < i := by
    by_contra! hi
    have iZero : i = 0 := le_antisymm hi (by exact Fin.zero_le i)
    let zero : Fin 10 → Bool := fun _ => false
    have fZero : F zero = false := by decide +kernel
    have seedOne : signal zero = true := by
      by_cases h : a.val < 10 <;> simp [signal,zero,h]
    have tapZero : W i zero = true := by
      rw [iZero]
      change (Circuit.wires ⟨D.gates,0⟩ (List.ofFn zero ++ [signal zero])).getD 10 false = _
      rw [preserve _ _ _ (by simp)]
      rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
      simpa using seedOne
    have bothOff := Bool.or_eq_false_iff.mp ((hCover zero).trans fZero)
    rcases selector with hu | hv
    · rw [hu,tapZero] at bothOff
      exact Bool.noConfusion bothOff.1
    · rw [hv,tapZero] at bothOff
      exact Bool.noConfusion bothOff.2
  have cmp (i j : Fin 18) (nonzero : 0 < i) (ij : i < j) (bound : j.val ≤ D.size)
      (cover : ∀ x, (W i x || W j x) = F x) : W i ≤ W j ∨ W j ≤ W i := by
    let shorter : Circuit := ⟨D.gates.take j.val,0⟩
    have exactSize : shorter.size = j.val := by
      change (D.gates.take j.val).length = j.val
      have fit : j.val ≤ D.gates.length := bound
      rw [List.length_take, Nat.min_eq_left fit]
    have allowed : FanInTwo shorter := fun g gIn => dLegal g (List.mem_of_mem_take gIn)
    let U (i : Fin 18) (x : Fin 10 → Bool) :=
      (shorter.wires (List.ofFn x ++ [signal x])).getD (10+i.val) false
    have unchanged (s : Fin 18) (hs : s ≤ j) : U s = W s := by
      funext x
      apply prefixValue j.val
      have size : (D.gates.take j.val).length = j.val := exactSize
      have hle : s.val ≤ j.val := hs
      simp only [List.length_append,List.length_ofFn,List.length_singleton,size]
      omega
    rw [← unchanged i ij.le,← unchanged j le_rfl] at cover ⊢
    unfold U at cover ⊢
    by_cases h : a.val < 10
    · simp only [signal,ite_eq_left h] at cover ⊢
      exact variableSeed shorter i j nonzero ij exactSize allowed cover
    · simp only [signal,ite_eq_right h] at cover ⊢
      exact constantSeed shorter i j nonzero ij exactSize allowed cover
  have incomparable : ¬ (W u ≤ W v ∨ W v ≤ W u) := by
    rintro (le | le)
    · have p := le yL
      rw [hLu,hLv] at p
      exact (by decide : ¬ (true ≤ false)) p
    · have p := le yR
      rw [hRu,hRv] at p
      exact (by decide : ¬ (true ≤ false)) p
  apply incomparable
  rcases lt_or_gt_of_ne different with lt | gt
  · exact cmp u v (positiveTap u (.inl rfl)) lt (hReal v yR hRv) hCover
  · apply Or.symm
    apply cmp v u (positiveTap v (.inr rfl)) gt (hReal u yL hLu)
    intro x
    rw [Bool.or_comm]
    exact hCover x
