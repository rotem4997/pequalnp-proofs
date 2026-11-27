import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The reader premise is the checked theorem L_meta_1908.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3064_292
    (known : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         x1.size ≤ (15 : ℕ) →           ∀ x6 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x8 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x9 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x8;               x9.inputs[(0 : ℕ)]? = Option.some x6 ∨ x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x6 ∈ x9.inputs)
    (residual : ∀ (middle : List Gate) (pins : List (Fin 24)),
      let edges : List (ℕ × ℕ) :=
        [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
      middle.length ≤ 13 → FanInTwo ⟨middle, 0⟩ →
      (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
      pins.length ≤ 2 → pins ≠ [] →
      (∀ i ∈ pins, 10 ≤ i.val ∧ i.val < 10 + middle.length) →
      (∀ v ∈ [4, 6], ∃! i : Fin middle.length,
        let g := middle.get i
        g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs) →
      ∃ x : Fin 9 → Bool,
        let wires := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 4 || x 6])
        GateOp.and.eval (pins.map fun i => wires.getD i.val false) ≠ edges.any (fun e => x (Fin.ofNat 9 e.1) && x (Fin.ofNat 9 e.2))) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro middle pins budget fan bounds pinLength
  by_contra! good
  let f (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
      x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let first : Gate := ⟨.or, [4, 6]⟩
  let last : Gate := ⟨.and, pins.map Fin.val⟩
  let tail := middle ++ [last]
  let D : Circuit := ⟨first :: tail, 10 + middle.length⟩
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  let wires (x : Fin 9 → Bool) := middle.foldl step (seed x)
  have correct (x : Fin 9 → Bool) :
      GateOp.and.eval (pins.map fun i => (wires x).getD i.val false) = f x := Classical.byContradiction (good x)
  have extend (gs : List Gate) (w : List Bool) :
      ∃ extra : List Bool, gs.foldl step w = w ++ extra ∧ extra.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      obtain ⟨extra, he, hl⟩ := ih (step w g)
      exact ⟨_, by simpa [step, List.append_assoc] using he, by simp [hl]⟩
  have read (x : Fin 9 → Bool) (j : Fin 9) : (List.ofFn x).getD j.val false = x j := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have firstStep (x : Fin 9 → Bool) : step (List.ofFn x) first = seed x := by
    have h4 : (List.ofFn x).getD 4 false = x 4 := read x 4
    have h6 : (List.ofFn x).getD 6 false = x 6 := read x 6
    change List.ofFn x ++ [[(List.ofFn x).getD 4 false, (List.ofFn x).getD 6 false].any id] = _
    rw [h4, h6]
    simp only [seed, List.any_cons, List.any_nil, id, Bool.or_false]
  have seedLength (x : Fin 9 → Bool) : (seed x).length = 10 := by simp [seed]
  have atNine (x : Fin 9 → Bool) : (seed x).getD 9 false = (x 4 || x 6) := by
    change (List.ofFn x ++ [x 4 || x 6]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ first :: (middle ++ [last]) at hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · rcases List.mem_append.mp h with hmid | hlast
      · exact fan _ hmid
      · have he : g = last := List.mem_singleton.mp hlast
        subst g
        exact ⟨Or.inl rfl, by simpa only [last, List.length_map] using pinLength⟩
  have sizeD : D.size ≤ 15 := by
    change (first :: (middle ++ [last])).length ≤ 15
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  have headWire (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 4 || x 6) := by
    change (tail.foldl step (step (List.ofFn x) first)).getD 9 false = _
    rw [firstStep]
    obtain ⟨extra,he,_⟩ := extend tail (seed x)
    rw [he, List.getD_append _ _ _ _ (by rw [seedLength]; decide), atNine]
  have equality : circuitFun 9 D = f := by
    funext x
    change ((middle ++ [last]).foldl step (step (List.ofFn x) first)).getD (10 + middle.length) false = f x
    rw [firstStep, List.foldl_append]
    obtain ⟨extra,he,hl⟩ := extend middle (seed x)
    have len : (wires x).length = 10 + middle.length := by
      change (middle.foldl step (seed x)).length = _
      rw [he, List.length_append, seedLength, hl]
    change (wires x ++ [GateOp.and.eval ((pins.map Fin.val).map fun i => (wires x).getD i false)]).getD
      (10+middle.length) false = f x
    rw [← len, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.map_map]
    exact correct x
  have uniqueReaders := known D fanD headWire equality sizeD
  have pinsNonempty : pins ≠ [] := by
    intro empty
    have h := correct (fun _ => false)
    rw [empty] at h
    change true = false at h
    exact Bool.noConfusion h
  let x : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 1)
  let y : Fin 9 → Bool := fun j => decide (j = 2 ∨ j = 3)
  have fx : f x = true := by decide
  have fy : f y = true := by decide
  have pinTrue (z : Fin 9 → Bool) (hz : f z = true) (i : Fin 24) (hi : i ∈ pins) :
      (wires z).getD i.val false = true := by
    have h := correct z
    change (pins.map fun j => (wires z).getD j.val false).all id = f z at h
    rw [hz, List.all_eq_true] at h
    exact h _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have span (i : Fin 24) (hi : i ∈ pins) : 10 ≤ i.val ∧ i.val < 10 + middle.length := by
    have hx := pinTrue x fx i hi
    have hy := pinTrue y fy i hi
    obtain ⟨xx,ex,lx⟩ := extend middle (seed x)
    obtain ⟨yy,ey,_⟩ := extend middle (seed y)
    change wires x = seed x ++ xx at ex
    change wires y = seed y ++ yy at ey
    have len : (wires x).length = 10 + middle.length := by
      rw [ex, List.length_append, seedLength, lx]
    constructor
    · by_contra! small
      rw [ex, List.getD_append _ _ _ _ (by rwa [seedLength])] at hx
      rw [ey, List.getD_append _ _ _ _ (by rwa [seedLength])] at hy
      by_cases raw : i.val < 9
      · let j : Fin 9 := ⟨i.val,raw⟩
        change (List.ofFn x ++ [x 4 || x 6]).getD j.val false = true at hx
        change (List.ofFn y ++ [y 4 || y 6]).getD j.val false = true at hy
        rw [List.getD_append _ _ _ _ (by simp), read] at hx hy
        have hx' : j = 0 ∨ j = 1 := of_decide_eq_true hx
        have hy' : j = 2 ∨ j = 3 := of_decide_eq_true hy
        rcases hx' with he | he <;> rw [he] at hy' <;> exact (by decide : ¬ _) hy'
      · have eq : i.val = 9 := by omega
        rw [eq, atNine] at hx
        change false = true at hx
        exact Bool.noConfusion hx
    · by_contra! big
      rw [List.getD_eq_default _ _ (by rwa [len])] at hx
      exact Bool.noConfusion hx
  have uniqueMiddle : ∀ v ∈ [4, 6], ∃! i : Fin middle.length,
      let g := middle.get i
      g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs := by
    intro v hv
    have vlt : v < 10 := by
      have cases : v = 4 ∨ v = 6 := by simpa using hv
      rcases cases with rfl | rfl <;> decide
    let reads (g : Gate) := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
    have lastDoesNotRead : ¬ reads last := by
      intro hh
      have member : v ∈ last.inputs := by
        rcases hh with first | other
        · exact List.mem_of_getElem? first
        · exact other.2
      change v ∈ pins.map Fin.val at member
      obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
      exact (Nat.not_le_of_lt vlt) (eq ▸ (span j hj).1)
    have full : ∃! i : Fin tail.length, reads (tail.get i) := uniqueReaders v hv
    obtain ⟨i,hi,uniq⟩ := full
    have tailLength : tail.length = middle.length + 1 := by simp [tail]
    have beforeEnd : i.val < middle.length := by
      by_contra! after
      have lastGate : tail.get i = last := by
        change (middle ++ [last])[i.val]'i.isLt = last
        simp only [List.getElem_append_right after, List.getElem_singleton]
      exact lastDoesNotRead (lastGate ▸ hi)
    let widen (j : Fin middle.length) : Fin tail.length :=
      ⟨j.val, by rw [tailLength]; exact Nat.lt_succ_of_lt j.isLt⟩
    have gateEq (j : Fin middle.length) : tail.get (widen j) = middle.get j := by
      change (middle ++ [last])[j.val]'(widen j).isLt = middle[j.val]
      rw [List.getElem_append_left j.isLt]
    let j : Fin middle.length := ⟨i.val,beforeEnd⟩
    change ∃! k : Fin middle.length, reads (middle.get k)
    refine ⟨j, ?_, ?_⟩
    · change reads (middle.get j)
      rw [← gateEq j]
      have widenJ : widen j = i := Fin.ext rfl
      rwa [widenJ]
    · intro k hk
      have widerReads : reads (tail.get (widen k)) := by rwa [gateEq]
      apply Fin.ext
      exact congrArg (fun a : Fin tail.length => a.val) (uniq _ widerReads)
  have remaining := residual middle pins budget fan bounds pinLength pinsNonempty span uniqueMiddle
  obtain ⟨z, bad⟩ := remaining
  apply bad
  change GateOp.and.eval (pins.map fun i => (wires z).getD i.val false) = _
  rw [correct z]
  simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rfl
