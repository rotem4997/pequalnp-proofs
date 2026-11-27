import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pin either endpoint of the first AND to false. Its output becomes false as
-- well. Each later gate that effectively reads either fixed wire disappears.
theorem PEqualNP.Outside.R_meta_1669_303
    (pin : ∀ (m : ℕ) (D : Circuit) (w : List (Option (Fin m))) (S : List ℕ),
      FanInTwo D → (∀ i ∈ S, w[i]? = some none) →
      (∃ a b : Fin m → Bool, D.eval (w.map fun q => q.elim false a) ≠
        D.eval (w.map fun q => q.elim false b)) →
      ∃ E : Circuit, FanInTwo E ∧
        E.size + (D.gates.filter (fun g => S.any fun i => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i)).length ≤ D.size ∧
        ∀ y : Fin m → Bool, E.eval (List.ofFn y) = D.eval (w.map fun q => q.elim false y))
    (lower :
      let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => F (Fin.cons false y)) 11)
    (sibling : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (sparse : ∀ D : Circuit, FanInTwo D →
      (∃ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 3]) ≠
        D.eval (List.ofFn y ++ [y 4 && y 6])) →
      (∃ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 3]) ≠
        D.eval (List.ofFn y ++ [false])) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 3]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      (∀ i ∈ ([0,3] : List ℕ),
        (D.gates.filter (fun g => [i,9].any fun k =>
          (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains k)).length ≤ 2) →
      15 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  intro C hFan hHead computes
  by_contra! tooSmall
  obtain ⟨gs, o⟩ := C
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have kept (rs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (rs.foldl step w).getD i false = w.getD i false := by
    induction rs generalizing w with
    | nil => rfl
    | cons g rs ih =>
      rw [List.foldl_cons]
      have hi' : i < (step w g).length := by simp [step]; omega
      rw [ih _ hi', List.getD_append _ _ _ _ hi]
  cases gs with
  | nil =>
    have h := hHead (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ _ (by simp)] at h
    contradiction
  | cons first tail =>
    let D : Circuit := ⟨tail, o⟩
    have hD : FanInTwo D := fun g hg => hFan g (List.mem_cons_of_mem _ hg)
    have cap : D.size ≤ 14 := by
      change (first :: tail).length < 16 at tooSmall
      change tail.length ≤ 14
      simp only [List.length_cons] at tooSmall
      omega
    have suffix (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 && x 3]) = F x := by
      have hw := hHead x
      change (tail.foldl step (step (List.ofFn x) first)).getD 9 false = _ at hw
      rw [kept tail _ 9 (by simp [step])] at hw
      have hv : first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) =
          (x 0 && x 3) := by simpa [step, List.getD_append_right] using hw
      have h := congrFun computes x
      change (tail.foldl step (List.ofFn x ++ [_])).getD o false = F x at h
      change (tail.foldl step (List.ofFn x ++ [x 0 && x 3])).getD o false = F x
      simpa only [hv] using h
    have hcount (w : List (Option (Fin 8))) (S : List ℕ)
        (fixed : ∀ i ∈ S, w[i]? = some none)
        (fiber : ∀ y : Fin 8 → Bool, D.eval (w.map fun q => q.elim false y) = F (Fin.cons false y)) :
        (D.gates.filter (fun g => S.any fun i => (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i)).length ≤ 2 := by
      let a : Fin 8 → Bool := fun _ => false
      let b : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have hn : D.eval (w.map fun q => q.elim false a) ≠ D.eval (w.map fun q => q.elim false b) := by
        rw [fiber a, fiber b]
        decide
      obtain ⟨E, hE, cost, truth⟩ := pin 8 D w S hD fixed ⟨a,b,hn⟩
      by_contra! large
      apply lower
      exact ⟨E, hE, by omega, fun y => (truth y).trans (fiber y)⟩
    have separates : ∃ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 3]) ≠
        D.eval (List.ofFn y ++ [y 4 && y 6]) := by
      by_contra! same
      let g : Gate := ⟨.and, [4,6]⟩
      let C' : Circuit := ⟨g :: tail,o⟩
      have fan' : FanInTwo C' := by
        intro z hz
        change z ∈ g :: tail at hz
        rcases List.mem_cons.mp hz with rfl | ht
        · exact ⟨Or.inl rfl, by decide⟩
        · exact hD z ht
      have gateValue (y : Fin 9 → Bool) : step (List.ofFn y) g =
          List.ofFn y ++ [y 4 && y 6] := by
        change List.ofFn y ++ [(List.ofFn y).getD 4 false && ((List.ofFn y).getD 6 false && true)] = _
        simp [List.getD_eq_getElem?_getD]
      have first' (y : Fin 9 → Bool) : (C'.wires (List.ofFn y)).getD 9 false = (y 4 && y 6) := by
        change (tail.foldl step (step (List.ofFn y) g)).getD 9 false = _
        rw [gateValue, kept tail _ 9 (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp
      have truth' : circuitFun 9 C' = F := by
        funext y
        change (tail.foldl step (step (List.ofFn y) g)).getD o false = _
        rw [gateValue]
        exact (same y).symm.trans (suffix y)
      have bound := sibling C' fan' first' truth'
      change 16 ≤ (g :: tail).length at bound
      change tail.length ≤ 14 at cap
      simp only [List.length_cons] at bound
      omega
    have add_first (E : Circuit) (hE : FanInTwo E) :
        ∃ C : Circuit, FanInTwo C ∧ C.size = E.size + 1 ∧
          (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) ∧
          circuitFun 9 C = circuitFun 9 E := by
      let sh (i : ℕ) := if i < 9 then i else i+1
      let ren (g : Gate) : Gate := ⟨g.op, g.inputs.map sh⟩
      let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have lookup (x : Fin 9 → Bool) (r : List Bool) (b : Bool) (i : ℕ) :
          ((List.ofFn x ++ [b]) ++ r).getD (sh i) false = (List.ofFn x ++ r).getD i false := by
        by_cases short : i < 9
        · simp only [sh, short, ite_true]
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          rw [List.getD_append _ _ _ _ (by simpa using short)]
          rw [List.getD_append _ _ _ _ (by simpa using short)]
        · simp only [sh, short, ite_false]
          rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_append, List.length_ofFn, List.length_singleton]
          congr 1
      have run (rs : List Gate) (x : Fin 9 → Bool) (b : Bool) : ∀ r : List Bool,
          ∃ t, rs.foldl step (List.ofFn x ++ r) = List.ofFn x ++ t ∧
            (rs.map ren).foldl step ((List.ofFn x ++ [b]) ++ r) = (List.ofFn x ++ [b]) ++ t := by
        induction rs with
        | nil => intro r; exact ⟨r,rfl,rfl⟩
        | cons h rs ih =>
          intro r
          let v := h.op.eval (h.inputs.map fun i => (List.ofFn x ++ r).getD i false)
          have same : (ren h).op.eval ((ren h).inputs.map
              fun i => ((List.ofFn x ++ [b]) ++ r).getD i false) = v := by
            change h.op.eval ((h.inputs.map sh).map _) = _
            rw [List.map_map]
            apply congrArg h.op.eval
            apply List.map_congr_left
            intro i _
            exact lookup x r b i
          obtain ⟨t, h1, h2⟩ := ih (r ++ [v])
          refine ⟨t, ?_, ?_⟩
          · simpa only [List.foldl_cons, step, List.append_assoc, v] using h1
          · change (rs.map ren).foldl step ((((List.ofFn x ++ [b]) ++ r) ++
                [(ren h).op.eval ((ren h).inputs.map fun i => ((List.ofFn x ++ [b]) ++ r).getD i false)])) =
                (List.ofFn x ++ [b]) ++ t
            rw [same]
            simpa only [List.append_assoc] using h2
      let g : Gate := ⟨.and,[4,6]⟩
      let C : Circuit := ⟨g :: E.gates.map ren, sh E.output⟩
      have hv (x : Fin 9 → Bool) : step (List.ofFn x) g = List.ofFn x ++ [x 4 && x 6] := by
        change List.ofFn x ++ [(List.ofFn x).getD 4 false && ((List.ofFn x).getD 6 false && true)] = _
        simp [List.getD_eq_getElem?_getD]
      refine ⟨C, ?_, ?_, ?_, ?_⟩
      · intro h hh
        change h ∈ g :: E.gates.map ren at hh
        rcases List.mem_cons.mp hh with rfl | hh
        · exact ⟨Or.inl rfl, by decide⟩
        · obtain ⟨h', hE', rfl⟩ := List.mem_map.mp hh
          exact ⟨(hE h' hE').1, by simpa [ren] using (hE h' hE').2⟩
      · change (g :: E.gates.map ren).length = E.gates.length + 1
        simp
      · intro x
        obtain ⟨t, _, qr⟩ := run E.gates x (x 4 && x 6) []
        simp only [List.append_nil] at qr
        change ((E.gates.map ren).foldl step (step (List.ofFn x) g)).getD 9 false = _
        rw [hv, qr, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp
      · funext x
        obtain ⟨t, ql, qr⟩ := run E.gates x (x 4 && x 6) []
        simp only [List.append_nil] at ql qr
        change ((E.gates.map ren).foldl step (step (List.ofFn x) g)).getD (sh E.output) false =
          (E.gates.foldl step (List.ofFn x)).getD E.output false
        rw [hv, ql, qr]
        exact lookup x t (x 4 && x 6) E.output
    have needed : ∃ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 3]) ≠
        D.eval (List.ofFn y ++ [false]) := by
      by_contra! same
      have pinned (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [false]) = F x :=
        (same x).symm.trans (suffix x)
      let w : List (Option (Fin 9)) := (List.ofFn fun i : Fin 9 => some i) ++ [none]
      have rows (x : Fin 9 → Bool) : w.map (fun p => p.elim false x) = List.ofFn x ++ [false] := by
        simp [w]
      have preserved (x : Fin 9 → Bool) : D.eval (w.map fun p => p.elim false x) = F x := by
        rw [rows, pinned]
      let a : Fin 9 → Bool := fun _ => false
      let b : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have hn : D.eval (w.map fun p => p.elim false a) ≠ D.eval (w.map fun p => p.elim false b) := by
        rw [preserved a, preserved b]
        decide
      obtain ⟨E, hE, ecost, etruth⟩ := pin 9 D w [] hD (by simp) ⟨a,b,hn⟩
      have ele : E.size ≤ D.size := (Nat.le_add_right _ _).trans ecost
      have et : circuitFun 9 E = F := funext fun x => (etruth x).trans (preserved x)
      obtain ⟨C', hc', length', head', eval'⟩ := add_first E hE
      have lb := sibling C' hc' head' (eval'.trans et)
      omega
    have low := sparse D hD separates needed suffix (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · let w : List (Option (Fin 8)) :=
          [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, none]
        apply hcount w [0,9] (by decide)
        intro y
        have e : w.map (fun q => q.elim false y) = List.ofFn (Fin.cons false y : Fin 9 → Bool) ++
            [(Fin.cons false y : Fin 9 → Bool) 0 && (Fin.cons false y : Fin 9 → Bool) 3] := by
          simp [w, List.ofFn_succ, Fin.cons]
        rw [e, suffix]
      · let w : List (Option (Fin 8)) :=
          [some 2, some 1, some 0, none, some 3, some 7, some 6, some 5, some 4, none]
        apply hcount w [3,9] (by decide)
        intro y
        let x : Fin 9 → Bool := ![y 2,y 1,y 0,false,y 3,y 7,y 6,y 5,y 4]
        have e : w.map (fun q => q.elim false y) = List.ofFn x ++ [x 0 && x 3] := by
          simp [w, x, List.ofFn_succ]
        rw [e, suffix]
        change F (![y 2,y 1,y 0,false,y 3,y 7,y 6,y 5,y 4]) = F (Fin.cons false y)
        simp [F, Fin.cons]
        ac_rfl)
    omega
