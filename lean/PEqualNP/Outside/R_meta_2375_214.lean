import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2375_214
    (cost : let F := fun (x : Fin 10 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  ∀ C : Circuit, FanInTwo C → circuitFun 10 C = F →
    16 ≤ C.gates.countP (fun g => !(g.op.eval [false])))
    (remaining : let F := fun (x : Fin 10 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  ∀ (C : Circuit) (i j : Fin 28), FanInTwo C → C.size = 18 →
    15 ≤ C.gates.countP (fun g => !(g.op.eval [false])) →
    let w := fun (x : Fin 10 → Bool) k => (C.wires (List.ofFn x)).getD k false
    (∃ x, w x i = true ∧ w x j = false) →
    (∃ x, w x i = false ∧ w x j = true) →
    ¬ (∀ x, (w x i && w x j) = F x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro g D i j hg hd hsmall F w hi hj hpos
  by_contra absent
  let C : Circuit := ⟨g :: D.gates, 0⟩
  let last : Gate := ⟨.and,[i,j]⟩
  let total : Circuit := ⟨C.gates ++ [last],10+C.gates.length⟩
  have ok : FanInTwo C := by
    intro h mem
    rcases List.mem_cons.mp mem with rfl|mem
    · exact hg _ (by simp)
    · exact hd _ mem
  have size : C.size ≤ 18 := by
    change D.gates.length ≤ 17 at hsmall
    change (g::D.gates).length ≤ 18
    simp; omega
  have legal : FanInTwo total := by
    intro h mem
    rcases List.mem_append.mp mem with mem|mem
    · exact ok _ mem
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨Or.inl rfl,by simp [last]⟩
  have equals (x) : (w x i && w x j)=F x := by
    cases h : F x with
    | false =>
      cases a : w x i <;> cases b : w x j <;> try rfl
      exact False.elim (absent ⟨x,h,a,b⟩)
    | true => obtain ⟨a,b⟩ := hpos x h; simp [a,b]
  have length (gs : List Gate) (initial : List Bool) :
      ((⟨gs,0⟩ : Circuit).wires initial).length = initial.length+gs.length := by
    induction gs generalizing initial with
    | nil => rfl
    | cons h hs ih =>
      change ((⟨hs,0⟩ : Circuit).wires (initial++[_])).length=_
      rw [ih]; simp; omega
  have hit : circuitFun 10 total = F := by
    funext x
    let prev := C.wires (List.ofFn x)
    have plen : prev.length=total.output := by
      change ((⟨C.gates,0⟩ : Circuit).wires (List.ofFn x)).length=10+C.gates.length
      rw [length,List.length_ofFn]
    change (total.wires (List.ofFn x)).getD total.output false=_
    have run : total.wires (List.ofFn x) = prev++[w x i && w x j] := by
      change List.foldl _ _ (C.gates ++ [last]) = _
      rw [List.foldl_append]
      change prev ++ [[w x i,w x j].all id] = _
      simp only [List.all_cons,List.all_nil,id_eq,Bool.and_true]
    rw [run,← plen]
    simpa [List.getD_eq_getElem?_getD] using equals x
  have low := cost total legal hit
  have count : total.gates.countP (fun h => !(h.op.eval [false])) =
      C.gates.countP (fun h => !(h.op.eval [false])) + 1 := by
        change (C.gates++[last]).countP _ = _
        rw [List.countP_append]
        rfl
  have bound : 15 ≤ C.gates.countP (fun h => !(h.op.eval [false])) :=
    Nat.le_of_succ_le_succ (calc
      16 ≤ total.gates.countP (fun h => !(h.op.eval [false])) := low
      _ = _ := count)
  let pad : Gate := ⟨.or,[]⟩
  let P : Circuit := ⟨C.gates ++ List.replicate (18-C.size) pad,0⟩
  have psize : P.size=18 := by
    change (C.gates ++ List.replicate (18-C.gates.length) pad).length=18
    change C.gates.length ≤ 18 at size
    simp; omega
  have pok : FanInTwo P := by
    intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact ok _ hq
    · have e : q=pad := (List.mem_replicate.mp hq).2
      subst q
      exact ⟨Or.inr (Or.inl rfl),by simp [pad]⟩
  have pcost : 15 ≤ P.gates.countP (fun h => !(h.op.eval [false])) := by
    change 15 ≤ (C.gates ++ _).countP _
    rw [List.countP_append]
    omega
  have aux (n : Nat) (start : List Bool) :
      ((⟨List.replicate n pad,0⟩ : Circuit).wires start) = start++List.replicate n false := by
    induction n generalizing start with
    | zero => exact (List.append_nil start).symm
    | succ n ih =>
      rw [List.replicate_succ]
      change ((⟨List.replicate n pad,0⟩ : Circuit).wires (start++[false]))=_
      rw [ih,List.append_assoc,List.replicate_succ]
      rfl
  have same (x : Fin 10→Bool) (k : Nat) : (P.wires (List.ofFn x)).getD k false = w x k := by
    let base := C.wires (List.ofFn x)
    have ep : P.wires (List.ofFn x)=base++List.replicate (18-C.size) false := by
      change List.foldl _ _ (C.gates++_)=_
      rw [List.foldl_append]
      exact aux _ base
    rw [ep]; change (base++_).getD k false=base.getD k false
    by_cases hk : k<base.length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hk]
    · have he : base[k]?=none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : base.length≤k),he,
        List.getElem?_replicate]
      split <;> rfl
  have wi (k : Nat) (h : ∃ x, w x k=true) : k<28 := by
    obtain ⟨x,hx⟩ := h
    have n : (P.wires (List.ofFn x)).length=28 := by
      have l := length P.gates (List.ofFn x)
      change (P.wires (List.ofFn x)).length=_ at l
      change P.gates.length=18 at psize
      simpa [psize] using l
    by_contra! ge
    have empty : (P.wires (List.ofFn x))[k]?=none := List.getElem?_eq_none (by omega)
    rw [←same x k,List.getD_eq_getElem?_getD,empty] at hx
    contradiction
  obtain ⟨xi,ai,bi⟩ := hi
  obtain ⟨xj,aj,bj⟩ := hj
  let a : Fin 28 := ⟨i,wi i ⟨xi,ai⟩⟩
  let b : Fin 28 := ⟨j,wi j ⟨xj,bj⟩⟩
  apply remaining P a b pok psize pcost
  · exact ⟨xi,(same xi i).trans ai,(same xi j).trans bi⟩
  · exact ⟨xj,(same xj i).trans aj,(same xj j).trans bj⟩
  · intro x
    exact (congrArg₂ Bool.and (same x i) (same x j)).trans (equals x)
