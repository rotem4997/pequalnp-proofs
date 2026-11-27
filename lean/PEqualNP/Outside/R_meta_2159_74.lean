import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2159_74 :
    (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
      x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12) →
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
         (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
     ∀ C : Circuit, FanInTwo C → (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
       (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
       C.size ≤ 15 →
       (∀ v : Fin 3, C.gates.countP (fun g => g.inputs.contains (![4, 6, 7] v)) ≤ 2) →
       circuitFun 9 C ≠ f) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro lower remaining C fanin noNot first computes
  by_contra! large
  have small : C.size ≤ 15 := by omega
  let f : (Fin 9 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have graph (x : Fin 9 → Bool) : f x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 ||
      (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 ||
      (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = _
    simp only [Bool.or_false, Bool.or_assoc]
  have exactC : circuitFun 9 C = f := funext fun x => (congrFun computes x).trans (graph x).symm
  have positive (g : Gate) (mem : g ∈ C.gates) : g.op = .and ∨ g.op = .or := by
    have op := (fanin g mem).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, noNot g mem, or_false] using op
  have budget : ∀ v : Fin 3, C.gates.countP (fun g => g.inputs.contains (![4, 6, 7] v)) ≤ 2 := by
    intro j
    by_contra! many
    let vertex : ℕ := ![4, 6, 7] j
    let mapping : Fin 3 → Fin 9 → ℕ :=
      ![![0, 1, 2, 3, 100, 4, 5, 6, 7],
        ![1, 0, 4, 7, 5, 2, 100, 6, 3],
        ![2, 1, 0, 4, 6, 3, 5, 100, 7]]
    let table : List ℕ := List.ofFn (mapping j)
    let embed : (Fin 8 → Bool) → Fin 9 → Bool := fun y i =>
      (List.ofFn y).getD (mapping j i) false
    have mapLen : table.length = 9 := by simp [table]
    have vertexBound : vertex < 9 := by fin_cases j <;> dsimp only [vertex] <;> decide
    have mapVertex : table.getD vertex 100 = 100 := by
      fin_cases j <;> dsimp only [table, mapping, vertex] <;> decide
    have mapValid (i : ℕ) : table.getD i 100 < 8 ∨ table.getD i 100 = 100 := by
      by_cases inside : i < 9
      · have checked : ∀ (k : Fin 3) (a : Fin 9),
          (List.ofFn (mapping k)).getD a 100 < 8 ∨ (List.ofFn (mapping k)).getD a 100 = 100 := by
          dsimp only [mapping]
          decide
        exact checked j ⟨i, inside⟩
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Or.inr rfl
    have raw (y : Fin 8 → Bool) (i : ℕ) :
        (List.ofFn (embed y)).getD i false = (List.ofFn y).getD (table.getD i 100) false := by
      by_cases inside : i < 9
      · have hx : i < (List.ofFn (embed y)).length := by simpa
        have ht : table.getD i 100 = mapping j ⟨i, inside⟩ := by
          change (List.ofFn (mapping j)).getD i 100 = _
          rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
        rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn, ht]
      · rw [List.getD_eq_default (List.ofFn (embed y)) _ (by simp; omega),
          List.getD_eq_default table _ (by omega),
          List.getD_eq_default (List.ofFn y) _ (by simp)]
    have cofactor (y : Fin 8 → Bool) : f (embed y) =
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
          y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4) := by
      rw [graph]
      fin_cases j
      · change (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && false ||
          false && y 0 || y 0 && y 4 || y 1 && y 5 || y 2 && y 6 || y 3 && y 7 ||
          y 4 && y 6 || y 5 && y 7 || y 7 && y 4) = _
        simp only [Bool.and_false, Bool.false_and, Bool.or_false]
      · change (y 1 && y 0 || y 0 && y 4 || y 4 && y 7 || y 7 && y 5 ||
          y 5 && y 1 || y 1 && y 2 || y 0 && false || y 4 && y 6 || y 7 && y 3 ||
          y 2 && y 6 || false && y 3 || y 3 && y 2) = _
        simp only [Bool.and_false, Bool.false_and, Bool.or_false]
        ac_rfl
      · change (y 2 && y 1 || y 1 && y 0 || y 0 && y 4 || y 4 && y 6 ||
          y 6 && y 2 || y 2 && y 3 || y 1 && y 5 || y 0 && false || y 4 && y 7 ||
          y 3 && false || y 5 && y 7 || y 7 && y 3) = _
        simp only [Bool.and_false, Bool.or_false]
        ac_rfl
    classical
    let step : List Bool → Gate → List Bool := fun u g =>
      u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    let normalize : List ℕ × List Gate → Gate → List ℕ × List Gate := fun acc g =>
      if g.inputs.contains vertex then
        let wire := if g.op = GateOp.or then
          acc.1.getD ((g.inputs.filter fun i => i != vertex).headD vertex) 100 else 100
        (acc.1 ++ [wire], acc.2)
      else
        (acc.1 ++ [8 + acc.2.length],
          acc.2 ++ [⟨g.op, g.inputs.map fun i => acc.1.getD i 100⟩])
    have safeAnd (vals : List Bool) (mem : false ∈ vals) : vals.all id = false := by
      by_contra diff
      exact Bool.noConfusion ((List.all_eq_true.mp (Bool.eq_true_of_not_eq_false diff)) false mem)
    have safeOr (is : List ℕ) (len : is.length ≤ 2) (has : vertex ∈ is)
        (r : ℕ → Bool) (zero : r vertex = false) :
        (is.map r).any id = r ((is.filter fun i => i != vertex).headD vertex) := by
      rcases is with _ | ⟨a, _ | ⟨b, _ | ⟨c, is⟩⟩⟩
      · simp at has
      · have eq : a = vertex := (List.mem_singleton.mp has).symm
        subst a
        simp [zero]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at has
        rcases has with h | h
        · subst a
          by_cases same : b = vertex
          · subst b
            simp [zero]
          · simp [same, zero]
        · subst b
          by_cases same : a = vertex
          · subst a
            simp [zero]
          · simp [same, zero]
      · simp at len
    have getLast {α : Type} (xs : List α) (x d : α) :
        (xs ++ [x]).getD xs.length d = x := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have skipLast {α : Type} (xs : List α) (x d : α) (i : ℕ) (ne : i ≠ xs.length) :
        (xs ++ [x]).getD i d = xs.getD i d := by
      by_cases early : i < xs.length
      · exact List.getD_append _ _ _ _ early
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have stepLen (rs : List Gate) (xs : List Bool) :
        (rs.foldl step xs).length = xs.length + rs.length := by
      induction rs generalizing xs with
      | nil => simp
      | cons g rs ih =>
        rw [List.foldl_cons, ih]
        simp [step]
        omega
    have normalized (rs : List Gate) (acc : List ℕ × List Gate) (old : List Bool)
        (y : Fin 8 → Bool)
        (pos : ∀ g ∈ rs, g.op = .and ∨ g.op = .or)
        (arity : ∀ g ∈ rs, g.inputs.length ≤ 2)
        (aligned : old.length = acc.1.length)
        (bound : 8 + acc.2.length + rs.length < 100)
        (before : vertex < acc.1.length)
        (masked : acc.1.getD vertex 100 = 100)
        (index : ∀ i, acc.1.getD i 100 < 8 + acc.2.length ∨ acc.1.getD i 100 = 100)
        (agree : ∀ i, old.getD i false =
          (acc.2.foldl step (List.ofFn y)).getD (acc.1.getD i 100) false)
        (okAcc : FanInTwo ⟨acc.2, 0⟩) :
        let out := rs.foldl normalize acc
        (∀ i, (rs.foldl step old).getD i false =
          (out.2.foldl step (List.ofFn y)).getD (out.1.getD i 100) false) ∧
        FanInTwo ⟨out.2, 0⟩ ∧
        out.2.length + rs.countP (fun g => g.inputs.contains vertex) ≤ acc.2.length + rs.length := by
      induction rs generalizing acc old with
      | nil => exact ⟨agree, okAcc, by simp⟩
      | cons g rs ih =>
        let new := acc.2.foldl step (List.ofFn y)
        have newLen : new.length = 8 + acc.2.length := by simp [new, stepLen]
        have no100 : new.getD 100 false = false := List.getD_eq_default _ _ (by omega)
        have p := pos g (by simp)
        have maxArity := arity g (by simp)
        have tailPos : ∀ q ∈ rs, q.op = .and ∨ q.op = .or :=
          fun q mem => pos q (List.mem_cons_of_mem _ mem)
        have tailArity : ∀ q ∈ rs, q.inputs.length ≤ 2 :=
          fun q mem => arity q (List.mem_cons_of_mem _ mem)
        change (∀ i, (rs.foldl step (step old g)).getD i false =
            ((rs.foldl normalize (normalize acc g)).2.foldl step (List.ofFn y)).getD
              ((rs.foldl normalize (normalize acc g)).1.getD i 100) false) ∧
          FanInTwo ⟨(rs.foldl normalize (normalize acc g)).2, 0⟩ ∧
          (rs.foldl normalize (normalize acc g)).2.length +
            (g :: rs).countP (fun q => q.inputs.contains vertex) ≤ acc.2.length + (g :: rs).length
        by_cases reads : g.inputs.contains vertex = true
        · have mem : vertex ∈ g.inputs := List.contains_iff_mem.mp reads
          let q := (g.inputs.filter fun i => i != vertex).headD vertex
          let a := if g.op = GateOp.or then acc.1.getD q 100 else 100
          let b : List ℕ × List Gate := (acc.1 ++ [a], acc.2)
          have same : normalize acc g = b := by
            dsimp only [normalize]
            rw [ite_eq_left reads]
          rw [same]
          have keptMask : b.1.getD vertex 100 = 100 := by
            change (acc.1 ++ [_]).getD vertex 100 = _
            rw [List.getD_append _ _ _ _ before, masked]
          have keepIndex (i : ℕ) : b.1.getD i 100 < 8 + b.2.length ∨ b.1.getD i 100 = 100 := by
            change (acc.1 ++ [a]).getD i 100 < 8 + acc.2.length ∨
              (acc.1 ++ [a]).getD i 100 = 100
            by_cases eq : i = acc.1.length
            · subst i
              rw [getLast]
              by_cases disj : g.op = .or
              · simpa [a, disj] using index q
              · simp [a, disj]
            · simpa only [skipLast _ _ _ _ eq] using index i
          have isZero : old.getD vertex false = false := by
            rw [agree, masked]
            exact no100
          have equalWire : g.op.eval (g.inputs.map fun i => old.getD i false) = new.getD a false := by
            rcases p with p | p
            · rw [p]
              change (g.inputs.map fun i => old.getD i false).all id = _
              rw [safeAnd _ (List.mem_map.mpr ⟨vertex, mem, isZero⟩)]
              have redirected : a = 100 := by simp [a, p]
              rw [redirected, no100]
            · rw [p]
              change (g.inputs.map fun i => old.getD i false).any id = _
              rw [safeOr g.inputs maxArity mem _ isZero]
              have redirected : a = acc.1.getD q 100 := by simp [a, p]
              change old.getD q false = new.getD a false
              rw [redirected]
              exact agree q
          have keepAgree (i : ℕ) : (step old g).getD i false =
              (b.2.foldl step (List.ofFn y)).getD (b.1.getD i 100) false := by
            change (old ++ [_]).getD i false = new.getD ((acc.1 ++ [a]).getD i 100) false
            by_cases eq : i = acc.1.length
            · have eqOld : i = old.length := by omega
              rw [eq, getLast, ← aligned, getLast]
              exact equalWire
            · rw [skipLast _ _ _ _ (by omega), skipLast _ _ _ _ eq]
              exact agree i
          have next := ih b (step old g) tailPos tailArity
            (by simp [b, step, aligned]) (by dsimp [b]; simp at bound; omega)
            (by simp [b]; omega) keptMask keepIndex keepAgree okAcc
          refine ⟨next.1, next.2.1, ?_⟩
          have nextCount : (rs.foldl normalize b).2.length +
              rs.countP (fun q => q.inputs.contains vertex) ≤ acc.2.length + rs.length := next.2.2
          have count := List.countP_cons_of_pos (p := fun q : Gate => q.inputs.contains vertex)
            (a := g) (l := rs) reads
          rw [count, List.length_cons]
          omega
        · let r : Gate := ⟨g.op, g.inputs.map fun i => acc.1.getD i 100⟩
          let b : List ℕ × List Gate := (acc.1 ++ [8 + acc.2.length], acc.2 ++ [r])
          have same : normalize acc g = b := by
            dsimp only [normalize]
            rw [ite_eq_right reads]
          rw [same]
          have keptMask : b.1.getD vertex 100 = 100 := by
            change (acc.1 ++ [_]).getD vertex 100 = _
            rw [List.getD_append _ _ _ _ before, masked]
          have keepIndex (i : ℕ) : b.1.getD i 100 < 8 + b.2.length ∨ b.1.getD i 100 = 100 := by
            have nb : 8 + b.2.length = 8 + acc.2.length + 1 := by simp [b]; omega
            rw [nb]
            change (acc.1 ++ [_]).getD i 100 < _ ∨ (acc.1 ++ [_]).getD i 100 = 100
            by_cases eq : i = acc.1.length
            · subst i
              rw [getLast]
              exact Or.inl (by omega)
            · rw [skipLast _ _ _ _ eq]
              rcases index i with h | h
              · exact Or.inl (by omega)
              · exact Or.inr h
          have appendNew : b.2.foldl step (List.ofFn y) = step new r := by
            exact List.foldl_append
          have equalGate : g.op.eval (g.inputs.map fun i => old.getD i false) =
              r.op.eval (r.inputs.map fun i => new.getD i false) := by
            simp only [r, List.map_map, agree]
            rfl
          have keepAgree (i : ℕ) : (step old g).getD i false =
              (b.2.foldl step (List.ofFn y)).getD (b.1.getD i 100) false := by
            rw [appendNew]
            change (old ++ [_]).getD i false = (new ++ [_]).getD ((acc.1 ++ [_]).getD i 100) false
            by_cases eq : i = acc.1.length
            · rw [eq, getLast, ← newLen, getLast, ← aligned, getLast]
              exact equalGate
            · rw [skipLast _ _ _ _ (by omega), skipLast _ _ _ _ eq, skipLast _ _ _ _]
              · exact agree i
              · rcases index i with h | h <;> omega
          have okNext : FanInTwo ⟨b.2, 0⟩ := by
            intro q mem
            change q ∈ acc.2 ++ [r] at mem
            rcases List.mem_append.mp mem with old | new
            · exact okAcc q old
            · have h : q = r := by simpa using new
              subst q
              exact ⟨(p.elim (fun h => by simp [r, h]) (fun h => by simp [r, h])),
                by simpa [r] using maxArity⟩
          have next := ih b (step old g) tailPos tailArity
            (by simp [b, step, aligned]) (by simp [b] at bound ⊢; omega)
            (by simp [b]; omega) keptMask keepIndex keepAgree okNext
          refine ⟨next.1, next.2.1, ?_⟩
          have nextCount : (rs.foldl normalize b).2.length +
              rs.countP (fun q => q.inputs.contains vertex) ≤ b.2.length + rs.length := next.2.2
          have newSize : b.2.length = acc.2.length + 1 := by simp [b]
          rw [newSize] at nextCount
          have count := List.countP_cons_of_neg (p := fun q : Gate => q.inputs.contains vertex)
            (a := g) (l := rs) reads
          rw [count, List.length_cons]
          omega
    let result := C.gates.foldl normalize (table, [])
    let D : Circuit := ⟨result.2, result.1.getD C.output 100⟩
    have evalSlice (y : Fin 8 → Bool) :
        (∀ i, (C.gates.foldl step (List.ofFn (embed y))).getD i false =
          (D.gates.foldl step (List.ofFn y)).getD (result.1.getD i 100) false) ∧
        FanInTwo D ∧ D.size + C.gates.countP (fun g => g.inputs.contains vertex) ≤ C.size := by
      have h := normalized C.gates (table, []) (List.ofFn (embed y)) y positive
        (fun g hg => (fanin g hg).2) (by simp [mapLen])
        (by change 8 + 0 + C.size < 100; omega)
        (by change vertex < table.length; omega) mapVertex mapValid (raw y)
        (by intro g hg; exact (List.not_mem_nil hg).elim)
      refine ⟨h.1, h.2.1, ?_⟩
      change result.2.length + C.gates.countP (fun g => g.inputs.contains vertex) ≤ C.gates.length
      simpa only [result, List.length_nil, Nat.zero_add] using h.2.2
    obtain ⟨_, faninD, sizeD⟩ := evalSlice (fun _ => false)
    change 2 < C.gates.countP (fun g => g.inputs.contains vertex) at many
    apply lower
    refine ⟨D, faninD, by omega, ?_⟩
    intro y
    have equal := (evalSlice y).1 C.output
    exact equal.symm.trans ((congrFun exactC (embed y)).trans (cofactor y))
  exact remaining C fanin noNot first small budget exactC
