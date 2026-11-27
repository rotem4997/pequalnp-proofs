import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The two hypotheses concern extracting a single OR reading the leaf and repairing its ownership.
-- With a two-gate budget the old owners lift and a fresh AND owns the restored edge.
theorem PEqualNP.Outside.R_meta_4626_1
    (extract : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
      (z u : Fin n), G.degree z = 1 → G.Adj z u → H = G.deleteEdges {s(z,u)} →
      (∃ a b, H.Adj a b) → ∀ M : Circuit, IsMinimalMonoCircuit n M →
      circuitFun n M = graphFun H ∅ →
      (∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size < M.size + 2) →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        C.size = M.size + 1 ∧ (C.gates.filter (fun g => decide (z.val ∈ g.inputs))).map Gate.op = [.or])
    (repair : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      ∀ z u, G.degree z = 1 → G.Adj z u → H = G.deleteEdges {s(z,u)} →
      ∀ M C : Circuit, IsMinimalMonoCircuit n M → circuitFun n M = graphFun H ∅ →
      (∀ j < M.gates.length, (gateAt M j).op = GateOp.and → ∃ a b, H.Adj a b ∧ Owns n M j a b) →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → C.size = M.size + 1 →
      (C.gates.filter (fun g => decide (z.val ∈ g.inputs))).map Gate.op = [.or] →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∃ a b, G.Adj a b ∧ Owns n D j a b) :
∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [_x4 : DecidableRel x2.Adj] [_x5 : DecidableRel x3.Adj], (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x6) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x8 x9 : Fin x1), x2.degree x8 = (1 : ℕ) → x2.Adj x8 x9 → x3 = x2.deleteEdges {s(x8, x9)} → (∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ ∧ ∀ x14 < x13.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x13 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x17 : Fin x1) (x18 : Fin x1), x3.Adj x17 x18 ∧ PEqualNP.EdgeOwnership.Owns x1 x13 x14 x17 x18) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x14 ∧ PEqualNP.MetaComplexity.circuitFun x1 x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x15 < x14.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x14 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Fin x1) (x19 : Fin x1), x2.Adj x18 x19 ∧ PEqualNP.EdgeOwnership.Owns x1 x14 x15 x18 x19 := by
  have andDef (l : List Bool) : GateOp.eval .and l = l.all id := rfl
  have orDef (l : List Bool) : GateOp.eval .or l = l.any id := rfl
  have gateDef (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j ⟨.or, []⟩ := rfl
  have sizeDef (C : Circuit) : C.size = C.gates.length := rfl
  have conesDef (n : ℕ) (C : Circuit) : cones n C = C.gates.foldl (coneStep n) [] := rfl
  have coneDef (n : ℕ) (cs : List (List ℕ)) (g : Gate) : coneStep n cs g =
      cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  have graphDef {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
      (x : Fin n → Bool) : graphFun K A x =
        (decide (∃ a ∈ A, x a = true) || decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)) := rfl
  have pairDef {n : ℕ} (u v w : Fin n) : pairInput u v w = decide (w = u ∨ w = v) := rfl
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_length (C : Circuit) (x : List Bool) :
      (C.wires x).length = x.length + C.gates.length := by
    change (C.gates.foldl step x).length = _
    generalize C.gates = gs
    induction gs generalizing x with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step x g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.size := by
    have aux (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp
      | cons g gs ih =>
        change (gs.foldl (coneStep n) (coneStep n cs g)).length = _
        rw [ih]
        simp only [coneDef, List.length_append, List.length_cons, List.length_nil]
        omega
    simpa [conesDef, sizeDef] using aux C.gates []

  let attach {n : ℕ} (C : Circuit) (u v : Fin n) : Circuit :=
    ⟨C.gates ++ [⟨.and, [u, v]⟩, ⟨.or, [C.output, n + C.size]⟩], n + C.size + 1⟩

  have input_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
      (C.wires (List.ofFn x)).getD i false = x i := by
    have keep (gs : List Gate) (xs : List Bool) (h : i.val < xs.length) :
        (gs.foldl step xs).getD i false = xs.getD i false := by
      induction gs generalizing xs with
      | nil => rfl
      | cons g gs ih =>
        change (gs.foldl step (step xs g)).getD i false = _
        rw [ih _ (by simp [step]; omega)]
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    change (C.gates.foldl step (List.ofFn x)).getD i false = x i
    rw [keep _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]

  have attach_compute {n : ℕ} (C : Circuit) (u v : Fin n)
      (houtput : C.output ≤ n + C.size) (x : Fin n → Bool) :
      circuitFun n (attach C u v) x = (circuitFun n C x || (x u && x v)) := by
    let w := C.wires (List.ofFn x)
    have len : w.length = n + C.size := by simp [w, wires_length, sizeDef]
    let e := x u && x v
    let a : Gate := ⟨.and, [u, v]⟩
    let o : Gate := ⟨.or, [C.output, n + C.size]⟩
    have ru : w[u.val]?.getD false = x u := by
      simpa only [w, List.getD_eq_getElem?_getD] using input_wire C x u
    have rv : w[v.val]?.getD false = x v := by
      simpa only [w, List.getD_eq_getElem?_getD] using input_wire C x v
    have ha : step w a = w ++ [e] := by simp [step, a, e, andDef, ru, rv]
    have edge : (w ++ [e]).getD (n + C.size) false = e := by
      rw [← len]
      simp [List.getD_eq_getElem?_getD]
    change (List.foldl step (List.ofFn x) (C.gates ++ [a, o])).getD (n + C.size + 1) false = _
    rw [List.foldl_append]
    change (step (step w a) o).getD (n + C.size + 1) false = (w.getD C.output false || e)
    rw [ha]
    have atLast (b : Bool) : ((w ++ [e]) ++ [b]).getD (n + C.size + 1) false = b := by
      have h : (w ++ [e]).length = n + C.size + 1 := by simp [len]
      rw [← h]
      simp [List.getD_eq_getElem?_getD]
    simp only [step, o, List.map_cons, List.map_nil, orDef, List.any_cons,
      List.any_nil, id_eq, Bool.or_false]
    rw [atLast, edge]
    rcases lt_or_eq_of_le houtput with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rfl
    · rw [h, edge, List.getD_eq_default _ _ (by omega)]
      cases e <;> rfl

  have attach_old_owns {n : ℕ} (C : Circuit) (u v x y : Fin n) (j : ℕ)
      (h : Owns n C j x y) : Owns n (attach C u v) j x y := by
    let D := attach C u v
    have hg (k : ℕ) (hk : k < C.gates.length) : gateAt D k = gateAt C k := by
      simp [D, attach, gateDef, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
    have hv (k : ℕ) (hk : k < C.gates.length) :
        gateVal n D k (pairInput x y) = gateVal n C k (pairInput x y) := by
      have hw : n + k < (C.wires (List.ofFn (pairInput x y))).length := by
        rw [wires_length, List.length_ofFn]; omega
      unfold gateVal
      change ((C.gates ++ _).foldl step (List.ofFn (pairInput x y))).getD (n + k) false = _
      rw [List.foldl_append]
      change ((C.wires (List.ofFn (pairInput x y))) ++ [_] ++ [_]).getD (n + k) false = _
      rw [List.append_assoc]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
    have hc (i k : ℕ) (hk : k < C.gates.length) : InCone n D i k ↔ InCone n C i k := by
      have hw : k < (cones n C).length := by simpa [cones_length, sizeDef]
      unfold InCone
      change i ∈ ((C.gates ++ _).foldl (coneStep n) []).getD k [] ↔ _
      rw [List.foldl_append]
      change i ∈ ((cones n C) ++ [_] ++ [_]).getD k [] ↔ _
      rw [List.append_assoc]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
    obtain ⟨hj,hop, hval, hlo⟩ := h
    refine ⟨by simp [attach]; omega, (congrArg Gate.op (hg j hj)).trans hop,
      (hv j hj).trans hval, ?_⟩
    intro i hi hcone hop
    have hi' : i < C.gates.length := by omega
    rw [hv i hi']
    exact hlo i hi ((hc i j hj).mp hcone) ((congrArg Gate.op (hg i hi')).symm.trans hop)

  have attach_new_owns {n : ℕ} (C : Circuit) (u v : Fin n) :
      Owns n (attach C u v) C.size u v := by
    let D := attach C u v
    let x := pairInput u v
    let a : Gate := ⟨.and, [u, v]⟩
    let o : Gate := ⟨.or, [C.output, n + C.size]⟩
    have hop : gateAt D C.size = a := by
      simp [D, attach, a, gateDef, sizeDef, List.getD_eq_getElem?_getD]
    have hval : gateVal n D C.size x = true := by
      let w := C.wires (List.ofFn x)
      have hlen : w.length = n + C.size := by simp [w, wires_length, sizeDef]
      have e : step w a = w ++ [true] := by
        have ru : w[u.val]?.getD false = true := by
          simpa [w, List.getD_eq_getElem?_getD, x, pairDef] using input_wire C x u
        have rv : w[v.val]?.getD false = true := by
          simpa [w, List.getD_eq_getElem?_getD, x, pairDef] using input_wire C x v
        simp [step, a, andDef, ru, rv]
      change ((C.gates ++ [a, o]).foldl step (List.ofFn x)).getD (n + C.size) false = true
      rw [List.foldl_append]
      change (step (step w a) o).getD (n + C.size) false = true
      rw [e]
      change (((w ++ [true]) ++ [_]).getD (n + C.size) false) = true
      rw [List.append_assoc, ← hlen]
      simp [List.getD_eq_getElem?_getD]
    have hcone (i : ℕ) : ¬ InCone n D i C.size := by
      change i ∉ ((C.gates ++ [a, o]).foldl (coneStep n) []).getD C.size []
      rw [List.foldl_append]
      change i ∉ (coneStep n (coneStep n (cones n C) a) o).getD C.size []
      have ha : coneStep n (cones n C) a = cones n C ++ [[]] := by
        simp [coneDef, a, show ¬ n ≤ u.val by omega, show ¬ n ≤ v.val by omega]
      rw [ha]
      change i ∉ (((cones n C) ++ [[]]) ++ [_]).getD C.size []
      rw [List.append_assoc, ← cones_length n C]
      simp [List.getD_eq_getElem?_getD]
    exact ⟨by simp [attach, sizeDef], congrArg Gate.op hop, hval, fun i _ hi => (hcone i hi).elim⟩

  have attach_mono {n : ℕ} (C : Circuit) (u v : Fin n) (M : Monotone2 C) :
      Monotone2 (attach C u v) := by
    intro g hg
    rcases List.mem_append.mp hg with ho | hnew
    · exact M g ho
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hnew
      rcases hnew with rfl | rfl <;> simp

  have restored_graph {n : ℕ} (G H : SimpleGraph (Fin n))
      [DecidableRel G.Adj] [DecidableRel H.Adj] (u v : Fin n) (edge : G.Adj u v)
      (del : H = G.deleteEdges {s(u, v)}) (x : Fin n → Bool) :
      graphFun G ∅ x = (graphFun H ∅ x || (x u && x v)) := by
    rw [graphDef G, graphDef H, Bool.eq_iff_iff]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨p, q, hpq, hp, hq⟩
      by_cases removed : s(p, q) = s(u, v)
      · right
        rcases (Sym2.mk_eq_mk_iff (p := (p, q)) (q := (u, v))).mp removed with same | swap
        · cases same
          exact ⟨hp, hq⟩
        · change (p, q) = (v, u) at swap
          cases swap
          exact ⟨hq, hp⟩
      · left
        refine ⟨p, q, ?_, hp, hq⟩
        rw [del, SimpleGraph.deleteEdges_adj]
        exact ⟨hpq, removed⟩
    · rintro (⟨p, q, hpq, hp, hq⟩ | ⟨hu, hv⟩)
      · rw [del, SimpleGraph.deleteEdges_adj] at hpq
        exact ⟨p, q, hpq.1, hp, hq⟩
      · exact ⟨u, v, edge, hu, hv⟩

  have append_optimal {n : ℕ} (G H : SimpleGraph (Fin n))
      [DecidableRel G.Adj] [DecidableRel H.Adj] (u v : Fin n) (edge : G.Adj u v)
      (del : H = G.deleteEdges {s(u, v)}) (C : Circuit) (M : Monotone2 C)
      (funC : circuitFun n C = graphFun H ∅)
      (oldedge : ∃ x y, H.Adj x y)
      (bound : ∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → C.size + 2 ≤ E.size)
      (owners : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ x y, H.Adj x y ∧ Owns n C j x y) :
      ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∃ x y, G.Adj x y ∧ Owns n D j x y := by
    let D := attach C u v
    have dos : D.size = C.size + 2 := by simp [D, attach, sizeDef]
    have out : C.output ≤ n + C.size := by
      obtain ⟨x, y, hy⟩ := oldedge
      have hb : circuitFun n C (fun _ => true) = true := by
        rw [funC, graphDef]
        simp only [Finset.notMem_empty, exists_false, decide_false,
          Bool.false_or, and_true, decide_eq_true_eq]
        exact ⟨x, y, hy⟩
      by_contra bad
      change (C.wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at hb
      rw [List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn]; change n + C.size ≤ _; omega)] at hb
      contradiction
    have eqD : circuitFun n D = graphFun G ∅ := by
      funext x
      rw [restored_graph G H u v edge del, attach_compute C u v out, funC]
    refine ⟨D, ⟨attach_mono C u v M, ?_⟩, eqD, ?_⟩
    · intro E he hEq
      rw [dos]
      exact bound E he (hEq.trans eqD)
    intro j hj hAND
    by_cases old : j < C.gates.length
    · have hg : gateAt D j = gateAt C j := by
        simp [D, attach, gateDef, List.getD_eq_getElem?_getD, List.getElem?_append_left old]
      obtain ⟨x, y, hxy, ho⟩ := owners j old ((congrArg Gate.op hg).symm.trans hAND)
      rw [del, SimpleGraph.deleteEdges_adj] at hxy
      exact ⟨x, y, hxy.1, attach_old_owns C u v x y j ho⟩
    · have hcase : j = C.size ∨ j = C.size + 1 := by
        change j < D.size at hj
        rw [dos] at hj
        change ¬ j < C.size at old
        omega
      rcases hcase with rfl | hlast
      · exact ⟨u, v, edge, attach_new_owns C u v⟩
      · have hg : gateAt D j = ⟨.or, [C.output, n + C.size]⟩ := by
          have h : j = C.gates.length + 1 := hlast
          rw [h]
          simp [D, attach, gateDef, List.getD_eq_getElem?_getD]
        rw [hg] at hAND
        contradiction

  intro n G H decG decH tri four z u leaf edge deletion old
  obtain ⟨M, minM, funM, ownM⟩ := old
  by_cases nonempty : ∃ a b, H.Adj a b
  · by_cases cheap : ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size < M.size + 2
    · obtain ⟨C, minC, funC, cost, port⟩ := extract n G H z u leaf edge deletion nonempty M minM funM cheap
      obtain ⟨D, monoD, boundD, funD, owners⟩ :=
        repair n G H tri four z u leaf edge deletion M C minM funM ownM minC funC cost port
      exact ⟨D, ⟨monoD, fun E m eq => boundD.trans (minC.2 E m (eq.trans funD))⟩,
        funD.trans funC, owners⟩
    · apply append_optimal G H z u edge deletion M minM.1 funM nonempty _ ownM
      intro E he hf
      exact Nat.le_of_not_gt (fun h => cheap ⟨E, he, hf, h⟩)
  · let D : Circuit := ⟨[⟨.and, [z.val, u.val]⟩], n⟩
    have calcD (x : Fin n → Bool) : circuitFun n D x = (x z && x u) := by
      let w := List.ofFn x
      have bits (i : Fin n) : w.getD i false = x i := by
        simp [w, List.getD_eq_getElem?_getD, i.isLt]
      have last (b : Bool) : (w ++ [b]).getD n false = b := by
        have h : n = w.length := by simp [w]
        rw [h]
        simp [List.getD_eq_getElem?_getD]
      change (w ++ [((w.getD z false && (w.getD u false && true)))]).getD n false = _
      simp only [last, bits, Bool.and_true]
    have funD : circuitFun n D = graphFun G ∅ := by
      funext x
      rw [restored_graph G H z u edge deletion, calcD]
      have emptyH : graphFun H ∅ x = false := by
        rw [graphDef]
        simp [show ∀ a b, ¬ H.Adj a b from fun a b h => nonempty ⟨a, b, h⟩]
      rw [emptyH, Bool.false_or]
    have owners : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∃ a b, G.Adj a b ∧ Owns n D j a b := by
      intro j hj op
      change j < 1 at hj
      obtain rfl : j = 0 := by omega
      refine ⟨z, u, edge, hj, op, ?_, fun i hi => by omega⟩
      change circuitFun n D (pairInput z u) = true
      simp [calcD, pairDef]
    by_cases zero : ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size = 0
    · obtain ⟨E, m, f, s⟩ := zero
      exact ⟨E, ⟨m, fun _ _ _ => s ▸ Nat.zero_le _⟩, f, by
        intro j hj
        change E.gates.length = 0 at s
        omega⟩
    · refine ⟨D, ⟨?_, ?_⟩, funD, owners⟩
      · intro g hg
        simp only [D, List.mem_singleton] at hg
        subst g
        simp
      · intro E m f
        change 1 ≤ E.size
        by_contra! h
        exact zero ⟨E, m, f.trans funD, by omega⟩
