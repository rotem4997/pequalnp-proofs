import PEqualNP.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- Boundary packing was used in the earlier submission by jturcot42.
-- Exclude a new word whenever an earlier word already makes a subset of its errors.
-- Each word packs fourteen positive edges followed by the maximal independent sets.
-- Remaining slots, when present, test the all-false input.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4833_32
    (trim : ∀ (a : List (BitVec 32)) (m : BitVec 32) (p : Fin 18 → Bool × Fin 29 × Fin 29) (t : Fin 19),
      0 ∈ a → m ∈ ((List.ofFn p).take t.val).foldl (fun (ws : List (BitVec 32)) (g : Bool × Fin 29 × Fin 29) =>
          ws ++ [if g.1 then ws.getD g.2.1.val 0 &&& ws.getD g.2.2.val 0
                 else ws.getD g.2.1.val 0 ||| ws.getD g.2.2.val 0]) a →
      ∃ s : List (BitVec 32), s.length ≤ t.val ∧ m ∈ a ++ s ∧ ∀ j : Fin s.length, let w := a ++ s.take j.val
            (∃ u ∈ w, ∃ v ∈ w, s.get j = u &&& v ∨ s.get j = u ||| v) ∧
            ∀ u ∈ w, ((u ^^^ m) &&& (s.get j ^^^ m)) ≠ (u ^^^ m))
    (obstruction : ∀ a ∈ ([[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]] : List (List (BitVec 32))),
      ∀ s : List (BitVec 32), s.length ≤ 18 →
        (∀ j : Fin s.length, let w := a ++ s.take j.val
            (∃ u ∈ w, ∃ v ∈ w, s.get j = u &&& v ∨ s.get j = u ||| v) ∧
            ∀ u ∈ w, ((u ^^^ (16383 : BitVec 32)) &&& (s.get j ^^^ (16383 : BitVec 32))) ≠ (u ^^^ (16383 : BitVec 32))) → (16383 : BitVec 32) ∉ a ++ s) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (19 : ℕ) ≤ x3.size := by
  have compile : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a : List (BitVec 32)),
      PEqualNP.TopForm.IsAO2 11 C → a.length = 11 → C.size ≤ 18 →
      ∃ p : Fin 18 → Bool × Fin 29 × Fin 29, ∀ k : Fin 32,
        C.eval (a.map (fun w => w.getLsbD k.val)) =
        ((((List.ofFn p).take C.size).foldl (fun (ws : List (BitVec 32)) (g : Bool × Fin 29 × Fin 29) =>
          ws ++ [if g.1 then ws.getD g.2.1.val 0 &&& ws.getD g.2.2.val 0
                 else ws.getD g.2.1.val 0 ||| ws.getD g.2.2.val 0]) a).getD C.output 0).getLsbD k.val := by
    classical
    let enc (g : Gate) : Bool × Fin 29 × Fin 29 := by
      classical
      exact (decide (g.op = GateOp.and), ⟨g.inputs.getD 0 0 % 29, Nat.mod_lt _ (by decide)⟩,
        ⟨g.inputs.getD 1 0 % 29, Nat.mod_lt _ (by decide)⟩)

    let bstep (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    let vstep (w : List (BitVec 32)) (g : Bool × Fin 29 × Fin 29) : List (BitVec 32) :=
      w ++ [if g.1 then w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0
            else w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0]

    have step (g : Gate) (w : List (BitVec 32)) (k : Nat)
        (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
        (hinputs : ∃ x y, g.inputs = [x,y] ∧ x < 29 ∧ y < 29) :
        (vstep w (enc g)).map (fun v => v.getLsbD k) =
          bstep (w.map (fun v => v.getLsbD k)) g := by
      classical
      obtain ⟨x,y,hxy,hx,hy⟩ := hinputs
      have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
      have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
      rcases hop with hop | hop <;>
        simp [vstep, bstep, enc, hxy, hop, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
          andEval, orEval, BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
        cases hxw : w[x]? <;> cases hyw : w[y]? <;> simp [hxw, hyw]

    have fold_sim (gs : List Gate) (w : List (BitVec 32)) (k : Nat)
        (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ x y, g.inputs = [x,y] ∧ x < 29 ∧ y < 29) :
        ((gs.map enc).foldl vstep w).map (fun v => v.getLsbD k) =
          gs.foldl bstep (w.map (fun v => v.getLsbD k)) := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [ih _ (fun g hg => h g (by simp [hg])), step g w k (h g (by simp)).1 (h g (by simp)).2]

    intro C a hC ha hs
    have sizeEq (D : Circuit) : D.size = D.gates.length := rfl
    let p : Fin 18 → Bool × Fin 29 × Fin 29 := fun i => enc (C.gates.getD i.val ⟨GateOp.or, []⟩)
    have hp : (List.ofFn p).take C.size = C.gates.map enc := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_ofFn, List.length_map, sizeEq]
        simp only [sizeEq] at hs
        omega
      · intro i hi hi2
        have hi3 : i < C.gates.length := by simpa using hi2
        rw [List.getElem_take, List.getElem_ofFn, List.getElem_map]
        change enc (C.gates.getD i ⟨GateOp.or, []⟩) = enc C.gates[i]
        rw [List.getD_eq_getElem _ _ hi3]
    have hall : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ x y, g.inputs = [x,y] ∧ x < 29 ∧ y < 29 := by
      intro g hg
      have hop := hC.1 g hg
      obtain ⟨x,y,hxy⟩ := List.length_eq_two.mp (hC.2.2 g hg)
      obtain ⟨j,hj,hjg⟩ := List.mem_iff_getElem.mp hg
      have hgate : gateAt C j = g := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj, hjg]
      have hx : x < 29 := by
        have h := hC.2.1 j hj x (by simpa [hgate, hxy])
        simp only [sizeEq] at hs
        omega
      have hy : y < 29 := by
        have h := hC.2.1 j hj y (by simpa [hgate, hxy])
        simp only [sizeEq] at hs
        omega
      exact ⟨hop, x,y,hxy,hx,hy⟩
    refine ⟨p, ?_⟩
    intro k
    rw [hp]
    have h := fold_sim C.gates a k.val hall
    change (C.gates.foldl bstep (a.map (fun w => w.getLsbD k.val))).getD C.output false =
      ((C.gates.map enc).foldl vstep a |>.getD C.output 0).getLsbD k.val
    rw [← h]
    simpa using List.getD_map ((C.gates.map enc).foldl vstep a) (0 : BitVec 32)
      (n := C.output) (fun w => w.getLsbD k.val)
  intro G v C hv hao agree
  by_contra! tooSmall
  let A : Fin 4 → List (BitVec 32) := ![[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]]
  let x (i : Fin 4) (k : Fin 32) (j : Fin 11) : Bool :=
    ((A i).getD j.val 0).getLsbD k.val
  let i : Fin 4 := ⟨v.val,hv⟩
  have lengths : ∀ j, (A j).length = 11 := by decide +kernel
  have rows : ∀ j k, (A j).map (fun w => w.getLsbD k.val) = List.ofFn (x j k) := by decide +kernel
  have off : ∀ (j : Fin 4) (k : Fin 32), x j k ⟨j.val,Nat.lt_trans j.isLt (by decide : 4 < 11)⟩ = false := by decide +kernel
  have targets : ∀ (j : Fin 4) (k : Fin 32),
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (x j k) =
        (16383 : BitVec 32).getLsbD k.val := by decide +kernel
  obtain ⟨p,hp⟩ := compile C (A i) hao (lengths i) (by omega)
  let ws : List (BitVec 32) := ((List.ofFn p).take C.size).foldl (fun (ws : List (BitVec 32)) (g : Bool × Fin 29 × Fin 29) =>
          ws ++ [if g.1 then ws.getD g.2.1.val 0 &&& ws.getD g.2.2.val 0
                 else ws.getD g.2.1.val 0 ||| ws.getD g.2.2.val 0]) (A i)
  have value : ws.getD C.output 0 = (16383 : BitVec 32) := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    let k : Fin 32 := ⟨r,hr⟩
    have witness := hp k
    rw [rows i k] at witness
    have computes := agree (x i k) (off i k)
    exact witness.symm.trans (computes.trans (targets i k))
  have valid : C.output < ws.length := by
    by_contra! hout
    have hz : ws.getD C.output 0 = 0 := List.getD_eq_default _ _ hout
    exact (by decide : (0 : BitVec 32) ≠ 16383) (hz.symm.trans value)
  have member : ws.getD C.output 0 ∈ ws := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem valid]
    exact List.getElem_mem valid
  have rowChoice : ∀ q : Fin 4, A q ∈ ([[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]] : List (List (BitVec 32))) := by
    intro q
    fin_cases q <;> simp [A]
  have zero : ∀ j : Fin 4, (0 : BitVec 32) ∈ A j := by decide +kernel
  obtain ⟨s,sz,hit,good⟩ := trim (A i) 16383 p ⟨C.size,by omega⟩ (zero i) (value ▸ member)
  exact obstruction (A i) (rowChoice i) s (by omega) good hit
