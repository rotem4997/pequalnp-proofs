import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2670_401
    (hTopForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty →
      IsMinimalMonoCircuit n C →
      circuitFun n C = graphFun G ∅ →
      let cost : Circuit → ℕ := fun D =>
        {k : ℕ | k < D.gates.length ∧ (gateAt D k).op = GateOp.and ∧
          ∀ u v : Fin n, G.Adj u v → ¬ Owns n D k u v}.ncard
      ∃ C' : Circuit,
        IsAO2 n C' ∧
        circuitFun n C' = graphFun G ∅ ∧
        C'.size ≤ C.size ∧
        TopForm G C' ∧
        cost C' ≤ cost C)
    (hOneJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      NoFourCycle G →
      G.edgeFinset.Nonempty →
      let cost : Circuit → ℕ := fun D =>
        {k : ℕ | k < D.gates.length ∧ (gateAt D k).op = GateOp.and ∧
          ∀ u v : Fin n, G.Adj u v → ¬ Owns n D k u v}.ncard
      ∀ (C : Circuit) (g : ℕ),
        IsMinimalMonoCircuit n C →
        IsAO2 n C →
        circuitFun n C = graphFun G ∅ →
        TopForm G C →
        0 < cost C →
        junk G C = {g} →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ cost D < cost C)
    (hFlatJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      NoFourCycle G →
      G.edgeFinset.Nonempty →
      let cost : Circuit → ℕ := fun D =>
        {k : ℕ | k < D.gates.length ∧ (gateAt D k).op = GateOp.and ∧
          ∀ u v : Fin n, G.Adj u v → ¬ Owns n D k u v}.ncard
      ∀ C : Circuit,
        IsMinimalMonoCircuit n C →
        IsAO2 n C →
        circuitFun n C = graphFun G ∅ →
        TopForm G C →
        0 < cost C →
        2 ≤ (junk G C).card →
        (∀ a ∈ junk G C, ∀ b ∈ junk G C, ¬ InCone n C a b) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ cost D < cost C)
    (hNestedJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      NoFourCycle G →
      G.edgeFinset.Nonempty →
      let cost : Circuit → ℕ := fun D =>
        {k : ℕ | k < D.gates.length ∧ (gateAt D k).op = GateOp.and ∧
          ∀ u v : Fin n, G.Adj u v → ¬ Owns n D k u v}.ncard
      ∀ C : Circuit,
        IsMinimalMonoCircuit n C →
        IsAO2 n C →
        circuitFun n C = graphFun G ∅ →
        TopForm G C →
        0 < cost C →
        2 ≤ (junk G C).card →
        (∃ a ∈ junk G C, ∃ b ∈ junk G C, InCone n C a b) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ cost D < cost C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => {x7 : ℕ | x7 < x6.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → ¬PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9}.ncard;       ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → ¬PEqualNP.EdgeOwnership.Owns x1 x7 x10 x13 x14) → (∀ x14 < x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x14 x17 x18) → ∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 (PEqualNP.CircuitMoves.eraseGate x1 x7 x10 (x1 + x7.gates.length)) (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.false → ∃ (x20 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x20 ∧ PEqualNP.MetaComplexity.circuitFun x1 x20 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x20.size ≤ x7.size ∧ x6 x20 < x6 x7 := by
  classical
  intro n G _ hTri hFour cost C hMin hFun j hj hjAnd hjNoOwn _ u v huv _ _
  have hNonempty : G.edgeFinset.Nonempty :=
    ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr huv)⟩
  let bad (D : Circuit) : Set ℕ :=
    {k : ℕ | k < D.gates.length ∧ (gateAt D k).op = GateOp.and ∧
      ∀ p q : Fin n, G.Adj p q → ¬ Owns n D k p q}
  have hBadFin : ∀ D : Circuit, (bad D).Finite := fun D =>
    (Set.finite_lt_nat D.gates.length).subset (fun _ hk => hk.1)
  have hCostPosC : 0 < cost C :=
    (Set.ncard_pos (hBadFin C)).mpr ⟨j, hj, hjAnd, hjNoOwn⟩
  obtain ⟨C', hAO, hFun', hSize', hTF, hCostLe⟩ := hTopForm n G C hNonempty hMin hFun
  have hMono' : Monotone2 C' := by
    intro g hg
    refine ⟨?_, by have := hAO.2.2 g hg; omega⟩
    rcases hAO.1 g hg with h | h
    · exact Or.inl h
    · exact Or.inr h
  by_cases hDrop : cost C' < cost C
  · exact ⟨C', hMono', hFun', hSize', hDrop⟩
  · have hCostPos' : 0 < cost C' := by omega
    have hMin' : IsMinimalMonoCircuit n C' :=
      ⟨hMono', fun D hDm hDf => hSize'.trans (hMin.2 D hDm (hDf.trans (hFun'.trans hFun.symm)))⟩
    have hJunkNonempty : (junk G C').Nonempty := by
      by_contra hJunkEmpty
      rw [Finset.not_nonempty_iff_eq_empty] at hJunkEmpty
      obtain ⟨k, hkLt, hkAnd, hkNoOwn⟩ := (Set.ncard_pos (hBadFin C')).mp hCostPos'
      have hAllBelow : ∀ i < C'.gates.length, (gateAt C' i).op = GateOp.and → BelowF G C' i := by
        intro i hi hiAnd x hval
        by_contra hF
        have hFfalse : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hF
        have hDirty : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C' i :=
          ⟨hiAnd, hi, x, hval, hFfalse⟩
        have hMem : i ∈ junk G C' := by
          change i ∈ (Finset.range C'.gates.length).filter
            (fun r => PEqualNP.CleanedNonEdge.IsDirtyAnd n G C' r)
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, hDirty⟩
        rw [hJunkEmpty] at hMem
        exact Finset.notMem_empty i hMem
      have hNoCone : ∀ i < k, (gateAt C' i).op = GateOp.and → ¬ InCone n C' i k := by
        intro i hi hiAnd
        exact hTF i (hi.trans hkLt) k hkLt hiAnd (hAllBelow i (hi.trans hkLt) hiAnd) hkAnd
      let stepW : List Bool → Gate → List Bool :=
        fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have hFoldLen : ∀ (gs : List Gate) (w : List Bool),
          (gs.foldl stepW w).length = w.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro w; simp
        | cons g gs ih =>
          intro w
          rw [List.foldl_cons, ih]
          simp [stepW]
          omega
      have hFoldLt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (gs.foldl stepW w).getD i false = w.getD i false := by
        intro gs
        induction gs with
        | nil => intro w i _; rfl
        | cons g gs ih =>
          intro w i hi
          rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have hGetDGe : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
        intro w i hi
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
      have hFoldGate : ∀ (gs : List Gate) (w : List Bool) (r : ℕ) (hr : r < gs.length),
          (gs.foldl stepW w).getD (w.length + r) false =
            gs[r].op.eval (gs[r].inputs.map fun i =>
              if i < w.length + r then (gs.foldl stepW w).getD i false else false) := by
        intro gs
        induction gs with
        | nil => intro w r hr; simp at hr
        | cons g gs ih =>
          intro w r hr
          rw [List.foldl_cons]
          cases r with
          | zero =>
            rw [Nat.add_zero, hFoldLt gs (stepW w g) w.length (by simp [stepW])]
            simp only [List.getElem_cons_zero]
            have hLast : (stepW w g).getD w.length false =
                g.op.eval (g.inputs.map fun i => w.getD i false) := by
              simp [stepW, List.getD_eq_getElem?_getD]
            rw [hLast]
            congr 1
            refine List.map_congr_left fun i _ => ?_
            by_cases hi : i < w.length
            · simp only [hi, ↓reduceIte]
              rw [hFoldLt gs (stepW w g) i (by simp [stepW]; omega)]
              simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
            · simp only [hi, ↓reduceIte]
              exact hGetDGe w i (by omega)
          | succ r =>
            have hr' : r < gs.length := by simpa using hr
            have hKey := ih (stepW w g) r hr'
            have hLen : (stepW w g).length = w.length + 1 := by simp [stepW]
            rw [hLen] at hKey
            have hEq : w.length + (r + 1) = w.length + 1 + r := by omega
            simp only [List.getElem_cons_succ]
            rw [hEq]
            exact hKey
      have hGateAt : ∀ (D : Circuit) (r : ℕ) (hr : r < D.gates.length),
          gateAt D r = D.gates[r] := by
        intro D r hr
        change D.gates.getD r ⟨GateOp.or, []⟩ = D.gates[r]
        simp [List.getD_eq_getElem?_getD, hr]
      have hWiresInput : ∀ (D : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n),
          (D.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
        intro D x i hi
        change (D.gates.foldl stepW (List.ofFn x)).getD i false = x ⟨i, hi⟩
        rw [hFoldLt D.gates (List.ofFn x) i (by simpa using hi)]
        simp [List.getD_eq_getElem?_getD, hi]
      have hWiresGate : ∀ (D : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < D.gates.length),
          (D.wires (List.ofFn x)).getD (n + r) false =
            (gateAt D r).op.eval ((gateAt D r).inputs.map fun i =>
              if i < n + r then (D.wires (List.ofFn x)).getD i false else false) := by
        intro D x r hr
        rw [hGateAt D r hr]
        have h := hFoldGate D.gates (List.ofFn x) r hr
        rw [List.length_ofFn] at h
        exact h
      have hWiresGe : ∀ (D : Circuit) (x : Fin n → Bool) (w : ℕ),
          n + D.gates.length ≤ w → (D.wires (List.ofFn x)).getD w false = false := by
        intro D x w hw
        apply hGetDGe
        change (D.gates.foldl stepW (List.ofFn x)).length ≤ w
        rw [hFoldLen, List.length_ofFn]
        exact hw
      have hOpMono : ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) →
          ∀ (l : List ℕ) (f g : ℕ → Bool),
            (∀ i ∈ l, f i = true → g i = true) →
            op.eval (l.map f) = true → op.eval (l.map g) = true := by
        intro op hop l f g hfg
        rcases hop with rfl | rfl
        · change (l.map f).all id = true → (l.map g).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h1 i hi
          exact hfg i hi (h1 i hi)
        · change (l.map f).any id = true → (l.map g).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i, hi, h1⟩
          exact ⟨i, hi, hfg i hi h1⟩
      have hWiresMono : ∀ (D : Circuit), Monotone2 D → ∀ (x y : Fin n → Bool),
          (∀ i : Fin n, x i = true → y i = true) →
          ∀ w : ℕ, (D.wires (List.ofFn x)).getD w false = true →
            (D.wires (List.ofFn y)).getD w false = true := by
        intro D hDm x y hxy w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases hwn : w < n
          · rw [hWiresInput D x w hwn, hWiresInput D y w hwn]
            exact hxy ⟨w, hwn⟩
          · by_cases hwlt : w < n + D.gates.length
            · obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
              have hr : r < D.gates.length := by omega
              rw [hWiresGate D x r hr, hWiresGate D y r hr]
              have hop : (gateAt D r).op = GateOp.and ∨ (gateAt D r).op = GateOp.or := by
                have hm := (hDm (D.gates[r]) (List.getElem_mem hr)).1
                rw [hGateAt D r hr]
                simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
              refine hOpMono _ hop _ _ _ (fun i _ hi => ?_)
              by_cases hilt : i < n + r
              · simp only [hilt, ↓reduceIte] at hi ⊢
                exact ih i hilt hi
              · simp only [hilt, ↓reduceIte] at hi
                cases hi
            · rw [hWiresGe D x w (by omega)]
              intro h; cases h
      have hExistsEdge : ∃ p q : Fin n, G.Adj p q ∧ gateVal n C' k (pairInput p q) = true := by
        by_contra hNoEdge
        have hAllFalse : ∀ p q : Fin n, G.Adj p q → gateVal n C' k (pairInput p q) = false := by
          intro p q hpq
          exact Bool.eq_false_iff.mpr (fun h => hNoEdge ⟨p, q, hpq, h⟩)
        let rd := eraseRedirect n k (n + C'.gates.length)
        let E := eraseGate n C' k (n + C'.gates.length)
        have hEdef : E =
            { gates := C'.gates.take k ++
                (C'.gates.drop (k + 1)).map (fun g => ⟨g.op, g.inputs.map rd⟩)
              output := rd C'.output } := by
          change (if k < C'.gates.length then
            { gates := C'.gates.take k ++
                (C'.gates.drop (k + 1)).map (fun g => ⟨g.op, g.inputs.map rd⟩)
              output := rd C'.output } else C') = _
          simp only [hkLt, ↓reduceIte]
        have hEout : E.output = rd C'.output := by
          rw [hEdef]
        have hElen : E.gates.length = C'.gates.length - 1 := by
          rw [hEdef]
          simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
          omega
        have hEmono : Monotone2 E := by
          intro g hg
          rw [hEdef] at hg
          rcases List.mem_append.mp hg with hg1 | hg2
          · exact hMono' g (List.mem_of_mem_take hg1)
          · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg2
            have h0 := hMono' g0 (List.mem_of_mem_drop hg0)
            exact ⟨h0.1, by simpa using h0.2⟩
        have hEgateLt : ∀ r < k, gateAt E r = gateAt C' r := by
          intro r hr
          have hrE : r < E.gates.length := by omega
          have hrC : r < C'.gates.length := by omega
          rw [hGateAt E r hrE, hGateAt C' r hrC]
          have hTakeLen : (C'.gates.take k).length = k := by simp; omega
          simp only [hEdef, List.getElem_append_left (by omega : r < (C'.gates.take k).length),
            List.getElem_take]
        have hEgateGt : ∀ r, k < r → r < C'.gates.length →
            gateAt E (r - 1) = ⟨(gateAt C' r).op, (gateAt C' r).inputs.map rd⟩ := by
          intro r hkr hrC
          have hrE : r - 1 < E.gates.length := by omega
          rw [hGateAt E (r - 1) hrE, hGateAt C' r hrC]
          have hTakeLen : (C'.gates.take k).length = k := by simp; omega
          have hNotLt : ¬ r - 1 < (C'.gates.take k).length := by omega
          simp only [hEdef, List.getElem_append_right (by omega : (C'.gates.take k).length ≤ r - 1),
            hTakeLen, List.getElem_map, List.getElem_drop]
          have hIdx : k + 1 + (r - 1 - k) = r := by omega
          simp only [hIdx]
        have hRdLt : ∀ a, a < n + k → rd a = a := by
          intro a ha
          change (if a = n + k then n + C'.gates.length else if n + k < a then a - 1 else a) = a
          have h1 : ¬ a = n + k := by omega
          have h2 : ¬ n + k < a := by omega
          simp only [h1, h2, ↓reduceIte]
        have hRdEq : rd (n + k) = n + C'.gates.length := by
          change (if n + k = n + k then n + C'.gates.length
            else if n + k < n + k then n + k - 1 else n + k) = n + C'.gates.length
          simp only [↓reduceIte]
        have hRdGt : ∀ a, n + k < a → rd a = a - 1 := by
          intro a ha
          change (if a = n + k then n + C'.gates.length
            else if n + k < a then a - 1 else a) = a - 1
          have h1 : ¬ a = n + k := by omega
          simp only [h1, ha, ↓reduceIte]
        have hEle : ∀ (x : Fin n → Bool) (w : ℕ), w < n + C'.gates.length →
            (E.wires (List.ofFn x)).getD (rd w) false = true →
            (C'.wires (List.ofFn x)).getD w false = true := by
          intro x w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hwn : w < n
            · rw [hRdLt w (by omega), hWiresInput E x w hwn, hWiresInput C' x w hwn]
              exact id
            · obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
              have hrC : r < C'.gates.length := by omega
              by_cases hrk : r < k
              · rw [hRdLt (n + r) (by omega), hWiresGate E x r (by omega),
                  hWiresGate C' x r hrC, hEgateLt r hrk]
                have hop : (gateAt C' r).op = GateOp.and ∨ (gateAt C' r).op = GateOp.or := by
                  rw [hGateAt C' r hrC]
                  exact hAO.1 _ (List.getElem_mem hrC)
                refine hOpMono _ hop _ _ _ (fun i hi hval => ?_)
                have hiLt : i < n + r := hAO.2.1 r hrC i hi
                simp only [hiLt, ↓reduceIte] at hval ⊢
                have hri : rd i = i := hRdLt i (by omega)
                rw [← hri] at hval
                exact ih i hiLt (by omega) hval
              · by_cases hreq : r = k
                · subst hreq
                  rw [hRdEq, hWiresGe E x (n + C'.gates.length) (by omega)]
                  intro h; cases h
                · have hkr : k < r := by omega
                  have hRdR : rd (n + r) = n + (r - 1) := by
                    rw [hRdGt (n + r) (by omega)]
                    omega
                  rw [hRdR, hWiresGate E x (r - 1) (by omega), hWiresGate C' x r hrC,
                    hEgateGt r hkr hrC]
                  simp only [List.map_map]
                  have hop : (gateAt C' r).op = GateOp.and ∨ (gateAt C' r).op = GateOp.or := by
                    rw [hGateAt C' r hrC]
                    exact hAO.1 _ (List.getElem_mem hrC)
                  refine hOpMono _ hop _ _ _ (fun i hi hval => ?_)
                  have hiLt : i < n + r := hAO.2.1 r hrC i hi
                  simp only [hiLt, ↓reduceIte]
                  change (if rd i < n + (r - 1) then (E.wires (List.ofFn x)).getD (rd i) false
                    else false) = true at hval
                  by_cases hRdi : rd i < n + (r - 1)
                  · simp only [hRdi, ↓reduceIte] at hval
                    exact ih i hiLt (by omega) hval
                  · simp only [hRdi, ↓reduceIte] at hval
                    cases hval
        have hEevalLe : ∀ x : Fin n → Bool,
            E.eval (List.ofFn x) = true → C'.eval (List.ofFn x) = true := by
          intro x hEx
          change (E.wires (List.ofFn x)).getD E.output false = true at hEx
          rw [hEout] at hEx
          by_cases hout : C'.output < n + C'.gates.length
          · exact hEle x C'.output hout hEx
          · have hGe : n + E.gates.length ≤ rd C'.output := by
              rw [hRdGt C'.output (by omega), hElen]
              omega
            rw [hWiresGe E x (rd C'.output) hGe] at hEx
            cases hEx
        have hEeqFalse : ∀ (x : Fin n → Bool), gateVal n C' k x = false →
            ∀ w < n + C'.gates.length,
              (E.wires (List.ofFn x)).getD (rd w) false =
                (C'.wires (List.ofFn x)).getD w false := by
          intro x hkx w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hwn : w < n
            · rw [hRdLt w (by omega), hWiresInput E x w hwn, hWiresInput C' x w hwn]
            · obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
              have hrC : r < C'.gates.length := by omega
              by_cases hrk : r < k
              · rw [hRdLt (n + r) (by omega), hWiresGate E x r (by omega),
                  hWiresGate C' x r hrC, hEgateLt r hrk]
                congr 1
                refine List.map_congr_left fun i hi => ?_
                have hiLt : i < n + r := hAO.2.1 r hrC i hi
                simp only [hiLt, ↓reduceIte]
                have hri : rd i = i := hRdLt i (by omega)
                have hIh := ih i hiLt (by omega)
                rw [hri] at hIh
                exact hIh
              · by_cases hreq : r = k
                · subst hreq
                  rw [hRdEq, hWiresGe E x (n + C'.gates.length) (by omega)]
                  exact hkx.symm
                · have hkr : k < r := by omega
                  have hRdR : rd (n + r) = n + (r - 1) := by
                    rw [hRdGt (n + r) (by omega)]
                    omega
                  rw [hRdR, hWiresGate E x (r - 1) (by omega), hWiresGate C' x r hrC,
                    hEgateGt r hkr hrC]
                  simp only [List.map_map]
                  congr 1
                  refine List.map_congr_left fun i hi => ?_
                  have hiLt : i < n + r := hAO.2.1 r hrC i hi
                  simp only [hiLt, ↓reduceIte]
                  change (if rd i < n + (r - 1) then (E.wires (List.ofFn x)).getD (rd i) false
                    else false) = (C'.wires (List.ofFn x)).getD i false
                  by_cases hik : i = n + k
                  · subst hik
                    have hNotLt : ¬ rd (n + k) < n + (r - 1) := by
                      rw [hRdEq]; omega
                    simp only [hNotLt, ↓reduceIte]
                    exact hkx.symm
                  · have hRdi : rd i < n + (r - 1) := by
                      by_cases hilt : i < n + k
                      · rw [hRdLt i hilt]; omega
                      · rw [hRdGt i (by omega)]; omega
                    simp only [hRdi, ↓reduceIte]
                    exact ih i hiLt (by omega)
        have hEfun : circuitFun n E = circuitFun n C' := by
          funext x
          rw [Bool.eq_iff_iff]
          constructor
          · exact hEevalLe x
          · intro hCx
            have hGx : graphFun G ∅ x = true := by
              rw [← hFun']
              exact hCx
            have hEdgeX : ∃ p q : Fin n, G.Adj p q ∧ x p = true ∧ x q = true := by
              change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
                decide (∃ p q : Fin n, G.Adj p q ∧ x p = true ∧ x q = true)) = true at hGx
              simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                Bool.false_or, decide_eq_true_eq] at hGx
              exact hGx
            obtain ⟨p, q, hpq, hxp, hxq⟩ := hEdgeX
            have hCpq : C'.eval (List.ofFn (pairInput p q)) = true := by
              change circuitFun n C' (pairInput p q) = true
              rw [hFun']
              change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput p q a = true) ||
                decide (∃ a b : Fin n, G.Adj a b ∧ pairInput p q a = true ∧
                  pairInput p q b = true)) = true
              simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                Bool.false_or, decide_eq_true_eq]
              exact ⟨p, q, hpq, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
            have hout : C'.output < n + C'.gates.length := by
              by_contra hge
              have h0 : C'.eval (List.ofFn (pairInput p q)) = false :=
                hWiresGe C' (pairInput p q) C'.output (by omega)
              rw [h0] at hCpq
              cases hCpq
            have hEpq : E.eval (List.ofFn (pairInput p q)) = true := by
              change (E.wires (List.ofFn (pairInput p q))).getD E.output false = true
              rw [hEout, hEeqFalse (pairInput p q) (hAllFalse p q hpq) C'.output hout]
              exact hCpq
            refine hWiresMono E hEmono (pairInput p q) x ?_ E.output hEpq
            intro w hw
            change decide (w = p ∨ w = q) = true at hw
            rw [decide_eq_true_eq] at hw
            rcases hw with rfl | rfl
            · exact hxp
            · exact hxq
        have hSizeLe := hMin'.2 E hEmono hEfun
        change C'.gates.length ≤ E.gates.length at hSizeLe
        omega
      obtain ⟨p, q, hpq, hval⟩ := hExistsEdge
      have hOwns : Owns n C' k p q := by
        refine ⟨hkLt, hkAnd, hval, ?_⟩
        intro i hi hic hiAnd
        exact False.elim (hNoCone i hi hiAnd hic)
      exact hkNoOwn p q hpq hOwns
    have hCardPos : 1 ≤ (junk G C').card := Finset.one_le_card.mpr hJunkNonempty
    by_cases hOne : (junk G C').card = 1
    · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hOne
      obtain ⟨D, hDm, hDf, hDs, hDc⟩ :=
        hOneJunk n G hTri hFour hNonempty C' g hMin' hAO hFun' hTF hCostPos' hg
      exact ⟨D, hDm, hDf, hDs.trans hSize', lt_of_lt_of_le hDc hCostLe⟩
    · have hTwo : 2 ≤ (junk G C').card := by omega
      by_cases hNest : ∃ a ∈ junk G C', ∃ b ∈ junk G C', InCone n C' a b
      · obtain ⟨D, hDm, hDf, hDs, hDc⟩ :=
          hNestedJunk n G hTri hFour hNonempty C' hMin' hAO hFun' hTF hCostPos' hTwo hNest
        exact ⟨D, hDm, hDf, hDs.trans hSize', lt_of_lt_of_le hDc hCostLe⟩
      · have hFlat : ∀ a ∈ junk G C', ∀ b ∈ junk G C', ¬ InCone n C' a b :=
          fun a ha b hb hc => hNest ⟨a, ha, b, hb, hc⟩
        obtain ⟨D, hDm, hDf, hDs, hDc⟩ :=
          hFlatJunk n G hTri hFour hNonempty C' hMin' hAO hFun' hTF hCostPos' hTwo hFlat
        exact ⟨D, hDm, hDf, hDs.trans hSize', lt_of_lt_of_le hDc hCostLe⟩
