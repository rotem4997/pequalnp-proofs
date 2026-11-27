import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.NotPremium

-- Minimize the number of nonedge pair incidences across AND gates.
-- A dominating gate replacement that removes even one incidence must miss a critical edge.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5284_1
    (bipartite : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let F := graphFun G (∅ : Finset (Fin n))
      let V := fun (D : Circuit) (j : ℕ) => gateVal n D j
      let P := fun (D : Circuit) (j : ℕ) (u v : Fin n) => V D j (pairInput u v)
      let A := fun (D : Circuit) (j : ℕ) => (gateAt D j).op = GateOp.and
      let R := fun (j : ℕ) (g : Gate) => Circuit.mk (C.gates.set j g) C.output
      NoFourCycle G → G.IsBipartite → Monotone2 C → circuitFun n C = F →
      (∀ j < C.size, ∀ u, A C j → P C j u u = false) →
      (∀ j g u v, j < C.size → A C j → ¬ G.Adj u v → P C j u v = true →
        Monotone2 (R j g) →
        (∀ x, V (R j g) j x = true → V C j x = true) → P (R j g) j u v = false →
        circuitFun n (R j g) ≠ F) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun n D = F ∧
        ∀ j u v, A D j → P D j u v = true → G.Adj u v)
    (odd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let F := graphFun G (∅ : Finset (Fin n))
      let V := fun (D : Circuit) (j : ℕ) => gateVal n D j
      let P := fun (D : Circuit) (j : ℕ) (u v : Fin n) => V D j (pairInput u v)
      let A := fun (D : Circuit) (j : ℕ) => (gateAt D j).op = GateOp.and
      let R := fun (j : ℕ) (g : Gate) => Circuit.mk (C.gates.set j g) C.output
      NoFourCycle G → G.CliqueFree 3 → ¬ G.IsBipartite → Monotone2 C → circuitFun n C = F →
      (∀ j < C.size, ∀ u, A C j → P C j u u = false) →
      (∀ j g u v, j < C.size → A C j → ¬ G.Adj u v → P C j u v = true →
        Monotone2 (R j g) →
        (∀ x, V (R j g) j x = true → V C j x = true) → P (R j g) j u v = false →
        circuitFun n (R j g) ≠ F) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun n D = F ∧
        ∀ j u v, A D j → P D j u v = true → G.Adj u v) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22
 := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wire_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step w g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      apply List.getD_append
      exact hi

  have eval_preserves_true (g : Gate) (basis : g.op = .and ∨ g.op = .or)
      (a b : ℕ → Bool) (pointwise : ∀ i, a i = true → b i = true)
      (yes : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
    rcases basis with hop | hop
    · rw [hop] at yes ⊢
      change (g.inputs.map a).all id = true at yes
      change (g.inputs.map b).all id = true
      apply List.all_eq_true.mpr
      intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact pointwise i (List.all_eq_true.mp yes _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
    · rw [hop] at yes ⊢
      change (g.inputs.map a).any id = true at yes
      change (g.inputs.map b).any id = true
      obtain ⟨t, ht, htTrue⟩ := List.any_eq_true.mp yes
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact List.any_eq_true.mpr ⟨b i, List.mem_map.mpr ⟨i,hi,rfl⟩, pointwise i htTrue⟩

  have run_preserves_true (gs : List Gate)
      (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (a b : List Bool) (len : a.length = b.length)
      (h : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      have basis_g := basis g (by simp)
      have basis_tail : ∀ z ∈ gs, z.op = .and ∨ z.op = .or := fun z hz => basis z (by simp [hz])
      change ∀ i, (gs.foldl step (step a g)).getD i false = true →
        (gs.foldl step (step b g)).getD i false = true
      apply ih basis_tail
      · simp [step, len]
      · intro i hi
        by_cases hs : i < a.length
        · have ht : i < b.length := by omega
          change (a ++ [_]).getD i false = true at hi
          rw [List.getD_append _ _ _ _ hs] at hi
          change (b ++ [_]).getD i false = true
          rw [List.getD_append _ _ _ _ ht]
          exact h i hi
        · change (a ++ [_]).getD i false = true at hi
          change (b ++ [_]).getD i false = true
          rw [List.getD_append_right _ _ _ _ (by omega : a.length ≤ i)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), ←len]
          by_cases eq : i = a.length
          · simp only [eq, Nat.sub_self, List.getD_cons_zero] at hi ⊢
            exact eval_preserves_true g basis_g (fun p => a.getD p false) (fun p => b.getD p false) h hi
          · have positive : 0 < i - a.length := by omega
            rw [List.getD_eq_default _ _ (by simp; omega)] at hi
            contradiction

  have wire_preserves_true {n : ℕ} (C : Circuit) (basis : AndOrOnly C)
      (a b : Fin n → Bool) (pointwise : ∀ j, a j = true → b j = true) (w : ℕ) :
      wireVal n C w a = true → wireVal n C w b = true := by
    apply run_preserves_true C.gates basis (List.ofFn a) (List.ofFn b) (by simp) _ w
    intro i hi
    by_cases h : i < n
    · have aTrue : a ⟨i,h⟩ = true := by simpa [List.getD_eq_getElem?_getD, h] using hi
      simpa [List.getD_eq_getElem?_getD, h] using pointwise ⟨i,h⟩ aTrue
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction

  have gate_from_earlier {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (x : Fin n → Bool) :
      gateVal n C j x = (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i =>
          ((C.gates.take j).foldl step (List.ofFn x)).getD i false) := by
    let pre := C.gates.take j
    let post := C.gates.drop (j+1)
    let g := C.gates[j]
    have hGate : gateAt C j = g := List.getD_eq_getElem _ _ hj
    have split : C.gates = pre ++ g :: post := by
      dsimp only [pre, g, post]
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    let before := pre.foldl step (List.ofFn x)
    have sizeBefore : before.length = n+j := by
      simp [before, wire_len, pre, List.length_take, Nat.min_eq_left hj.le]
    rw [hGate]
    change (C.gates.foldl step (List.ofFn x)).getD (n+j) false =
      g.op.eval (g.inputs.map fun i => before.getD i false)
    conv_lhs => rw [split, List.foldl_append]
    change (post.foldl step (step before g)).getD (n+j) false = _
    rw [old_read _ _ _ (by simp [step, sizeBefore])]
    change (before ++ [_]).getD (n+j) false = _
    rw [List.getD_append_right _ _ _ _ (by omega : before.length ≤ n+j), sizeBefore,
      Nat.sub_self, List.getD_cons_zero]

  let setGate (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
    ⟨C.gates.set j g, C.output⟩

  let low {n : ℕ} (C : Circuit) (j : ℕ) : Circuit :=
    ⟨replaceByConst C.gates j false, C.output⟩

  let before {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :=
    (C.gates.take j).foldl step (List.ofFn x)

  let gateResult {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate) (x : Fin n → Bool) : Bool :=
    g.op.eval (g.inputs.map (fun i => (before C j x).getD i false))

  have basisOf (C : Circuit) (m : Monotone2 C) : AndOrOnly C := fun g hg => (m g hg).1

  have setMono (C : Circuit) (m : Monotone2 C) (j : ℕ) (g : Gate)
      (good : g.op = .and ∨ g.op = .or) (small : g.inputs.length ≤ 2) :
      Monotone2 (setGate C j g) := by
    intro h hh
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hh
    change (C.gates.set j g)[i]? = some h at hi
    by_cases eq : j = i
    · subst i
      by_cases b : j < C.gates.length
      · rw [List.getElem?_set_self b] at hi
        cases hi
        exact ⟨good, small⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hi
        contradiction
    · rw [List.getElem?_set_ne eq] at hi
      exact m _ (List.mem_iff_getElem?.mpr ⟨i,hi⟩)

  have setGateAt (C : Circuit) (j i : ℕ) (g : Gate) (h : j < C.size) :
      gateAt (setGate C j g) i = if i = j then g else gateAt C i := by
    change (C.gates.set j g).getD i ⟨.or,[]⟩ =
      if i = j then g else C.gates.getD i ⟨.or,[]⟩
    by_cases eq : i = j
    · subst i
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h, ite_eq_left rfl]
      rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm eq), ite_eq_right eq]
      rfl

  have runSet {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.size) (g : Gate)
      (x : Fin n → Bool) :
      (setGate C j g).wires (List.ofFn x) =
        (C.gates.drop (j+1)).foldl step (before C j x ++ [gateResult C j g x]) := by
    change (C.gates.set j g).foldl step (List.ofFn x) = _
    rw [List.set_eq_take_append_cons_drop, ite_eq_left (show j < C.gates.length from hj), List.foldl_append]
    rfl

  have runOrig {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.size) (x : Fin n → Bool) :
      C.wires (List.ofFn x) =
        (C.gates.drop (j+1)).foldl step (before C j x ++ [gateVal n C j x]) := by
    let g := C.gates[j]'hj
    have hs : C.gates = C.gates.take j ++ g :: C.gates.drop (j+1) := by
      rw [show g :: C.gates.drop (j+1) = C.gates.drop j from (List.drop_eq_getElem_cons hj).symm,
        List.take_append_drop]
    have last : step (before C j x) g = before C j x ++ [gateVal n C j x] := by
      rw [gate_from_earlier C j hj x, show gateAt C j = g from List.getD_eq_getElem _ _ hj]
    change C.gates.foldl step (List.ofFn x) = _
    conv_lhs => rw [hs, List.foldl_append]
    exact congrArg ((C.gates.drop (j+1)).foldl step) last

  have altAt {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.size) (g : Gate)
      (x : Fin n → Bool) :
      gateVal n (setGate C j g) j x = gateResult C j g x := by
    change ((setGate C j g).wires (List.ofFn x)).getD (n+j) false = _
    rw [runSet C j hj]
    have lens : (before C j x).length = n+j := by
      have bound : j ≤ C.gates.length := hj.le
      simp [before, wire_len, List.length_take, Nat.min_eq_left bound]
    rw [old_read _ _ _ (by simp [lens])]
    exact List.getD_append_right _ _ _ _ (by omega) |>.trans (by rw [lens]; simp)

  have runCompare {n : ℕ} (C : Circuit) (m : Monotone2 C) (j : ℕ)
      (x : Fin n → Bool) (p q : Bool) (imp : p = true → q = true) :
      ∀ i, ((C.gates.drop (j+1)).foldl step (before C j x ++ [p])).getD i false = true →
        ((C.gates.drop (j+1)).foldl step (before C j x ++ [q])).getD i false = true := by
    apply run_preserves_true
    · exact fun g hg => basisOf C m g (List.mem_of_mem_drop hg)
    · simp
    · intro i h
      by_cases lo : i < (before C j x).length
      · rw [List.getD_append _ _ _ _ lo] at h ⊢
        exact h
      · rw [List.getD_append_right _ _ _ _ (by omega : (before C j x).length ≤ i)] at h ⊢
        by_cases eq : i = (before C j x).length
        · simp only [eq, Nat.sub_self, List.getD_cons_zero] at h ⊢
          exact imp h
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          contradiction

  have dominated {n : ℕ} (C : Circuit) (m : Monotone2 C) (j : ℕ) (hj : j < C.size)
      (g : Gate) (x : Fin n → Bool) (imp : gateResult C j g x = true → gateVal n C j x = true) :
      ∀ i, wireVal n (setGate C j g) i x = true → wireVal n C i x = true := by
    intro i h
    change ((setGate C j g).wires (List.ofFn x)).getD i false = true at h
    change (C.wires (List.ofFn x)).getD i false = true
    rw [runSet C j hj] at h
    rw [runOrig C j hj]
    exact runCompare C m j x _ _ imp i h

  have retains {n : ℕ} (C : Circuit) (m : Monotone2 C) (j : ℕ) (hj : j < C.size)
      (g : Gate) (x : Fin n → Bool)
      (ok : circuitFun n (low (n := n) C j) x = false → gateResult C j g x = true)
      (was : circuitFun n C x = true) :
      circuitFun n (setGate C j g) x = true := by
    change ((setGate C j g).wires (List.ofFn x)).getD C.output false = true
    rw [runSet C j hj]
    by_cases v : gateResult C j g x = true
    · change (C.wires (List.ofFn x)).getD C.output false = true at was
      rw [runOrig C j hj] at was
      exact runCompare C m j x _ _ (fun _ => v) _ was
    · have ht : circuitFun n (low (n := n) C j) x = true := by
        by_contra hf
        exact v (ok (Bool.eq_false_of_not_eq_true hf))
      have e : low (n := n) C j = setGate C j ⟨.or,[]⟩ := rfl
      rw [e] at ht
      change ((setGate C j ⟨.or,[]⟩).wires (List.ofFn x)).getD C.output false = true at ht
      rw [runSet C j hj] at ht
      exact runCompare C m j x _ _ (by intro ht; exact (Bool.false_ne_true ht).elim) _ ht

  have edgeTest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → Bool) :
      graphFun G ∅ a = true ↔ ∃ u v, G.Adj u v ∧ a u = true ∧ a v = true := by
    change (decide (∃ i ∈ (∅ : Finset (Fin n)), a i = true) || decide _) = true ↔ _
    simp

  have pairEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n)
      (h : G.Adj a b) : graphFun G ∅ (pairInput a b) = true := by
    apply (edgeTest G _).mpr
    exact ⟨a,b,h,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩

  have edgeComplete {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
      (m : Monotone2 D) (cap : ∀ a, circuitFun n D a = true → graphFun G ∅ a = true)
      (hits : ∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true) :
      circuitFun n D = graphFun G ∅ := by
    funext a
    apply Bool.eq_iff_iff.mpr
    refine ⟨cap a, ?_⟩
    intro h
    obtain ⟨u,v,edge,hu,hv⟩ := (edgeTest G a).mp h
    apply wire_preserves_true D (basisOf D m) (pairInput u v) a _ D.output (hits u v edge)
    intro i hi
    change decide (i = u ∨ i = v) = true at hi
    rcases (show i = u ∨ i = v from of_decide_eq_true hi) with rfl | rfl
    · exact hu
    · exact hv

  intro n G dec
  dsimp only
  intro tri four C mC fC sC
  classical
  by_cases hVertices : Nonempty (Fin n)
  swap
  · let empty : Circuit := ⟨[], 0⟩
    refine ⟨empty, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp [empty] at hg
    · exact Nat.zero_le C.size
    · intro u
      exact (hVertices ⟨u⟩).elim
    · intro u
      exact (hVertices ⟨u⟩).elim
    · intro j g hj
      simp [empty] at hj
  have exactC : circuitFun n C = graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) = graphFun G ∅ x
    rw [fC]
    change decide _ = (decide (∃ i ∈ (∅ : Finset (Fin n)), x i = true) || decide _)
    simp
  have no4 : NoFourCycle G := by
    intro a b ab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨_, au, bu⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, av, bv⟩ := Finset.mem_filter.mp hv
    exact (four a u b v au bu.symm bv av.symm).resolve_left ab

  let oneClean (A : Circuit) := ∀ j : ℕ, j < A.size → ∀ v : Fin n,
    (gateAt A j).op = .and → gateVal n A j (pairInput v v) = false

  have oneC : oneClean C := by
    intro j hj v hAnd
    let g := C.gates[j]'hj
    have get : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    have eqG : gateAt C j = g := List.getD_eq_getElem _ _ hj
    have eqInput : (fun w : Fin n => decide (w ∈ ({v} : Finset (Fin n)))) = pairInput v v := by
      funext w
      change decide (w ∈ ({v} : Finset (Fin n))) = decide (w = v ∨ w = v)
      simp
    have h := sC j g get (eqG ▸ hAnd) {v} (by simp)
    change gateVal n C j (fun w : Fin n => decide (w ∈ ({v} : Finset (Fin n)))) = false at h
    simpa only [eqInput] using h

  let bad (A : Circuit) : Finset (ℕ × (Fin n × Fin n)) :=
    ((Finset.range A.size) ×ˢ Finset.univ).filter fun z =>
      (gateAt A z.1).op = .and ∧ ¬ G.Adj z.2.1 z.2.2 ∧
      gateVal n A z.1 (pairInput z.2.1 z.2.2) = true

  let candidate (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
    circuitFun n D = graphFun G ∅ ∧ oneClean D ∧ (bad D).card = k

  have someCandidate : ∃ k, candidate k := ⟨_, C, mC, le_rfl, exactC, oneC, rfl⟩
  obtain ⟨D, mD, dSize, dExact, dOne, dCount⟩ := Nat.find_spec someCandidate

  have cannotRepair (j : ℕ) (g : Gate) (u v : Fin n) (hj : j < D.size)
      (jAnd : (gateAt D j).op = .and) (he : ¬ G.Adj u v)
      (on : gateVal n D j (pairInput u v) = true)
      (valid : Monotone2 (setGate D j g))
      (cap : ∀ x, gateVal n (setGate D j g) j x = true → gateVal n D j x = true)
      (off : gateVal n (setGate D j g) j (pairInput u v) = false) :
      circuitFun n (setGate D j g) ≠ graphFun G ∅ ∧
      ∃ a b, G.Adj a b ∧ circuitFun n (low (n := n) D j) (pairInput a b) = false ∧
        gateVal n (setGate D j g) j (pairInput a b) = false := by
    let E := setGate D j g
    have esize : E.size = D.size := List.length_set
    have shrink (x : Fin n → Bool) (i : ℕ) : wireVal n E i x = true → wireVal n D i x = true := by
      apply dominated D mD j hj g x
      rw [← altAt D j hj g x]
      exact cap x
    have oldAnd (i : ℕ) (isAnd : (gateAt E i).op = .and) : (gateAt D i).op = .and := by
      by_cases e : i = j
      · rwa [e]
      · rw [setGateAt D j i g hj, ite_eq_right e] at isAnd
        exact isAnd
    have eone : oneClean E := by
      intro i hi z op
      by_contra err
      have yup := Bool.eq_true_of_not_eq_false err
      have oldVal : gateVal n D i (pairInput z z) = true := shrink _ _ yup
      rw [dOne i (esize ▸ hi) z (oldAnd i op)] at oldVal
      contradiction
    have exactLost : circuitFun n E ≠ graphFun G ∅ := by
      intro calcE
      have subset : bad E ⊆ bad D := by
        rintro ⟨i, a, b⟩ h
        obtain ⟨hm, op, ne, y⟩ := Finset.mem_filter.mp h
        apply Finset.mem_filter.mpr
        refine ⟨?_, oldAnd i op, ne, shrink _ _ y⟩
        rw [esize] at hm
        exact hm
      have strict : bad E ⊂ bad D := by
        apply (Finset.ssubset_iff_of_subset subset).mpr
        refine ⟨(j,u,v), ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩, jAnd, he, on⟩
        · intro yes
          exact Bool.false_ne_true (off ▸ (Finset.mem_filter.mp yes).2.2.2)
      have hmin : Nat.find someCandidate ≤ (bad E).card :=
        Nat.find_min' someCandidate ⟨E, valid, esize ▸ dSize, calcE, eone, rfl⟩
      have hsmall := Finset.card_lt_card strict
      omega
    refine ⟨exactLost, ?_⟩
    by_contra! none
    apply exactLost
    apply edgeComplete G E valid
    · intro x out
      rw [← dExact]
      exact shrink x D.output out
    · intro a b adj
      apply retains D mD j hj g (pairInput a b)
      · intro drops
        rw [← altAt D j hj g (pairInput a b)]
        exact Bool.eq_true_of_not_eq_false (none a b adj drops)
      · rw [dExact]
        exact pairEdge G a b adj

  have triFree : G.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hs.2
    have edges := hs.1
    rw [hset] at edges
    have ab := edges (by simp : a ∈ ({a,b,c} : Finset (Fin n)))
      (by simp : b ∈ ({a,b,c} : Finset (Fin n))) hab
    have bc := edges (by simp : b ∈ ({a,b,c} : Finset (Fin n)))
      (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hbc
    have ca := edges (by simp : c ∈ ({a,b,c} : Finset (Fin n)))
      (by simp : a ∈ ({a,b,c} : Finset (Fin n))) hac.symm
    exact tri a b c ab bc ca
  have secure : ∀ j g u v, j < D.size → (gateAt D j).op = .and → ¬ G.Adj u v →
      gateVal n D j (pairInput u v) = true →
      Monotone2 (setGate D j g) →
      (∀ x, gateVal n (setGate D j g) j x = true → gateVal n D j x = true) →
      gateVal n (setGate D j g) j (pairInput u v) = false →
      circuitFun n (setGate D j g) ≠ graphFun G ∅ :=
    fun j g u v hj hAnd ne on m cap off => (cannotRepair j g u v hj hAnd ne on m cap off).1
  obtain ⟨E, mE, szE, exE, clean⟩ :
      ∃ E : Circuit, Monotone2 E ∧ E.size ≤ D.size ∧ circuitFun n E = graphFun G ∅ ∧
        ∀ j u v, (gateAt E j).op = .and → gateVal n E j (pairInput u v) = true → G.Adj u v := by
    by_cases h : G.IsBipartite
    · exact bipartite n G D no4 h mD dExact dOne secure
    · exact odd n G D no4 triFree h mD dExact dOne secure
  have pairMark (u v : Fin n) :
      (fun w : Fin n => decide (w ∈ ({u,v} : Finset (Fin n)))) = pairInput u v := by
    funext w
    change decide (w ∈ ({u,v} : Finset (Fin n))) = decide (w = u ∨ w = v)
    simp
  have oneMark (u : Fin n) :
      (fun w : Fin n => decide (w ∈ ({u} : Finset (Fin n)))) = pairInput u u := by
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self u)] using pairMark u u
  have accept (u v : Fin n) (h : G.Adj u v) : E.eval (List.ofFn (pairInput u v)) = true := by
    change circuitFun n E (pairInput u v) = true
    rw [exE]
    exact pairEdge G u v h
  refine ⟨E, mE, szE.trans dSize, ?_, ?_, ?_⟩
  · intro u v h
    rw [pairMark]
    exact accept u v h
  · intro u
    rw [oneMark]
    change circuitFun n E (pairInput u u) = false
    rw [exE]
    apply Bool.eq_false_of_not_eq_true
    intro h
    obtain ⟨a, b, ab, ha, hb⟩ := (edgeTest G _).mp h
    change decide (a = u ∨ a = u) = true at ha
    change decide (b = u ∨ b = u) = true at hb
    have aU : a = u := by simpa using ha
    have bU : b = u := by simpa using hb
    exact (ab.ne (aU.trans bU.symm)).elim
  · intro j g get gAnd S hs active
    have gate : gateAt E j = g := by
      change E.gates.getD j ⟨.or, []⟩ = g
      rw [List.getD_eq_getElem?_getD, get]
      rfl
    have andGate : (gateAt E j).op = .and := gate ▸ gAnd
    by_cases hTwo : S.card = 2
    · obtain ⟨u, v, _, rfl⟩ := Finset.card_eq_two.mp hTwo
      change gateVal n E j (fun w : Fin n => decide (w ∈ ({u,v} : Finset (Fin n)))) = true at active
      rw [pairMark] at active
      exact ⟨u, by simp, v, by simp, clean j u v andGate active⟩
    · have hOne : S.card ≤ 1 := by omega
      by_cases hne : S.Nonempty
      · obtain ⟨u, hu⟩ := hne
        have single : S = {u} := by
          ext w
          simpa only [Finset.mem_singleton] using
            (show w ∈ S ↔ w = u from ⟨fun hw => Finset.card_le_one.mp hOne w hw u hu,
              fun h => h ▸ hu⟩)
        subst S
        change gateVal n E j (fun w : Fin n => decide (w ∈ ({u} : Finset (Fin n)))) = true at active
        rw [oneMark] at active
        exact ((G.loopless.irrefl u) (clean j u u andGate active)).elim
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne] at active
        obtain ⟨u⟩ := hVertices
        have on : gateVal n E j (pairInput u u) = true := by
          apply wire_preserves_true E (basisOf E mE) (fun w : Fin n => decide (w ∈ (∅ : Finset (Fin n)))) _ _ (n+j) active
          simp
        exact ((G.loopless.irrefl u) (clean j u u andGate on)).elim
