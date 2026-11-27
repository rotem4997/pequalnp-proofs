import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

-- Replace an AND by an OR of two singleton witnesses at the same gate index.
-- A circuit minimizing the number of ANDs that accept a singleton must lose a remote edge under each such replacement.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4316_1
    (single : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      let on (D : Circuit) (j : ℕ) (u : Fin n) := gateVal n D j (pairInput u u)
      (∀ j < C.size, (gateAt C j).op = .and → ∀ x y, on C j x = true → on C j y = true →
        ∃ a b, G.Adj a b ∧ x ∉ s(a,b) ∧ y ∉ s(a,b) ∧ gateVal n C j (pairInput a b) = true ∧
          (Circuit.mk (C.gates.set j ⟨.or, [x.val,y.val]⟩) C.output).eval (List.ofFn (pairInput a b)) = false) →
      (∃ j < C.size, (gateAt C j).op = .and ∧ ∃! u, on C j u = true) → ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size ≤ C.size ∧
        ∀ j < D.size, (gateAt D j).op = .and → ∀ u, on D j u = false)
    (multiple : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      let on (D : Circuit) (j : ℕ) (u : Fin n) := gateVal n D j (pairInput u u)
      (∀ j < C.size, (gateAt C j).op = .and → ∀ x y, on C j x = true → on C j y = true →
        ∃ a b, G.Adj a b ∧ x ∉ s(a,b) ∧ y ∉ s(a,b) ∧ gateVal n C j (pairInput a b) = true ∧
          (Circuit.mk (C.gates.set j ⟨.or, [x.val,y.val]⟩) C.output).eval (List.ofFn (pairInput a b)) = false) →
      (∀ j < C.size, (gateAt C j).op = .and → ∀ u, on C j u = true → ∃ v ≠ u, on C j v = true) → ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size ≤ C.size ∧
        ∀ j < D.size, (gateAt D j).op = .and → ∀ u, on D j u = false) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → x2.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x7.size ∧ ∀ x11 < x10.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x14 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x10 x11 (PEqualNP.EdgeOwnership.pairInput x14 x14) = Bool.false := by
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

  let replaceAt {n : ℕ} (C : Circuit) (j : ℕ) (x y : Fin n) : Circuit :=
    ⟨C.gates.set j ⟨.or,[x.val,y.val]⟩, C.output⟩

  have basisOf (C : Circuit) (m : Monotone2 C) : AndOrOnly C := fun g hg => (m g hg).1

  have replMono {n : ℕ} (C : Circuit) (m : Monotone2 C) (j : ℕ) (x y : Fin n) :
      Monotone2 (replaceAt C j x y) := by
    intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    change (C.gates.set j _)[i]? = some g at hi
    by_cases h : j = i
    · subst i
      by_cases b : j < C.gates.length
      · rw [List.getElem?_set_self b] at hi
        cases hi
        simp
      · rw [List.getElem?_eq_none (by simp; omega)] at hi
        contradiction
    · rw [List.getElem?_set_ne h] at hi
      exact m _ (List.mem_iff_getElem?.mpr ⟨i,hi⟩)

  have replRun {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.size) (x y : Fin n)
      (a : Fin n → Bool) :
      let pre := (C.gates.take j).foldl step (List.ofFn a)
      let post := C.gates.drop (j+1)
      (C.wires (List.ofFn a) = post.foldl step (pre ++ [gateVal n C j a])) ∧
        ((replaceAt C j x y).wires (List.ofFn a) = post.foldl step (pre ++ [a x || a y])) := by
    let pre := (C.gates.take j).foldl step (List.ofFn a)
    let post := C.gates.drop (j+1)
    let g := C.gates[j]'hj
    let alt : Gate := ⟨.or,[x.val,y.val]⟩
    have hs : C.gates = C.gates.take j ++ g :: post := by
      rw [show g :: post = C.gates.drop j from (List.drop_eq_getElem_cons hj).symm, List.take_append_drop]
    have orig : step pre g = pre ++ [gateVal n C j a] := by
      rw [gate_from_earlier C j hj a, show gateAt C j = g from List.getD_eq_getElem _ _ hj]
    have raw (z : Fin n) : pre.getD z.val false = a z := by
      change ((C.gates.take j).foldl step (List.ofFn a)).getD z.val false = _
      rw [old_read _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, z.isLt]
    have altVal : step pre alt = pre ++ [a x || a y] := by
      change pre ++ [pre.getD x false || (pre.getD y false || false)] = _
      rw [raw x, raw y, Bool.or_false]
    constructor
    · change (C.gates.foldl step (List.ofFn a)) = post.foldl step (pre ++ [gateVal n C j a])
      conv_lhs => rw [hs, List.foldl_append]
      exact congrArg (post.foldl step) orig
    · change (C.gates.set j alt).foldl step (List.ofFn a) = post.foldl step (pre ++ [a x || a y])
      rw [List.set_eq_take_append_cons_drop, ite_eq_left (show j < C.gates.length from hj), List.foldl_append]
      exact congrArg (post.foldl step) altVal

  have shrink {n : ℕ} (C : Circuit) (m : Monotone2 C) (j : ℕ) (hj : j < C.size) (x y : Fin n)
      (hx : gateVal n C j (pairInput x x) = true) (hy : gateVal n C j (pairInput y y) = true)
      (a : Fin n → Bool) :
      (((a x || a y) = true → gateVal n C j a = true) ∧
       (∀ i, wireVal n (replaceAt C j x y) i a = true → wireVal n C i a = true)) := by
    have one (z : Fin n) (hz : gateVal n C j (pairInput z z) = true) (az : a z = true) :
        gateVal n C j a = true := by
      apply wire_preserves_true C (basisOf C m) (pairInput z z) a _ (n+j) hz
      intro i h
      change decide (i = z ∨ i = z) = true at h
      rcases (show i = z ∨ i = z from of_decide_eq_true h) with rfl | rfl <;> exact az
    have joined : (a x || a y) = true → gateVal n C j a = true := by
      intro h
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact one x hx h
      · exact one y hy h
    refine ⟨joined, ?_⟩
    let pre := (C.gates.take j).foldl step (List.ofFn a)
    have runs := replRun C j hj x y a
    change ∀ i, ((replaceAt C j x y).wires (List.ofFn a)).getD i false = true →
      (C.wires (List.ofFn a)).getD i false = true
    rw [runs.1,runs.2]
    apply run_preserves_true
    · exact fun g h => basisOf C m g (List.mem_of_mem_drop h)
    · simp
    · intro i h
      change (pre ++ [_]).getD i false = true at h ⊢
      by_cases lo : i < pre.length
      · rw [List.getD_append _ _ _ _ lo] at h ⊢; exact h
      · rw [List.getD_append_right _ _ _ _ (by omega : pre.length ≤ i)] at h ⊢
        by_cases eq : i = pre.length
        · simp only [eq, Nat.sub_self, List.getD_cons_zero] at h ⊢
          exact joined h
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          contradiction

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
  intro n G decG tri four nonempty C mC fC
  classical
  let bad (D : Circuit) := (Finset.range D.size).filter fun j =>
    (gateAt D j).op = .and ∧ ∃ u : Fin n, gateVal n D j (pairInput u u) = true
  let candidates (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
    D.size ≤ C.size ∧ (bad D).card = k
  have inhabited : ∃ k, candidates k := ⟨_,C,mC,fC,le_rfl,rfl⟩
  obtain ⟨D,mD,fD,sz,mincount⟩ := Nat.find_spec inhabited
  have robust (j : ℕ) (hj : j < D.size) (op : (gateAt D j).op = .and) (x y : Fin n)
      (hx : gateVal n D j (pairInput x x) = true) (hy : gateVal n D j (pairInput y y) = true) :
      ∃ a b, G.Adj a b ∧ x ∉ s(a,b) ∧ y ∉ s(a,b) ∧ gateVal n D j (pairInput a b) = true ∧
        (replaceAt D j x y).eval (List.ofFn (pairInput a b)) = false := by
    let E := replaceAt D j x y
    have sizeE : E.size = D.size := List.length_set
    have mE : Monotone2 E := replMono D mD j x y
    have noExact : circuitFun n E ≠ graphFun G ∅ := by
      intro fE
      have gateChanged : (gateAt E j).op = .or := by
        change ((D.gates.set j _).getD j ⟨.or, []⟩).op = .or
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
        rfl
      have small : bad E ⊂ bad D := by
        have sub : bad E ⊆ bad D := by
          intro i hi
          obtain ⟨ilt,op',u,hu⟩ := Finset.mem_filter.mp hi
          have neq : j ≠ i := by
            rintro rfl
            rw [gateChanged] at op'
            contradiction
          have gEq : gateAt E i = gateAt D i := by
            change (D.gates.set j _).getD i ⟨.or,[]⟩ = D.gates.getD i ⟨.or,[]⟩
            simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne neq]
          exact Finset.mem_filter.mpr ⟨sizeE ▸ ilt, (congrArg Gate.op gEq).symm.trans op', u,
            (shrink D mD j hj x y hx hy (pairInput u u)).2 (n+i) hu⟩
        apply (Finset.ssubset_iff_of_subset sub).mpr
        · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, op, x, hx⟩, ?_⟩
          intro badJ
          have impossible := (Finset.mem_filter.mp badJ).2.1
          rw [gateChanged] at impossible
          contradiction
      have lower : Nat.find inhabited ≤ (bad E).card := Nat.find_min' inhabited ⟨E,mE,fE,sizeE ▸ sz,rfl⟩
      have less := Finset.card_lt_card small
      omega
    have cap (a : Fin n → Bool) : circuitFun n E a = true → graphFun G ∅ a = true := by
      rw [← fD]
      exact (shrink D mD j hj x y hx hy a).2 D.output
    have lost : ∃ a b, G.Adj a b ∧ circuitFun n E (pairInput a b) = false := by
      by_contra! none
      apply noExact
      apply edgeComplete G E mE cap
      intro a b e
      exact Bool.eq_true_of_not_eq_false (none a b e)
    obtain ⟨a,b,edge,miss⟩ := lost
    let p := pairInput a b
    have old : D.eval (List.ofFn p) = true := (congrFun fD p).trans (pairEdge G a b edge)
    have diff : (p x || p y) ≠ gateVal n D j p := by
      intro eq
      have rr := replRun D j hj x y p
      have w : E.wires (List.ofFn p) = D.wires (List.ofFn p) := by rw [rr.2,rr.1,eq]
      change (E.wires (List.ofFn p)).getD D.output false = false at miss
      change (D.wires (List.ofFn p)).getD D.output false = true at old
      exact Bool.noConfusion (miss.symm.trans ((congrArg (fun s : List Bool => s.getD D.output false) w).trans old))
    have newFalse : (p x || p y) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro yes
      exact diff (yes.trans ((shrink D mD j hj x y hx hy p).1 yes).symm)
    have oldTrue : gateVal n D j p = true := by
      apply Bool.eq_true_of_not_eq_false
      exact fun no => diff (newFalse.trans no.symm)
    have apart (t : Fin n) (h : p t = false) : t ∉ s(a,b) := by
      intro ht
      have yes : p t = true := decide_eq_true (Sym2.mem_iff.mp ht)
      exact Bool.noConfusion (h.symm.trans yes)
    obtain ⟨fx,fy⟩ := Bool.or_eq_false_iff.mp newFalse
    exact ⟨a,b,edge,apart x fx,apart y fy,oldTrue,miss⟩
  by_cases one : ∃ j < D.size, (gateAt D j).op = .and ∧ ∃! u : Fin n,
      gateVal n D j (pairInput u u) = true
  · obtain ⟨W,m,f,s,c⟩ := single n G tri four nonempty D mD fD robust one
    exact ⟨W,m,f.trans fD,s.trans sz,c⟩
  · have many (j : ℕ) (hj : j < D.size) (op : (gateAt D j).op = .and) (u : Fin n)
        (hu : gateVal n D j (pairInput u u) = true) :
        ∃ v ≠ u, gateVal n D j (pairInput v v) = true := by
      by_contra! none
      apply one
      refine ⟨j,hj,op,u,hu,fun v hv => ?_⟩
      by_contra ne
      exact none v ne hv
    obtain ⟨W,m,f,s,c⟩ := multiple n G tri four nonempty D mD fD robust many
    exact ⟨W,m,f.trans fD,s.trans sz,c⟩
