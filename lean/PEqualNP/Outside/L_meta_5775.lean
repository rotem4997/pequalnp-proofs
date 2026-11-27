import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5775

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def validStep (f1 f2 : DMFormula 14) (p1 p2 : Prop) : Prop :=
  p1 ∧ p2 ∧ ¬∃ i : Fin 14, f1 = DMFormula.lit i true ∧ f2 = DMFormula.lit i true

def valid (f : DMFormula 14) : Prop :=
  DMFormula.rec (fun _ b => b = true) validStep validStep f

def fDeg (k : ℕ) : DMFormula 14 → ℕ
  | DMFormula.lit i _ => if (i : ℕ) = k then 1 else 0
  | DMFormula.and f1 f2 => fDeg k f1 + fDeg k f2
  | DMFormula.or f1 f2 => max (fDeg k f1) (fDeg k f2)

lemma fDeg_eq_rec (k : ℕ) (f : DMFormula 14) :
    fDeg k f = DMFormula.rec (fun (i : Fin 14) (_ : Bool) => if (i : ℕ) = k then 1 else 0)
      (fun _ _ a b => a + b) (fun _ _ a b => max a b) f := by
  induction f with
  | lit i b => rfl
  | and f1 f2 ih1 ih2 => simp only [fDeg, ih1, ih2]
  | or f1 f2 ih1 ih2 => simp only [fDeg, ih1, ih2]

def shiftWire (off w : ℕ) : ℕ :=
  if w < 14 then w else w + off

def shiftGate (off : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire off)⟩

def shiftGates (off : ℕ) (gs : List Gate) : List Gate :=
  gs.map (shiftGate off)

def combine (op : GateOp) (c1 c2 : Circuit) : Circuit :=
  let off := c1.gates.length
  ⟨c1.gates ++ shiftGates off c2.gates ++ [⟨op, [c1.output, shiftWire off c2.output]⟩],
    14 + off + c2.gates.length⟩

def compile : DMFormula 14 → Circuit
  | DMFormula.lit i _ => ⟨[], i.val⟩
  | DMFormula.and f1 f2 => combine GateOp.and (compile f1) (compile f2)
  | DMFormula.or f1 f2 => combine GateOp.or (compile f1) (compile f2)

def usedGateWires (c : Circuit) : List ℕ :=
  List.filter (fun w => decide (14 ≤ w)) (c.output :: List.flatMap Gate.inputs c.gates)

def stepGen {α : Type} (d0 : α) (f : GateOp → List α → α) (w : List α) (g : Gate) : List α :=
  w ++ [f g.op (g.inputs.map fun i => w.getD i d0)]

def evalGen {α : Type} (d0 : α) (f : GateOp → List α → α) (c : Circuit) (xs : List α) : α :=
  (c.gates.foldl (stepGen d0 f) xs).getD c.output d0

def lineDegOp : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.sum
  | _, l => l.foldr max 0

lemma shiftWire_injective (off : ℕ) : Function.Injective (shiftWire off) := by
  intro a b h
  unfold shiftWire at h
  split_ifs at h <;> omega

lemma le_shiftWire_iff (off w : ℕ) : 14 ≤ shiftWire off w ↔ 14 ≤ w := by
  unfold shiftWire
  split_ifs <;> omega

lemma filter_map_shiftWire (off : ℕ) (l : List ℕ) :
    List.filter (fun w => decide (14 ≤ w)) (l.map (shiftWire off)) =
      (List.filter (fun w => decide (14 ≤ w)) l).map (shiftWire off) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons]
    have hiff : decide (14 ≤ shiftWire off a) = decide (14 ≤ a) :=
      decide_eq_decide.mpr (le_shiftWire_iff off a)
    rw [hiff]
    cases decide (14 ≤ a) <;> simp [ih]

lemma flatMap_inputs_shiftGates (off : ℕ) (gs : List Gate) :
    List.flatMap Gate.inputs (shiftGates off gs) =
      (List.flatMap Gate.inputs gs).map (shiftWire off) := by
  induction gs with
  | nil => rfl
  | cons g t ih =>
    simp only [shiftGates, List.map_cons, List.flatMap_cons, shiftGate, List.map_append]
    rw [← shiftGates, ih]

lemma compile_output_lt (f : DMFormula 14) :
    (compile f).output < 14 + (compile f).gates.length := by
  cases f with
  | lit i b =>
    simp only [compile, List.length_nil, Nat.add_zero]
    exact i.isLt
  | and f1 f2 =>
    simp only [compile, combine, shiftGates, List.length_append, List.length_map,
      List.length_singleton]
    omega
  | or f1 f2 =>
    simp only [compile, combine, shiftGates, List.length_append, List.length_map,
      List.length_singleton]
    omega

lemma output_lt_14_of_valid {f : DMFormula 14} (hf : valid f) (h : (compile f).output < 14) :
    ∃ i : Fin 14, f = DMFormula.lit i true ∧ (compile f).output = i.val := by
  cases f with
  | lit i b =>
    have hb : b = true := hf
    subst hb
    exact ⟨i, rfl, rfl⟩
  | and f1 f2 =>
    simp only [compile, combine] at h
    omega
  | or f1 f2 =>
    simp only [compile, combine] at h
    omega

lemma outputs_ne {f1 f2 : DMFormula 14} (h1 : valid f1) (h2 : valid f2)
    (hdiff : ¬∃ i : Fin 14, f1 = DMFormula.lit i true ∧ f2 = DMFormula.lit i true) :
    (compile f1).output ≠ shiftWire (compile f1).gates.length (compile f2).output := by
  intro heq
  by_cases ho1 : (compile f1).output < 14
  · by_cases ho2 : (compile f2).output < 14
    · simp only [shiftWire, ho2, ite_true] at heq
      obtain ⟨i, rfl, hi⟩ := output_lt_14_of_valid h1 ho1
      obtain ⟨j, rfl, hj⟩ := output_lt_14_of_valid h2 ho2
      have hij : i = j := Fin.ext (by omega)
      subst hij
      exact hdiff ⟨i, rfl, rfl⟩
    · simp only [shiftWire, ho2, ite_false] at heq
      omega
  · by_cases ho2 : (compile f2).output < 14
    · simp only [shiftWire, ho2, ite_true] at heq
      omega
    · simp only [shiftWire, ho2, ite_false] at heq
      have hlt := compile_output_lt f1
      omega

lemma andOrOnly_combine {op : GateOp} {c1 c2 : Circuit}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (h1 : AndOrOnly c1) (h2 : AndOrOnly c2) :
    AndOrOnly (combine op c1 c2) := by
  intro g hg
  simp only [combine, shiftGates, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact h1 g hg
  · exact h2 g' hg'
  · exact hop

lemma len2_combine {op : GateOp} {c1 c2 : Circuit}
    (h1 : ∀ g ∈ c1.gates, g.inputs.length = 2)
    (h2 : ∀ g ∈ c2.gates, g.inputs.length = 2) :
    ∀ g ∈ (combine op c1 c2).gates, g.inputs.length = 2 := by
  intro g hg
  simp only [combine, shiftGates, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact h1 g hg
  · simp only [shiftGate, List.length_map]
    exact h2 g' hg'
  · rfl

lemma readsBack_combine {op : GateOp} {c1 c2 : Circuit}
    (h1 : ReadsBack 14 c1) (h2 : ReadsBack 14 c2)
    (ho1 : c1.output < 14 + c1.gates.length)
    (ho2 : c2.output < 14 + c2.gates.length) :
    ReadsBack 14 (combine op c1 c2) := by
  intro j hj i hi
  simp only [combine, shiftGates, List.length_append, List.length_map,
    List.length_singleton] at hj
  unfold gateAt at hi
  rw [List.getD_eq_getElem?_getD] at hi
  by_cases hj1 : j < c1.gates.length
  · have hget : (combine op c1 c2).gates[j]? = c1.gates[j]? := by
      simp only [combine, List.append_assoc]
      exact List.getElem?_append_left hj1
    rw [hget] at hi
    have hi' : i ∈ (gateAt c1 j).inputs := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD]
      exact hi
    exact h1 j hj1 i hi'
  · by_cases hj2 : j < c1.gates.length + c2.gates.length
    · have hk : j - c1.gates.length < c2.gates.length := by omega
      have hget : (combine op c1 c2).gates[j]? =
          some (shiftGate c1.gates.length (c2.gates[j - c1.gates.length]'hk)) := by
        simp only [combine, shiftGates]
        rw [List.getElem?_append_left (by simp; omega)]
        rw [List.getElem?_append_right (by omega)]
        rw [List.getElem?_map, List.getElem?_eq_getElem hk]
        rfl
      rw [hget] at hi
      simp only [Option.getD_some, shiftGate, List.mem_map] at hi
      obtain ⟨w, hw, rfl⟩ := hi
      have hw' : w ∈ (gateAt c2 (j - c1.gates.length)).inputs := by
        unfold gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        exact hw
      have hlt := h2 (j - c1.gates.length) hk w hw'
      unfold shiftWire
      split_ifs <;> omega
    · have hjeq : j = c1.gates.length + c2.gates.length := by omega
      have hlen : (c1.gates ++ shiftGates c1.gates.length c2.gates).length = j := by
        simp only [shiftGates, List.length_append, List.length_map]
        omega
      have hget : (combine op c1 c2).gates[j]? =
          some ⟨op, [c1.output, shiftWire c1.gates.length c2.output]⟩ := by
        simp only [combine]
        rw [List.getElem?_append_right (by omega)]
        rw [hlen, Nat.sub_self]
        rfl
      rw [hget] at hi
      simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · unfold shiftWire
        split_ifs <;> omega

lemma gateInputs_nodup_combine {op : GateOp} {c1 c2 : Circuit}
    (h1 : ∀ g ∈ c1.gates, g.inputs.Nodup)
    (h2 : ∀ g ∈ c2.gates, g.inputs.Nodup)
    (hne : c1.output ≠ shiftWire c1.gates.length c2.output) :
    ∀ g ∈ (combine op c1 c2).gates, g.inputs.Nodup := by
  intro g hg
  simp only [combine, shiftGates, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact h1 g hg
  · exact (h2 g' hg').map (shiftWire_injective c1.gates.length)
  · simp [hne]

lemma usedGateWires_bounds {c : Circuit} (hrb : ReadsBack 14 c)
    (ho : c.output < 14 + c.gates.length) :
    ∀ w ∈ usedGateWires c, 14 ≤ w ∧ w < 14 + c.gates.length := by
  intro w hw
  simp only [usedGateWires, List.mem_filter, decide_eq_true_eq, List.mem_cons,
    List.mem_flatMap] at hw
  refine ⟨hw.2, ?_⟩
  rcases hw.1 with rfl | ⟨g, hg, hwg⟩
  · exact ho
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hwg' : w ∈ (gateAt c j).inputs := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact hwg
    have hlt := hrb j hj w hwg'
    omega

lemma usedGateWires_perm_combine (op : GateOp) (c1 c2 : Circuit) :
    (usedGateWires (combine op c1 c2)).Perm
      ((14 + c1.gates.length + c2.gates.length) ::
        (usedGateWires c1 ++ (usedGateWires c2).map (shiftWire c1.gates.length))) := by
  unfold usedGateWires combine
  simp only [List.flatMap_append, List.flatMap_singleton, flatMap_inputs_shiftGates]
  rw [List.filter_cons]
  have htop : decide (14 ≤ 14 + c1.gates.length + c2.gates.length) = true :=
    decide_eq_true (by omega)
  rw [htop]
  simp only [ite_true]
  apply List.Perm.cons
  simp only [List.filter_append, filter_map_shiftWire]
  have hpair :
      List.filter (fun w => decide (14 ≤ w))
        [c1.output, shiftWire c1.gates.length c2.output] =
      List.filter (fun w => decide (14 ≤ w)) [c1.output] ++
        (List.filter (fun w => decide (14 ≤ w)) [c2.output]).map
          (shiftWire c1.gates.length) := by
    rw [← filter_map_shiftWire]
    have hcons : [c1.output, shiftWire c1.gates.length c2.output] =
        [c1.output] ++ [c2.output].map (shiftWire c1.gates.length) := rfl
    rw [hcons, List.filter_append]
  rw [hpair]
  have h1 :
      List.filter (fun w => decide (14 ≤ w)) (c1.output :: List.flatMap Gate.inputs c1.gates) =
      List.filter (fun w => decide (14 ≤ w)) [c1.output] ++
        List.filter (fun w => decide (14 ≤ w)) (List.flatMap Gate.inputs c1.gates) := by
    rw [← List.filter_append]
    rfl
  have h2 :
      (List.filter (fun w => decide (14 ≤ w))
          (c2.output :: List.flatMap Gate.inputs c2.gates)).map (shiftWire c1.gates.length) =
      (List.filter (fun w => decide (14 ≤ w)) [c2.output]).map (shiftWire c1.gates.length) ++
        (List.filter (fun w => decide (14 ≤ w)) (List.flatMap Gate.inputs c2.gates)).map
          (shiftWire c1.gates.length) := by
    rw [← List.map_append, ← List.filter_append]
    rfl
  rw [h1, h2]
  set A := List.filter (fun w => decide (14 ≤ w)) (List.flatMap Gate.inputs c1.gates)
  set B := (List.filter (fun w => decide (14 ≤ w)) (List.flatMap Gate.inputs c2.gates)).map
    (shiftWire c1.gates.length)
  set C := List.filter (fun w => decide (14 ≤ w)) [c1.output]
  set D := (List.filter (fun w => decide (14 ≤ w)) [c2.output]).map (shiftWire c1.gates.length)
  have p1 : (A ++ B ++ (C ++ D)).Perm ((C ++ D) ++ (A ++ B)) := List.perm_append_comm
  have p2 : ((C ++ D) ++ (A ++ B)).Perm (C ++ ((A ++ B) ++ D)) := by
    rw [List.append_assoc]
    exact List.Perm.append_left C List.perm_append_comm
  have p3 : (C ++ ((A ++ B) ++ D)).Perm ((C ++ A) ++ (D ++ B)) := by
    have heq1 : C ++ ((A ++ B) ++ D) = (C ++ A) ++ (B ++ D) := by simp [List.append_assoc]
    rw [heq1]
    exact List.Perm.append_left (C ++ A) List.perm_append_comm
  exact p1.trans (p2.trans p3)

lemma usedGateWires_nodup_combine (op : GateOp) {c1 c2 : Circuit}
    (hrb1 : ReadsBack 14 c1) (hrb2 : ReadsBack 14 c2)
    (ho1 : c1.output < 14 + c1.gates.length) (ho2 : c2.output < 14 + c2.gates.length)
    (hn1 : (usedGateWires c1).Nodup) (hn2 : (usedGateWires c2).Nodup) :
    (usedGateWires (combine op c1 c2)).Nodup := by
  rw [(usedGateWires_perm_combine op c1 c2).nodup_iff]
  have hb1 := usedGateWires_bounds hrb1 ho1
  have hb2 := usedGateWires_bounds hrb2 ho2
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hmem
    rw [List.mem_append] at hmem
    rcases hmem with h | h
    · have := hb1 _ h
      omega
    · rw [List.mem_map] at h
      obtain ⟨w, hw, heq⟩ := h
      have := hb2 w hw
      unfold shiftWire at heq
      split_ifs at heq <;> omega
  · rw [List.nodup_append]
    refine ⟨hn1, hn2.map (shiftWire_injective c1.gates.length), ?_⟩
    intro a ha b hb hab
    subst hab
    rw [List.mem_map] at hb
    obtain ⟨w, hw, heq⟩ := hb
    have h1 := hb1 _ ha
    have h2 := hb2 w hw
    unfold shiftWire at heq
    split_ifs at heq <;> omega

lemma getD_append_shiftWire {α : Type} (d0 : α) (off : ℕ) (xs g1 g2 : List α)
    (hxs : xs.length = 14) (hg1 : g1.length = off) (i : ℕ) :
    (xs ++ g1 ++ g2).getD (shiftWire off i) d0 = (xs ++ g2).getD i d0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  unfold shiftWire
  split_ifs with hi
  · rw [List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by simp [hxs, hg1]; omega)]
    rw [List.getElem?_append_right (by omega)]
    have hsub : i + off - (xs ++ g1).length = i - xs.length := by
      simp [hxs, hg1]
      omega
    rw [hsub]

lemma foldl_stepGen_append {α : Type} (d0 : α) (f : GateOp → List α → α) :
    ∀ (gs : List Gate) (w : List α),
      ∃ t : List α, t.length = gs.length ∧ gs.foldl (stepGen d0 f) w = w ++ t
  | [], w => ⟨[], rfl, by simp⟩
  | g :: gs, w => by
    simp only [List.foldl_cons, stepGen]
    obtain ⟨t, htlen, hteq⟩ :=
      foldl_stepGen_append d0 f gs (w ++ [f g.op (g.inputs.map fun i => w.getD i d0)])
    refine ⟨f g.op (g.inputs.map fun i => w.getD i d0) :: t, by simp [htlen], ?_⟩
    rw [hteq]
    simp [List.append_assoc]

lemma foldl_stepGen_shift {α : Type} (d0 : α) (f : GateOp → List α → α) (off : ℕ)
    (xs g1 : List α) (hxs : xs.length = 14) (hg1 : g1.length = off) :
    ∀ (gs : List Gate) (g2 : List α),
      ∃ t : List α, t.length = gs.length ∧
        gs.foldl (stepGen d0 f) (xs ++ g2) = xs ++ g2 ++ t ∧
        (shiftGates off gs).foldl (stepGen d0 f) (xs ++ g1 ++ g2) = xs ++ g1 ++ g2 ++ t
  | [], g2 => ⟨[], rfl, by simp, by simp [shiftGates]⟩
  | g :: gs, g2 => by
    simp only [shiftGates, List.map_cons, List.foldl_cons]
    have hmap :
        (shiftGate off g).inputs.map (fun i => (xs ++ g1 ++ g2).getD i d0) =
          g.inputs.map (fun i => (xs ++ g2).getD i d0) := by
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact getD_append_shiftWire d0 off xs g1 g2 hxs hg1 i
    set v := f g.op (g.inputs.map fun i => (xs ++ g2).getD i d0)
    have hstep1 : stepGen d0 f (xs ++ g2) g = xs ++ (g2 ++ [v]) := by
      simp only [stepGen, v, List.append_assoc]
    have hstep2 : stepGen d0 f (xs ++ g1 ++ g2) (shiftGate off g) = xs ++ g1 ++ (g2 ++ [v]) := by
      unfold stepGen
      rw [hmap]
      simp only [shiftGate, v, List.append_assoc]
    rw [hstep1, hstep2]
    obtain ⟨t, htlen, ht1, ht2⟩ :=
      foldl_stepGen_shift d0 f off xs g1 hxs hg1 gs (g2 ++ [v])
    refine ⟨v :: t, by simp [htlen], ?_, ?_⟩
    · rw [ht1]
      simp [List.append_assoc]
    · rw [← shiftGates, ht2]
      simp [List.append_assoc]

lemma evalGen_combine {α : Type} (d0 : α) (f : GateOp → List α → α) (op : GateOp)
    (c1 c2 : Circuit) (xs : List α) (hxs : xs.length = 14)
    (ho1 : c1.output < 14 + c1.gates.length) :
    evalGen d0 f (combine op c1 c2) xs =
      f op [evalGen d0 f c1 xs, evalGen d0 f c2 xs] := by
  unfold evalGen combine
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨g1, hg1len, hg1eq⟩ := foldl_stepGen_append d0 f c1.gates xs
  obtain ⟨g2, hg2len, hg2eq1, hg2eq2⟩ :=
    foldl_stepGen_shift d0 f c1.gates.length xs g1 hxs hg1len c2.gates []
  simp only [List.append_nil] at hg2eq1 hg2eq2
  rw [hg1eq, hg2eq1, hg2eq2]
  unfold stepGen
  simp only [List.map_cons, List.map_nil]
  have hv1 : (xs ++ g1 ++ g2).getD c1.output d0 = (xs ++ g1).getD c1.output d0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [hxs, hg1len]; omega)]
  have hv2 : (xs ++ g1 ++ g2).getD (shiftWire c1.gates.length c2.output) d0 =
      (xs ++ g2).getD c2.output d0 :=
    getD_append_shiftWire d0 c1.gates.length xs g1 g2 hxs hg1len c2.output
  rw [hv1, hv2]
  rw [List.getD_eq_getElem?_getD]
  have hlen : (xs ++ g1 ++ g2).length = 14 + c1.gates.length + c2.gates.length := by
    simp [hxs, hg1len, hg2len]
    omega
  rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  rfl

lemma eval_eq_evalGen (c : Circuit) (xs : List Bool) :
    c.eval xs = evalGen false GateOp.eval c xs := rfl

lemma lineDegree_eq (g : Gate) (d : List ℕ) :
    g.lineDegree d = lineDegOp g.op (g.inputs.map fun i => d.getD i 0) := by
  unfold Gate.lineDegree lineDegOp
  cases g.op <;> rfl

lemma lineDeg_eq_evalGen (c : Circuit) (marked : Finset ℕ) :
    c.lineDeg 14 marked =
      evalGen 0 lineDegOp c ((List.range 14).map fun i => if i ∈ marked then 1 else 0) := by
  unfold Circuit.lineDeg Circuit.lineDegrees evalGen
  have hfn : (fun d g => d ++ [Gate.lineDegree g d]) = stepGen 0 lineDegOp := by
    funext d g
    simp only [stepGen, lineDegree_eq]
  rw [hfn]

lemma compile_spec (f : DMFormula 14) (hf : valid f) :
    IsAO2 14 (compile f) ∧
    (∀ g ∈ (compile f).gates, g.inputs.Nodup) ∧
    (compile f).size + 1 = f.leaves ∧
    (usedGateWires (compile f)).Nodup ∧
    (∀ x : Fin 14 → Bool, (compile f).eval (List.ofFn x) = f.eval x) ∧
    (∀ k : ℕ, (compile f).lineDeg 14 {k} = fDeg k f) := by
  induction f with
  | lit i b =>
    have hb : b = true := hf
    subst hb
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp [compile] at hg
    · intro j hj; simp [compile] at hj
    · intro g hg; simp [compile] at hg
    · intro g hg; simp [compile] at hg
    · rfl
    · simp only [usedGateWires, compile, List.flatMap_nil, List.filter_cons, List.filter_nil]
      have hi : decide (14 ≤ i.val) = false := decide_eq_false (by omega)
      rw [hi]
      exact List.nodup_nil
    · intro x
      simp only [compile, Circuit.eval, Circuit.wires, List.foldl_nil, DMFormula.eval, ite_true]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [i.isLt]
    · intro k
      simp only [compile, Circuit.lineDeg, Circuit.lineDegrees, List.foldl_nil, fDeg]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
      simp
  | and f1 f2 ih1 ih2 =>
    obtain ⟨hv1, hv2, hdiff⟩ := hf
    obtain ⟨⟨hao1, hrb1, hlen1⟩, hnd1, hsz1, hug1, hev1, hld1⟩ := ih1 hv1
    obtain ⟨⟨hao2, hrb2, hlen2⟩, hnd2, hsz2, hug2, hev2, hld2⟩ := ih2 hv2
    have ho1 := compile_output_lt f1
    have ho2 := compile_output_lt f2
    refine ⟨⟨andOrOnly_combine (Or.inl rfl) hao1 hao2,
             readsBack_combine hrb1 hrb2 ho1 ho2,
             len2_combine hlen1 hlen2⟩,
            gateInputs_nodup_combine hnd1 hnd2 (outputs_ne hv1 hv2 hdiff),
            ?_,
            usedGateWires_nodup_combine GateOp.and hrb1 hrb2 ho1 ho2 hug1 hug2,
            ?_, ?_⟩
    · simp only [compile, combine, Circuit.size, shiftGates, List.length_append, List.length_map,
        List.length_singleton, DMFormula.leaves] at hsz1 hsz2 ⊢
      omega
    · intro x
      simp only [compile, eval_eq_evalGen]
      rw [evalGen_combine false GateOp.eval GateOp.and (compile f1) (compile f2)
        (List.ofFn x) (List.length_ofFn) ho1]
      rw [← eval_eq_evalGen, ← eval_eq_evalGen, hev1 x, hev2 x]
      simp [GateOp.eval, DMFormula.eval]
    · intro k
      simp only [compile, lineDeg_eq_evalGen]
      rw [evalGen_combine 0 lineDegOp GateOp.and (compile f1) (compile f2)
        ((List.range 14).map fun i => if i ∈ ({k} : Finset ℕ) then 1 else 0)
        (by simp) ho1]
      rw [← lineDeg_eq_evalGen, ← lineDeg_eq_evalGen, hld1 k, hld2 k]
      simp [lineDegOp, fDeg]
  | or f1 f2 ih1 ih2 =>
    obtain ⟨hv1, hv2, hdiff⟩ := hf
    obtain ⟨⟨hao1, hrb1, hlen1⟩, hnd1, hsz1, hug1, hev1, hld1⟩ := ih1 hv1
    obtain ⟨⟨hao2, hrb2, hlen2⟩, hnd2, hsz2, hug2, hev2, hld2⟩ := ih2 hv2
    have ho1 := compile_output_lt f1
    have ho2 := compile_output_lt f2
    refine ⟨⟨andOrOnly_combine (Or.inr rfl) hao1 hao2,
             readsBack_combine hrb1 hrb2 ho1 ho2,
             len2_combine hlen1 hlen2⟩,
            gateInputs_nodup_combine hnd1 hnd2 (outputs_ne hv1 hv2 hdiff),
            ?_,
            usedGateWires_nodup_combine GateOp.or hrb1 hrb2 ho1 ho2 hug1 hug2,
            ?_, ?_⟩
    · simp only [compile, combine, Circuit.size, shiftGates, List.length_append, List.length_map,
        List.length_singleton, DMFormula.leaves] at hsz1 hsz2 ⊢
      omega
    · intro x
      simp only [compile, eval_eq_evalGen]
      rw [evalGen_combine false GateOp.eval GateOp.or (compile f1) (compile f2)
        (List.ofFn x) (List.length_ofFn) ho1]
      rw [← eval_eq_evalGen, ← eval_eq_evalGen, hev1 x, hev2 x]
      simp [GateOp.eval, DMFormula.eval]
    · intro k
      simp only [compile, lineDeg_eq_evalGen]
      rw [evalGen_combine 0 lineDegOp GateOp.or (compile f1) (compile f2)
        ((List.range 14).map fun i => if i ∈ ({k} : Finset ℕ) then 1 else 0)
        (by simp) ho1]
      rw [← lineDeg_eq_evalGen, ← lineDeg_eq_evalGen, hld1 k, hld2 k]
      simp [lineDegOp, fDeg]

end PEqualNP.Outside.L_meta_5775

theorem PEqualNP.Outside.L_meta_5775 :
    have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x6 ∧ (∀ x7 ∈ x6.gates, x7.inputs.Nodup) ∧ x6.size + (1 : ℕ) = x4.leaves ∧ (List.filter (fun (x7 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x7)) (x6.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x6.gates)).Nodup ∧ (∀ (x7 : Fin (14 : ℕ) → Bool), x6.eval (List.ofFn x7) = x4.eval x7) ∧ ∀ (x7 : ℕ), x6.lineDeg (14 : ℕ) {x7} = x3 x7 x4 := by
  dsimp only
  intro x4 hx4
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := PEqualNP.Outside.L_meta_5775.compile_spec x4 hx4
  refine ⟨PEqualNP.Outside.L_meta_5775.compile x4, h1, h2, h3, h4, h5, ?_⟩
  intro x7
  rw [h6 x7, PEqualNP.Outside.L_meta_5775.fDeg_eq_rec]
