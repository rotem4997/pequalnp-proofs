import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3087

-- Gate deletion and evaluation agreement adapted from the upstream L-meta-522 proof.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))


private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

private lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]


-- The gate-deletion lemmas above are adapted from L_meta_1975.
private def isNeg (g : Gate) : Bool :=
  g.op.eval [false] && !g.op.eval [true]

private def normalizeGate (bound : ℕ) (g : Gate) : Gate :=
  ⟨g.op, (if isNeg g then g.inputs.take 1 else g.inputs).map fun i => min i bound⟩

private def normalize (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (normalizeGate (n+C.size)), min C.output (n+C.size)⟩

private lemma normSize (n : ℕ) (C : Circuit) : (normalize n C).size = C.size := by
  change (C.gates.map _).length = C.gates.length
  rw [List.length_map]

private lemma normFan (n : ℕ) (C : Circuit) (fan : FanInTwo C) :
    FanInTwo (normalize n C) := by
  intro g hg
  change g ∈ C.gates.map (normalizeGate (n+C.size)) at hg
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hg
  refine ⟨(fan original ho).1, ?_⟩
  change ((if isNeg original then original.inputs.take 1 else original.inputs).map _).length ≤ 2
  rw [List.length_map]
  split
  · simp [List.length_take]
  · exact (fan original ho).2

private lemma normArity (n : ℕ) (C : Circuit) {g : Gate} (hg : g ∈ (normalize n C).gates)
    (h : isNeg g = true) : g.inputs.length ≤ 1 := by
  change g ∈ C.gates.map _ at hg
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hg
  change isNeg original = true at h
  simp [normalizeGate, h, List.length_take]

private lemma normBound (n : ℕ) (C : Circuit) :
    (normalize n C).output ≤ n + (normalize n C).size ∧
      ∀ g ∈ (normalize n C).gates, ∀ i ∈ g.inputs, i ≤ n + (normalize n C).size := by
  rw [normSize]
  refine ⟨Nat.min_le_right _ _, ?_⟩
  intro g hg i hi
  change g ∈ C.gates.map (normalizeGate (n+C.size)) at hg
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right _ _

private lemma normEval (n : ℕ) (C : Circuit) (fan : FanInTwo C) :
    circuitFun n (normalize n C) = circuitFun n C := by
  let bound := n + C.size
  have read (w : List Bool) (hlen : w.length ≤ bound) (i : ℕ) :
      w.getD (min i bound) false = w.getD i false := by
    by_cases h : i ≤ bound
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ hlen,
        List.getD_eq_default _ _ (by omega)]
  have equalGate (w : List Bool) (hlen : w.length ≤ bound) (g : Gate)
      (ok : OkGate g) :
      (normalizeGate bound g).op.eval ((normalizeGate bound g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    let short := if isNeg g then g.inputs.take 1 else g.inputs
    change g.op.eval ((short.map (fun i => min i bound)).map (fun i => w.getD i false)) = _
    rw [List.map_map]
    have agreed : short.map (fun i => w.getD (min i bound) false) =
        short.map (fun i => w.getD i false) := List.map_congr_left (fun i _ => read w hlen i)
    change g.op.eval (short.map fun i => w.getD (min i bound) false) = _
    rw [agreed]
    rcases ok.1 with ha | ho | hn
    · have flag : isNeg g = false := by
        change g.op = .and at ha
        unfold isNeg
        rw [ha]
        rfl
      simp [short, flag]
    · have flag : isNeg g = false := by
        change g.op = .or at ho
        unfold isNeg
        rw [ho]
        rfl
      simp [short, flag]
    · change g.op = .not at hn
      have flag : isNeg g = true := by
        unfold isNeg
        rw [hn]
        rfl
      simp only [short, flag, ↓reduceIte, hn]
      cases g.inputs <;> rfl
  have equalRun (gs : List Gate) (ok : ∀ g ∈ gs, OkGate g)
      (w : List Bool) (hlen : w.length + gs.length ≤ bound) :
      wiresFrom (gs.map (normalizeGate bound)) w = wiresFrom gs w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons,
        equalGate w (by simp only [List.length_cons] at hlen; omega) g (ok g List.mem_cons_self)]
      apply ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      simp only [List.length_cons] at hlen
      simp only [List.length_append, List.length_singleton]
      omega
  funext x
  have same := equalRun C.gates fan (List.ofFn x) (by simp [bound, Circuit.size])
  change (wiresFrom (C.gates.map (normalizeGate bound)) (List.ofFn x)).getD
    (min C.output bound) false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
  rw [same]
  exact read _ (by rw [wiresFrom_length]; simp [bound, Circuit.size]) _

private lemma firstInputsUsed {n : ℕ} (D : Circuit)
    (essential : ∀ u : Fin n, ∃ x y : Fin n → Bool, (∀ j ≠ u, x j = y j) ∧
      circuitFun n D x ≠ circuitFun n D y) :
    ∀ i < n, i ∈ D.output :: D.gates.flatMap Gate.inputs := by
  intro i hi
  by_contra ignored
  obtain ⟨x,y,agree,ne⟩ := essential ⟨i,hi⟩
  have hout : D.output ∉ ({i} : Set ℕ) := by
    intro h
    exact ignored (List.mem_cons.mpr (Or.inl (Set.mem_singleton_iff.mp h).symm))
  have hread : ∀ g ∈ D.gates, ∀ j ∈ g.inputs, j ∉ ({i} : Set ℕ) := by
    intro g hg j hj e
    exact ignored (List.mem_cons.mpr (Or.inr
      (List.mem_flatMap.mpr ⟨g,hg,(Set.mem_singleton_iff.mp e) ▸ hj⟩)))
  apply ne
  apply (wiresFrom_agree D.gates ({i} : Set ℕ) (List.ofFn x) (List.ofFn y)
    (by simp) (by simpa using hi) ?_ hread).2 D.output hout
  intro j hj
  by_cases h : j < n
  · rw [ofFn_getD_lt _ _ _ h, ofFn_getD_lt _ _ _ h]
    exact agree _ (fun e => hj (congrArg Fin.val e))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma liveOutputs {n : ℕ} {f : (Fin n → Bool) → Bool} (D : Circuit)
    (fan : FanInTwo D) (hd : circuitFun n D = f)
    (minD : ∀ t, HasCircuitSize n f t → D.size ≤ t) :
    ∀ i < D.gates.length, n+i ∈ D.output :: D.gates.flatMap Gate.inputs := by
  intro i hi
  by_contra ignored
  have hout : D.output ≠ n+i := fun e => ignored (List.mem_cons.mpr (Or.inl e.symm))
  have hno : ∀ j, (hj : j < D.gates.length) → i < j → n+i ∉ D.gates[j].inputs := by
    intro j hj _ h
    exact ignored (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, h⟩))
  have cut := deleteDeadGate D fan i hi hout hno
  have impossible := minD _ (hd ▸ cut)
  change D.gates.length ≤ D.gates.length - 1 at impossible
  omega

private lemma sumCountBound (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

private lemma portBudget (gs : List Gate) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (neg : ∀ g ∈ gs, isNeg g = true → g.inputs.length ≤ 1) :
    (gs.flatMap Gate.inputs).length + (gs.filter isNeg).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have head := fan g List.mem_cons_self
    have tail := ih (fun a ha => fan a (List.mem_cons_of_mem _ ha))
      (fun a ha => neg a (List.mem_cons_of_mem _ ha))
    simp only [List.flatMap_cons, List.length_append, List.filter_cons, List.length_cons]
    by_cases h : isNeg g = true
    · have hlen := neg g List.mem_cons_self h
      simp only [h, ↓reduceIte, List.length_cons]
      omega
    · simp only [h, Bool.false_eq_true, if_false]
      omega

end PEqualNP.Outside.L_meta_3087

open PEqualNP.Outside.L_meta_3087

theorem PEqualNP.Outside.L_meta_3087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := by
  classical
  intro C fan essential
  let f := circuitFun 10 C
  have witness : HasCircuitSize 10 f C.size := ⟨C, fan, le_rfl, fun x => rfl⟩
  have someSize : ∃ s, HasCircuitSize 10 f s := ⟨C.size, witness⟩
  obtain ⟨B, fanB, sizeB, computesB⟩ := Nat.find_spec someSize
  let D := normalize 10 B
  have sameSize : D.size = B.size := normSize _ _
  have fanD : FanInTwo D := normFan 10 B fanB
  have computesD : circuitFun 10 D = f := (normEval 10 B fanB).trans (funext computesB)
  have minD (t : ℕ) (ht : HasCircuitSize 10 f t) : D.size ≤ t := by
    rw [sameSize]
    exact sizeB.trans (Nat.find_min' someSize ht)
  have inputUsed := firstInputsUsed D (by rw [computesD]; exact essential)
  have gateUsed := liveOutputs D fanD computesD minD
  let slots := D.output :: D.gates.flatMap Gate.inputs
  have every (i : ℕ) (hi : i < 10 + D.size) : i ∈ slots := by
    by_cases h : i < 10
    · exact inputUsed i h
    · have hlt : i - 10 < D.gates.length := by
        change i < 10 + D.gates.length at hi
        omega
      have hrew : 10 + (i - 10) = i := by omega
      rw [← hrew]
      exact gateUsed (i - 10) hlt
  refine ⟨D, fanD, computesD, minD _ witness, normBound 10 B, every, ?_⟩
  let range := Finset.range (10+D.size)
  have positive (i : ℕ) (hi : i ∈ range) : 1 ≤ slots.count i :=
    List.count_pos_iff.mpr (every i (Finset.mem_range.mp hi))
  have equality :
      (∑ i ∈ range, ((slots.count i - 1) + 1)) = ∑ i ∈ range, slots.count i :=
    Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (positive i hi))
  rw [Finset.sum_add_distrib] at equality
  simp only [Finset.sum_const, smul_eq_mul, mul_one, range, Finset.card_range] at equality
  have count := sumCountBound slots range
  have ports := portBudget D.gates (fun g hg => (fanD g hg).2) (fun g hg => normArity 10 B hg)
  have hlen : slots.length = (D.gates.flatMap Gate.inputs).length + 1 := rfl
  rw [hlen] at count
  change (D.gates.flatMap Gate.inputs).length + (D.gates.filter isNeg).length ≤ 2 * D.size at ports
  change 9 + (D.gates.filter isNeg).length + (∑ i ∈ range, (slots.count i - 1)) ≤ D.size
  dsimp only [range] at count ⊢
  omega
