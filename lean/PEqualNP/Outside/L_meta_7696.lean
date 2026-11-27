import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7696

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega


lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq_getElem (delDead n k C) j hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq_getElem C j (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq_getElem C (j + 1) (by omega)]


lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega


def evalStep {α : Type} (d0 : α) (evalG : GateOp → List α → α) (acc : List α) (g : Gate) :
    List α :=
  acc ++ [evalG g.op (g.inputs.map fun i => acc.getD i d0)]

lemma foldl_evalStep_length {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) :
    (gs.foldl (evalStep d0 evalG) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_prefix {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl (evalStep d0 evalG) acc).getD w d0 = acc.getD w d0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (evalStep d0 evalG acc g).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (evalStep d0 evalG acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_left hw]

lemma foldl_evalStep_gate {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG (gateAt C j).op
        ((gateAt C j).inputs.map fun u => (C.gates.foldl (evalStep d0 evalG) init).getD u d0) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (evalStep d0 evalG) init with hacc
  have hacc_len : acc.length = n + j := by
    rw [hacc, foldl_evalStep_length, hinit, List.length_take]
    omega
  have hpref : ∀ u < n + j,
      (C.gates.foldl (evalStep d0 evalG) init).getD u d0 = acc.getD u d0 := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_evalStep_prefix d0 evalG (C.gates.drop j) acc u (by omega)
  have hval : (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG C.gates[j].op (C.gates[j].inputs.map fun u => acc.getD u d0) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + j < (evalStep d0 evalG acc C.gates[j]).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_evalStep_prefix d0 evalG (C.gates.drop (j + 1)) (evalStep d0 evalG acc C.gates[j])
      (n + j) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_right (by omega : acc.length ≤ n + j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C j hj] at hu
  exact (hpref u (hRB j hj u hu)).symm

lemma delDead_evalStep_eq {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n k : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ w : ℕ,
      ((delDead n k C).gates.foldl (evalStep d0 evalG) init).getD w d0 =
        (C.gates.foldl (evalStep d0 evalG) init).getD (unshiftW n k w) d0 := by
  have hRB' : ReadsBack n (delDead n k C) := delDead_readsBack n k C hRB hk hno
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_oob : n + (delDead n k C).gates.length ≤ w
    · have hlen' : ((delDead n k C).gates.foldl (evalStep d0 evalG) init).length =
          n + (delDead n k C).gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hlen : (C.gates.foldl (evalStep d0 evalG) init).length = n + C.gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hdl := delDead_length n k C hk
      have huw : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hw_oob
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw]
        rw [foldl_evalStep_prefix d0 evalG (delDead n k C).gates init w (by omega)]
        rw [foldl_evalStep_prefix d0 evalG C.gates init w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (delDead n k C).gates.length := by omega
        have hdl := delDead_length n k C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [foldl_evalStep_gate d0 evalG n (delDead n k C) init hinit hRB' j hj_lt]
        rw [foldl_evalStep_gate d0 evalG n C init hinit hRB (unshiftG k j) hj0_lt]
        rw [delDead_gateAt n k C hk j hj_lt]
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : shiftW n k u < n + j := by
          have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
            rw [delDead_gateAt n k C hk j hj_lt]
            simp only [shiftGate, List.mem_map]
            exact ⟨u, hu, rfl⟩
          exact hRB' j hj_lt (shiftW n k u) hmem
        have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
        simp only [Function.comp_apply]
        rw [ih (shiftW n k u) (by omega), unshiftW_shiftW n k u hu_ne]

lemma delDead_wires_eq (n k : ℕ) (C : Circuit) (l : List Bool) (hl : l.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (w : ℕ) :
    ((delDead n k C).wires l).getD w false = (C.wires l).getD (unshiftW n k w) false :=
  delDead_evalStep_eq false GateOp.eval n k C l hl hRB hk hno w


lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]


lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ m < j, (cones n C).getD m [] = acc.getD m [] := by
    intro m hm
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc m (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi


private lemma delDead_ao2 {n k : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    IsAO2 n (delDead n k C) := by
  have mapped : ∀ g ∈ (delDead n k C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hm := List.mem_of_mem_eraseIdx hg'
    exact ⟨h.1 g' hm, by simp [shiftGate, h.2.2 g' hm]⟩
  exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack n k C h.2.1 hk hno,
    fun g hg => (mapped g hg).2⟩

private def IsSmallest (n : ℕ) (C : Circuit) : Prop :=
  ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size

private lemma reader {n k : ℕ} {C : Circuit} (h : IsAO2 n C) (hmin : IsSmallest n C)
    (hk : k < C.gates.length) (hout : C.output ≠ n + k) :
    ∃ j < C.gates.length, n + k ∈ (gateAt C j).inputs := by
  by_contra hnot
  have hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs :=
    fun j hj hj' => hnot ⟨j, hj, hj'⟩
  have heq : circuitFun n (delDead n k C) = circuitFun n C := by
    funext x
    unfold circuitFun Circuit.eval
    rw [delDead_wires_eq n k C _ List.length_ofFn h.2.1 hk hno]
    change (C.wires (List.ofFn x)).getD (unshiftW n k (shiftW n k C.output)) false = _
    rw [unshiftW_shiftW n k C.output hout]
  have hle := hmin _ (delDead_ao2 h hk hno) heq
  have hsize := delDead_size n k C hk
  omega

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma inputValue {n w : ℕ} (C : Circuit) (x : Fin n → Bool) (hw : w < n) :
    value C x w = x ⟨w, hw⟩ := by
  change (C.gates.foldl (evalStep false GateOp.eval) (List.ofFn x)).getD w false = _
  rw [foldl_evalStep_prefix false GateOp.eval C.gates (List.ofFn x) w (by simpa using hw)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hw)]
  simp

private lemma gateValue {n j : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    value C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) :=
  foldl_evalStep_gate false GateOp.eval n C _ List.length_ofFn h.2.1 j hj

private lemma gateMem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C j hj]
  exact List.getElem_mem _

private lemma andOr {n j : ℕ} {C : Circuit} (h : IsAO2 n C) (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
  h.1 _ (gateMem hj)

private lemma operands {n j : ℕ} {C : Circuit} (h : IsAO2 n C) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] := by
  have hlen := h.2.2 _ (gateMem hj)
  exact ⟨_, _, List.eq_getElem_of_length_eq_two _ hlen⟩

private lemma noAndPair {n i j : ℕ} {C : Circuit} (hz : andPairs n C = 0)
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hai : (gateAt C i).op = GateOp.and) (haj : (gateAt C j).op = GateOp.and) :
    ¬ InCone n C i j := by
  intro hc
  let gateOpEq : DecidableEq GateOp := gateOpDecEq
  unfold andPairs at hz
  have hm : (i, j) ∈ ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun (p : ℕ × ℕ) =>
    (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    simp [hi, hj, hai, haj, hc]
  rw [Finset.card_eq_zero.mp hz] at hm
  exact Finset.notMem_empty _ hm

private lemma coneThrough {n i j k : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hk : k < C.gates.length) (hu : n + j ∈ (gateAt C k).inputs)
    (hc : i = j ∨ InCone n C i j) : InCone n C i k := by
  apply (inCone_iff n C i k hk).mpr
  refine ⟨n + j, hu, by omega, h.2.1 k hk _ hu, ?_⟩
  simpa using hc

-- A maximal true gate reached from the AND gate must be the output.
private lemma andBelowOutput {n i : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hmin : IsSmallest n C) (hz : andPairs n C = 0) (hi : i < C.gates.length)
    (hop : (gateAt C i).op = GateOp.and) (x : Fin n → Bool)
    (hv : value C x (n + i) = true) : circuitFun n C x = true := by
  classical
  let S := (Finset.range C.gates.length).filter fun j =>
    (i = j ∨ InCone n C i j) ∧ value C x (n + j) = true
  have hm : ∀ j, j ∈ S ↔ j < C.gates.length ∧
      (i = j ∨ InCone n C i j) ∧ value C x (n + j) = true := by
    intro j
    simp [S]
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image id ⟨i, (hm i).mpr ⟨hi, Or.inl rfl, hv⟩⟩
  obtain ⟨hj', hjc, hjv⟩ := (hm j).mp hj
  by_cases hout : C.output = n + j
  · change value C x C.output = true
    rwa [hout]
  obtain ⟨k, hk, hread⟩ := reader h hmin hj' hout
  have hcone := coneThrough h hk hread hjc
  have hkor : (gateAt C k).op = GateOp.or :=
    (andOr h hk).resolve_left fun ha => noAndPair hz hi hk hop ha hcone
  have hkv : value C x (n + k) = true := by
    rw [gateValue h hk x, hkor]
    change ((gateAt C k).inputs.map (value C x)).any id = true
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨n + j, hread, hjv⟩, rfl⟩
  have hle : k ≤ j := hmax k ((hm k).mpr ⟨hk, Or.inr hcone, hkv⟩)
  have hlt := h.2.1 k hk _ hread
  omega

private def PureOR (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  w < n ∨ ∃ j < C.gates.length, w = n + j ∧
    (gateAt C j).op = GateOp.or ∧
    ∀ i < C.gates.length, InCone n C i j → (gateAt C i).op ≠ GateOp.and

private lemma pureOperand {n j w : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hclean : ∀ i < C.gates.length, InCone n C i j → (gateAt C i).op ≠ GateOp.and) :
    PureOR n C w := by
  by_cases hin : w < n
  · exact Or.inl hin
  have hwlt := h.2.1 j hj w hw
  let k := w - n
  have heq : w = n + k := by dsimp [k]; omega
  have hk : k < C.gates.length := by omega
  rw [heq] at hw
  refine Or.inr ⟨k, hk, heq, (andOr h hk).resolve_left (hclean k hk
    (coneThrough h hj hw (Or.inl rfl))), ?_⟩
  intro i hi hc
  exact hclean i hi (coneThrough h hj hw (Or.inr hc))

private def sideInput (n cut : ℕ) (b : Bool) (i : Fin n) : Bool :=
  if b then decide (cut ≤ (i : ℕ)) else decide ((i : ℕ) < cut)

private lemma sideAtInput {n w cut : ℕ} (hw : w < n) (b : Bool) :
    sideInput n cut b (⟨w, hw⟩ : Fin n) = true ↔ decide (cut ≤ w) = b := by
  cases b <;> by_cases h : cut ≤ w <;> simp [sideInput, h, Nat.not_lt.mpr]
  omega

private lemma someSide {n w : ℕ} {C : Circuit} (cut : ℕ) (h : IsAO2 n C)
    (hp : PureOR n C w) : ∃ b, value C (sideInput n cut b) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hp with hw | ⟨j, hj, rfl, hop, hc⟩
    · refine ⟨decide (cut ≤ w), ?_⟩
      rw [inputValue C _ hw, sideAtInput]
    · obtain ⟨a, b, hab⟩ := operands h hj
      have ha : a ∈ (gateAt C j).inputs := by simp [hab]
      obtain ⟨s, hs⟩ := ih a (h.2.1 j hj a ha) (pureOperand h hj ha hc)
      refine ⟨s, ?_⟩
      rw [gateValue h hj, hop, hab]
      simp [GateOp.eval, hs]

-- A pure OR wire belongs to a side when it is false on the opposite side input.
private noncomputable def sideWires (n cut : ℕ) (C : Circuit) (b : Bool) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter fun w =>
    PureOR n C w ∧ value C (sideInput n cut !b) w = false

private lemma memSideWires {n cut w : ℕ} {C : Circuit} {b : Bool} :
    w ∈ sideWires n cut C b ↔ PureOR n C w ∧ value C (sideInput n cut !b) w = false := by
  classical
  simp only [sideWires, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun hw => hw.2, fun hw => ⟨?_, hw⟩⟩
  rcases hw.1 with hi | ⟨j, hj, hEq, _, _⟩ <;> omega

private lemma sideClosed {n cut w : ℕ} {C : Circuit} (h : IsAO2 n C) (b : Bool)
    (hw : w ∈ sideWires n cut C b) :
    w < n ∧ decide (cut ≤ w) = b ∨
    ∃ j < C.gates.length, w = n + j ∧ (gateAt C j).op = GateOp.or ∧
      ∀ u ∈ (gateAt C j).inputs, u ∈ sideWires n cut C b := by
  obtain ⟨hp, hv⟩ := memSideWires.mp hw
  rcases hp with hi | ⟨j, hj, rfl, hop, hc⟩
  · left
    refine ⟨hi, ?_⟩
    rw [inputValue C _ hi] at hv
    have hs : decide (cut ≤ w) ≠ !b := by
      intro he
      have := (sideAtInput hi (!b)).mpr he
      rw [hv] at this
      contradiction
    cases hcut : decide (cut ≤ w) <;> cases b <;> simp_all
  · right
    refine ⟨j, hj, rfl, hop, fun u hu => memSideWires.mpr ⟨pureOperand h hj hu hc, ?_⟩⟩
    rw [gateValue h hj, hop] at hv
    cases hval : value C (sideInput n cut !b) u
    · rfl
    · have ht : ((gateAt C j).inputs.map (value C (sideInput n cut !b))).any id = true :=
        List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨u, hu, hval⟩, rfl⟩
      change ((gateAt C j).inputs.map (value C (sideInput n cut !b))).any id = false at hv
      rw [hv] at ht
      contradiction

private lemma oppositeSides {n cut a b : ℕ} {C : Circuit} (h : IsAO2 n C)
    (ha : PureOR n C a) (hb : PureOR n C b)
    (hf : ∀ s : Bool, value C (sideInput n cut s) a = false ∨
      value C (sideInput n cut s) b = false) :
    ∃ s : Bool, a ∈ sideWires n cut C s ∧ b ∈ sideWires n cut C !s := by
  obtain ⟨s, hs⟩ := someSide cut h ha
  have hbfalse := (hf s).resolve_left (by rw [hs]; decide)
  obtain ⟨t, ht⟩ := someSide cut h hb
  have htne : t ≠ s := by
    rintro rfl
    rw [hbfalse] at ht
    contradiction
  have hteq : t = !s := by cases s <;> cases t <;> simp_all
  have hafalse := (hf t).resolve_right (by rw [ht]; decide)
  rw [hteq] at hafalse
  refine ⟨s, memSideWires.mpr ⟨ha, hafalse⟩, memSideWires.mpr ⟨hb, ?_⟩⟩
  simpa using hbfalse

private theorem solve :
    ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.MetaComplexity.circuitFun (x1 + x2) x3 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (x1 + x2) x3 = (0 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x3 fun (x7 : Fin (x1 + x2)) => Decidable.decide (↑x7 < x1)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x3 fun (x8 : Fin (x1 + x2)) => Decidable.decide (x1 ≤ ↑x8)) = Bool.false → ∃ (x9 : Bool → Finset ℕ), (∀ (x10 : Bool), ∀ x11 ∈ x9 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x3.size, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).inputs, x14 ∈ x9 x10) ∧ ∀ x10 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).inputs = [x13, x14] ∧ x13 ∈ x9 x15 ∧ x14 ∈ x9 !x15 := by
  intro x1 x2 x3 h hmin hz hleft hright
  refine ⟨sideWires (x1 + x2) x1 x3, fun b w hw => sideClosed h b hw, ?_⟩
  intro j hj hop
  have hclean : ∀ i < x3.gates.length, InCone (x1 + x2) x3 i j →
      (gateAt x3 i).op ≠ GateOp.and :=
    fun i hi hc ha => noAndPair hz hi hj ha hop hc
  obtain ⟨a, b, hab⟩ := operands h hj
  have ha := pureOperand h hj (show a ∈ _ from by simp [hab]) hclean
  have hb := pureOperand h hj (show b ∈ _ from by simp [hab]) hclean
  have hf (s : Bool) : value x3 (sideInput (x1 + x2) x1 s) a = false ∨
      value x3 (sideInput (x1 + x2) x1 s) b = false := by
    by_contra hh
    push Not at hh
    have hv : value x3 (sideInput (x1 + x2) x1 s) (x1 + x2 + j) = true := by
      rw [gateValue h hj, hop, hab]
      simpa [GateOp.eval] using hh
    have htrue := andBelowOutput h hmin hz hj hop (sideInput (x1 + x2) x1 s) hv
    cases s
    · exact Bool.false_ne_true (hleft.symm.trans htrue)
    · exact Bool.false_ne_true (hright.symm.trans htrue)
  obtain ⟨s, hs, ht⟩ := oppositeSides h ha hb hf
  exact ⟨a, b, s, hab, hs, ht⟩

end PEqualNP.Outside.L_meta_7696

theorem PEqualNP.Outside.L_meta_7696 :
    ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.MetaComplexity.circuitFun (x1 + x2) x3 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (x1 + x2) x3 = (0 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x3 fun (x7 : Fin (x1 + x2)) => Decidable.decide (↑x7 < x1)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x3 fun (x8 : Fin (x1 + x2)) => Decidable.decide (x1 ≤ ↑x8)) = Bool.false → ∃ (x9 : Bool → Finset ℕ), (∀ (x10 : Bool), ∀ x11 ∈ x9 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x3.size, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).inputs, x14 ∈ x9 x10) ∧ ∀ x10 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).inputs = [x13, x14] ∧ x13 ∈ x9 x15 ∧ x14 ∈ x9 !x15 :=
  PEqualNP.Outside.L_meta_7696.solve
