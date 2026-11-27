import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9425

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wval_input C _ w hwn]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq]
      have hop := hAO.1 _ (gateAt_mem hj)
      have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
      have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
      have hv0 := ih _ h0 (by omega)
      have hv1 := ih _ h1 (by omega)
      rcases hop with hand | hor
      · rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, ite_eq_left hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, ite_eq_left hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_wval_not_inCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ∀ w < n + C.gates.length, w ≠ n + j → (n ≤ w → ¬ InCone n C j (w - n)) →
      wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj hnc
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · have hnc' : ¬ InCone n C j (w - n) := hnc (by omega)
      have hop_ok : ∀ b : Fin 2, opnd C (w - n) b ≠ n + j ∧
          (n ≤ opnd C (w - n) b → ¬ InCone n C j (opnd C (w - n) b - n)) := by
        intro b
        have hk : w - n < C.gates.length := by omega
        have hmem := opnd_mem hAO hk b
        have hlt := opnd_lt hAO hk b
        constructor
        · intro heq; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, by omega, hlt, Or.inl (by omega)⟩
        · intro hnu hin; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, hnu, hlt, Or.inr hin⟩
      by_cases hlt : w < n + j
      · have hk : w - n < j := by omega
        have hdw : delWire n j r w = n + (w - n) := by
          unfold delWire; rw [ite_eq_right hwj, ite_eq_right (by omega)]; omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
        rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
        have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (hop_ok 0).1 (hop_ok 0).2
        have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (hop_ok 1).1 (hop_ok 1).2
        rw [h0, h1, hg]
      · have hgt : n + j < w := by omega
        have hk : w - n - 1 < C.gates.length - 1 := by omega
        have hjk : j ≤ w - n - 1 := by omega
        have hdw : delWire n j r w = n + (w - n - 1) := by
          unfold delWire; rw [ite_eq_right hwj, ite_eq_left hgt]; omega
        have hw_eq : w = n + (w - n - 1 + 1) := by omega
        have hidx : w - n = w - n - 1 + 1 := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
        rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
        have h0 := ih (opnd C (w - n - 1 + 1) 0)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by rw [← hidx]; exact (hop_ok 0).1) (by rw [← hidx]; exact (hop_ok 0).2)
        have h1 := ih (opnd C (w - n - 1 + 1) 1)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by rw [← hidx]; exact (hop_ok 1).1) (by rw [← hidx]; exact (hop_ok 1).2)
        rw [h0, h1, hg]


lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩


lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  obtain ⟨u, v, huv⟩ := hne
  have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
    rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
    simp at h1
  · by_contra hge
    push Not at hge
    have h1 := hfun (pairInput u v)
    rw [wval_ge_len C _ hge, (graphFun_pair_iff u v).mpr huv] at h1
    cases h1

lemma least_inOutputCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    ∀ j < C.gates.length, InOutputCone n C j := by
  have ⟨u, _, _⟩ := hne
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hout := output_bounds hL hne
  intro j hj
  refine ⟨hj, ?_⟩
  by_contra hnot
  push Not at hnot
  have hr : 0 < n + j := by omega
  let C' := delCircuit n C j 0
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_not_inCone hL.1 x hj hr C.output hout.2 hnot.1 (fun _ => hnot.2 hout.1)
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj 0] at hsz
  omega

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma orT_opnds_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) {h : ℕ} (hh : h < C.gates.length)
    (hor : (gateAt C h).op = GateOp.or) (hb : BelowF G C h) (b : Fin 2) :
    n ≤ opnd C h b ∧ opnd C h b - n < C.gates.length ∧ BelowF G C (opnd C h b - n) := by
  have hwb : ∀ x, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
    intro x hwx
    apply hb x
    rw [gateVal_eq_wval, wval_gate_or hL.1 x hh hor, Bool.or_eq_true]
    fin_cases b
    · exact Or.inl hwx
    · exact Or.inr hwx
  have hge : n ≤ opnd C h b := by
    by_contra hlt; push Not at hlt; exact input_not_belowF hlt hwb
  have hlt : opnd C h b < n + h := opnd_lt hL.1 hh b
  refine ⟨hge, by omega, ?_⟩
  intro x hx
  apply hwb x
  rw [gateVal_eq_wval] at hx
  rwa [show n + (opnd C h b - n) = opnd C h b by omega] at hx

lemma mem_tops_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ tops G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ BelowF G C k := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold tops gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orT_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orT G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ BelowF G C k := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orT gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orN_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orN G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ ¬ BelowF G C k := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orN gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_junk_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty BelowF
  constructor
  · rintro ⟨hk, hand, _, x, hgx, hfx⟩
    refine ⟨hk, hand, fun hb => ?_⟩
    have := hb x hgx; rw [hfx] at this; cases this
  · rintro ⟨hk, hand, hnb⟩
    push Not at hnb
    rcases hnb with ⟨x, hgx, hfx⟩
    refine ⟨hk, hand, hk, x, hgx, ?_⟩
    cases h : graphFun G ∅ x
    · rfl
    · exact absurd h hfx

lemma output_gate_mem_tops_or_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    C.output - n ∈ tops G C ∪ orT G C := by
  have hout := output_bounds hL hne
  have hk : C.output - n < C.gates.length := by omega
  have hb : BelowF G C (C.output - n) := by
    intro x hx
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega] at hx
    rw [← congrFun hL.2.1 x]; exact hx
  rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
  rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
  · exact Or.inl ⟨hk, hand, hb⟩
  · exact Or.inr ⟨hk, hor, hb⟩

lemma circuit_size_partition {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) :
    C.size = (tops G C).card + (orT G C).card + (junk G C).card + (orN G C).card := by
  have hU : Finset.range C.gates.length = tops G C ∪ orT G C ∪ junk G C ∪ orN G C := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, mem_tops_iff, mem_orT_iff, mem_junk_iff, mem_orN_iff]
    constructor
    · intro hk
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inl ⟨hk, hand, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, hand, hb⟩)
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inr ⟨hk, hor, hb⟩))
        · exact Or.inr ⟨hk, hor, hb⟩
    · rintro (((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk
  have hd1 : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_tops_iff] at h1; rw [mem_orT_iff] at h2; rw [h1.2.1] at h2; cases h2.2.1
  have hd2 : Disjoint (tops G C ∪ orT G C) (junk G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_junk_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff] at h1
    rcases h1 with h1 | h1 <;> exact h2.2.2 h1.2.2
  have hd3 : Disjoint (tops G C ∪ orT G C ∪ junk G C) (orN G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_orN_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff, mem_junk_iff] at h1
    rcases h1 with (h1 | h1) | h1
    · exact h2.2.2 h1.2.2
    · exact h2.2.2 h1.2.2
    · rw [h1.2.1] at h2; cases h2.2.1
  change C.gates.length = _
  rw [← Finset.card_range C.gates.length, hU,
    Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1]

lemma circuitFun_iff_exists_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) (x : Fin n → Bool) :
    circuitFun n C x = true ↔ ∃ a ∈ tops G C, gateVal n C a x = true := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  constructor
  · intro hcx
    have hkey : ∀ k, k ∈ tops G C ∪ orT G C → gateVal n C k x = true →
        ∃ a ∈ tops G C, gateVal n C a x = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hvk
        rw [Finset.mem_union] at hk
        rcases hk with htop | horT
        · exact ⟨k, htop, hvk⟩
        · rw [mem_orT_iff] at horT
          rw [gateVal_eq_wval, wval_gate_or hL.1 x horT.1 horT.2.1, Bool.or_eq_true] at hvk
          rcases hvk with h0 | h1
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 0
            have hlt_k : opnd C k 0 - n < k := by have := opnd_lt hL.1 horT.1 0; omega
            have hmem : opnd C k 0 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 0 - n) = opnd C k 0 by omega]; exact h0)
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 1
            have hlt_k : opnd C k 1 - n < k := by have := opnd_lt hL.1 horT.1 1; omega
            have hmem : opnd C k 1 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 1 - n) = opnd C k 1 by omega]; exact h1)
    apply hkey (C.output - n) hout_mem
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega]
    exact hcx
  · rintro ⟨a, ha, hva⟩
    rw [mem_tops_iff] at ha
    rw [congrFun hL.2.1 x]
    exact ha.2.2 x hva


lemma operand_iff {n : ℕ} {C : Circuit} (hao : IsAO2 n C)
    {j k : ℕ} (hj : j < C.gates.length) :
    InCone n C k j ↔ ∃ b : Fin 2,
      n ≤ opnd C j b ∧ (k = opnd C j b - n ∨ InCone n C k (opnd C j b - n)) := by
  rw [inCone_iff hj, gate_inputs_eq hao hj]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨w, rfl | rfl, hge, _, hk⟩
    · exact ⟨0, hge, hk⟩
    · exact ⟨1, hge, hk⟩
  · rintro ⟨b, hge, hk⟩
    have hlt := opnd_lt hao hj b
    fin_cases b
    · exact ⟨_, Or.inl rfl, hge, hlt, hk⟩
    · exact ⟨_, Or.inr rfl, hge, hlt, hk⟩

lemma below_has_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) (hb : BelowF G C j) :
    ∃ t ∈ tops G C, t = j ∨ InCone n C t j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rcases hL.1.1 _ (gateAt_mem hj) with ha | ho
    · exact ⟨j, mem_tops_iff.mpr ⟨hj, ha, hb⟩, Or.inl rfl⟩
    · obtain ⟨hge, hlt, hb'⟩ := orT_opnds_belowF hL hj ho hb 0
      have hback := opnd_lt hL.1 hj 0
      obtain ⟨t, ht, hc⟩ := ih _ (by omega) hlt hb'
      exact ⟨t, ht, Or.inr ((operand_iff hL.1 hj).mpr ⟨0, hge, hc⟩)⟩

lemma below_avoids_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C)
    {i j : ℕ} (hj : j < C.gates.length) (ha : (gateAt C j).op = GateOp.and)
    (hc : InCone n C i j) : ¬ BelowF G C i := by
  intro hb
  obtain ⟨t, ht, hti⟩ := below_has_top hL i (by have := inCone_lt hc; omega) hb
  have hd := mem_tops_iff.mp ht
  apply hT t hd.1 j hj hd.2.1 hd.2.2 ha
  rcases hti with rfl | hti
  · exact hc
  · exact inCone_trans hti hc

lemma below_reader {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C)
    {k j : ℕ} (hc : InCone n C k j) (hk : BelowF G C k) (hb : BelowF G C j) :
    ∃ m ∈ orT G C, ∃ b : Fin 2, opnd C m b = n + k := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len hc
    have ho : (gateAt C j).op = GateOp.or := by
      rcases hL.1.1 _ (gateAt_mem hj) with ha | ho
      · exact False.elim (below_avoids_and hL hT hj ha hc hk)
      · exact ho
    obtain ⟨b, hge, heq | hcone⟩ := (operand_iff hL.1 hj).mp hc
    · exact ⟨j, mem_orT_iff.mpr ⟨hj, ho, hb⟩, b, by omega⟩
    · have hback := opnd_lt hL.1 hj b
      exact ih _ (by omega) hcone (orT_opnds_belowF hL hj ho hb b).2.2

lemma tops_le_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    (tops G C).card ≤ (orT G C).card + 1 := by
  classical
  have hout := output_bounds hL hne
  have hm := output_gate_mem_tops_or_orT hL hne
  have houtb : BelowF G C (C.output - n) := by
    intro x hx
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega] at hx
    exact (congrFun hL.2.1 x).symm ▸ hx
  have hd : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]
    intro k hk ht
    have ha := (mem_tops_iff.mp hk).2.1
    have ho := (mem_orT_iff.mp ht).2.1
    rw [ha] at ho
    cases ho
  let S := ((tops G C ∪ orT G C).erase (C.output - n)).image (fun k => n + k)
  let U := (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => opnd C p.1 p.2)
  have hsub : S ⊆ U := by
    intro w hw
    obtain ⟨k, hkin, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hko, hmem⟩ := Finset.mem_erase.mp hkin
    have hkb : k < C.gates.length ∧ BelowF G C k := by
      rcases Finset.mem_union.mp hmem with ht | hr
      · exact ⟨(mem_tops_iff.mp ht).1, (mem_tops_iff.mp ht).2.2⟩
      · exact ⟨(mem_orT_iff.mp hr).1, (mem_orT_iff.mp hr).2.2⟩
    have hc : InCone n C k (C.output - n) := by
      rcases (least_inOutputCone hL hne k hkb.1).2 with heq | ⟨_, hc⟩
      · exact False.elim (hko (by omega))
      · exact hc
    obtain ⟨m, hmo, b, hb⟩ := below_reader hL hT hc hkb.2 houtb
    exact Finset.mem_image.mpr ⟨(m, b), Finset.mem_product.mpr ⟨hmo, Finset.mem_univ _⟩, hb⟩
  have hcardS : S.card = (tops G C).card + (orT G C).card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_erase_of_mem hm, Finset.card_union_of_disjoint hd]
  have hcardU : U.card ≤ (orT G C).card * 2 := by
    calc
      U.card ≤ (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_image_le
      _ = (orT G C).card * 2 := by simp
  have hc := Finset.card_le_card hsub
  omega


def touches (n : ℕ) (C : Circuit) (w j : ℕ) : Prop :=
  n ≤ w ∧ (j = w - n ∨ InCone n C j (w - n))

def sample {n : ℕ} (X : Fin n → Finset ℕ) (f : (Fin n → Bool) → Bool) : Finset ℕ :=
  {k ∈ Finset.range 40 | f (fun i => decide (k ∈ X i)) = true}

noncomputable def tagged {n : ℕ} (C : Circuit) (X : Fin n → Finset ℕ) (p q w : ℕ) : Finset ℕ := by
  classical
  exact sample X (fun x => wval C x w) ∪
    (if touches n C w p then {40} else ∅) ∪ (if touches n C w q then {41} else ∅)

def join (A B : Finset ℕ) : Finset ℕ :=
  A ∩ B ∩ Finset.range 40 ∪ (if {(40 : ℕ), 41} ⊆ A ∪ B then {40} else ∅)

lemma mem_mark (P : Prop) [Decidable P] (m k : ℕ) :
    k ∈ (if P then ({m} : Finset ℕ) else ∅) ↔ k = m ∧ P := by
  by_cases h : P <;> simp [h]

lemma mem_tagged {n : ℕ} (C : Circuit) (X : Fin n → Finset ℕ) (p q w k : ℕ) :
    k ∈ tagged C X p q w ↔
      k ∈ sample X (fun x => wval C x w) ∨
      (k = 40 ∧ touches n C w p) ∨ (k = 41 ∧ touches n C w q) := by
  classical
  unfold tagged
  simp only [Finset.mem_union, mem_mark, or_assoc]

lemma tagged_input {n : ℕ} (C : Circuit) (X : Fin n → Finset ℕ)
    (hX : ∀ i, X i ⊆ Finset.range 40) (p q w : ℕ) (hw : w < n) :
    tagged C X p q w = X ⟨w, hw⟩ := by
  ext k
  rw [mem_tagged]
  have hnp : ¬ touches n C w p := fun h => by have := h.1; omega
  have hnq : ¬ touches n C w q := fun h => by have := h.1; omega
  simp only [hnp, hnq, and_false, or_false, sample, Finset.mem_filter, wval_input C _ w hw,
    decide_eq_true_eq]
  exact ⟨And.right, fun hk => ⟨hX _ hk, hk⟩⟩

lemma tagged_plain {n : ℕ} (C : Circuit) (X : Fin n → Finset ℕ) {p q w : ℕ}
    (hp : ¬ touches n C w p) (hq : ¬ touches n C w q) :
    tagged C X p q w = sample X (fun x => wval C x w) := by
  ext k
  simp [mem_tagged, hp, hq]

lemma tagged_junk {n : ℕ} (C : Circuit) (X : Fin n → Finset ℕ)
    {p q : ℕ} (hpq : p < q) (hc : ¬ InCone n C p q) :
    tagged C X p q (n + p) = insert 40 (sample X (gateVal n C p)) ∧
    tagged C X p q (n + q) = insert 41 (sample X (gateVal n C q)) := by
  have hge (j : ℕ) : n ≤ n + j := by omega
  have hpne : p ≠ q := by omega
  have hqne : q ≠ p := by omega
  have hrev : ¬ InCone n C q p := fun h => by have := inCone_lt h; omega
  constructor <;> ext k
  · simp only [mem_tagged, touches, hge, Nat.add_sub_cancel_left, true_or, hqne,
      hrev, or_self, and_false, or_false, and_true, Finset.mem_insert]
    exact or_comm
  · simp only [mem_tagged, touches, hge, Nat.add_sub_cancel_left, true_or, hpne,
      hc, or_self, and_false, false_or, and_true, Finset.mem_insert]
    exact or_comm

lemma touches_iff {n : ℕ} {C : Circuit} (hao : IsAO2 n C) {j k : ℕ}
    (hj : j < C.gates.length) :
    InCone n C k j ↔ touches n C (opnd C j 0) k ∨ touches n C (opnd C j 1) k := by
  rw [operand_iff hao hj]
  exact ⟨fun ⟨b, hb⟩ => by fin_cases b; exact Or.inl hb; exact Or.inr hb,
    fun h => h.elim (fun h0 => ⟨0, h0⟩) (fun h1 => ⟨1, h1⟩)⟩

lemma tagged_or {n : ℕ} {C : Circuit} (X : Fin n → Finset ℕ) (hao : IsAO2 n C)
    {j p q : ℕ} (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or)
    (hp : j ≠ p) (hq : j ≠ q) :
    tagged C X p q (n + j) =
      tagged C X p q (opnd C j 0) ∪ tagged C X p q (opnd C j 1) := by
  have ht (k : ℕ) (hk : k ≠ j) : touches n C (n + j) k ↔ InCone n C k j := by
    simp [touches, show n ≤ n + j by omega, hk]
  ext k
  simp only [Finset.mem_union, mem_tagged, ht p hp.symm, ht q hq.symm, touches_iff hao hj,
    sample, Finset.mem_filter, wval_gate_or hao _ hj ho, Bool.or_eq_true]
  tauto

lemma mem_join {k : ℕ} {A B : Finset ℕ} :
    k ∈ join A B ↔ (k ∈ A ∧ k ∈ B ∧ k < 40) ∨
      (k = 40 ∧ (40 ∈ A ∨ 40 ∈ B) ∧ (41 ∈ A ∨ 41 ∈ B)) := by
  unfold join
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_range, mem_mark,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]
  tauto

lemma real_in_tagged {n : ℕ} {C : Circuit} {X : Fin n → Finset ℕ} {p q w k : ℕ}
    (hk : k < 40) :
    k ∈ tagged C X p q w ↔ wval C (fun i => decide (k ∈ X i)) w = true := by
  simp [mem_tagged, sample, hk, show k ≠ 40 by omega, show k ≠ 41 by omega]

lemma mark40_in_tagged {n : ℕ} {C : Circuit} {X : Fin n → Finset ℕ} {p q w : ℕ} :
    40 ∈ tagged C X p q w ↔ touches n C w p := by
  simp [mem_tagged, sample]

lemma mark41_in_tagged {n : ℕ} {C : Circuit} {X : Fin n → Finset ℕ} {p q w : ℕ} :
    41 ∈ tagged C X p q w ↔ touches n C w q := by
  simp [mem_tagged, sample]

noncomputable def relevant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset ℕ := by
  classical
  exact (orN G C).filter fun j =>
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ InCone n C j a

def goodWire (n p q : ℕ) (W : Finset ℕ) (w : ℕ) : Prop :=
  w < n ∨ w = n + p ∨ w = n + q ∨ ∃ j ∈ W, w = n + j

lemma operands_good {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {p q j : ℕ} (hjunk : junk G C = {p, q})
    (hj : j < C.gates.length)
    (hparent : (gateAt C j).op = GateOp.and ∨ j ∈ relevant G C) (b : Fin 2) :
    goodWire n p q (relevant G C) (opnd C j b) := by
  classical
  by_cases hin : opnd C j b < n
  · exact Or.inl hin
  let i := opnd C j b - n
  have hwi : opnd C j b = n + i := by dsimp [i]; omega
  have hic : InCone n C i j := (operand_iff hL.1 hj).mpr ⟨b, by omega, Or.inl rfl⟩
  have hilt : i < C.gates.length := by have := inCone_lt hic; omega
  have hr : ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ InCone n C i a := by
    rcases hparent with ha | hrel
    · exact ⟨j, hj, ha, hic⟩
    · obtain ⟨a, ha, hand, hc⟩ := (Finset.mem_filter.mp hrel).2
      exact ⟨a, ha, hand, inCone_trans hic hc⟩
  obtain ⟨a, ha, hand, hc⟩ := hr
  have hb := below_avoids_and hL hT ha hand hc
  rcases hL.1.1 _ (gateAt_mem hilt) with hi | hi
  · have hmem := mem_junk_iff.mpr ⟨hilt, hi, hb⟩
    rw [hjunk, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inr (Or.inl hwi)
    · exact Or.inr (Or.inr (Or.inl hwi))
  · exact Or.inr (Or.inr (Or.inr ⟨i,
      Finset.mem_filter.mpr ⟨mem_orN_iff.mpr ⟨hilt, hi, hb⟩, a, ha, hand, hc⟩, hwi⟩))

lemma strict_decomposition {F B : Finset (Finset ℕ)} {T : ℕ → Finset ℕ} {OK : ℕ → Prop}
    (hmem : ∀ w, OK w → T w ∈ F) (hrep : ∀ S ∈ F \ B, ∃ w, OK w ∧ T w = S)
    (hstep : ∀ w, OK w → T w ∉ B →
      ∃ u v, u < w ∧ v < w ∧ OK u ∧ OK v ∧ T w = T u ∪ T v) :
    ∀ S ∈ F \ B, ∃ U ∈ F, ∃ V ∈ F, U ⊂ S ∧ V ⊂ S ∧ S = U ∪ V := by
  classical
  intro S hS
  have hex := hrep S hS
  let w := Nat.find hex
  have hw : OK w ∧ T w = S := Nat.find_spec hex
  obtain ⟨u, v, hu, hv, hou, hov, he⟩ := hstep w hw.1 (by
    rw [hw.2]; exact (Finset.mem_sdiff.mp hS).2)
  have hne (z : ℕ) (hz : z < w) (hoz : OK z) : T z ≠ S := by
    intro heq
    have hn : w ≤ z := Nat.find_min' hex ⟨hoz, heq⟩
    omega
  rw [hw.2] at he
  refine ⟨T u, hmem u hou, T v, hmem v hov, ?_, ?_, he⟩
  · exact (Finset.ssubset_iff_subset_ne).mpr ⟨he ▸ Finset.subset_union_left, hne u hu hou⟩
  · exact (Finset.ssubset_iff_subset_ne).mpr ⟨he ▸ Finset.subset_union_right, hne v hv hov⟩


lemma main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (p q : ℕ) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hpq : p < q) (hJ : junk G C = {p, q}) (hpnot : ¬ InCone n C p q)
    (hcommon : ∃ t ∈ tops G C, InCone n C p t ∧ InCone n C q t)
    (X : Fin n → Finset ℕ) (hX : ∀ i, X i ⊆ Finset.range 40) :
    let P := sample X (gateVal n C p)
    let Q := sample X (gateVal n C q)
    let base := insert (insert 40 P) (insert (insert 41 Q) (Finset.image X Finset.univ))
    ∃ F H : Finset (Finset ℕ),
      let bare := F.filter (· ⊆ Finset.range 40)
      let meet := Finset.image₂ (· ∩ ·) bare bare
      P ∈ meet ∧ Q ∈ meet ∧
        (∀ S ∈ F \ base, ∃ U ∈ F, ∃ V ∈ F, U ⊂ S ∧ V ⊂ S ∧ S = U ∪ V) ∧
        H ⊆ Finset.image₂ join F F ∧
        H.biUnion id = insert 40 (sample X (circuitFun n C)) ∧
        (F \ base).card + 2 * H.card + 1 ≤ C.size := by
  classical
  dsimp only
  let T := tagged C X p q
  let W := relevant G C
  let P := sample X (gateVal n C p)
  let Q := sample X (gateVal n C q)
  let base := insert (insert 40 P) (insert (insert 41 Q) (Finset.image X Finset.univ))
  let I := W.image (fun j => T (n + j))
  let F := base ∪ I
  let bare := F.filter (· ⊆ Finset.range 40)
  let terms := fun j => join (T (opnd C j 0)) (T (opnd C j 1))
  let H := (tops G C).image terms
  have hpb : p ∈ junk G C := by rw [hJ]; simp
  have hqb : q ∈ junk G C := by rw [hJ]; simp
  have hp := mem_junk_iff.mp hpb
  have hq := mem_junk_iff.mp hqb
  have hrel (j : ℕ) (hj : j ∈ W) := mem_orN_iff.mp (Finset.mem_filter.mp hj).1
  have hjsets := tagged_junk C X hpq hpnot
  have hbase : ∀ w, goodWire n p q W w → T w ∈ base ∨ T w ∈ I := by
    intro w hw
    rcases hw with hi | rfl | rfl | ⟨j, hj, rfl⟩
    · apply Or.inl
      simp only [T, tagged_input C X hX p q w hi, base, Finset.mem_insert]
      exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨⟨w, hi⟩, Finset.mem_univ _, rfl⟩))
    · exact Or.inl (by change tagged C X p q (n + p) ∈ base; rw [hjsets.1]; simp [base, P])
    · exact Or.inl (by change tagged C X p q (n + q) ∈ base; rw [hjsets.2]; simp [base, Q])
    · exact Or.inr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hmem (w : ℕ) (hw : goodWire n p q W w) : T w ∈ F :=
    Finset.mem_union.mpr (hbase w hw)
  have hrep (S : Finset ℕ) (hS : S ∈ F \ base) : ∃ j ∈ W, T (n + j) = S := by
    obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hS
    exact Finset.mem_image.mp ((Finset.mem_union.mp hm).resolve_left hn)
  have hdecomp : ∀ S ∈ F \ base, ∃ U ∈ F, ∃ V ∈ F, U ⊂ S ∧ V ⊂ S ∧ S = U ∪ V := by
    apply strict_decomposition hmem
    · intro S hS
      obtain ⟨j, hj, rfl⟩ := hrep S hS
      exact ⟨n + j, Or.inr (Or.inr (Or.inr ⟨j, hj, rfl⟩)), rfl⟩
    · intro w hw hn
      obtain ⟨j, hj, rfl⟩ : ∃ j ∈ W, w = n + j := by
        rcases hw with hi | rfl | rfl | hw
        · exact False.elim (hn (by
            change tagged C X p q w ∈ base
            rw [tagged_input C X hX p q w hi]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨⟨w, hi⟩, Finset.mem_univ _, rfl⟩))))
        · exact False.elim (hn (by change tagged C X p q (n + p) ∈ base; rw [hjsets.1]; simp [base, P]))
        · exact False.elim (hn (by change tagged C X p q (n + q) ∈ base; rw [hjsets.2]; simp [base, Q]))
        · exact hw
      have hr := hrel j hj
      have hjp : j ≠ p := fun he => by rw [he, hp.2.1] at hr; cases hr.2.1
      have hjq : j ≠ q := fun he => by rw [he, hq.2.1] at hr; cases hr.2.1
      exact ⟨opnd C j 0, opnd C j 1, opnd_lt hL.1 hr.1 0, opnd_lt hL.1 hr.1 1,
        operands_good hL hT hJ hr.1 (Or.inr hj) 0, operands_good hL hT hJ hr.1 (Or.inr hj) 1,
        tagged_or X hL.1 hr.1 hr.2.1 hjp hjq⟩
  have handwire {j : ℕ} (hj : j < C.gates.length) (ha : (gateAt C j).op = GateOp.and)
      (b : Fin 2) : T (opnd C j b) ∈ F :=
    hmem _ (operands_good hL hT hJ hj (Or.inl ha) b)
  have hmeet {j : ℕ} (hj : j < C.gates.length) (ha : (gateAt C j).op = GateOp.and)
      (hnp : ¬ InCone n C p j) (hnq : ¬ InCone n C q j) :
      sample X (gateVal n C j) ∈ Finset.image₂ (· ∩ ·) bare bare := by
    have hplain (b : Fin 2) : T (opnd C j b) = sample X (fun x => wval C x (opnd C j b)) := by
      apply tagged_plain
      · exact fun h => hnp ((operand_iff hL.1 hj).mpr ⟨b, h⟩)
      · exact fun h => hnq ((operand_iff hL.1 hj).mpr ⟨b, h⟩)
    have hb (b : Fin 2) : T (opnd C j b) ∈ bare := by
      apply Finset.mem_filter.mpr
      refine ⟨handwire hj ha b, ?_⟩
      rw [hplain b]
      exact Finset.filter_subset _ _
    apply Finset.mem_image₂.mpr
    refine ⟨_, hb 0, _, hb 1, ?_⟩
    rw [hplain 0, hplain 1]
    ext k
    simp only [Finset.mem_inter, sample, Finset.mem_filter, gateVal_eq_wval,
      wval_gate_and hL.1 _ hj ha, Bool.and_eq_true]
    tauto
  have hpmeet : P ∈ Finset.image₂ (· ∩ ·) bare bare :=
    hmeet hp.1 hp.2.1 (fun h => (Nat.lt_irrefl p) (inCone_lt h))
      (fun h => by have := inCone_lt h; omega)
  have hqmeet : Q ∈ Finset.image₂ (· ∩ ·) bare bare :=
    hmeet hq.1 hq.2.1 hpnot (fun h => (Nat.lt_irrefl q) (inCone_lt h))
  have hHimg : H ⊆ Finset.image₂ join F F := by
    intro S hS
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
    have ht := mem_tops_iff.mp hj
    exact Finset.mem_image₂.mpr ⟨_, handwire ht.1 ht.2.1 0, _, handwire ht.1 ht.2.1 1, rfl⟩
  obtain ⟨t, ht, htp, htq⟩ := hcommon
  have htd := mem_tops_iff.mp ht
  have hne : ∃ u v : Fin n, G.Adj u v := by
    have hv : gateVal n C t (fun _ : Fin n => true) = true :=
      wval_allTrue hL.1 (n + t) (by have := htd.1; omega)
    obtain ⟨u, v, huv, _, _⟩ := (graphFun_iff _).mp (htd.2.2 _ hv)
    exact ⟨u, v, huv⟩
  have hmark : 40 ∈ terms t := by
    apply mem_join.mpr
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · exact ((touches_iff hL.1 htd.1).mp htp).imp mark40_in_tagged.mpr mark40_in_tagged.mpr
    · exact ((touches_iff hL.1 htd.1).mp htq).imp mark41_in_tagged.mpr mark41_in_tagged.mpr
  have hreal (j : ℕ) (hj : j ∈ tops G C) {k : ℕ} (hk : k < 40) :
      k ∈ terms j ↔ gateVal n C j (fun i => decide (k ∈ X i)) = true := by
    have hdata := mem_tops_iff.mp hj
    change k ∈ join _ _ ↔ _
    rw [mem_join, real_in_tagged hk, real_in_tagged hk, gateVal_eq_wval,
      wval_gate_and hL.1 _ hdata.1 hdata.2.1, Bool.and_eq_true]
    have hneq : k ≠ 40 := by omega
    simp [hk, hneq]
  have houtput : H.biUnion id = insert 40 (sample X (circuitFun n C)) := by
    ext k
    rw [Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro ⟨S, hS, hk⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
      change k ∈ join _ _ at hk
      rcases mem_join.mp hk with hreal' | hmark'
      · have hklt := hreal'.2.2
        refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, ?_⟩)
        exact (circuitFun_iff_exists_top hL hne _).mpr ⟨j, hj, (hreal j hj hklt).mp hk⟩
      · exact Or.inl hmark'.1
    · rintro (rfl | hk)
      · exact ⟨terms t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hmark⟩
      · obtain ⟨hkr, hval⟩ := Finset.mem_filter.mp hk
        obtain ⟨j, hj, hjv⟩ := (circuitFun_iff_exists_top hL hne _).mp hval
        exact ⟨terms j, Finset.mem_image.mpr ⟨j, hj, rfl⟩,
          (hreal j hj (Finset.mem_range.mp hkr)).mpr hjv⟩
  have hFcard : (F \ base).card ≤ (orN G C).card := by
    calc
      (F \ base).card ≤ I.card :=
        Finset.card_le_card (fun S hS => Finset.mem_image.mpr (hrep S hS))
      _ ≤ W.card := Finset.card_image_le
      _ ≤ (orN G C).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hHcard : H.card ≤ (tops G C).card := Finset.card_image_le
  have htcount := tops_le_orT hL hT hne
  have hpart := circuit_size_partition hL
  have hjcount : (junk G C).card = 2 := by rw [hJ]; simp [show p ≠ q by omega]
  change ∃ F H : Finset (Finset ℕ), _
  refine ⟨F, H, hpmeet, hqmeet, hdecomp, hHimg, houtput, ?_⟩
  change (F \ base).card + 2 * H.card + 1 ≤ C.size
  omega

end PEqualNP.Outside.L_meta_9425

theorem PEqualNP.Outside.L_meta_9425 :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   have x6 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;   (PEqualNP.TopForm.IsLeastAO x1 x3 ∧ PEqualNP.TopForm.TopForm x1 x3 ∧ x4 < x5 ∧ PEqualNP.TopForm.junk x1 x3 = {x4, x5} ∧ ¬x6 x4 x5 ∧ ∃ x7 ∈ PEqualNP.TopForm.tops x1 x3, x6 x4 x7 ∧ x6 x5 x7) →     have x8 : Finset ℕ := Finset.range (40 : ℕ);     ∀ (x9 : Fin (11 : ℕ) → Finset ℕ),       (∀ (x10 : Fin (11 : ℕ)), x9 x10 ⊆ x8) →         have x11 : Finset (Finset ℕ) := Finset.image x9 Finset.univ;         have x12 : ((Fin (11 : ℕ) → Bool) → Bool) → Finset ℕ := fun (x12 : (Fin (11 : ℕ) → Bool) → Bool) => {x13 ∈ x8 | (x12 fun (x14 : Fin (11 : ℕ)) => Decidable.decide (x13 ∈ x9 x14)) = Bool.true};         have x13 : Finset ℕ := x12 (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4);         have x14 : Finset ℕ := x12 (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5);         have x15 : Finset ℕ := Insert.insert (40 : ℕ) (x12 (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3));         ∃ (x16 : Finset (Finset ℕ)) (x17 : Finset (Finset ℕ)),           have x18 : Finset (Finset ℕ) := Insert.insert (Insert.insert (40 : ℕ) x13) (Insert.insert (Insert.insert (41 : ℕ) x14) x11);           have x19 : Finset (Finset ℕ) := {x19 ∈ x16 | x19 ⊆ x8};           have x20 : Finset (Finset ℕ) := Finset.image₂ (fun (x20 x21 : Finset ℕ) => x20 ∩ x21) x19 x19;           have x21 : Finset ℕ → Finset ℕ → Finset ℕ := fun (x21 x22 : Finset ℕ) => x21 ∩ x22 ∩ x8 ∪ if {(40 : ℕ), (41 : ℕ)} ⊆ x21 ∪ x22 then {(40 : ℕ)} else ∅;           x13 ∈ x20 ∧ x14 ∈ x20 ∧ (∀ x22 ∈ x16 \ x18, ∃ x24 ∈ x16, ∃ x25 ∈ x16, x24 ⊂ x22 ∧ x25 ⊂ x22 ∧ x22 = x24 ∪ x25) ∧ x17 ⊆ Finset.image₂ x21 x16 x16 ∧ x17.biUnion id = x15 ∧ (x16 \ x18).card + (2 : ℕ) * x17.card + (1 : ℕ) ≤ x3.size := by
  intro G x2 C p q _ h _ X hX
  exact @PEqualNP.Outside.L_meta_9425.main 11 G x2 C p q h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2 X hX
