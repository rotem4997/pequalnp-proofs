import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8875

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def andIndexSum (C : Circuit) : ℕ :=
  ∑ k ∈ (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true), k

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma wireVal_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    wireVal n ⟨C.gates ++ [g], out⟩ w x = wireVal n C w x := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD w false =
    (C.gates.foldl wireStep (List.ofFn x)).getD w false
  rw [List.foldl_append]
  have hw' : w < (C.gates.foldl wireStep (List.ofFn x)).length := by
    rw [foldl_wireStep_length, List.length_ofFn]
    exact hw
  exact foldl_wireStep_prefix [g] (C.gates.foldl wireStep (List.ofFn x)) w hw'

lemma wireVal_append_last (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool) :
    wireVal n ⟨C.gates ++ [g], out⟩ (n + C.gates.length) x =
      g.op.eval (g.inputs.map fun u => wireVal n C u x) := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set acc := C.gates.foldl wireStep (List.ofFn x) with hacc
  have hlen : acc.length = n + C.gates.length := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD]
  simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + C.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rfl

lemma output_lt_of_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hF : circuitFun n C = graphFun G ∅) :
    C.output < n + C.gates.length := by
  by_contra hge
  push Not at hge
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have htrue : graphFun G ∅ (fun _ => true) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact ⟨u, v, hadj, rfl, rfl⟩
    have hfalse : circuitFun n C (fun _ => true) = false := by
      unfold circuitFun Circuit.eval
      rw [List.getD_eq_getElem?_getD]
      have hlen : (C.wires (List.ofFn (fun _ : Fin n => true))).length = n + C.gates.length := by
        rw [wires_length, List.length_ofFn]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have hEq := congrFun hF (fun _ => true)
    rw [hfalse, htrue] at hEq
    cases hEq

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
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
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

lemma exists_direct_reader (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (h : InCone n C i j) :
    ∃ g, i < g ∧ g ≤ j ∧ g < C.gates.length ∧ n + i ∈ (gateAt C g).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · refine ⟨j, by omega, le_refl j, hj, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [heq]
      exact hw
    · have hklt : w - n < j := by omega
      obtain ⟨g, hig, hgk, hglen, hmem⟩ := ih (w - n) hklt (by omega) hcone
      exact ⟨g, hig, by omega, hglen, hmem⟩

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp2, rfl⟩ := hb
    have hp1 : p < l1.length := by omega
    exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp1, hbp⟩ := hb
    have hp2 : p < l2.length := by omega
    exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩

lemma delGate_wireVal_mono (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAOOnly : AndOrOnly C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmono_g : wireVal n C (n + g) x = true → wireVal n C r x = true) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n C (origWire n g w) x = true → wireVal n (delGate n g r C) w x = true := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn] at htrue
      exact htrue
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq] at htrue ⊢
      rw [wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB] at htrue
      simp only [mapGate, List.map_map]
      have hop : (gateAt C k0).op = GateOp.and ∨ (gateAt C k0).op = GateOp.or := by
        rw [gateAt_eq_getElem C k0 hk0_lt]
        exact hAOOnly C.gates[k0] (List.getElem_mem hk0_lt)
      apply gateOp_eval_mono (gateAt C k0).op hop _ _ (by simp) _ htrue
      intro p hp1 hp2 hv
      simp only [List.getElem_map, Function.comp_apply] at hv ⊢
      set u := (gateAt C k0).inputs[p]'(by simpa using hp1) with hu_def
      have hu_mem : u ∈ (gateAt C k0).inputs := List.getElem_mem (by simpa using hp1)
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu_mem, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      apply ih (remap n g r u) (by omega) (by omega)
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr]
        rw [hug] at hv
        exact hmono_g hv
      · rw [origWire_remap_ne n g r u hug]
        exact hv

lemma delGate_wireVal_prefix_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g) :
    ∀ w < n + g, wireVal n (delGate n g r C) w x = wireVal n C w x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hkg : k < g := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by
        rw [delGate_length n g r C hg]; omega
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k (by omega)]
      simp only [hkg, ↓reduceIte]
      rw [wireVal_gate n C x k (by omega) hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k := hRB k (by omega) u hu
      have hrm : remap n g r u = u := by unfold remap; split_ifs <;> omega
      simp only [Function.comp_apply, hrm]
      exact ih u (by omega) (by omega)

lemma no_and_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hg : g < C.gates.length)
    (hBelow : BelowF G C i)
    (hgAnd : (gateAt C g).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) : False := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  set C' := delGate n g (n + i) C with hC'
  have hAO' : IsAO2 n C' := delGate_isAO2 n g (n + i) C ⟨hAOOnly, hRB, hLen2⟩ hg (by omega)
  have hout' : C'.output < n + C'.gates.length :=
    delGate_output_lt n g (n + i) C hg (by omega) hout
  have hF' : circuitFun n C' = graphFun G ∅ := by
    funext x
    have hmono_g : wireVal n C (n + g) x = true → wireVal n C (n + i) x = true := by
      intro hg_true
      rw [wireVal_gate n C x g hg hRB, hgAnd] at hg_true
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hg_true
      exact hg_true (wireVal n C (n + i) x) ⟨n + i, hmem, rfl⟩
    cases hgx : graphFun G ∅ x
    · have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hg_false : wireVal n C (n + g) x = false := by
        cases hvg : wireVal n C (n + g) x with
        | false => rfl
        | true =>
          have := hmono_g hvg
          rw [hi_false] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C (n + i) x := by
        rw [hg_false, hi_false]
      have hval := delGate_wireVal_eq n g (n + i) C x hRB hg (by omega) hmatch C'.output hout'
      have hcf : circuitFun n C' x = wireVal n C' C'.output x := rfl
      rw [hcf, hval]
      have hcfC : circuitFun n C x = false := by rw [hF, hgx]
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega), ← hmatch]
        change wireVal n C (n + g) x = false
        rw [← ho]
        exact hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
    · have hcfC : wireVal n C C.output x = true := by
        change circuitFun n C x = true
        rw [hF, hgx]
      have hval := delGate_wireVal_mono n g (n + i) C x hAOOnly hRB hg (by omega) hmono_g
        C'.output hout'
      change wireVal n C' C'.output x = true
      apply hval
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega)]
        rw [ho] at hcfC
        exact hmono_g hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
  have hle := hMin C' hAO' hF'
  have hsz : C'.size = C.size - 1 := delGate_length n g (n + i) C hg
  change C.gates.length ≤ C'.gates.length at hle
  rw [show C'.gates.length = C.gates.length - 1 from hsz] at hle
  omega

def pushOr (n g y i : ℕ) (C : Circuit) : Circuit :=
  let Cmid := delGate n g y C
  ⟨Cmid.gates ++ [⟨GateOp.or, [Cmid.output, n + i]⟩], n + Cmid.gates.length⟩

def shiftDown (g k : ℕ) : ℕ :=
  if k < g then k else k - 1



lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length)
    (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, _, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · omega
    · have hklt : w - n < j := by omega
      have h1 := ih (w - n) hklt (by omega) hcone
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a b c : ℕ) (hc : c < C.gates.length)
    (hab : InCone n C a b) (hbc : InCone n C b c) : InCone n C a c := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    rw [inCone_iff n C b c hc] at hbc
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := hbc
    rw [inCone_iff n C a c hc]
    refine ⟨w, hw, hnw, hlt, Or.inr ?_⟩
    rcases hcase with rfl | hcone
    · exact hab
    · exact ih (w - n) (by omega) (by omega) hcone

lemma delGate_inCone (n g y : ℕ) (C : Circuit)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hy : y < n + g)
    (hymem : y ∈ (gateAt C g).inputs) :
    ∀ b < C.gates.length, b ≠ g → ∀ a < C.gates.length, a ≠ g →
      InCone n (delGate n g y C) (shiftDown g a) (shiftDown g b) → InCone n C a b := by
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro hb hbne a ha hane hcone
    have hsb_lt : shiftDown g b < (delGate n g y C).gates.length := by
      rw [delGate_length n g y C hg]; unfold shiftDown; split_ifs <;> omega
    rw [inCone_iff n (delGate n g y C) (shiftDown g a) (shiftDown g b) hsb_lt] at hcone
    obtain ⟨w', hw', hnw', hlt', hcase⟩ := hcone
    rw [delGate_gateAt n g y C hg (shiftDown g b) (by rw [delGate_length n g y C hg] at hsb_lt; exact hsb_lt)] at hw'
    have hidx : (if shiftDown g b < g then shiftDown g b else shiftDown g b + 1) = b := by
      unfold shiftDown; split_ifs <;> omega
    rw [hidx] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    have hw_lt : w < n + b := hRB b hb w hw
    by_cases hwg : w = n + g
    · have hrm : remap n g y w = y := by
        rw [hwg]; unfold remap; simp
      rw [hrm] at hnw' hlt' hcase
      have hgb : g < b := by omega
      have hyn_lt : y - n < g := by omega
      have hyn_sd : shiftDown g (y - n) = y - n := by
        unfold shiftDown; simp [hyn_lt]
      have ha_cone_g : InCone n C a g := by
        rw [inCone_iff n C a g hg]
        refine ⟨y, hymem, hnw', hy, ?_⟩
        rcases hcase with heq | hsub
        · left
          unfold shiftDown at heq
          split_ifs at heq <;> omega
        · right
          rw [← hyn_sd] at hsub
          exact ih (y - n) (by omega) (by omega) (by omega) a ha hane hsub
      rw [inCone_iff n C a b hb]
      refine ⟨n + g, hwg ▸ hw, by omega, by omega, Or.inr ?_⟩
      simpa using ha_cone_g
    · have hnw : n ≤ w := by
        unfold remap at hnw'
        split_ifs at hnw' <;> omega
      have hwn_ne : w - n ≠ g := by omega
      have hwn_sd : remap n g y w - n = shiftDown g (w - n) := by
        unfold remap shiftDown
        split_ifs <;> omega
      rw [inCone_iff n C a b hb]
      refine ⟨w, hw, hnw, hw_lt, ?_⟩
      rcases hcase with heq | hsub
      · left
        rw [hwn_sd] at heq
        unfold shiftDown at heq
        split_ifs at heq <;> omega
      · right
        rw [hwn_sd] at hsub
        exact ih (w - n) (by omega) (by omega) hwn_ne a ha hane hsub

lemma inCone_append_lt (n : ℕ) (C : Circuit) (gt : Gate) (out : ℕ) (a b : ℕ)
    (hb : b < C.gates.length) :
    InCone n ⟨C.gates ++ [gt], out⟩ a b ↔ InCone n C a b := by
  unfold InCone cones
  rw [List.foldl_append]
  have hlen : (C.gates.foldl (coneStep n) []).length = C.gates.length := by
    rw [foldl_coneStep_length, List.length_nil, zero_add]
  rw [foldl_coneStep_prefix n [gt] _ b (by omega)]

lemma delGate_wireVal_noCone (n g y : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hy : y < n + g) :
    ∀ w < n + (delGate n g y C).gates.length,
      (∀ k, origWire n g w = n + k → k ≠ g ∧ ¬ InCone n C g k) →
      wireVal n (delGate n g y C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g y C) := by
    intro k hk w' hw'
    rw [delGate_length n g y C hg] at hk
    rw [delGate_gateAt n g y C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g y C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g y C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g y C hg]; exact hk_lt
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      have hk0_no := hno k0 (by rw [hw_eq, horig])
      rw [hw_eq, wireVal_gate n (delGate n g y C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g y C hg k hk_lt']
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k0 := hRB k0 hk0_lt u hu
      have hug : u ≠ n + g := by
        intro heq
        apply hk0_no.2
        rw [inCone_iff n C g k0 hk0_lt]
        exact ⟨u, hu, by omega, hu_lt, Or.inl (by omega)⟩
      have hru_lt : remap n g y u < n + k := by
        have h1 : remap n g y u ∈ (gateAt (delGate n g y C) k).inputs := by
          rw [delGate_gateAt n g y C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g y u) h1
      have hru_orig : origWire n g (remap n g y u) = u := origWire_remap_ne n g y u hug
      have hih := ih (remap n g y u) (by omega) (by omega) (by
        intro c hc
        rw [hru_orig] at hc
        refine ⟨by omega, ?_⟩
        intro hgc
        apply hk0_no.2
        rw [inCone_iff n C g k0 hk0_lt]
        refine ⟨u, hu, by omega, hu_lt, Or.inr ?_⟩
        simpa [hc] using hgc)
      simp only [Function.comp_apply, hih, hru_orig]

noncomputable def unownedCount {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : ℕ :=
  {k : ℕ | k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
    ∀ u v : Fin n, G.Adj u v → ¬ Owns n C k u v}.ncard

lemma pushOr_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g j : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hgj : g < j) (hj : j < C.gates.length)
    (hiAnd : (gateAt C i).op = GateOp.and)
    (hBelow : BelowF G C i)
    (hgOr : (gateAt C g).op = GateOp.or)
    (hjAnd : (gateAt C j).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) :
    ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
      (junk G C').card = (junk G C).card ∧ unownedCount G C' ≤ unownedCount G C ∧
      andIndexSum C' < andIndexSum C := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hg : g < C.gates.length := by omega
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  have hgin_len : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq_getElem C g hg]
    exact hLen2 C.gates[g] (List.getElem_mem hg)
  rcases hgin : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [hgin] at hgin_len
  · simp [hgin] at hgin_len
  · have hmem' : n + i = a ∨ n + i = b := by
      simpa [hgin] using hmem
    set y := if a = n + i then b else a with hy_def
    have hy_mem : y ∈ (gateAt C g).inputs := by
      rw [hgin, hy_def]
      split_ifs <;> simp
    have hy_lt : y < n + g := hRB g hg y hy_mem
    have hg_eval : ∀ x : Fin n → Bool,
        wireVal n C (n + g) x = (wireVal n C (n + i) x || wireVal n C y x) := by
      intro x
      rw [wireVal_gate n C x g hg hRB, hgOr, hgin]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hy_def]
      split_ifs with ha
      · rw [ha]
      · rcases hmem' with rfl | rfl
        · exact absurd rfl ha
        · exact Bool.or_comm _ _
    set Cmid := delGate n g y C with hCmid
    set C' := pushOr n g y i C with hC'
    have hCmid_len : Cmid.gates.length = C.gates.length - 1 := delGate_length n g y C hg
    have hC'_len : C'.gates.length = C.gates.length := by
      simp only [hC', pushOr, List.length_append, List.length_singleton, ← hCmid, hCmid_len]
      omega
    have hCmid_AO : IsAO2 n Cmid := delGate_isAO2 n g y C ⟨hAOOnly, hRB, hLen2⟩ hg hy_lt
    have hCmid_out : Cmid.output < n + Cmid.gates.length :=
      delGate_output_lt n g y C hg hy_lt hout
    have hC'_AO : IsAO2 n C' := by
      rcases hCmid_AO with ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h1 gt hgt
        · exact Or.inr rfl
      · intro k hk w hw
        have hk' : k < Cmid.gates.length + 1 := by
          simpa [hC', pushOr, ← hCmid] using hk
        by_cases hkm : k < Cmid.gates.length
        · have hgat : gateAt C' k = gateAt Cmid k := by
            rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem Cmid k hkm]
            simp [hC', pushOr, ← hCmid, List.getElem_append_left hkm]
          rw [hgat] at hw
          exact h2 k hkm w hw
        · have hkeq : k = Cmid.gates.length := by omega
          have hgat : gateAt C' k = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
            rw [gateAt_eq_getElem C' k hk]
            simp [hC', pushOr, ← hCmid, hkeq]
          rw [hgat] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · omega
          · rw [hkeq, hCmid_len]; omega
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h3 gt hgt
        · rfl
    have hC'_F : circuitFun n C' = graphFun G ∅ := by
      funext x
      have hlast : circuitFun n C' x =
          (wireVal n Cmid Cmid.output x || wireVal n Cmid (n + i) x) := by
        change wireVal n C' (n + Cmid.gates.length) x = _
        have h := wireVal_append_last n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩
          (n + Cmid.gates.length) x
        simpa [hC', pushOr, ← hCmid, GateOp.eval] using h
      rw [hlast]
      have hni : wireVal n Cmid (n + i) x = wireVal n C (n + i) x :=
        delGate_wireVal_prefix_eq n g y C x hRB hg hy_lt (n + i) (by omega)
      rw [hni]
      cases hvi : wireVal n C (n + i) x
      · have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
          rw [hg_eval x, hvi, Bool.false_or]
        have hval := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch Cmid.output hCmid_out
        rw [hval, Bool.or_false]
        have hcfC : wireVal n C C.output x = graphFun G ∅ x := congrFun hF x
        by_cases ho : C.output = n + g
        · simp only [hCmid, delGate]
          rw [ho, origWire_remap_eq n g y hy_lt, ← hmatch, ← ho]
          exact hcfC
        · simp only [hCmid, delGate]
          rw [origWire_remap_ne n g y C.output ho]
          exact hcfC
      · rw [Bool.or_true]
        exact (hBelow x hvi).symm
    have hC'_Least : IsLeastAO G C' := by
      refine ⟨hC'_AO, hC'_F, ?_⟩
      intro D hDAO hDF
      have hle := hMin D hDAO hDF
      change C'.gates.length ≤ D.gates.length
      rw [hC'_len]
      exact hle
    have hgateAt_lt : ∀ m < Cmid.gates.length,
        gateAt C' m = gateAt Cmid m := by
      intro m hm
      have hm' : m < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' m hm', gateAt_eq_getElem Cmid m hm]
      simp [hC', pushOr, ← hCmid, List.getElem_append_left hm]
    have hgateAt_last : gateAt C' Cmid.gates.length = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
      have hm' : Cmid.gates.length < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' Cmid.gates.length hm']
      simp [hC', pushOr, ← hCmid]
    have hop_shift : ∀ k < C.gates.length, k ≠ g →
        (gateAt C' (shiftDown g k)).op = (gateAt C k).op := by
      intro k hk hne
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      rw [hgateAt_lt (shiftDown g k) hsd]
      rw [hCmid, delGate_gateAt n g y C hg (shiftDown g k) (by omega)]
      simp only [mapGate]
      have hidx : (if shiftDown g k < g then shiftDown g k else shiftDown g k + 1) = k := by
        unfold shiftDown; split_ifs <;> omega
      rw [hidx]
    have hval_false : ∀ k < C.gates.length, k ≠ g → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false →
        gateVal n C' (shiftDown g k) x = gateVal n C k x := by
      intro k hk hne x hgx
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
        rw [hg_eval x, hi_false, Bool.false_or]
      have happ : wireVal n C' (n + shiftDown g k) x = wireVal n Cmid (n + shiftDown g k) x :=
        wireVal_append_lt n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩ (n + Cmid.gates.length) x
          (n + shiftDown g k) (by omega)
      have heq := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch
        (n + shiftDown g k) (by rw [← hCmid]; omega)
      have horig : origWire n g (n + shiftDown g k) = n + k := by
        unfold origWire shiftDown
        split_ifs <;> omega
      change wireVal n C' (n + shiftDown g k) x = wireVal n C (n + k) x
      rw [happ, hCmid, heq, horig]
    have hjunk : (junk G C').card = (junk G C).card := by
      symm
      apply Finset.card_bij (fun k _ => shiftDown g k)
      · intro k hk
        unfold junk gatesWhere at hk ⊢
        rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
        rcases hk with ⟨hk_lt, hk_and, _, x, hkx, hgx⟩
        have hkne : k ≠ g := by
          intro hEq; rw [hEq, hgOr] at hk_and; cases hk_and
        have hsd_lt : shiftDown g k < C'.gates.length := by
          unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
        refine ⟨hsd_lt, ?_, hsd_lt, x, ?_, hgx⟩
        · rw [hop_shift k hk_lt hkne]; exact hk_and
        · rw [hval_false k hk_lt hkne x hgx]; exact hkx
      · intro k1 hk1 k2 hk2 heq
        unfold junk gatesWhere at hk1 hk2
        rw [Finset.mem_filter, Finset.mem_range] at hk1 hk2
        have hne1 : k1 ≠ g := by
          intro hEq; have := hk1.2.1; rw [hEq, hgOr] at this; cases this
        have hne2 : k2 ≠ g := by
          intro hEq; have := hk2.2.1; rw [hEq, hgOr] at this; cases this
        unfold shiftDown at heq
        split_ifs at heq <;> omega
      · intro m hm
        unfold junk gatesWhere at hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rcases hm with ⟨hm_lt, hm_and, _, x, hmx, hgx⟩
        have hm_ne : m ≠ Cmid.gates.length := by
          intro hEq; rw [hEq, hgateAt_last] at hm_and; cases hm_and
        have hm_mid : m < Cmid.gates.length := by
          rw [hC'_len] at hm_lt; omega
        set k := if m < g then m else m + 1 with hk_def
        have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
        have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
        have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
        refine ⟨k, ?_, hsd⟩
        unfold junk gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_, hk_lt, x, ?_, hgx⟩
        · rw [← hop_shift k hk_lt hkne, hsd]; exact hm_and
        · rw [← hval_false k hk_lt hkne x hgx, hsd]; exact hmx
    have hsum : andIndexSum C' < andIndexSum C := by
      unfold andIndexSum
      set A := (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true)
      set A' := (Finset.range C'.gates.length).filter (fun k => isAndOp (gateAt C' k).op = true)
      have hsum_eq : ∑ k ∈ A, shiftDown g k = ∑ m ∈ A', m := by
        apply Finset.sum_bij (fun k _ => shiftDown g k)
        · intro k hk
          simp only [A, A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk ⊢
          have hkne : k ≠ g := by
            intro hEq; rw [hEq, hgOr] at hk; cases hk.2
          have hsd_lt : shiftDown g k < C'.gates.length := by
            unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
          exact ⟨hsd_lt, by rw [hop_shift k hk.1 hkne]; exact hk.2⟩
        · intro k1 hk1 k2 hk2 heq
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk1 hk2
          have hne1 : k1 ≠ g := by intro hEq; rw [hEq, hgOr] at hk1; cases hk1.2
          have hne2 : k2 ≠ g := by intro hEq; rw [hEq, hgOr] at hk2; cases hk2.2
          unfold shiftDown at heq
          split_ifs at heq <;> omega
        · intro m hm
          simp only [A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hm
          have hm_ne : m ≠ Cmid.gates.length := by
            intro hEq; rw [hEq, hgateAt_last] at hm; cases hm.2
          have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm; omega
          set k := if m < g then m else m + 1 with hk_def
          have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
          have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
          have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
          refine ⟨k, ?_, hsd⟩
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hk_lt, by rw [← hop_shift k hk_lt hkne, hsd]; exact hm.2⟩
        · intro _ _; rfl
      rw [← hsum_eq]
      apply Finset.sum_lt_sum
      · intro k _
        unfold shiftDown; split_ifs <;> omega
      · refine ⟨j, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hj, hjAnd⟩
        · unfold shiftDown; split_ifs <;> omega
    have howns_pres : ∀ k < C.gates.length, ∀ u v : Fin n, G.Adj u v →
        Owns n C k u v → Owns n C' (shiftDown g k) u v := by
      intro k hk u v _ hown
      rcases hown with ⟨_, hkAnd, hkTrue, hkMin⟩
      have hkne : k ≠ g := by
        intro hEq; rw [hEq, hgOr] at hkAnd; cases hkAnd
      have hsd_mid : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      have hsd_lt : shiftDown g k < C'.gates.length := by
        rw [hC'_len]; unfold shiftDown; split_ifs <;> omega
      have hsd_and : (gateAt C' (shiftDown g k)).op = GateOp.and := by
        rw [hop_shift k hk hkne]; exact hkAnd
      have hval_pair : ∀ a < C.gates.length, a ≠ g → (a = k ∨ InCone n C a k) →
          gateVal n C' (shiftDown g a) (pairInput u v) = gateVal n C a (pairInput u v) := by
        intro a ha hane ha_rel
        have hasd_mid : shiftDown g a < Cmid.gates.length := by
          unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
        have happ : wireVal n C' (n + shiftDown g a) (pairInput u v) =
            wireVal n Cmid (n + shiftDown g a) (pairInput u v) :=
          wireVal_append_lt n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩ (n + Cmid.gates.length)
            (pairInput u v) (n + shiftDown g a) (by omega)
        have horig : origWire n g (n + shiftDown g a) = n + a := by
          unfold origWire shiftDown; split_ifs <;> omega
        change wireVal n C' (n + shiftDown g a) (pairInput u v) =
          wireVal n C (n + a) (pairInput u v)
        rw [happ]
        cases hvi : wireVal n C (n + i) (pairInput u v)
        · have hmatch : wireVal n C (n + g) (pairInput u v) = wireVal n C y (pairInput u v) := by
            rw [hg_eval (pairInput u v), hvi, Bool.false_or]
          rw [hCmid, delGate_wireVal_eq n g y C (pairInput u v) hRB hg hy_lt hmatch
            (n + shiftDown g a) (by rw [← hCmid]; omega), horig]
        · have hg_not_cone : ¬ InCone n C g a := by
            intro hga
            have hig_cone : InCone n C i g := by
              rw [inCone_iff n C i g hg]
              exact ⟨n + i, hmem, by omega, by omega, Or.inl (by omega)⟩
            have hia : InCone n C i a := inCone_trans n C i g a ha hig_cone hga
            have hik : InCone n C i k := by
              rcases ha_rel with rfl | hak
              · exact hia
              · exact inCone_trans n C i a k hk hia hak
            have hik_lt : i < k := inCone_lt n C i k hk hik
            have hfalse := hkMin i hik_lt hik hiAnd
            change wireVal n C (n + i) (pairInput u v) = false at hfalse
            rw [hvi] at hfalse
            cases hfalse
          rw [hCmid, delGate_wireVal_noCone n g y C (pairInput u v) hRB hg hy_lt
            (n + shiftDown g a) (by rw [← hCmid]; omega) (by
              intro c hc
              rw [horig] at hc
              have hca : c = a := by omega
              subst hca
              exact ⟨hane, hg_not_cone⟩), horig]
      refine ⟨hsd_lt, hsd_and, ?_, ?_⟩
      · rw [hval_pair k hk hkne (Or.inl rfl)]; exact hkTrue
      · intro m hm_lt hm_cone hm_and
        have hm_mid : m < Cmid.gates.length := by omega
        set a := if m < g then m else m + 1 with ha_def
        have ha_lt : a < C.gates.length := by rw [ha_def]; split_ifs <;> omega
        have hane : a ≠ g := by rw [ha_def]; split_ifs <;> omega
        have hasd : shiftDown g a = m := by unfold shiftDown; rw [ha_def]; split_ifs <;> omega
        have hm_cone_mid : InCone n Cmid (shiftDown g a) (shiftDown g k) := by
          rw [hasd]
          exact (inCone_append_lt n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩
            (n + Cmid.gates.length) m (shiftDown g k) hsd_mid).mp hm_cone
        have hak_cone : InCone n C a k :=
          delGate_inCone n g y C hRB hg hy_lt hy_mem k hk hkne a ha_lt hane hm_cone_mid
        have ha_and : (gateAt C a).op = GateOp.and := by
          rw [← hop_shift a ha_lt hane, hasd]; exact hm_and
        have hak_lt : a < k := inCone_lt n C a k hk hak_cone
        rw [← hasd, hval_pair a ha_lt hane (Or.inr hak_cone)]
        exact hkMin a hak_lt hak_cone ha_and
    have hunowned : unownedCount G C' ≤ unownedCount G C := by
      classical
      let S : Finset ℕ := (Finset.range C.gates.length).filter fun k =>
        (gateAt C k).op = GateOp.and ∧ ∀ u v : Fin n, G.Adj u v → ¬ Owns n C k u v
      let S' : Finset ℕ := (Finset.range C'.gates.length).filter fun m =>
        (gateAt C' m).op = GateOp.and ∧ ∀ u v : Fin n, G.Adj u v → ¬ Owns n C' m u v
      have hS_eq : unownedCount G C = S.card := by
        unfold unownedCount
        rw [← Set.ncard_coe_finset]
        congr 1
        ext k
        simp [S]
      have hS'_eq : unownedCount G C' = S'.card := by
        unfold unownedCount
        rw [← Set.ncard_coe_finset]
        congr 1
        ext m
        simp [S']
      rw [hS_eq, hS'_eq]
      have hsub : S' ⊆ S.image (shiftDown g) := by
        intro m hm
        simp only [S', Finset.mem_filter, Finset.mem_range] at hm
        rcases hm with ⟨hm_lt, hm_and, hm_no⟩
        have hm_ne : m ≠ Cmid.gates.length := by
          intro hEq; rw [hEq, hgateAt_last] at hm_and; cases hm_and
        have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm_lt; omega
        set k := if m < g then m else m + 1 with hk_def
        have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
        have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
        have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
        refine Finset.mem_image.mpr ⟨k, ?_, hsd⟩
        simp only [S, Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_, ?_⟩
        · rw [← hop_shift k hk_lt hkne, hsd]; exact hm_and
        · intro u v huv hown
          exact hm_no u v huv (hsd ▸ howns_pres k hk_lt u v huv hown)
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    exact ⟨C', hC'_Least, hC'_len, hjunk, hunowned, hsum⟩
  · simp [hgin] at hgin_len



lemma main_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) (m : ℕ) :
    ∀ C : Circuit, andIndexSum C = m → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
        unownedCount G C' ≤ unownedCount G C ∧ TopForm G C' := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro C hm hL
    by_cases hTF : TopForm G C
    · exact ⟨C, hL, rfl, le_rfl, hTF⟩
    · unfold TopForm at hTF
      push Not at hTF
      obtain ⟨i, hi, j, hj, hiAnd, hiBelow, hjAnd, hCone⟩ := hTF
      obtain ⟨g, hig, hgj, hglen, hmem⟩ := exists_direct_reader n C i j hj hCone
      have hgAO : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
        rw [gateAt_eq_getElem C g hglen]
        exact hL.1.1 C.gates[g] (List.getElem_mem hglen)
      rcases hgAO with hgAnd | hgOr
      · exfalso
        exact no_and_reader G C i g hE hL hig hglen hiBelow hgAnd hmem
      · have hgj_lt : g < j := by
          by_contra hge
          have hEq : g = j := by omega
          rw [hEq, hjAnd] at hgOr
          cases hgOr
        obtain ⟨C1, hL1, hsz1, _, hun1, hsum1⟩ :=
          pushOr_step G C i g j hE hL hig hgj_lt hj hiAnd hiBelow hgOr hjAnd hmem
        obtain ⟨C2, hL2, hsz2, hun2, hTF2⟩ :=
          ih (andIndexSum C1) (by omega) C1 rfl hL1
        exact ⟨C2, hL2, hsz2.trans hsz1, le_trans hun2 hun1, hTF2⟩

lemma isMinimalMono_isLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hMin : IsMinimalMonoCircuit n C) (hF : circuitFun n C = graphFun G ∅) :
    IsLeastAO G C := by
  have hCfalse : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
    have h := congrFun hF (fun _ : Fin n => false)
    change C.eval (List.ofFn (fun _ : Fin n => false)) = graphFun G ∅ (fun _ : Fin n => false) at h
    rw [h]
    simp [graphFun]
  let evalGates (gs : List Gate) (x : List Bool) : List Bool := gs.foldl wireStep x
  have evalGates_append : ∀ (gs₁ gs₂ : List Gate) (x : List Bool),
      evalGates (gs₁ ++ gs₂) x = evalGates gs₂ (evalGates gs₁ x) :=
    fun _ _ _ => List.foldl_append
  have evalGates_append_singleton : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      evalGates (gs ++ [g]) x = wireStep (evalGates gs x) g := by
    intro gs g x; rw [evalGates_append]; rfl
  have evalGates_length : ∀ (gs : List Gate) (x : List Bool),
      (evalGates gs x).length = x.length + gs.length :=
    fun gs x => foldl_wireStep_length gs x
  have getD_append_left : ∀ {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α), i < l₁.length →
      (l₁ ++ l₂).getD i d = l₁.getD i d := by
    intro α l₁ l₂ i d hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_append_singleton_self : ∀ {α : Type} (l : List α) (a d : α),
      (l ++ [a]).getD l.length d = a := by
    intro α l a d
    simp [List.getD_eq_getElem?_getD]
  have getD_of_le : ∀ {α : Type} (l : List α) (i : ℕ) (d : α), l.length ≤ i →
      l.getD i d = d := by
    intro α l i d hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  let repVal (outWires : List Bool) : Bool ⊕ ℕ → Bool :=
    Sum.elim id (fun k => outWires.getD k false)
  let repBound (bound : ℕ) : Bool ⊕ ℕ → Prop :=
    Sum.elim (fun _ => True) (fun k => k < bound)
  have repBound_mono : ∀ {b₁ b₂ : ℕ} {r : Bool ⊕ ℕ}, b₁ ≤ b₂ → repBound b₁ r → repBound b₂ r := by
    intro b₁ b₂ r h hr
    cases r with
    | inl _ => trivial
    | inr k => exact Nat.lt_of_lt_of_le hr h
  have repVal_append : ∀ (w₁ w₂ : List Bool) (r : Bool ⊕ ℕ), repBound w₁.length r →
      repVal (w₁ ++ w₂) r = repVal w₁ r := by
    intro w₁ w₂ r hr
    cases r with
    | inl _ => rfl
    | inr k => exact getD_append_left w₁ w₂ k false hr
  let combineAnd (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ) : (Bool ⊕ ℕ) × List Gate :=
    Sum.elim
      (fun b1 => cond b1 (r2, outGates) (Sum.inl false, outGates))
      (fun k1 => Sum.elim
        (fun b2 => cond b2 (Sum.inr k1, outGates) (Sum.inl false, outGates))
        (fun k2 => (Sum.inr (n + outGates.length), outGates ++ [Gate.mk GateOp.and [k1, k2]]))
        r2)
      r1
  let combineOr (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ) : (Bool ⊕ ℕ) × List Gate :=
    Sum.elim
      (fun b1 => cond b1 (Sum.inl true, outGates) (r2, outGates))
      (fun k1 => Sum.elim
        (fun b2 => cond b2 (Sum.inl true, outGates) (Sum.inr k1, outGates))
        (fun k2 => (Sum.inr (n + outGates.length), outGates ++ [Gate.mk GateOp.or [k1, k2]]))
        r2)
      r1
  let stepGate (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
    let getR := fun i => st.1.getD i (Sum.inl false)
    let res : (Bool ⊕ ℕ) × List Gate :=
      GateOp.casesOn g.op
        (List.casesOn g.inputs (Sum.inl true, st.2) fun i l1 =>
          List.casesOn l1 (getR i, st.2) fun j l2 =>
            List.casesOn l2 (combineAnd st.2 (getR i) (getR j)) fun _ _ => (Sum.inl false, st.2))
        (List.casesOn g.inputs (Sum.inl false, st.2) fun i l1 =>
          List.casesOn l1 (getR i, st.2) fun j l2 =>
            List.casesOn l2 (combineOr st.2 (getR i) (getR j)) fun _ _ => (Sum.inl false, st.2))
        (Sum.inl false, st.2)
        (fun _ => (Sum.inl false, st.2))
        (Sum.inl false, st.2)
    (st.1 ++ [res.1], res.2)
  let initState : List (Bool ⊕ ℕ) × List Gate :=
    (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ)), [])
  let Bad (gs : List Gate) : Prop :=
    ∃ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).inputs.length ≠ 2 ∨
      ∃ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n + j ≤ u
  let Inv (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) : Prop :=
    st.1.length = n + gs.length ∧
    st.2.length ≤ gs.length ∧
    (Bad gs → st.2.length < gs.length) ∧
    IsAO2 n ⟨st.2, 0⟩ ∧
    (∀ w : ℕ, repBound (n + st.2.length) (st.1.getD w (Sum.inl false))) ∧
    (∀ (x : Fin n → Bool) (w : ℕ),
      (evalGates gs (List.ofFn x)).getD w false =
        repVal (evalGates st.2 (List.ofFn x)) (st.1.getD w (Sum.inl false)))
  have isAO2_append_singleton : ∀ (gs : List Gate) (op : GateOp) (k1 k2 : ℕ),
      IsAO2 n ⟨gs, 0⟩ → (op = GateOp.and ∨ op = GateOp.or) →
      k1 < n + gs.length → k2 < n + gs.length →
      IsAO2 n ⟨gs ++ [Gate.mk op [k1, k2]], 0⟩ := by
    intro gs op k1 k2 h hop hk1 hk2
    rcases h with ⟨hao, hrb, hlen⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hao g hg
      · exact hop
    · intro j hj w hw
      have hj' : j < gs.length + 1 := by simpa using hj
      by_cases hlt : j < gs.length
      · have hga : gateAt ⟨gs ++ [Gate.mk op [k1, k2]], 0⟩ j = gateAt ⟨gs, 0⟩ j :=
          getD_append_left gs [Gate.mk op [k1, k2]] j ⟨GateOp.or, []⟩ hlt
        rw [hga] at hw
        exact hrb j hlt w hw
      · have heq : j = gs.length := by omega
        subst heq
        have hga : gateAt ⟨gs ++ [Gate.mk op [k1, k2]], 0⟩ gs.length = Gate.mk op [k1, k2] :=
          getD_append_singleton_self gs (Gate.mk op [k1, k2]) ⟨GateOp.or, []⟩
        rw [hga] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hk1
        · exact hk2
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hlen g hg
      · rfl
  have combineAnd_spec : ∀ (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ),
      IsAO2 n ⟨outGates, 0⟩ →
      repBound (n + outGates.length) r1 →
      repBound (n + outGates.length) r2 →
      let res := combineAnd outGates r1 r2
      (∃ extra : List Gate, res.2 = outGates ++ extra ∧ extra.length ≤ 1 ∧
        ((r1 = Sum.inl false ∨ r2 = Sum.inl false) → extra = [])) ∧
      IsAO2 n ⟨res.2, 0⟩ ∧
      repBound (n + res.2.length) res.1 ∧
      (∀ x : Fin n → Bool,
        (∃ tail : List Bool, evalGates res.2 (List.ofFn x) = evalGates outGates (List.ofFn x) ++ tail) ∧
        repVal (evalGates res.2 (List.ofFn x)) res.1 =
          (repVal (evalGates outGates (List.ofFn x)) r1 && repVal (evalGates outGates (List.ofFn x)) r2)) := by
    intro outGates r1 r2 hao hr1 hr2
    cases r1 with
    | inl b1 =>
      cases b1 with
      | false =>
        refine ⟨⟨[], by simp [combineAnd], by simp, fun _ => rfl⟩, hao, trivial, ?_⟩
        intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
      | true =>
        refine ⟨⟨[], by simp [combineAnd], by simp, fun _ => rfl⟩, hao, hr2, ?_⟩
        intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
    | inr k1 =>
      cases r2 with
      | inl b2 =>
        cases b2 with
        | false =>
          refine ⟨⟨[], by simp [combineAnd], by simp, fun _ => rfl⟩, hao, trivial, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
        | true =>
          refine ⟨⟨[], by simp [combineAnd], by simp, fun _ => rfl⟩, hao, hr1, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
      | inr k2 =>
        refine ⟨⟨[Gate.mk GateOp.and [k1, k2]], rfl, by simp, fun h => by rcases h with h | h <;> cases h⟩, ?_, ?_, ?_⟩
        · exact isAO2_append_singleton outGates GateOp.and k1 k2 hao (Or.inl rfl) hr1 hr2
        · change n + outGates.length < n + (outGates ++ [Gate.mk GateOp.and [k1, k2]]).length
          simp
        · intro x
          have hstep : evalGates (outGates ++ [Gate.mk GateOp.and [k1, k2]]) (List.ofFn x) =
              evalGates outGates (List.ofFn x) ++
                [(evalGates outGates (List.ofFn x)).getD k1 false &&
                 (evalGates outGates (List.ofFn x)).getD k2 false] := by
            rw [evalGates_append_singleton]
            change evalGates outGates (List.ofFn x) ++
              [((evalGates outGates (List.ofFn x)).getD k1 false &&
                ((evalGates outGates (List.ofFn x)).getD k2 false && true))] = _
            rw [Bool.and_true]
          refine ⟨⟨[(evalGates outGates (List.ofFn x)).getD k1 false &&
                    (evalGates outGates (List.ofFn x)).getD k2 false], hstep⟩, ?_⟩
          change (evalGates (outGates ++ [Gate.mk GateOp.and [k1, k2]]) (List.ofFn x)).getD
            (n + outGates.length) false =
            ((evalGates outGates (List.ofFn x)).getD k1 false &&
             (evalGates outGates (List.ofFn x)).getD k2 false)
          rw [hstep]
          have hlen : (evalGates outGates (List.ofFn x)).length = n + outGates.length := by
            rw [evalGates_length, List.length_ofFn]
          rw [← hlen]
          exact getD_append_singleton_self _ _ false
  have combineOr_spec : ∀ (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ),
      IsAO2 n ⟨outGates, 0⟩ →
      repBound (n + outGates.length) r1 →
      repBound (n + outGates.length) r2 →
      let res := combineOr outGates r1 r2
      (∃ extra : List Gate, res.2 = outGates ++ extra ∧ extra.length ≤ 1 ∧
        ((r1 = Sum.inl false ∨ r2 = Sum.inl false) → extra = [])) ∧
      IsAO2 n ⟨res.2, 0⟩ ∧
      repBound (n + res.2.length) res.1 ∧
      (∀ x : Fin n → Bool,
        (∃ tail : List Bool, evalGates res.2 (List.ofFn x) = evalGates outGates (List.ofFn x) ++ tail) ∧
        repVal (evalGates res.2 (List.ofFn x)) res.1 =
          (repVal (evalGates outGates (List.ofFn x)) r1 || repVal (evalGates outGates (List.ofFn x)) r2)) := by
    intro outGates r1 r2 hao hr1 hr2
    cases r1 with
    | inl b1 =>
      cases b1 with
      | true =>
        refine ⟨⟨[], by simp [combineOr], by simp, fun _ => rfl⟩, hao, trivial, ?_⟩
        intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
      | false =>
        refine ⟨⟨[], by simp [combineOr], by simp, fun _ => rfl⟩, hao, hr2, ?_⟩
        intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
    | inr k1 =>
      cases r2 with
      | inl b2 =>
        cases b2 with
        | true =>
          refine ⟨⟨[], by simp [combineOr], by simp, fun _ => rfl⟩, hao, trivial, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
        | false =>
          refine ⟨⟨[], by simp [combineOr], by simp, fun _ => rfl⟩, hao, hr1, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
      | inr k2 =>
        refine ⟨⟨[Gate.mk GateOp.or [k1, k2]], rfl, by simp, fun h => by rcases h with h | h <;> cases h⟩, ?_, ?_, ?_⟩
        · exact isAO2_append_singleton outGates GateOp.or k1 k2 hao (Or.inr rfl) hr1 hr2
        · change n + outGates.length < n + (outGates ++ [Gate.mk GateOp.or [k1, k2]]).length
          simp
        · intro x
          have hstep : evalGates (outGates ++ [Gate.mk GateOp.or [k1, k2]]) (List.ofFn x) =
              evalGates outGates (List.ofFn x) ++
                [(evalGates outGates (List.ofFn x)).getD k1 false ||
                 (evalGates outGates (List.ofFn x)).getD k2 false] := by
            rw [evalGates_append_singleton]
            change evalGates outGates (List.ofFn x) ++
              [((evalGates outGates (List.ofFn x)).getD k1 false ||
                ((evalGates outGates (List.ofFn x)).getD k2 false || false))] = _
            rw [Bool.or_false]
          refine ⟨⟨[(evalGates outGates (List.ofFn x)).getD k1 false ||
                    (evalGates outGates (List.ofFn x)).getD k2 false], hstep⟩, ?_⟩
          change (evalGates (outGates ++ [Gate.mk GateOp.or [k1, k2]]) (List.ofFn x)).getD
            (n + outGates.length) false =
            ((evalGates outGates (List.ofFn x)).getD k1 false ||
             (evalGates outGates (List.ofFn x)).getD k2 false)
          rw [hstep]
          have hlen : (evalGates outGates (List.ofFn x)).length = n + outGates.length := by
            rw [evalGates_length, List.length_ofFn]
          rw [← hlen]
          exact getD_append_singleton_self _ _ false
  have inv_step_aux : ∀ (pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
      (res : (Bool ⊕ ℕ) × List Gate),
      Inv pre st →
      (∃ extra : List Gate, res.2 = st.2 ++ extra ∧ extra.length ≤ 1 ∧
        ((g.inputs.length ≠ 2 ∨ ∃ u ∈ g.inputs, n + pre.length ≤ u) → extra = [])) →
      IsAO2 n ⟨res.2, 0⟩ →
      repBound (n + res.2.length) res.1 →
      (∀ x : Fin n → Bool,
        ∃ tail : List Bool, evalGates res.2 (List.ofFn x) = evalGates st.2 (List.ofFn x) ++ tail) →
      (∀ x : Fin n → Bool,
        repVal (evalGates res.2 (List.ofFn x)) res.1 =
          g.op.eval (g.inputs.map fun i => (evalGates pre (List.ofFn x)).getD i false)) →
      Inv (pre ++ [g]) (st.1 ++ [res.1], res.2) := by
    intro pre st g res hinv hex hao hrb htail hval
    rcases hinv with ⟨h1, h2, hbad, _, h4, h5⟩
    rcases hex with ⟨extra, hres2, hexLen, hexZero⟩
    have hlen_le : st.2.length ≤ res.2.length := by rw [hres2, List.length_append]; omega
    refine ⟨?_, ?_, ?_, hao, ?_, ?_⟩
    · simp [h1]; omega
    · rw [hres2, List.length_append, List.length_append, List.length_singleton]; omega
    · intro hbad'
      rcases hbad' with ⟨j, hj, hcond⟩
      have hj' : j < pre.length + 1 := by simpa using hj
      by_cases hjp : j < pre.length
      · have hget : (pre ++ [g]).getD j ⟨GateOp.or, []⟩ = pre.getD j ⟨GateOp.or, []⟩ :=
          getD_append_left pre [g] j ⟨GateOp.or, []⟩ hjp
        rw [hget] at hcond
        have hlt := hbad ⟨j, hjp, hcond⟩
        rw [hres2, List.length_append, List.length_append, List.length_singleton]
        omega
      · have hjeq : j = pre.length := by omega
        subst hjeq
        have hget : (pre ++ [g]).getD pre.length ⟨GateOp.or, []⟩ = g :=
          getD_append_singleton_self pre g ⟨GateOp.or, []⟩
        rw [hget] at hcond
        have hzero := hexZero hcond
        rw [hres2, hzero, List.append_nil, List.length_append, List.length_singleton]
        omega
    · intro w
      by_cases hw : w < st.1.length
      · rw [getD_append_left st.1 [res.1] w (Sum.inl false) hw]
        exact repBound_mono (by dsimp only; omega) (h4 w)
      · by_cases heq : w = st.1.length
        · subst heq
          rw [getD_append_singleton_self]
          exact hrb
        · have hge : (st.1 ++ [res.1]).length ≤ w := by simp; omega
          rw [getD_of_le _ _ _ hge]
          trivial
    · intro x w
      have hprelen : (evalGates pre (List.ofFn x)).length = n + pre.length := by
        rw [evalGates_length, List.length_ofFn]
      have houtlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
        rw [evalGates_length, List.length_ofFn]
      rw [evalGates_append_singleton]
      dsimp only [wireStep]
      by_cases hw : w < n + pre.length
      · have hw1 : w < (evalGates pre (List.ofFn x)).length := by omega
        have hw2 : w < st.1.length := by omega
        rw [getD_append_left _ _ w false hw1, getD_append_left _ _ w (Sum.inl false) hw2]
        obtain ⟨tail, htx⟩ := htail x
        rw [htx, repVal_append _ tail _ (by rw [houtlen]; exact h4 w)]
        exact h5 x w
      · by_cases heq : w = n + pre.length
        · subst heq
          have h1' : (evalGates pre (List.ofFn x)).length = n + pre.length := hprelen
          rw [← h1', getD_append_singleton_self, h1', ← h1, getD_append_singleton_self]
          exact (hval x).symm
        · have hge1 : (evalGates pre (List.ofFn x) ++
              [g.op.eval (g.inputs.map fun i => (evalGates pre (List.ofFn x)).getD i false)]).length ≤ w := by
            rw [List.length_append, List.length_singleton, hprelen]; omega
          have hge2 : (st.1 ++ [res.1]).length ≤ w := by simp [h1]; omega
          rw [getD_of_le _ _ false hge1, getD_of_le _ _ (Sum.inl false) hge2]
          rfl
  have inv_step : ∀ (pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate),
      (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      Inv pre st →
      Inv (pre ++ [g]) (stepGate st g) := by
    intro pre st g hg hinvFull
    rcases hg with ⟨hop, hlen⟩
    have hinv := hinvFull
    rcases hinv with ⟨h1, h2, hbad, h3, h4, h5⟩
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    rcases hop' with hop | hop
    · cases hins : g.inputs with
      | nil =>
        have hst : stepGate st g = (st.1 ++ [Sum.inl true], st.2) := by
          dsimp only [stepGate]; rw [hop, hins]
        rw [hst]
        refine inv_step_aux pre st g (Sum.inl true, st.2) hinvFull
          ⟨[], by simp, by simp, fun _ => rfl⟩ h3 trivial (fun _ => ⟨[], by simp⟩) ?_
        intro x; rw [hop, hins]; rfl
      | cons i rest =>
        cases rest with
        | nil =>
          have hst : stepGate st g = (st.1 ++ [st.1.getD i (Sum.inl false)], st.2) := by
            dsimp only [stepGate]; rw [hop, hins]
          rw [hst]
          refine inv_step_aux pre st g (st.1.getD i (Sum.inl false), st.2) hinvFull
            ⟨[], by simp, by simp, fun _ => rfl⟩ h3 (h4 i) (fun _ => ⟨[], by simp⟩) ?_
          intro x
          rw [hop, hins]
          change repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) =
            ((evalGates pre (List.ofFn x)).getD i false && true)
          rw [Bool.and_true]
          exact (h5 x i).symm
        | cons j rest2 =>
          cases rest2 with
          | nil =>
            have hst : stepGate st g =
                (st.1 ++ [(combineAnd st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).1],
                 (combineAnd st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).2) := by
              dsimp only [stepGate]; rw [hop, hins]
            rw [hst]
            have hc := combineAnd_spec st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))
              h3 (h4 i) (h4 j)
            rcases hc with ⟨⟨extra, hex1, hex2, hexZ⟩, hc2, hc3, hc4⟩
            refine inv_step_aux pre st g _ hinvFull
              ⟨extra, hex1, hex2, ?_⟩ hc2 hc3 (fun x => (hc4 x).1) ?_
            · rintro (hne | ⟨u, hu, hge⟩)
              · simp [hins] at hne
              · rw [hins] at hu
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl
                · exact hexZ (Or.inl (getD_of_le _ _ _ (by omega)))
                · exact hexZ (Or.inr (getD_of_le _ _ _ (by omega)))
            · intro x
              rw [(hc4 x).2, hop, hins]
              change (repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) &&
                repVal (evalGates st.2 (List.ofFn x)) (st.1.getD j (Sum.inl false))) =
                ((evalGates pre (List.ofFn x)).getD i false &&
                 ((evalGates pre (List.ofFn x)).getD j false && true))
              rw [Bool.and_true, h5 x i, h5 x j]
          | cons k rest3 =>
            simp [hins] at hlen
    · cases hins : g.inputs with
      | nil =>
        have hst : stepGate st g = (st.1 ++ [Sum.inl false], st.2) := by
          dsimp only [stepGate]; rw [hop, hins]
        rw [hst]
        refine inv_step_aux pre st g (Sum.inl false, st.2) hinvFull
          ⟨[], by simp, by simp, fun _ => rfl⟩ h3 trivial (fun _ => ⟨[], by simp⟩) ?_
        intro x; rw [hop, hins]; rfl
      | cons i rest =>
        cases rest with
        | nil =>
          have hst : stepGate st g = (st.1 ++ [st.1.getD i (Sum.inl false)], st.2) := by
            dsimp only [stepGate]; rw [hop, hins]
          rw [hst]
          refine inv_step_aux pre st g (st.1.getD i (Sum.inl false), st.2) hinvFull
            ⟨[], by simp, by simp, fun _ => rfl⟩ h3 (h4 i) (fun _ => ⟨[], by simp⟩) ?_
          intro x
          rw [hop, hins]
          change repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) =
            ((evalGates pre (List.ofFn x)).getD i false || false)
          rw [Bool.or_false]
          exact (h5 x i).symm
        | cons j rest2 =>
          cases rest2 with
          | nil =>
            have hst : stepGate st g =
                (st.1 ++ [(combineOr st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).1],
                 (combineOr st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).2) := by
              dsimp only [stepGate]; rw [hop, hins]
            rw [hst]
            have hc := combineOr_spec st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))
              h3 (h4 i) (h4 j)
            rcases hc with ⟨⟨extra, hex1, hex2, hexZ⟩, hc2, hc3, hc4⟩
            refine inv_step_aux pre st g _ hinvFull
              ⟨extra, hex1, hex2, ?_⟩ hc2 hc3 (fun x => (hc4 x).1) ?_
            · rintro (hne | ⟨u, hu, hge⟩)
              · simp [hins] at hne
              · rw [hins] at hu
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl
                · exact hexZ (Or.inl (getD_of_le _ _ _ (by omega)))
                · exact hexZ (Or.inr (getD_of_le _ _ _ (by omega)))
            · intro x
              rw [(hc4 x).2, hop, hins]
              change (repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) ||
                repVal (evalGates st.2 (List.ofFn x)) (st.1.getD j (Sum.inl false))) =
                ((evalGates pre (List.ofFn x)).getD i false ||
                 ((evalGates pre (List.ofFn x)).getD j false || false))
              rw [Bool.or_false, h5 x i, h5 x j]
          | cons k rest3 =>
            simp [hins] at hlen
  have inv_init : Inv [] initState := by
    refine ⟨by simp [initState], by simp [initState], ?_, ?_, ?_, ?_⟩
    · rintro ⟨j, hj, _⟩; simp at hj
    · refine ⟨by intro g hg; simp [initState] at hg,
              by intro j hj; simp [initState] at hj,
              by intro g hg; simp [initState] at hg⟩
    · intro w
      dsimp only [initState]
      by_cases hw : w < n
      · have hlt : w < (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length := by
          simp [hw]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
        simpa [repBound] using hw
      · have hge : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by
          simp; omega
        rw [getD_of_le _ _ _ hge]
        trivial
    · intro x w
      dsimp only [initState, evalGates]
      rw [List.foldl_nil]
      by_cases hw : w < n
      · have hlt2 : w < (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length := by
          simp [hw]
        have hget : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).getD w (Sum.inl false) = Sum.inr w := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2, Option.getD_some, List.getElem_ofFn]
        rw [hget]
        rfl
      · have hge1 : (List.ofFn x).length ≤ w := by simp; omega
        have hge2 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by
          simp; omega
        rw [getD_of_le _ _ _ hge1, getD_of_le _ _ _ hge2]
        rfl
  have inv_foldl : ∀ (rest pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      Inv pre st →
      Inv (pre ++ rest) (rest.foldl stepGate st) := by
    intro rest
    induction rest with
    | nil => intro pre st _ hinv; simpa using hinv
    | cons g rest ih =>
      intro pre st hm hinv
      have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hm g (by simp)
      have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hm g' (by simp [hg'])
      have hstep : Inv (pre ++ [g]) (stepGate st g) := inv_step pre st g hg hinv
      have hrec := ih (pre ++ [g]) (stepGate st g) hrest hstep
      simpa [List.append_assoc] using hrec
  let st := C.gates.foldl stepGate initState
  have hinv : Inv C.gates st := by
    simpa using inv_foldl C.gates [] initState hMin.1 inv_init
  rcases hinv with ⟨_, hsz_le, hbad, hao, _, hev⟩
  have hexD : ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size = st.2.length := by
    have hao_mono : ∀ out, Monotone2 ⟨st.2, out⟩ := by
      intro out g hg
      have h1 := hao.1 g hg
      have h2 := hao.2.2 g hg
      refine ⟨?_, by omega⟩
      rcases h1 with h | h <;> simp [h]
    cases hr : st.1.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | true =>
        have h0 := hev (fun _ : Fin n => Bool.false) C.output
        rw [hr] at h0
        simp only [repVal] at h0
        have hc : C.eval (List.ofFn (fun _ : Fin n => Bool.false)) = Bool.true := h0
        rw [hCfalse] at hc
        exact Bool.noConfusion hc
      | false =>
        refine ⟨⟨st.2, n + st.2.length⟩, hao_mono _, ?_, rfl⟩
        funext x
        have hx := hev x C.output
        rw [hr] at hx
        simp only [repVal] at hx
        have hlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
          rw [evalGates_length, List.length_ofFn]
        have hout : Circuit.eval ⟨st.2, n + st.2.length⟩ (List.ofFn x) = Bool.false := by
          change (evalGates st.2 (List.ofFn x)).getD (n + st.2.length) false = false
          rw [← hlen]
          exact getD_of_le _ _ false (Nat.le_refl _)
        exact hout.trans hx.symm
    | inr k =>
      refine ⟨⟨st.2, k⟩, hao_mono k, ?_, rfl⟩
      funext x
      have hx := hev x C.output
      rw [hr] at hx
      simp only [repVal] at hx
      exact hx.symm
  obtain ⟨D, hDmono, hDfun, hDsz⟩ := hexD
  have hnotBad : ¬ Bad C.gates := by
    intro hb
    have hlt := hbad hb
    have hle := hMin.2 D hDmono hDfun
    change C.gates.length ≤ D.gates.length at hle
    change D.gates.length = st.2.length at hDsz
    omega
  have hAO_C : IsAO2 n C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      have h1 := (hMin.1 g hg).1
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
    · intro j hj u hu
      by_contra hge
      push Not at hge
      apply hnotBad
      refine ⟨j, hj, Or.inr ⟨u, ?_, hge⟩⟩
      exact hu
    · intro g hg
      rw [List.mem_iff_getElem] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      by_contra hne
      apply hnotBad
      refine ⟨j, hj, Or.inl ?_⟩
      have hget : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      rw [hget]
      exact hne
  refine ⟨hAO_C, hF, ?_⟩
  intro E hEao hEf
  have hEmono : Monotone2 E := by
    intro g hg
    refine ⟨?_, by have := hEao.2.2 g hg; omega⟩
    rcases hEao.1 g hg with h | h <;> simp [h]
  exact hMin.2 E hEmono (hEf.trans hF.symm)

end PEqualNP.Outside.L_meta_8875


theorem PEqualNP.Outside.L_meta_8875 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2.edgeFinset.Nonempty →     PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 →       PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →         have x8 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 : ℕ | x9 < x8.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → ¬PEqualNP.EdgeOwnership.Owns x1 x8 x9 x10 x11}.ncard;         ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x9 ∧ PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x9.size ≤ x4.size ∧ PEqualNP.TopForm.TopForm x2 x9 ∧ x8 x9 ≤ x8 x4 := by
  intro n G _ C hE hMin hF
  dsimp only
  have hL : PEqualNP.TopForm.IsLeastAO G C :=
    PEqualNP.Outside.L_meta_8875.isMinimalMono_isLeastAO G C hMin hF
  obtain ⟨C', hL', hsz', hun', hTF'⟩ :=
    PEqualNP.Outside.L_meta_8875.main_aux G hE (PEqualNP.Outside.L_meta_8875.andIndexSum C) C rfl hL
  exact ⟨C', hL'.1, hL'.2.1, le_of_eq hsz', hTF', hun'⟩
