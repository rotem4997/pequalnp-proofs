import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18715

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

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
  rw [gateAt_eq hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (C := C) (j := j) (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (C := C) (j := j + 1) (by omega)]

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
  rw [hval, gateAt_eq hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq hj] at hu
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

private theorem keepNodup {n k : ℕ} {C : Circuit} (nd : ∀ g ∈ C.gates, g.inputs.Nodup)
    (no : ∀ j < C.gates.length, n+k ∉ (gateAt C j).inputs) :
    ∀ g ∈ (delDead n k C).gates, g.inputs.Nodup := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  have hq' := List.mem_of_mem_eraseIdx hq
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hq'
  have hgate : gateAt C j = q := (gateAt_eq hj).trans eq
  have safe : n+k ∉ q.inputs := hgate ▸ no j hj
  apply (nd q hq').map_on
  intro a ha b hb equal
  have aNe : a ≠ n+k := fun e => safe (e ▸ ha)
  have bNe : b ≠ n+k := fun e => safe (e ▸ hb)
  simpa only [unshiftW_shiftW n k a aNe, unshiftW_shiftW n k b bNe] using
    congrArg (unshiftW n k) equal

end PEqualNP.Outside.L_meta_18715

open PEqualNP.Outside.L_meta_18715 PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18715 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), x1.size = (65 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → x1.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } → (∃ x8 < (64 : ℕ), ∀ x9 < (65 : ℕ), x8 < x9 → (26 : ℕ) + x8 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).inputs) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) (x11 : ℕ), x9.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x12 ∈ x9.gates, x12.inputs.Nodup) ∧ x10 ≠ x11 ∧ x10 < (26 : ℕ) + x9.size ∧ x11 < (26 : ℕ) + x9.size ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x12 x2 ∧ PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x12 x3 := by
  intro C a b size ao nd final existsDead
  obtain ⟨k, klt, dead⟩ := existsDead
  change C.gates.length = 65 at size
  have hk : k < C.gates.length := by omega
  have hl : 64 < C.gates.length := by omega
  have lastGate : gateAt C 64 = ⟨.and,[a,b]⟩ := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD,final]
  have ha : a ∈ (gateAt C 64).inputs := by simp [lastGate]
  have hb : b ∈ (gateAt C 64).inputs := by simp [lastGate]
  have aLt := ao.2.1 64 hl a ha
  have bLt := ao.2.1 64 hl b hb
  have no : ∀ j < C.gates.length, 26+k ∉ (gateAt C j).inputs := by
    intro j hj mem
    by_cases h : k < j
    · exact dead j (by omega) h mem
    · have := ao.2.1 j hj (26+k) mem
      omega
  have aNe : a ≠ 26+k := fun h => no 64 hl (h ▸ ha)
  have bNe : b ≠ 26+k := fun h => no 64 hl (h ▸ hb)
  have ab : a ≠ b := by
    have h := nd _ (gateAt_mem hl)
    simpa [lastGate] using h
  let E := delDead 26 k C
  let i := shiftW 26 k a
  let j := shiftW 26 k b
  have len : E.gates.length = 64 := by rw [delDead_length 26 k C hk, size]
  have he : PEqualNP.TopForm.IsAO2 26 E := delDead_ao2 ao hk no
  have ndE : ∀ g ∈ E.gates, g.inputs.Nodup := keepNodup nd no
  have iLt : i < 26+63 := by dsimp [i,shiftW]; split_ifs <;> omega
  have jLt : j < 26+63 := by dsimp [j,shiftW]; split_ifs <;> omega
  have ij : i ≠ j := by
    intro eq
    apply ab
    simpa only [i,j,unshiftW_shiftW 26 k a aNe, unshiftW_shiftW 26 k b bNe] using
      congrArg (unshiftW 26 k) eq
  have last : 63 < E.gates.length := by omega
  have noLast : ∀ t < E.gates.length, 26+63 ∉ (gateAt E t).inputs := by
    intro t ht mem
    have := he.2.1 t ht (26+63) mem
    omega
  let D := delDead 26 63 E
  have dsize : D.size = 63 := by
    change (delDead 26 63 E).gates.length = 63
    rw [delDead_length 26 63 E last, len]
  refine ⟨D,i,j,by omega, delDead_ao2 he last noLast, keepNodup ndE noLast,
    ij,by omega,by omega,fun x => ?_⟩
  have obs (w : ℕ) (hw : w ≠ 26+k) (bound : shiftW 26 k w < 26+63) :
      PEqualNP.BlindGate.wireValue D 26 x (shiftW 26 k w) =
        PEqualNP.BlindGate.wireValue C 26 x w := by
    unfold PEqualNP.BlindGate.wireValue
    rw [delDead_wires_eq 26 63 E _ List.length_ofFn he.2.1 last noLast]
    rw [show unshiftW 26 63 (shiftW 26 k w) = shiftW 26 k w from ite_eq_left bound]
    rw [delDead_wires_eq 26 k C _ List.length_ofFn ao.2.1 hk no, unshiftW_shiftW 26 k w hw]
  exact ⟨obs a aNe iLt,obs b bNe jLt⟩
