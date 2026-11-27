import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2780
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem all_false (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ U : List Bool, (∀ i, U.getD i false = false) → ∀ i, (wf gs U).getD i false = false := by
  induction gs with
  | nil => intro U h i; exact h i
  | cons g gs ih =>
    intro U h i
    rw [wf_cons]
    refine ih (fun g' hg' => hleg g' (by simp [hg'])) _ ?_ i
    intro t
    obtain ⟨hop, hlen⟩ := hleg g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false) = false := by
      rw [hab]
      simp only [List.map_cons, List.map_nil, h]
      rcases hop with h' | h' <;> rw [h'] <;> rfl
    rw [hv]
    rcases Nat.lt_trichotomy t U.length with ht | ht | ht
    · rw [getD_snoc_lt _ _ _ ht]; exact h t
    · subst ht; rw [getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ ht]

theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _

theorem rep_false (n i : ℕ) : (List.replicate n false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem to_true (B : List Bool) (n : ℕ) (hB : B.length = n) (i : ℕ) :
    B.getD i false = true → (List.replicate n true).getD i false = true := by
  intro h
  have hi : i < n := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h
    exact absurd h (by simp)
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hi]

theorem from_false (B : List Bool) (n i : ℕ) :
    (List.replicate n false).getD i false = true → B.getD i false = true := by
  intro h
  rw [rep_false] at h
  exact absurd h (by simp)

theorem sandL (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (n w : ℕ)
    (h : ∀ x6 : Fin n → Bool, (wf gs (List.ofFn x6 ++ List.replicate n false)).getD w false
      = (wf gs (List.ofFn x6 ++ List.replicate n true)).getD w false)
    (A B : List Bool) (x6 : Fin n → Bool) (hA : A = List.ofFn x6) (hB : B.length = n) :
    (wf gs (A ++ B)).getD w false = (wf gs (A ++ List.replicate n false)).getD w false := by
  have lo_mid := mono2 gs hleg (A ++ List.replicate n false) (A ++ B) (by simp [hB])
    (app_mono A A _ B rfl (fun _ => id) (from_false B n)) w
  have mid_hi := mono2 gs hleg (A ++ B) (A ++ List.replicate n true) (by simp [hB])
    (app_mono A A B _ rfl (fun _ => id) (to_true B n hB)) w
  have e := h x6
  rw [← hA] at e
  cases hl : (wf gs (A ++ List.replicate n false)).getD w false
  · by_contra hne
    have hm : (wf gs (A ++ B)).getD w false = true := by simpa using hne
    have := mid_hi hm
    rw [← e, hl] at this
    exact absurd this (by simp)
  · exact lo_mid hl

theorem sandP (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (n w : ℕ)
    (h : ∀ x6 : Fin n → Bool, (wf gs (List.replicate n false ++ List.ofFn x6)).getD w false
      = (wf gs (List.replicate n true ++ List.ofFn x6)).getD w false)
    (A B : List Bool) (x6 : Fin n → Bool) (hB : B = List.ofFn x6) (hA : A.length = n) :
    (wf gs (A ++ B)).getD w false = (wf gs (List.replicate n false ++ B)).getD w false := by
  have lo_mid := mono2 gs hleg (List.replicate n false ++ B) (A ++ B) (by simp [hA])
    (app_mono _ A B B (by simp [hA]) (from_false A n) (fun _ => id)) w
  have mid_hi := mono2 gs hleg (A ++ B) (List.replicate n true ++ B) (by simp [hA])
    (app_mono A _ B B (by simp [hA]) (to_true A n hA) (fun _ => id)) w
  have e := h x6
  rw [← hB] at e
  cases hl : (wf gs (List.replicate n false ++ B)).getD w false
  · by_contra hne
    have hm : (wf gs (A ++ B)).getD w false = true := by simpa using hne
    have := mid_hi hm
    rw [← e, hl] at this
    exact absurd this (by simp)
  · exact lo_mid hl

end PEqualNP.Outside.L_meta_2780

open PEqualNP.Outside.L_meta_2780 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2780 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.false) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.true) x4) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.false ++ List.ofFn x6) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.true ++ List.ofFn x6) x4); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x2 + x2) x3 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x1 x2 x3 x7 → x6 ∈ x4) → ∀ x7 < x3.size, x7 ∉ x4 → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Finset (Fin x2) → Bool) (x12 : Finset (Fin x2) → Bool), ∀ (x13 x14 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x3 (PEqualNP.GenericRejection.incidenceInput x13 x14) (x2 + x2 + x7) = (x11 x13 && x12 x14) := by
  intro P n C T hC hT k hk hkT hop
  obtain ⟨hao, hrb, h2⟩ := hC
  have hk' : k < C.gates.length := hk
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk']
  rw [hG] at hop
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hleg : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => ⟨hao g' hg', le_of_eq (h2 g' hg')⟩
  have hleg2 : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
    fun g' hg' => ⟨hao g' hg', h2 g' hg'⟩
  have hlt : ∀ i ∈ [a, b], i < n + n + k := by
    intro i hi
    have := hrb k hk' i
    rw [hG, hin] at this
    exact this hi
  have hnot : ¬ (C.gates[k].op = GateOp.and ∧ ((∀ x4 ∈ C.gates[k].inputs, ∃ (x6 : Fin n → Bool), wireValue C (List.ofFn x6 ++ List.replicate n Bool.false) x4 ≠ wireValue C (List.ofFn x6 ++ List.replicate n Bool.true) x4) ∨ ∀ x4 ∈ C.gates[k].inputs, ∃ (x6 : Fin n → Bool), wireValue C (List.replicate n Bool.false ++ List.ofFn x6) x4 ≠ wireValue C (List.replicate n Bool.true ++ List.ofFn x6) x4)) :=
    fun h => hkT (hT k C.gates[k] (List.getElem?_eq_getElem hk') h)
  obtain ⟨hA, hB⟩ := not_or.mp (fun h => hnot ⟨hop, h⟩)
  push_neg at hA hB
  obtain ⟨i, hi, hLi⟩ := hA
  obtain ⟨i', hi', hPi⟩ := hB
  rw [hin] at hi hi'
  have gv : ∀ X Y : Finset (Fin n), (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD (n + n + k) false
      = ((wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD a false
        && (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD b false) := by
    intro X Y
    have hlen : (PEqualNP.GenericRejection.incidenceInput X Y).length = n + n := by
      simp [PEqualNP.GenericRejection.incidenceInput]
    have g1 := gate_val C.gates (PEqualNP.GenericRejection.incidenceInput X Y) k hk'
    rw [hlen, hin, hop] at g1
    rw [g1, wire_take C.gates _ k a (by rw [hlen]; exact hlt a (by simp)) (le_of_lt hk'),
      wire_take C.gates _ k b (by rw [hlen]; exact hlt b (by simp)) (le_of_lt hk')]
    simp [GateOp.eval]
  have sL : ∀ w, (∀ x6 : Fin n → Bool, wireValue C (List.ofFn x6 ++ List.replicate n Bool.false) w = wireValue C (List.ofFn x6 ++ List.replicate n Bool.true) w) →
      ∀ X Y : Finset (Fin n), (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD w false
        = (wf C.gates (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.replicate n false)).getD w false := by
    intro w h X Y
    exact sandL C.gates hleg n w h _ _ (fun p : Fin n => decide (p ∈ X)) rfl (by simp)
  have sP : ∀ w, (∀ x6 : Fin n → Bool, wireValue C (List.replicate n Bool.false ++ List.ofFn x6) w = wireValue C (List.replicate n Bool.true ++ List.ofFn x6) w) →
      ∀ X Y : Finset (Fin n), (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD w false
        = (wf C.gates (List.replicate n false ++ List.ofFn (fun l : Fin n => decide (l ∈ Y)))).getD w false := by
    intro w h X Y
    exact sandP C.gates hleg n w h _ _ (fun l : Fin n => decide (l ∈ Y)) rfl (by simp)
  have zero : ∀ w, (∀ x6 : Fin n → Bool, wireValue C (List.ofFn x6 ++ List.replicate n Bool.false) w = wireValue C (List.ofFn x6 ++ List.replicate n Bool.true) w) →
      (∀ x6 : Fin n → Bool, wireValue C (List.replicate n Bool.false ++ List.ofFn x6) w = wireValue C (List.replicate n Bool.true ++ List.ofFn x6) w) →
      ∀ X Y : Finset (Fin n), (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD w false = false := by
    intro w h1 h2' X Y
    rw [sL w h1 X Y, ← sL w h1 X ∅, sP w h2' X ∅, ← sP w h2' ∅ ∅]
    refine all_false C.gates hleg2 _ ?_ w
    intro t
    rw [List.getD_eq_getElem?_getD]
    cases ht : (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin n)) (∅ : Finset (Fin n)))[t]? with
    | none => rfl
    | some v =>
      have hm := List.mem_of_getElem? ht
      simp [PEqualNP.GenericRejection.incidenceInput] at hm
      simp [hm]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hi'
  rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
  · refine ⟨fun _ => false, fun _ => false, fun X Y => ?_⟩
    show (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD (n + n + k) false = _
    rw [gv, zero _ hLi hPi]
    rfl
  · refine ⟨fun X => (wf C.gates (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.replicate n false)).getD i false,
      fun Y => (wf C.gates (List.replicate n false ++ List.ofFn (fun l : Fin n => decide (l ∈ Y)))).getD i' false, fun X Y => ?_⟩
    show (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD (n + n + k) false = _
    rw [gv, sL _ hLi, sP _ hPi]
  · refine ⟨fun X => (wf C.gates (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.replicate n false)).getD i false,
      fun Y => (wf C.gates (List.replicate n false ++ List.ofFn (fun l : Fin n => decide (l ∈ Y)))).getD i' false, fun X Y => ?_⟩
    show (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD (n + n + k) false = _
    rw [gv, sL _ hLi, sP _ hPi, Bool.and_comm]
  · refine ⟨fun _ => false, fun _ => false, fun X Y => ?_⟩
    show (wf C.gates (PEqualNP.GenericRejection.incidenceInput X Y)).getD (n + n + k) false = _
    rw [gv, zero _ hLi hPi, Bool.and_false]
    rfl
