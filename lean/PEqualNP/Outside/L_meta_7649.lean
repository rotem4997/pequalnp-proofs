import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7649

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CircuitMoves

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

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireValue_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = x ⟨w, hw⟩ := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireValue_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    PEqualNP.BlindGate.wireValue C n x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => PEqualNP.BlindGate.wireValue C n x u) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, PEqualNP.BlindGate.wireValue C n x u = acc.getD u false := by
    intro u hu
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : PEqualNP.BlindGate.wireValue C n x (n + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
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

lemma list_eq_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => exact ⟨a, b, rfl⟩
      | cons _ _ => simp at h

lemma gate_inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
  rcases list_eq_two hlen with ⟨a, b, hab⟩
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact hAO.2.1 j hj a (by simp [hab])
  · exact hAO.2.1 j hj b (by simp [hab])

lemma wireValue_and_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a && PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

lemma wireValue_or_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a || PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

lemma merge_bound {α : Type*} [DecidableEq α]
    (f : ℕ → Finset α) (M : Finset ℕ)
    (hBase : ∀ w, w ∉ M → (f w).card ≤ 1)
    (hStep : ∀ m ∈ M, f m = ∅ ∨ (∃ a < m, f m ⊆ f a) ∨ (∃ a < m, ∃ b < m, f m ⊆ f a ∪ f b)) :
    ∀ B : ℕ, ∀ R : Finset ℕ, (∀ r ∈ R, r < B) →
      (R.biUnion f).card ≤ R.card + (M.filter (· < B)).card := by
  intro B
  induction B with
  | zero =>
    intro R hR
    have hRe : R = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]
      intro hr; have := hR r hr; omega
    subst hRe; simp
  | succ B ih =>
    intro R hR
    have hMsub : (M.filter (· < B)).card ≤ (M.filter (· < B + 1)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    by_cases hBR : B ∈ R
    · let R0 := R.erase B
      have hR0lt : ∀ r ∈ R0, r < B := by
        intro r hr
        have hr1 := Finset.mem_erase.mp hr
        have hr2 := hR r hr1.2
        omega
      have hR0card : R0.card + 1 = R.card := Finset.card_erase_add_one hBR
      have hRins : R = insert B R0 := (Finset.insert_erase hBR).symm
      by_cases hBM : B ∈ M
      · have hMfilt : (M.filter (· < B + 1)).card = (M.filter (· < B)).card + 1 := by
          have heq : M.filter (· < B + 1) = insert B (M.filter (· < B)) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hxM, hxlt⟩
              by_cases hxB : x = B
              · exact Or.inl hxB
              · exact Or.inr ⟨hxM, by omega⟩
            · rintro (rfl | ⟨hxM, hxlt⟩)
              · exact ⟨hBM, by omega⟩
              · exact ⟨hxM, by omega⟩
          rw [heq, Finset.card_insert_of_notMem]
          simp
        rcases hStep B hBM with hEmpty | ⟨a, haB, hfa⟩ | ⟨a, haB, b, hbB, hfab⟩
        · have hsub : R.biUnion f ⊆ R0.biUnion f := by
            rw [hRins, Finset.biUnion_insert, hEmpty, Finset.empty_union]
          have h1 := Finset.card_le_card hsub
          have h2 := ih R0 hR0lt
          omega
        · let R' := insert a R0
          have hR'lt : ∀ r ∈ R', r < B := by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr0
            · exact haB
            · exact hR0lt r hr0
          have hsub : R.biUnion f ⊆ R'.biUnion f := by
            rw [hRins, Finset.biUnion_insert, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hfa
          have h1 := Finset.card_le_card hsub
          have h2 := ih R' hR'lt
          have h3 : R'.card ≤ R0.card + 1 := Finset.card_insert_le a R0
          omega
        · let R' := insert a (insert b R0)
          have hR'lt : ∀ r ∈ R', r < B := by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr1
            · exact haB
            · rcases Finset.mem_insert.mp hr1 with rfl | hr0
              · exact hbB
              · exact hR0lt r hr0
          have hsub : R.biUnion f ⊆ R'.biUnion f := by
            rw [hRins, Finset.biUnion_insert, Finset.biUnion_insert, Finset.biUnion_insert,
              ← Finset.union_assoc]
            exact Finset.union_subset_union_left hfab
          have h1 := Finset.card_le_card hsub
          have h2 := ih R' hR'lt
          have h3 : R'.card ≤ (insert b R0).card + 1 := Finset.card_insert_le a (insert b R0)
          have h4 : (insert b R0).card ≤ R0.card + 1 := Finset.card_insert_le b R0
          omega
      · have hBcard : (f B).card ≤ 1 := hBase B hBM
        have h1 : (R.biUnion f).card ≤ (f B).card + (R0.biUnion f).card := by
          rw [hRins, Finset.biUnion_insert]
          exact Finset.card_union_le _ _
        have h2 := ih R0 hR0lt
        omega
    · have hRlt : ∀ r ∈ R, r < B := by
        intro r hr
        have h1 := hR r hr
        have hne : r ≠ B := fun he => hBR (he ▸ hr)
        omega
      have h2 := ih R hRlt
      omega


def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  PEqualNP.BlindGate.wireValue C n x w

lemma wire_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (h : n + C.gates.length ≤ w) : wire C x w = false := by
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rwa [foldl_wireStep_length, List.length_ofFn]

def children (C : Circuit) (j : ℕ) : ℕ × ℕ :=
  (opnd C j 0, opnd C j 1)

lemma children_spec {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) :
    (gateAt C j).inputs = [(children C j).1, (children C j).2] ∧
      (children C j).1 < n + j ∧ (children C j).2 < n + j := by
  obtain ⟨a, b, hab, ha, hb⟩ := gate_inputs_two n C hAO j hj
  simpa [children, opnd, hab] using And.intro hab (And.intro ha hb)

def splitOr (n : ℕ) (C : Circuit) (w : ℕ) : Option (ℕ × ℕ) :=
  if w < n then none else
    match (gateAt C (w - n)).op with
    | .or => some (children C (w - n))
    | _ => none

def splitTop (n : ℕ) (C : Circuit) (w : ℕ) : Option (ℕ × ℕ) :=
  if w < n then none else
    let p := children C (w - n)
    match (gateAt C (w - n)).op with
    | .or => some p
    | .and =>
      if WireBelowOutput n C p.1 then some (p.1, p.1)
      else if WireBelowOutput n C p.2 then some (p.2, p.2)
      else none
    | _ => none

def atoms (step : ℕ → Option (ℕ × ℕ)) (w : ℕ) : Finset ℕ :=
  match step w with
  | none => {w}
  | some (a, b) =>
    if _h : a < w ∧ b < w then atoms step a ∪ atoms step b else {w}
termination_by w
decreasing_by all_goals omega

lemma atoms_stop {step : ℕ → Option (ℕ × ℕ)} {w : ℕ}
    (h : step w = none) : atoms step w = {w} := by
  rw [atoms, h]

lemma atoms_split {step : ℕ → Option (ℕ × ℕ)} {w a b : ℕ}
    (h : step w = some (a, b)) (ha : a < w) (hb : b < w) :
    atoms step w = atoms step a ∪ atoms step b := by
  rw [atoms, h]
  simp [ha, hb]

lemma atoms_nonempty (step : ℕ → Option (ℕ × ℕ)) (w : ℕ) :
    (atoms step w).Nonempty := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [atoms]
    split
    · simp
    · split
      · exact Finset.Nonempty.mono Finset.subset_union_left (ih _ (by omega))
      · simp

def Clean (n : ℕ) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
    ¬ WireBelowOutput n C (n + j) →
    g.op = .or ∧ ∀ w ∈ g.inputs, ¬ WireBelowOutput n C w

lemma gate_get {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [gateAt_eq_getElem C j hj, List.getElem?_eq_getElem hj]

lemma or_below_children {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hor : (gateAt C j).op = .or)
    (h : WireBelowOutput n C (n + j)) :
    WireBelowOutput n C (children C j).1 ∧ WireBelowOutput n C (children C j).2 := by
  have hp := (children_spec hAO hj).1
  constructor
  · intro x hx
    apply h x
    change wire C x (n + j) = true
    rw [wire, wireValue_or_pair n C hAO.2.1 j _ _ hj hor hp x]
    change wire C x (children C j).1 = true at hx
    rw [Bool.or_eq_true]
    exact Or.inl hx
  · intro x hx
    apply h x
    change wire C x (n + j) = true
    rw [wire, wireValue_or_pair n C hAO.2.1 j _ _ hj hor hp x]
    change wire C x (children C j).2 = true at hx
    rw [Bool.or_eq_true]
    exact Or.inr hx

lemma and_below {n : ℕ} {C : Circuit} (hc : Clean n C) {j : ℕ}
    (hj : j < C.gates.length) (hand : (gateAt C j).op = .and) :
    WireBelowOutput n C (n + j) := by
  by_contra hn
  have ho := (hc j _ (gate_get hj) hn).1
  rw [hand] at ho
  cases ho

lemma or_atoms_spec {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (hc : Clean n C) :
    ∀ w < n + C.gates.length, ¬ WireBelowOutput n C w →
      (∀ u ∈ atoms (splitOr n C) w, u < n) ∧
      (∀ x : Fin n → Bool, wire C x w = true ↔
        ∃ u ∈ atoms (splitOr n C) w, wire C x u = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnb
    by_cases h : w < n
    · rw [atoms_stop (show splitOr n C w = none by simp [splitOr, h])]
      simp [h]
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have he : w = n + j := by omega
      have hok := hc j _ (gate_get hj) (by rwa [← he])
      obtain ⟨hp, ha, hb⟩ := children_spec hAO hj
      have hs : splitOr n C w = some (children C j) := by simp [splitOr, h, hok.1, j]
      have hpa := ih _ (by omega : (children C j).1 < w) (by omega)
        (hok.2 _ (by simp [hp]))
      have hpb := ih _ (by omega : (children C j).2 < w) (by omega)
        (hok.2 _ (by simp [hp]))
      have hu := atoms_split hs (by omega : (children C j).1 < w)
        (by omega : (children C j).2 < w)
      rw [hu]
      refine ⟨fun u hu => (Finset.mem_union.mp hu).elim (hpa.1 u) (hpb.1 u), ?_⟩
      intro x
      conv_lhs => rw [he]
      rw [wire, wireValue_or_pair n C hAO.2.1 j _ _ hj hok.1 hp x, Bool.or_eq_true]
      change wire C x (children C j).1 = true ∨ wire C x (children C j).2 = true ↔ _
      rw [hpa.2, hpb.2]
      constructor
      · rintro (⟨u, hu, hval⟩ | ⟨u, hu, hval⟩)
        · exact ⟨u, Finset.mem_union_left _ hu, hval⟩
        · exact ⟨u, Finset.mem_union_right _ hu, hval⟩
      · rintro ⟨u, hu, hval⟩
        rcases Finset.mem_union.mp hu with hu | hu
        · exact Or.inl ⟨u, hu, hval⟩
        · exact Or.inr ⟨u, hu, hval⟩

lemma top_split_spec {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w a b : ℕ}
    (hw : w < n + C.gates.length) (hbelow : WireBelowOutput n C w)
    (hs : splitTop n C w = some (a, b)) :
    a < w ∧ b < w ∧ WireBelowOutput n C a ∧ WireBelowOutput n C b ∧
      ∀ x : Fin n → Bool, wire C x w = true → wire C x a = true ∨ wire C x b = true := by
  by_cases hn : w < n
  · simp [splitTop, hn] at hs
  let j := w - n
  have hwj : w = n + j := by omega
  have hj : j < C.gates.length := by omega
  obtain ⟨hp, ha, hb⟩ := children_spec hAO hj
  have hop := hAO.1 (gateAt C j) (by rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj)
  rcases hop with hand | hor
  · simp only [splitTop, hn, ↓reduceIte, (show w - n = j from rfl), hand] at hs
    have heval (x : Fin n → Bool) :
        wire C x w = (wire C x (children C j).1 && wire C x (children C j).2) := by
      rw [hwj]
      exact wireValue_and_pair n C hAO.2.1 j _ _ hj hand hp x
    split at hs
    · rename_i h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      exact ⟨by omega, by omega, h, h, fun x hx => by
          rw [heval, Bool.and_eq_true] at hx
          exact Or.inl hx.1⟩
    · split at hs
      · rename_i h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        exact ⟨by omega, by omega, h, h, fun x hx => by
            rw [heval, Bool.and_eq_true] at hx
            exact Or.inl hx.2⟩
      · cases hs
  · simp only [splitTop, hn, ↓reduceIte, (show w - n = j from rfl), hor] at hs
    have heq := Option.some.inj hs
    have hbc := or_below_children hAO hj hor (by rwa [← hwj])
    have hpa : (children C j).1 = a := congrArg Prod.fst heq
    have hpb : (children C j).2 = b := congrArg Prod.snd heq
    rw [← hpa, ← hpb]
    refine ⟨by omega, by omega, hbc.1, hbc.2, ?_⟩
    intro x hx
    rw [hwj] at hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_or_pair n C hAO.2.1 j _ _ hj hor hp x, Bool.or_eq_true] at hx
    exact hx

def IsTerm (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ j < C.gates.length, w = n + j ∧ (gateAt C j).op = .and ∧
    ¬ WireBelowOutput n C (children C j).1 ∧ ¬ WireBelowOutput n C (children C j).2

lemma top_atoms_spec {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (hInput : ∀ w < n, ¬ WireBelowOutput n C w) :
    ∀ w < n + C.gates.length, WireBelowOutput n C w →
      (∀ u ∈ atoms (splitTop n C) w, IsTerm n C u) ∧
      (∀ x : Fin n → Bool, wire C x w = true →
        ∃ u ∈ atoms (splitTop n C) w, wire C x u = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hb
    cases hs : splitTop n C w with
    | none =>
      rw [atoms_stop hs]
      refine ⟨?_, fun x hx => ⟨w, by simp, hx⟩⟩
      intro u hu
      rw [Finset.mem_singleton.mp hu]
      have hn : ¬ w < n := fun h => hInput w h hb
      let j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      have hop := hAO.1 (gateAt C j) (by rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj)
      rcases hop with hand | hor
      · simp only [splitTop, hn, ↓reduceIte, (show w - n = j from rfl), hand] at hs
        split at hs
        · cases hs
        · rename_i hn1
          split at hs
          · cases hs
          · rename_i hn2
            exact ⟨j, hj, hwj, hand, hn1, hn2⟩
      · simp [splitTop, hn, (show w - n = j from rfl), hor] at hs
    | some p =>
      rcases p with ⟨a, b⟩
      obtain ⟨ha, hb', hab, hbb, hval⟩ := top_split_spec hAO hw hb hs
      have hsa := ih a ha (by omega) hab
      have hsb := ih b hb' (by omega) hbb
      rw [atoms_split hs ha hb']
      refine ⟨fun u hu => (Finset.mem_union.mp hu).elim (hsa.1 u) (hsb.1 u), ?_⟩
      intro x hx
      rcases hval x hx with hxa | hxb
      · obtain ⟨u, hu, hv⟩ := hsa.2 x hxa
        exact ⟨u, Finset.mem_union_left _ hu, hv⟩
      · obtain ⟨u, hu, hv⟩ := hsb.2 x hxb
        exact ⟨u, Finset.mem_union_right _ hu, hv⟩


def EdgeLR {l r : ℕ} (R : Fin l → Fin r → Prop) (u v : ℕ) : Prop :=
  ∃ i : Fin l, ∃ j : Fin r, u = i.val ∧ v = l + j.val ∧ R i j

def Edge {l r : ℕ} (R : Fin l → Fin r → Prop) (u v : ℕ) : Prop :=
  EdgeLR R u v ∨ EdgeLR R v u

lemma edgeLR_bounds {l r : ℕ} {R : Fin l → Fin r → Prop} {u v : ℕ}
    (h : EdgeLR R u v) : u < l ∧ l ≤ v ∧ v < l + r := by
  obtain ⟨i, j, rfl, rfl, _⟩ := h
  have := i.isLt
  have := j.isLt
  omega

lemma edge_symm {l r : ℕ} {R : Fin l → Fin r → Prop} {u v : ℕ}
    (h : Edge R u v) : Edge R v u :=
  h.symm

lemma edge_bounds {l r : ℕ} {R : Fin l → Fin r → Prop} {u v : ℕ}
    (h : Edge R u v) : u < l + r ∧ v < l + r ∧ u ≠ v := by
  rcases h with hl | hr
  · obtain ⟨_, _, _⟩ := edgeLR_bounds hl
    omega
  · obtain ⟨_, _, _⟩ := edgeLR_bounds hr
    omega

lemma edge_side {l r : ℕ} {R : Fin l → Fin r → Prop} {u v : ℕ} (h : Edge R u v) :
    (u < l ∧ l ≤ v ∧ v < l + r) ∨ (l ≤ u ∧ u < l + r ∧ v < l) := by
  rcases h with h | h
  · exact Or.inl (edgeLR_bounds h)
  · obtain ⟨ha, hb, hc⟩ := edgeLR_bounds h
    exact Or.inr ⟨hb, hc, ha⟩

lemma edge_codes {l r : ℕ} {R : Fin l → Fin r → Prop} (i : Fin l) (j : Fin r) :
    Edge R i.val (l + j.val) ↔ R i j := by
  constructor
  · rintro (⟨i', j', hi, hj, hr⟩ | hr)
    · have ei : i = i' := Fin.ext hi
      have ej : j = j' := Fin.ext (by omega)
      simpa only [← ei, ← ej] using hr
    · have := (edgeLR_bounds hr).1
      omega
  · intro h
    exact Or.inl ⟨i, j, rfl, rfl, h⟩

lemma rect_first_left {l r : ℕ} {R : Fin l → Fin r → Prop}
    (hC4 : ∀ i i' j j', i ≠ i' → j ≠ j' → ¬ (R i j ∧ R i j' ∧ R i' j ∧ R i' j'))
    {u v a b : ℕ} (huv : u ≠ v) (hab : a ≠ b)
    (hua : EdgeLR R u a) (hub : Edge R u b) (hva : Edge R v a) (hvb : Edge R v b) :
    False := by
  obtain ⟨i, j, rfl, rfl, hij⟩ := hua
  have hv : v < l := by
    rcases hva with h | h
    · exact (edgeLR_bounds h).1
    · have := (edgeLR_bounds h).1
      omega
  have hdiag : EdgeLR R v b := by
    rcases hvb with h | h
    · exact h
    · have := (edgeLR_bounds h).2.1
      omega
  obtain ⟨i', j', rfl, rfl, hij'⟩ := hdiag
  exact hC4 i i' j j' (fun h => huv (congrArg Fin.val h))
    (fun h => hab (by rw [h])) ⟨hij, (edge_codes i j').mp hub, (edge_codes i' j).mp hva, hij'⟩

lemma no_rect {l r : ℕ} {R : Fin l → Fin r → Prop}
    (hC4 : ∀ i i' j j', i ≠ i' → j ≠ j' → ¬ (R i j ∧ R i j' ∧ R i' j ∧ R i' j'))
    {u v a b : ℕ} (huv : u ≠ v) (hab : a ≠ b)
    (hua : Edge R u a) (hub : Edge R u b) (hva : Edge R v a) (hvb : Edge R v b) :
    False := by
  rcases hua with h | h
  · exact rect_first_left hC4 huv hab h hub hva hvb
  · exact rect_first_left hC4 hab huv h (edge_symm hva) (edge_symm hub) (edge_symm hvb)

def Computes {l r : ℕ} (R : Fin l → Fin r → Prop) [DecidableRel R] (C : Circuit) : Prop :=
  ∀ x : Fin (l + r) → Bool, circuitFun (l + r) C x =
    decide (∃ i : Fin l, ∃ j : Fin r, R i j ∧
      x (Fin.castAdd r i) = true ∧ x (Fin.natAdd l j) = true)

def mark {n : ℕ} (u v : ℕ) (i : Fin n) : Bool :=
  decide (i.val = u ∨ i.val = v)

lemma output_mark {l r : ℕ} {R : Fin l → Fin r → Prop} [DecidableRel R] {C : Circuit}
    (hc : Computes R C) (u v : ℕ) :
    circuitFun (l + r) C (mark u v) = true ↔ Edge R u v := by
  rw [hc]
  simp only [mark, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd]
  constructor
  · rintro ⟨i, j, hr, hi, hj⟩
    have hne : i.val ≠ l + j.val := by have := i.isLt; omega
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hne (hi.trans hj.symm)).elim
    · exact Or.inl ⟨i, j, hi.symm, hj.symm, hr⟩
    · exact Or.inr ⟨i, j, hi.symm, hj.symm, hr⟩
    · exact (hne (hi.trans hj.symm)).elim
  · rintro (⟨i, j, hi, hj, hr⟩ | ⟨i, j, hi, hj, hr⟩)
    · exact ⟨i, j, hr, Or.inl hi.symm, Or.inr hj.symm⟩
    · exact ⟨i, j, hr, Or.inr hi.symm, Or.inl hj.symm⟩

lemma wire_mark {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) (u v : ℕ) :
    wire C (mark (n := n) u v) w = true ↔ w = u ∨ w = v := by
  change PEqualNP.BlindGate.wireValue C n (mark u v) w = true ↔ _
  rw [wireValue_input n C _ w hw]
  simp [mark]

lemma input_not_below {l r : ℕ} {R : Fin l → Fin r → Prop} [DecidableRel R] {C : Circuit}
    (hc : Computes R C) (w : ℕ) (hw : w < l + r) : ¬ WireBelowOutput (l + r) C w := by
  intro h
  have hv := (wire_mark C hw w w).2 (Or.inl rfl)
  have ho : circuitFun (l + r) C (mark w w) = true := h _ hv
  exact (edge_bounds ((output_mark hc w w).mp ho)).2.2 rfl

lemma biclique_star {l r : ℕ} {R : Fin l → Fin r → Prop}
    (hC4 : ∀ i i' j j', i ≠ i' → j ≠ j' → ¬ (R i j ∧ R i j' ∧ R i' j ∧ R i' j'))
    {A B : Finset ℕ} (ha : A.Nonempty) (hb : B.Nonempty)
    (h : ∀ u ∈ A, ∀ v ∈ B, Edge R u v) :
    (∃ c, A = {c} ∧ ∀ v ∈ B, Edge R c v) ∨
      (∃ c, B = {c} ∧ ∀ u ∈ A, Edge R c u) := by
  by_cases hcard : 1 < A.card
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨b, hb⟩ := hb
    refine Or.inr ⟨b, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hb),
      fun a ha' => edge_symm (h a ha' b hb)⟩
    intro a ha'
    apply Finset.mem_singleton.mpr
    by_contra hab
    exact no_rect hC4 huv hab (h u hu a ha') (h u hu b hb) (h v hv a ha') (h v hv b hb)
  · have hA : A.card = 1 := by have := Finset.card_pos.mpr ha; omega
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hA
    exact Or.inl ⟨c, rfl, h c (Finset.mem_singleton_self c)⟩

lemma term_star {l r : ℕ} {R : Fin l → Fin r → Prop} [DecidableRel R] {C : Circuit}
    (hC4 : ∀ i i' j j', i ≠ i' → j ≠ j' → ¬ (R i j ∧ R i j' ∧ R i' j ∧ R i' j'))
    (hAO : IsAO2 (l + r) C) (hc : Computes R C) (hclean : Clean (l + r) C)
    {w : ℕ} (hw : IsTerm (l + r) C w) :
    ∃ p : ℕ × ℕ,
      p.2 < l + r + C.gates.length ∧ ¬ WireBelowOutput (l + r) C p.2 ∧
      (∀ v ∈ atoms (splitOr (l + r) C) p.2, Edge R p.1 v) ∧
      ∀ x : Fin (l + r) → Bool, wire C x w = true →
        wire C x p.1 = true ∧ ∃ v ∈ atoms (splitOr (l + r) C) p.2, wire C x v = true := by
  obtain ⟨j, hj, rfl, hand, hna, hnb⟩ := hw
  obtain ⟨hp, ha, hb⟩ := children_spec hAO hj
  let a := (children C j).1
  let b := (children C j).2
  have hal : a < l + r + C.gates.length := by dsimp [a]; omega
  have hbl : b < l + r + C.gates.length := by dsimp [b]; omega
  obtain ⟨haIn, haVal⟩ := or_atoms_spec hAO hclean a hal hna
  obtain ⟨hbIn, hbVal⟩ := or_atoms_spec hAO hclean b hbl hnb
  have heval (x : Fin (l + r) → Bool) :
      wire C x (l + r + j) = (wire C x a && wire C x b) :=
    wireValue_and_pair (l + r) C hAO.2.1 j a b hj hand hp x
  have hedges : ∀ u ∈ atoms (splitOr (l + r) C) a,
      ∀ v ∈ atoms (splitOr (l + r) C) b, Edge R u v := by
    intro u hu v hv
    let x : Fin (l + r) → Bool := mark u v
    have hu' : wire C x u = true := (wire_mark C (haIn u hu) u v).mpr (Or.inl rfl)
    have hv' : wire C x v = true := (wire_mark C (hbIn v hv) u v).mpr (Or.inr rfl)
    have htrue : wire C x (l + r + j) = true := by
      rw [heval, Bool.and_eq_true]
      exact ⟨(haVal x).mpr ⟨u, hu, hu'⟩, (hbVal x).mpr ⟨v, hv, hv'⟩⟩
    exact (output_mark hc u v).mp (and_below hclean hj hand x htrue)
  rcases biclique_star hC4 (atoms_nonempty _ _) (atoms_nonempty _ _) hedges with
    ⟨c, hsing, hE⟩ | ⟨c, hsing, hE⟩
  · refine ⟨(c, b), hbl, hnb, hE, fun x hx => ?_⟩
    rw [heval, Bool.and_eq_true] at hx
    have hxc := (haVal x).mp hx.1
    rw [hsing] at hxc
    simpa only [Finset.mem_singleton, exists_eq_left] using And.intro hxc ((hbVal x).mp hx.2)
  · refine ⟨(c, a), hal, hna, hE, fun x hx => ?_⟩
    rw [heval, Bool.and_eq_true] at hx
    have hxc := (hbVal x).mp hx.2
    rw [hsing] at hxc
    simpa only [Finset.mem_singleton, exists_eq_left] using And.intro hxc ((haVal x).mp hx.1)


lemma term_stop {n : ℕ} {C : Circuit} {w : ℕ} (ht : IsTerm n C w) :
    splitTop n C w = none := by
  obtain ⟨j, _, rfl, hop, ha, hb⟩ := ht
  have hn : ¬ n + j < n := by omega
  simp [splitTop, hn, hop, ha, hb]

lemma top_budget {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (hInput : ∀ w < n, ¬ WireBelowOutput n C w)
    (hOut : C.output < n + C.gates.length) :
    ∃ M : Finset ℕ,
      (atoms (splitTop n C) C.output).card ≤ M.card + 1 ∧
      ∀ w ∈ M, n ≤ w ∧ w < n + C.gates.length ∧
        WireBelowOutput n C w ∧ ¬ IsTerm n C w := by
  let B := n + C.gates.length
  let f : ℕ → Finset ℕ := fun w =>
    if w < B ∧ WireBelowOutput n C w then atoms (splitTop n C) w else ∅
  let M := (Finset.range B).filter fun w =>
    WireBelowOutput n C w ∧ (splitTop n C w).isSome
  have hBase : ∀ w, w ∉ M → (f w).card ≤ 1 := by
    intro w hw
    by_cases h : w < B ∧ WireBelowOutput n C w
    · cases hs : splitTop n C w with
      | none => simp [f, h, atoms_stop hs]
      | some p => exact (hw (by simp [M, hs, h.1, h.2])).elim
    · simp [f, h]
  have hStep : ∀ w ∈ M,
      ∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b := by
    intro w hw
    have ⟨hwB, hwbelow, hs⟩ : w < B ∧ WireBelowOutput n C w ∧
        (splitTop n C w).isSome := by simpa [M] using hw
    cases heq : splitTop n C w with
    | none => simp [heq] at hs
    | some p =>
      obtain ⟨a, b⟩ := p
      obtain ⟨ha, hb, hba, hbb, _⟩ := top_split_spec hAO hwB hwbelow heq
      refine ⟨a, ha, b, hb, ?_⟩
      have haB : a < B := lt_trans ha hwB
      have hbB : b < B := lt_trans hb hwB
      simp [f, hwB, hwbelow, haB, hbB, hba, hbb, atoms_split heq ha hb]
  have hBound := merge_bound f M hBase (fun w hw => Or.inr (Or.inr (hStep w hw)))
    B {C.output} (by simpa using hOut)
  have hOutBelow : WireBelowOutput n C C.output := fun _ h => h
  have hEq : f C.output = atoms (splitTop n C) C.output := by simp [f, B, hOut, hOutBelow]
  rw [Finset.singleton_biUnion, Finset.card_singleton, hEq] at hBound
  have hFilter := Finset.card_filter_le M (fun w => w < B)
  refine ⟨M, by omega, ?_⟩
  intro w hw
  have ⟨hwB, hwbelow, hs⟩ : w < B ∧ WireBelowOutput n C w ∧
      (splitTop n C w).isSome := by simpa [M] using hw
  refine ⟨Nat.le_of_not_gt (fun hn => hInput w hn hwbelow), hwB, hwbelow, ?_⟩
  intro ht
  simp [term_stop ht] at hs

lemma sum_card_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → Finset β) (t : Finset β)
    (hd : Set.PairwiseDisjoint (s : Set α) f) (hsub : ∀ c ∈ s, f c ⊆ t) :
    (∑ c ∈ s, (f c).card) ≤ t.card := by
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨c, hc, hwc⟩ := Finset.mem_biUnion.mp hw
  exact hsub c hc hwc

def centered (A : Finset ℕ) (data : ℕ → ℕ × ℕ) (c : ℕ) : Finset ℕ :=
  A.filter fun g => (data g).1 = c

def spokes (n : ℕ) (C : Circuit) (A : Finset ℕ) (data : ℕ → ℕ × ℕ)
    (c : ℕ) : Finset ℕ :=
  (centered A data c).biUnion fun g => atoms (splitOr n C) (data g).2

lemma leaf_budget {l r : ℕ} {R : Fin l → Fin r → Prop} {C : Circuit}
    (hC4 : ∀ i i' j j', i ≠ i' → j ≠ j' → ¬ (R i j ∧ R i j' ∧ R i' j ∧ R i' j'))
    (hAO : IsAO2 (l + r) C) (hclean : Clean (l + r) C)
    (A : Finset ℕ) (data : ℕ → ℕ × ℕ)
    (hData : ∀ g ∈ A, (data g).2 < l + r + C.gates.length ∧
      ¬ WireBelowOutput (l + r) C (data g).2 ∧
      ∀ v ∈ atoms (splitOr (l + r) C) (data g).2, Edge R (data g).1 v) :
    (∑ c ∈ A.image (fun g => (data g).1), (spokes (l + r) C A data c).card) ≤
      A.card + ((Finset.Ico (l + r) (l + r + C.gates.length)).filter
        fun w => ¬ WireBelowOutput (l + r) C w).card := by
  classical
  let n := l + r
  let B := n + C.gates.length
  let s := A.image (fun g => (data g).1)
  let d := atoms (splitOr n C)
  let good (c w : ℕ) := w < B ∧ ¬ WireBelowOutput n C w ∧ ∀ v ∈ d w, Edge R c v
  let M (c : ℕ) := (Finset.Ico n B).filter fun w => good c w ∧ 1 < (d w).card
  have hgroup : ∀ c, (spokes n C A data c).card ≤ (centered A data c).card + (M c).card := by
    intro c
    let f (w : ℕ) := if good c w then d w else ∅
    have hBase : ∀ w, w ∉ M c → (f w).card ≤ 1 := by
      intro w hw
      by_cases hg : good c w
      · rw [show f w = d w by simp [f, hg]]
        by_cases hn : w < n
        · simp [d, atoms_stop (show splitOr n C w = none by simp [splitOr, hn])]
        · by_contra hcard
          apply hw
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hg.1⟩, hg, by omega⟩
      · simp [f, hg]
    have hStep : ∀ w ∈ M c, ∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b := by
      intro w hw
      obtain ⟨hi, hg, _⟩ := Finset.mem_filter.mp hw
      have hn : ¬ w < n := Nat.not_lt.mpr (Finset.mem_Ico.mp hi).1
      let j := w - n
      have hj : j < C.gates.length := by have := hg.1; dsimp [B] at this; omega
      have hwj : w = n + j := by omega
      have hok := hclean j _ (gate_get hj) (by rw [← hwj]; exact hg.2.1)
      obtain ⟨hp, ha, hb⟩ := children_spec hAO hj
      let a := (children C j).1
      let b := (children C j).2
      have haw : a < w := by dsimp [a]; omega
      have hbw : b < w := by dsimp [b]; omega
      have hs : splitOr n C w = some (a, b) := by
        have hpair : children C j = (a, b) := (Prod.eta (children C j)).symm
        simpa only [splitOr, hn, ↓reduceIte, (show w - n = j from rfl), hok.1] using congrArg some hpair
      have hUnion : d w = d a ∪ d b := atoms_split hs haw hbw
      have hga : good c a := ⟨lt_trans haw hg.1, hok.2 _ (by simp [hp, a]),
        fun v hv => hg.2.2 v (by rw [hUnion]; exact Finset.mem_union_left _ hv)⟩
      have hgb : good c b := ⟨lt_trans hbw hg.1, hok.2 _ (by simp [hp, b]),
        fun v hv => hg.2.2 v (by rw [hUnion]; exact Finset.mem_union_right _ hv)⟩
      exact ⟨a, haw, b, hbw, by simp [f, hg, hga, hgb, hUnion]⟩
    let roots := (centered A data c).image fun g => (data g).2
    have hRoots : ∀ w ∈ roots, good c w := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
      have ⟨hgA, hgc⟩ := Finset.mem_filter.mp hg
      obtain ⟨hbound, hbelow, hedges⟩ := hData g hgA
      exact ⟨hbound, hbelow, fun v hv => hgc ▸ hedges v hv⟩
    have hEq : roots.biUnion f = spokes n C A data c := by
      ext v
      simp only [Finset.mem_biUnion, spokes]
      constructor
      · rintro ⟨w, hw, hv⟩
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨g, hg, by simpa only [f, hRoots _ hw, ↓reduceIte] using hv⟩
      · rintro ⟨g, hg, hv⟩
        have hw : (data g).2 ∈ roots := Finset.mem_image.mpr ⟨g, hg, rfl⟩
        exact ⟨_, hw, by simpa only [f, hRoots _ hw, ↓reduceIte] using hv⟩
    have hmb := merge_bound f (M c) hBase (fun w hw => Or.inr (Or.inr (hStep w hw)))
      B roots (fun w hw => (hRoots w hw).1)
    rw [hEq] at hmb
    have hf := Finset.card_filter_le (M c) (fun w => w < B)
    have hr : roots.card ≤ (centered A data c).card := Finset.card_image_le
    omega
  have hc := sum_card_le s (centered A data) A
    (by
      intro c _ c' _ hne
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      exact hne ((Finset.mem_filter.mp hw).2.symm.trans (Finset.mem_filter.mp hw').2))
    (fun _ _ _ hw => (Finset.mem_filter.mp hw).1)
  have hm := sum_card_le s M ((Finset.Ico n B).filter fun w => ¬ WireBelowOutput n C w)
    (by
      intro c _ c' _ hne
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      have hc := (Finset.mem_filter.mp hw).2
      have hc' := (Finset.mem_filter.mp hw').2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc.2
      exact no_rect hC4 hne hab (hc.1.2.2 a ha) (hc.1.2.2 b hb)
        (hc'.1.2.2 a ha) (hc'.1.2.2 b hb))
    (fun _ _ _ hw => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.1.2.1⟩)
  calc
    _ ≤ ∑ c ∈ s, ((centered A data c).card + (M c).card) :=
      Finset.sum_le_sum fun c _ => hgroup c
    _ = (∑ c ∈ s, (centered A data c).card) + ∑ c ∈ s, (M c).card :=
      Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add hc hm


lemma main_proof (l r : ℕ) (R : Fin l → Fin r → Prop) [DecidableRel R] (C : Circuit)
    (hC4 : ∀ i i' j j', i ≠ i' → j ≠ j' → ¬ (R i j ∧ R i j' ∧ R i' j ∧ R i' j'))
    (hAO : IsAO2 (l + r) C) (hcomp : Computes R C) (hclean : Clean (l + r) C) :
    ∃ stars : List (ℕ × List ℕ),
      (∀ p ∈ stars, p.2 ≠ [] ∧
        ((p.1 < l ∧ ∀ v ∈ p.2, l ≤ v ∧ v < l + r) ∨
          l ≤ p.1 ∧ p.1 < l + r ∧ ∀ v ∈ p.2, v < l)) ∧
      (∀ (i : Fin l) (j : Fin r), R i j ↔ ∃ p ∈ stars,
        p.1 = i.val ∧ l + j.val ∈ p.2 ∨ p.1 = l + j.val ∧ i.val ∈ p.2) ∧
      (stars.map (fun p => p.2.length)).sum + stars.length - 1 ≤ C.size := by
  classical
  by_cases hE : ∃ i j, R i j
  · let n := l + r
    let B := n + C.gates.length
    have hOut : C.output < B := by
      by_contra h
      obtain ⟨i, j, hij⟩ := hE
      have hval := (output_mark hcomp i.val (l + j.val)).mpr ((edge_codes i j).mpr hij)
      have hfalse := wire_missing C (mark (n := n) i.val (l + j.val)) C.output (by omega)
      exact Bool.false_ne_true (hfalse.symm.trans hval)
    let A := atoms (splitTop n C) C.output
    have hOutBelow : WireBelowOutput n C C.output := fun _ h => h
    obtain ⟨hTerms, hReach⟩ := top_atoms_spec hAO (input_not_below hcomp) C.output hOut hOutBelow
    have hStar : ∀ w ∈ A, ∃ p : ℕ × ℕ,
        p.2 < B ∧ ¬ WireBelowOutput n C p.2 ∧
        (∀ v ∈ atoms (splitOr n C) p.2, Edge R p.1 v) ∧
        ∀ x : Fin n → Bool, wire C x w = true →
          wire C x p.1 = true ∧ ∃ v ∈ atoms (splitOr n C) p.2, wire C x v = true :=
      fun w hw => term_star hC4 hAO hcomp hclean (hTerms w hw)
    let data (w : ℕ) : ℕ × ℕ := if h : w ∈ A then Classical.choose (hStar w h) else (0, 0)
    have hData (w : ℕ) (hw : w ∈ A) :
        (data w).2 < B ∧ ¬ WireBelowOutput n C (data w).2 ∧
        (∀ v ∈ atoms (splitOr n C) (data w).2, Edge R (data w).1 v) ∧
        ∀ x : Fin n → Bool, wire C x w = true →
          wire C x (data w).1 = true ∧
            ∃ v ∈ atoms (splitOr n C) (data w).2, wire C x v = true := by
      simpa only [data, dite_eq_left hw] using Classical.choose_spec (hStar w hw)
    let centers := A.image fun w => (data w).1
    let leaves := spokes n C A data
    have hLeaves (w : ℕ) (hw : w ∈ A) {v : ℕ}
        (hv : v ∈ atoms (splitOr n C) (data w).2) : v ∈ leaves (data w).1 :=
      Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, rfl⟩, hv⟩
    have hLeafEdge (c v : ℕ) (hv : v ∈ leaves c) : Edge R c v := by
      obtain ⟨w, hw, hmem⟩ := Finset.mem_biUnion.mp hv
      have ⟨hwA, hcw⟩ := Finset.mem_filter.mp hw
      exact hcw ▸ (hData w hwA).2.2.1 v hmem
    have hLeafNonempty (c : ℕ) (hc : c ∈ centers) : (leaves c).Nonempty := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨v, hv⟩ := atoms_nonempty (splitOr n C) (data w).2
      exact ⟨v, hLeaves w hw hv⟩
    let stars : List (ℕ × List ℕ) := centers.toList.map fun c => (c, (leaves c).toList)
    refine ⟨stars, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      simp only [Finset.mem_toList] at hc
      obtain ⟨v, hv⟩ := hLeafNonempty c hc
      have hne : (leaves c).toList ≠ [] := by
        intro he
        have hmem := Finset.mem_toList.mpr hv
        rw [he] at hmem
        exact List.not_mem_nil hmem
      refine ⟨hne, ?_⟩
      rcases edge_side (hLeafEdge c v hv) with h | h
      · refine Or.inl ⟨h.1, fun z hz => ?_⟩
        rcases edge_side (hLeafEdge c z (Finset.mem_toList.mp hz)) with h' | h'
        · exact h'.2
        · omega
      · refine Or.inr ⟨h.1, h.2.1, fun z hz => ?_⟩
        rcases edge_side (hLeafEdge c z (Finset.mem_toList.mp hz)) with h' | h'
        · omega
        · exact h'.2.2
    · intro i j
      let u := i.val
      let v := l + j.val
      rw [← edge_codes (R := R) i j]
      change Edge R u v ↔ _
      constructor
      · intro huv
        have hout := (output_mark hcomp u v).mpr huv
        obtain ⟨w, hw, hwv⟩ := hReach (mark u v) hout
        obtain ⟨hc, z, hz, hzv⟩ := (hData w hw).2.2.2 _ hwv
        let c := (data w).1
        have hzc := hLeaves w hw hz
        have hed := edge_bounds (hLeafEdge c z hzc)
        have hc' := (wire_mark C hed.1 u v).mp hc
        have hz' := (wire_mark C hed.2.1 u v).mp hzv
        have hcenter : c ∈ centers := Finset.mem_image.mpr ⟨w, hw, rfl⟩
        refine ⟨(c, (leaves c).toList), List.mem_map.mpr
          ⟨c, Finset.mem_toList.mpr hcenter, rfl⟩, ?_⟩
        obtain hc' | hc' := hc' <;> obtain hz' | hz' := hz'
        · exact (hed.2.2 (hc'.trans hz'.symm)).elim
        · refine Or.inl ⟨hc', Finset.mem_toList.mpr ?_⟩
          change v ∈ leaves c
          rwa [← hz']
        · refine Or.inr ⟨hc', Finset.mem_toList.mpr ?_⟩
          change u ∈ leaves c
          rwa [← hz']
        · exact (hed.2.2 (hc'.trans hz'.symm)).elim
      · rintro ⟨p, hp, h⟩
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hp
        rcases h with ⟨hc, hv⟩ | ⟨hc, hu⟩
        · change c = u at hc
          rw [← hc]
          exact hLeafEdge c v (Finset.mem_toList.mp hv)
        · change c = v at hc
          rw [← hc]
          exact edge_symm (hLeafEdge c u (Finset.mem_toList.mp hu))
    · let gates := Finset.Ico n B
      let bottom := gates.filter fun w => ¬ WireBelowOutput n C w
      obtain ⟨M, hMcard, hM⟩ := top_budget hAO (input_not_below hcomp) hOut
      have hAsub : A ⊆ gates := by
        intro w hw
        obtain ⟨j, hj, rfl, _⟩ := hTerms w hw
        exact Finset.mem_Ico.mpr ⟨by omega, by dsimp [B]; omega⟩
      have hMsub : M ⊆ gates := fun w hw => Finset.mem_Ico.mpr ⟨(hM w hw).1, (hM w hw).2.1⟩
      have hAM : Disjoint A M :=
        Finset.disjoint_left.mpr fun w hwA hwM => (hM w hwM).2.2.2 (hTerms w hwA)
      have hAB : Disjoint (A ∪ M) bottom := by
        apply Finset.disjoint_left.mpr
        intro w hw hb
        have hnb := (Finset.mem_filter.mp hb).2
        apply hnb
        rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨j, hj, rfl, hand, _⟩ := hTerms w hw
          exact and_below hclean hj hand
        · exact (hM w hw).2.2.1
      have hsub : (A ∪ M) ∪ bottom ⊆ gates :=
        Finset.union_subset (Finset.union_subset hAsub hMsub) (Finset.filter_subset _ _)
      have htotal := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hAM] at htotal
      have hgateCard : gates.card = C.size := by simp [gates, B, Circuit.size]
      rw [hgateCard] at htotal
      have hcenters : centers.card ≤ A.card := Finset.card_image_le
      have hl : (∑ c ∈ centers, (leaves c).card) ≤ A.card + bottom.card :=
        leaf_budget hC4 hAO hclean A data (fun w hw =>
          ⟨(hData w hw).1, (hData w hw).2.1, (hData w hw).2.2.1⟩)
      have hlen : stars.length = centers.card := by simp [stars]
      have hsum : (stars.map (fun p => p.2.length)).sum = ∑ c ∈ centers, (leaves c).card := by
        simp only [stars, List.map_map, Function.comp_def, Finset.length_toList]
        exact Finset.sum_map_toList _ _
      rw [hlen, hsum]
      change A.card ≤ M.card + 1 at hMcard
      omega
  · exact ⟨[], by simp, fun i j => by simp [show ¬ R i j from fun h => hE ⟨i, j, h⟩], by simp⟩

end PEqualNP.Outside.L_meta_7649



theorem PEqualNP.Outside.L_meta_7649 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → (∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x9]? = Option.some x10 → ¬PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 (x1 + x2 + x9) → x10.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ x10.inputs, ¬PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x1 + x2) ∨ x1 ≤ x11.1 ∧ x11.1 < x1 + x2 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size :=
  PEqualNP.Outside.L_meta_7649.main_proof
