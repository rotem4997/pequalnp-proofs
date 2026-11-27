import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7372

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

def keepList (p : ℕ → Bool) (m : ℕ) : List ℕ :=
  (List.range m).filter p

def rankOf (p : ℕ → Bool) (k : ℕ) : ℕ :=
  (keepList p k).length

lemma keepList_succ (p : ℕ → Bool) (m : ℕ) :
    keepList p (m + 1) = keepList p m ++ if p m then [m] else [] := by
  unfold keepList
  rw [List.range_succ, List.filter_append]
  cases hp : p m <;> simp [hp]

lemma rankOf_succ (p : ℕ → Bool) (m : ℕ) :
    rankOf p (m + 1) = rankOf p m + if p m then 1 else 0 := by
  unfold rankOf
  rw [keepList_succ, List.length_append]
  cases p m <;> simp

lemma rankOf_mono (p : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) :
    rankOf p a ≤ rankOf p b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact le_refl _
  | succ b ih =>
    by_cases hlt : a ≤ b
    · have h1 := ih hlt
      rw [rankOf_succ]
      omega
    · have ha : a = b + 1 := by omega
      subst ha
      exact le_refl _

lemma rankOf_lt_of_lt (p : ℕ → Bool) {a b : ℕ} (hab : a < b) (ha : p a = true) :
    rankOf p a < rankOf p b := by
  have h1 : rankOf p a + 1 = rankOf p (a + 1) := by
    rw [rankOf_succ, ha]
    simp
  have h2 : rankOf p (a + 1) ≤ rankOf p b := rankOf_mono p hab
  omega

lemma keepList_getElem_props (p : ℕ → Bool) (m : ℕ) :
    ∀ k (hk : k < (keepList p m).length),
      (keepList p m)[k] < m ∧ p (keepList p m)[k] = true ∧ rankOf p (keepList p m)[k] = k := by
  induction m with
  | zero =>
    intro k hk
    simp [keepList] at hk
  | succ m ih =>
    intro k hk
    cases hpm : p m
    · have hEq : keepList p (m + 1) = keepList p m := by
        rw [keepList_succ, hpm]
        simp
      have hk' : k < (keepList p m).length := by simpa [hEq] using hk
      have h1 := ih k hk'
      have hget : (keepList p (m + 1))[k] = (keepList p m)[k] := by
        simp [hEq]
      rw [hget]
      exact ⟨by omega, h1.2.1, h1.2.2⟩
    · have hEq : keepList p (m + 1) = keepList p m ++ [m] := by
        rw [keepList_succ, hpm]
        simp
      have hk' : k < (keepList p m).length + 1 := by
        simpa [hEq] using hk
      by_cases hlt : k < (keepList p m).length
      · have h1 := ih k hlt
        have hget : (keepList p (m + 1))[k] = (keepList p m)[k] := by
          simp [hEq, List.getElem_append_left hlt]
        rw [hget]
        exact ⟨by omega, h1.2.1, h1.2.2⟩
      · have hkeq : k = (keepList p m).length := by omega
        have hget : (keepList p (m + 1))[k] = m := by
          simp [hEq, hkeq]
        rw [hget]
        exact ⟨by omega, hpm, by unfold rankOf; omega⟩

lemma keepList_getElem_rankOf (p : ℕ → Bool) (m : ℕ) :
    ∀ j < m, p j = true →
      ∃ hlt : rankOf p j < (keepList p m).length, (keepList p m)[rankOf p j] = j := by
  induction m with
  | zero =>
    intro j hj
    omega
  | succ m ih =>
    intro j hj hpj
    cases hpm : p m
    · have hEq : keepList p (m + 1) = keepList p m := by
        rw [keepList_succ, hpm]
        simp
      have hjm : j < m := by
        by_contra hge
        have : j = m := by omega
        subst this
        rw [hpm] at hpj
        cases hpj
      obtain ⟨hlt, hget⟩ := ih j hjm hpj
      refine ⟨by simpa [hEq] using hlt, ?_⟩
      simp [hEq, hget]
    · have hEq : keepList p (m + 1) = keepList p m ++ [m] := by
        rw [keepList_succ, hpm]
        simp
      by_cases hjm : j < m
      · obtain ⟨hlt, hget⟩ := ih j hjm hpj
        refine ⟨by simp [hEq]; omega, ?_⟩
        simp [hEq, List.getElem_append_left hlt, hget]
      · have hjeq : j = m := by omega
        subst hjeq
        have hr : rankOf p j = (keepList p j).length := rfl
        refine ⟨by simp [hEq, hr], ?_⟩
        simp [hEq, hr]

lemma rankOf_add_filter_card (p : ℕ → Bool) (m : ℕ) :
    rankOf p m + ((Finset.range m).filter (fun j => p j = false)).card = m := by
  induction m with
  | zero => simp [rankOf, keepList]
  | succ m ih =>
    rw [rankOf_succ, Finset.range_add_one, Finset.filter_insert]
    cases hpm : p m
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hnot : m ∉ (Finset.range m).filter (fun j => p j = false) := by
        simp
      rw [Finset.card_insert_of_notMem hnot]
      omega
    · simp only [↓reduceIte, Bool.true_eq_false]
      omega

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def isTopAndB (n : ℕ) (C : Circuit) (j : ℕ) : Bool :=
  decide (j < C.gates.length) &&
  decide (WireBelowOutput n C (n + j)) &&
  isAndOp (gateAt C j).op &&
  (gateAt C j).inputs.all (fun u => !decide (WireBelowOutput n C u))

lemma isTopAndB_eq_true_iff (n : ℕ) (C : Circuit) (j : ℕ) :
    isTopAndB n C j = true ↔
      j < C.gates.length ∧ WireBelowOutput n C (n + j) ∧
      (gateAt C j).op = GateOp.and ∧
      ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
  unfold isTopAndB
  simp only [Bool.and_eq_true, decide_eq_true_eq, isAndOp_eq_true_iff, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, and_assoc]

lemma kept_downward_closed (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (hOr : ∀ j < C.size, ∀ (a b : ℕ),
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b))
    (j : ℕ) (hj : j < C.gates.length) (hnot : ¬ WireBelowOutput n C (n + j)) :
    ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
  obtain ⟨a, b, hab, _, _⟩ := gate_inputs_two n C hAO j hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.1 C.gates[j] (List.getElem_mem hj)
  intro u hu
  rw [hab] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hop with hand | hor
  · intro hwu
    apply hnot
    intro x hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_and_pair n C hAO.2.1 j a b hj hand hab x] at hx
    rw [Bool.and_eq_true] at hx
    rcases hu with rfl | rfl
    · exact hwu x hx.1
    · exact hwu x hx.2
  · have hget : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ := by
      rw [List.getElem?_eq_getElem hj]
      congr 1
      have h1 : C.gates[j].op = GateOp.or := by rw [← gateAt_eq_getElem C j hj]; exact hor
      have h2 : C.gates[j].inputs = [a, b] := by rw [← gateAt_eq_getElem C j hj]; exact hab
      cases hcj : C.gates[j] with
      | mk gop ginputs =>
        rw [hcj] at h1 h2
        dsimp only at h1 h2
        rw [h1, h2]
    have horj := hOr j hj a b hget
    intro hwu
    have hboth : WireBelowOutput n C a ∧ WireBelowOutput n C b := by
      rcases hu with hEq | hEq
      · rw [hEq] at hwu
        have ha_ge : n ≤ a := by
          by_contra hlt
          exact hNoIn a (by omega) hwu
        exact ⟨hwu, horj.2 ha_ge hwu⟩
      · rw [hEq] at hwu
        have hb_ge : n ≤ b := by
          by_contra hlt
          exact hNoIn b (by omega) hwu
        exact ⟨horj.1 hb_ge hwu, hwu⟩
    apply hnot
    intro x hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_or_pair n C hAO.2.1 j a b hj hor hab x] at hx
    rw [Bool.or_eq_true] at hx
    rcases hx with hxa | hxb
    · exact hboth.1 x hxa
    · exact hboth.2 x hxb

lemma peel_below (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (below : Finset ℕ)
    (hbelow_def : below = (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))) :
    ∀ k : ℕ, ∀ S D : Finset ℕ,
      below.card - D.card ≤ k →
      S ⊆ below →
      D ⊆ below →
      Disjoint S D →
      S.card ≤ D.card + 1 →
      (∀ x : Fin n → Bool, circuitFun n C x = true →
        ∃ j ∈ S, PEqualNP.BlindGate.wireValue C n x (n + j) = true) →
      (∀ s ∈ S, isTopAndB n C s = false → ∀ d ∈ D, s < d) →
      ∃ S' D' : Finset ℕ,
        S' ⊆ below ∧
        D' ⊆ below ∧
        Disjoint S' D' ∧
        S'.card ≤ D'.card + 1 ∧
        (∀ j ∈ S', isTopAndB n C j = true) ∧
        (∀ x : Fin n → Bool, circuitFun n C x = true →
          ∃ j ∈ S', PEqualNP.BlindGate.wireValue C n x (n + j) = true) := by
  intro k
  induction k with
  | zero =>
    intro S D hk hS hD hDisj hCard hCov hOrd
    set bad := S.filter (fun j => isTopAndB n C j = false) with hbad_def
    by_cases hEmpty : bad = ∅
    · refine ⟨S, D, hS, hD, hDisj, hCard, ?_, hCov⟩
      intro j hj
      cases ht : isTopAndB n C j with
      | true => rfl
      | false =>
        have hmem : j ∈ bad := by
          rw [hbad_def, Finset.mem_filter]
          exact ⟨hj, ht⟩
        rw [hEmpty] at hmem
        exact absurd hmem (Finset.notMem_empty j)
    · have hne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨m, hm⟩ := hne
      rw [hbad_def, Finset.mem_filter] at hm
      have hmB : m ∈ below := hS hm.1
      have hmNotD : m ∉ D := Finset.disjoint_left.mp hDisj hm.1
      have hDlt : D.card < below.card := by
        have hsub : insert m D ⊆ below := Finset.insert_subset hmB hD
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hmNotD] at h1
        omega
      omega
  | succ k ih =>
    intro S D hk hS hD hDisj hCard hCov hOrd
    set bad := S.filter (fun j => isTopAndB n C j = false) with hbad_def
    by_cases hEmpty : bad = ∅
    · refine ⟨S, D, hS, hD, hDisj, hCard, ?_, hCov⟩
      intro j hj
      cases ht : isTopAndB n C j with
      | true => rfl
      | false =>
        have hmem : j ∈ bad := by
          rw [hbad_def, Finset.mem_filter]
          exact ⟨hj, ht⟩
        rw [hEmpty] at hmem
        exact absurd hmem (Finset.notMem_empty j)
    · have hne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      set m := bad.max' hne with hm_def
      have hm_bad : m ∈ bad := Finset.max'_mem bad hne
      rw [hbad_def, Finset.mem_filter] at hm_bad
      have hmS : m ∈ S := hm_bad.1
      have hmFalse : isTopAndB n C m = false := hm_bad.2
      have hmB : m ∈ below := hS hmS
      have hmNotD : m ∉ D := Finset.disjoint_left.mp hDisj hmS
      have hmProps : m < C.gates.length ∧ WireBelowOutput n C (n + m) := by
        rw [hbelow_def, Finset.mem_filter, Finset.mem_range] at hmB
        exact hmB
      have hm_lt_D : ∀ d ∈ D, m < d := hOrd m hmS hmFalse
      have hD'_card : (insert m D).card = D.card + 1 := Finset.card_insert_of_notMem hmNotD
      have hD'_sub : insert m D ⊆ below := Finset.insert_subset hmB hD
      have hk' : below.card - (insert m D).card ≤ k := by
        have hle := Finset.card_le_card hD'_sub
        omega
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO m hmProps.1
      have hop : (gateAt C m).op = GateOp.and ∨ (gateAt C m).op = GateOp.or := by
        rw [gateAt_eq_getElem C m hmProps.1]
        exact hAO.1 C.gates[m] (List.getElem_mem hmProps.1)
      rcases hop with hand | hor
      · have hex : ∃ u ∈ (gateAt C m).inputs, WireBelowOutput n C u := by
          by_contra hall
          push Not at hall
          have htrue : isTopAndB n C m = true := by
            rw [isTopAndB_eq_true_iff]
            exact ⟨hmProps.1, hmProps.2, hand, hall⟩
          rw [hmFalse] at htrue
          cases htrue
        obtain ⟨u, hu_mem, hu_below⟩ := hex
        have hu_lt : u < n + m := hAO.2.1 m hmProps.1 u hu_mem
        have hu_ge : n ≤ u := by
          by_contra hlt
          exact hNoIn u (by omega) hu_below
        set ju := u - n with hju_def
        have hju_lt : ju < m := by omega
        have hju_eq : n + ju = u := by omega
        have hjuB : ju ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hju_eq]; exact hu_below⟩
        set S1 := insert ju (S.erase m) with hS1_def
        set D1 := insert m D with hD1_def
        apply ih S1 D1 hk'
        · intro s hs
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with rfl | ⟨_, hsS⟩
          · exact hjuB
          · exact hS hsS
        · exact hD'_sub
        · rw [Finset.disjoint_left]
          intro s hs hsD1
          simp only [hD1_def, Finset.mem_insert] at hsD1
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqs | ⟨hne_m, hsS⟩
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD
              omega
          · rcases hsD1 with hEqm | hdD
            · exact hne_m hEqm
            · exact Finset.disjoint_left.mp hDisj hsS hdD
        · have h1 : S1.card ≤ (S.erase m).card + 1 := Finset.card_insert_le ju (S.erase m)
          have h2 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
          have h3 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
          rw [hD1_def, hD'_card]
          omega
        · intro x hfx
          obtain ⟨j, hjS, hjx⟩ := hCov x hfx
          by_cases hjm : j = m
          · rw [hjm] at hjx
            refine ⟨ju, ?_, ?_⟩
            · simp [hS1_def]
            · rw [hju_eq]
              rw [wireValue_and_pair n C hAO.2.1 m a b hmProps.1 hand hab x] at hjx
              rw [Bool.and_eq_true] at hjx
              rw [hab] at hu_mem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
              rcases hu_mem with rfl | rfl
              · exact hjx.1
              · exact hjx.2
          · exact ⟨j, by simp [hS1_def, hjm, hjS], hjx⟩
        · intro s hs hsFalse d hd
          have hm_le_d : m ≤ d := by
            simp only [hD1_def, Finset.mem_insert] at hd
            rcases hd with hEqm | hdD
            · omega
            · have := hm_lt_D d hdD; omega
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqs | ⟨hne_m, hsS⟩
          · omega
          · have hs_bad : s ∈ bad := by
              rw [hbad_def, Finset.mem_filter]
              exact ⟨hsS, hsFalse⟩
            have hs_le : s ≤ m := Finset.le_max' bad s hs_bad
            omega
      · have ha_below : WireBelowOutput n C a := by
          intro x hxa
          apply hmProps.2 x
          change PEqualNP.BlindGate.wireValue C n x (n + m) = true
          change PEqualNP.BlindGate.wireValue C n x a = true at hxa
          rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x, hxa]
          simp
        have hb_below : WireBelowOutput n C b := by
          intro x hxb
          apply hmProps.2 x
          change PEqualNP.BlindGate.wireValue C n x (n + m) = true
          change PEqualNP.BlindGate.wireValue C n x b = true at hxb
          rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x, hxb]
          simp
        have ha_ge : n ≤ a := by
          by_contra hlt
          exact hNoIn a (by omega) ha_below
        have hb_ge : n ≤ b := by
          by_contra hlt
          exact hNoIn b (by omega) hb_below
        set ja := a - n with hja_def
        set jb := b - n with hjb_def
        have hja_lt : ja < m := by omega
        have hjb_lt : jb < m := by omega
        have hja_eq : n + ja = a := by omega
        have hjb_eq : n + jb = b := by omega
        have hjaB : ja ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hja_eq]; exact ha_below⟩
        have hjbB : jb ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hjb_eq]; exact hb_below⟩
        set S1 := insert ja (insert jb (S.erase m)) with hS1_def
        set D1 := insert m D with hD1_def
        apply ih S1 D1 hk'
        · intro s hs
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with rfl | rfl | ⟨_, hsS⟩
          · exact hjaB
          · exact hjbB
          · exact hS hsS
        · exact hD'_sub
        · rw [Finset.disjoint_left]
          intro s hs hsD1
          simp only [hD1_def, Finset.mem_insert] at hsD1
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqa | hEqb | ⟨hne_m, hsS⟩
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD; omega
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD; omega
          · rcases hsD1 with hEqm | hdD
            · exact hne_m hEqm
            · exact Finset.disjoint_left.mp hDisj hsS hdD
        · have h1 : S1.card ≤ (insert jb (S.erase m)).card + 1 :=
            Finset.card_insert_le ja (insert jb (S.erase m))
          have h2 : (insert jb (S.erase m)).card ≤ (S.erase m).card + 1 :=
            Finset.card_insert_le jb (S.erase m)
          have h3 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
          have h4 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
          rw [hD1_def, hD'_card]
          omega
        · intro x hfx
          obtain ⟨j, hjS, hjx⟩ := hCov x hfx
          by_cases hjm : j = m
          · rw [hjm] at hjx
            rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x] at hjx
            rw [Bool.or_eq_true] at hjx
            rcases hjx with hxa | hxb
            · exact ⟨ja, by simp [hS1_def], by rw [hja_eq]; exact hxa⟩
            · exact ⟨jb, by simp [hS1_def], by rw [hjb_eq]; exact hxb⟩
          · exact ⟨j, by simp [hS1_def, hjm, hjS], hjx⟩
        · intro s hs hsFalse d hd
          have hm_le_d : m ≤ d := by
            simp only [hD1_def, Finset.mem_insert] at hd
            rcases hd with hEqm | hdD
            · omega
            · have := hm_lt_D d hdD; omega
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqa | hEqb | ⟨hne_m, hsS⟩
          · omega
          · omega
          · have hs_bad : s ∈ bad := by
              rw [hbad_def, Finset.mem_filter]
              exact ⟨hsS, hsFalse⟩
            have hs_le : s ≤ m := Finset.le_max' bad s hs_bad
            omega

lemma main_proof (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hOut : C.output < n + C.size)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (hOr : ∀ j < C.size, ∀ (a b : ℕ),
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b)) :
    ∃ (C' : Circuit) (pairs : List (ℕ × ℕ)),
      IsAO2 n C' ∧
      (∀ k < C'.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C' n x (n + k) = true ∧ circuitFun n C x = false) ∧
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔
        ∃ p ∈ pairs, PEqualNP.BlindGate.wireValue C' n x p.1 = true ∧
          PEqualNP.BlindGate.wireValue C' n x p.2 = true) ∧
      C'.size + 2 * pairs.length ≤ C.size + 1 := by
  let keepB : ℕ → Bool := fun j => !decide (WireBelowOutput n C (n + j))
  have hkeepB_true : ∀ j, keepB j = true ↔ ¬ WireBelowOutput n C (n + j) := by
    intro j
    simp [keepB]
  have hkeepB_false : ∀ j, keepB j = false ↔ WireBelowOutput n C (n + j) := by
    intro j
    simp [keepB]
  let wmap : ℕ → ℕ := fun w => if w < n then w else n + rankOf keepB (w - n)
  let kl := keepList keepB C.gates.length
  let C' : Circuit :=
    { gates := kl.map (fun j => ⟨(gateAt C j).op, (gateAt C j).inputs.map wmap⟩)
      output := 0 }
  have hC'_len : C'.gates.length = kl.length := by
    simp [C']
  have hDC : ∀ j < C.gates.length, keepB j = true →
      ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
    intro j hj hkj u hu
    exact kept_downward_closed n C hAO hNoIn hOr j hj ((hkeepB_true j).mp hkj) u hu
  have hC'_gateAt : ∀ k (hk : k < kl.length),
      gateAt C' k = ⟨(gateAt C kl[k]).op, (gateAt C kl[k]).inputs.map wmap⟩ := by
    intro k hk
    have hk' : k < C'.gates.length := by rw [hC'_len]; exact hk
    rw [gateAt_eq_getElem C' k hk']
    simp [C']
  have hC'_AO : IsAO2 n C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj_lt : j < C.gates.length := by
        simp only [kl, keepList, List.mem_filter, List.mem_range] at hj
        exact hj.1
      rw [gateAt_eq_getElem C j hj_lt]
      exact hAO.1 C.gates[j] (List.getElem_mem hj_lt)
    · intro k hk w' hw'
      have hk_kl : k < kl.length := by rw [← hC'_len]; exact hk
      rw [hC'_gateAt k hk_kl] at hw'
      simp only [List.mem_map] at hw'
      obtain ⟨u, hu, rfl⟩ := hw'
      have hprops := keepList_getElem_props keepB C.gates.length k hk_kl
      have hj_lt : kl[k] < C.gates.length := hprops.1
      have hj_keep : keepB kl[k] = true := hprops.2.1
      have hj_rank : rankOf keepB kl[k] = k := hprops.2.2
      have hu_lt : u < n + kl[k] := hAO.2.1 kl[k] hj_lt u hu
      have hu_not : ¬ WireBelowOutput n C u := hDC kl[k] hj_lt hj_keep u hu
      by_cases hun : u < n
      · simp only [wmap, hun, ↓reduceIte]
        omega
      · simp only [wmap, hun, ↓reduceIte]
        have hku_true : keepB (u - n) = true := by
          rw [hkeepB_true]
          have heq : n + (u - n) = u := by omega
          rw [heq]
          exact hu_not
        have hlt_r : rankOf keepB (u - n) < rankOf keepB kl[k] :=
          rankOf_lt_of_lt keepB (by omega) hku_true
        omega
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj_lt : j < C.gates.length := by
        simp only [kl, keepList, List.mem_filter, List.mem_range] at hj
        exact hj.1
      simp only [List.length_map]
      rw [gateAt_eq_getElem C j hj_lt]
      exact hAO.2.2 C.gates[j] (List.getElem_mem hj_lt)
  have hWireEq : ∀ w < n + C.gates.length, ¬ WireBelowOutput n C w →
      ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C' n x (wmap w) = PEqualNP.BlindGate.wireValue C n x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnot x
      by_cases hwn : w < n
      · simp only [wmap, hwn, ↓reduceIte]
        rw [wireValue_input n C' x w hwn, wireValue_input n C x w hwn]
      · simp only [wmap, hwn, ↓reduceIte]
        set j := w - n with hj_def
        have hw_eq : n + j = w := by omega
        have hj_lt : j < C.gates.length := by omega
        have hj_keep : keepB j = true := by
          rw [hkeepB_true, hw_eq]
          exact hnot
        obtain ⟨hr_lt, hr_get⟩ := keepList_getElem_rankOf keepB C.gates.length j hj_lt hj_keep
        have hr_lt' : rankOf keepB j < C'.gates.length := by rw [hC'_len]; exact hr_lt
        rw [wireValue_gate n C' x (rankOf keepB j) hr_lt' hC'_AO.2.1]
        rw [hC'_gateAt (rankOf keepB j) hr_lt, hr_get]
        rw [← hw_eq, wireValue_gate n C x j hj_lt hAO.2.1]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < n + j := hAO.2.1 j hj_lt u hu
        have hu_not : ¬ WireBelowOutput n C u := hDC j hj_lt hj_keep u hu
        exact ih u (by omega) (by omega) hu_not x
  have hC'_dirty : ∀ k < C'.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue C' n x (n + k) = true ∧ circuitFun n C x = false := by
    intro k hk
    have hk_kl : k < kl.length := by
      change k < C'.gates.length at hk
      rw [← hC'_len]; exact hk
    have hprops := keepList_getElem_props keepB C.gates.length k hk_kl
    have hj_lt : kl[k] < C.gates.length := hprops.1
    have hj_not : ¬ WireBelowOutput n C (n + kl[k]) := (hkeepB_true kl[k]).mp hprops.2.1
    have hj_rank : rankOf keepB kl[k] = k := hprops.2.2
    have hex : ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C n x (n + kl[k]) = true ∧ circuitFun n C x = false := by
      by_contra hno
      apply hj_not
      intro x hx
      cases hcx : circuitFun n C x with
      | true => exact hcx
      | false => exact absurd ⟨x, hx, hcx⟩ hno
    obtain ⟨x, hx1, hx2⟩ := hex
    refine ⟨x, ?_, hx2⟩
    have hweq := hWireEq (n + kl[k]) (by omega) hj_not x
    have hwm : wmap (n + kl[k]) = n + k := by
      have hge : ¬ (n + kl[k] < n) := by omega
      simp only [wmap, hge, ↓reduceIte, Nat.add_sub_cancel_left, hj_rank]
    rw [← hwm, hweq]
    exact hx1
  set below := (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j)) with hbelow_def
  have hOut_below : WireBelowOutput n C C.output := fun _ hx => hx
  have hOut_ge : n ≤ C.output := by
    by_contra hlt
    exact hNoIn C.output (by omega) hOut_below
  set jOut := C.output - n with hjOut_def
  have hjOut_eq : n + jOut = C.output := by omega
  have hjOut_lt : jOut < C.gates.length := by
    change C.output < n + C.gates.length at hOut
    omega
  have hjOut_mem : jOut ∈ below := by
    rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjOut_lt, by rw [hjOut_eq]; exact hOut_below⟩
  obtain ⟨S, D, hS_sub, hD_sub, hDisj, hCard, hS_top, hCov⟩ :=
    peel_below n C hAO hNoIn below hbelow_def below.card {jOut} ∅ (by simp)
      (Finset.singleton_subset_iff.mpr hjOut_mem) (Finset.empty_subset _)
      (Finset.disjoint_empty_right _) (by simp)
      (fun x hfx => ⟨jOut, Finset.mem_singleton_self jOut, by rw [hjOut_eq]; exact hfx⟩)
      (fun _ _ _ _ hd => absurd hd (Finset.notMem_empty _))
  let pairs : List (ℕ × ℕ) := S.toList.map (fun j => (wmap (opnd C j 0), wmap (opnd C j 1)))
  refine ⟨C', pairs, hC'_AO, hC'_dirty, ?_, ?_⟩
  · intro x
    constructor
    · intro hfx
      obtain ⟨j, hjS, hjx⟩ := hCov x hfx
      have htop := (isTopAndB_eq_true_iff n C j).mp (hS_top j hjS)
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO j htop.1
      have ha_not : ¬ WireBelowOutput n C a := htop.2.2.2 a (by simp [hab])
      have hb_not : ¬ WireBelowOutput n C b := htop.2.2.2 b (by simp [hab])
      have hop0 : opnd C j 0 = a := by simp [opnd, hab]
      have hop1 : opnd C j 1 = b := by simp [opnd, hab]
      rw [wireValue_and_pair n C hAO.2.1 j a b htop.1 htop.2.2.1 hab x, Bool.and_eq_true] at hjx
      refine ⟨(wmap a, wmap b), ?_, ?_, ?_⟩
      · simp only [pairs, List.mem_map, Finset.mem_toList]
        exact ⟨j, hjS, by rw [hop0, hop1]⟩
      · rw [hWireEq a (by omega) ha_not x]; exact hjx.1
      · rw [hWireEq b (by omega) hb_not x]; exact hjx.2
    · rintro ⟨p, hp, hp1, hp2⟩
      simp only [pairs, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨j, hjS, rfl⟩ := hp
      have htop := (isTopAndB_eq_true_iff n C j).mp (hS_top j hjS)
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO j htop.1
      have ha_not : ¬ WireBelowOutput n C a := htop.2.2.2 a (by simp [hab])
      have hb_not : ¬ WireBelowOutput n C b := htop.2.2.2 b (by simp [hab])
      have hop0 : opnd C j 0 = a := by simp [opnd, hab]
      have hop1 : opnd C j 1 = b := by simp [opnd, hab]
      dsimp only at hp1 hp2
      rw [hop0] at hp1
      rw [hop1] at hp2
      rw [hWireEq a (by omega) ha_not x] at hp1
      rw [hWireEq b (by omega) hb_not x] at hp2
      apply htop.2.1 x
      change PEqualNP.BlindGate.wireValue C n x (n + j) = true
      rw [wireValue_and_pair n C hAO.2.1 j a b htop.1 htop.2.2.1 hab x, hp1, hp2]
      rfl
  · have hpair_len : pairs.length = S.card := by
      simp [pairs]
    have hSD_le : S.card + D.card ≤ below.card := by
      rw [← Finset.card_union_of_disjoint hDisj]
      exact Finset.card_le_card (Finset.union_subset hS_sub hD_sub)
    have hbelow_eq : below = (Finset.range C.gates.length).filter (fun j => keepB j = false) := by
      ext j
      simp [hbelow_def, hkeepB_false]
    have hsum_size : C'.size + below.card = C.size := by
      have h1 := rankOf_add_filter_card keepB C.gates.length
      rw [← hbelow_eq] at h1
      change C'.gates.length + below.card = C.gates.length
      rw [hC'_len]
      exact h1
    omega

end PEqualNP.Outside.L_meta_7372

theorem PEqualNP.Outside.L_meta_7372 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.size → (∀ x5 < x1, ¬PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x5) → (∀ x6 < x2.size, ∀ (x8 x9 : ℕ), x2.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x9)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 x1 x7 ∧ (∀ x9 < x7.size, ∃ (x11 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x7 x1 x11 (x1 + x9) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.false) ∧ (∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.BlindGate.wireValue x7 x1 x9 x10.1 = Bool.true ∧ PEqualNP.BlindGate.wireValue x7 x1 x9 x10.2 = Bool.true) ∧ x7.size + (2 : ℕ) * x8.length ≤ x2.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_7372.main_proof
