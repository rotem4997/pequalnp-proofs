import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8435

open PEqualNP.CircuitLowerBounds PEqualNP.SharedBlockCost

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def T {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val C (fun a : Fin n => decide (a = i)) w = true

theorem mem_T {n : ℕ} (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ (T C w : Finset (Fin n)) ↔ val C (fun a : Fin n => decide (a = i)) w = true := by
  simp [T]

theorem T_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (T C w : Finset (Fin n)) = {⟨w, hw⟩} := by
  ext i
  rw [mem_T]
  have h := val_input C (fun a : Fin n => decide (a = i)) ⟨w, hw⟩
  change val C (fun a : Fin n => decide (a = i)) w = _ at h
  rw [h]
  simp only [decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

theorem T_gate {n : ℕ} (C : Circuit) (hC : IsOrCircuit n C) (p : ℕ) (hp : p < C.gates.length) :
    ∃ a b, a < n + p ∧ b < n + p ∧ (T C (n + p) : Finset (Fin n)) = T C a ∪ T C b := by
  obtain ⟨hop, hlen, hin⟩ := hC p hp
  have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp
  have hor : (C.gates[p]).op = GateOp.or := by
    generalize (C.gates[p]).op = o at hop
    cases o <;> first | rfl | (simp [isOrOp] at hop)
  obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[p]).inputs = [a, b] := by
    match h : (C.gates[p]).inputs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have ha : a < n + p := hin a (by simp [hab])
  have hb : b < n + p := hin b (by simp [hab])
  refine ⟨a, b, ha, hb, ?_⟩
  ext i
  rw [Finset.mem_union, mem_T, mem_T, mem_T, val_gate C _ hg, hor, hab]
  simp [GateOp.eval, operand, ha, hb]

theorem T_computes {n : ℕ} (C : Circuit) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : T C w = s := by
  ext i
  rw [mem_T]
  have h2 := h.2 (fun a : Fin n => decide (a = i))
  change (val C (fun a : Fin n => decide (a = i)) w = true ↔ _) at h2
  rw [h2]
  simp


def Good {n : ℕ} (R : Fin n → Fin n → Prop) (C : Circuit) (c u : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ t ∈ (T C (n + j) : Finset (Fin n)), R c t) ∧
    u ∈ (T C (n + j) : Finset (Fin n)) ∧ ∃ u0 ∈ (T C (n + j) : Finset (Fin n)), u0 < u

theorem no_below {n : ℕ} (R : Fin n → Fin n → Prop) (C : Circuit) (c u : Fin n) (j a : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j)
    (hadj : ∀ t ∈ (T C a : Finset (Fin n)), R c t) (hu : u ∈ (T C a : Finset (Fin n)))
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') : ∀ t ∈ (T C a : Finset (Fin n)), ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [T_input C a han, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j', rfl⟩ : ∃ j', a = n + j' := ⟨a - n, by omega⟩
    exact hmin j' (by omega) ⟨by omega, hadj, hu, t, ht, hlt⟩

theorem no_lt_aux {n : ℕ} (R : Fin n → Fin n → Prop) (C : Circuit) (c u u' : Fin n) (j a b : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j) (hb : b < n + j)
    (hT : (T C (n + j) : Finset (Fin n)) = T C a ∪ T C b)
    (hg : Good R C c u j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c u' j')
    (hlt : u < u') (hu'a : u' ∈ (T C a : Finset (Fin n))) : False := by
  obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
  have hadja : ∀ t ∈ (T C a : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_left _ ht)
  have hadjb : ∀ t ∈ (T C b : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_right _ ht)
  have h1 := no_below R C c u' j a hj ha hadja hu'a hmin'
  rw [hT, Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below R C c u j b hj hb hadjb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

theorem no_lt {n : ℕ} (R : Fin n → Fin n → Prop) (C : Circuit) (hC : IsOrCircuit n C)
    (c u u' : Fin n) (j : ℕ) (hg : Good R C c u j) (hg' : Good R C c u' j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c u' j')
    (hlt : u < u') : False := by
  have hj := hg.1
  obtain ⟨a, b, ha, hb, hT⟩ := T_gate C hC j hj
  have hu' := hg'.2.2.1
  rw [hT, Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux R C c u u' j a b hj ha hb hT hg hmin hmin' hlt h
  · exact no_lt_aux R C c u u' j b a hj hb ha (by rw [hT, Finset.union_comm]) hg hmin hmin' hlt h

theorem inj_core {n : ℕ} (R : Fin n → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (C : Circuit) (hC : IsOrCircuit n C)
    (c u c' u' : Fin n) (j : ℕ) (hg : Good R C c u j) (hg' : Good R C c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c' u' j') :
    c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
    exact hN u0 u (ne_of_lt hu0lt) c c' (hadj u0 hu0) (hadj u hu) (hg'.2.1 u0 hu0) (hg'.2.1 u hu)
  subst hcc
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt R C hC c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt R C hC c u' u j hg' hg hmin' hmin h).elim

theorem leaf_min {n : ℕ} (R : Fin n → Fin n → Prop) (C : Circuit) (L : Finset (Fin n))
    (hS : ∃ w < n + C.gates.length, ComputesOr n C w L) (c u : Fin n)
    (hadj : ∀ t ∈ L, R c t) (hu : u ∈ L)
    (hng : ¬ ∃ j, Good R C c u j) : ∀ t ∈ L, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w, hw, hcomp⟩ := hS
  have hT := T_computes C w L hcomp
  by_cases hwn : w < n
  · rw [← hT, T_input C w hwn, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    exact hng ⟨j, by omega, by rw [hT]; exact hadj, by rw [hT]; exact hu, t,
      by rw [hT]; exact ht, hlt⟩

theorem count_gen {n : ℕ} (R : Fin n → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (C : Circuit) (hC : IsOrCircuit n C)
    (K : Finset (Fin n × Finset (Fin n)))
    (hK : ∀ k ∈ K, (∃ w < n + C.gates.length, ComputesOr n C w k.2) ∧ ∀ t ∈ k.2, R k.1 t)
    (P : Finset (Σ _ : Fin n, Fin n))
    (hP : ∀ q ∈ P, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2) :
    P.card ≤ C.gates.length + K.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good R C q.1 q.2 j).card ≤ C.gates.length := by
    rw [← Finset.card_range C.gates.length]
    refine Finset.card_le_card_of_forall_subsingleton
      (fun q j => Good R C q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good R C q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      exact Finset.mem_range.2 (Nat.find_spec hex).1
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core R hN C hC c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good R C q.1 q.2 j).card ≤ K.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun q k => k.1 = q.1 ∧ q.2 ∈ k.2) ?_ ?_
    · intro q hq
      exact hP q (Finset.mem_filter.1 hq).1
    · intro k hk q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨hq1, hqc, hqu⟩ := hq
      obtain ⟨hq1', hqc', hqu'⟩ := hq'
      have hcc : c = c' := hqc.symm.trans hqc'
      subst hcc
      obtain ⟨hcomp, hadj⟩ := hK k hk
      rw [hqc] at hadj
      have h1 := leaf_min R C k.2 hcomp c u hadj hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min R C k.2 hcomp c u' hadj hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good R C q.1 q.2 j)
  omega

theorem star_card {m n : ℕ} (A : Fin m → Finset (Fin n)) (B : Fin m → Finset (Fin n))
    (hA : ∀ j, (A j).card ≤ 1) :
    ((Finset.univ : Finset (Fin m)).biUnion
      (fun j => (A j).image (fun a => (a, B j)))).card ≤ m := by
  classical
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ j : Fin m, ((A j).image (fun a => (a, B j))).card ≤ ∑ _j : Fin m, 1 :=
        Finset.sum_le_sum fun j _ => le_trans Finset.card_image_le (hA j)
    _ = m := by simp

theorem main_bound (x1 x2 x3 x4 : ℕ) (x5 : Fin x1 → Finset (Fin x1))
    (x6 x7 x8 x9 : Fin x2 → Finset (Fin x1))
    (hlin : ∀ (x10 x11 : Fin x1), x10 ≠ x11 → (x5 x10 ∩ x5 x11).card ≤ 1)
    (hB : HasOrCost x1 (Finset.image x6 Finset.univ) x3)
    (hA : HasOrCost x1 (Finset.image x7 Finset.univ) x4)
    (hc : ∀ (x13 : Fin x2), (x8 x13).card ≤ 1 ∧ (x9 x13).card ≤ 1)
    (h14 : ∀ (x14 : Fin x2), ∀ x15 ∈ x8 x14, ∀ x17 ∈ x7 x14, x15 ∈ x5 x17)
    (h15 : ∀ (x15 : Fin x2), ∀ x16 ∈ x9 x15, x6 x15 ⊆ x5 x16)
    (hcov : ∀ (x16 x17 : Fin x1), x17 ∈ x5 x16 → ∃ (x19 : Fin x2),
      x17 ∈ x8 x19 ∧ x16 ∈ x7 x19 ∨ x17 ∈ x6 x19 ∧ x16 ∈ x9 x19) :
    ∑ x17 : Fin x1, (x5 x17).card ≤ x3 + x4 + 2 * x2 := by
  classical
  obtain ⟨CB, ⟨hCB, hSB⟩, hlenB⟩ := hB
  obtain ⟨CA, ⟨hCA, hSA⟩, hlenA⟩ := hA
  let I : Finset (Σ _ : Fin x1, Fin x1) := (Finset.univ : Finset (Fin x1)).sigma x5
  have hI : I.card = ∑ x17 : Fin x1, (x5 x17).card := Finset.card_sigma _ _
  let IB := I.filter (fun q => ∃ j, q.2 ∈ x6 j ∧ q.1 ∈ x9 j)
  let IA := I.filter (fun q => ¬ ∃ j, q.2 ∈ x6 j ∧ q.1 ∈ x9 j)
  have hsplit : IB.card + IA.card = I.card := Finset.card_filter_add_card_filter_not _
  let KB := (Finset.univ : Finset (Fin x2)).biUnion (fun j => (x9 j).image (fun a => (a, x6 j)))
  let KA := (Finset.univ : Finset (Fin x2)).biUnion (fun j => (x8 j).image (fun b => (b, x7 j)))
  have hKB : KB.card ≤ x2 := star_card x9 x6 (fun j => (hc j).2)
  have hKA : KA.card ≤ x2 := star_card x8 x7 (fun j => (hc j).1)
  have hBcount : IB.card ≤ CB.gates.length + KB.card := by
    refine count_gen (fun c t => t ∈ x5 c) ?_ CB hCB KB ?_ IB ?_
    · intro u0 u hne c c' h1 h2 h3 h4
      by_contra hcc
      have hle := hlin c c' hcc
      exact hne (Finset.card_le_one.1 hle u0 (Finset.mem_inter.2 ⟨h1, h3⟩) u
        (Finset.mem_inter.2 ⟨h2, h4⟩))
    · intro k hk
      obtain ⟨j, _, hk'⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hk'
      refine ⟨hSB _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩), ?_⟩
      intro t ht
      exact h15 j a ha ht
    · intro q hq
      obtain ⟨_, j, h1, h2⟩ := Finset.mem_filter.1 hq
      exact ⟨(q.1, x6 j), Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
        Finset.mem_image.2 ⟨q.1, h2, rfl⟩⟩, rfl, h1⟩
  let sw : (Σ _ : Fin x1, Fin x1) → (Σ _ : Fin x1, Fin x1) := fun q => ⟨q.2, q.1⟩
  have hsw : Function.Injective sw := by
    intro q q' h
    obtain ⟨a, b⟩ := q
    obtain ⟨a', b'⟩ := q'
    simp only [sw, Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2; rfl
  have hAcount : (IA.image sw).card ≤ CA.gates.length + KA.card := by
    refine count_gen (fun c t => c ∈ x5 t) ?_ CA hCA KA ?_ (IA.image sw) ?_
    · intro u0 u hne c c' h1 h2 h3 h4
      exact Finset.card_le_one.1 (hlin u0 u hne) c (Finset.mem_inter.2 ⟨h1, h2⟩) c'
        (Finset.mem_inter.2 ⟨h3, h4⟩)
    · intro k hk
      obtain ⟨j, _, hk'⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hk'
      refine ⟨hSA _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩), ?_⟩
      intro t ht
      exact h14 j b hb t ht
    · intro q hq
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨hq0I, hnot⟩ := Finset.mem_filter.1 hq0
      have hmem : q0.2 ∈ x5 q0.1 := (Finset.mem_sigma.1 hq0I).2
      obtain ⟨j, hj⟩ := hcov q0.1 q0.2 hmem
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(q0.2, x7 j), Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
          Finset.mem_image.2 ⟨q0.2, h1, rfl⟩⟩, rfl, h2⟩
      · exact (hnot ⟨j, h1, h2⟩).elim
  rw [Finset.card_image_of_injective _ hsw] at hAcount
  omega

end PEqualNP.Outside.L_meta_8435

theorem PEqualNP.Outside.L_meta_8435 : ∀ (x1 x2 x3 x4 : ℕ) (x5 : Fin x1 → Finset (Fin x1)) (x6 x7 x8 x9 : Fin x2 → Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x10 ≠ x11 → (x5 x10 ∩ x5 x11).card ≤ (1 : ℕ)) → PEqualNP.SharedBlockCost.HasOrCost x1 (Finset.image x6 Finset.univ) x3 → PEqualNP.SharedBlockCost.HasOrCost x1 (Finset.image x7 Finset.univ) x4 → (∀ (x13 : Fin x2), (x8 x13).card ≤ (1 : ℕ) ∧ (x9 x13).card ≤ (1 : ℕ)) → (∀ (x14 : Fin x2), ∀ x15 ∈ x8 x14, ∀ x17 ∈ x7 x14, x15 ∈ x5 x17) → (∀ (x15 : Fin x2), ∀ x16 ∈ x9 x15, x6 x15 ⊆ x5 x16) → (∀ (x16 x17 : Fin x1), x17 ∈ x5 x16 → ∃ (x19 : Fin x2), x17 ∈ x8 x19 ∧ x16 ∈ x7 x19 ∨ x17 ∈ x6 x19 ∧ x16 ∈ x9 x19) → ∑ x17 : Fin x1, (x5 x17).card ≤ x3 + x4 + (2 : ℕ) * x2 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 h1 h2 h3 h4 h5 h6 h7
  exact PEqualNP.Outside.L_meta_8435.main_bound x1 x2 x3 x4 x5 x6 x7 x8 x9 h1 h2 h3 h4 h5 h6 h7
