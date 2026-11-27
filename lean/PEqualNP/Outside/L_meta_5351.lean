import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5351

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.GenericRejection

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (C : Circuit) (z : List Bool) (w : ℕ) : Bool :=
  (C.wires z).getD w false

def gi0 (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 0 0

def gi1 (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 1 0

lemma wires_eq_foldl (C : Circuit) (z : List Bool) :
    C.wires z = C.gates.foldl step z := rfl

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
    omega

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (step w g).length := by simp only [step, List.length_append]; omega
    rw [ih (step w g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [step, List.getElem_append_left hi]

lemma wv_input (C : Circuit) (z : List Bool) (i : ℕ) (hi : i < z.length) :
    wv C z i = z.getD i false := by
  unfold wv
  rw [wires_eq_foldl]
  exact foldl_step_getD_lt C.gates z i hi

lemma wv_ge (C : Circuit) (z : List Bool) (w : ℕ) (hw : z.length + C.gates.length ≤ w) :
    wv C z w = false := by
  unfold wv
  rw [wires_eq_foldl]
  have hlen : (C.gates.foldl step z).length ≤ w := by rw [foldl_step_length]; omega
  rw [List.getD_eq_default _ _ hlen]

lemma wv_gate (m : ℕ) (C : Circuit) (hRB : ReadsBack m C) (z : List Bool) (hz : z.length = m)
    (j : ℕ) (hj : j < C.gates.length) :
    wv C z (m + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv C z i) := by
  unfold wv
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← hdrop, this]
  let pref := (C.gates.take j).foldl step z
  have hplen : pref.length = m + j := by
    simp only [pref, foldl_step_length, hz, List.length_take]
    omega
  have hpref_get : ∀ i < m + j, (C.gates.foldl step z).getD i false = pref.getD i false := by
    intro i hi
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
    exact foldl_step_getD_lt _ pref i (by omega)
  have hgate_eq : gateAt C j = C.gates[j] := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
  have hval : (C.gates.foldl step z).getD (m + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pref.getD i false) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlt : m + j < (step pref C.gates[j]).length := by
      simp only [step, List.length_append, List.length_singleton, hplen]; omega
    rw [foldl_step_getD_lt _ (step pref C.gates[j]) (m + j) hlt, List.getD_eq_getElem _ _ hlt]
    have hidx : m + j = pref.length := hplen.symm
    simp only [step, hidx, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
  rw [hval, hgate_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < m + j := hRB j hj i (hgate_eq ▸ hi)
  exact (hpref_get i hilt).symm

lemma gate_inputs_pair {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [gi0 C j, gi1 C j] := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  dsimp only [gi0, gi1]
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => simp [h] at hlen
  | [_] => simp [h] at hlen
  | _ :: _ :: _ :: _ => simp [h] at hlen

lemma gate_inputs_lt {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) {j : ℕ} (hj : j < C.gates.length) :
    gi0 C j < m + j ∧ gi1 C j < m + j := by
  have hpair := gate_inputs_pair hAO hj
  have h0 : gi0 C j ∈ (gateAt C j).inputs := by rw [hpair]; simp
  have h1 : gi1 C j ∈ (gateAt C j).inputs := by rw [hpair]; simp
  exact ⟨hAO.2.1 j hj _ h0, hAO.2.1 j hj _ h1⟩

lemma wv_and_eq {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) {z : List Bool} (hz : z.length = m)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wv C z (m + j) = (wv C z (gi0 C j) && wv C z (gi1 C j)) := by
  rw [wv_gate m C hAO.2.1 z hz j hj, hop, gate_inputs_pair hAO hj]
  simp [GateOp.eval]

lemma wv_or_eq {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) {z : List Bool} (hz : z.length = m)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wv C z (m + j) = (wv C z (gi0 C j) || wv C z (gi1 C j)) := by
  rw [wv_gate m C hAO.2.1 z hz j hj, hop, gate_inputs_pair hAO hj]
  simp [GateOp.eval]

lemma wv_mono {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) {x y : List Bool}
    (hx : x.length = m) (hy : y.length = m)
    (hle : ∀ i < m, x.getD i false = true → y.getD i false = true) :
    ∀ w : ℕ, wv C x w = true → wv C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases h1 : w < m
    · rw [wv_input C x w (by omega)] at htrue
      rw [wv_input C y w (by omega)]
      exact hle w h1 htrue
    · by_cases h2 : w - m < C.gates.length
      · let j := w - m
        have hjlt : j < C.gates.length := h2
        have hwj : w = m + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj] at htrue ⊢
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [wv_and_eq hAO hx hjlt hand, Bool.and_eq_true] at htrue
          rw [wv_and_eq hAO hy hjlt hand, Bool.and_eq_true]
          exact ⟨ih _ (by omega) htrue.1, ih _ (by omega) htrue.2⟩
        · rw [wv_or_eq hAO hx hjlt hor, Bool.or_eq_true] at htrue
          rw [wv_or_eq hAO hy hjlt hor, Bool.or_eq_true]
          rcases htrue with h | h
          · exact Or.inl (ih _ (by omega) h)
          · exact Or.inr (ih _ (by omega) h)
      · rw [wv_ge C x w (by omega)] at htrue
        cases htrue

lemma wv_congr {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) {x y : List Bool}
    (hx : x.length = m) (hy : y.length = m)
    (heq : ∀ i < m, x.getD i false = y.getD i false) :
    ∀ w : ℕ, wv C x w = wv C y w := by
  intro w
  cases h : wv C x w with
  | true => exact (wv_mono hAO hx hy (fun i hi ht => by rw [← heq i hi, ht]) w h).symm
  | false =>
    cases h2 : wv C y w with
    | false => rfl
    | true =>
      have := wv_mono hAO hy hx (fun i hi ht => by rw [heq i hi, ht]) w h2
      rw [h] at this; cases this

def unitVec (m i : ℕ) : List Bool :=
  List.ofFn fun k : Fin m => decide (k.val = i)

def pairVec (m i j : ℕ) : List Bool :=
  List.ofFn fun k : Fin m => decide (k.val = i ∨ k.val = j)

def allFalse (m : ℕ) : List Bool :=
  List.ofFn fun _ : Fin m => false

def zFlip (m : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  List.ofFn fun k : Fin m => z.getD k.val false || decide (k.val = i)

lemma unitVec_length (m i : ℕ) : (unitVec m i).length = m := by simp [unitVec]

lemma pairVec_length (m i j : ℕ) : (pairVec m i j).length = m := by simp [pairVec]

lemma allFalse_length (m : ℕ) : (allFalse m).length = m := by simp [allFalse]

lemma zFlip_length (m : ℕ) (z : List Bool) (i : ℕ) : (zFlip m z i).length = m := by simp [zFlip]

lemma unitVec_getD (m i k : ℕ) (hk : k < m) :
    (unitVec m i).getD k false = decide (k = i) := by
  have hlt : k < (unitVec m i).length := by rw [unitVec_length]; exact hk
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [unitVec, List.getElem_ofFn]

lemma pairVec_getD (m i j k : ℕ) (hk : k < m) :
    (pairVec m i j).getD k false = decide (k = i ∨ k = j) := by
  have hlt : k < (pairVec m i j).length := by rw [pairVec_length]; exact hk
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [pairVec, List.getElem_ofFn]

lemma allFalse_getD (m k : ℕ) (hk : k < m) :
    (allFalse m).getD k false = false := by
  have hlt : k < (allFalse m).length := by rw [allFalse_length]; exact hk
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [allFalse, List.getElem_ofFn]

lemma zFlip_getD (m : ℕ) (z : List Bool) (i k : ℕ) (hk : k < m) :
    (zFlip m z i).getD k false = (z.getD k false || decide (k = i)) := by
  have hlt : k < (zFlip m z i).length := by rw [zFlip_length]; exact hk
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [zFlip, List.getElem_ofFn]

lemma incidenceInput_length {N : ℕ} (X Y : Finset (Fin N)) :
    (incidenceInput X Y).length = N + N := by
  simp [incidenceInput]

lemma incidenceInput_getD_pt {N : ℕ} (X Y : Finset (Fin N)) (p : Fin N) :
    (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
  have hlt1 : p.val < (List.ofFn fun x : Fin N => decide (x ∈ X)).length := by simp
  have hlt2 : p.val < (incidenceInput X Y).length := by
    rw [incidenceInput_length]; exact Nat.lt_trans p.isLt (by omega)
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [incidenceInput, List.getElem_append_left hlt1, List.getElem_ofFn, Fin.eta]

lemma incidenceInput_getD_ln {N : ℕ} (X Y : Finset (Fin N)) (l : Fin N) :
    (incidenceInput X Y).getD (N + l.val) false = decide (l ∈ Y) := by
  have hlt2 : N + l.val < (incidenceInput X Y).length := by
    rw [incidenceInput_length]; omega
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [incidenceInput]
  have hge : (List.ofFn fun x : Fin N => decide (x ∈ X)).length ≤ N + l.val := by simp
  rw [List.getElem_append_right hge]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn, Fin.eta]

lemma incidenceInput_getD_lt {N : ℕ} (X Y : Finset (Fin N)) (i : ℕ) (hi : i < N + N) :
    (incidenceInput X Y).getD i false = true ↔
      (∃ h : i < N, (⟨i, h⟩ : Fin N) ∈ X) ∨ (∃ h : N ≤ i, (⟨i - N, by omega⟩ : Fin N) ∈ Y) := by
  by_cases h1 : i < N
  · have := incidenceInput_getD_pt X Y ⟨i, h1⟩
    simp only [this, decide_eq_true_iff]
    constructor
    · intro h; exact Or.inl ⟨h1, h⟩
    · rintro (⟨_, h⟩ | ⟨hge, _⟩)
      · exact h
      · omega
  · have hge : N ≤ i := by omega
    have hi_eq : i = N + (i - N) := by omega
    have := incidenceInput_getD_ln X Y ⟨i - N, by omega⟩
    rw [← hi_eq] at this
    simp only [this, decide_eq_true_iff]
    constructor
    · intro h; exact Or.inr ⟨hge, h⟩
    · rintro (⟨hlt, _⟩ | ⟨_, h⟩)
      · omega
      · exact h

section Plane

def linesThrough {N : ℕ} (S : Fin N → Finset (Fin N)) (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun l => p ∈ S l

lemma linesThrough_card {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (p : Fin N) :
    (linesThrough S p).card = q + 1 := by
  let f : Fin N → Finset (Fin N) := fun l => (S l).erase p
  have hbiU : (linesThrough S p).biUnion f = Finset.univ.erase p := by
    ext x
    simp only [Finset.mem_biUnion, linesThrough, Finset.mem_filter, Finset.mem_univ, true_and,
      f, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨l, _, hne, _⟩; exact hne
    · intro hne
      obtain ⟨l, ⟨hp, hx⟩, _⟩ := huniq p x hne.symm
      exact ⟨l, hp, hne, hx⟩
  have hdisj : Set.PairwiseDisjoint (↑(linesThrough S p) : Set (Fin N)) f := by
    intro l1 hl1 l2 hl2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [f, Finset.mem_erase] at hx1 hx2
    simp only [Finset.mem_coe, linesThrough, Finset.mem_filter, Finset.mem_univ, true_and] at hl1 hl2
    obtain ⟨l, _, hlu⟩ := huniq p x hx1.1.symm
    have h1 := hlu l1 ⟨hl1, hx1.2⟩
    have h2 := hlu l2 ⟨hl2, hx2.2⟩
    exact hne (h1.trans h2.symm)
  have hsum : ((linesThrough S p).biUnion f).card = (linesThrough S p).card * q := by
    rw [Finset.card_biUnion hdisj]
    have hconst : ∀ l ∈ linesThrough S p, (f l).card = q := by
      intro l hl
      have hpl : p ∈ S l := (Finset.mem_filter.mp hl).2
      dsimp only [f]
      rw [Finset.card_erase_of_mem hpl, hcard l]
      omega
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rw [hbiU, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hsum
  have hmul : (linesThrough S p).card * q = (q + 1) * q := by
    have : N - 1 = (q + 1) * q := by rw [hN]; ring_nf; omega
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) hmul

lemma lines_inter_card_le_one {N : ℕ} (S : Fin N → Finset (Fin N))
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (l1 l2 : Fin N) (hne : l1 ≠ l2) :
    (S l1 ∩ S l2).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p1 hp1 p2 hp2
  by_contra hne_p
  simp only [Finset.mem_inter] at hp1 hp2
  obtain ⟨l, _, hlu⟩ := huniq p1 p2 hne_p
  exact hne ((hlu l1 ⟨hp1.1, hp2.1⟩).trans (hlu l2 ⟨hp1.2, hp2.2⟩).symm)

lemma lines_inter_card {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (l1 l2 : Fin N) (hne : l1 ≠ l2) :
    (S l1 ∩ S l2).card = 1 := by
  have hsum_eq : ∑ l ∈ Finset.univ.erase l1, (S l1 ∩ S l).card = (Finset.univ.erase l1).card := by
    have h1 : ∀ l : Fin N, (S l1 ∩ S l).card = ∑ p ∈ S l1, if p ∈ S l then 1 else 0 := by
      intro l
      rw [← Finset.card_filter]
      congr 1
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ p ∈ S l1, (∑ l ∈ Finset.univ.erase l1, if p ∈ S l then 1 else 0) = q := by
      intro p hp
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ.erase l1).filter (fun l => p ∈ S l) = (linesThrough S p).erase l1 := by
        ext l; simp [linesThrough, and_comm]
      have hl1_mem : l1 ∈ linesThrough S p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      rw [hfilt, Finset.card_erase_of_mem hl1_mem, linesThrough_card S hq hN hcard huniq p]
      omega
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, hcard l1,
      Finset.card_erase_of_mem (Finset.mem_univ l1), Finset.card_univ, Fintype.card_fin]
    rw [hN]; ring_nf; omega
  have hle : (S l1 ∩ S l2).card ≤ 1 := lines_inter_card_le_one S huniq l1 l2 hne
  by_contra hne1
  have hlt : (S l1 ∩ S l2).card < 1 := by omega
  have hmem : l2 ∈ Finset.univ.erase l1 := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ l2⟩
  have hlt_sum : ∑ l ∈ Finset.univ.erase l1, (S l1 ∩ S l).card < ∑ _l ∈ Finset.univ.erase l1, 1 := by
    apply Finset.sum_lt_sum
    · intro l hl
      exact lines_inter_card_le_one S huniq l1 l (Finset.mem_erase.mp hl).1.symm
    · exact ⟨l2, hmem, hlt⟩
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt_sum
  omega

lemma indep_card_le {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (AP AL : Finset (Fin N)) (hind : ∀ p ∈ AP, ∀ l ∈ AL, p ∉ S l) :
    AP.card + AL.card ≤ N := by
  have h1 : ∑ p ∈ AP, ∑ l ∈ Finset.univ \ AL, (if p ∈ S l then 1 else 0) = AP.card * (q + 1) := by
    have hin : ∀ p ∈ AP, (∑ l ∈ Finset.univ \ AL, if p ∈ S l then 1 else 0) = q + 1 := by
      intro p hp
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ \ AL).filter (fun l => p ∈ S l) = linesThrough S p := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, linesThrough]
        exact ⟨fun h => h.2, fun h => ⟨fun hl => hind p hp l hl h, h⟩⟩
      rw [hfilt, linesThrough_card S hq hN hcard huniq p]
    rw [Finset.sum_congr rfl hin, Finset.sum_const, smul_eq_mul]
  have h2 : ∑ l ∈ Finset.univ \ AL, ∑ p ∈ AP, (if p ∈ S l then 1 else 0) ≤
      (Finset.univ \ AL).card * (q + 1) := by
    calc ∑ l ∈ Finset.univ \ AL, ∑ p ∈ AP, (if p ∈ S l then 1 else 0)
        ≤ ∑ l ∈ Finset.univ \ AL, (q + 1) := by
          apply Finset.sum_le_sum
          intro l _
          rw [← Finset.card_filter, ← hcard l]
          apply Finset.card_le_card
          intro p hp
          exact (Finset.mem_filter.mp hp).2
      _ = (Finset.univ \ AL).card * (q + 1) := by rw [Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_comm] at h1
  rw [h1] at h2
  have hle := Nat.le_of_mul_le_mul_right h2 (by omega : 0 < q + 1)
  have hdiff : (Finset.univ \ AL).card = N - AL.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ AL), Finset.card_univ, Fintype.card_fin]
  have hAL : AL.card ≤ N := by
    have := Finset.card_le_univ AL
    simpa using this
  omega

lemma exists_max_false_input {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) :
    ∃ P0 L0 : Finset (Fin N),
      P0.card = q ∧ L0.card = q ∧ IsFalseInput S P0 L0 ∧
      (∀ p : Fin N, p ∉ P0 → ∃ l ∈ L0, p ∈ S l) ∧
      (∀ l : Fin N, l ∉ L0 → ∃ p ∈ P0, p ∈ S l) := by
  have hNpos : 0 < N := by rw [hN]; nlinarith
  let p0 : Fin N := ⟨0, hNpos⟩
  have hlt_ne : (linesThrough S p0).Nonempty := by
    rw [← Finset.card_pos, linesThrough_card S hq hN hcard huniq p0]; omega
  obtain ⟨l0, hl0⟩ := hlt_ne
  have hp0l0 : p0 ∈ S l0 := (Finset.mem_filter.mp hl0).2
  let L0 := (linesThrough S p0).erase l0
  let P0 := (S l0).erase p0
  refine ⟨P0, L0, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [P0]; rw [Finset.card_erase_of_mem hp0l0, hcard l0]; omega
  · dsimp only [L0]; rw [Finset.card_erase_of_mem hl0, linesThrough_card S hq hN hcard huniq p0]; omega
  · intro l hl
    rw [Finset.disjoint_left]
    intro p hpl hpP0
    have hlne : l ≠ l0 := (Finset.mem_erase.mp hl).1
    have hp0l : p0 ∈ S l := (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2
    have hpne : p ≠ p0 := (Finset.mem_erase.mp hpP0).1
    have hpl0 : p ∈ S l0 := (Finset.mem_erase.mp hpP0).2
    have h1 := lines_inter_card_le_one S huniq l l0 hlne
    rw [Finset.card_le_one] at h1
    exact hpne (h1 p (Finset.mem_inter.mpr ⟨hpl, hpl0⟩) p0 (Finset.mem_inter.mpr ⟨hp0l, hp0l0⟩))
  · intro p hp
    by_cases heq : p = p0
    · subst heq
      have hL0ne : L0.Nonempty := by
        rw [← Finset.card_pos]
        dsimp only [L0]
        rw [Finset.card_erase_of_mem hl0, linesThrough_card S hq hN hcard huniq p0]; omega
      obtain ⟨l, hl⟩ := hL0ne
      exact ⟨l, hl, (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2⟩
    · have hpnotl0 : p ∉ S l0 := fun h => hp (Finset.mem_erase.mpr ⟨heq, h⟩)
      obtain ⟨l, ⟨hp0l, hpl⟩, _⟩ := huniq p0 p (Ne.symm heq)
      have hlne : l ≠ l0 := fun e => hpnotl0 (e ▸ hpl)
      exact ⟨l, Finset.mem_erase.mpr ⟨hlne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0l⟩⟩, hpl⟩
  · intro l hl
    by_cases heq : l = l0
    · subst heq
      have hP0ne : P0.Nonempty := by
        rw [← Finset.card_pos]
        dsimp only [P0]; rw [Finset.card_erase_of_mem hp0l0, hcard l]; omega
      obtain ⟨p, hp⟩ := hP0ne
      exact ⟨p, hp, (Finset.mem_erase.mp hp).2⟩
    · have hp0not : p0 ∉ S l := fun h =>
        hl (Finset.mem_erase.mpr ⟨heq, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
      have hinter : (S l ∩ S l0).Nonempty := by
        rw [← Finset.card_pos, lines_inter_card S hq hN hcard huniq l l0 heq]; omega
      obtain ⟨p, hp⟩ := hinter
      simp only [Finset.mem_inter] at hp
      have hpne : p ≠ p0 := fun e => hp0not (e ▸ hp.1)
      exact ⟨p, Finset.mem_erase.mpr ⟨hpne, hp.2⟩, hp.1⟩

lemma exists_sep_false {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (x y : ℕ) (hx : x < N + N) (hy : y < N + N) (hne : x ≠ y) :
    ∃ (P L : Finset (Fin N)),
      L.card ≤ q ∧ IsFalseInput S P L ∧
      (incidenceInput P L).getD y false = true ∧
      (incidenceInput P L).getD x false = false ∧
      ∃ (p l : Fin N), p ∈ S l ∧
        ∀ k < N + N, (incidenceInput {p} {l}).getD k false = true →
          (zFlip (N + N) (incidenceInput P L) x).getD k false = true := by
  have hq1 : 1 ≤ q := by omega
  by_cases hx1 : x < N
  · let px : Fin N := ⟨x, hx1⟩
    by_cases hy1 : y < N
    · let py : Fin N := ⟨y, hy1⟩
      have hne_p : px ≠ py := fun e => hne (congrArg Fin.val e)
      obtain ⟨l_xy, ⟨_, _⟩, hlu⟩ := huniq px py hne_p
      have hne_lt : ((linesThrough S px).erase l_xy).Nonempty := by
        rw [← Finset.card_pos]
        have hc := linesThrough_card S hq1 hN hcard huniq px
        have := Finset.card_erase_le (s := linesThrough S px) (a := l_xy)
        have hlt2 : (linesThrough S px).card - 1 ≤ ((linesThrough S px).erase l_xy).card := by
          by_cases hm : l_xy ∈ linesThrough S px
          · rw [Finset.card_erase_of_mem hm]
          · rw [Finset.erase_eq_of_notMem hm]; omega
        omega
      obtain ⟨l, hl⟩ := hne_lt
      have hlne : l ≠ l_xy := (Finset.mem_erase.mp hl).1
      have hpxl : px ∈ S l := (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2
      have hpynot : py ∉ S l := fun h => hlne (hlu l ⟨hpxl, h⟩)
      refine ⟨{py}, {l}, by simp; omega, ?_, ?_, ?_, px, l, hpxl, ?_⟩
      · intro l' hl'; simp only [Finset.mem_singleton] at hl'; subst hl'
        simp [Finset.disjoint_singleton_right, hpynot]
      · have := incidenceInput_getD_pt ({py} : Finset (Fin N)) {l} py
        simpa [py] using this
      · have := incidenceInput_getD_pt ({py} : Finset (Fin N)) {l} px
        simpa [px, hne_p] using this
      · intro k hk ht
        rw [zFlip_getD (N + N) _ x k hk, Bool.or_eq_true]
        rw [incidenceInput_getD_lt _ _ k hk] at ht
        rcases ht with ⟨hkN, hp'⟩ | ⟨hkge, hl'⟩
        · simp only [Finset.mem_singleton] at hp'
          right
          have : k = x := by have := congrArg Fin.val hp'; simpa [px] using this
          simp [this]
        · simp only [Finset.mem_singleton] at hl'
          left
          have hk_eq : k = N + l.val := by have := congrArg Fin.val hl'; simp only at this; omega
          rw [hk_eq]
          simpa using incidenceInput_getD_ln ({py} : Finset (Fin N)) {l} l
    · let ly : Fin N := ⟨y - N, by omega⟩
      have hlt_ne : (linesThrough S px).Nonempty := by
        rw [← Finset.card_pos, linesThrough_card S hq1 hN hcard huniq px]; omega
      obtain ⟨l, hl⟩ := hlt_ne
      have hpxl : px ∈ S l := (Finset.mem_filter.mp hl).2
      refine ⟨∅, {l, ly}, ?_, ?_, ?_, ?_, px, l, hpxl, ?_⟩
      · have := Finset.card_insert_le l ({ly} : Finset (Fin N)); simp at this; omega
      · intro l' _; simp
      · have hy_eq : y = N + ly.val := by simp [ly]; omega
        rw [hy_eq]
        simpa using incidenceInput_getD_ln (∅ : Finset (Fin N)) {l, ly} ly
      · have := incidenceInput_getD_pt (∅ : Finset (Fin N)) {l, ly} px
        simpa [px] using this
      · intro k hk ht
        rw [zFlip_getD (N + N) _ x k hk, Bool.or_eq_true]
        rw [incidenceInput_getD_lt _ _ k hk] at ht
        rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
        · simp only [Finset.mem_singleton] at hp'
          right
          have : k = x := by have := congrArg Fin.val hp'; simpa [px] using this
          simp [this]
        · simp only [Finset.mem_singleton] at hl'
          left
          have hk_eq : k = N + l.val := by have := congrArg Fin.val hl'; simp only at this; omega
          rw [hk_eq]
          simpa using incidenceInput_getD_ln (∅ : Finset (Fin N)) {l, ly} l
  · let lx : Fin N := ⟨x - N, by omega⟩
    have hx_eq : x = N + lx.val := by simp [lx]; omega
    by_cases hy1 : y < N
    · let py : Fin N := ⟨y, hy1⟩
      have hSne : (S lx).Nonempty := by rw [← Finset.card_pos, hcard lx]; omega
      obtain ⟨p, hplx⟩ := hSne
      refine ⟨{p, py}, ∅, by simp, by intro l hl; simp at hl, ?_, ?_, p, lx, hplx, ?_⟩
      · have := incidenceInput_getD_pt ({p, py} : Finset (Fin N)) ∅ py
        simpa [py] using this
      · rw [hx_eq]
        simpa using incidenceInput_getD_ln ({p, py} : Finset (Fin N)) ∅ lx
      · intro k hk ht
        rw [zFlip_getD (N + N) _ x k hk, Bool.or_eq_true]
        rw [incidenceInput_getD_lt _ _ k hk] at ht
        rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
        · simp only [Finset.mem_singleton] at hp'
          left
          have hk_eq : k = p.val := by have := congrArg Fin.val hp'; simpa using this
          rw [hk_eq]
          simpa using incidenceInput_getD_pt ({p, py} : Finset (Fin N)) ∅ p
        · simp only [Finset.mem_singleton] at hl'
          right
          have hk_eq : k = x := by have := congrArg Fin.val hl'; simp only at this; omega
          simp [hk_eq]
    · let ly : Fin N := ⟨y - N, by omega⟩
      have hy_eq : y = N + ly.val := by simp [ly]; omega
      have hne_l : lx ≠ ly := fun e => hne (by have := congrArg Fin.val e; omega)
      have hdiff_ne : (S lx \ S ly).Nonempty := by
        rw [← Finset.card_pos]
        have h1 : (S lx ∩ S ly).card ≤ 1 := lines_inter_card_le_one S huniq lx ly hne_l
        have h2 := Finset.card_sdiff_add_card_inter (S lx) (S ly)
        rw [hcard lx] at h2
        omega
      obtain ⟨p, hp⟩ := hdiff_ne
      simp only [Finset.mem_sdiff] at hp
      refine ⟨{p}, {ly}, by simp; omega, ?_, ?_, ?_, p, lx, hp.1, ?_⟩
      · intro l' hl'; simp only [Finset.mem_singleton] at hl'; subst hl'
        simp [Finset.disjoint_singleton_right, hp.2]
      · rw [hy_eq]
        simpa using incidenceInput_getD_ln ({p} : Finset (Fin N)) {ly} ly
      · rw [hx_eq]
        simpa [hne_l] using incidenceInput_getD_ln ({p} : Finset (Fin N)) {ly} lx
      · intro k hk ht
        rw [zFlip_getD (N + N) _ x k hk, Bool.or_eq_true]
        rw [incidenceInput_getD_lt _ _ k hk] at ht
        rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
        · simp only [Finset.mem_singleton] at hp'
          left
          have hk_eq : k = p.val := by have := congrArg Fin.val hp'; simpa using this
          rw [hk_eq]
          simpa using incidenceInput_getD_pt ({p} : Finset (Fin N)) {ly} p
        · simp only [Finset.mem_singleton] at hl'
          right
          have hk_eq : k = x := by have := congrArg Fin.val hl'; simp only at this; omega
          simp [hk_eq]

def neighborsOf {N : ℕ} (S : Fin N → Finset (Fin N)) (x : ℕ) : Finset ℕ :=
  if h : x < N then (linesThrough S ⟨x, h⟩).image (fun l => N + l.val)
  else if h2 : x - N < N then (S ⟨x - N, h2⟩).image (fun p => p.val)
  else ∅

lemma neighborsOf_card {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (x : ℕ) (hx : x < N + N) :
    (neighborsOf S x).card = q + 1 := by
  dsimp only [neighborsOf]
  split_ifs with h1 h2
  · rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega)),
      linesThrough_card S hq hN hcard huniq ⟨x, h1⟩]
  · rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext h), hcard ⟨x - N, h2⟩]
  · omega

lemma neighborsOf_lt {N : ℕ} (S : Fin N → Finset (Fin N)) (x y : ℕ) (hy : y ∈ neighborsOf S x) :
    y < N + N ∧ y ≠ x := by
  dsimp only [neighborsOf] at hy
  split_ifs at hy with h1 h2
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨by omega, by omega⟩
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨by omega, by omega⟩
  · simp at hy

lemma neighborsOf_inc {N : ℕ} (S : Fin N → Finset (Fin N)) (x y : ℕ) (hy : y ∈ neighborsOf S x) :
    ∃ p l : Fin N, p ∈ S l ∧
      ∀ k < N + N, (incidenceInput {p} {l}).getD k false = true →
        (pairVec (N + N) x y).getD k false = true := by
  dsimp only [neighborsOf] at hy
  split_ifs at hy with h1 h2
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
    have hpl : (⟨x, h1⟩ : Fin N) ∈ S l := (Finset.mem_filter.mp hl).2
    refine ⟨⟨x, h1⟩, l, hpl, ?_⟩
    intro k hk ht
    rw [pairVec_getD (N + N) x (N + l.val) k hk, decide_eq_true_iff]
    rw [incidenceInput_getD_lt _ _ k hk] at ht
    rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
    · simp only [Finset.mem_singleton] at hp'
      left; have := congrArg Fin.val hp'; simpa using this
    · simp only [Finset.mem_singleton] at hl'
      right; have := congrArg Fin.val hl'; simp only at this; omega
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨p, ⟨x - N, h2⟩, hp, ?_⟩
    intro k hk ht
    rw [pairVec_getD (N + N) x p.val k hk, decide_eq_true_iff]
    rw [incidenceInput_getD_lt _ _ k hk] at ht
    rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
    · simp only [Finset.mem_singleton] at hp'
      right; have := congrArg Fin.val hp'; simpa using this
    · simp only [Finset.mem_singleton] at hl'
      left; have := congrArg Fin.val hl'; simp only at this; omega
  · simp at hy

end Plane

section ReachAndDeg

def inCone (m : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if m ≤ w ∧ w - m < C.gates.length then
    let j := w - m
    let u := gi0 C j
    let v := gi1 C j
    if _hu : u < w then
      if _hv : v < w then
        insert j (inCone m C u ∪ inCone m C v)
      else ∅
    else ∅
  else ∅
termination_by w

lemma inCone_lt (m : ℕ) (C : Circuit) (w : ℕ) (hw : w < m) :
    inCone m C w = ∅ := by
  rw [inCone]
  have h1 : ¬ (m ≤ w ∧ w - m < C.gates.length) := by omega
  simp only [h1, ↓reduceIte]

lemma inCone_gate {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (j : ℕ) (hj : j < C.gates.length) :
    inCone m C (m + j) = insert j (inCone m C (gi0 C j) ∪ inCone m C (gi1 C j)) := by
  rw [inCone]
  have h1 : m ≤ m + j ∧ m + j - m < C.gates.length := ⟨by omega, by omega⟩
  have hsub : m + j - m = j := by omega
  have hlt := gate_inputs_lt hAO hj
  rw [ite_eq_left_iff.mpr fun hn => absurd h1 hn]
  simp only [hsub, hlt.1, hlt.2, ↓reduceDIte]

lemma inCone_sub_range {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) :
    ∀ w : ℕ, inCone m C w ⊆ Finset.range C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : m ≤ w ∧ w - m < C.gates.length
    · let j := w - m
      have hw : w = m + j := by omega
      have hj : j < C.gates.length := h.2
      have hlt := gate_inputs_lt hAO hj
      rw [hw, inCone_gate hAO j hj]
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_union] at hk
      rcases hk with rfl | hk | hk
      · exact Finset.mem_range.mpr hj
      · exact ih _ (by omega) hk
      · exact ih _ (by omega) hk
    · rw [inCone]; simp [h]

lemma inCone_le {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) :
    ∀ w : ℕ, ∀ k ∈ inCone m C w, m + k ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk
    by_cases h : m ≤ w ∧ w - m < C.gates.length
    · let j := w - m
      have hw : w = m + j := by omega
      have hj : j < C.gates.length := h.2
      have hlt := gate_inputs_lt hAO hj
      rw [hw, inCone_gate hAO j hj] at hk
      simp only [Finset.mem_insert, Finset.mem_union] at hk
      rcases hk with rfl | hk | hk
      · omega
      · have := ih _ (by omega) k hk; omega
      · have := ih _ (by omega) k hk; omega
    · rw [inCone] at hk; simp [h] at hk

lemma inCone_closed {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) :
    ∀ w : ℕ, ∀ k ∈ inCone m C w,
      (gi0 C k < m ∨ ∃ t ∈ inCone m C w, gi0 C k = m + t) ∧
      (gi1 C k < m ∨ ∃ t ∈ inCone m C w, gi1 C k = m + t) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk
    by_cases h : m ≤ w ∧ w - m < C.gates.length
    · let j := w - m
      have hw : w = m + j := by omega
      have hj : j < C.gates.length := h.2
      have hlt := gate_inputs_lt hAO hj
      rw [hw, inCone_gate hAO j hj] at hk ⊢
      simp only [Finset.mem_insert, Finset.mem_union] at hk
      rcases hk with rfl | hk | hk
      · constructor
        · by_cases h0 : gi0 C j < m
          · exact Or.inl h0
          · right
            have h0lt : gi0 C j - m < C.gates.length := by omega
            refine ⟨gi0 C j - m, ?_, by omega⟩
            have heq : gi0 C j = m + (gi0 C j - m) := by omega
            have hmem : gi0 C j - m ∈ inCone m C (m + (gi0 C j - m)) := by
              rw [inCone_gate hAO _ h0lt]; exact Finset.mem_insert_self _ _
            rw [← heq] at hmem
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hmem)
        · by_cases h1 : gi1 C j < m
          · exact Or.inl h1
          · right
            have h1lt : gi1 C j - m < C.gates.length := by omega
            refine ⟨gi1 C j - m, ?_, by omega⟩
            have heq : gi1 C j = m + (gi1 C j - m) := by omega
            have hmem : gi1 C j - m ∈ inCone m C (m + (gi1 C j - m)) := by
              rw [inCone_gate hAO _ h1lt]; exact Finset.mem_insert_self _ _
            rw [← heq] at hmem
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hmem)
      · have hc := ih _ (by omega) k hk
        exact ⟨hc.1.imp_right fun ⟨t, ht, e⟩ => ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), e⟩,
               hc.2.imp_right fun ⟨t, ht, e⟩ => ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), e⟩⟩
      · have hc := ih _ (by omega) k hk
        exact ⟨hc.1.imp_right fun ⟨t, ht, e⟩ => ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), e⟩,
               hc.2.imp_right fun ⟨t, ht, e⟩ => ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), e⟩⟩
    · rw [inCone] at hk; simp [h] at hk

lemma inCone_has_parent {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) :
    ∀ w : ℕ, ∀ k ∈ inCone m C w, m + k ≠ w →
      ∃ j ∈ inCone m C w, gi0 C j = m + k ∨ gi1 C j = m + k := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk hne
    by_cases h : m ≤ w ∧ w - m < C.gates.length
    · let j := w - m
      have hw : w = m + j := by omega
      have hj : j < C.gates.length := h.2
      have hlt := gate_inputs_lt hAO hj
      rw [hw, inCone_gate hAO j hj] at hk ⊢
      simp only [Finset.mem_insert, Finset.mem_union] at hk
      rcases hk with rfl | hk | hk
      · exact absurd hw.symm hne
      · by_cases heq : m + k = gi0 C j
        · exact ⟨j, Finset.mem_insert_self _ _, Or.inl heq.symm⟩
        · obtain ⟨p, hp, hpar⟩ := ih _ (by omega) k hk heq
          exact ⟨p, Finset.mem_insert_of_mem (Finset.mem_union_left _ hp), hpar⟩
      · by_cases heq : m + k = gi1 C j
        · exact ⟨j, Finset.mem_insert_self _ _, Or.inr heq.symm⟩
        · obtain ⟨p, hp, hpar⟩ := ih _ (by omega) k hk heq
          exact ⟨p, Finset.mem_insert_of_mem (Finset.mem_union_right _ hp), hpar⟩
    · rw [inCone] at hk; simp [h] at hk

def deg (C : Circuit) (R : Finset ℕ) (w : ℕ) : ℕ :=
  ∑ j ∈ R, ((if gi0 C j = w then 1 else 0) + (if gi1 C j = w then 1 else 0))

lemma deg_pos_of_reader (C : Circuit) (R : Finset ℕ) (w j : ℕ) (hj : j ∈ R)
    (hr : gi0 C j = w ∨ gi1 C j = w) :
    1 ≤ deg C R w := by
  have h1 : 1 ≤ (if gi0 C j = w then 1 else 0) + (if gi1 C j = w then 1 else 0) := by
    rcases hr with h | h <;> simp [h]
  have h2 := Finset.single_le_sum (f := fun k => (if gi0 C k = w then 1 else 0) + (if gi1 C k = w then 1 else 0))
    (fun _ _ => Nat.zero_le _) hj
  exact le_trans h1 h2

lemma deg_ge_two_of_two_readers (C : Circuit) (R : Finset ℕ) (w j1 j2 : ℕ)
    (hj1 : j1 ∈ R) (hj2 : j2 ∈ R) (hne : j1 ≠ j2)
    (hr1 : gi0 C j1 = w ∨ gi1 C j1 = w) (hr2 : gi0 C j2 = w ∨ gi1 C j2 = w) :
    2 ≤ deg C R w := by
  let f : ℕ → ℕ := fun k => (if gi0 C k = w then 1 else 0) + (if gi1 C k = w then 1 else 0)
  have hf1 : 1 ≤ f j1 := by dsimp only [f]; rcases hr1 with h | h <;> simp [h]
  have hf2 : 1 ≤ f j2 := by dsimp only [f]; rcases hr2 with h | h <;> simp [h]
  have hsub : ({j1, j2} : Finset ℕ) ⊆ R := by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have hle : ∑ k ∈ ({j1, j2} : Finset ℕ), f k ≤ ∑ k ∈ R, f k :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hne] at hle
  change 2 ≤ ∑ k ∈ R, f k
  omega

lemma deg_ge_two_of_both_slots (C : Circuit) (R : Finset ℕ) (w j : ℕ) (hj : j ∈ R)
    (h0 : gi0 C j = w) (h1 : gi1 C j = w) :
    2 ≤ deg C R w := by
  have hle := Finset.single_le_sum (f := fun k => (if gi0 C k = w then 1 else 0) + (if gi1 C k = w then 1 else 0))
    (fun _ _ => Nat.zero_le _) hj
  simp only [h0, h1, ↓reduceIte] at hle
  exact hle

lemma deg_eq_one_exists_reader (C : Circuit) (R : Finset ℕ) (w : ℕ) (h1 : deg C R w = 1) :
    ∃ j ∈ R, (gi0 C j = w ∧ gi1 C j ≠ w) ∨ (gi1 C j = w ∧ gi0 C j ≠ w) := by
  have hne0 : ∃ j ∈ R, (if gi0 C j = w then 1 else 0) + (if gi1 C j = w then 1 else 0) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz : deg C R w = 0 := Finset.sum_eq_zero hall
    omega
  obtain ⟨j, hj, hjne⟩ := hne0
  have h01 : gi0 C j = w ∨ gi1 C j = w := by
    by_contra h
    push Not at h
    simp [h.1, h.2] at hjne
  have hnboth : ¬ (gi0 C j = w ∧ gi1 C j = w) := by
    rintro ⟨ha, hb⟩
    have := deg_ge_two_of_both_slots C R w j hj ha hb
    omega
  refine ⟨j, hj, ?_⟩
  rcases h01 with ha | hb
  · left; exact ⟨ha, fun e => hnboth ⟨ha, e⟩⟩
  · right; exact ⟨hb, fun e => hnboth ⟨e, hb⟩⟩

lemma sum_deg_eq {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ) :
    let R := inCone m C w0
    (∑ x ∈ Finset.range m, deg C R x) + (∑ j ∈ R, deg C R (m + j)) = 2 * R.card := by
  intro R
  let U := Finset.range m ∪ R.image (fun j => m + j)
  have hdisj : Disjoint (Finset.range m) (R.image (fun j => m + j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    have hlt := Finset.mem_range.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx2
    omega
  have hsumU : ∑ w ∈ U, deg C R w =
      (∑ x ∈ Finset.range m, deg C R x) + (∑ j ∈ R, deg C R (m + j)) := by
    dsimp only [U]
    rw [Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => by omega)]
  rw [← hsumU]
  unfold deg
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ R, ∑ w ∈ U, ((if gi0 C j = w then 1 else 0) + (if gi1 C j = w then 1 else 0)) = 2 := by
    intro j hj
    have hcl := inCone_closed hAO w0 j hj
    have h0U : gi0 C j ∈ U := by
      dsimp only [U]
      rcases hcl.1 with h | ⟨t, ht, he⟩
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, he.symm⟩)
    have h1U : gi1 C j ∈ U := by
      dsimp only [U]
      rcases hcl.2 with h | ⟨t, ht, he⟩
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, he.symm⟩)
    rw [Finset.sum_add_distrib]
    simp [h0U, h1U]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]

lemma wire_deg_bound {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (outJ : ℕ)
    (hout : C.output = m + outJ) (houtLt : outJ < C.gates.length) :
    let R := inCone m C C.output
    (∑ x ∈ Finset.range m, deg C R x) + (∑ j ∈ R.erase outJ, (deg C R (m + j) - 1)) ≤ R.card + 1 := by
  intro R
  have houtR : outJ ∈ R := by
    dsimp only [R]; rw [hout, inCone_gate hAO outJ houtLt]; exact Finset.mem_insert_self _ _
  have hpos : ∀ j ∈ R.erase outJ, 1 ≤ deg C R (m + j) := by
    intro j hj
    have hne : j ≠ outJ := (Finset.mem_erase.mp hj).1
    have hjR : j ∈ R := (Finset.mem_erase.mp hj).2
    obtain ⟨p, hp, hr⟩ := inCone_has_parent hAO C.output j hjR (by omega)
    exact deg_pos_of_reader C R (m + j) p hp hr
  have hsub_sum : (∑ j ∈ R.erase outJ, (deg C R (m + j) - 1)) + (R.erase outJ).card =
      ∑ j ∈ R.erase outJ, deg C R (m + j) := by
    have : ∑ j ∈ R.erase outJ, ((deg C R (m + j) - 1) + 1) = ∑ j ∈ R.erase outJ, deg C R (m + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have := hpos j hj
      omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
    exact this
  have hle_R : ∑ j ∈ R.erase outJ, deg C R (m + j) ≤ ∑ j ∈ R, deg C R (m + j) :=
    Finset.sum_le_sum_of_subset (Finset.erase_subset outJ R)
  have hsum := sum_deg_eq hAO C.output
  dsimp only at hsum
  have hcardE : (R.erase outJ).card = R.card - 1 := Finset.card_erase_of_mem houtR
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨outJ, houtR⟩
  dsimp only [R] at hsub_sum hle_R hcardE hRpos ⊢
  omega

end ReachAndDeg

section Chain

def oneHot (m : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun y => wv C (unitVec m y) w = true

lemma oneHot_input (m : ℕ) (C : Circuit) (x : ℕ) (hx : x < m) :
    oneHot m C x = {x} := by
  ext y
  simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, ht⟩
    rw [wv_input C _ x (by rw [unitVec_length]; exact hx), unitVec_getD m y x hx, decide_eq_true_iff] at ht
    exact ht.symm
  · rintro rfl
    refine ⟨hx, ?_⟩
    rw [wv_input C _ y (by rw [unitVec_length]; exact hx), unitVec_getD m y y hx]
    simp

lemma oneHot_gate_sub {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (j : ℕ) (hj : j < C.gates.length) :
    oneHot m C (m + j) ⊆ oneHot m C (gi0 C j) ∪ oneHot m C (gi1 C j) := by
  intro y hy
  simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hy ⊢
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  rcases hAO.1 (gateAt C j) hmem with hand | hor
  · rw [wv_and_eq hAO (unitVec_length m y) hj hand, Bool.and_eq_true] at hy
    exact Or.inl ⟨hy.1, hy.2.1⟩
  · rw [wv_or_eq hAO (unitVec_length m y) hj hor, Bool.or_eq_true] at hy
    rcases hy.2 with h | h
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨hy.1, h⟩

def GraphBarrier (m : ℕ) (C : Circuit) (R : Finset ℕ) (x : ℕ) (Ch : Finset ℕ) (w : ℕ) : Prop :=
  x ∈ Ch ∧ w ∈ Ch ∧
  (∀ c ∈ Ch, c ≤ w) ∧
  (∀ c ∈ Ch, c ≠ w → deg C R c = 1 ∧ ∃ j ∈ R, m + j ∈ Ch ∧ (gi0 C j = c ∨ gi1 C j = c))

lemma barrier_eval_eq {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ)
    (x : ℕ) (Ch : Finset ℕ) (w : ℕ)
    (hB : GraphBarrier m C (inCone m C w0) x Ch w)
    (z1 z2 : List Bool) (hz1 : z1.length = m) (hz2 : z2.length = m)
    (hagree : ∀ i < m, i ≠ x → z1.getD i false = z2.getD i false)
    (hw_eq : wv C z1 w = wv C z2 w) :
    ∀ u : ℕ, (u < m ∨ ∃ k ∈ inCone m C w0, u = m + k) → u ∉ Ch →
      wv C z1 u = wv C z2 u := by
  let R := inCone m C w0
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu huCh
    rcases hu with hu_lt | ⟨k, hkR, rfl⟩
    · rw [wv_input C z1 u (by omega), wv_input C z2 u (by omega)]
      have hne : u ≠ x := fun e => huCh (e ▸ hB.1)
      exact hagree u hu_lt hne
    · have hklt : k < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hkR)
      have hlt := gate_inputs_lt hAO hklt
      have hcl := inCone_closed hAO w0 k hkR
      have hchild : ∀ a : ℕ, a < m + k → (a < m ∨ ∃ t ∈ R, a = m + t) →
          (gi0 C k = a ∨ gi1 C k = a) → wv C z1 a = wv C z2 a := by
        intro a halt haR har
        by_cases haCh : a ∈ Ch
        · by_cases haw : a = w
          · rw [haw]; exact hw_eq
          · obtain ⟨hdeg1, j, hjR, hjCh, hjr⟩ := hB.2.2.2 a haCh haw
            have hne_kj : k ≠ j := fun e => huCh (e ▸ hjCh)
            have hdeg2 := deg_ge_two_of_two_readers C R a k j hkR hjR hne_kj har hjr
            dsimp only [R] at hdeg2
            omega
        · exact ih a halt haR haCh
      have h0 := hchild (gi0 C k) hlt.1 hcl.1 (Or.inl rfl)
      have h1 := hchild (gi1 C k) hlt.2 hcl.2 (Or.inr rfl)
      have hmem : gateAt C k ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
      rcases hAO.1 (gateAt C k) hmem with hand | hor
      · rw [wv_and_eq hAO hz1 hklt hand, wv_and_eq hAO hz2 hklt hand, h0, h1]
      · rw [wv_or_eq hAO hz1 hklt hor, wv_or_eq hAO hz2 hklt hor, h0, h1]

lemma barrier_indep_lt {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ)
    (x : ℕ) (Ch : Finset ℕ) (w : ℕ)
    (hB : GraphBarrier m C (inCone m C w0) x Ch w)
    (hdegw : deg C (inCone m C w0) w = 1)
    (j : ℕ) (hjR : j ∈ inCone m C w0) (hjr : gi0 C j = w ∨ gi1 C j = w)
    (z1 z2 : List Bool) (hz1 : z1.length = m) (hz2 : z2.length = m)
    (hagree : ∀ i < m, i ≠ x → z1.getD i false = z2.getD i false) :
    ∀ u : ℕ, u < m + j → (u < m ∨ ∃ k ∈ inCone m C w0, u = m + k) → u ∉ Ch →
      wv C z1 u = wv C z2 u := by
  let R := inCone m C w0
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hult huR huCh
    rcases huR with hu_lt | ⟨k, hkR, rfl⟩
    · rw [wv_input C z1 u (by omega), wv_input C z2 u (by omega)]
      have hne : u ≠ x := fun e => huCh (e ▸ hB.1)
      exact hagree u hu_lt hne
    · have hklt : k < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hkR)
      have hlt := gate_inputs_lt hAO hklt
      have hcl := inCone_closed hAO w0 k hkR
      have hne_kj : k ≠ j := by omega
      have hchild : ∀ a : ℕ, a < m + k → (a < m ∨ ∃ t ∈ R, a = m + t) →
          (gi0 C k = a ∨ gi1 C k = a) → wv C z1 a = wv C z2 a := by
        intro a halt haR har
        by_cases haCh : a ∈ Ch
        · by_cases haw : a = w
          · subst haw
            have hdeg2 := deg_ge_two_of_two_readers C R a k j hkR hjR hne_kj har hjr
            dsimp only [R] at hdeg2
            omega
          · obtain ⟨hdeg1, j', hj'R, hj'Ch, hj'r⟩ := hB.2.2.2 a haCh haw
            have hne_kj' : k ≠ j' := fun e => huCh (e ▸ hj'Ch)
            have hdeg2 := deg_ge_two_of_two_readers C R a k j' hkR hj'R hne_kj' har hj'r
            dsimp only [R] at hdeg2
            omega
        · exact ih a halt (by omega) haR haCh
      have h0 := hchild (gi0 C k) hlt.1 hcl.1 (Or.inl rfl)
      have h1 := hchild (gi1 C k) hlt.2 hcl.2 (Or.inr rfl)
      have hmem : gateAt C k ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
      rcases hAO.1 (gateAt C k) hmem with hand | hor
      · rw [wv_and_eq hAO hz1 hklt hand, wv_and_eq hAO hz2 hklt hand, h0, h1]
      · rw [wv_or_eq hAO hz1 hklt hor, wv_or_eq hAO hz2 hklt hor, h0, h1]

lemma barrier_other_not_mem {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ)
    (x : ℕ) (Ch : Finset ℕ) (w : ℕ)
    (hB : GraphBarrier m C (inCone m C w0) x Ch w)
    (_hdegw : deg C (inCone m C w0) w = 1)
    (j : ℕ) (hjR : j ∈ inCone m C w0)
    (v : ℕ) (hvne : v ≠ w) (hvr : gi0 C j = v ∨ gi1 C j = v) (hwr : gi0 C j = w ∨ gi1 C j = w) :
    v ∉ Ch := by
  intro hvCh
  obtain ⟨hdeg1, j', hj'R, hj'Ch, hj'r⟩ := hB.2.2.2 v hvCh hvne
  have hjlt : j < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hjR)
  have hlt := gate_inputs_lt hAO hjlt
  have hwlt : w < m + j := by rcases hwr with h | h <;> omega
  have hj'le : m + j' ≤ w := hB.2.2.1 (m + j') hj'Ch
  have hne : j ≠ j' := by omega
  have hdeg2 := deg_ge_two_of_two_readers C (inCone m C w0) v j j' hjR hj'R hne hvr hj'r
  omega

lemma barrier_deg_zero_absurd {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ)
    (x : ℕ) (Ch : Finset ℕ) (w : ℕ)
    (hB : GraphBarrier m C (inCone m C w0) x Ch w)
    (hdeg0 : deg C (inCone m C w0) w = 0)
    (z1 z2 : List Bool) (hz1 : z1.length = m) (hz2 : z2.length = m)
    (hagree : ∀ i < m, i ≠ x → z1.getD i false = z2.getD i false) :
    ∀ u : ℕ, (u < m ∨ ∃ k ∈ inCone m C w0, u = m + k) → u ∉ Ch →
      wv C z1 u = wv C z2 u := by
  let R := inCone m C w0
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu huCh
    rcases hu with hu_lt | ⟨k, hkR, rfl⟩
    · rw [wv_input C z1 u (by omega), wv_input C z2 u (by omega)]
      have hne : u ≠ x := fun e => huCh (e ▸ hB.1)
      exact hagree u hu_lt hne
    · have hklt : k < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hkR)
      have hlt := gate_inputs_lt hAO hklt
      have hcl := inCone_closed hAO w0 k hkR
      have hchild : ∀ a : ℕ, a < m + k → (a < m ∨ ∃ t ∈ R, a = m + t) →
          (gi0 C k = a ∨ gi1 C k = a) → wv C z1 a = wv C z2 a := by
        intro a halt haR har
        by_cases haCh : a ∈ Ch
        · by_cases haw : a = w
          · subst haw
            have hpos := deg_pos_of_reader C R a k hkR har
            dsimp only [R] at hpos
            omega
          · obtain ⟨hdeg1, j, hjR, hjCh, hjr⟩ := hB.2.2.2 a haCh haw
            have hne_kj : k ≠ j := fun e => huCh (e ▸ hjCh)
            have hdeg2 := deg_ge_two_of_two_readers C R a k j hkR hjR hne_kj har hjr
            dsimp only [R] at hdeg2
            omega
        · exact ih a halt haR haCh
      have h0 := hchild (gi0 C k) hlt.1 hcl.1 (Or.inl rfl)
      have h1 := hchild (gi1 C k) hlt.2 hcl.2 (Or.inr rfl)
      have hmem : gateAt C k ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
      rcases hAO.1 (gateAt C k) hmem with hand | hor
      · rw [wv_and_eq hAO hz1 hklt hand, wv_and_eq hAO hz2 hklt hand, h0, h1]
      · rw [wv_or_eq hAO hz1 hklt hor, wv_or_eq hAO hz2 hklt hor, h0, h1]

end Chain

section DagExpand

lemma dag_expand {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (E : Finset ℕ) (ch : ℕ → ℕ × ℕ)
    (hlt : ∀ w ∈ E, (ch w).1 < w ∧ (ch w).2 < w)
    (hsub : ∀ w ∈ E, F w ⊆ F (ch w).1 ∪ F (ch w).2)
    (hclosed : ∀ w ∈ E, ((ch w).1 ∈ E ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E ∨ (F (ch w).2).card ≤ 1)) :
    ∀ (W : Finset ℕ), (∀ w ∈ W, w ∈ E ∨ (F w).card ≤ 1) →
      (W.biUnion F).card ≤ W.card + E.card := by
  classical
  have hgen : ∀ (k : ℕ) (E : Finset ℕ), E.card = k →
      (∀ w ∈ E, (ch w).1 < w ∧ (ch w).2 < w) →
      (∀ w ∈ E, F w ⊆ F (ch w).1 ∪ F (ch w).2) →
      (∀ w ∈ E, ((ch w).1 ∈ E ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E ∨ (F (ch w).2).card ≤ 1)) →
      ∀ (W : Finset ℕ), (∀ w ∈ W, w ∈ E ∨ (F w).card ≤ 1) →
        (W.biUnion F).card ≤ W.card + E.card := by
    intro k
    induction k with
    | zero =>
      intro E hcard _ _ _ W hW
      have hE : E = ∅ := Finset.card_eq_zero.mp hcard
      subst hE
      calc (W.biUnion F).card
          ≤ ∑ w ∈ W, (F w).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum fun w hw => (hW w hw).resolve_left (by simp)
        _ = W.card := by simp
        _ = W.card + (∅ : Finset ℕ).card := by simp
    | succ k ih =>
      intro E hcard hlt hsub hclosed W hW
      have hne : E.Nonempty := Finset.card_pos.mp (by omega)
      let m := E.max' hne
      have hmE : m ∈ E := Finset.max'_mem E hne
      let E' := E.erase m
      have hE'card : E'.card = k := by
        change (E.erase m).card = k; rw [Finset.card_erase_of_mem hmE]; omega
      have hlt' : ∀ w ∈ E', (ch w).1 < w ∧ (ch w).2 < w := fun w hw => hlt w (Finset.mem_of_mem_erase hw)
      have hsub' : ∀ w ∈ E', F w ⊆ F (ch w).1 ∪ F (ch w).2 := fun w hw => hsub w (Finset.mem_of_mem_erase hw)
      have hclosed' : ∀ w ∈ E',
          ((ch w).1 ∈ E' ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E' ∨ (F (ch w).2).card ≤ 1) := by
        intro w hw
        have hwE : w ∈ E := Finset.mem_of_mem_erase hw
        have hwm : w ≤ m := Finset.le_max' E w hwE
        have hc := hclosed w hwE
        have hltw := hlt w hwE
        constructor
        · rcases hc.1 with h | h
          · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
          · exact Or.inr h
        · rcases hc.2 with h | h
          · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
          · exact Or.inr h
      by_cases hmW : m ∈ W
      · let W' := insert (ch m).1 (insert (ch m).2 (W.erase m))
        have hW'ok : ∀ w ∈ W', w ∈ E' ∨ (F w).card ≤ 1 := by
          intro w hw
          simp only [W', Finset.mem_insert, Finset.mem_erase] at hw
          have hcm := hclosed m hmE
          have hltm := hlt m hmE
          rcases hw with rfl | rfl | ⟨hwne, hwW⟩
          · rcases hcm.1 with h | h
            · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
            · exact Or.inr h
          · rcases hcm.2 with h | h
            · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
            · exact Or.inr h
          · rcases hW w hwW with h | h
            · left; exact Finset.mem_erase.mpr ⟨hwne, h⟩
            · exact Or.inr h
        have hW'sub : W.biUnion F ⊆ W'.biUnion F := by
          intro a ha
          obtain ⟨w, hwW, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwm : w = m
          · subst hwm
            have h1 := hsub m hmE haw
            simp only [Finset.mem_union] at h1
            rcases h1 with h | h
            · exact Finset.mem_biUnion.mpr ⟨(ch m).1, Finset.mem_insert_self _ _, h⟩
            · exact Finset.mem_biUnion.mpr ⟨(ch m).2,
                Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
          · exact Finset.mem_biUnion.mpr ⟨w,
              Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hwW⟩)), haw⟩
        have hW'card : W'.card ≤ W.card + 1 := by
          change (insert (ch m).1 (insert (ch m).2 (W.erase m))).card ≤ W.card + 1
          have h1 := Finset.card_insert_le (ch m).1 (insert (ch m).2 (W.erase m))
          have h2 := Finset.card_insert_le (ch m).2 (W.erase m)
          have h3 := Finset.card_erase_of_mem hmW
          have h4 : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hmW⟩
          omega
        have hih := ih E' hE'card hlt' hsub' hclosed' W' hW'ok
        have hle := Finset.card_le_card hW'sub
        omega
      · have hWok : ∀ w ∈ W, w ∈ E' ∨ (F w).card ≤ 1 := by
          intro w hw
          have hne : w ≠ m := fun e => hmW (e ▸ hw)
          rcases hW w hw with h | h
          · left; exact Finset.mem_erase.mpr ⟨hne, h⟩
          · exact Or.inr h
        have hih := ih E' hE'card hlt' hsub' hclosed' W hWok
        omega
  exact hgen E.card E rfl hlt hsub hclosed

lemma dag_expand_ub {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (E E2 : Finset ℕ) (ch : ℕ → ℕ × ℕ)
    (hlt : ∀ w ∈ E, (ch w).1 < w ∧ (ch w).2 < w)
    (hsub2 : ∀ w ∈ E, w ∈ E2 → F w ⊆ F (ch w).1 ∪ F (ch w).2)
    (hsub1 : ∀ w ∈ E, w ∉ E2 → F w ⊆ F (ch w).1 ∨ F w ⊆ F (ch w).2 ∨ F w = ∅)
    (hclosed : ∀ w ∈ E, ((ch w).1 ∈ E ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E ∨ (F (ch w).2).card ≤ 1)) :
    ∀ (W : Finset ℕ), (∀ w ∈ W, w ∈ E ∨ (F w).card ≤ 1) →
      (W.biUnion F).card ≤ W.card + (E ∩ E2).card := by
  classical
  have hgen : ∀ (k : ℕ) (E : Finset ℕ), E.card = k →
      (∀ w ∈ E, (ch w).1 < w ∧ (ch w).2 < w) →
      (∀ w ∈ E, w ∈ E2 → F w ⊆ F (ch w).1 ∪ F (ch w).2) →
      (∀ w ∈ E, w ∉ E2 → F w ⊆ F (ch w).1 ∨ F w ⊆ F (ch w).2 ∨ F w = ∅) →
      (∀ w ∈ E, ((ch w).1 ∈ E ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E ∨ (F (ch w).2).card ≤ 1)) →
      ∀ (W : Finset ℕ), (∀ w ∈ W, w ∈ E ∨ (F w).card ≤ 1) →
        (W.biUnion F).card ≤ W.card + (E ∩ E2).card := by
    intro k
    induction k with
    | zero =>
      intro E hcard _ _ _ _ W hW
      have hE : E = ∅ := Finset.card_eq_zero.mp hcard
      subst hE
      calc (W.biUnion F).card
          ≤ ∑ w ∈ W, (F w).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum fun w hw => (hW w hw).resolve_left (by simp)
        _ = W.card := by simp
        _ = W.card + ((∅ : Finset ℕ) ∩ E2).card := by simp
    | succ k ih =>
      intro E hcard hlt hsub2 hsub1 hclosed W hW
      have hne : E.Nonempty := Finset.card_pos.mp (by omega)
      let m := E.max' hne
      have hmE : m ∈ E := Finset.max'_mem E hne
      let E' := E.erase m
      have hE'card : E'.card = k := by
        change (E.erase m).card = k; rw [Finset.card_erase_of_mem hmE]; omega
      have hlt' : ∀ w ∈ E', (ch w).1 < w ∧ (ch w).2 < w := fun w hw => hlt w (Finset.mem_of_mem_erase hw)
      have hsub2' : ∀ w ∈ E', w ∈ E2 → F w ⊆ F (ch w).1 ∪ F (ch w).2 :=
        fun w hw => hsub2 w (Finset.mem_of_mem_erase hw)
      have hsub1' : ∀ w ∈ E', w ∉ E2 → F w ⊆ F (ch w).1 ∨ F w ⊆ F (ch w).2 ∨ F w = ∅ :=
        fun w hw => hsub1 w (Finset.mem_of_mem_erase hw)
      have hclosed' : ∀ w ∈ E',
          ((ch w).1 ∈ E' ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E' ∨ (F (ch w).2).card ≤ 1) := by
        intro w hw
        have hwE : w ∈ E := Finset.mem_of_mem_erase hw
        have hwm : w ≤ m := Finset.le_max' E w hwE
        have hc := hclosed w hwE
        have hltw := hlt w hwE
        constructor
        · rcases hc.1 with h | h
          · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
          · exact Or.inr h
        · rcases hc.2 with h | h
          · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
          · exact Or.inr h
      have hinter_le : (E' ∩ E2).card ≤ (E ∩ E2).card :=
        Finset.card_le_card (Finset.inter_subset_inter (Finset.erase_subset m E) (Finset.Subset.refl E2))
      by_cases hmW : m ∈ W
      · by_cases hmE2 : m ∈ E2
        · have hmInter : m ∈ E ∩ E2 := Finset.mem_inter.mpr ⟨hmE, hmE2⟩
          have hE'inter : E' ∩ E2 = (E ∩ E2).erase m := by
            ext x; simp only [E', Finset.mem_inter, Finset.mem_erase]; tauto
          have hE'inter_card : (E' ∩ E2).card + 1 = (E ∩ E2).card := by
            rw [hE'inter, Finset.card_erase_of_mem hmInter]
            have := Finset.card_pos.mpr ⟨m, hmInter⟩
            omega
          let W' := insert (ch m).1 (insert (ch m).2 (W.erase m))
          have hW'ok : ∀ w ∈ W', w ∈ E' ∨ (F w).card ≤ 1 := by
            intro w hw
            simp only [W', Finset.mem_insert, Finset.mem_erase] at hw
            have hcm := hclosed m hmE
            have hltm := hlt m hmE
            rcases hw with rfl | rfl | ⟨hwne, hwW⟩
            · rcases hcm.1 with h | h
              · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
              · exact Or.inr h
            · rcases hcm.2 with h | h
              · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
              · exact Or.inr h
            · rcases hW w hwW with h | h
              · left; exact Finset.mem_erase.mpr ⟨hwne, h⟩
              · exact Or.inr h
          have hW'sub : W.biUnion F ⊆ W'.biUnion F := by
            intro a ha
            obtain ⟨w, hwW, haw⟩ := Finset.mem_biUnion.mp ha
            by_cases hwm : w = m
            · subst hwm
              have h1 := hsub2 m hmE hmE2 haw
              simp only [Finset.mem_union] at h1
              rcases h1 with h | h
              · exact Finset.mem_biUnion.mpr ⟨(ch m).1, Finset.mem_insert_self _ _, h⟩
              · exact Finset.mem_biUnion.mpr ⟨(ch m).2,
                  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
            · exact Finset.mem_biUnion.mpr ⟨w,
                Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hwW⟩)), haw⟩
          have hW'card : W'.card ≤ W.card + 1 := by
            change (insert (ch m).1 (insert (ch m).2 (W.erase m))).card ≤ W.card + 1
            have h1 := Finset.card_insert_le (ch m).1 (insert (ch m).2 (W.erase m))
            have h2 := Finset.card_insert_le (ch m).2 (W.erase m)
            have h3 := Finset.card_erase_of_mem hmW
            have h4 : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hmW⟩
            omega
          have hih := ih E' hE'card hlt' hsub2' hsub1' hclosed' W' hW'ok
          have hle := Finset.card_le_card hW'sub
          omega
        · rcases hsub1 m hmE hmE2 with h1 | h2 | h3
          · let W' := insert (ch m).1 (W.erase m)
            have hW'ok : ∀ w ∈ W', w ∈ E' ∨ (F w).card ≤ 1 := by
              intro w hw
              simp only [W', Finset.mem_insert, Finset.mem_erase] at hw
              have hcm := hclosed m hmE
              have hltm := hlt m hmE
              rcases hw with rfl | ⟨hwne, hwW⟩
              · rcases hcm.1 with h | h
                · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
                · exact Or.inr h
              · rcases hW w hwW with h | h
                · left; exact Finset.mem_erase.mpr ⟨hwne, h⟩
                · exact Or.inr h
            have hW'sub : W.biUnion F ⊆ W'.biUnion F := by
              intro a ha
              obtain ⟨w, hwW, haw⟩ := Finset.mem_biUnion.mp ha
              by_cases hwm : w = m
              · subst hwm
                exact Finset.mem_biUnion.mpr ⟨(ch m).1, Finset.mem_insert_self _ _, h1 haw⟩
              · exact Finset.mem_biUnion.mpr ⟨w,
                  Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hwW⟩), haw⟩
            have hW'card : W'.card ≤ W.card := by
              change (insert (ch m).1 (W.erase m)).card ≤ W.card
              have hc1 := Finset.card_insert_le (ch m).1 (W.erase m)
              have hc2 := Finset.card_erase_of_mem hmW
              have hc3 : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hmW⟩
              omega
            have hih := ih E' hE'card hlt' hsub2' hsub1' hclosed' W' hW'ok
            have hle := Finset.card_le_card hW'sub
            omega
          · let W' := insert (ch m).2 (W.erase m)
            have hW'ok : ∀ w ∈ W', w ∈ E' ∨ (F w).card ≤ 1 := by
              intro w hw
              simp only [W', Finset.mem_insert, Finset.mem_erase] at hw
              have hcm := hclosed m hmE
              have hltm := hlt m hmE
              rcases hw with rfl | ⟨hwne, hwW⟩
              · rcases hcm.2 with h | h
                · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
                · exact Or.inr h
              · rcases hW w hwW with h | h
                · left; exact Finset.mem_erase.mpr ⟨hwne, h⟩
                · exact Or.inr h
            have hW'sub : W.biUnion F ⊆ W'.biUnion F := by
              intro a ha
              obtain ⟨w, hwW, haw⟩ := Finset.mem_biUnion.mp ha
              by_cases hwm : w = m
              · subst hwm
                exact Finset.mem_biUnion.mpr ⟨(ch m).2, Finset.mem_insert_self _ _, h2 haw⟩
              · exact Finset.mem_biUnion.mpr ⟨w,
                  Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hwW⟩), haw⟩
            have hW'card : W'.card ≤ W.card := by
              change (insert (ch m).2 (W.erase m)).card ≤ W.card
              have hc1 := Finset.card_insert_le (ch m).2 (W.erase m)
              have hc2 := Finset.card_erase_of_mem hmW
              have hc3 : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hmW⟩
              omega
            have hih := ih E' hE'card hlt' hsub2' hsub1' hclosed' W' hW'ok
            have hle := Finset.card_le_card hW'sub
            omega
          · let W' := W.erase m
            have hW'ok : ∀ w ∈ W', w ∈ E' ∨ (F w).card ≤ 1 := by
              intro w hw
              obtain ⟨hwne, hwW⟩ := Finset.mem_erase.mp hw
              rcases hW w hwW with h | h
              · left; exact Finset.mem_erase.mpr ⟨hwne, h⟩
              · exact Or.inr h
            have hW'sub : W.biUnion F ⊆ W'.biUnion F := by
              intro a ha
              obtain ⟨w, hwW, haw⟩ := Finset.mem_biUnion.mp ha
              by_cases hwm : w = m
              · subst hwm; rw [h3] at haw; simp at haw
              · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwm, hwW⟩, haw⟩
            have hW'card : W'.card ≤ W.card := Finset.card_erase_le
            have hih := ih E' hE'card hlt' hsub2' hsub1' hclosed' W' hW'ok
            have hle := Finset.card_le_card hW'sub
            omega
      · have hWok : ∀ w ∈ W, w ∈ E' ∨ (F w).card ≤ 1 := by
          intro w hw
          have hne : w ≠ m := fun e => hmW (e ▸ hw)
          rcases hW w hw with h | h
          · left; exact Finset.mem_erase.mpr ⟨hne, h⟩
          · exact Or.inr h
        have hih := ih E' hE'card hlt' hsub2' hsub1' hclosed' W hWok
        omega
  exact hgen E.card E rfl hlt hsub2 hsub1 hclosed

end DagExpand

section SensAndPriv

def sens (m : ℕ) (C : Circuit) (S0 : Finset ℕ) (andPick : ℕ → Option ℕ) (w : ℕ) : Finset ℕ :=
  if w < m then
    if w ∈ S0 then {w} else ∅
  else if w - m < C.gates.length then
    let j := w - m
    let u := gi0 C j
    let v := gi1 C j
    if _hu : u < w then
      if _hv : v < w then
        match (gateAt C j).op with
        | GateOp.or => sens m C S0 andPick u ∪ sens m C S0 andPick v
        | GateOp.and =>
          match andPick j with
          | some c => if _hc : c < w then sens m C S0 andPick c else ∅
          | none => ∅
        | _ => ∅
      else ∅
    else ∅
  else ∅
termination_by w

def sensVis (m : ℕ) (C : Circuit) (andPick : ℕ → Option ℕ) (w : ℕ) : Finset ℕ :=
  if w < m then ∅
  else if w - m < C.gates.length then
    let j := w - m
    let u := gi0 C j
    let v := gi1 C j
    if _hu : u < w then
      if _hv : v < w then
        match (gateAt C j).op with
        | GateOp.or => insert j (sensVis m C andPick u ∪ sensVis m C andPick v)
        | GateOp.and =>
          match andPick j with
          | some c => if _hc : c < w then insert j (sensVis m C andPick c) else {j}
          | none => {j}
        | _ => ∅
      else ∅
    else ∅
  else ∅
termination_by w

lemma sens_input (m : ℕ) (C : Circuit) (S0 : Finset ℕ) (andPick : ℕ → Option ℕ) (w : ℕ) (hw : w < m) :
    sens m C S0 andPick w = if w ∈ S0 then {w} else ∅ := by
  rw [sens]; simp only [hw, ↓reduceIte]

lemma sens_or {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (S0 : Finset ℕ) (andPick : ℕ → Option ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    sens m C S0 andPick (m + j) = sens m C S0 andPick (gi0 C j) ∪ sens m C S0 andPick (gi1 C j) := by
  rw [sens]
  have h1 : ¬ (m + j < m) := by omega
  have hsub : m + j - m = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma sens_and {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (S0 : Finset ℕ) (andPick : ℕ → Option ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    sens m C S0 andPick (m + j) =
      match andPick j with
      | some c => if c < m + j then sens m C S0 andPick c else ∅
      | none => ∅ := by
  rw [sens]
  have h1 : ¬ (m + j < m) := by omega
  have hsub : m + j - m = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]
  cases andPick j with
  | none => rfl
  | some c => by_cases hc : c < m + j <;> simp [hc]

lemma sensVis_input (m : ℕ) (C : Circuit) (andPick : ℕ → Option ℕ) (w : ℕ) (hw : w < m) :
    sensVis m C andPick w = ∅ := by
  rw [sensVis]; simp only [hw, ↓reduceIte]

lemma sensVis_or {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (andPick : ℕ → Option ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    sensVis m C andPick (m + j) =
      insert j (sensVis m C andPick (gi0 C j) ∪ sensVis m C andPick (gi1 C j)) := by
  rw [sensVis]
  have h1 : ¬ (m + j < m) := by omega
  have hsub : m + j - m = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma sensVis_and {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (andPick : ℕ → Option ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    sensVis m C andPick (m + j) =
      match andPick j with
      | some c => if c < m + j then insert j (sensVis m C andPick c) else {j}
      | none => {j} := by
  rw [sensVis]
  have h1 : ¬ (m + j < m) := by omega
  have hsub : m + j - m = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]
  cases andPick j with
  | none => rfl
  | some c => by_cases hc : c < m + j <;> simp [hc]

lemma sensVis_sub_inCone {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (andPick : ℕ → Option ℕ)
    (hvalid : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ c, andPick j = some c → c = gi0 C j ∨ c = gi1 C j) :
    ∀ w : ℕ, sensVis m C andPick w ⊆ inCone m C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < m
    · rw [sensVis_input m C andPick w h1]; simp
    · by_cases h2 : w - m < C.gates.length
      · let j := w - m
        have hjlt : j < C.gates.length := h2
        have hwj : w = m + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj, inCone_gate hAO j hjlt]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [sensVis_and hAO andPick j hjlt hand]
          cases hp : andPick j with
          | none => intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact Finset.mem_insert_self _ _
          | some c =>
            rcases hvalid j hjlt hand c hp with rfl | rfl
            · simp only [hlt.1, ↓reduceIte]
              intro k hk
              simp only [Finset.mem_insert] at hk ⊢
              rcases hk with rfl | hk
              · exact Or.inl rfl
              · exact Or.inr (Finset.mem_union_left _ (ih _ (by omega) hk))
            · simp only [hlt.2, ↓reduceIte]
              intro k hk
              simp only [Finset.mem_insert] at hk ⊢
              rcases hk with rfl | hk
              · exact Or.inl rfl
              · exact Or.inr (Finset.mem_union_right _ (ih _ (by omega) hk))
        · rw [sensVis_or hAO andPick j hjlt hor]
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_union] at hk ⊢
          rcases hk with rfl | hk | hk
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (ih _ (by omega) hk))
          · exact Or.inr (Or.inr (ih _ (by omega) hk))
      · rw [sensVis]; simp [h1, h2]

lemma sens_sound {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (z0 : List Bool) (hz0 : z0.length = m)
    (S0 : Finset ℕ) (andPick : ℕ → Option ℕ)
    (hpick : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      wv C z0 (m + j) = false →
      ∃ c, andPick j = some c ∧ (c = gi0 C j ∨ c = gi1 C j) ∧ wv C z0 c = false)
    (i : ℕ) (hiS : i ∈ S0) :
    ∀ w : ℕ, wv C z0 w = false → wv C (zFlip m z0 i) w = true → i ∈ sens m C S0 andPick w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hf ht
    by_cases h1 : w < m
    · rw [wv_input C z0 w (by omega)] at hf
      rw [wv_input C (zFlip m z0 i) w (by rw [zFlip_length]; omega), zFlip_getD m z0 i w h1, hf] at ht
      simp only [Bool.false_or, decide_eq_true_iff] at ht
      subst ht
      rw [sens_input m C S0 andPick w h1]; simp [hiS]
    · by_cases h2 : w - m < C.gates.length
      · let j := w - m
        have hjlt : j < C.gates.length := h2
        have hwj : w = m + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj] at hf ht ⊢
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · obtain ⟨c, hpc, hceq, hcf⟩ := hpick j hjlt hand hf
          rw [wv_and_eq hAO (zFlip_length m z0 i) hjlt hand, Bool.and_eq_true] at ht
          rw [sens_and hAO S0 andPick j hjlt hand, hpc]
          rcases hceq with rfl | rfl
          · simp only [hlt.1, ↓reduceIte]
            exact ih _ (by omega) hcf ht.1
          · simp only [hlt.2, ↓reduceIte]
            exact ih _ (by omega) hcf ht.2
        · rw [wv_or_eq hAO hz0 hjlt hor, Bool.or_eq_false_iff] at hf
          rw [wv_or_eq hAO (zFlip_length m z0 i) hjlt hor, Bool.or_eq_true] at ht
          rw [sens_or hAO S0 andPick j hjlt hor, Finset.mem_union]
          rcases ht with h | h
          · exact Or.inl (ih _ (by omega) hf.1 h)
          · exact Or.inr (ih _ (by omega) hf.2 h)
      · rw [wv_ge C (zFlip m z0 i) w (by rw [zFlip_length]; omega)] at ht
        cases ht

lemma sensVis_closed_step {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (S0 : Finset ℕ)
    (andPick : ℕ → Option ℕ)
    (hvalid : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ c, andPick j = some c → c = gi0 C j ∨ c = gi1 C j)
    (w0 : ℕ) :
    let V := sensVis m C andPick w0
    ∀ j ∈ V,
      ((gateAt C j).op = GateOp.or →
        ((gi0 C j ∈ V.image (m + ·) ∨ (sens m C S0 andPick (gi0 C j)).card ≤ 1) ∧
         (gi1 C j ∈ V.image (m + ·) ∨ (sens m C S0 andPick (gi1 C j)).card ≤ 1))) ∧
      ((gateAt C j).op = GateOp.and →
        ∀ c, andPick j = some c →
          c ∈ V.image (m + ·) ∨ (sens m C S0 andPick c).card ≤ 1) := by
  intro V
  have hmem_self : ∀ u : ℕ, u ∈ V.image (m + ·) ∨ (sens m C S0 andPick u).card ≤ 1 →
      True := fun _ _ => trivial
  have hgen : ∀ w : ℕ, ∀ j ∈ sensVis m C andPick w,
      ((gateAt C j).op = GateOp.or →
        ((gi0 C j ∈ (sensVis m C andPick w).image (m + ·) ∨ (sens m C S0 andPick (gi0 C j)).card ≤ 1) ∧
         (gi1 C j ∈ (sensVis m C andPick w).image (m + ·) ∨ (sens m C S0 andPick (gi1 C j)).card ≤ 1))) ∧
      ((gateAt C j).op = GateOp.and →
        ∀ c, andPick j = some c →
          c ∈ (sensVis m C andPick w).image (m + ·) ∨ (sens m C S0 andPick c).card ≤ 1) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      have hself_or_small : ∀ u : ℕ,
          u ∈ (sensVis m C andPick u).image (m + ·) ∨ (sens m C S0 andPick u).card ≤ 1 := by
        intro u
        by_cases h1 : u < m
        · right; rw [sens_input m C S0 andPick u h1]; split_ifs <;> simp
        · by_cases h2 : u - m < C.gates.length
          · left
            let k := u - m
            have hklt : k < C.gates.length := h2
            have huk : u = m + k := by omega
            have hmem : gateAt C k ∈ C.gates := by
              simp only [gateAt, List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
            refine Finset.mem_image.mpr ⟨k, ?_, huk.symm⟩
            rw [huk]
            rcases hAO.1 (gateAt C k) hmem with hand | hor
            · rw [sensVis_and hAO andPick k hklt hand]
              cases andPick k with
              | none => exact Finset.mem_singleton_self k
              | some c => by_cases hc : c < m + k <;> simp [hc]
            · rw [sensVis_or hAO andPick k hklt hor]
              exact Finset.mem_insert_self _ _
          · right; rw [sens]; simp [h1, h2]
      intro j hj
      by_cases h1 : w < m
      · rw [sensVis_input m C andPick w h1] at hj; simp at hj
      · by_cases h2 : w - m < C.gates.length
        · let j0 := w - m
          have hj0lt : j0 < C.gates.length := h2
          have hwj : w = m + j0 := by omega
          have hmem : gateAt C j0 ∈ C.gates := by
            simp only [gateAt, List.getD_eq_getElem _ _ hj0lt]; exact List.getElem_mem hj0lt
          have hlt := gate_inputs_lt hAO hj0lt
          rw [hwj] at hj ⊢
          rcases hAO.1 (gateAt C j0) hmem with hand | hor
          · rw [sensVis_and hAO andPick j0 hj0lt hand] at hj ⊢
            cases hp : andPick j0 with
            | none =>
              simp only [hp, Finset.mem_singleton] at hj
              subst hj
              exact ⟨(fun h => by rw [hand] at h; cases h), (fun _ _ hc => by rw [hp] at hc; cases hc)⟩
            | some c0 =>
              have hc0lt : c0 < m + j0 := by rcases hvalid j0 hj0lt hand c0 hp with rfl | rfl <;> omega
              simp only [hp, hc0lt, ↓reduceIte, Finset.mem_insert] at hj ⊢
              rcases hj with rfl | hjc
              · refine ⟨(fun h => by rw [hand] at h; cases h), (fun _ c hc => ?_)⟩
                rw [hp] at hc; injection hc with heq; subst heq
                rcases hself_or_small c0 with h | h
                · left
                  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
                  exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem ht, rfl⟩
                · exact Or.inr h
              · have hrec := ih c0 (by omega) j hjc
                refine ⟨fun h => ?_, fun h c hc => ?_⟩
                · have hr := hrec.1 h
                  exact ⟨hr.1.imp_left fun hi => by
                      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                      exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem ht, he⟩,
                    hr.2.imp_left fun hi => by
                      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                      exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem ht, he⟩⟩
                · exact (hrec.2 h c hc).imp_left fun hi => by
                    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                    exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem ht, he⟩
          · rw [sensVis_or hAO andPick j0 hj0lt hor] at hj ⊢
            simp only [Finset.mem_insert, Finset.mem_union] at hj
            rcases hj with rfl | hj0 | hj1
            · refine ⟨fun _ => ⟨?_, ?_⟩, fun h => by rw [hor] at h; cases h⟩
              · exact (hself_or_small (gi0 C j0)).imp_left fun hi => by
                  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                  exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), he⟩
              · exact (hself_or_small (gi1 C j0)).imp_left fun hi => by
                  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                  exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), he⟩
            · have hrec := ih _ (by omega) j hj0
              refine ⟨fun h => ?_, fun h c hc => ?_⟩
              · have hr := hrec.1 h
                exact ⟨hr.1.imp_left fun hi => by
                    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                    exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), he⟩,
                  hr.2.imp_left fun hi => by
                    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                    exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), he⟩⟩
              · exact (hrec.2 h c hc).imp_left fun hi => by
                  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                  exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), he⟩
            · have hrec := ih _ (by omega) j hj1
              refine ⟨fun h => ?_, fun h c hc => ?_⟩
              · have hr := hrec.1 h
                exact ⟨hr.1.imp_left fun hi => by
                    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                    exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), he⟩,
                  hr.2.imp_left fun hi => by
                    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                    exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), he⟩⟩
              · exact (hrec.2 h c hc).imp_left fun hi => by
                  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hi
                  exact Finset.mem_image.mpr ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), he⟩
        · rw [sensVis] at hj; simp [h1, h2] at hj
  exact hgen w0

lemma sens_card_le_vis_or {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (hm : 0 < m) (S0 : Finset ℕ)
    (andPick : ℕ → Option ℕ)
    (hvalid : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ c, andPick j = some c → c = gi0 C j ∨ c = gi1 C j)
    (w0 : ℕ) [DecidablePred (fun j => (gateAt C j).op = GateOp.or)] :
    let V := sensVis m C andPick w0
    let V_or := V.filter (fun j => (gateAt C j).op = GateOp.or)
    (sens m C S0 andPick w0).card ≤ 1 + V_or.card := by
  classical
  intro V V_or
  let E := V.image (fun j => m + j)
  let E2 := V_or.image (fun j => m + j)
  let ch (w : ℕ) : ℕ × ℕ :=
    let j := w - m
    if (gateAt C j).op = GateOp.and then
      match andPick j with
      | some c => (c, c)
      | none => (0, 0)
    else (gi0 C j, gi1 C j)
  have hV_sub : V ⊆ Finset.range C.gates.length :=
    Finset.Subset.trans (sensVis_sub_inCone hAO andPick hvalid w0) (inCone_sub_range hAO w0)
  have hcl := sensVis_closed_step hAO S0 andPick hvalid w0
  have hEE2 : E ∩ E2 = E2 := by
    apply Finset.inter_eq_right.mpr
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hE2card : E2.card = V_or.card := Finset.card_image_of_injective _ (fun _ _ h => by omega)
  have hzero_card : (sens m C S0 andPick 0).card ≤ 1 := by
    rw [sens_input m C S0 andPick 0 hm]; split_ifs <;> simp
  have hw0_ok : w0 ∈ E ∨ (sens m C S0 andPick w0).card ≤ 1 := by
    by_cases h1 : w0 < m
    · right; rw [sens_input m C S0 andPick w0 h1]; split_ifs <;> simp
    · by_cases h2 : w0 - m < C.gates.length
      · left
        let k := w0 - m
        have hklt : k < C.gates.length := h2
        have huk : w0 = m + k := by omega
        have hmem : gateAt C k ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
        refine Finset.mem_image.mpr ⟨k, ?_, huk.symm⟩
        dsimp only [V]; rw [huk]
        rcases hAO.1 (gateAt C k) hmem with hand | hor
        · rw [sensVis_and hAO andPick k hklt hand]
          cases andPick k with
          | none => exact Finset.mem_singleton_self k
          | some c => by_cases hc : c < m + k <;> simp [hc]
        · rw [sensVis_or hAO andPick k hklt hor]; exact Finset.mem_insert_self _ _
      · right; rw [sens]; simp [h1, h2]
  have hexp := dag_expand_ub (sens m C S0 andPick) E E2 ch
    (fun w hw => by
      obtain ⟨j, hjV, rfl⟩ := Finset.mem_image.mp hw
      have hjlt := Finset.mem_range.mp (hV_sub hjV)
      have hlt := gate_inputs_lt hAO hjlt
      dsimp only [ch]
      have hsub : m + j - m = j := by omega
      rw [hsub]
      split_ifs with hand
      · cases hp : andPick j with
        | none => dsimp only; exact ⟨by omega, by omega⟩
        | some c => dsimp only; rcases hvalid j hjlt hand c hp with rfl | rfl <;> exact ⟨by omega, by omega⟩
      · exact hlt)
    (fun w _ hw2 => by
      obtain ⟨j, hj2, rfl⟩ := Finset.mem_image.mp hw2
      have hjf := Finset.mem_filter.mp hj2
      have hjlt := Finset.mem_range.mp (hV_sub hjf.1)
      have hsub : m + j - m = j := by omega
      have hnot : (gateAt C j).op ≠ GateOp.and := fun h => by rw [hjf.2] at h; cases h
      rw [sens_or hAO S0 andPick j hjlt hjf.2]
      simp [ch, hsub, hnot])
    (fun w hw hnot2 => by
      obtain ⟨j, hjV, rfl⟩ := Finset.mem_image.mp hw
      have hjlt := Finset.mem_range.mp (hV_sub hjV)
      have hmem : gateAt C j ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
      rcases hAO.1 (gateAt C j) hmem with hand | hor
      · have hsub : m + j - m = j := by omega
        rw [sens_and hAO S0 andPick j hjlt hand]
        cases hp : andPick j with
        | none => right; right; rfl
        | some c =>
          have hclt : c < m + j := by
            have hlt := gate_inputs_lt hAO hjlt
            rcases hvalid j hjlt hand c hp with rfl | rfl <;> omega
          simp only [hclt, ↓reduceIte]
          left; simp [ch, hsub, hand, hp]
      · exfalso; apply hnot2
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hjV, hor⟩, rfl⟩)
    (fun w hw => by
      obtain ⟨j, hjV, rfl⟩ := Finset.mem_image.mp hw
      have hjlt := Finset.mem_range.mp (hV_sub hjV)
      have hmem : gateAt C j ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
      have hsub : m + j - m = j := by omega
      rcases hAO.1 (gateAt C j) hmem with hand | hor
      · cases hp : andPick j with
        | none =>
          simp [ch, hsub, hand, hp, hzero_card]
        | some c =>
          have hc := (hcl j hjV).2 hand c hp
          simp only [ch, hsub, hand, ↓reduceIte, hp]
          exact ⟨hc, hc⟩
      · have hnot : (gateAt C j).op ≠ GateOp.and := fun h => by rw [hor] at h; cases h
        have ho := (hcl j hjV).1 hor
        simp only [ch, hsub, hnot, ↓reduceIte]
        exact ho)
    {w0}
    (fun w hw => by simp only [Finset.mem_singleton] at hw; subst hw; exact hw0_ok)
  have hb : ({w0} : Finset ℕ).biUnion (sens m C S0 andPick) = sens m C S0 andPick w0 := by ext i; simp
  rw [hb, Finset.card_singleton, hEE2, hE2card] at hexp
  exact hexp

def privTree (m : ℕ) (C : Circuit) (R : Finset ℕ) (w : ℕ) : Finset ℕ :=
  if m ≤ w ∧ w - m ∈ R ∧ deg C R w = 1 ∧ 2 ≤ (oneHot m C w).card then
    let j := w - m
    let u := gi0 C j
    let v := gi1 C j
    if _hu : u < w then
      if _hv : v < w then
        insert j (privTree m C R u ∪ privTree m C R v)
      else ∅
    else ∅
  else ∅
termination_by w

lemma privTree_eq_empty_of_not {m : ℕ} {C : Circuit} {R : Finset ℕ} {w : ℕ}
    (h : ¬ (m ≤ w ∧ w - m ∈ R ∧ deg C R w = 1 ∧ 2 ≤ (oneHot m C w).card)) :
    privTree m C R w = ∅ := by
  rw [privTree]; simp only [h, ↓reduceIte]

lemma privTree_eq_insert {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ) (j : ℕ)
    (hjR : j ∈ inCone m C w0) (hdeg : deg C (inCone m C w0) (m + j) = 1)
    (hoh : 2 ≤ (oneHot m C (m + j)).card) :
    privTree m C (inCone m C w0) (m + j) =
      insert j (privTree m C (inCone m C w0) (gi0 C j) ∪ privTree m C (inCone m C w0) (gi1 C j)) := by
  have hjlt : j < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hjR)
  have hlt := gate_inputs_lt hAO hjlt
  rw [privTree]
  have hsub : m + j - m = j := by omega
  have hcond : m ≤ m + j ∧ m + j - m ∈ inCone m C w0 ∧ deg C (inCone m C w0) (m + j) = 1 ∧
      2 ≤ (oneHot m C (m + j)).card := ⟨by omega, by rw [hsub]; exact hjR, hdeg, hoh⟩
  rw [ite_eq_left_iff.mpr fun hn => absurd hcond hn]
  simp only [hsub, hlt.1, hlt.2, ↓reduceDIte]

lemma privTree_props {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ) :
    ∀ w : ℕ, ∀ t ∈ privTree m C (inCone m C w0) w,
      t ∈ inCone m C w0 ∧ deg C (inCone m C w0) (m + t) = 1 ∧ 2 ≤ (oneHot m C (m + t)).card := by
  let R := inCone m C w0
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro t ht
    by_cases h : m ≤ w ∧ w - m ∈ R ∧ deg C R w = 1 ∧ 2 ≤ (oneHot m C w).card
    · let j := w - m
      have hw : w = m + j := by omega
      have hjR : j ∈ R := h.2.1
      have hjlt : j < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hjR)
      have hlt := gate_inputs_lt hAO hjlt
      rw [hw] at h ht
      rw [privTree_eq_insert hAO w0 j hjR h.2.2.1 h.2.2.2] at ht
      simp only [Finset.mem_insert, Finset.mem_union] at ht
      rcases ht with rfl | ht | ht
      · exact ⟨hjR, h.2.2.1, h.2.2.2⟩
      · exact ih _ (by omega) t ht
      · exact ih _ (by omega) t ht
    · rw [privTree_eq_empty_of_not h] at ht; simp at ht

lemma privTree_reader_mem {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ) :
    ∀ w : ℕ, ∀ r ∈ inCone m C w0, (gi0 C r = w ∨ gi1 C r = w) →
      ∀ t ∈ privTree m C (inCone m C w0) w,
        ∀ p ∈ inCone m C w0, (gi0 C p = m + t ∨ gi1 C p = m + t) →
          p ∈ insert r (privTree m C (inCone m C w0) w) := by
  let R := inCone m C w0
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro r hrR hrr t ht p hpR hpr
    by_cases h : m ≤ w ∧ w - m ∈ R ∧ deg C R w = 1 ∧ 2 ≤ (oneHot m C w).card
    · let j := w - m
      have hw : w = m + j := by omega
      have hjR : j ∈ R := h.2.1
      have hjlt : j < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hjR)
      have hlt := gate_inputs_lt hAO hjlt
      rw [hw] at h hrr ht ⊢
      rw [privTree_eq_insert hAO w0 j hjR h.2.2.1 h.2.2.2] at ht ⊢
      simp only [Finset.mem_insert, Finset.mem_union] at ht ⊢
      rcases ht with rfl | ht | ht
      · by_cases hpr_eq : p = r
        · exact Or.inl hpr_eq
        · have h2 := deg_ge_two_of_two_readers C R (m + j) p r hpR hrR hpr_eq hpr hrr
          have := h.2.2.1; omega
      · have hrec := ih _ (by omega) j hjR (Or.inl rfl) t ht p hpR hpr
        simp only [Finset.mem_insert] at hrec
        rcases hrec with rfl | hrec
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl hrec))
      · have hrec := ih _ (by omega) j hjR (Or.inr rfl) t ht p hpR hpr
        simp only [Finset.mem_insert] at hrec
        rcases hrec with rfl | hrec
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr hrec))
    · rw [privTree_eq_empty_of_not h] at ht; simp at ht

lemma sensVis_disjoint_privTree {m : ℕ} {C : Circuit} (hAO : IsAO2 m C) (w0 : ℕ)
    (andPick : ℕ → Option ℕ)
    (hvalid : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ c, andPick j = some c → c = gi0 C j ∨ c = gi1 C j)
    (ax vx ux : ℕ) (haxR : ax ∈ inCone m C w0)
    (hax_and : (gateAt C ax).op = GateOp.and)
    (hax_vx : gi0 C ax = vx ∨ gi1 C ax = vx)
    (hpick_ax : andPick ax = some ux)
    (hux_oh : (oneHot m C ux).card ≤ 1) :
    let T := privTree m C (inCone m C w0) vx
    ∀ w : ℕ, (w < m ∨ ∃ k ∈ inCone m C w0, w = m + k) →
      (∀ t ∈ T, w ≠ m + t) → Disjoint (sensVis m C andPick w) T := by
  let R := inCone m C w0
  intro T w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR hwT
    rcases hwR with h1 | ⟨k, hkR, rfl⟩
    · rw [sensVis_input m C andPick w h1]
      exact Finset.disjoint_empty_left T
    · have hklt : k < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO w0 hkR)
      have hlt := gate_inputs_lt hAO hklt
      have hcl := inCone_closed hAO w0 k hkR
      have hk_notT : k ∉ T := fun h => hwT k h rfl
      have hmem : gateAt C k ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
      have hchild_notT : ∀ c : ℕ, k ≠ ax → (gi0 C k = c ∨ gi1 C k = c) → ∀ t ∈ T, c ≠ m + t := by
        intro c hne hcr t ht heq
        subst heq
        have hin := privTree_reader_mem hAO w0 vx ax haxR hax_vx t ht k hkR hcr
        simp only [Finset.mem_insert] at hin
        rcases hin with rfl | hin
        · exact hne rfl
        · exact hk_notT hin
      rcases hAO.1 (gateAt C k) hmem with hand | hor
      · rw [sensVis_and hAO andPick k hklt hand]
        by_cases hka : k = ax
        · subst hka
          rw [hpick_ax]
          have hux_r : ux = gi0 C k ∨ ux = gi1 C k := hvalid k hklt hand ux hpick_ax
          have hux_lt : ux < m + k := by rcases hux_r with rfl | rfl <;> omega
          have hux_R : ux < m ∨ ∃ t ∈ R, ux = m + t := by rcases hux_r with rfl | rfl; exact hcl.1; exact hcl.2
          have hux_notT : ∀ t ∈ T, ux ≠ m + t := by
            intro t ht heq
            have h2 := (privTree_props hAO w0 vx t ht).2.2
            rw [← heq] at h2
            omega
          simp only [hux_lt, ↓reduceIte]
          exact Finset.disjoint_insert_left.mpr ⟨hk_notT, ih ux hux_lt hux_R hux_notT⟩
        · cases hp : andPick k with
          | none => exact Finset.disjoint_singleton_left.mpr hk_notT
          | some c =>
            have hc_r : c = gi0 C k ∨ c = gi1 C k := hvalid k hklt hand c hp
            have hc_lt : c < m + k := by rcases hc_r with rfl | rfl <;> omega
            have hc_R : c < m ∨ ∃ t ∈ R, c = m + t := by rcases hc_r with rfl | rfl; exact hcl.1; exact hcl.2
            have hc_notT : ∀ t ∈ T, c ≠ m + t :=
              hchild_notT c hka (hc_r.imp Eq.symm Eq.symm)
            simp only [hc_lt, ↓reduceIte]
            exact Finset.disjoint_insert_left.mpr ⟨hk_notT, ih c hc_lt hc_R hc_notT⟩
      · rw [sensVis_or hAO andPick k hklt hor]
        have hka : k ≠ ax := fun e => by rw [e, hax_and] at hor; cases hor
        have hd0 := ih (gi0 C k) hlt.1 hcl.1 (hchild_notT _ hka (Or.inl rfl))
        have hd1 := ih (gi1 C k) hlt.2 hcl.2 (hchild_notT _ hka (Or.inr rfl))
        exact Finset.disjoint_insert_left.mpr ⟨hk_notT, Finset.disjoint_union_left.mpr ⟨hd0, hd1⟩⟩

end SensAndPriv

section MainProof

lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

lemma final_arith (q N S k kA kB : ℕ) (hq : 200 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hkN : k ≤ N) (hpart : k ≤ kA + kB + 2 * q)
    (hB1 : 8 * N + kA ≤ 2 * S + 2 + 2 * k)
    (hB2 : 2 * N + k + q * kB ≤ S + 2 * q + 1) :
    349 * N ≤ 100 * S := by
  have hm1 : q * (8 * N + kA) ≤ q * (2 * S + 2 + 2 * k) := Nat.mul_le_mul_left q hB1
  have hsum_q : q * k ≤ q * (kA + kB + 2 * q) := Nat.mul_le_mul_left q hpart
  have hqA_le : q * k ≤ q * N := Nat.mul_le_mul_left q hkN
  have hcomb : (7 * q + 3) * N ≤ (2 * q + 1) * S + (2 * q ^ 2 + 4 * q + 1) := by nlinarith
  have hpoly : 100 * (2 * q ^ 2 + 4 * q + 1) + 349 * N * (2 * q + 1) ≤ 100 * (7 * q + 3) * N := by
    rw [hN]; nlinarith
  have h100 : (2 * q + 1) * (349 * N) ≤ (2 * q + 1) * (100 * S) := by nlinarith
  exact Nat.le_of_mul_le_mul_left h100 (by omega)

lemma eval_unit_false {q N : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hq : 1 ≤ q) (hAO : IsAO2 (N + N) C)
    (hfalse : ∀ (P L : Finset (Fin N)), L.card ≤ q → IsFalseInput S P L →
      C.eval (incidenceInput P L) = false)
    (y : ℕ) (hy : y < N + N) :
    C.eval (unitVec (N + N) y) = false := by
  by_cases h1 : y < N
  · let p : Fin N := ⟨y, h1⟩
    have heq : ∀ i < N + N, (unitVec (N + N) y).getD i false =
        (incidenceInput ({p} : Finset (Fin N)) (∅ : Finset (Fin N))).getD i false := by
      intro i hi
      rw [unitVec_getD (N + N) y i hi]
      by_cases hi1 : i < N
      · have := incidenceInput_getD_pt ({p} : Finset (Fin N)) (∅ : Finset (Fin N)) ⟨i, hi1⟩
        simp only [Finset.mem_singleton] at this
        rw [this]
        congr 1; exact propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      · have hi_eq : i = N + (i - N) := by omega
        have := incidenceInput_getD_ln ({p} : Finset (Fin N)) (∅ : Finset (Fin N)) ⟨i - N, by omega⟩
        rw [← hi_eq] at this
        simp only [Finset.notMem_empty, decide_false] at this
        rw [this]; simp only [decide_eq_false_iff_not]; omega
    change wv C (unitVec (N + N) y) C.output = false
    rw [wv_congr hAO (unitVec_length _ _) (incidenceInput_length _ _) heq C.output]
    exact hfalse {p} ∅ (by simp) (by intro l hl; simp at hl)
  · let l : Fin N := ⟨y - N, by omega⟩
    have hy_eq : y = N + l.val := by simp [l]; omega
    have heq : ∀ i < N + N, (unitVec (N + N) y).getD i false =
        (incidenceInput (∅ : Finset (Fin N)) ({l} : Finset (Fin N))).getD i false := by
      intro i hi
      rw [unitVec_getD (N + N) y i hi]
      by_cases hi1 : i < N
      · have := incidenceInput_getD_pt (∅ : Finset (Fin N)) {l} ⟨i, hi1⟩
        simp only [Finset.notMem_empty, decide_false] at this
        rw [this]; simp only [decide_eq_false_iff_not]; omega
      · have hi_eq : i = N + (i - N) := by omega
        have := incidenceInput_getD_ln (∅ : Finset (Fin N)) {l} ⟨i - N, by omega⟩
        rw [← hi_eq] at this
        simp only [Finset.mem_singleton] at this
        rw [this]
        congr 1; exact propext ⟨fun h => Fin.ext (by simp [l]; omega), fun h => by have := congrArg Fin.val h; simp [l] at this; omega⟩
    change wv C (unitVec (N + N) y) C.output = false
    rw [wv_congr hAO (unitVec_length _ _) (incidenceInput_length _ _) heq C.output]
    exact hfalse ∅ {l} (by simp; omega) (by intro l' _; simp)

lemma eval_pair_true {N : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hAO : IsAO2 (N + N) C) (hinc : RightOnIncidentPairs S C)
    (x y : ℕ) (hy : y ∈ neighborsOf S x) :
    C.eval (pairVec (N + N) x y) = true := by
  obtain ⟨p, l, hpl, hle⟩ := neighborsOf_inc S x y hy
  exact wv_mono hAO (incidenceInput_length _ _) (pairVec_length _ _ _) hle C.output (hinc l p hpl)

lemma chain_classify {q N : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (hAO : IsAO2 (N + N) C) (hinc : RightOnIncidentPairs S C)
    (hfalse : ∀ (P L : Finset (Fin N)), L.card ≤ q → IsFalseInput S P L →
      C.eval (incidenceInput P L) = false)
    (outJ : ℕ) (hout : C.output = (N + N) + outJ) (houtLt : outJ < C.gates.length) :
    let m := N + N
    let R := inCone m C C.output
    ∀ x < m,
      (∃ w', (w' = x ∨ ∃ g ∈ R.erase outJ, w' = m + g) ∧ 2 ≤ deg C R w' ∧ oneHot m C w' = {x}) ∨
      (∃ (Ch : Finset ℕ) (u a v : ℕ),
        GraphBarrier m C R x Ch u ∧
        (∀ c ∈ Ch, oneHot m C c = {x}) ∧
        deg C R u = 1 ∧ a ∈ R ∧ (gateAt C a).op = GateOp.and ∧
        ((gi0 C a = u ∧ gi1 C a = v) ∨ (gi0 C a = v ∧ gi1 C a = u)) ∧
        wv C (unitVec m x) v = false ∧
        oneHot m C (m + a) = ∅ ∧
        (∀ y ∈ neighborsOf S x, y ∈ oneHot m C v)) := by
  intro m R x hx
  have hq1 : 1 ≤ q := by omega
  have houtR : outJ ∈ R := by
    dsimp only [R]; rw [hout, inCone_gate hAO outJ houtLt]; exact Finset.mem_insert_self _ _
  have hoh_out : oneHot m C C.output = ∅ := by
    ext y
    simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    intro hy
    change C.eval (unitVec m y) ≠ true
    rw [eval_unit_false hq1 hAO hfalse y hy]; decide
  have hne_nb : (neighborsOf S x).Nonempty := by
    rw [← Finset.card_pos, neighborsOf_card S hq1 hN hcard huniq x hx]; omega
  have hstep : ∀ (d : ℕ) (Ch : Finset ℕ) (w : ℕ),
      (m + C.gates.length) - w = d →
      w < m + C.gates.length →
      (w = x ∨ ∃ g ∈ R, w = m + g) →
      GraphBarrier m C R x Ch w →
      (∀ c ∈ Ch, oneHot m C c = {x}) →
      (∃ w', (w' = x ∨ ∃ g ∈ R.erase outJ, w' = m + g) ∧ 2 ≤ deg C R w' ∧ oneHot m C w' = {x}) ∨
      (∃ (Ch' : Finset ℕ) (u a v : ℕ),
        GraphBarrier m C R x Ch' u ∧
        (∀ c ∈ Ch', oneHot m C c = {x}) ∧
        deg C R u = 1 ∧ a ∈ R ∧ (gateAt C a).op = GateOp.and ∧
        ((gi0 C a = u ∧ gi1 C a = v) ∨ (gi0 C a = v ∧ gi1 C a = u)) ∧
        wv C (unitVec m x) v = false ∧
        oneHot m C (m + a) = ∅ ∧
        (∀ y ∈ neighborsOf S x, y ∈ oneHot m C v)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro Ch w hd hw_lt hwR hB hoh
      have hoh_w : oneHot m C w = {x} := hoh w hB.2.1
      have hout_notCh : C.output ∉ Ch := by
        intro hmem
        have h1 := hoh C.output hmem
        rw [hoh_out] at h1
        have : x ∈ (∅ : Finset ℕ) := by rw [h1]; exact Finset.mem_singleton_self x
        simp at this
      by_cases hdeg2 : 2 ≤ deg C R w
      · left
        refine ⟨w, ?_, hdeg2, hoh_w⟩
        rcases hwR with rfl | ⟨g, hgR, rfl⟩
        · exact Or.inl rfl
        · right
          have hne_out : g ≠ outJ := by
            intro e; subst e; apply hout_notCh; rw [hout]; exact hB.2.1
          exact ⟨g, Finset.mem_erase.mpr ⟨hne_out, hgR⟩, rfl⟩
      · by_cases hdeg0 : deg C R w = 0
        · exfalso
          obtain ⟨y, hy⟩ := hne_nb
          have hylt := neighborsOf_lt S x y hy
          have hagree : ∀ i < m, i ≠ x → (pairVec m x y).getD i false = (unitVec m y).getD i false := by
            intro i hi hne
            rw [pairVec_getD m x y i hi, unitVec_getD m y i hi]
            simp [hne]
          have heq := barrier_deg_zero_absurd hAO C.output x Ch w hB hdeg0
            (pairVec m x y) (unitVec m y) (pairVec_length _ _ _) (unitVec_length _ _) hagree
            C.output (Or.inr ⟨outJ, houtR, hout⟩) hout_notCh
          change C.eval (pairVec m x y) = C.eval (unitVec m y) at heq
          rw [eval_pair_true hAO hinc x y hy, eval_unit_false hq1 hAO hfalse y hylt.1] at heq
          cases heq
        · have hdeg1 : deg C R w = 1 := by omega
          obtain ⟨j, hjR, hjr⟩ := deg_eq_one_exists_reader C R w hdeg1
          have hjlt : j < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO C.output hjR)
          have hlt := gate_inputs_lt hAO hjlt
          have hcl := inCone_closed hAO C.output j hjR
          let v : ℕ := if gi0 C j = w then gi1 C j else gi0 C j
          have hpair_uv : (gi0 C j = w ∧ gi1 C j = v) ∨ (gi0 C j = v ∧ gi1 C j = w) := by
            dsimp only [v]
            rcases hjr with ⟨h0, _⟩ | ⟨h1, h0ne⟩
            · left; simp [h0]
            · right; simp [h0ne, h1]
          have hvne : v ≠ w := by
            dsimp only [v]
            rcases hjr with ⟨h0, h1ne⟩ | ⟨h1, h0ne⟩
            · simp [h0, h1ne]
            · simp [h0ne]
          have hwr : gi0 C j = w ∨ gi1 C j = w := hpair_uv.imp And.left And.right
          have hvr : gi0 C j = v ∨ gi1 C j = v := by
            rcases hpair_uv with ⟨_, h⟩ | ⟨h, _⟩
            · exact Or.inr h
            · exact Or.inl h
          have hw_lt_mj : w < m + j := by rcases hwr with h | h <;> omega
          have hv_lt_mj : v < m + j := by rcases hvr with h | h <;> omega
          have hv_R : v < m ∨ ∃ t ∈ R, v = m + t := by rcases hvr with h | h; rw [← h]; exact hcl.1; rw [← h]; exact hcl.2
          have hv_notCh : v ∉ Ch := barrier_other_not_mem hAO C.output x Ch w hB hdeg1 j hjR v hvne hvr hwr
          have hv_indep : ∀ z1 z2 : List Bool, z1.length = m → z2.length = m →
              (∀ i < m, i ≠ x → z1.getD i false = z2.getD i false) →
              wv C z1 v = wv C z2 v :=
            fun z1 z2 hz1 hz2 hag =>
              barrier_indep_lt hAO C.output x Ch w hB hdeg1 j hjR hwr z1 z2 hz1 hz2 hag v hv_lt_mj hv_R hv_notCh
          have hB_next : GraphBarrier m C R x (insert (m + j) Ch) (m + j) := by
            refine ⟨Finset.mem_insert_of_mem hB.1, Finset.mem_insert_self _ _, ?_, ?_⟩
            · intro c hc
              simp only [Finset.mem_insert] at hc
              rcases hc with rfl | hc
              · exact le_refl _
              · have := hB.2.2.1 c hc; omega
            · intro c hc hne
              simp only [Finset.mem_insert] at hc
              rcases hc with rfl | hc
              · exact absurd rfl hne
              · by_cases hcw : c = w
                · subst hcw
                  exact ⟨hdeg1, j, hjR, Finset.mem_insert_self _ _, hwr⟩
                · obtain ⟨hd1, j', hj'R, hj'Ch, hj'r⟩ := hB.2.2.2 c hc hcw
                  exact ⟨hd1, j', hj'R, Finset.mem_insert_of_mem hj'Ch, hj'r⟩
          have hw_unit_x : wv C (unitVec m x) w = true := by
            have hxmem : x ∈ oneHot m C w := by rw [hoh_w]; exact Finset.mem_singleton_self x
            exact (Finset.mem_filter.mp hxmem).2
          have hw_unit_ne : ∀ y < m, y ≠ x → wv C (unitVec m y) w = false := by
            intro y hy hne
            cases hb : wv C (unitVec m y) w with
            | false => rfl
            | true =>
              have : y ∈ oneHot m C w := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy, hb⟩
              rw [hoh_w, Finset.mem_singleton] at this
              exact absurd this hne
          have hmem : gateAt C j ∈ C.gates := by
            simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
          rcases hAO.1 (gateAt C j) hmem with hand | hor
          · by_cases hxv : wv C (unitVec m x) v = true
            · have hv_allFalse : wv C (allFalse m) v = true := by
                have hagree : ∀ i < m, i ≠ x → (unitVec m x).getD i false = (allFalse m).getD i false := by
                  intro i hi hne; rw [unitVec_getD m x i hi, allFalse_getD m i hi]; simp [hne]
                rw [← hv_indep (unitVec m x) (allFalse m) (unitVec_length _ _) (allFalse_length _) hagree]
                exact hxv
              have hoh_mj : oneHot m C (m + j) = {x} := by
                ext y
                simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
                constructor
                · rintro ⟨hy, ht⟩
                  rw [wv_and_eq hAO (unitVec_length m y) hjlt hand, Bool.and_eq_true] at ht
                  have hwt : wv C (unitVec m y) w = true := by
                    rcases hpair_uv with ⟨h0, _⟩ | ⟨_, h1⟩
                    · rw [← h0]; exact ht.1
                    · rw [← h1]; exact ht.2
                  by_contra hne
                  rw [hw_unit_ne y hy hne] at hwt; cases hwt
                · rintro rfl
                  refine ⟨hx, ?_⟩
                  rw [wv_and_eq hAO (unitVec_length m y) hjlt hand, Bool.and_eq_true]
                  rcases hpair_uv with ⟨h0, h1⟩ | ⟨h0, h1⟩
                  · rw [h0, h1]; exact ⟨hw_unit_x, hxv⟩
                  · rw [h0, h1]; exact ⟨hxv, hw_unit_x⟩
              have hoh_next : ∀ c ∈ insert (m + j) Ch, oneHot m C c = {x} := by
                intro c hc
                simp only [Finset.mem_insert] at hc
                rcases hc with rfl | hc
                · exact hoh_mj
                · exact hoh c hc
              have hdl : (m + C.gates.length) - (m + j) < d := by
                rw [← hd]; exact Nat.sub_lt_sub_left hw_lt hw_lt_mj
              exact ih ((m + C.gates.length) - (m + j)) hdl (insert (m + j) Ch) (m + j)
                rfl (Nat.add_lt_add_left hjlt m) (Or.inr ⟨j, hjR, rfl⟩) hB_next hoh_next
            · have hxv_false : wv C (unitVec m x) v = false := by
                cases h : wv C (unitVec m x) v
                · rfl
                · exact absurd h hxv
              have hoh_mj : oneHot m C (m + j) = ∅ := by
                ext y
                simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
                intro hy ht
                rw [wv_and_eq hAO (unitVec_length m y) hjlt hand, Bool.and_eq_true] at ht
                by_cases hyx : y = x
                · subst hyx
                  have hvt : wv C (unitVec m y) v = true := by
                    rcases hpair_uv with ⟨_, h1⟩ | ⟨h0, _⟩
                    · rw [← h1]; exact ht.2
                    · rw [← h0]; exact ht.1
                  rw [hxv_false] at hvt; cases hvt
                · have hwt : wv C (unitVec m y) w = true := by
                    rcases hpair_uv with ⟨h0, _⟩ | ⟨_, h1⟩
                    · rw [← h0]; exact ht.1
                    · rw [← h1]; exact ht.2
                  rw [hw_unit_ne y hy hyx] at hwt; cases hwt
              have hnb_v : ∀ y ∈ neighborsOf S x, y ∈ oneHot m C v := by
                intro y hy
                have hylt := neighborsOf_lt S x y hy
                refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hylt.1, ?_⟩
                have hagree : ∀ i < m, i ≠ x → (pairVec m x y).getD i false = (unitVec m y).getD i false := by
                  intro i hi hne; rw [pairVec_getD m x y i hi, unitVec_getD m y i hi]; simp [hne]
                have hvy_eq : wv C (pairVec m x y) v = wv C (unitVec m y) v :=
                  hv_indep (pairVec m x y) (unitVec m y) (pairVec_length _ _ _) (unitVec_length _ _) hagree
                have hmj_uy : wv C (unitVec m y) (m + j) = false := by
                  rw [wv_and_eq hAO (unitVec_length m y) hjlt hand]
                  rcases hpair_uv with ⟨h0, _⟩ | ⟨_, h1⟩
                  · rw [h0, hw_unit_ne y hylt.1 hylt.2]; simp
                  · rw [h1, hw_unit_ne y hylt.1 hylt.2]; simp
                have hmj_pair : wv C (pairVec m x y) (m + j) = true := by
                  cases hmjp : wv C (pairVec m x y) (m + j) with
                  | true => rfl
                  | false =>
                    exfalso
                    have hmj_eq : wv C (pairVec m x y) (m + j) = wv C (unitVec m y) (m + j) := by
                      rw [hmjp, hmj_uy]
                    have hout_not_next : C.output ∉ insert (m + j) Ch := by
                      intro hc
                      simp only [Finset.mem_insert] at hc
                      rcases hc with hco | hc
                      · rw [← hco] at hmjp
                        change C.eval (pairVec m x y) = false at hmjp
                        rw [eval_pair_true hAO hinc x y hy] at hmjp; cases hmjp
                      · exact hout_notCh hc
                    have hce := barrier_eval_eq hAO C.output x (insert (m + j) Ch) (m + j) hB_next
                      (pairVec m x y) (unitVec m y) (pairVec_length _ _ _) (unitVec_length _ _) hagree
                      hmj_eq C.output (Or.inr ⟨outJ, houtR, hout⟩) hout_not_next
                    change C.eval (pairVec m x y) = C.eval (unitVec m y) at hce
                    rw [eval_pair_true hAO hinc x y hy, eval_unit_false hq1 hAO hfalse y hylt.1] at hce
                    cases hce
                rw [wv_and_eq hAO (pairVec_length m x y) hjlt hand, Bool.and_eq_true] at hmj_pair
                have hvp : wv C (pairVec m x y) v = true := by
                  rcases hpair_uv with ⟨_, h1⟩ | ⟨h0, _⟩
                  · rw [← h1]; exact hmj_pair.2
                  · rw [← h0]; exact hmj_pair.1
                rw [← hvy_eq]; exact hvp
              right
              exact ⟨Ch, w, j, v, hB, hoh, hdeg1, hjR, hand, hpair_uv, hxv_false, hoh_mj, hnb_v⟩
          · have hoh_mj : oneHot m C (m + j) = {x} := by
              ext y
              simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
              constructor
              · rintro ⟨hy, ht⟩
                by_contra hne
                rw [wv_or_eq hAO (unitVec_length m y) hjlt hor, Bool.or_eq_true] at ht
                have hvt : wv C (unitVec m y) v = true := by
                  rcases hpair_uv with ⟨h0, h1⟩ | ⟨h0, h1⟩
                  · rw [h0, h1, hw_unit_ne y hy hne] at ht; simpa using ht
                  · rw [h0, h1, hw_unit_ne y hy hne] at ht; simpa using ht
                obtain ⟨P, L, hLle, hF, hgy, hgx, p, l, hpl, hle_pl⟩ :=
                  exists_sep_false S hq hN hcard huniq x y hx hy (Ne.symm hne)
                let z := incidenceInput P L
                have hz_len : z.length = m := incidenceInput_length P L
                have hle_uy : ∀ i < m, (unitVec m y).getD i false = true → z.getD i false = true := by
                  intro i hi h1
                  rw [unitVec_getD m y i hi, decide_eq_true_iff] at h1
                  subst h1; exact hgy
                have hvz : wv C z v = true := wv_mono hAO (unitVec_length m y) hz_len hle_uy v hvt
                have hagree : ∀ i < m, i ≠ x → z.getD i false = (zFlip m z x).getD i false := by
                  intro i hi hnix
                  rw [zFlip_getD m z x i hi]
                  simp [hnix]
                have hvzf : wv C (zFlip m z x) v = true := by
                  rw [← hv_indep z (zFlip m z x) hz_len (zFlip_length _ _ _) hagree]; exact hvz
                have hmj_z : wv C z (m + j) = true := by
                  rw [wv_or_eq hAO hz_len hjlt hor, Bool.or_eq_true]
                  rcases hpair_uv with ⟨_, h1⟩ | ⟨h0, _⟩
                  · right; rw [h1]; exact hvz
                  · left; rw [h0]; exact hvz
                have hmj_zf : wv C (zFlip m z x) (m + j) = true := by
                  rw [wv_or_eq hAO (zFlip_length _ _ _) hjlt hor, Bool.or_eq_true]
                  rcases hpair_uv with ⟨_, h1⟩ | ⟨h0, _⟩
                  · right; rw [h1]; exact hvzf
                  · left; rw [h0]; exact hvzf
                have hcz_false : C.eval z = false := hfalse P L hLle hF
                have hczf_true : C.eval (zFlip m z x) = true :=
                  wv_mono hAO (incidenceInput_length _ _) (zFlip_length _ _ _) hle_pl C.output (hinc l p hpl)
                have hout_not_next : C.output ∉ insert (m + j) Ch := by
                  intro hc
                  simp only [Finset.mem_insert] at hc
                  rcases hc with hco | hc
                  · rw [← hco] at hmj_z
                    change C.eval z = true at hmj_z
                    rw [hcz_false] at hmj_z; cases hmj_z
                  · exact hout_notCh hc
                have hce := barrier_eval_eq hAO C.output x (insert (m + j) Ch) (m + j) hB_next
                  z (zFlip m z x) hz_len (zFlip_length _ _ _) hagree (by rw [hmj_z, hmj_zf])
                  C.output (Or.inr ⟨outJ, houtR, hout⟩) hout_not_next
                change C.eval z = C.eval (zFlip m z x) at hce
                rw [hcz_false, hczf_true] at hce; cases hce
              · rintro rfl
                refine ⟨hx, ?_⟩
                rw [wv_or_eq hAO (unitVec_length m y) hjlt hor, Bool.or_eq_true]
                rcases hpair_uv with ⟨h0, _⟩ | ⟨_, h1⟩
                · left; rw [h0]; exact hw_unit_x
                · right; rw [h1]; exact hw_unit_x
            have hoh_next : ∀ c ∈ insert (m + j) Ch, oneHot m C c = {x} := by
              intro c hc
              simp only [Finset.mem_insert] at hc
              rcases hc with rfl | hc
              · exact hoh_mj
              · exact hoh c hc
            have hdl : (m + C.gates.length) - (m + j) < d := by
              rw [← hd]; exact Nat.sub_lt_sub_left hw_lt hw_lt_mj
            exact ih ((m + C.gates.length) - (m + j)) hdl (insert (m + j) Ch) (m + j)
              rfl (Nat.add_lt_add_left hjlt m) (Or.inr ⟨j, hjR, rfl⟩) hB_next hoh_next
  have hB0 : GraphBarrier m C R x {x} x := by
    refine ⟨Finset.mem_singleton_self x, Finset.mem_singleton_self x, ?_, ?_⟩
    · intro c hc; simp only [Finset.mem_singleton] at hc; omega
    · intro c hc hne; simp only [Finset.mem_singleton] at hc; exact absurd hc hne
  have hoh0 : ∀ c ∈ ({x} : Finset ℕ), oneHot m C c = {x} := by
    intro c hc; simp only [Finset.mem_singleton] at hc; subst hc; exact oneHot_input m C c hx
  exact hstep ((m + C.gates.length) - x) {x} x rfl (by omega) (Or.inl rfl) hB0 hoh0

set_option maxHeartbeats 800000 in
lemma main_proof (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l)
    (hAO : IsAO2 (N + N) C) (hinc : RightOnIncidentPairs S C)
    (hfalse : ∀ (P L : Finset (Fin N)), L.card ≤ q → IsFalseInput S P L →
      C.eval (incidenceInput P L) = false) :
    349 * N ≤ 100 * C.size := by
  classical
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hNpos : 0 < N := by rw [hN]; nlinarith
  let m := N + N
  have hm_pos : 0 < m := by omega
  have hout_ge : m ≤ C.output := by
    by_contra hlt
    push Not at hlt
    have hf := eval_unit_false hq1 hAO hfalse C.output hlt
    have ht : C.eval (unitVec m C.output) = true := by
      change wv C (unitVec m C.output) C.output = true
      rw [wv_input C _ C.output (by rw [unitVec_length]; exact hlt), unitVec_getD m _ _ hlt]
      simp
    rw [hf] at ht; cases ht
  have hout_lt : C.output < m + C.gates.length := by
    by_contra hge
    push Not at hge
    let l0 : Fin N := ⟨0, hNpos⟩
    have hSne : (S l0).Nonempty := by rw [← Finset.card_pos, hcard l0]; omega
    obtain ⟨p0, hp0⟩ := hSne
    have ht := hinc l0 p0 hp0
    have hf : C.eval (incidenceInput {p0} {l0}) = false :=
      wv_ge C _ C.output (by rw [incidenceInput_length]; exact hge)
    rw [hf] at ht; cases ht
  let outJ := C.output - m
  have hout : C.output = m + outJ := by omega
  have houtLt : outJ < C.gates.length := by omega
  let R := inCone m C C.output
  have hR_le_size : R.card ≤ C.size := by
    have := Finset.card_le_card (inCone_sub_range hAO C.output)
    rw [Finset.card_range] at this
    exact this
  have houtR : outJ ∈ R := by
    dsimp only [R]; rw [hout, inCone_gate hAO outJ houtLt]; exact Finset.mem_insert_self _ _
  have hoh_out : oneHot m C C.output = ∅ := by
    ext y
    simp only [oneHot, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    intro hy
    change C.eval (unitVec m y) ≠ true
    rw [eval_unit_false hq1 hAO hfalse y hy]; decide
  let Out2 (x : ℕ) : Prop :=
    ∃ (Ch : Finset ℕ) (u a v : ℕ),
      GraphBarrier m C R x Ch u ∧
      (∀ c ∈ Ch, oneHot m C c = {x}) ∧
      deg C R u = 1 ∧ a ∈ R ∧ (gateAt C a).op = GateOp.and ∧
      ((gi0 C a = u ∧ gi1 C a = v) ∨ (gi0 C a = v ∧ gi1 C a = u)) ∧
      wv C (unitVec m x) v = false ∧
      oneHot m C (m + a) = ∅ ∧
      (∀ y ∈ neighborsOf S x, y ∈ oneHot m C v)
  let A := (Finset.range m).filter Out2
  let B := (Finset.range m).filter (fun x => ¬ Out2 x)
  have hAB_card : A.card + B.card = m := by
    have := card_filter_add_not (Finset.range m) Out2
    rw [Finset.card_range] at this
    exact this
  -- Extract witnesses for x ∈ A
  let ChA (x : ℕ) : Finset ℕ := if h : Out2 x then Classical.choose h else ∅
  let uA (x : ℕ) : ℕ := if h : Out2 x then Classical.choose (Classical.choose_spec h) else 0
  let aA (x : ℕ) : ℕ :=
    if h : Out2 x then Classical.choose (Classical.choose_spec (Classical.choose_spec h)) else 0
  let vA (x : ℕ) : ℕ :=
    if h : Out2 x then
      Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))
    else 0
  have hA_spec : ∀ x ∈ A,
      GraphBarrier m C R x (ChA x) (uA x) ∧
      (∀ c ∈ ChA x, oneHot m C c = {x}) ∧
      deg C R (uA x) = 1 ∧ aA x ∈ R ∧ (gateAt C (aA x)).op = GateOp.and ∧
      ((gi0 C (aA x) = uA x ∧ gi1 C (aA x) = vA x) ∨ (gi0 C (aA x) = vA x ∧ gi1 C (aA x) = uA x)) ∧
      wv C (unitVec m x) (vA x) = false ∧
      oneHot m C (m + aA x) = ∅ ∧
      (∀ y ∈ neighborsOf S x, y ∈ oneHot m C (vA x)) := by
    intro x hx
    have h2 : Out2 x := (Finset.mem_filter.mp hx).2
    dsimp only [ChA, uA, aA, vA]
    simp only [h2, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h2)))
  have ha_inj : ∀ x1 ∈ A, ∀ x2 ∈ A, aA x1 = aA x2 → x1 = x2 := by
    intro x1 hx1 x2 hx2 heq
    by_contra hne
    have hs1 := hA_spec x1 hx1
    have hs2 := hA_spec x2 hx2
    have hu1_oh : oneHot m C (uA x1) = {x1} := hs1.2.1 (uA x1) hs1.1.2.1
    have hu2_oh : oneHot m C (uA x2) = {x2} := hs2.2.1 (uA x2) hs2.1.2.1
    have hu_ne : uA x1 ≠ uA x2 := by
      intro e; rw [e, hu2_oh] at hu1_oh
      have : x1 ∈ ({x2} : Finset ℕ) := by rw [hu1_oh]; exact Finset.mem_singleton_self x1
      simp only [Finset.mem_singleton] at this
      exact hne this
    have hv1_eq : vA x1 = uA x2 := by
      rw [heq] at hs1
      rcases hs1.2.2.2.2.2.1 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      rcases hs2.2.2.2.2.2.1 with ⟨g0, g1⟩ | ⟨g0, g1⟩
      · exact absurd (h0.symm.trans g0) hu_ne
      · exact h1.symm.trans g1
      · exact h0.symm.trans g0
      · exact absurd (h1.symm.trans g1) hu_ne
    have hnb_sub : neighborsOf S x1 ⊆ oneHot m C (vA x1) := hs1.2.2.2.2.2.2.2.2
    have hc1 := Finset.card_le_card hnb_sub
    rw [neighborsOf_card S hq1 hN hcard huniq x1 (Finset.mem_range.mp (Finset.mem_filter.mp hx1).1),
      hv1_eq, hu2_oh, Finset.card_singleton] at hc1
    omega
  have hA_no_adj : ∀ x ∈ A, ∀ y ∈ A, y ∈ neighborsOf S x → False := by
    have hdir : ∀ x ∈ A, ∀ y ∈ A, y ∈ neighborsOf S x → aA x < aA y → False := by
      intro x hx y hy hxy halt
      have hsx := hA_spec x hx
      have hsy := hA_spec y hy
      have hxlt : x < m := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hylt : y < m := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hxy_ne : y ≠ x := (neighborsOf_lt S x y hxy).2
      have hax_not_Chy : m + aA x ∉ ChA y := by
        intro hmem
        have h1 := hsy.2.1 (m + aA x) hmem
        rw [hsx.2.2.2.2.2.2.2.1] at h1
        have : y ∈ (∅ : Finset ℕ) := by rw [h1]; exact Finset.mem_singleton_self y
        simp at this
      have hagree_y : ∀ i < m, i ≠ y → (pairVec m x y).getD i false = (unitVec m x).getD i false := by
        intro i hi hniy; rw [pairVec_getD m x y i hi, unitVec_getD m x i hi]; simp [hniy]
      have hax_indep_y := barrier_indep_lt hAO C.output y (ChA y) (uA y) hsy.1 hsy.2.2.1
        (aA y) hsy.2.2.2.1 (hsy.2.2.2.2.2.1.imp And.left And.right)
        (pairVec m x y) (unitVec m x) (pairVec_length _ _ _) (unitVec_length _ _) hagree_y
        (m + aA x) (by omega) (Or.inr ⟨aA x, hsx.2.2.2.1, rfl⟩) hax_not_Chy
      have hax_ux : wv C (unitVec m x) (m + aA x) = false := by
        cases hb : wv C (unitVec m x) (m + aA x) with
        | false => rfl
        | true =>
          have : x ∈ oneHot m C (m + aA x) := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxlt, hb⟩
          rw [hsx.2.2.2.2.2.2.2.1] at this; simp at this
      have hax_uy : wv C (unitVec m y) (m + aA x) = false := by
        cases hb : wv C (unitVec m y) (m + aA x) with
        | false => rfl
        | true =>
          have : y ∈ oneHot m C (m + aA x) := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hylt, hb⟩
          rw [hsx.2.2.2.2.2.2.2.1] at this; simp at this
      have hax_eq : wv C (pairVec m x y) (m + aA x) = wv C (unitVec m y) (m + aA x) := by
        rw [hax_indep_y, hax_ux, hax_uy]
      have hB_ax : GraphBarrier m C R x (insert (m + aA x) (ChA x)) (m + aA x) := by
        have hax_lt : aA x < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO C.output hsx.2.2.2.1)
        have hlt := gate_inputs_lt hAO hax_lt
        have hur : gi0 C (aA x) = uA x ∨ gi1 C (aA x) = uA x := hsx.2.2.2.2.2.1.imp And.left And.right
        have hult : uA x < m + aA x := by rcases hur with h | h <;> omega
        refine ⟨Finset.mem_insert_of_mem hsx.1.1, Finset.mem_insert_self _ _, ?_, ?_⟩
        · intro c hc
          simp only [Finset.mem_insert] at hc
          rcases hc with rfl | hc
          · exact le_refl _
          · have := hsx.1.2.2.1 c hc; omega
        · intro c hc hne
          simp only [Finset.mem_insert] at hc
          rcases hc with rfl | hc
          · exact absurd rfl hne
          · by_cases hcu : c = uA x
            · subst hcu; exact ⟨hsx.2.2.1, aA x, hsx.2.2.2.1, Finset.mem_insert_self _ _, hur⟩
            · obtain ⟨hd1, j', hj'R, hj'Ch, hj'r⟩ := hsx.1.2.2.2 c hc hcu
              exact ⟨hd1, j', hj'R, Finset.mem_insert_of_mem hj'Ch, hj'r⟩
      have hout_not : C.output ∉ insert (m + aA x) (ChA x) := by
        intro hc
        simp only [Finset.mem_insert] at hc
        rcases hc with hco | hc
        · rw [← hco] at hax_indep_y
          change C.eval (pairVec m x y) = C.eval (unitVec m x) at hax_indep_y
          rw [eval_pair_true hAO hinc x y hxy, eval_unit_false hq1 hAO hfalse x hxlt] at hax_indep_y
          cases hax_indep_y
        · have h1 := hsx.2.1 C.output hc
          rw [hoh_out] at h1
          have : x ∈ (∅ : Finset ℕ) := by rw [h1]; exact Finset.mem_singleton_self x
          simp at this
      have hagree_x : ∀ i < m, i ≠ x → (pairVec m x y).getD i false = (unitVec m y).getD i false := by
        intro i hi hnix; rw [pairVec_getD m x y i hi, unitVec_getD m y i hi]; simp [hnix]
      have hce := barrier_eval_eq hAO C.output x (insert (m + aA x) (ChA x)) (m + aA x) hB_ax
        (pairVec m x y) (unitVec m y) (pairVec_length _ _ _) (unitVec_length _ _) hagree_x hax_eq
        C.output (Or.inr ⟨outJ, houtR, hout⟩) hout_not
      change C.eval (pairVec m x y) = C.eval (unitVec m y) at hce
      rw [eval_pair_true hAO hinc x y hxy, eval_unit_false hq1 hAO hfalse y hylt] at hce
      cases hce
    intro x hx y hy hxy
    have hxy_ne : y ≠ x := (neighborsOf_lt S x y hxy).2
    have hane : aA x ≠ aA y := fun e => hxy_ne (ha_inj x hx y hy e).symm
    have hyx : x ∈ neighborsOf S y := by
      dsimp only [neighborsOf] at hxy ⊢
      split_ifs at hxy with h1 h2
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxy
        have hnot : ¬ (N + l.val < N) := by omega
        have hlt2 : N + l.val - N < N := by have := l.isLt; omega
        simp only [hnot, ↓reduceDIte, hlt2]
        refine Finset.mem_image.mpr ⟨⟨x, h1⟩, ?_, rfl⟩
        have hl_eq : (⟨N + l.val - N, hlt2⟩ : Fin N) = l := Fin.ext (by simp)
        rw [hl_eq]
        exact (Finset.mem_filter.mp hl).2
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxy
        simp only [p.isLt, ↓reduceDIte]
        refine Finset.mem_image.mpr ⟨⟨x - N, h2⟩, ?_, by simp; omega⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      · simp at hxy
    rcases lt_or_gt_of_ne hane with h | h
    · exact hdir x hx y hy hxy h
    · exact hdir y hy x hx hyx h
  have hA_le_N : A.card ≤ N := by
    let AP : Finset (Fin N) := Finset.univ.filter fun p => p.val ∈ A
    let AL : Finset (Fin N) := Finset.univ.filter fun l => N + l.val ∈ A
    have hcard_eq : A.card = AP.card + AL.card := by
      have hpart : A = AP.image (fun p : Fin N => p.val) ∪ AL.image (fun l : Fin N => N + l.val) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_image, AP, AL, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hxA
          have hxlt : x < N + N := Finset.mem_range.mp (Finset.mem_filter.mp hxA).1
          by_cases h1 : x < N
          · exact Or.inl ⟨⟨x, h1⟩, hxA, rfl⟩
          · refine Or.inr ⟨⟨x - N, by omega⟩, ?_, by simp; omega⟩
            have heqx : N + (x - N) = x := by omega
            simpa [heqx] using hxA
        · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩) <;> assumption
      have hdisj : Disjoint (AP.image (fun p : Fin N => p.val)) (AL.image (fun l : Fin N => N + l.val)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨l, _, he⟩ := Finset.mem_image.mp hx2
        omega
      rw [hpart, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun _ _ h => Fin.ext h),
        Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))]
    rw [hcard_eq]
    apply indep_card_le S hq1 hN hcard huniq AP AL
    intro p hp l hl hpl
    have hpA : p.val ∈ A := (Finset.mem_filter.mp hp).2
    have hlA : N + l.val ∈ A := (Finset.mem_filter.mp hl).2
    have hnb : N + l.val ∈ neighborsOf S p.val := by
      dsimp only [neighborsOf]
      simp only [p.isLt, ↓reduceDIte]
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩, rfl⟩
    exact hA_no_adj p.val hpA (N + l.val) hlA hnb
  -- Outcome 1 witnesses for x ∈ B
  have hB_ex : ∀ x ∈ B, ∃ w', (w' = x ∨ ∃ g ∈ R.erase outJ, w' = m + g) ∧ 2 ≤ deg C R w' ∧ oneHot m C w' = {x} := by
    intro x hx
    have hxlt : x < m := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hnot : ¬ Out2 x := (Finset.mem_filter.mp hx).2
    exact (chain_classify hq2 hN hcard huniq hAO hinc hfalse outJ hout houtLt x hxlt).resolve_right hnot
  let wB (x : ℕ) : ℕ := if h : x ∈ B then Classical.choose (hB_ex x h) else 0
  have hwB_spec : ∀ x ∈ B, (wB x = x ∨ ∃ g ∈ R.erase outJ, wB x = m + g) ∧
      2 ≤ deg C R (wB x) ∧ oneHot m C (wB x) = {x} := by
    intro x hx
    dsimp only [wB]; simp only [hx, ↓reduceDIte]; exact Classical.choose_spec (hB_ex x hx)
  let B_in := B.filter (fun x => wB x = x)
  let B_gt := B.filter (fun x => wB x ≠ x)
  have hB_part : B_in.card + B_gt.card = B.card :=
    card_filter_add_not B (fun x => wB x = x)
  let gB (x : ℕ) : ℕ := wB x - m
  let G_B : Finset ℕ := B_gt.image gB
  have hGB_props : ∀ x ∈ B_gt, gB x ∈ R.erase outJ ∧ wB x = m + gB x ∧
      2 ≤ deg C R (m + gB x) ∧ oneHot m C (m + gB x) = {x} := by
    intro x hx
    have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
    have hne : wB x ≠ x := (Finset.mem_filter.mp hx).2
    have hs := hwB_spec x hxB
    obtain ⟨g, hg, hwg⟩ := hs.1.resolve_left hne
    have hg_eq : gB x = g := by dsimp only [gB]; omega
    rw [hg_eq, ← hwg]
    exact ⟨hg, rfl, hs.2.1, hs.2.2⟩
  have hGB_sub : G_B ⊆ R.erase outJ := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact (hGB_props x hx).1
  have hGB_card : G_B.card = B_gt.card := by
    apply Finset.card_image_of_injOn
    intro x1 hx1 x2 hx2 heq
    have h1 := (hGB_props x1 hx1).2.2.2
    have h2 := (hGB_props x2 hx2).2.2.2
    rw [heq, h2] at h1
    have : x1 ∈ ({x2} : Finset ℕ) := by rw [h1]; exact Finset.mem_singleton_self x1
    exact Finset.mem_singleton.mp this
  have hGB_oh : ∀ g ∈ G_B, (oneHot m C (m + g)).card = 1 := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    rw [(hGB_props x hx).2.2.2, Finset.card_singleton]
  have hdeg_in_pos : ∀ x ∈ Finset.range m, 1 ≤ deg C R x := by
    intro x hx
    have hxlt : x < m := Finset.mem_range.mp hx
    by_contra h0
    have hdeg0 : deg C R x = 0 := by omega
    have hB0 : GraphBarrier m C R x {x} x := by
      refine ⟨Finset.mem_singleton_self x, Finset.mem_singleton_self x, ?_, ?_⟩
      · intro c hc; simp only [Finset.mem_singleton] at hc; omega
      · intro c hc hne; simp only [Finset.mem_singleton] at hc; exact absurd hc hne
    have hne_nb : (neighborsOf S x).Nonempty := by
      rw [← Finset.card_pos, neighborsOf_card S hq1 hN hcard huniq x hxlt]; omega
    obtain ⟨y, hy⟩ := hne_nb
    have hylt := neighborsOf_lt S x y hy
    have hagree : ∀ i < m, i ≠ x → (pairVec m x y).getD i false = (unitVec m y).getD i false := by
      intro i hi hne; rw [pairVec_getD m x y i hi, unitVec_getD m y i hi]; simp [hne]
    have hout_not : C.output ∉ ({x} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
    have hce := barrier_deg_zero_absurd hAO C.output x {x} x hB0 hdeg0
      (pairVec m x y) (unitVec m y) (pairVec_length _ _ _) (unitVec_length _ _) hagree
      C.output (Or.inr ⟨outJ, houtR, hout⟩) hout_not
    change C.eval (pairVec m x y) = C.eval (unitVec m y) at hce
    rw [eval_pair_true hAO hinc x y hy, eval_unit_false hq1 hAO hfalse y hylt.1] at hce
    cases hce
  have hsum_in_GB : 2 * m - A.card ≤
      (∑ x ∈ Finset.range m, deg C R x) + (∑ g ∈ G_B, (deg C R (m + g) - 1)) := by
    have hBin_sub : B_in ⊆ Finset.range m :=
      Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsum_in : m + B_in.card ≤ ∑ x ∈ Finset.range m, deg C R x := by
      have hsplit : ∑ x ∈ Finset.range m, deg C R x =
          (∑ x ∈ B_in, deg C R x) + (∑ x ∈ Finset.range m \ B_in, deg C R x) := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hBin_sub]
      rw [hsplit]
      have h1 : 2 * B_in.card ≤ ∑ x ∈ B_in, deg C R x := by
        calc 2 * B_in.card = ∑ _x ∈ B_in, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ x ∈ B_in, deg C R x := by
            apply Finset.sum_le_sum
            intro x hx
            have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
            have hwx : wB x = x := (Finset.mem_filter.mp hx).2
            have hs := (hwB_spec x hxB).2.1
            rw [hwx] at hs; exact hs
      have h2 : (Finset.range m \ B_in).card ≤ ∑ x ∈ Finset.range m \ B_in, deg C R x := by
        calc (Finset.range m \ B_in).card = ∑ _x ∈ Finset.range m \ B_in, 1 := by simp
          _ ≤ ∑ x ∈ Finset.range m \ B_in, deg C R x :=
            Finset.sum_le_sum fun x hx => hdeg_in_pos x (Finset.mem_sdiff.mp hx).1
      have hsd : (Finset.range m \ B_in).card = m - B_in.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBin_sub, Finset.card_range]
      have hBle : B_in.card ≤ m := by
        have := Finset.card_le_card hBin_sub; rw [Finset.card_range] at this; exact this
      omega
    have hsum_GB : B_gt.card ≤ ∑ g ∈ G_B, (deg C R (m + g) - 1) := by
      rw [← hGB_card]
      calc G_B.card = ∑ _g ∈ G_B, 1 := by simp
        _ ≤ ∑ g ∈ G_B, (deg C R (m + g) - 1) := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
          have := (hGB_props x hx).2.2.1
          omega
    omega
  -- Maximal false input (P0, L0) and custom sens / sensVis
  obtain ⟨P0, L0, hP0card, hL0card, hF0, hP0cov, hL0cov⟩ :=
    exists_max_false_input S hq1 hN hcard huniq
  let z0 := incidenceInput P0 L0
  have hz0_len : z0.length = m := incidenceInput_length P0 L0
  have hz0_false : wv C z0 C.output = false := hfalse P0 L0 (by omega) hF0
  let S0 : Finset ℕ := (Finset.range m).filter fun i => z0.getD i false = false
  let T0 : Finset ℕ := (Finset.range m).filter fun i => z0.getD i false = true
  have hT0_card : T0.card = 2 * q := by
    have hT0_eq : T0 = P0.image (fun p : Fin N => p.val) ∪ L0.image (fun l : Fin N => N + l.val) := by
      ext i
      simp only [T0, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨hi, ht⟩
        rw [incidenceInput_getD_lt P0 L0 i hi] at ht
        rcases ht with ⟨h1, hp⟩ | ⟨h2, hl⟩
        · exact Or.inl ⟨⟨i, h1⟩, hp, rfl⟩
        · exact Or.inr ⟨⟨i - N, by dsimp only [m] at hi; omega⟩, hl, by simp; omega⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩)
        · refine ⟨by omega, ?_⟩
          have := incidenceInput_getD_pt P0 L0 p
          simp only [hp, decide_true] at this; exact this
        · refine ⟨by omega, ?_⟩
          have := incidenceInput_getD_ln P0 L0 l
          simp only [hl, decide_true] at this; exact this
    have hdisj : Disjoint (P0.image (fun p : Fin N => p.val)) (L0.image (fun l : Fin N => N + l.val)) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨l, _, he⟩ := Finset.mem_image.mp h2
      omega
    rw [hT0_eq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => Fin.ext h),
      Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega)), hP0card, hL0card]
    omega
  have hS0_card : S0.card = m - 2 * q := by
    have hpart : S0.card + T0.card = m := by
      have h1 : T0 = (Finset.range m).filter (fun i => ¬ z0.getD i false = false) := by
        ext i; simp [T0]
      rw [h1]
      have := card_filter_add_not (Finset.range m) (fun i => z0.getD i false = false)
      rw [Finset.card_range] at this; exact this
    omega
  have hz0_flip_true : ∀ i ∈ S0, wv C (zFlip m z0 i) C.output = true := by
    intro i hiS
    have hiF := Finset.mem_filter.mp hiS
    have hilt : i < m := Finset.mem_range.mp hiF.1
    have hfalse_i : z0.getD i false = false := hiF.2
    have hex_pl : ∃ p l : Fin N, p ∈ S l ∧
        ∀ k < m, (incidenceInput {p} {l}).getD k false = true →
          (zFlip m z0 i).getD k false = true := by
      by_cases hp : i < N
      · let p : Fin N := ⟨i, hp⟩
        have hpnot : p ∉ P0 := by
          intro hm
          have hg := incidenceInput_getD_pt P0 L0 p
          simp only [hm, decide_true] at hg
          change z0.getD i false = true at hg
          rw [hfalse_i] at hg; cases hg
        obtain ⟨l, hlL0, hpl⟩ := hP0cov p hpnot
        refine ⟨p, l, hpl, ?_⟩
        intro k hk ht
        rw [zFlip_getD m z0 i k hk, Bool.or_eq_true]
        rw [incidenceInput_getD_lt _ _ k hk] at ht
        rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
        · simp only [Finset.mem_singleton] at hp'
          right; have : k = i := by have := congrArg Fin.val hp'; simpa [p] using this
          simp [this]
        · simp only [Finset.mem_singleton] at hl'
          left
          have hk_eq : k = N + l.val := by have := congrArg Fin.val hl'; simp only at this; omega
          rw [hk_eq]
          have hg := incidenceInput_getD_ln P0 L0 l
          simp only [hlL0, decide_true] at hg; exact hg
      · let l : Fin N := ⟨i - N, by omega⟩
        have hi_eq : i = N + l.val := by simp [l]; omega
        have hlnot : l ∉ L0 := by
          intro hm
          have hg := incidenceInput_getD_ln P0 L0 l
          simp only [hm, decide_true] at hg
          change z0.getD (N + l.val) false = true at hg
          rw [← hi_eq, hfalse_i] at hg; cases hg
        obtain ⟨p, hpP0, hpl⟩ := hL0cov l hlnot
        refine ⟨p, l, hpl, ?_⟩
        intro k hk ht
        rw [zFlip_getD m z0 i k hk, Bool.or_eq_true]
        rw [incidenceInput_getD_lt _ _ k hk] at ht
        rcases ht with ⟨_, hp'⟩ | ⟨_, hl'⟩
        · simp only [Finset.mem_singleton] at hp'
          left
          have hk_eq : k = p.val := by have := congrArg Fin.val hp'; simpa using this
          rw [hk_eq]
          have hg := incidenceInput_getD_pt P0 L0 p
          simp only [hpP0, decide_true] at hg; exact hg
        · simp only [Finset.mem_singleton] at hl'
          right; have : k = i := by have := congrArg Fin.val hl'; simp only at this; omega
          simp [this]
    obtain ⟨p, l, hpl, hle⟩ := hex_pl
    exact wv_mono hAO (incidenceInput_length _ _) (zFlip_length _ _ _) hle C.output (hinc l p hpl)
  let A' := A ∩ S0
  have hA'_card_ge : A.card ≤ A'.card + 2 * q := by
    have hsub : A \ A' ⊆ T0 := by
      intro x hx
      simp only [A', Finset.mem_sdiff, Finset.mem_inter] at hx
      have hxlt : x < m := Finset.mem_range.mp (Finset.mem_filter.mp hx.1).1
      have hnotS0 : x ∉ S0 := fun h => hx.2 ⟨hx.1, h⟩
      simp only [S0, Finset.mem_filter, Finset.mem_range] at hnotS0
      have hnt : z0.getD x false ≠ false := fun h => hnotS0 ⟨hxlt, h⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxlt, ?_⟩
      cases hb : z0.getD x false
      · exact absurd hb hnt
      · rfl
    have h1 := Finset.card_le_card hsub
    rw [hT0_card] at h1
    have h2 := Finset.card_sdiff_add_card_inter A S0
    dsimp only [A'] at h1 ⊢
    have h3 : A \ (A ∩ S0) = A \ S0 := by ext x; simp
    rw [h3] at h1
    omega
  have huA_z0_false : ∀ x ∈ A', wv C z0 (uA x) = false := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxS0 : x ∈ S0 := (Finset.mem_inter.mp hx).2
    have hs := hA_spec x hxA
    cases hb : wv C z0 (uA x) with
    | false => rfl
    | true =>
      exfalso
      have hle : ∀ i < m, z0.getD i false = true → (zFlip m z0 x).getD i false = true := by
        intro i hi ht; rw [zFlip_getD m z0 x i hi, ht]; rfl
      have hflip_u : wv C (zFlip m z0 x) (uA x) = true :=
        wv_mono hAO hz0_len (zFlip_length _ _ _) hle (uA x) hb
      have hagree : ∀ i < m, i ≠ x → z0.getD i false = (zFlip m z0 x).getD i false := by
        intro i hi hne; rw [zFlip_getD m z0 x i hi]; simp [hne]
      have hout_not : C.output ∉ ChA x := by
        intro hc
        have h1 := hs.2.1 C.output hc
        rw [hoh_out] at h1
        have : x ∈ (∅ : Finset ℕ) := by rw [h1]; exact Finset.mem_singleton_self x
        simp at this
      have hce := barrier_eval_eq hAO C.output x (ChA x) (uA x) hs.1
        z0 (zFlip m z0 x) hz0_len (zFlip_length _ _ _) hagree (by rw [hb, hflip_u])
        C.output (Or.inr ⟨outJ, houtR, hout⟩) hout_not
      rw [hz0_false, hz0_flip_true x hxS0] at hce; cases hce
  let andPick (j : ℕ) : Option ℕ :=
    if h : ∃ x ∈ A', aA x = j then some (uA (Classical.choose h))
    else if wv C z0 (gi0 C j) = false then some (gi0 C j)
    else if wv C z0 (gi1 C j) = false then some (gi1 C j)
    else none
  have handPick_valid : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ c, andPick j = some c → c = gi0 C j ∨ c = gi1 C j := by
    intro j _ _ c hc
    dsimp only [andPick] at hc
    split_ifs at hc with h1 h2 h3
    · injection hc with heq; subst heq
      let x0 := Classical.choose h1
      have hspec : x0 ∈ A' ∧ aA x0 = j := Classical.choose_spec h1
      have hs := hA_spec x0 (Finset.mem_inter.mp hspec.1).1
      have hxj : aA x0 = j := hspec.2
      change uA x0 = gi0 C j ∨ uA x0 = gi1 C j
      rw [← hxj]
      exact (hs.2.2.2.2.2.1.imp And.left And.right).imp Eq.symm Eq.symm
    · injection hc with heq; exact Or.inl heq.symm
    · injection hc with heq; exact Or.inr heq.symm
  have handPick_sound : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      wv C z0 (m + j) = false →
      ∃ c, andPick j = some c ∧ (c = gi0 C j ∨ c = gi1 C j) ∧ wv C z0 c = false := by
    intro j hj hand hfj
    rw [wv_and_eq hAO hz0_len hj hand, Bool.and_eq_false_iff] at hfj
    dsimp only [andPick]
    split_ifs with h1 h2 h3
    · let x0 := Classical.choose h1
      have hspec : x0 ∈ A' ∧ aA x0 = j := Classical.choose_spec h1
      have hs := hA_spec x0 (Finset.mem_inter.mp hspec.1).1
      have hxj : aA x0 = j := hspec.2
      refine ⟨uA x0, rfl, ?_, huA_z0_false x0 hspec.1⟩
      rw [← hxj]
      exact (hs.2.2.2.2.2.1.imp And.left And.right).imp Eq.symm Eq.symm
    · exact ⟨gi0 C j, rfl, Or.inl rfl, h2⟩
    · exact ⟨gi1 C j, rfl, Or.inr rfl, h3⟩
    · exfalso; rcases hfj with h | h; exact h2 h; exact h3 h
  have handPick_ax : ∀ x ∈ A', andPick (aA x) = some (uA x) := by
    intro x hx
    have hex : ∃ y ∈ A', aA y = aA x := ⟨x, hx, rfl⟩
    dsimp only [andPick]
    simp only [hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    have heq := ha_inj _ (Finset.mem_inter.mp hspec.1).1 x (Finset.mem_inter.mp hx).1 hspec.2
    rw [heq]
  let V := sensVis m C andPick C.output
  let V_or := V.filter (fun j => (gateAt C j).op = GateOp.or)
  have hVor_sub : V_or ⊆ R :=
    Finset.Subset.trans (Finset.filter_subset _ _) (sensVis_sub_inCone hAO andPick handPick_valid C.output)
  have hVor_card : m - 2 * q ≤ 1 + V_or.card := by
    have hS0_sub : S0 ⊆ sens m C S0 andPick C.output :=
      fun i hi => sens_sound hAO z0 hz0_len S0 andPick handPick_sound i hi C.output hz0_false (hz0_flip_true i hi)
    have h1 := Finset.card_le_card hS0_sub
    rw [hS0_card] at h1
    have h2 := sens_card_le_vis_or hAO hm_pos S0 andPick handPick_valid C.output
    exact le_trans h1 h2
  -- Private trees T_x for x ∈ A'
  let TA (x : ℕ) : Finset ℕ := privTree m C R (vA x)
  have hTA_sub : ∀ x ∈ A', TA x ⊆ R := fun x _ t ht => (privTree_props hAO C.output (vA x) t ht).1
  have hTA_disj_Vor : ∀ x ∈ A', Disjoint V_or (TA x) := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hs := hA_spec x hxA
    have hux_oh : (oneHot m C (uA x)).card ≤ 1 := by
      rw [hs.2.1 (uA x) hs.1.2.1, Finset.card_singleton]
    have hvrx : gi0 C (aA x) = vA x ∨ gi1 C (aA x) = vA x := by
      rcases hs.2.2.2.2.2.1 with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h
    have hdisjV := sensVis_disjoint_privTree hAO C.output andPick handPick_valid
      (aA x) (vA x) (uA x) hs.2.2.2.1 hs.2.2.2.2.1 hvrx
      (handPick_ax x hx) hux_oh C.output (Or.inr ⟨outJ, houtR, hout⟩)
      (fun t ht heq => by
        have h2 := (privTree_props hAO C.output (vA x) t ht).2.2
        rw [← heq, hoh_out] at h2; simp at h2)
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hdisjV
  have hTA_disj_aA : ∀ x ∈ A', ∀ y ∈ A, aA y ∉ TA x := by
    intro x _ y hy hmem
    have h2 := (privTree_props hAO C.output (vA x) (aA y) hmem).2.2
    rw [(hA_spec y hy).2.2.2.2.2.2.2.1] at h2; simp at h2
  have hTA_disj_pair : ∀ x1 ∈ A', ∀ x2 ∈ A', x1 ≠ x2 → Disjoint (TA x1) (TA x2) := by
    intro x1 hx1 x2 hx2 hne
    rw [Finset.disjoint_left]
    intro t0 ht01 ht02
    have hne_inter : (TA x1 ∩ TA x2).Nonempty := ⟨t0, Finset.mem_inter.mpr ⟨ht01, ht02⟩⟩
    let t := (TA x1 ∩ TA x2).max' hne_inter
    have ht_inter : t ∈ TA x1 ∩ TA x2 := Finset.max'_mem _ hne_inter
    have ht1 : t ∈ TA x1 := (Finset.mem_inter.mp ht_inter).1
    have ht2 : t ∈ TA x2 := (Finset.mem_inter.mp ht_inter).2
    have ht_props := privTree_props hAO C.output (vA x1) t ht1
    obtain ⟨r, hrR, hrr⟩ := deg_eq_one_exists_reader C R (m + t) ht_props.2.1
    have hrr_or : gi0 C r = m + t ∨ gi1 C r = m + t := hrr.imp And.left And.left
    have hs1 := hA_spec x1 (Finset.mem_inter.mp hx1).1
    have hs2 := hA_spec x2 (Finset.mem_inter.mp hx2).1
    have hvr1 : gi0 C (aA x1) = vA x1 ∨ gi1 C (aA x1) = vA x1 := by
      rcases hs1.2.2.2.2.2.1 with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h
    have hvr2 : gi0 C (aA x2) = vA x2 ∨ gi1 C (aA x2) = vA x2 := by
      rcases hs2.2.2.2.2.2.1 with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h
    have hr1 := privTree_reader_mem hAO C.output (vA x1) (aA x1) hs1.2.2.2.1 hvr1 t ht1 r hrR hrr_or
    have hr2 := privTree_reader_mem hAO C.output (vA x2) (aA x2) hs2.2.2.2.1 hvr2 t ht2 r hrR hrr_or
    simp only [Finset.mem_insert] at hr1 hr2
    rcases hr1 with rfl | hrT1
    · rcases hr2 with haeq | hrT2
      · exact hne (ha_inj x1 (Finset.mem_inter.mp hx1).1 x2 (Finset.mem_inter.mp hx2).1 haeq)
      · exact hTA_disj_aA x2 hx2 x1 (Finset.mem_inter.mp hx1).1 hrT2
    · rcases hr2 with rfl | hrT2
      · exact hTA_disj_aA x1 hx1 x2 (Finset.mem_inter.mp hx2).1 hrT1
      · have hr_le : r ≤ t := Finset.le_max' (TA x1 ∩ TA x2) r (Finset.mem_inter.mpr ⟨hrT1, hrT2⟩)
        have hrlt : r < C.gates.length := Finset.mem_range.mp (inCone_sub_range hAO C.output hrR)
        have hlt := gate_inputs_lt hAO hrlt
        rcases hrr_or with h | h <;> omega
  have hins_disj : ∀ x1 ∈ A', ∀ x2 ∈ A', x1 ≠ x2 →
      Disjoint (insert (aA x1) (TA x1)) (insert (aA x2) (TA x2)) := by
    intro x1 hx1 x2 hx2 hne
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
    refine ⟨?_, ?_, hTA_disj_pair x1 hx1 x2 hx2 hne⟩
    · simp only [Finset.mem_insert, not_or]
      exact ⟨fun e => hne (ha_inj x1 (Finset.mem_inter.mp hx1).1 x2 (Finset.mem_inter.mp hx2).1 e),
        hTA_disj_aA x2 hx2 x1 (Finset.mem_inter.mp hx1).1⟩
    · exact hTA_disj_aA x1 hx1 x2 (Finset.mem_inter.mp hx2).1
  -- Case A vs Case B on A'
  let isCaseA (x : ℕ) : Prop :=
    ∃ (p k : ℕ), p ∈ insert (aA x) (TA x) ∧ k ∈ R.erase outJ ∧
      2 ≤ deg C R (m + k) ∧ 2 ≤ (oneHot m C (m + k)).card ∧ (gi0 C p = m + k ∨ gi1 C p = m + k)
  let A'_A := A'.filter isCaseA
  let A'_B := A'.filter (fun x => ¬ isCaseA x)
  have hA'_part : A'_A.card + A'_B.card = A'.card :=
    card_filter_add_not A' isCaseA
  -- Bound 1 via W_A for A'_A
  let pA (x : ℕ) : ℕ := if h : isCaseA x then Classical.choose h else 0
  let kA (x : ℕ) : ℕ := if h : isCaseA x then Classical.choose (Classical.choose_spec h) else 0
  have hCaseA_spec : ∀ x ∈ A'_A,
      pA x ∈ insert (aA x) (TA x) ∧ kA x ∈ R.erase outJ ∧
      2 ≤ deg C R (m + kA x) ∧ 2 ≤ (oneHot m C (m + kA x)).card ∧
      (gi0 C (pA x) = m + kA x ∨ gi1 C (pA x) = m + kA x) := by
    intro x hx
    have h : isCaseA x := (Finset.mem_filter.mp hx).2
    dsimp only [pA, kA]; simp only [h, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec h)
  let W_A : Finset ℕ := A'_A.image kA
  have hWA_sub : W_A ⊆ R.erase outJ := by
    intro k hk; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk; exact (hCaseA_spec x hx).2.1
  have hGB_WA_disj : Disjoint G_B W_A := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := hGB_oh k hk1
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk2
    have h2 := (hCaseA_spec x hx).2.2.2.1
    omega
  have hWA_sum : A'_A.card ≤ 2 * ∑ k ∈ W_A, (deg C R (m + k) - 1) := by
    have hfib : A'_A.card = ∑ k ∈ W_A, (A'_A.filter (fun x => kA x = k)).card := by
      have := Finset.card_eq_sum_card_fiberwise (f := kA) (s := A'_A) (t := W_A)
        (fun x hx => Finset.mem_image_of_mem kA hx)
      exact this
    rw [hfib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hk
    let Fk := A'_A.filter (fun x => kA x = kA x0)
    have hp_inj : Set.InjOn pA (↑Fk : Set ℕ) := by
      intro x1 hx1 x2 hx2 heq
      by_contra hne
      have hx1' : x1 ∈ A' := (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).1
      have hx2' : x2 ∈ A' := (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).1
      have hp1 : pA x1 ∈ insert (aA x1) (TA x1) := (hCaseA_spec x1 (Finset.mem_filter.mp hx1).1).1
      have hp2 : pA x2 ∈ insert (aA x2) (TA x2) := (hCaseA_spec x2 (Finset.mem_filter.mp hx2).1).1
      rw [← heq] at hp2
      exact Finset.disjoint_left.mp (hins_disj x1 hx1' x2 hx2' hne) hp1 hp2
    have hFk_le_deg : Fk.card ≤ deg C R (m + kA x0) := by
      rw [← Finset.card_image_of_injOn hp_inj]
      have hsub_R : Fk.image pA ⊆ R := by
        intro p hp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        have hxA' : x ∈ A' := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        have hpm := (hCaseA_spec x (Finset.mem_filter.mp hx).1).1
        simp only [Finset.mem_insert] at hpm
        rcases hpm with h | h
        · rw [h]; exact (hA_spec x (Finset.mem_inter.mp hxA').1).2.2.2.1
        · exact hTA_sub x hxA' h
      calc (Fk.image pA).card = ∑ _p ∈ Fk.image pA, 1 := by simp
        _ ≤ ∑ p ∈ Fk.image pA, ((if gi0 C p = m + kA x0 then 1 else 0) + (if gi1 C p = m + kA x0 then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          have hkx : kA x = kA x0 := (Finset.mem_filter.mp hx).2
          have hr := (hCaseA_spec x (Finset.mem_filter.mp hx).1).2.2.2.2
          rw [hkx] at hr
          rcases hr with h | h <;> simp [h]
        _ ≤ deg C R (m + kA x0) := Finset.sum_le_sum_of_subset hsub_R
    have hdeg2 : 2 ≤ deg C R (m + kA x0) := (hCaseA_spec x0 hx0).2.2.1
    dsimp only [Fk] at hFk_le_deg
    omega
  have hBound1 : 8 * N + A'_A.card ≤ 2 * R.card + 2 + 2 * A.card := by
    have hwb := wire_deg_bound hAO outJ hout houtLt
    have hsub_U : G_B ∪ W_A ⊆ R.erase outJ := Finset.union_subset hGB_sub hWA_sub
    have hsum_U : (∑ g ∈ G_B, (deg C R (m + g) - 1)) + (∑ k ∈ W_A, (deg C R (m + k) - 1)) ≤
        ∑ j ∈ R.erase outJ, (deg C R (m + j) - 1) := by
      rw [← Finset.sum_union hGB_WA_disj]
      exact Finset.sum_le_sum_of_subset hsub_U
    dsimp only [m, R] at hwb hsum_in_GB hsum_U hWA_sum ⊢
    omega
  -- Bound 2 via TA for A'_B
  have hTA_card_B : ∀ x ∈ A'_B, q ≤ (TA x).card := by
    intro x hx
    have hxA' : x ∈ A' := (Finset.mem_filter.mp hx).1
    have hnotA : ¬ isCaseA x := (Finset.mem_filter.mp hx).2
    have hxA : x ∈ A := (Finset.mem_inter.mp hxA').1
    have hxlt : x < m := Finset.mem_range.mp (Finset.mem_filter.mp hxA).1
    have hs := hA_spec x hxA
    have hv_oh : q + 1 ≤ (oneHot m C (vA x)).card := by
      have := Finset.card_le_card (show neighborsOf S x ⊆ oneHot m C (vA x) from hs.2.2.2.2.2.2.2.2)
      rw [neighborsOf_card S hq1 hN hcard huniq x hxlt] at this
      exact this
    have hv_in_TA : ∃ j0 ∈ TA x, vA x = m + j0 := by
      have hcl := inCone_closed hAO C.output (aA x) hs.2.2.2.1
      have hvr : gi0 C (aA x) = vA x ∨ gi1 C (aA x) = vA x := by
        rcases hs.2.2.2.2.2.1 with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h
      have hvR : vA x < m ∨ ∃ j0 ∈ R, vA x = m + j0 := by
        rcases hvr with h | h; rw [← h]; exact hcl.1; rw [← h]; exact hcl.2
      rcases hvR with hvlt | ⟨j0, hj0R, hv_eq⟩
      · exfalso; rw [oneHot_input m C (vA x) hvlt, Finset.card_singleton] at hv_oh; omega
      · have hj0ne : j0 ≠ outJ := by
          intro e; subst e; rw [← hout] at hv_eq; rw [hv_eq, hoh_out] at hv_oh; simp at hv_oh
        have hdeg_pos : 1 ≤ deg C R (m + j0) := deg_pos_of_reader C R (m + j0) (aA x) hs.2.2.2.1
          (by rw [← hv_eq]; exact hvr)
        have hdeg1 : deg C R (m + j0) = 1 := by
          by_contra hne1
          apply hnotA
          exact ⟨aA x, j0, Finset.mem_insert_self _ _, Finset.mem_erase.mpr ⟨hj0ne, hj0R⟩,
            by omega, by rw [← hv_eq]; omega, by rw [← hv_eq]; exact hvr⟩
        refine ⟨j0, ?_, hv_eq⟩
        dsimp only [TA]
        have hv_oh2 : 2 ≤ (oneHot (N + N) C (N + N + j0)).card := by
          rw [← hv_eq]; dsimp only [m] at hv_oh; omega
        rw [hv_eq, privTree_eq_insert hAO C.output j0 hj0R hdeg1 hv_oh2]
        exact Finset.mem_insert_self _ _
    obtain ⟨j0, hj0TA, hv_eq⟩ := hv_in_TA
    let E := (TA x).image (fun j => m + j)
    let ch (w : ℕ) : ℕ × ℕ := (gi0 C (w - m), gi1 C (w - m))
    have hexp := dag_expand (oneHot m C) E ch
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjlt := Finset.mem_range.mp (inCone_sub_range hAO C.output (hTA_sub x hxA' hj))
        simpa [ch] using gate_inputs_lt hAO hjlt)
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjlt := Finset.mem_range.mp (inCone_sub_range hAO C.output (hTA_sub x hxA' hj))
        simpa [ch] using oneHot_gate_sub hAO j hjlt)
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjR := hTA_sub x hxA' hj
        have hcl := inCone_closed hAO C.output j hjR
        have hchild_ok : ∀ c : ℕ, (gi0 C j = c ∨ gi1 C j = c) →
            (c < m ∨ ∃ k ∈ R, c = m + k) → c ∈ E ∨ (oneHot m C c).card ≤ 1 := by
          intro c hcr hcR
          by_cases hcE : c ∈ E
          · exact Or.inl hcE
          · right
            by_contra h2
            push Not at h2
            rcases hcR with hclt | ⟨k, hkR, rfl⟩
            · rw [oneHot_input m C c hclt, Finset.card_singleton] at h2; omega
            · have hkne : k ≠ outJ := by
                intro e; subst e; rw [← hout, hoh_out] at h2; simp at h2
              have hdp := deg_pos_of_reader C R (m + k) j hjR hcr
              by_cases hd1 : deg C R (m + k) = 1
              · apply hcE
                have hk_oh2 : 2 ≤ (oneHot (N + N) C (N + N + k)).card := by dsimp only [m] at h2; omega
                have hk_in_sub : k ∈ privTree m C R (m + k) := by
                  rw [privTree_eq_insert hAO C.output k hkR hd1 hk_oh2]
                  exact Finset.mem_insert_self _ _
                have hpriv_sub : ∀ w' : ℕ, j ∈ privTree m C R w' → k ∈ privTree m C R w' := by
                  intro w'
                  induction w' using Nat.strong_induction_on with
                  | ind w' ih =>
                    intro hjw'
                    by_cases hcond : m ≤ w' ∧ w' - m ∈ R ∧ deg C R w' = 1 ∧ 2 ≤ (oneHot m C w').card
                    · let t := w' - m
                      have hwt : w' = m + t := by omega
                      have htR : t ∈ R := hcond.2.1
                      have htlt := Finset.mem_range.mp (inCone_sub_range hAO C.output htR)
                      have hlt_t := gate_inputs_lt hAO htlt
                      rw [hwt] at hcond hjw' ⊢
                      rw [privTree_eq_insert hAO C.output t htR hcond.2.2.1 hcond.2.2.2] at hjw' ⊢
                      simp only [Finset.mem_insert, Finset.mem_union] at hjw' ⊢
                      rcases hjw' with rfl | h0 | h1
                      · rcases hcr with h0eq | h1eq
                        · right; left; rw [h0eq]; exact hk_in_sub
                        · right; right; rw [h1eq]; exact hk_in_sub
                      · right; left; exact ih _ (by omega) h0
                      · right; right; exact ih _ (by omega) h1
                    · rw [privTree_eq_empty_of_not hcond] at hjw'; simp at hjw'
                exact Finset.mem_image.mpr ⟨k, hpriv_sub (vA x) hj, rfl⟩
              · apply hnotA
                exact ⟨j, k, Finset.mem_insert_of_mem hj, Finset.mem_erase.mpr ⟨hkne, hkR⟩,
                  by omega, by omega, hcr⟩
        have hsub : m + j - m = j := by omega
        dsimp only [ch]; rw [hsub]
        exact ⟨hchild_ok (gi0 C j) (Or.inl rfl) hcl.1, hchild_ok (gi1 C j) (Or.inr rfl) hcl.2⟩)
      {vA x}
      (fun w hw => by
        simp only [Finset.mem_singleton] at hw; subst hw
        exact Or.inl (Finset.mem_image.mpr ⟨j0, hj0TA, hv_eq.symm⟩))
    have hb : ({vA x} : Finset ℕ).biUnion (oneHot m C) = oneHot m C (vA x) := by ext i; simp
    have hEcard : E.card = (TA x).card := Finset.card_image_of_injective _ (fun _ _ h => by omega)
    rw [hb, Finset.card_singleton, hEcard] at hexp
    omega
  have hBound2 : 2 * N + A.card + q * A'_B.card ≤ R.card + 2 * q + 1 := by
    let U_A := A.image aA
    let U_T := A'_B.biUnion TA
    have hUA_sub : U_A ⊆ R := by
      intro g hg; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg; exact (hA_spec x hx).2.2.2.1
    have hUT_sub : U_T ⊆ R := by
      intro t ht; obtain ⟨x, hx, htx⟩ := Finset.mem_biUnion.mp ht
      exact hTA_sub x (Finset.mem_filter.mp hx).1 htx
    have hUA_card : U_A.card = A.card := Finset.card_image_of_injOn (fun x1 h1 x2 h2 e => ha_inj x1 h1 x2 h2 e)
    have hUT_card : q * A'_B.card ≤ U_T.card := by
      have hpw : Set.PairwiseDisjoint (↑A'_B : Set ℕ) TA := fun x1 h1 x2 h2 hne =>
        hTA_disj_pair x1 (Finset.mem_filter.mp h1).1 x2 (Finset.mem_filter.mp h2).1 hne
      rw [Finset.card_biUnion hpw]
      calc q * A'_B.card = ∑ _x ∈ A'_B, q := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ x ∈ A'_B, (TA x).card := Finset.sum_le_sum fun x hx => hTA_card_B x hx
    have hd1 : Disjoint V_or U_A := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      have hor : (gateAt C g).op = GateOp.or := (Finset.mem_filter.mp hg1).2
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg2
      have hand := (hA_spec x hx).2.2.2.2.1
      rw [hand] at hor; cases hor
    have hd2 : Disjoint V_or U_T := by
      rw [Finset.disjoint_right]
      intro t ht htv
      obtain ⟨x, hx, htx⟩ := Finset.mem_biUnion.mp ht
      exact Finset.disjoint_left.mp (hTA_disj_Vor x (Finset.mem_filter.mp hx).1) htv htx
    have hd3 : Disjoint U_A U_T := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg1
      obtain ⟨x, hx, hgx⟩ := Finset.mem_biUnion.mp hg2
      exact hTA_disj_aA x (Finset.mem_filter.mp hx).1 y hy hgx
    have hall_sub : V_or ∪ (U_A ∪ U_T) ⊆ R := Finset.union_subset hVor_sub (Finset.union_subset hUA_sub hUT_sub)
    have hcard_all := Finset.card_le_card hall_sub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hd1, hd2⟩),
      Finset.card_union_of_disjoint hd3, hUA_card] at hcard_all
    omega
  have hfinal : 349 * N ≤ 100 * R.card :=
    final_arith q N R.card A.card A'_A.card A'_B.card hq hN hA_le_N (by omega) hBound1 hBound2
  omega

end MainProof

end PEqualNP.Outside.L_meta_5351

theorem PEqualNP.Outside.L_meta_5351 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x11 x12 : Finset (Fin x2)), x12.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x11 x12 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x11 x12) = Bool.false) →
      (349 : ℕ) * x2 ≤ (100 : ℕ) * x4.size :=
  PEqualNP.Outside.L_meta_5351.main_proof
