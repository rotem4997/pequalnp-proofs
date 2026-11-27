import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7497

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_gateStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, gateStep, List.length_append, List.length_singleton]
    omega

lemma list_getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma list_getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma foldl_gateStep_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (gateStep w g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [ih (gateStep w g) hlen]
    exact list_getD_append_left w _ i false hi

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_gateStep_length C.gates x

lemma wires_getD_take (C : Circuit) (x : List Bool) (t w : ℕ)
    (ht : t ≤ C.gates.length) (hw : w < x.length + t) :
    ({ gates := C.gates.take t, output := w } : Circuit).eval x = (C.wires x).getD w false := by
  simp only [Circuit.eval, wires_eq_foldl]
  have hsplit : C.gates = C.gates.take t ++ C.gates.drop t := (List.take_append_drop t C.gates).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : w < ((C.gates.take t).foldl gateStep x).length := by
    rw [foldl_gateStep_length, List.length_take, Nat.min_eq_left ht]
    exact hw
  exact (foldl_gateStep_getD_of_lt (C.gates.drop t) _ w hlen).symm

lemma wires_getD_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false :=
  foldl_gateStep_getD_of_lt C.gates x w hw

lemma gateAt_eq_getElem (C : Circuit) (t : ℕ) (ht : t < C.gates.length) :
    gateAt C t = C.gates[t] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

lemma wires_getD_gate (C : Circuit) (x : List Bool) (t : ℕ) (ht : t < C.gates.length)
    (a b : ℕ) (ha : a < x.length + t) (hb : b < x.length + t)
    (hins : (gateAt C t).inputs = [a, b]) :
    (C.wires x).getD (x.length + t) false =
      (gateAt C t).op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
  have ht1 : t + 1 ≤ C.gates.length := ht
  have hw : x.length + t < x.length + (t + 1) := by omega
  rw [← wires_getD_take C x (t + 1) (x.length + t) ht1 hw]
  simp only [Circuit.eval, wires_eq_foldl]
  have htake : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]] := List.take_succ_eq_append_getElem ht
  rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set pref := (C.gates.take t).foldl gateStep x
  have hplen : pref.length = x.length + t := by
    rw [foldl_gateStep_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt ht)]
  rw [gateStep, list_getD_append_right pref _ (x.length + t) false (by omega)]
  have hsub : x.length + t - pref.length = 0 := by omega
  rw [hsub]
  simp only [List.getD_cons_zero]
  rw [← gateAt_eq_getElem C t ht, hins]
  simp only [List.map_cons, List.map_nil]
  have hpa : pref.getD a false = (C.wires x).getD a false := by
    have := wires_getD_take C x t a (Nat.le_of_lt ht) ha
    simpa only [Circuit.eval, wires_eq_foldl] using this
  have hpb : pref.getD b false = (C.wires x).getD b false := by
    have := wires_getD_take C x t b (Nat.le_of_lt ht) hb
    simpa only [Circuit.eval, wires_eq_foldl] using this
  rw [hpa, hpb]
  rfl

lemma gateOp_and_eval_two (u v : Bool) : GateOp.and.eval [u, v] = (u && v) := by
  cases u <;> cases v <;> rfl

lemma gateOp_or_eval_two (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
  cases u <;> cases v <;> rfl

lemma incidenceInput_length {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    (incidenceInput X Y).length = n + m := by
  simp [incidenceInput]

lemma incidenceInput_getD_lt {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m))
    (w : ℕ) (hw : w < n) :
    (incidenceInput X Y).getD w false = decide (⟨w, hw⟩ ∈ X) := by
  unfold incidenceInput
  rw [list_getD_append_left _ _ w false (by simp [hw])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hw]

lemma incidenceInput_getD_ge {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m))
    (w : ℕ) (h1 : n ≤ w) (h2 : w < n + m) :
    (incidenceInput X Y).getD w false = decide (⟨w - n, by omega⟩ ∈ Y) := by
  unfold incidenceInput
  rw [list_getD_append_right _ _ w false (by simp [h1])]
  rw [List.length_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hsub : w - n < m := by omega
  simp [hsub]

def wireVal (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

def safe {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit) (l : Fin x2) (w : ℕ) : Prop :=
  wireVal C (incidenceInput (x3 l)ᶜ {l}) w = false

def coverSet {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit) (l : Fin x2) (w : ℕ) :
    Finset (Fin x2) :=
  (x3 l).filter fun p => wireVal C (incidenceInput {p} {l}) w = true

def HasCover {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit) (l : Fin x2)
    (t c : ℕ) : Prop :=
  ∃ F : Finset ℕ, F.card ≤ c ∧
    (∀ w ∈ F, w < x2 + x2 + t ∧ safe x3 C l w) ∧
    x3 l ⊆ F.biUnion (coverSet x3 C l)

def isGood {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit) (t : ℕ) (l : Fin x2) : Bool :=
  match (gateAt C t).op, (gateAt C t).inputs with
  | GateOp.or, [a, b] =>
    !wireVal C (incidenceInput (x3 l)ᶜ {l}) a &&
    !wireVal C (incidenceInput (x3 l)ᶜ {l}) b &&
    decide (∃ p ∈ x3 l, wireVal C (incidenceInput {p} {l}) a = true ∧
      wireVal C (incidenceInput {p} {l}) b = false) &&
    decide (∃ p ∈ x3 l, wireVal C (incidenceInput {p} {l}) a = false ∧
      wireVal C (incidenceInput {p} {l}) b = true)
  | _, _ => false

lemma card_coverSet_le_one {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit)
    (l : Fin x2) (w : ℕ) (hw : w < x2 + x2) (hs : safe x3 C l w) :
    (coverSet x3 C l w).card ≤ 1 := by
  by_cases hlt : w < x2
  · have hsub : coverSet x3 C l w ⊆ {⟨w, hlt⟩} := by
      intro p hp
      simp only [coverSet, Finset.mem_filter] at hp
      have hv : wireVal C (incidenceInput {p} {l}) w = decide (⟨w, hlt⟩ ∈ ({p} : Finset (Fin x2))) := by
        unfold wireVal
        rw [wires_getD_input C _ w (by rw [incidenceInput_length]; omega)]
        exact incidenceInput_getD_lt {p} {l} w hlt
      rw [hv] at hp
      have hmem : (⟨w, hlt⟩ : Fin x2) ∈ ({p} : Finset (Fin x2)) := of_decide_eq_true hp.2
      simp only [Finset.mem_singleton] at hmem ⊢
      exact hmem.symm
    exact (Finset.card_le_card hsub).trans (by simp)
  · have hge : x2 ≤ w := by omega
    have hsafe' : decide (⟨w - x2, by omega⟩ ∈ ({l} : Finset (Fin x2))) = false := by
      unfold safe wireVal at hs
      rw [wires_getD_input C _ w (by rw [incidenceInput_length]; omega),
        incidenceInput_getD_ge _ _ w hge hw] at hs
      exact hs
    have hempty : coverSet x3 C l w = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [coverSet, Finset.mem_filter] at hp
      have hv : wireVal C (incidenceInput {p} {l}) w =
          decide (⟨w - x2, by omega⟩ ∈ ({l} : Finset (Fin x2))) := by
        unfold wireVal
        rw [wires_getD_input C _ w (by rw [incidenceInput_length]; omega)]
        exact incidenceInput_getD_ge {p} {l} w hge hw
      rw [hv, hsafe'] at hp
      exact Bool.false_ne_true hp.2
    rw [hempty]
    simp

lemma hasCover_zero_le {x1 x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit)
    (l : Fin x2) (hcard : (x3 l).card = x1 + 1) (c : ℕ) (hc : HasCover x3 C l 0 c) :
    x1 + 1 ≤ c := by
  rcases hc with ⟨F, hFc, hFok, hFcov⟩
  have h1 : (x3 l).card ≤ (F.biUnion (coverSet x3 C l)).card := Finset.card_le_card hFcov
  have h2 : (F.biUnion (coverSet x3 C l)).card ≤ ∑ w ∈ F, (coverSet x3 C l w).card :=
    Finset.card_biUnion_le
  have h3 : ∑ w ∈ F, (coverSet x3 C l w).card ≤ ∑ _w ∈ F, 1 := by
    apply Finset.sum_le_sum
    intro w hw
    have ⟨hlt, hs⟩ := hFok w hw
    exact card_coverSet_le_one x3 C l w (by omega) hs
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h3
  omega

lemma hasCover_end {x1 x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit)
    (l : Fin x2) (hcard : (x3 l).card = x1 + 1)
    (hright : RightOnIncidentPairs x3 C)
    (hfalse : C.eval (incidenceInput (x3 l)ᶜ {l}) = false) :
    HasCover x3 C l C.size 1 := by
  have hne : (x3 l).Nonempty := Finset.card_pos.mp (by omega)
  rcases hne with ⟨p0, hp0⟩
  have hout_lt : C.output < x2 + x2 + C.size := by
    by_contra hge
    have hlen : (C.wires (incidenceInput {p0} {l})).length = x2 + x2 + C.size := by
      rw [wires_length, incidenceInput_length, Circuit.size]
    have hval : C.eval (incidenceInput {p0} {l}) = false := by
      unfold Circuit.eval
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have htrue := hright l p0 hp0
    rw [hval] at htrue
    exact Bool.false_ne_true htrue
  refine ⟨{C.output}, by simp, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hout_lt, hfalse⟩
  · intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left, coverSet,
      Finset.mem_filter]
    exact ⟨hp, hright l p hp⟩

lemma hasCover_mono {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit) (l : Fin x2)
    (t c1 c2 : ℕ) (hle : c1 ≤ c2) (hc : HasCover x3 C l t c1) : HasCover x3 C l t c2 := by
  rcases hc with ⟨F, hFc, hFok, hFcov⟩
  exact ⟨F, hFc.trans hle, hFok, hFcov⟩

lemma hasCover_step {x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit)
    (hao : IsAO2 (x2 + x2) C) (l : Fin x2) (t c : ℕ) (ht : t < C.gates.length)
    (hc : HasCover x3 C l (t + 1) c) :
    HasCover x3 C l t (c + if isGood x3 C t l = true then 1 else 0) := by
  rcases hc with ⟨F, hFc, hFok, hFcov⟩
  set wt := x2 + x2 + t
  by_cases hmem : wt ∉ F
  · apply hasCover_mono x3 C l t c _ (Nat.le_add_right c _)
    refine ⟨F, hFc, ?_, hFcov⟩
    intro w hw
    have ⟨hlt, hs⟩ := hFok w hw
    have hne : w ≠ wt := fun h => hmem (h ▸ hw)
    exact ⟨by omega, hs⟩
  · push Not at hmem
    have hwt_safe : safe x3 C l wt := (hFok wt hmem).2
    have hgate_mem : gateAt C t ∈ C.gates := by
      rw [gateAt_eq_getElem C t ht]
      exact List.getElem_mem ht
    have hlen2 : (gateAt C t).inputs.length = 2 := hao.2.2 (gateAt C t) hgate_mem
    obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C t).inputs = [a, b] := by
      cases h : (gateAt C t).inputs with
      | nil => simp [h] at hlen2
      | cons a rest =>
        cases rest with
        | nil => simp [h] at hlen2
        | cons b rest2 =>
          cases rest2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [h] at hlen2
    have ha : a < wt := hao.2.1 t ht a (by rw [hab]; simp)
    have hb : b < wt := hao.2.1 t ht b (by rw [hab]; simp)
    have hval_eq : ∀ (A : Finset (Fin x2)),
        wireVal C (incidenceInput A {l}) wt =
          (gateAt C t).op.eval [wireVal C (incidenceInput A {l}) a,
            wireVal C (incidenceInput A {l}) b] := by
      intro A
      unfold wireVal
      have hlenA : (incidenceInput A {l}).length = x2 + x2 := incidenceInput_length A {l}
      have h1 := wires_getD_gate C (incidenceInput A {l}) t ht a b
        (by rw [hlenA]; exact ha) (by rw [hlenA]; exact hb) hab
      simpa only [hlenA] using h1
    have hop := hao.1 (gateAt C t) hgate_mem
    rcases hop with hand | hor
    · have hfalse_and : (wireVal C (incidenceInput (x3 l)ᶜ {l}) a &&
          wireVal C (incidenceInput (x3 l)ᶜ {l}) b) = false := by
        have h1 := hval_eq (x3 l)ᶜ
        rw [hand, gateOp_and_eval_two] at h1
        rw [← h1]
        exact hwt_safe
      have hcov_a : coverSet x3 C l wt ⊆ coverSet x3 C l a := by
        intro p hp
        simp only [coverSet, Finset.mem_filter] at hp ⊢
        have h1 := hval_eq {p}
        rw [hand, gateOp_and_eval_two] at h1
        rw [h1, Bool.and_eq_true] at hp
        exact ⟨hp.1, hp.2.1⟩
      have hcov_b : coverSet x3 C l wt ⊆ coverSet x3 C l b := by
        intro p hp
        simp only [coverSet, Finset.mem_filter] at hp ⊢
        have h1 := hval_eq {p}
        rw [hand, gateOp_and_eval_two] at h1
        rw [h1, Bool.and_eq_true] at hp
        exact ⟨hp.1, hp.2.2⟩
      rw [Bool.and_eq_false_iff] at hfalse_and
      apply hasCover_mono x3 C l t c _ (Nat.le_add_right c _)
      rcases hfalse_and with hsa | hsb
      · refine ⟨insert a (F.erase wt), ?_, ?_, ?_⟩
        · have h1 := Finset.card_insert_le a (F.erase wt)
          have h2 : (F.erase wt).card + 1 = F.card := Finset.card_erase_add_one hmem
          omega
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | ⟨hne, hwF⟩
          · exact ⟨ha, hsa⟩
          · have ⟨hlt, hs⟩ := hFok w hwF
            exact ⟨by omega, hs⟩
        · intro p hp
          have hp' := hFcov hp
          simp only [Finset.mem_biUnion] at hp' ⊢
          rcases hp' with ⟨w, hwF, hpw⟩
          by_cases hweq : w = wt
          · subst hweq
            exact ⟨a, Finset.mem_insert_self a _, hcov_a hpw⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hwF⟩), hpw⟩
      · refine ⟨insert b (F.erase wt), ?_, ?_, ?_⟩
        · have h1 := Finset.card_insert_le b (F.erase wt)
          have h2 : (F.erase wt).card + 1 = F.card := Finset.card_erase_add_one hmem
          omega
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | ⟨hne, hwF⟩
          · exact ⟨hb, hsb⟩
          · have ⟨hlt, hs⟩ := hFok w hwF
            exact ⟨by omega, hs⟩
        · intro p hp
          have hp' := hFcov hp
          simp only [Finset.mem_biUnion] at hp' ⊢
          rcases hp' with ⟨w, hwF, hpw⟩
          by_cases hweq : w = wt
          · subst hweq
            exact ⟨b, Finset.mem_insert_self b _, hcov_b hpw⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hwF⟩), hpw⟩
    · have hfalse_or : (wireVal C (incidenceInput (x3 l)ᶜ {l}) a ||
          wireVal C (incidenceInput (x3 l)ᶜ {l}) b) = false := by
        have h1 := hval_eq (x3 l)ᶜ
        rw [hor, gateOp_or_eval_two] at h1
        rw [← h1]
        exact hwt_safe
      rw [Bool.or_eq_false_iff] at hfalse_or
      rcases hfalse_or with ⟨hsa, hsb⟩
      have hcov_or : ∀ p ∈ coverSet x3 C l wt, p ∈ coverSet x3 C l a ∨ p ∈ coverSet x3 C l b := by
        intro p hp
        simp only [coverSet, Finset.mem_filter] at hp ⊢
        have h1 := hval_eq {p}
        rw [hor, gateOp_or_eval_two] at h1
        rw [h1, Bool.or_eq_true] at hp
        rcases hp.2 with ha1 | hb1
        · exact Or.inl ⟨hp.1, ha1⟩
        · exact Or.inr ⟨hp.1, hb1⟩
      by_cases hsub1 : coverSet x3 C l a ⊆ coverSet x3 C l b
      · apply hasCover_mono x3 C l t c _ (Nat.le_add_right c _)
        refine ⟨insert b (F.erase wt), ?_, ?_, ?_⟩
        · have h1 := Finset.card_insert_le b (F.erase wt)
          have h2 : (F.erase wt).card + 1 = F.card := Finset.card_erase_add_one hmem
          omega
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | ⟨hne, hwF⟩
          · exact ⟨hb, hsb⟩
          · have ⟨hlt, hs⟩ := hFok w hwF
            exact ⟨by omega, hs⟩
        · intro p hp
          have hp' := hFcov hp
          simp only [Finset.mem_biUnion] at hp' ⊢
          rcases hp' with ⟨w, hwF, hpw⟩
          by_cases hweq : w = wt
          · subst hweq
            rcases hcov_or p hpw with hpa | hpb
            · exact ⟨b, Finset.mem_insert_self b _, hsub1 hpa⟩
            · exact ⟨b, Finset.mem_insert_self b _, hpb⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hwF⟩), hpw⟩
      · by_cases hsub2 : coverSet x3 C l b ⊆ coverSet x3 C l a
        · apply hasCover_mono x3 C l t c _ (Nat.le_add_right c _)
          refine ⟨insert a (F.erase wt), ?_, ?_, ?_⟩
          · have h1 := Finset.card_insert_le a (F.erase wt)
            have h2 : (F.erase wt).card + 1 = F.card := Finset.card_erase_add_one hmem
            omega
          · intro w hw
            simp only [Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | ⟨hne, hwF⟩
            · exact ⟨ha, hsa⟩
            · have ⟨hlt, hs⟩ := hFok w hwF
              exact ⟨by omega, hs⟩
          · intro p hp
            have hp' := hFcov hp
            simp only [Finset.mem_biUnion] at hp' ⊢
            rcases hp' with ⟨w, hwF, hpw⟩
            by_cases hweq : w = wt
            · subst hweq
              rcases hcov_or p hpw with hpa | hpb
              · exact ⟨a, Finset.mem_insert_self a _, hpa⟩
              · exact ⟨a, Finset.mem_insert_self a _, hsub2 hpb⟩
            · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hwF⟩), hpw⟩
        · have hex1 : ∃ p ∈ x3 l, wireVal C (incidenceInput {p} {l}) a = true ∧
              wireVal C (incidenceInput {p} {l}) b = false := by
            rw [Finset.not_subset] at hsub1
            rcases hsub1 with ⟨p, hpa, hpnb⟩
            simp only [coverSet, Finset.mem_filter] at hpa hpnb
            have hbf : wireVal C (incidenceInput {p} {l}) b = false := by
              cases hbv : wireVal C (incidenceInput {p} {l}) b
              · rfl
              · exact False.elim (hpnb ⟨hpa.1, hbv⟩)
            exact ⟨p, hpa.1, hpa.2, hbf⟩
          have hex2 : ∃ p ∈ x3 l, wireVal C (incidenceInput {p} {l}) a = false ∧
              wireVal C (incidenceInput {p} {l}) b = true := by
            rw [Finset.not_subset] at hsub2
            rcases hsub2 with ⟨p, hpb, hpna⟩
            simp only [coverSet, Finset.mem_filter] at hpb hpna
            have haf : wireVal C (incidenceInput {p} {l}) a = false := by
              cases hav : wireVal C (incidenceInput {p} {l}) a
              · rfl
              · exact False.elim (hpna ⟨hpb.1, hav⟩)
            exact ⟨p, hpb.1, haf, hpb.2⟩
          have hgood : isGood x3 C t l = true := by
            unfold isGood
            rw [hor, hab]
            simp [hsa, hsb, hex1, hex2]
          simp only [hgood, ↓reduceIte]
          refine ⟨insert a (insert b (F.erase wt)), ?_, ?_, ?_⟩
          · have h1 := Finset.card_insert_le a (insert b (F.erase wt))
            have h2 := Finset.card_insert_le b (F.erase wt)
            have h3 : (F.erase wt).card + 1 = F.card := Finset.card_erase_add_one hmem
            omega
          · intro w hw
            simp only [Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | rfl | ⟨hne, hwF⟩
            · exact ⟨ha, hsa⟩
            · exact ⟨hb, hsb⟩
            · have ⟨hlt, hs⟩ := hFok w hwF
              exact ⟨by omega, hs⟩
          · intro p hp
            have hp' := hFcov hp
            simp only [Finset.mem_biUnion] at hp' ⊢
            rcases hp' with ⟨w, hwF, hpw⟩
            by_cases hweq : w = wt
            · subst hweq
              rcases hcov_or p hpw with hpa | hpb
              · exact ⟨a, Finset.mem_insert_self a _, hpa⟩
              · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self b _), hpb⟩
            · exact ⟨w, Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hweq, hwF⟩)), hpw⟩

lemma hasCover_back_ind {x1 x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit)
    (hao : IsAO2 (x2 + x2) C) (l : Fin x2) (hcard : (x3 l).card = x1 + 1)
    (hright : RightOnIncidentPairs x3 C)
    (hfalse : C.eval (incidenceInput (x3 l)ᶜ {l}) = false) :
    ∀ k ≤ C.size, HasCover x3 C l (C.size - k)
      (1 + ((Finset.Ico (C.size - k) C.size).filter (fun t => isGood x3 C t l = true)).card) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.sub_zero, Finset.Ico_self, Finset.filter_empty, Finset.card_empty, Nat.add_zero]
    exact hasCover_end x3 C l hcard hright hfalse
  | succ k ih =>
    intro hk
    have hk' : k ≤ C.size := Nat.le_of_succ_le hk
    have hprev := ih hk'
    set t := C.size - (k + 1)
    have ht_lt : t < C.gates.length := by
      have hsz : C.size = C.gates.length := rfl
      omega
    have ht_succ : t + 1 = C.size - k := by omega
    rw [← ht_succ] at hprev
    have hstep := hasCover_step x3 C hao l t _ ht_lt hprev
    have hico : Finset.Ico t C.size = insert t (Finset.Ico (t + 1) C.size) := by
      ext u
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have ht_not_mem : t ∉ Finset.Ico (t + 1) C.size := by
      simp only [Finset.mem_Ico]
      omega
    have hcard_eq : ((Finset.Ico t C.size).filter (fun u => isGood x3 C u l = true)).card =
        ((Finset.Ico (t + 1) C.size).filter (fun u => isGood x3 C u l = true)).card +
          if isGood x3 C t l = true then 1 else 0 := by
      rw [hico, Finset.filter_insert]
      by_cases hg : isGood x3 C t l = true
      · simp only [hg, ↓reduceIte]
        rw [Finset.card_insert_of_notMem]
        intro hmem
        exact ht_not_mem (Finset.mem_filter.mp hmem).1
      · simp [hg]
    rw [hcard_eq]
    simpa only [Nat.add_assoc] using hstep

lemma good_count_ge {x1 x2 : ℕ} (x3 : Fin x2 → Finset (Fin x2)) (C : Circuit)
    (hao : IsAO2 (x2 + x2) C) (l : Fin x2) (hcard : (x3 l).card = x1 + 1)
    (hright : RightOnIncidentPairs x3 C)
    (hfalse : C.eval (incidenceInput (x3 l)ᶜ {l}) = false) :
    x1 ≤ ((Finset.range C.size).filter (fun t => isGood x3 C t l = true)).card := by
  have h0 := hasCover_back_ind x3 C hao l hcard hright hfalse C.size (le_refl _)
  simp only [Nat.sub_self, Nat.Ico_zero_eq_range] at h0
  have hle := hasCover_zero_le x3 C l hcard _ h0
  omega

lemma main_proof (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : Circuit)
    (hcard : ∀ x5 : Fin x2, (x3 x5).card = x1 + 1)
    (hao : IsAO2 (x2 + x2) x4)
    (hright : RightOnIncidentPairs x3 x4)
    (hfalse : ∀ x8 : Fin x2, x4.eval (incidenceInput (x3 x8)ᶜ {x8}) = false)
    (hsize : 100 * x4.size < x2 * x1) :
    ∃ (x10 x11 : List Gate) (x12 x13 : ℕ) (x14 : Finset (Fin x2)),
      x4.gates = x10 ++ { op := GateOp.or, inputs := [x12, x13] : Gate } :: x11 ∧
      101 ≤ x14.card ∧
      ∀ x15 ∈ x14,
        have x17 : ℕ → Finset (Fin x2) → Bool := fun x17 x18 =>
          { gates := x10, output := x17 : Circuit }.eval (incidenceInput x18 {x15})
        x17 x12 (x3 x15)ᶜ = false ∧ x17 x13 (x3 x15)ᶜ = false ∧
        (∃ x18 ∈ x3 x15, x17 x12 {x18} = true ∧ x17 x13 {x18} = false) ∧
        ∃ x18 ∈ x3 x15, x17 x12 {x18} = false ∧ x17 x13 {x18} = true := by
  have hsum_ge : x2 * x1 ≤
      ∑ t ∈ Finset.range x4.size, (Finset.univ.filter (fun l : Fin x2 => isGood x3 x4 t l = true)).card := by
    have h1 : x2 * x1 = ∑ _l : Fin x2, x1 := by simp
    have h2 : ∑ _l : Fin x2, x1 ≤
        ∑ l : Fin x2, ((Finset.range x4.size).filter (fun t => isGood x3 x4 t l = true)).card := by
      apply Finset.sum_le_sum
      intro l _
      exact good_count_ge x3 x4 hao l (hcard l) hright (hfalse l)
    have h3 : ∑ l : Fin x2, ((Finset.range x4.size).filter (fun t => isGood x3 x4 t l = true)).card =
        ∑ l : Fin x2, ∑ t ∈ Finset.range x4.size, if isGood x3 x4 t l = true then 1 else 0 := by
      congr 1
      ext l
      rw [Finset.card_filter]
    have h4 : ∑ l : Fin x2, ∑ t ∈ Finset.range x4.size, (if isGood x3 x4 t l = true then 1 else 0) =
        ∑ t ∈ Finset.range x4.size, ∑ l : Fin x2, if isGood x3 x4 t l = true then 1 else 0 :=
      Finset.sum_comm
    have h5 : ∑ t ∈ Finset.range x4.size, ∑ l : Fin x2, (if isGood x3 x4 t l = true then 1 else 0) =
        ∑ t ∈ Finset.range x4.size, (Finset.univ.filter (fun l : Fin x2 => isGood x3 x4 t l = true)).card := by
      congr 1
      ext t
      rw [Finset.card_filter]
    omega
  obtain ⟨t, ht_mem, ht_big⟩ :
      ∃ t ∈ Finset.range x4.size,
        101 ≤ (Finset.univ.filter (fun l : Fin x2 => isGood x3 x4 t l = true)).card := by
    by_contra hno
    push Not at hno
    have hle : ∑ t ∈ Finset.range x4.size,
        (Finset.univ.filter (fun l : Fin x2 => isGood x3 x4 t l = true)).card ≤
        ∑ _t ∈ Finset.range x4.size, 100 := by
      apply Finset.sum_le_sum
      intro t ht
      have := hno t ht
      omega
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    omega
  have ht : t < x4.gates.length := Finset.mem_range.mp ht_mem
  set x14 : Finset (Fin x2) := Finset.univ.filter (fun l : Fin x2 => isGood x3 x4 t l = true)
  have hx14_ne : x14.Nonempty := Finset.card_pos.mp (by omega)
  rcases hx14_ne with ⟨l0, hl0⟩
  have hl0_good : isGood x3 x4 t l0 = true := (Finset.mem_filter.mp hl0).2
  have hgate_mem : gateAt x4 t ∈ x4.gates := by
    rw [gateAt_eq_getElem x4 t ht]
    exact List.getElem_mem ht
  have hlen2 : (gateAt x4 t).inputs.length = 2 := hao.2.2 (gateAt x4 t) hgate_mem
  obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt x4 t).inputs = [a, b] := by
    cases h : (gateAt x4 t).inputs with
    | nil => simp [h] at hlen2
    | cons a rest =>
      cases rest with
      | nil => simp [h] at hlen2
      | cons b rest2 =>
        cases rest2 with
        | nil => exact ⟨a, b, rfl⟩
        | cons _ _ => simp [h] at hlen2
  have hor : (gateAt x4 t).op = GateOp.or := by
    unfold isGood at hl0_good
    rw [hab] at hl0_good
    cases hop : (gateAt x4 t).op <;> simp [hop] at hl0_good ⊢
  have hgate_eq : x4.gates[t] = { op := GateOp.or, inputs := [a, b] : Gate } := by
    have h1 := gateAt_eq_getElem x4 t ht
    cases hg : x4.gates[t] with
    | mk op ins =>
      rw [hg] at h1
      rw [h1] at hor hab
      simp only at hor hab
      subst hor hab
      rfl
  have ha : a < x2 + x2 + t := hao.2.1 t ht a (by rw [hab]; simp)
  have hb : b < x2 + x2 + t := hao.2.1 t ht b (by rw [hab]; simp)
  refine ⟨x4.gates.take t, x4.gates.drop (t + 1), a, b, x14, ?_, ht_big, ?_⟩
  · calc x4.gates
        = x4.gates.take t ++ x4.gates.drop t := (List.take_append_drop t x4.gates).symm
      _ = x4.gates.take t ++ x4.gates[t] :: x4.gates.drop (t + 1) := by
          rw [List.drop_eq_getElem_cons ht]
      _ = x4.gates.take t ++ { op := GateOp.or, inputs := [a, b] : Gate } :: x4.gates.drop (t + 1) := by
          rw [hgate_eq]
  · intro l hl
    have hl_good : isGood x3 x4 t l = true := (Finset.mem_filter.mp hl).2
    unfold isGood at hl_good
    rw [hor, hab] at hl_good
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hl_good
    rcases hl_good with ⟨⟨⟨hfa, hfb⟩, hex1⟩, hex2⟩
    have heval_a : ∀ A : Finset (Fin x2),
        ({ gates := x4.gates.take t, output := a } : Circuit).eval (incidenceInput A {l}) =
          wireVal x4 (incidenceInput A {l}) a := by
      intro A
      exact wires_getD_take x4 (incidenceInput A {l}) t a (Nat.le_of_lt ht)
        (by rw [incidenceInput_length]; exact ha)
    have heval_b : ∀ A : Finset (Fin x2),
        ({ gates := x4.gates.take t, output := b } : Circuit).eval (incidenceInput A {l}) =
          wireVal x4 (incidenceInput A {l}) b := by
      intro A
      exact wires_getD_take x4 (incidenceInput A {l}) t b (Nat.le_of_lt ht)
        (by rw [incidenceInput_length]; exact hb)
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heval_a]; exact hfa
    · rw [heval_b]; exact hfb
    · rcases hex1 with ⟨p, hp, hpa, hpb⟩
      exact ⟨p, hp, by rw [heval_a]; exact hpa, by rw [heval_b]; exact hpb⟩
    · rcases hex2 with ⟨p, hp, hpa, hpb⟩
      exact ⟨p, hp, by rw [heval_a]; exact hpa, by rw [heval_b]; exact hpb⟩

end PEqualNP.Outside.L_meta_7497

theorem PEqualNP.Outside.L_meta_7497 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x5 : Fin x2), (x3 x5).card = x1 + (1 : ℕ)) →     PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →       PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →         (∀ (x8 : Fin x2), x4.eval (PEqualNP.GenericRejection.incidenceInput (x3 x8)ᶜ {x8}) = Bool.false) →           (100 : ℕ) * x4.size < x2 * x1 →             ∃ (x10 : List PEqualNP.CircuitLowerBounds.Gate) (x11 : List PEqualNP.CircuitLowerBounds.Gate) (x12 : ℕ) (x13 : ℕ) (x14 : Finset (Fin x2)),               x4.gates = x10 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x12, x13] : PEqualNP.CircuitLowerBounds.Gate } :: x11 ∧                 (101 : ℕ) ≤ x14.card ∧                   ∀ x15 ∈ x14,                     have x17 : ℕ → Finset (Fin x2) → Bool := fun (x17 : ℕ) (x18 : Finset (Fin x2)) => { gates := x10, output := x17 : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput x18 {x15});                     x17 x12 (x3 x15)ᶜ = Bool.false ∧ x17 x13 (x3 x15)ᶜ = Bool.false ∧ (∃ x18 ∈ x3 x15, x17 x12 {x18} = Bool.true ∧ x17 x13 {x18} = Bool.false) ∧ ∃ x18 ∈ x3 x15, x17 x12 {x18} = Bool.false ∧ x17 x13 {x18} = Bool.true :=
  PEqualNP.Outside.L_meta_7497.main_proof
