import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.ReadTwo

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (C : Circuit) (z : List Bool) (w : ℕ) : Bool :=
  (C.wires z).getD w false

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

lemma wv_gate (C : Circuit) (hRB : ReadsBack 26 C) (z : List Bool) (hz : z.length = 26)
    (j : ℕ) (hj : j < C.gates.length) :
    wv C z (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv C z i) := by
  unfold wv
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← hdrop, this]
  let pref := (C.gates.take j).foldl step z
  have hplen : pref.length = 26 + j := by
    simp only [pref, foldl_step_length, hz, List.length_take]
    omega
  have hpref_get : ∀ i < 26 + j, (C.gates.foldl step z).getD i false = pref.getD i false := by
    intro i hi
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
    exact foldl_step_getD_lt _ pref i (by omega)
  have hgate_eq : gateAt C j = C.gates[j] := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
  have hval : (C.gates.foldl step z).getD (26 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pref.getD i false) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlt : 26 + j < (step pref C.gates[j]).length := by
      simp only [step, List.length_append, List.length_singleton, hplen]; omega
    rw [foldl_step_getD_lt _ (step pref C.gates[j]) (26 + j) hlt, List.getD_eq_getElem _ _ hlt]
    have hidx : 26 + j = pref.length := hplen.symm
    simp only [step, hidx, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
  rw [hval, hgate_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < 26 + j := hRB j hj i (hgate_eq ▸ hi)
  exact (hpref_get i hilt).symm

lemma gate_inputs_pair {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0] := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => simp [h] at hlen
  | [_] => simp [h] at hlen
  | _ :: _ :: _ :: _ => simp [h] at hlen

lemma gate_inputs_lt {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs.getD 0 0 < 26 + j ∧ (gateAt C j).inputs.getD 1 0 < 26 + j := by
  have hpair := gate_inputs_pair hAO hj
  have h0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by rw [hpair]; simp
  have h1 : (gateAt C j).inputs.getD 1 0 ∈ (gateAt C j).inputs := by rw [hpair]; simp
  exact ⟨hAO.2.1 j hj _ h0, hAO.2.1 j hj _ h1⟩

lemma wv_and_eq {C : Circuit} (hAO : IsAO2 26 C) {z : List Bool} (hz : z.length = 26)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wv C z (26 + j) = (wv C z ((gateAt C j).inputs.getD 0 0) && wv C z ((gateAt C j).inputs.getD 1 0)) := by
  rw [wv_gate C hAO.2.1 z hz j hj, hop, gate_inputs_pair hAO hj]
  simp [GateOp.eval]

lemma wv_or_eq {C : Circuit} (hAO : IsAO2 26 C) {z : List Bool} (hz : z.length = 26)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wv C z (26 + j) = (wv C z ((gateAt C j).inputs.getD 0 0) || wv C z ((gateAt C j).inputs.getD 1 0)) := by
  rw [wv_gate C hAO.2.1 z hz j hj, hop, gate_inputs_pair hAO hj]
  simp [GateOp.eval]

lemma wv_mono {C : Circuit} (hAO : IsAO2 26 C) {x y : List Bool}
    (hx : x.length = 26) (hy : y.length = 26)
    (hle : ∀ i < 26, x.getD i false = true → y.getD i false = true) :
    ∀ w : ℕ, wv C x w = true → wv C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases h1 : w < 26
    · rw [wv_input C x w (by omega)] at htrue
      rw [wv_input C y w (by omega)]
      exact hle w h1 htrue
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
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

lemma list_filter_length_eq_card_range (l : List Gate) (p : Gate → Bool) (d : Gate) :
    (l.filter p).length = ((Finset.range l.length).filter (fun j => p (l.getD j d) = true)).card := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [List.filter_append, List.length_append, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    have hlast : (l ++ [g]).getD l.length d = g := by
      have hlt : l.length < (l ++ [g]).length := by simp
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    have hfilt_eq : (Finset.range l.length).filter (fun j => p ((l ++ [g]).getD j d) = true) =
        (Finset.range l.length).filter (fun j => p (l.getD j d) = true) := by
      apply Finset.filter_congr
      intro j hj
      have hjlt : j < l.length := Finset.mem_range.mp hj
      have hjlt2 : j < (l ++ [g]).length := by simp; omega
      rw [List.getD_eq_getElem _ _ hjlt2, List.getD_eq_getElem _ _ hjlt, List.getElem_append_left hjlt]
    rw [hlast, hfilt_eq]
    cases hpg : p g with
    | false =>
      simp [List.filter, hpg, ih]
    | true =>
      simp [List.filter, hpg, ih]

lemma nAnd_eq_card (C : Circuit) [DecidablePred (fun j => (gateAt C j).op = GateOp.and)] :
    nAnd C = ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)).card := by
  unfold nAnd
  rw [list_filter_length_eq_card_range C.gates _ ⟨GateOp.or, []⟩]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
  rfl

lemma nOr_eq_card (C : Circuit) [DecidablePred (fun j => (gateAt C j).op = GateOp.or)] :
    nOr C = ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or)).card := by
  unfold nOr
  rw [list_filter_length_eq_card_range C.gates _ ⟨GateOp.or, []⟩]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
  rfl

def pairInput (p l : Fin 13) : List Bool :=
  (List.ofFn fun x : Fin 13 => decide (x = p)) ++
  (List.ofFn fun x : Fin 13 => decide (x = l))

def quadInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
  (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))

lemma pairInput_length (p l : Fin 13) : (pairInput p l).length = 26 := by
  simp [pairInput]

lemma quadInput_length (Q : Finset (Fin 13)) : (quadInput Q).length = 26 := by
  simp [quadInput]

lemma pairInput_getD_true (p l : Fin 13) (i : ℕ) (hi : i < 26)
    (ht : (pairInput p l).getD i false = true) : i = p.val ∨ i = 13 + l.val := by
  have hlt : i < (pairInput p l).length := by rw [pairInput_length]; exact hi
  rw [List.getD_eq_getElem _ _ hlt] at ht
  simp only [pairInput] at ht
  by_cases h1 : i < 13
  · have hlt1 : i < (List.ofFn fun x : Fin 13 => decide (x = p)).length := by simp; omega
    rw [List.getElem_append_left hlt1, List.getElem_ofFn] at ht
    simp only [decide_eq_true_iff] at ht
    left
    have := congrArg Fin.val ht
    simpa using this
  · have hge : (List.ofFn fun x : Fin 13 => decide (x = p)).length ≤ i := by simp; omega
    rw [List.getElem_append_right hge] at ht
    simp only [List.length_ofFn, List.getElem_ofFn, decide_eq_true_iff] at ht
    right
    have := congrArg Fin.val ht
    simp only at this
    omega

lemma quadInput_getD_pt (Q : Finset (Fin 13)) (p : Fin 13) :
    (quadInput Q).getD p.val false = decide (p ∈ Q) := by
  have hlt1 : p.val < (List.ofFn fun x : Fin 13 => decide (x ∈ Q)).length := by simp
  have hlt2 : p.val < (quadInput Q).length := by rw [quadInput_length]; exact Nat.lt_trans p.isLt (by omega)
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [quadInput, List.getElem_append_left hlt1, List.getElem_ofFn, Fin.eta]

lemma quadInput_getD_ln (Q : Finset (Fin 13)) (l : Fin 13) :
    (quadInput Q).getD (13 + l.val) false = decide (l ∈ missLines singerLines3 Q) := by
  have hlt2 : 13 + l.val < (quadInput Q).length := by rw [quadInput_length]; omega
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [quadInput]
  have hge : (List.ofFn fun x : Fin 13 => decide (x ∈ Q)).length ≤ 13 + l.val := by simp
  rw [List.getElem_append_right hge]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn, Fin.eta]

lemma mem_singerLines3_add (p l s : Fin 13) :
    p + s ∈ singerLines3 (l + s) ↔ p ∈ singerLines3 l := by
  simp only [singerLines3, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_add]
  have hp := p.isLt
  have hl := l.isLt
  have hs := s.isLt
  have hmod : ((p.val + s.val) % 13 + 13 - (l.val + s.val) % 13) % 13 = (p.val + 13 - l.val) % 13 := by
    omega
  rw [hmod]

lemma mem_quadrangles_iff (Q : Finset (Fin 13)) :
    Q ∈ quadrangles singerLines3 ↔ Q.card = 4 ∧ ∀ l : Fin 13, (Q ∩ singerLines3 l).card ≤ 2 := by
  simp [quadrangles, Finset.mem_powersetCard]

lemma shift_mem_quadrangles (Q : Finset (Fin 13)) (hQ : Q ∈ quadrangles singerLines3) (s : Fin 13) :
    Q.image (· + s) ∈ quadrangles singerLines3 := by
  rw [mem_quadrangles_iff] at hQ ⊢
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hQ.1
  · intro l
    have hsub : Q.image (· + s) ∩ singerLines3 l = (Q ∩ singerLines3 (l - s)).image (· + s) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hx⟩
        refine ⟨a, ⟨ha, ?_⟩, rfl⟩
        have hl : l = (l - s) + s := (sub_add_cancel l s).symm
        rw [hl] at hx
        exact (mem_singerLines3_add a (l - s) s).mp hx
      · rintro ⟨a, ⟨ha, hal⟩, rfl⟩
        refine ⟨⟨a, ha, rfl⟩, ?_⟩
        have hl : l = (l - s) + s := (sub_add_cancel l s).symm
        rw [hl]
        exact (mem_singerLines3_add a (l - s) s).mpr hal
    rw [hsub, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hQ.2 (l - s)

lemma shift_mem_missLines (Q : Finset (Fin 13)) (l s : Fin 13) :
    l + s ∈ missLines singerLines3 (Q.image (· + s)) ↔ l ∈ missLines singerLines3 Q := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  constructor
  · intro h p hp hpQ
    exact h ((mem_singerLines3_add p l s).mpr hp) (Finset.mem_image_of_mem _ hpQ)
  · intro h x hx hximg
    obtain ⟨p, hpQ, rfl⟩ := Finset.mem_image.mp hximg
    exact h ((mem_singerLines3_add p l s).mp hx) hpQ

def Rlist (i : Fin 10) : List (Fin 13) :=
  match i.val with
  | 0 => [0, 1, 2, 5]
  | 1 => [0, 1, 2, 6]
  | 2 => [0, 1, 2, 7]
  | 3 => [0, 1, 2, 11]
  | 4 => [0, 1, 4, 6]
  | 5 => [0, 1, 4, 8]
  | 6 => [0, 1, 4, 11]
  | 7 => [0, 1, 5, 10]
  | 8 => [0, 1, 5, 11]
  | _ => [0, 1, 6, 7]

def R (i : Fin 10) : Finset (Fin 13) := (Rlist i).toFinset

def Qof (i : Fin 10) (s : Fin 13) : Finset (Fin 13) := (R i).image (· + s)

lemma R_mem_quadrangles (i : Fin 10) : R i ∈ quadrangles singerLines3 := by
  rw [mem_quadrangles_iff]
  fin_cases i <;> decide

lemma Qof_mem_quadrangles (i : Fin 10) (s : Fin 13) : Qof i s ∈ quadrangles singerLines3 :=
  shift_mem_quadrangles (R i) (R_mem_quadrangles i) s

lemma Qof_card (i : Fin 10) (s : Fin 13) : (Qof i s).card = 4 :=
  ((mem_quadrangles_iff _).mp (Qof_mem_quadrangles i s)).1

lemma R_miss_cover (i : Fin 10) (p : Fin 13) (hp : p ∉ R i) :
    ∃ l ∈ missLines singerLines3 (R i), p ∈ singerLines3 l := by
  fin_cases i <;> fin_cases p <;> revert hp <;> decide

lemma Qof_miss_cover (i : Fin 10) (s : Fin 13) (p : Fin 13) (hp : p ∉ Qof i s) :
    ∃ l ∈ missLines singerLines3 (Qof i s), p ∈ singerLines3 l := by
  have hp0 : p - s ∉ R i := by
    intro h
    apply hp
    exact Finset.mem_image.mpr ⟨p - s, h, sub_add_cancel p s⟩
  obtain ⟨l0, hl0m, hl0p⟩ := R_miss_cover i (p - s) hp0
  refine ⟨l0 + s, (shift_mem_missLines (R i) l0 s).mpr hl0m, ?_⟩
  have hps : p = (p - s) + s := (sub_add_cancel p s).symm
  rw [hps]
  exact (mem_singerLines3_add (p - s) l0 s).mpr hl0p

lemma Rlist_shift_inj :
    ∀ (i1 i2 : Fin 10) (d : Fin 13),
      (∀ x ∈ Rlist i1, x + d ∈ Rlist i2) → i1 = i2 ∧ d = 0 := by
  decide

lemma Qof_inj : Function.Injective (fun x : Fin 10 × Fin 13 => Qof x.1 x.2) := by
  rintro ⟨i1, s1⟩ ⟨i2, s2⟩ heq
  dsimp only at heq
  have hall : ∀ x ∈ Rlist i1, x + (s1 - s2) ∈ Rlist i2 := by
    intro x hx
    have hxR : x ∈ R i1 := List.mem_toFinset.mpr hx
    have hximg : x + s1 ∈ Qof i1 s1 := Finset.mem_image_of_mem _ hxR
    rw [heq] at hximg
    obtain ⟨y, hyR, hy⟩ := Finset.mem_image.mp hximg
    have hxy : x + (s1 - s2) = y := by
      have : x + (s1 - s2) + s2 = y + s2 := by
        calc x + (s1 - s2) + s2 = x + ((s1 - s2) + s2) := by rw [add_assoc]
          _ = x + s1 := by rw [sub_add_cancel]
          _ = y + s2 := hy.symm
      exact add_right_cancel this
    rw [hxy]
    exact List.mem_toFinset.mp hyR
  obtain ⟨hi, hd⟩ := Rlist_shift_inj i1 i2 (s1 - s2) hall
  have hs : s1 = s2 := sub_eq_zero.mp hd
  exact Prod.ext hi hs

def zOr (z1 z2 : List Bool) : List Bool :=
  List.ofFn fun k : Fin 26 => z1.getD k.val false || z2.getD k.val false

lemma zOr_length (z1 z2 : List Bool) : (zOr z1 z2).length = 26 := by
  simp [zOr]

lemma zOr_getD (z1 z2 : List Bool) (i : ℕ) (hi : i < 26) :
    (zOr z1 z2).getD i false = (z1.getD i false || z2.getD i false) := by
  have hlt : i < (zOr z1 z2).length := by rw [zOr_length]; exact hi
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [zOr, List.getElem_ofFn]

def evSel (C : Circuit) (sel : ℕ → Bool) (z : List Bool) (w : ℕ) : Bool :=
  if w < 26 then z.getD w false
  else if w - 26 < C.gates.length then
    let j := w - 26
    let g := gateAt C j
    let u := g.inputs.getD 0 0
    let v := g.inputs.getD 1 0
    if _hu : u < w then
      if _hv : v < w then
        match g.op with
        | GateOp.or => evSel C sel z u || evSel C sel z v
        | GateOp.and => if sel j then evSel C sel z v else evSel C sel z u
        | _ => false
      else false
    else false
  else false
termination_by w

lemma evSel_input (C : Circuit) (sel : ℕ → Bool) (z : List Bool) (w : ℕ) (hw : w < 26) :
    evSel C sel z w = z.getD w false := by
  rw [evSel]; simp only [hw, ↓reduceIte]

lemma evSel_ge (C : Circuit) (sel : ℕ → Bool) (z : List Bool) (w : ℕ)
    (hw : 26 + C.gates.length ≤ w) :
    evSel C sel z w = false := by
  rw [evSel]
  have h1 : ¬ (w < 26) := by omega
  have h2 : ¬ (w - 26 < C.gates.length) := by omega
  simp only [h1, h2, ↓reduceIte]

lemma evSel_or (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool) (z : List Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    evSel C sel z (26 + j) =
      (evSel C sel z ((gateAt C j).inputs.getD 0 0) || evSel C sel z ((gateAt C j).inputs.getD 1 0)) := by
  rw [evSel]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma evSel_and (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool) (z : List Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    evSel C sel z (26 + j) =
      (if sel j then evSel C sel z ((gateAt C j).inputs.getD 1 0)
       else evSel C sel z ((gateAt C j).inputs.getD 0 0)) := by
  rw [evSel]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma evSel_congr (C : Circuit) (hAO : IsAO2 26 C) (sel1 sel2 : ℕ → Bool)
    (hagree : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → sel1 j = sel2 j)
    (z : List Bool) :
    ∀ w : ℕ, evSel C sel1 z w = evSel C sel2 z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [evSel_input C sel1 z w h1, evSel_input C sel2 z w h1]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [evSel_and C hAO sel1 z j hjlt hand, evSel_and C hAO sel2 z j hjlt hand,
            hagree j hjlt hand, ih _ (by omega), ih _ (by omega)]
        · rw [evSel_or C hAO sel1 z j hjlt hor, evSel_or C hAO sel2 z j hjlt hor,
            ih _ (by omega), ih _ (by omega)]
      · rw [evSel_ge C sel1 z w (by omega), evSel_ge C sel2 z w (by omega)]

lemma evSel_of_wv (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool)
    (z : List Bool) (hz : z.length = 26) :
    ∀ w : ℕ, wv C z w = true → evSel C sel z w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases h1 : w < 26
    · rw [wv_input C z w (by omega)] at htrue
      rw [evSel_input C sel z w h1]
      exact htrue
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj] at htrue ⊢
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [wv_and_eq hAO hz hjlt hand, Bool.and_eq_true] at htrue
          rw [evSel_and C hAO sel z j hjlt hand]
          cases sel j
          · exact ih _ (by omega) htrue.1
          · exact ih _ (by omega) htrue.2
        · rw [wv_or_eq hAO hz hjlt hor, Bool.or_eq_true] at htrue
          rw [evSel_or C hAO sel z j hjlt hor, Bool.or_eq_true]
          rcases htrue with h | h
          · exact Or.inl (ih _ (by omega) h)
          · exact Or.inr (ih _ (by omega) h)
      · rw [wv_ge C z w (by omega)] at htrue
        cases htrue

def pickOf (C : Circuit) (z : List Bool) (j : ℕ) : Bool :=
  wv C z ((gateAt C j).inputs.getD 0 0)

lemma evSel_pickOf (C : Circuit) (hAO : IsAO2 26 C) (z : List Bool) (hz : z.length = 26) :
    ∀ w : ℕ, evSel C (pickOf C z) z w = wv C z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [evSel_input C _ z w h1, wv_input C z w (by omega)]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [evSel_and C hAO _ z j hjlt hand, wv_and_eq hAO hz hjlt hand,
            ih _ (by omega), ih _ (by omega)]
          dsimp only [pickOf]
          have hbool : ∀ a b : Bool, (if a = true then b else a) = (a && b) := by decide
          exact hbool _ _
        · rw [evSel_or C hAO _ z j hjlt hor, wv_or_eq hAO hz hjlt hor,
            ih _ (by omega), ih _ (by omega)]
      · rw [evSel_ge C _ z w (by omega), wv_ge C z w (by omega)]

lemma evSel_zOr (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool) (z1 z2 : List Bool) :
    ∀ w : ℕ, evSel C sel (zOr z1 z2) w = (evSel C sel z1 w || evSel C sel z2 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [evSel_input C sel _ w h1, evSel_input C sel z1 w h1, evSel_input C sel z2 w h1,
        zOr_getD z1 z2 w h1]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [evSel_and C hAO sel _ j hjlt hand, evSel_and C hAO sel z1 j hjlt hand,
            evSel_and C hAO sel z2 j hjlt hand]
          cases sel j
          · exact ih _ (by omega)
          · exact ih _ (by omega)
        · rw [evSel_or C hAO sel _ j hjlt hor, evSel_or C hAO sel z1 j hjlt hor,
            evSel_or C hAO sel z2 j hjlt hor, ih _ (by omega), ih _ (by omega)]
          cases evSel C sel z1 ((gateAt C j).inputs.getD 0 0) <;>
          cases evSel C sel z1 ((gateAt C j).inputs.getD 1 0) <;>
          cases evSel C sel z2 ((gateAt C j).inputs.getD 0 0) <;>
          cases evSel C sel z2 ((gateAt C j).inputs.getD 1 0) <;> rfl
      · rw [evSel_ge C sel _ w (by omega), evSel_ge C sel z1 w (by omega),
          evSel_ge C sel z2 w (by omega)]
        rfl

lemma lower_nAnd (C : Circuit) (hAO : IsAO2 26 C)
    (hinc : ∀ (p l : Fin 13), p ∈ singerLines3 l → C.eval (pairInput p l) = true)
    (hquad : ∀ Q ∈ quadrangles singerLines3, C.eval (quadInput Q) = false) :
    8 ≤ nAnd C := by
  classical
  let GA := (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)
  have hGA_eq : nAnd C = GA.card := nAnd_eq_card C
  let Φ : Fin 10 × Fin 13 → ({j // j ∈ GA} → Bool) :=
    fun x j => pickOf C (quadInput (Qof x.1 x.2)) j.val
  have hΦ_inj : Function.Injective Φ := by
    intro x1 x2 hEq
    by_contra hne
    have hQne : Qof x1.1 x1.2 ≠ Qof x2.1 x2.2 := fun h => hne (Qof_inj h)
    have hexp : ∃ p ∈ Qof x1.1 x1.2, p ∉ Qof x2.1 x2.2 := by
      by_contra hall
      push Not at hall
      have hsub : Qof x1.1 x1.2 ⊆ Qof x2.1 x2.2 := hall
      have hcardEq : (Qof x1.1 x1.2).card = (Qof x2.1 x2.2).card := by
        rw [Qof_card, Qof_card]
      exact hQne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardEq.symm))
    obtain ⟨p, hp1, hp2⟩ := hexp
    obtain ⟨l, hl2, hpl⟩ := Qof_miss_cover x2.1 x2.2 p hp2
    let z1 := quadInput (Qof x1.1 x1.2)
    let z2 := quadInput (Qof x2.1 x2.2)
    let sel := pickOf C z1
    have hagree : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        sel j = pickOf C z2 j := by
      intro j hj hop
      have hjGA : j ∈ GA := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩
      exact congrFun hEq ⟨j, hjGA⟩
    have hev1 : evSel C sel z1 C.output = false := by
      rw [evSel_pickOf C hAO z1 (quadInput_length _)]
      exact hquad (Qof x1.1 x1.2) (Qof_mem_quadrangles x1.1 x1.2)
    have hev2 : evSel C sel z2 C.output = false := by
      rw [evSel_congr C hAO sel (pickOf C z2) hagree z2 C.output,
        evSel_pickOf C hAO z2 (quadInput_length _)]
      exact hquad (Qof x2.1 x2.2) (Qof_mem_quadrangles x2.1 x2.2)
    have hevOr : evSel C sel (zOr z1 z2) C.output = false := by
      rw [evSel_zOr C hAO sel z1 z2 C.output, hev1, hev2]
      rfl
    have hle : ∀ i < 26, (pairInput p l).getD i false = true → (zOr z1 z2).getD i false = true := by
      intro i hi ht
      rw [zOr_getD z1 z2 i hi, Bool.or_eq_true]
      rcases pairInput_getD_true p l i hi ht with rfl | rfl
      · left
        have := quadInput_getD_pt (Qof x1.1 x1.2) p
        simp only [hp1, decide_true] at this
        exact this
      · right
        have := quadInput_getD_ln (Qof x2.1 x2.2) l
        simp only [hl2, decide_true] at this
        exact this
    have htrue_or : wv C (zOr z1 z2) C.output = true :=
      wv_mono hAO (pairInput_length p l) (zOr_length z1 z2) hle C.output (hinc p l hpl)
    have hevOrTrue : evSel C sel (zOr z1 z2) C.output = true :=
      evSel_of_wv C hAO sel (zOr z1 z2) (zOr_length z1 z2) C.output htrue_or
    rw [hevOr] at hevOrTrue
    cases hevOrTrue
  have hcard := Fintype.card_le_of_injective Φ hΦ_inj
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe] at hcard
  rw [hGA_eq]
  by_contra hlt
  push Not at hlt
  have hpow : 2 ^ GA.card ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

def zFlip (z : List Bool) (i : ℕ) : List Bool :=
  List.ofFn fun k : Fin 26 => z.getD k.val false || decide (k.val = i)

lemma zFlip_length (z : List Bool) (i : ℕ) : (zFlip z i).length = 26 := by
  simp [zFlip]

lemma zFlip_getD (z : List Bool) (i k : ℕ) (hk : k < 26) :
    (zFlip z i).getD k false = (z.getD k false || decide (k = i)) := by
  have hlt : k < (zFlip z i).length := by rw [zFlip_length]; exact hk
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [zFlip, List.getElem_ofFn]

def sens (C : Circuit) (z0 : List Bool) (S0 : Finset ℕ) (w : ℕ) : Finset ℕ :=
  if w < 26 then
    if w ∈ S0 then {w} else ∅
  else if w - 26 < C.gates.length then
    let g := gateAt C (w - 26)
    let u := g.inputs.getD 0 0
    let v := g.inputs.getD 1 0
    if _hu : u < w then
      if _hv : v < w then
        match g.op with
        | GateOp.or => sens C z0 S0 u ∪ sens C z0 S0 v
        | GateOp.and =>
          if wv C z0 u = false then sens C z0 S0 u
          else if wv C z0 v = false then sens C z0 S0 v
          else ∅
        | _ => ∅
      else ∅
    else ∅
  else ∅
termination_by w

lemma sens_input (C : Circuit) (z0 : List Bool) (S0 : Finset ℕ) (w : ℕ) (hw : w < 26) :
    sens C z0 S0 w = if w ∈ S0 then {w} else ∅ := by
  rw [sens]; simp only [hw, ↓reduceIte]

lemma sens_ge (C : Circuit) (z0 : List Bool) (S0 : Finset ℕ) (w : ℕ)
    (hw : 26 + C.gates.length ≤ w) :
    sens C z0 S0 w = ∅ := by
  rw [sens]
  have h1 : ¬ (w < 26) := by omega
  have h2 : ¬ (w - 26 < C.gates.length) := by omega
  simp only [h1, h2, ↓reduceIte]

lemma sens_or (C : Circuit) (hAO : IsAO2 26 C) (z0 : List Bool) (S0 : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    sens C z0 S0 (26 + j) =
      sens C z0 S0 ((gateAt C j).inputs.getD 0 0) ∪ sens C z0 S0 ((gateAt C j).inputs.getD 1 0) := by
  rw [sens]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma sens_and (C : Circuit) (hAO : IsAO2 26 C) (z0 : List Bool) (S0 : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    sens C z0 S0 (26 + j) =
      if wv C z0 ((gateAt C j).inputs.getD 0 0) = false then
        sens C z0 S0 ((gateAt C j).inputs.getD 0 0)
      else if wv C z0 ((gateAt C j).inputs.getD 1 0) = false then
        sens C z0 S0 ((gateAt C j).inputs.getD 1 0)
      else ∅ := by
  rw [sens]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma sens_sound (C : Circuit) (hAO : IsAO2 26 C) (z0 : List Bool) (hz0 : z0.length = 26)
    (S0 : Finset ℕ) (i : ℕ) (hiS : i ∈ S0) :
    ∀ w : ℕ, wv C z0 w = false → wv C (zFlip z0 i) w = true → i ∈ sens C z0 S0 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hf ht
    by_cases h1 : w < 26
    · rw [wv_input C z0 w (by omega)] at hf
      rw [wv_input C (zFlip z0 i) w (by rw [zFlip_length]; omega), zFlip_getD z0 i w h1, hf] at ht
      simp only [Bool.false_or, decide_eq_true_iff] at ht
      subst ht
      rw [sens_input C z0 S0 w h1]
      simp [hiS]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj] at hf ht ⊢
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [wv_and_eq hAO hz0 hjlt hand, Bool.and_eq_false_iff] at hf
          rw [wv_and_eq hAO (zFlip_length z0 i) hjlt hand, Bool.and_eq_true] at ht
          rw [sens_and C hAO z0 S0 j hjlt hand]
          by_cases hu : wv C z0 ((gateAt C j).inputs.getD 0 0) = false
          · simp only [hu, ↓reduceIte]
            exact ih _ (by omega) hu ht.1
          · have hv : wv C z0 ((gateAt C j).inputs.getD 1 0) = false := hf.resolve_left hu
            simp only [hu, hv, ↓reduceIte]
            exact ih _ (by omega) hv ht.2
        · rw [wv_or_eq hAO hz0 hjlt hor, Bool.or_eq_false_iff] at hf
          rw [wv_or_eq hAO (zFlip_length z0 i) hjlt hor, Bool.or_eq_true] at ht
          rw [sens_or C hAO z0 S0 j hjlt hor, Finset.mem_union]
          rcases ht with h | h
          · exact Or.inl (ih _ (by omega) hf.1 h)
          · exact Or.inr (ih _ (by omega) hf.2 h)
      · rw [wv_ge C (zFlip z0 i) w (by rw [zFlip_length]; omega)] at ht
        cases ht

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
        change (E.erase m).card = k
        rw [Finset.card_erase_of_mem hmE]
        omega
      have hlt' : ∀ w ∈ E', (ch w).1 < w ∧ (ch w).2 < w :=
        fun w hw => hlt w (Finset.mem_of_mem_erase hw)
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
      have hinter_sub : E' ∩ E2 ⊆ E ∩ E2 :=
        Finset.inter_subset_inter (Finset.erase_subset m E) (Finset.Subset.refl E2)
      have hinter_le : (E' ∩ E2).card ≤ (E ∩ E2).card := Finset.card_le_card hinter_sub
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

def z0 : List Bool := quadInput (R 0)

def S0 : Finset ℕ := (Finset.range 26).filter fun i => z0.getD i false = false

lemma S0_card : S0.card = 19 := by
  decide

lemma lower_nOr (C : Circuit) (hAO : IsAO2 26 C)
    (hinc : ∀ (p l : Fin 13), p ∈ singerLines3 l → C.eval (pairInput p l) = true)
    (hquad : ∀ Q ∈ quadrangles singerLines3, C.eval (quadInput Q) = false) :
    18 ≤ nOr C := by
  classical
  have hz0_len : z0.length = 26 := quadInput_length (R 0)
  have hz0_false : wv C z0 C.output = false := hquad (R 0) (R_mem_quadrangles 0)
  have hS0_sub : S0 ⊆ sens C z0 S0 C.output := by
    intro i hiS
    have hiF := Finset.mem_filter.mp hiS
    have hilt : i < 26 := Finset.mem_range.mp hiF.1
    have hfalse_i : z0.getD i false = false := hiF.2
    have hex_pl : ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        ∀ k < 26, (pairInput p l).getD k false = true → (zFlip z0 i).getD k false = true := by
      by_cases hp : i < 13
      · let p : Fin 13 := ⟨i, hp⟩
        have hpnot : p ∉ R 0 := by
          intro hmem
          have hg := quadInput_getD_pt (R 0) p
          simp only [hmem, decide_true] at hg
          change z0.getD i false = true at hg
          rw [hfalse_i] at hg
          cases hg
        obtain ⟨l, hlm, hpl⟩ := R_miss_cover 0 p hpnot
        refine ⟨p, l, hpl, ?_⟩
        intro k hk ht
        rw [zFlip_getD z0 i k hk, Bool.or_eq_true]
        rcases pairInput_getD_true p l k hk ht with rfl | rfl
        · right; simp
        · left
          have hg := quadInput_getD_ln (R 0) l
          simp only [hlm, decide_true] at hg
          exact hg
      · let l : Fin 13 := ⟨i - 13, by omega⟩
        have hi_eq : i = 13 + l.val := by simp only [l]; omega
        have hlnot : l ∉ missLines singerLines3 (R 0) := by
          intro hmem
          have hg := quadInput_getD_ln (R 0) l
          simp only [hmem, decide_true] at hg
          change z0.getD (13 + l.val) false = true at hg
          rw [← hi_eq, hfalse_i] at hg
          cases hg
        have hndisj : ¬ Disjoint (singerLines3 l) (R 0) := by
          intro hd
          apply hlnot
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hd⟩
        obtain ⟨p, hpl, hpR⟩ := Finset.not_disjoint_iff.mp hndisj
        refine ⟨p, l, hpl, ?_⟩
        intro k hk ht
        rw [zFlip_getD z0 i k hk, Bool.or_eq_true]
        rcases pairInput_getD_true p l k hk ht with rfl | rfl
        · left
          have hg := quadInput_getD_pt (R 0) p
          simp only [hpR, decide_true] at hg
          exact hg
        · right; simp [hi_eq]
    obtain ⟨p, l, hpl, hle⟩ := hex_pl
    have hflip_true : wv C (zFlip z0 i) C.output = true :=
      wv_mono hAO (pairInput_length p l) (zFlip_length z0 i) hle C.output (hinc p l hpl)
    exact sens_sound C hAO z0 hz0_len S0 i hiS C.output hz0_false hflip_true
  have h19 : 19 ≤ (sens C z0 S0 C.output).card := by
    have := Finset.card_le_card hS0_sub
    rw [S0_card] at this
    exact this
  let allG := Finset.range C.gates.length
  let GO := allG.filter (fun j => (gateAt C j).op = GateOp.or)
  have hGO_eq : nOr C = GO.card := nOr_eq_card C
  let E := allG.image (fun j => 26 + j)
  let E2 := GO.image (fun j => 26 + j)
  have hEE2 : E ∩ E2 = E2 := by
    apply Finset.inter_eq_right.mpr
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hE2card : E2.card = GO.card := Finset.card_image_of_injective _ (fun _ _ h => by omega)
  let ch (w : ℕ) : ℕ × ℕ := ((gateAt C (w - 26)).inputs.getD 0 0, (gateAt C (w - 26)).inputs.getD 1 0)
  have hnot_in : ∀ w, w ∉ E → (sens C z0 S0 w).card ≤ 1 := by
    intro w hw
    by_cases h1 : w < 26
    · rw [sens_input C z0 S0 w h1]
      split_ifs <;> simp
    · by_cases h2 : w - 26 < C.gates.length
      · exfalso; apply hw
        exact Finset.mem_image.mpr ⟨w - 26, Finset.mem_range.mpr h2, by omega⟩
      · rw [sens_ge C z0 S0 w (by omega)]; simp
  have hexp := dag_expand_ub (sens C z0 S0) E E2 ch
    (fun w hw => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have hjlt := Finset.mem_range.mp hj
      simpa [ch] using gate_inputs_lt hAO hjlt)
    (fun w hw hw2 => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw2
      have hjf := Finset.mem_filter.mp hj
      rw [sens_or C hAO z0 S0 j (Finset.mem_range.mp hjf.1) hjf.2]
      simp [ch])
    (fun w hw hnot2 => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have hjlt := Finset.mem_range.mp hj
      have hmem : gateAt C j ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
      rcases hAO.1 (gateAt C j) hmem with hand | hor
      · rw [sens_and C hAO z0 S0 j hjlt hand]
        split_ifs
        · left; simp [ch]
        · right; left; simp [ch]
        · right; right; rfl
      · exfalso; apply hnot2
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hor⟩, rfl⟩)
    (fun w _ => ⟨by by_cases h : (ch w).1 ∈ E; exact Or.inl h; exact Or.inr (hnot_in _ h),
                 by by_cases h : (ch w).2 ∈ E; exact Or.inl h; exact Or.inr (hnot_in _ h)⟩)
    {C.output}
    (fun w _ => by by_cases h : w ∈ E; exact Or.inl h; exact Or.inr (hnot_in _ h))
  have hb : ({C.output} : Finset ℕ).biUnion (sens C z0 S0) = sens C z0 S0 C.output := by
    ext i; simp
  rw [hb, Finset.card_singleton, hEE2, hE2card] at hexp
  omega

lemma main_proof (C : Circuit) (hAO : IsAO2 26 C)
    (hinc : ∀ (p l : Fin 13), p ∈ singerLines3 l → C.eval (pairInput p l) = true)
    (hquad : ∀ Q ∈ quadrangles singerLines3, C.eval (quadInput Q) = false) :
    8 ≤ nAnd C ∧ 18 ≤ nOr C :=
  ⟨lower_nAnd C hAO hinc hquad, lower_nOr C hAO hinc hquad⟩

end PEqualNP.Outside.L_meta_5274

theorem PEqualNP.Outside.L_meta_5274 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
      (∀ (x3 x4 : Fin (13 : ℕ)),
        x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
        x1.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++
          List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) →
      (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
        x1.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) ++
          List.ofFn fun (x6 : Fin (13 : ℕ)) =>
            Decidable.decide (x6 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) →
      (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x1 :=
  PEqualNP.Outside.L_meta_5274.main_proof
