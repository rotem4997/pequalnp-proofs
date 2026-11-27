import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_640_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma runWires_nil (x : List Bool) : runWires [] x = x := rfl

lemma runWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    runWires (gs1 ++ gs2) x = runWires gs2 (runWires gs1 x) := by
  simp [runWires, List.foldl_append]

lemma runWires_singleton (g : Gate) (x : List Bool) :
    runWires [g] x = stepWire x g := rfl

lemma runWires_length (gs : List Gate) (x : List Bool) :
    (runWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [stepWire]
    omega

lemma getD_append_left_lt (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma runWires_getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (runWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).getD i false = x.getD i false
    have hlt : i < (stepWire x g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire x g) hlt]
    exact getD_append_left_lt x _ i hi

lemma wires_eq_runWires (C : Circuit) (x : List Bool) :
    C.wires x = runWires C.gates x := rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact runWires_length C.gates x

lemma wires_getD_input (C : Circuit) (x : Fin 7 → Bool) (i : Fin 7) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  rw [wires_eq_runWires, runWires_getD_prefix]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  · simp

lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval
        ((C.gates[k]).inputs.map fun a =>
          if a < x.length + k then (C.wires x).getD a false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  let pref := runWires (C.gates.take k) x
  have hpref_len : pref.length = x.length + k := by
    change (runWires (C.gates.take k) x).length = x.length + k
    rw [runWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hwires : C.wires x = runWires (C.gates.drop (k + 1)) (stepWire pref C.gates[k]) := by
    rw [wires_eq_runWires]
    conv_lhs => rw [hsplit]
    rw [runWires_append, runWires_append, runWires_singleton]
  have hstep_len : x.length + k < (stepWire pref C.gates[k]).length := by
    simp [stepWire, hpref_len]
  rw [hwires, runWires_getD_prefix _ _ _ hstep_len]
  have hstep_eq : (stepWire pref C.gates[k]).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => pref.getD a false) := by
    rw [← hpref_len]
    exact getD_append_singleton_eq pref _
  rw [hstep_eq]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < x.length + k
  · rw [if_pos ha]
    have ha' : a < (stepWire pref C.gates[k]).length := by omega
    rw [runWires_getD_prefix _ _ _ ha']
    have ha'' : a < pref.length := by omega
    exact (getD_append_left_lt pref _ a ha'').symm
  · rw [if_neg ha]
    exact getD_of_le pref a (by omega)

def linePts : Fin 7 → Finset (Fin 7)
  | 0 => {0, 1, 2}
  | 1 => {0, 3, 4}
  | 2 => {0, 5, 6}
  | 3 => {1, 3, 5}
  | 4 => {1, 4, 6}
  | 5 => {2, 3, 6}
  | 6 => {2, 4, 5}

def lineFn (i : Fin 7) (x : Fin 7 → Bool) : Bool :=
  decide (∃ p ∈ linePts i, x p = true)

def unitVec (p : Fin 7) : Fin 7 → Bool :=
  fun q => decide (q = p)

lemma lineFn_eq_explicit (x : Fin 7 → Bool) :
    lineFn 0 x = (x 0 || x 1 || x 2) ∧
    lineFn 1 x = (x 0 || x 3 || x 4) ∧
    lineFn 2 x = (x 0 || x 5 || x 6) ∧
    lineFn 3 x = (x 1 || x 3 || x 5) ∧
    lineFn 4 x = (x 1 || x 4 || x 6) ∧
    lineFn 5 x = (x 2 || x 3 || x 6) ∧
    lineFn 6 x = (x 2 || x 4 || x 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [lineFn, linePts, Bool.or_assoc]

lemma linePts_card (i : Fin 7) : (linePts i).card = 3 := by
  revert i; decide

lemma linePts_inter_card (i j : Fin 7) (hij : i ≠ j) :
    (linePts i ∩ linePts j).card = 1 := by
  revert i j; decide

lemma linePts_exists_diff (i j : Fin 7) (hij : i ≠ j) :
    ∃ p : Fin 7, p ∈ linePts i ∧ p ∉ linePts j := by
  revert i j; decide

lemma linePts_exists_inter (i j : Fin 7) :
    ∃ p : Fin 7, p ∈ linePts i ∧ p ∈ linePts j := by
  revert i j; decide

lemma lineFn_unit (i p : Fin 7) :
    lineFn i (unitVec p) = true ↔ p ∈ linePts i := by
  simp [lineFn, unitVec]

lemma lineFn_false_zero (i : Fin 7) :
    lineFn i (fun _ => false) = false := by
  simp [lineFn]

lemma lineFn_true_one (i : Fin 7) :
    lineFn i (fun _ => true) = true := by
  revert i; decide

lemma lineFn_zero_card (i : Fin 7) :
    (Finset.univ.filter (fun x : Fin 7 → Bool => lineFn i x = false)).card = 16 := by
  revert i; decide

lemma lineFn_zero_inter_card (i j : Fin 7) (hij : i ≠ j) :
    (Finset.univ.filter (fun x : Fin 7 → Bool => lineFn i x = false ∧ lineFn j x = false)).card = 4 := by
  revert i j; decide

def evalW (C : Circuit) (w : ℕ) (x : Fin 7 → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def IsPrivate (C : Circuit) (i : Fin 7) (w : ℕ) : Prop :=
  ((∀ x : Fin 7 → Bool, evalW C w x = true → lineFn i x = true) ∧
    2 ≤ (Finset.univ.filter (fun p : Fin 7 => evalW C w (unitVec p) = true)).card) ∨
  ((∀ x : Fin 7 → Bool, lineFn i x = true → evalW C w x = true) ∧
    8 ≤ (Finset.univ.filter (fun x : Fin 7 → Bool => evalW C w x = false)).card) ∨
  (∀ x : Fin 7 → Bool, evalW C w x = !(lineFn i x))

lemma isPrivate_self (C : Circuit) (i : Fin 7) (w : ℕ)
    (hw : ∀ x : Fin 7 → Bool, evalW C w x = lineFn i x) :
    IsPrivate C i w := by
  left
  refine ⟨fun x hx => by rwa [hw] at hx, ?_⟩
  have hfilt : Finset.univ.filter (fun p : Fin 7 => evalW C w (unitVec p) = true) = linePts i := by
    ext p
    simp [hw, lineFn_unit]
  rw [hfilt, linePts_card]
  omega

lemma isPrivate_ge_seven (C : Circuit) (i : Fin 7) (w : ℕ) (hp : IsPrivate C i w) :
    7 ≤ w := by
  by_contra hlt
  push_neg at hlt
  let pw : Fin 7 := ⟨w, hlt⟩
  have hev : ∀ x : Fin 7 → Bool, evalW C w x = x pw := fun x => wires_getD_input C x pw
  rcases hp with ⟨_, hcard⟩ | ⟨hle, _⟩ | hnot
  · have hsub : Finset.univ.filter (fun p : Fin 7 => evalW C w (unitVec p) = true) ⊆ {pw} := by
      intro p hp'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hev, unitVec,
        decide_eq_true_eq] at hp'
      simp [hp']
    have h1 := Finset.card_le_card hsub
    simp at h1
    omega
  · have hsub : linePts i ⊆ {pw} := by
      intro p hp'
      have h1 : lineFn i (unitVec p) = true := (lineFn_unit i p).mpr hp'
      have h2 := hle (unitVec p) h1
      rw [hev] at h2
      simp only [unitVec, decide_eq_true_eq] at h2
      simp [h2]
    have h1 := Finset.card_le_card hsub
    rw [linePts_card] at h1
    simp at h1
  · have h0 := hnot (fun _ => false)
    rw [hev, lineFn_false_zero] at h0
    cases h0

lemma isPrivate_lt_end (C : Circuit) (i : Fin 7) (w : ℕ) (hp : IsPrivate C i w) :
    w < 7 + C.size := by
  by_contra hge
  push_neg at hge
  have hev : ∀ x : Fin 7 → Bool, evalW C w x = false := by
    intro x
    apply getD_of_le
    rw [wires_length, List.length_ofFn]
    exact hge
  rcases hp with ⟨_, hcard⟩ | ⟨hle, _⟩ | hnot
  · have hemp : Finset.univ.filter (fun p : Fin 7 => evalW C w (unitVec p) = true) = ∅ := by
      ext p; simp [hev]
    rw [hemp] at hcard
    simp at hcard
  · have h1 := hle (fun _ => true) (lineFn_true_one i)
    rw [hev] at h1
    cases h1
  · have h0 := hnot (fun _ => false)
    rw [hev, lineFn_false_zero] at h0
    cases h0

lemma isPrivate_disjoint (C : Circuit) (i j : Fin 7) (w : ℕ)
    (hij : i ≠ j) (hi : IsPrivate C i w) (hj : IsPrivate C j w) : False := by
  rcases hi with ⟨hi_le, hi_card⟩ | ⟨hi_ge, hi_card⟩ | hi_not
  · rcases hj with ⟨hj_le, _⟩ | ⟨hj_ge, _⟩ | hj_not
    · have hsub : Finset.univ.filter (fun p : Fin 7 => evalW C w (unitVec p) = true) ⊆
          linePts i ∩ linePts j := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact Finset.mem_inter.mpr
          ⟨(lineFn_unit i p).mp (hi_le _ hp), (lineFn_unit j p).mp (hj_le _ hp)⟩
      have hc := Finset.card_le_card hsub
      rw [linePts_inter_card i j hij] at hc
      omega
    · rcases linePts_exists_diff j i hij.symm with ⟨p, hpj, hpi⟩
      have h1 : evalW C w (unitVec p) = true := hj_ge _ ((lineFn_unit j p).mpr hpj)
      have h2 : lineFn i (unitVec p) = true := hi_le _ h1
      exact hpi ((lineFn_unit i p).mp h2)
    · have h0 : evalW C w (fun _ => false) = true := by
        rw [hj_not, lineFn_false_zero]; rfl
      have h1 := hi_le _ h0
      rw [lineFn_false_zero] at h1
      cases h1
  · rcases hj with ⟨hj_le, _⟩ | ⟨hj_ge, _⟩ | hj_not
    · rcases linePts_exists_diff i j hij with ⟨p, hpi, hpj⟩
      have h1 : evalW C w (unitVec p) = true := hi_ge _ ((lineFn_unit i p).mpr hpi)
      have h2 : lineFn j (unitVec p) = true := hj_le _ h1
      exact hpj ((lineFn_unit j p).mp h2)
    · have hsub : Finset.univ.filter (fun x : Fin 7 → Bool => evalW C w x = false) ⊆
          Finset.univ.filter (fun x : Fin 7 → Bool => lineFn i x = false ∧ lineFn j x = false) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        constructor
        · cases hfi : lineFn i x
          · rfl
          · have := hi_ge x hfi; rw [hx] at this; cases this
        · cases hfj : lineFn j x
          · rfl
          · have := hj_ge x hfj; rw [hx] at this; cases this
      have hc := Finset.card_le_card hsub
      rw [lineFn_zero_inter_card i j hij] at hc
      omega
    · rcases linePts_exists_inter i j with ⟨p, hpi, hpj⟩
      have h1 : evalW C w (unitVec p) = true := hi_ge _ ((lineFn_unit i p).mpr hpi)
      have h2 : lineFn j (unitVec p) = true := (lineFn_unit j p).mpr hpj
      rw [hj_not, h2] at h1
      cases h1
  · rcases hj with ⟨hj_le, _⟩ | ⟨hj_ge, _⟩ | hj_not
    · have h0 : evalW C w (fun _ => false) = true := by
        rw [hi_not, lineFn_false_zero]; rfl
      have h1 := hj_le _ h0
      rw [lineFn_false_zero] at h1
      cases h1
    · rcases linePts_exists_inter i j with ⟨p, hpi, hpj⟩
      have h1 : evalW C w (unitVec p) = true := hj_ge _ ((lineFn_unit j p).mpr hpj)
      have h2 : lineFn i (unitVec p) = true := (lineFn_unit i p).mpr hpi
      rw [hi_not, h2] at h1
      cases h1
    · rcases linePts_exists_diff i j hij with ⟨p, hpi, hpj⟩
      have h1 := hi_not (unitVec p)
      have h2 := hj_not (unitVec p)
      have hfi : lineFn i (unitVec p) = true := (lineFn_unit i p).mpr hpi
      have hfj : lineFn j (unitVec p) = false := by
        cases h : lineFn j (unitVec p)
        · rfl
        · exact absurd ((lineFn_unit j p).mp h) hpj
      rw [hfi] at h1
      rw [hfj] at h2
      rw [h1] at h2
      cases h2

lemma exists_private_input (C : Circuit) (hfan : FanInTwo C) (i : Fin 7) (oi : ℕ)
    (hoi : ∀ x : Fin 7 → Bool, evalW C oi x = lineFn i x) :
    ∃ u : ℕ, u < oi ∧ IsPrivate C i u := by
  have hself : IsPrivate C i oi := isPrivate_self C i oi hoi
  have hge7 : 7 ≤ oi := isPrivate_ge_seven C i oi hself
  have hltend : oi < 7 + C.size := isPrivate_lt_end C i oi hself
  have hk : oi - 7 < C.gates.length := by
    change oi - 7 < C.size
    omega
  let g := C.gates[oi - 7]
  have hg_mem : g ∈ C.gates := List.getElem_mem hk
  have hfg := hfan g hg_mem
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hfg.1
  have hlen : g.inputs.length ≤ 2 := hfg.2
  have heq : ∀ x : Fin 7 → Bool,
      lineFn i x = g.op.eval (g.inputs.map fun a => if a < oi then evalW C a x else false) := by
    intro x
    rw [← hoi x]
    have h7k : (List.ofFn x).length + (oi - 7) = oi := by
      rw [List.length_ofFn]; omega
    have hgate := wires_getD_gate C (List.ofFn x) (oi - 7) hk
    rw [h7k] at hgate
    exact hgate
  let rd : ℕ → (Fin 7 → Bool) → Bool := fun a x => if a < oi then evalW C a x else false
  have hrd_eq : ∀ a, a < oi → ∀ x, rd a x = evalW C a x := fun a ha x => if_pos ha
  have hrd_false : ∀ a, ¬ a < oi → ∀ x, rd a x = false := fun a ha x => if_neg ha
  rcases hop with hand | hor | hnot
  · rcases h_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · have h0 := heq (fun _ => false)
      rw [hand, h_in, lineFn_false_zero] at h0
      simp [GateOp.eval] at h0
    · have ha_eq : ∀ x, lineFn i x = rd a x := by
        intro x; have h := heq x; rw [hand, h_in] at h; simpa [GateOp.eval, rd] using h
      by_cases ha : a < oi
      · refine ⟨a, ha, isPrivate_self C i a fun x => ?_⟩
        rw [← hrd_eq a ha x, ← ha_eq x]
      · have h1 := ha_eq (fun _ => true)
        rw [lineFn_true_one, hrd_false a ha] at h1
        cases h1
    · have hab_eq : ∀ x, lineFn i x = (rd a x && rd b x) := by
        intro x; have h := heq x; rw [hand, h_in] at h; simpa [GateOp.eval, rd] using h
      have ha : a < oi := by
        by_contra hna
        have h1 := hab_eq (fun _ => true)
        rw [lineFn_true_one, hrd_false a hna] at h1
        cases h1
      have hb : b < oi := by
        by_contra hnb
        have h1 := hab_eq (fun _ => true)
        rw [lineFn_true_one, hrd_false b hnb] at h1
        simp at h1
      have ha_ge : ∀ x, lineFn i x = true → evalW C a x = true := by
        intro x hx; have h := hab_eq x; rw [hx, hrd_eq a ha, hrd_eq b hb] at h
        exact (Bool.and_eq_true _ _).mp h.symm |>.1
      have hb_ge : ∀ x, lineFn i x = true → evalW C b x = true := by
        intro x hx; have h := hab_eq x; rw [hx, hrd_eq a ha, hrd_eq b hb] at h
        exact (Bool.and_eq_true _ _).mp h.symm |>.2
      have hcov : Finset.univ.filter (fun x : Fin 7 → Bool => lineFn i x = false) ⊆
          Finset.univ.filter (fun x : Fin 7 → Bool => evalW C a x = false) ∪
          Finset.univ.filter (fun x : Fin 7 → Bool => evalW C b x = false) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
        have h := hab_eq x
        rw [hx, hrd_eq a ha, hrd_eq b hb] at h
        exact (Bool.and_eq_false_iff).mp h.symm
      have hc := Finset.card_le_card hcov
      have hu := Finset.card_union_le
        (Finset.univ.filter (fun x : Fin 7 → Bool => evalW C a x = false))
        (Finset.univ.filter (fun x : Fin 7 → Bool => evalW C b x = false))
      rw [lineFn_zero_card i] at hc
      by_cases hca : 8 ≤ (Finset.univ.filter (fun x : Fin 7 → Bool => evalW C a x = false)).card
      · exact ⟨a, ha, Or.inr (Or.inl ⟨ha_ge, hca⟩)⟩
      · exact ⟨b, hb, Or.inr (Or.inl ⟨hb_ge, by omega⟩)⟩
    · rw [h_in] at hlen; simp at hlen
  · rcases h_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · have h1 := heq (fun _ => true)
      rw [hor, h_in, lineFn_true_one] at h1
      simp [GateOp.eval] at h1
    · have ha_eq : ∀ x, lineFn i x = rd a x := by
        intro x; have h := heq x; rw [hor, h_in] at h; simpa [GateOp.eval, rd] using h
      by_cases ha : a < oi
      · refine ⟨a, ha, isPrivate_self C i a fun x => ?_⟩
        rw [← hrd_eq a ha x, ← ha_eq x]
      · have h1 := ha_eq (fun _ => true)
        rw [lineFn_true_one, hrd_false a ha] at h1
        cases h1
    · have hab_eq : ∀ x, lineFn i x = (rd a x || rd b x) := by
        intro x; have h := heq x; rw [hor, h_in] at h; simpa [GateOp.eval, rd] using h
      have hcov : linePts i ⊆
          Finset.univ.filter (fun p : Fin 7 => rd a (unitVec p) = true) ∪
          Finset.univ.filter (fun p : Fin 7 => rd b (unitVec p) = true) := by
        intro p hp
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        have h := hab_eq (unitVec p)
        rw [(lineFn_unit i p).mpr hp] at h
        exact Bool.or_eq_true_iff.mp h.symm
      have hc := Finset.card_le_card hcov
      have hu := Finset.card_union_le
        (Finset.univ.filter (fun p : Fin 7 => rd a (unitVec p) = true))
        (Finset.univ.filter (fun p : Fin 7 => rd b (unitVec p) = true))
      rw [linePts_card i] at hc
      by_cases hca : 2 ≤ (Finset.univ.filter (fun p : Fin 7 => rd a (unitVec p) = true)).card
      · have ha : a < oi := by
          by_contra hna
          have hemp : Finset.univ.filter (fun p : Fin 7 => rd a (unitVec p) = true) = ∅ := by
            ext p; simp [hrd_false a hna]
          rw [hemp] at hca; simp at hca
        refine ⟨a, ha, Or.inl ⟨?_, ?_⟩⟩
        · intro x hx
          rw [hab_eq x, hrd_eq a ha x, hx]; rfl
        · simpa [hrd_eq a ha] using hca
      · have hcb : 2 ≤ (Finset.univ.filter (fun p : Fin 7 => rd b (unitVec p) = true)).card := by
          omega
        have hb : b < oi := by
          by_contra hnb
          have hemp : Finset.univ.filter (fun p : Fin 7 => rd b (unitVec p) = true) = ∅ := by
            ext p; simp [hrd_false b hnb]
          rw [hemp] at hcb; simp at hcb
        refine ⟨b, hb, Or.inl ⟨?_, ?_⟩⟩
        · intro x hx
          rw [hab_eq x, hrd_eq b hb x, hx]; simp
        · simpa [hrd_eq b hb] using hcb
    · rw [h_in] at hlen; simp at hlen
  · rcases h_in : g.inputs with _ | ⟨a, rest⟩
    · have h0 := heq (fun _ => false)
      rw [hnot, h_in, lineFn_false_zero] at h0
      simp [GateOp.eval] at h0
    · have ha_eq : ∀ x, lineFn i x = !(rd a x) := by
        intro x; have h := heq x; rw [hnot, h_in] at h; simpa [GateOp.eval, rd] using h
      have ha : a < oi := by
        by_contra hna
        have h0 := ha_eq (fun _ => false)
        rw [lineFn_false_zero, hrd_false a hna] at h0
        cases h0
      refine ⟨a, ha, Or.inr (Or.inr fun x => ?_)⟩
      have h := ha_eq x
      rw [hrd_eq a ha x] at h
      cases h1 : evalW C a x <;> rw [h1] at h <;> simp [h]

lemma lower_bound :
    ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 13 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool,
      (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧
      (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧
      (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧
      (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧
      (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧
      (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧
      (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) := by
  rintro ⟨C, hfan, hsize, o, ho_raw⟩
  have ho : ∀ (i : Fin 7) (x : Fin 7 → Bool), evalW C (o i) x = lineFn i x := by
    intro i x
    have h1 := ho_raw x
    have h2 := lineFn_eq_explicit x
    fin_cases i
    · exact h1.1.trans h2.1.symm
    · exact h1.2.1.trans h2.2.1.symm
    · exact h1.2.2.1.trans h2.2.2.1.symm
    · exact h1.2.2.2.1.trans h2.2.2.2.1.symm
    · exact h1.2.2.2.2.1.trans h2.2.2.2.2.1.symm
    · exact h1.2.2.2.2.2.1.trans h2.2.2.2.2.2.1.symm
    · exact h1.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.symm
  have hex : ∀ i : Fin 7, ∃ u : ℕ, u < o i ∧ IsPrivate C i u :=
    fun i => exists_private_input C hfan i (o i) (ho i)
  choose u hu_lt hu_priv using hex
  have ho_priv : ∀ i : Fin 7, IsPrivate C i (o i) :=
    fun i => isPrivate_self C i (o i) (ho i)
  have ho_inj : Function.Injective o := by
    intro i j hij
    by_contra hne
    exact isPrivate_disjoint C i j (o i) hne (ho_priv i) (hij ▸ ho_priv j)
  have hu_inj : Function.Injective u := by
    intro i j hij
    by_contra hne
    exact isPrivate_disjoint C i j (u i) hne (hu_priv i) (hij ▸ hu_priv j)
  have hu_ne_o : ∀ i j : Fin 7, u i ≠ o j := by
    intro i j heq
    by_cases hij : i = j
    · subst hij; exact Nat.ne_of_lt (hu_lt i) heq
    · exact isPrivate_disjoint C i j (u i) hij (hu_priv i) (heq ▸ ho_priv j)
  have hfO_inj : Function.Injective (fun i : Fin 7 => o i - 7) := by
    intro i j hij
    dsimp only at hij
    apply ho_inj
    have hi := isPrivate_ge_seven C i (o i) (ho_priv i)
    have hj := isPrivate_ge_seven C j (o j) (ho_priv j)
    omega
  have hfU_inj : Function.Injective (fun i : Fin 7 => u i - 7) := by
    intro i j hij
    dsimp only at hij
    apply hu_inj
    have hi := isPrivate_ge_seven C i (u i) (hu_priv i)
    have hj := isPrivate_ge_seven C j (u j) (hu_priv j)
    omega
  have hSO_card : (Finset.univ.image (fun i : Fin 7 => o i - 7)).card = 7 := by
    rw [Finset.card_image_of_injective _ hfO_inj]; simp
  have hSU_card : (Finset.univ.image (fun i : Fin 7 => u i - 7)).card = 7 := by
    rw [Finset.card_image_of_injective _ hfU_inj]; simp
  have hdisj : Disjoint (Finset.univ.image (fun i : Fin 7 => o i - 7))
      (Finset.univ.image (fun i : Fin 7 => u i - 7)) := by
    rw [Finset.disjoint_left]
    intro x hxO hxU
    rcases Finset.mem_image.mp hxO with ⟨j, _, rfl⟩
    rcases Finset.mem_image.mp hxU with ⟨i, _, hi⟩
    have h1 := isPrivate_ge_seven C j (o j) (ho_priv j)
    have h2 := isPrivate_ge_seven C i (u i) (hu_priv i)
    exact hu_ne_o i j (by omega)
  have hsub : Finset.univ.image (fun i : Fin 7 => o i - 7) ∪
      Finset.univ.image (fun i : Fin 7 => u i - 7) ⊆ Finset.range C.size := by
    intro x hx
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hx with hxO | hxU
    · rcases Finset.mem_image.mp hxO with ⟨i, _, rfl⟩
      have h1 := isPrivate_ge_seven C i (o i) (ho_priv i)
      have h2 := isPrivate_lt_end C i (o i) (ho_priv i)
      omega
    · rcases Finset.mem_image.mp hxU with ⟨i, _, rfl⟩
      have h1 := isPrivate_ge_seven C i (u i) (hu_priv i)
      have h2 := isPrivate_lt_end C i (u i) (hu_priv i)
      omega
  have htot := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hSO_card, hSU_card, Finset.card_range] at htot
  omega

def upperCircuit : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 2]⟩,
      ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [11, 6]⟩,
      ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [13, 5]⟩,
      ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [15, 6]⟩,
      ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [17, 6]⟩,
      ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [19, 5]⟩
    ]
    output := 8 }

def upperOut : Fin 7 → ℕ
  | 0 => 8
  | 1 => 10
  | 2 => 12
  | 3 => 14
  | 4 => 16
  | 5 => 18
  | 6 => 20

lemma upper_bound :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool,
      (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧
      (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧
      (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧
      (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧
      (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧
      (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧
      (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5) := by
  refine ⟨upperCircuit, ?_, ?_, upperOut, ?_⟩
  · intro g hg
    simp only [upperCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  · simp [upperCircuit, Circuit.size]
  · intro x
    have hof : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hof]
    simp [upperCircuit, upperOut, Circuit.wires, GateOp.eval]

theorem main :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) :=
  ⟨upper_bound, lower_bound⟩

end PEqualNP.Outside.L_meta_640_aux

theorem PEqualNP.Outside.L_meta_640 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) :=
  PEqualNP.Outside.L_meta_640_aux.main
