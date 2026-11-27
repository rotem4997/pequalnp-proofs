import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_738

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]

section C

variable (P L : ℕ) (C : Circuit)

def deg (i : ℕ) : ℕ := (C.lineDegrees (P + L) (Finset.Ico P (P + L))).getD i 0

def val (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD i false

lemma lineDegrees_eq : C.lineDegrees (P + L) (Finset.Ico P (P + L)) =
    fw (fun d g => g.lineDegree d) C.gates
      ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) := rfl

lemma wires_eq (z : List Bool) : C.wires z =
    fw (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates z := rfl

lemma deg_input (i : ℕ) (hi : i < P + L) : deg P L C i = if P ≤ i then 1 else 0 := by
  unfold deg
  rw [lineDegrees_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun d g => g.lineDegree d) C.gates
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0)
  rw [hr, getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma deg_point (i : ℕ) (hi : i < P) : deg P L C i = 0 := by
  rw [deg_input P L C i (by omega)]; simp; omega

lemma deg_line (i : ℕ) (hi : P ≤ i) (hi2 : i < P + L) : deg P L C i = 1 := by
  rw [deg_input P L C i hi2]; simp [hi]

lemma deg_ge (i : ℕ) (hi : P + L + C.gates.length ≤ i) : deg P L C i = 0 := by
  unfold deg
  apply List.getD_eq_default
  rw [lineDegrees_eq, fw_length]; simp; omega

lemma deg_gate_eq (j : ℕ) (hj : j < C.gates.length) :
    deg P L C (P + L + j) =
      C.gates[j].lineDegree ((C.lineDegrees (P + L) (Finset.Ico P (P + L))).take (P + L + j)) := by
  have h := fw_getD_gate (fun d g => g.lineDegree d) C.gates
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) j hj 0
  simp only [List.length_map, List.length_range] at h
  unfold deg
  rw [lineDegrees_eq, h]

lemma deg_gate_and (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    deg P L C (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0).sum := by
  rw [deg_gate_eq P L C j hj]
  unfold Gate.lineDegree
  rw [if_pos hop]
  simp only [getD_take']
  rfl

lemma deg_gate_or (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    deg P L C (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0).foldr max 0 := by
  rw [deg_gate_eq P L C j hj]
  unfold Gate.lineDegree
  rw [if_neg (by rw [hop]; exact fun h => GateOp.noConfusion h)]
  simp only [getD_take']
  rfl

lemma val_input (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : i < P + L) :
    val P L C x y i = (List.ofFn x ++ List.ofFn y).getD i false := by
  unfold val
  rw [wires_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x ++ List.ofFn y)
  rw [hr, getD_append_left' _ _ _ _ (by simp; omega)]

lemma val_point (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : i < P) :
    val P L C x y i = x ⟨i, hi⟩ := by
  rw [val_input P L C x y i (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; exact hi)]
  simp [hi]

lemma val_line (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : P ≤ i) (hi2 : i < P + L) :
    val P L C x y i = y ⟨i - P, by omega⟩ := by
  rw [val_input P L C x y i hi2]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; exact hi)]
  have h3 : i - (List.ofFn x).length < L := by simp; omega
  simp only [List.getElem?_ofFn, List.length_ofFn]
  simp [show i - P < L by omega]

lemma val_ge (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : P + L + C.gates.length ≤ i) :
    val P L C x y i = false := by
  unfold val
  apply List.getD_eq_default
  rw [wires_eq, fw_length]; simp; omega

lemma val_gate (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val P L C x y (P + L + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < P + L + j then val P L C x y i else false) := by
  have h := fw_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates
    (List.ofFn x ++ List.ofFn y) j hj false
  simp only [List.length_append, List.length_ofFn] at h
  unfold val
  rw [wires_eq, h]
  simp only [getD_take']

end C

lemma le_foldr_max (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma foldr_max_eq_zero (l : List ℕ) (h : l.foldr max 0 = 0) (a : ℕ) (ha : a ∈ l) : a = 0 := by
  have := le_foldr_max l a ha; omega

section Deg

variable (P L : ℕ) (C : Circuit)

lemma op_cases (hm : IsMonotoneCircuit C) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or :=
  hm _ (List.getElem_mem hj)

lemma deg_le_of_input (hm : IsMonotoneCircuit C) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hi : i ∈ C.gates[j].inputs) (hlt : i < P + L + j) :
    deg P L C i ≤ deg P L C (P + L + j) := by
  have hmem : deg P L C i ∈ (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0) :=
    List.mem_map.mpr ⟨i, hi, by simp [hlt]⟩
  rcases op_cases C hm j hj with hop | hop
  · rw [deg_gate_and P L C j hj hop]; exact List.le_sum_of_mem hmem
  · rw [deg_gate_or P L C j hj hop]; exact le_foldr_max _ _ hmem

abbrev Rel (P L : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C.gates.length, b1 = P + L + i1.val ∧ a1 ∈ (C.gates.get i1).inputs

lemma deg_le_of_rel (hm : IsMonotoneCircuit C) (a b : ℕ) (h : Rel P L C a b) :
    deg P L C a ≤ deg P L C b := by
  obtain ⟨hab, i, rfl, hmem⟩ := h
  exact deg_le_of_input P L C hm i.val i.isLt a hmem hab

lemma deg_le_of_reach (hm : IsMonotoneCircuit C) (a b : ℕ)
    (h : Relation.ReflTransGen (Rel P L C) a b) : deg P L C a ≤ deg P L C b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hr ih => exact le_trans ih (deg_le_of_rel P L C hm _ _ hr)

end Deg

section Phase1

variable (P L : ℕ) (C : Circuit)

def evf : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)

def dw (gs : List Gate) (z : List Bool) : List Bool := fw evf gs z

lemma dw_length (gs : List Gate) (z : List Bool) : (dw gs z).length = z.length + gs.length :=
  fw_length _ _ _

lemma dw_getD_append (gs r : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length + gs.length) :
    (dw (gs ++ r) z).getD i false = (dw gs z).getD i false := by
  unfold dw
  rw [fw_append]
  obtain ⟨t, ht⟩ := fw_prefix evf r (fw evf gs z)
  rw [ht, getD_append_left' _ _ _ _ (by rw [fw_length]; exact hi)]

lemma dw_getD_snoc (gs : List Gate) (g : Gate) (z : List Bool) :
    (dw (gs ++ [g]) z).getD (z.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (dw gs z).getD i false) := by
  unfold dw
  rw [fw_snoc]
  have hl := fw_length evf gs z
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hl]
  rfl

lemma dw_getD_input (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
    (dw gs z).getD i false = z.getD i false := by
  unfold dw
  obtain ⟨t, ht⟩ := fw_prefix evf gs z
  rw [ht, getD_append_left' _ _ _ _ hi]

lemma dw_getD_ge (gs : List Gate) (z : List Bool) (i : ℕ) (hi : z.length + gs.length ≤ i) :
    (dw gs z).getD i false = false := by
  apply List.getD_eq_default; rw [dw_length]; exact hi

lemma dw_point (gs : List Gate) (x : Fin P → Bool) (i : ℕ) (hi : i < P) :
    (dw gs (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [dw_getD_input _ _ _ (by simp; exact hi)]
  simp [List.getD_eq_getElem?_getD, hi]

def rank (k : ℕ) : ℕ := ((Finset.range k).filter fun j => deg P L C (P + L + j) = 0).card

lemma rank_succ (k : ℕ) : rank P L C (k + 1) = rank P L C k + if deg P L C (P + L + k) = 0 then 1 else 0 := by
  unfold rank
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma rank_mono (j k : ℕ) (h : j ≤ k) : rank P L C j ≤ rank P L C k := by
  unfold rank
  apply Finset.card_le_card
  intro a; simp; omega

lemma rank_lt (j k : ℕ) (h : j < k) (hd : deg P L C (P + L + j) = 0) : rank P L C j < rank P L C k := by
  have h1 := rank_succ P L C j
  rw [if_pos hd] at h1
  have h2 := rank_mono P L C (j + 1) k h
  omega

def dflt : Gate := ⟨GateOp.or, []⟩

def gt (j : ℕ) : Gate := C.gates.getD j dflt

lemma gt_eq (j : ℕ) (hj : j < C.gates.length) : gt C j = C.gates[j] := by
  simp [gt, List.getD_eq_getElem?_getD, hj]

def sig (j i : ℕ) : ℕ :=
  if i < P then i else if i < P + L + j then P + rank P L C (i - (P + L)) else P + rank P L C j

def copyGate (j : ℕ) : Gate := ⟨(gt C j).op, (gt C j).inputs.map (sig P L C j)⟩

def phase1 (k : ℕ) : List Gate :=
  (List.range k).filterMap fun j => if deg P L C (P + L + j) = 0 then some (copyGate P L C j) else none

lemma phase1_succ (k : ℕ) : phase1 P L C (k + 1) =
    phase1 P L C k ++ (if deg P L C (P + L + k) = 0 then [copyGate P L C k] else []) := by
  unfold phase1
  rw [List.range_succ, List.filterMap_append]
  split_ifs with h <;> simp [h]

lemma phase1_length (k : ℕ) : (phase1 P L C k).length = rank P L C k := by
  induction k with
  | zero => simp [phase1, rank]
  | succ k ih =>
    rw [phase1_succ, rank_succ, List.length_append, ih]
    split_ifs <;> simp

lemma phase1_val (hm : IsMonotoneCircuit C) (x : Fin P → Bool) (y : Fin L → Bool) (k : ℕ)
    (hk : k ≤ C.gates.length) (j : ℕ) (hj : j < k) (hd : deg P L C (P + L + j) = 0) :
    (dw (phase1 P L C k) (List.ofFn x)).getD (P + rank P L C j) false = val P L C x y (P + L + j) := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [phase1_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [dw_getD_append _ _ _ _ (by rw [phase1_length]; simp; exact rank_lt P L C j k hj hd)]
      exact ih (by omega) j hj hd
    · subst hj
      rw [if_pos hd]
      have hl : (List.ofFn x).length + (phase1 P L C j).length = P + rank P L C j := by
        rw [phase1_length]; simp
      rw [← hl, dw_getD_snoc, val_gate P L C x y j (by omega)]
      unfold copyGate
      rw [gt_eq C j (by omega)]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp]
      unfold sig
      by_cases h1 : i < P
      · rw [if_pos h1, if_pos (show i < P + L + j by omega), dw_point P _ x i h1, val_point P L C x y i h1]
      · by_cases h2 : i < P + L + j
        · have hdi : deg P L C i = 0 := by
            have := deg_le_of_input P L C hm j (by omega) i hi h2; omega
          have hiL : P + L ≤ i := by
            by_contra hc
            have := deg_line P L C i (by omega) (by omega); omega
          simp only [h1, h2, if_false, if_true]
          have hk' := ih (by omega) (i - (P + L)) (by omega) (by rw [show P + L + (i - (P + L)) = i by omega]; exact hdi)
          rw [show P + L + (i - (P + L)) = i by omega] at hk'
          exact hk'
        · simp only [h1, h2, if_false]
          rw [dw_getD_ge]
          rw [phase1_length]; simp

end Phase1

section Phase2

variable (P L : ℕ) (C : Circuit)


def vEv (gs : List Gate) (x : Fin P → Bool) : Option ℕ → Bool
  | none => true
  | some i => (dw gs (List.ofFn x)).getD i false

def aEv (gs : List Gate) (x : Fin P → Bool) : Option (Option ℕ) → Bool
  | none => false
  | some c => vEv P gs x c

def Valid (gs : List Gate) (c : Option ℕ) : Prop := ∀ b, c = some b → b < P + gs.length

def push (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) : (List Gate × (ℕ → Option (Option ℕ))) :=
  match s.2 v, c with
  | none, _ => (s.1, Function.update s.2 v (some c))
  | some none, _ => s
  | some (some _), none => (s.1, Function.update s.2 v (some none))
  | some (some a), some b =>
    (s.1 ++ [⟨GateOp.or, [a, b]⟩], Function.update s.2 v (some (some (P + s.1.length))))

def GoodGates (r : List Gate) : Prop :=
  ∀ g ∈ r, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma goodGates_append (a b : List Gate) (ha : GoodGates a) (hb : GoodGates b) : GoodGates (a ++ b) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ha g h
  · exact hb g h

lemma vEv_append (gs r : List Gate) (x : Fin P → Bool) (c : Option ℕ) (hc : Valid P gs c) :
    vEv P (gs ++ r) x c = vEv P gs x c := by
  cases c with
  | none => rfl
  | some b =>
    simp only [vEv]
    exact dw_getD_append gs r _ b (by simp; exact hc b rfl)

lemma aEv_append (gs r : List Gate) (x : Fin P → Bool) (a : Option (Option ℕ))
    (ha : ∀ c, a = some c → Valid P gs c) :
    aEv P (gs ++ r) x a = aEv P gs x a := by
  cases a with
  | none => rfl
  | some c => exact vEv_append P gs r x c (ha c rfl)

lemma valid_append (gs r : List Gate) (c : Option ℕ) (hc : Valid P gs c) : Valid P (gs ++ r) c := by
  intro b hb; have := hc b hb; simp; omega

lemma push_fst (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) :
    ∃ r, (push P s v c).1 = s.1 ++ r ∧ r.length ≤ (if s.2 v = none then 0 else 1) ∧ GoodGates r := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp only [h, reduceCtorEq, ↓reduceIte]
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[⟨GateOp.or, [a, b]⟩], by simp, by simp, by simp [GoodGates]⟩

lemma push_snd_other (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (u : ℕ) (hu : u ≠ v) :
    (push P s v c).2 u = s.2 u := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp [Function.update_of_ne hu]

lemma push_snd_self (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) : (push P s v c).2 v ≠ none := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp [h]

lemma push_keep (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (u : ℕ) (hu : s.2 u ≠ none) :
    (push P s v c).2 u ≠ none := by
  by_cases h : u = v
  · subst h; exact push_snd_self P s u c
  · rw [push_snd_other P s v c u h]; exact hu

def RefsOK (s : (List Gate × (ℕ → Option (Option ℕ)))) : Prop := ∀ v c, s.2 v = some c → Valid P s.1 c

lemma valid_none (gs : List Gate) : Valid P gs none := by
  intro b hb; simp at hb

lemma push_refs (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (hs : RefsOK P s) (hc : Valid P s.1 c) :
    RefsOK P (push P s v c) := by
  intro u d hd
  by_cases huv : u = v
  · subst huv
    unfold push at hd ⊢
    rcases h : s.2 u with _ | _ | a <;> rcases c with _ | b <;>
      simp only [h, Function.update_self, Option.some.injEq] at hd ⊢
    · subst hd; exact valid_none P _
    · subst hd; exact hc
    · exact hs u _ (by rw [h, hd])
    · exact hs u _ (by rw [h, hd])
    · subst hd; exact valid_none P _
    · subst hd; intro b' hb'; simp at hb' ⊢; omega
  · obtain ⟨r, hr, -, -⟩ := push_fst P s v c
    rw [push_snd_other P s v c u huv] at hd
    rw [hr]
    exact valid_append P _ _ _ (hs u d hd)

lemma push_sem (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (hs : RefsOK P s) (hc : Valid P s.1 c)
    (x : Fin P → Bool) (u : ℕ) :
    aEv P (push P s v c).1 x ((push P s v c).2 u) =
      if u = v then (aEv P s.1 x (s.2 v) || vEv P s.1 x c) else aEv P s.1 x (s.2 u) := by
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl]
    unfold push
    rcases h : s.2 u with _ | _ | a <;> rcases c with _ | b <;>
      simp only [h, Function.update_self]
    · simp [aEv, vEv]
    · simp [aEv]
    · simp [aEv, vEv]
    · simp [aEv, vEv]
    · simp [aEv, vEv]
    · have ha := hs u (some a) h a rfl
      have hb := hc b rfl
      have hl : (List.ofFn x).length + s.1.length = P + s.1.length := by simp
      simp only [aEv, vEv]
      rw [← hl, dw_getD_snoc]
      simp only [List.map_cons, List.map_nil]
      simp [GateOp.eval]
  · obtain ⟨r, hr, -, -⟩ := push_fst P s v c
    rw [if_neg huv, push_snd_other P s v c u huv, hr]
    exact aEv_append P _ _ _ _ (fun d hd => hs u d hd)

lemma push_count (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (K : ℕ) :
    (push P s v c).1.length + ((Finset.range K).filter fun u => (push P s v c).2 u ≠ none).card ≤
      s.1.length + ((Finset.range K).filter fun u => s.2 u ≠ none).card + 1 := by
  obtain ⟨r, hr, hrl, -⟩ := push_fst P s v c
  rw [hr, List.length_append]
  by_cases h : s.2 v = none
  · rw [if_pos h] at hrl
    have hsub : ((Finset.range K).filter fun u => (push P s v c).2 u ≠ none) ⊆
        insert v ((Finset.range K).filter fun u => s.2 u ≠ none) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert] at hu ⊢
      by_cases huv : u = v
      · left; exact huv
      · right; rw [push_snd_other P s v c u huv] at hu; exact hu
    have := Finset.card_le_card hsub
    have := Finset.card_insert_le v ((Finset.range K).filter fun u => s.2 u ≠ none)
    omega
  · rw [if_neg h] at hrl
    have hsub : ((Finset.range K).filter fun u => (push P s v c).2 u ≠ none) ⊆
        ((Finset.range K).filter fun u => s.2 u ≠ none) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
      by_cases huv : u = v
      · subst huv; exact ⟨hu.1, h⟩
      · rw [push_snd_other P s v c u huv] at hu; exact hu
    have := Finset.card_le_card hsub
    omega

end Phase2

section Step

variable (P L : ℕ) (C : Circuit)

def Pre (s : (List Gate × (ℕ → Option (Option ℕ)))) : Prop := ∃ r, s.1 = phase1 P L C C.gates.length ++ r

lemma pre_append (s : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (h : Pre P L C s) (a : ℕ → Option (Option ℕ)) :
    Pre P L C (s.1 ++ r, a) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q ++ r, by simp [hq]⟩

lemma sig_valid (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Pre P L C s) (j : ℕ) (hj : j < C.gates.length) (f : ℕ)
    (hf : f < P + L + j) (hd : deg P L C f = 0) : sig P L C j f < P + s.1.length := by
  obtain ⟨q, hq⟩ := hs
  rw [hq, List.length_append, phase1_length]
  unfold sig
  by_cases h1 : f < P
  · rw [if_pos h1]; omega
  · rw [if_neg h1, if_pos hf]
    have hiL : P + L ≤ f := by
      by_contra hc
      have := deg_line P L C f (by omega) (by omega); omega
    have := rank_lt P L C (f - (P + L)) C.gates.length (by omega)
      (by rw [show P + L + (f - (P + L)) = f by omega]; exact hd)
    omega

lemma sig_val (hm : IsMonotoneCircuit C) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Pre P L C s) (j : ℕ) (hj : j < C.gates.length)
    (f : ℕ) (hf : f < P + L + j) (hd : deg P L C f = 0) (x : Fin P → Bool) (y : Fin L → Bool) :
    (dw s.1 (List.ofFn x)).getD (sig P L C j f) false = val P L C x y f := by
  have hv := sig_valid P L C s hs j hj f hf hd
  obtain ⟨q, hq⟩ := hs
  unfold sig at hv ⊢
  by_cases h1 : f < P
  · rw [if_pos h1, dw_point P _ x f h1, val_point P L C x y f h1]
  · rw [if_neg h1, if_pos hf] at hv ⊢
    have hiL : P + L ≤ f := by
      by_contra hc
      have := deg_line P L C f (by omega) (by omega); omega
    have hr := rank_lt P L C (f - (P + L)) C.gates.length (by omega)
      (by rw [show P + L + (f - (P + L)) = f by omega]; exact hd)
    rw [hq, dw_getD_append _ _ _ _ (by simp [phase1_length]; exact hr)]
    rw [phase1_val P L C hm x y C.gates.length le_rfl (f - (P + L)) (by omega)
      (by rw [show P + L + (f - (P + L)) = f by omega]; exact hd)]
    rw [show P + L + (f - (P + L)) = f by omega]

lemma val_indep (hm : IsMonotoneCircuit C) (x : Fin P → Bool) (y y' : Fin L → Bool) (i : ℕ)
    (hd : deg P L C i = 0) : val P L C x y i = val P L C x y' i := by
  by_cases h1 : i < P
  · rw [val_point P L C x y i h1, val_point P L C x y' i h1]
  · by_cases h2 : i < P + L
    · have := deg_line P L C i (by omega) h2; omega
    · by_cases h3 : i < P + L + C.gates.length
      · have e := fun yy => phase1_val P L C hm x yy C.gates.length le_rfl (i - (P + L)) (by omega)
          (by rw [show P + L + (i - (P + L)) = i by omega]; exact hd)
        rw [show P + L + (i - (P + L)) = i by omega] at e
        rw [← e y, ← e y']
      · rw [val_ge P L C x y i (by omega), val_ge P L C x y' i (by omega)]

def andTerm (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (c : Option ℕ) (f : ℕ) : (List Gate × (ℕ → Option (Option ℕ))) × Option ℕ :=
  if f < P + L + j then
    match c with
    | none => (s, some (sig P L C j f))
    | some cw => ((s.1 ++ [⟨GateOp.and, [cw, sig P L C j f]⟩], s.2), some (P + s.1.length))
  else ((s.1 ++ [⟨GateOp.or, []⟩], s.2), some (P + s.1.length))

lemma andTerm_fst (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (c : Option ℕ) (f : ℕ) :
    ∃ r, (andTerm P L C j s c f).1.1 = s.1 ++ r ∧ r.length ≤ 1 ∧ GoodGates r ∧
      (andTerm P L C j s c f).1.2 = s.2 := by
  unfold andTerm
  split_ifs
  · rcases c with _ | cw
    · exact ⟨[], by simp, by simp, by simp [GoodGates], rfl⟩
    · exact ⟨_, rfl, by simp, by simp [GoodGates], rfl⟩
  · exact ⟨_, rfl, by simp, by simp [GoodGates], rfl⟩

lemma andTerm_valid (j : ℕ) (hj : j < C.gates.length) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Pre P L C s) (c : Option ℕ)
    (hc : Valid P s.1 c) (f : ℕ) (hf : f < P + L + j → deg P L C f = 0) :
    Valid P (andTerm P L C j s c f).1.1 (andTerm P L C j s c f).2 := by
  unfold andTerm
  split_ifs with h
  · rcases c with _ | cw
    · intro b hb; simp at hb; subst hb; exact sig_valid P L C s hs j hj f h (hf h)
    · intro b hb; simp at hb ⊢; omega
  · intro b hb; simp at hb ⊢; omega

lemma andTerm_val (hm : IsMonotoneCircuit C) (j : ℕ) (hj : j < C.gates.length) (s : (List Gate × (ℕ → Option (Option ℕ))))
    (hs : Pre P L C s) (c : Option ℕ) (hc : Valid P s.1 c) (f : ℕ)
    (hf : f < P + L + j → deg P L C f = 0) (x : Fin P → Bool) (y : Fin L → Bool) :
    vEv P (andTerm P L C j s c f).1.1 x (andTerm P L C j s c f).2 =
      (vEv P s.1 x c && if f < P + L + j then val P L C x y f else false) := by
  have hl : (List.ofFn x).length + s.1.length = P + s.1.length := by simp
  unfold andTerm
  split_ifs with h
  · rcases c with _ | cw
    · simp only [vEv, Bool.true_and]
      exact sig_val P L C hm s hs j hj f h (hf h) x y
    · simp only [vEv]
      rw [← hl, dw_getD_snoc]
      simp only [List.map_cons, List.map_nil]
      rw [sig_val P L C hm s hs j hj f h (hf h) x y]
      simp [GateOp.eval]
  · simp only [vEv, Bool.and_false]
    rw [← hl, dw_getD_snoc]
    simp [GateOp.eval]

def orFold (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) : (List Gate × (ℕ → Option (Option ℕ))) :=
  l.foldl (fun s i => if i < P + L + j ∧ deg P L C i = 1 then push P s i c else s) s

lemma orFold_cons (j : ℕ) (c : Option ℕ) (i : ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) :
    orFold P L C j c (i :: l) s =
      orFold P L C j c l (if i < P + L + j ∧ deg P L C i = 1 then push P s i c else s) := rfl

lemma orFold_fst (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) :
    ∃ r, (orFold P L C j c l s).1 = s.1 ++ r ∧ r.length ≤ l.length ∧ GoodGates r := by
  induction l generalizing s with
  | nil => exact ⟨[], by simp [orFold], by simp, by simp [GoodGates]⟩
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · obtain ⟨r1, h1, l1, g1⟩ := push_fst P s i c
      obtain ⟨r2, h2, l2, g2⟩ := ih (push P s i c)
      refine ⟨r1 ++ r2, by rw [h2, h1]; simp, ?_, goodGates_append _ _ g1 g2⟩
      simp; split_ifs at l1 <;> omega
    · obtain ⟨r2, h2, l2, g2⟩ := ih s
      exact ⟨r2, h2, by simp; omega, g2⟩

lemma orFold_keep (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (u : ℕ) (hu : s.2 u ≠ none) :
    (orFold P L C j c l s).2 u ≠ none := by
  induction l generalizing s with
  | nil => exact hu
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · exact ih _ (push_keep P s i c u hu)
    · exact ih _ hu

lemma orFold_hit (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (u : ℕ) (hu : u ∈ l)
    (hy : u < P + L + j ∧ deg P L C u = 1) : (orFold P L C j c l s).2 u ≠ none := by
  induction l generalizing s with
  | nil => simp at hu
  | cons i l ih =>
    rw [orFold_cons]
    rcases List.mem_cons.mp hu with h | h
    · subst h
      rw [if_pos hy]
      exact orFold_keep P L C j c l _ u (push_snd_self P s u c)
    · exact ih _ h

lemma orFold_refs (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : RefsOK P s)
    (hc : Valid P s.1 c) : RefsOK P (orFold P L C j c l s) ∧ Valid P (orFold P L C j c l s).1 c := by
  induction l generalizing s with
  | nil => exact ⟨hs, hc⟩
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · apply ih
      · exact push_refs P s i c hs hc
      · obtain ⟨r, hr, -, -⟩ := push_fst P s i c
        rw [hr]; exact valid_append P _ _ _ hc
    · exact ih s hs hc

lemma orFold_count (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (K : ℕ) :
    (orFold P L C j c l s).1.length + ((Finset.range K).filter fun u => (orFold P L C j c l s).2 u ≠ none).card ≤
      s.1.length + ((Finset.range K).filter fun u => s.2 u ≠ none).card + l.length := by
  induction l generalizing s with
  | nil => exact Nat.le_add_right _ _
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · have := ih (push P s i c)
      have := push_count P s i c K
      rw [List.length_cons]; omega
    · have := ih s
      rw [List.length_cons]; omega

lemma orFold_sem (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : RefsOK P s)
    (hc : Valid P s.1 c) (x : Fin P → Bool) (u : ℕ) :
    aEv P (orFold P L C j c l s).1 x ((orFold P L C j c l s).2 u) =
      (aEv P s.1 x (s.2 u) || (vEv P s.1 x c && decide (u ∈ l ∧ u < P + L + j ∧ deg P L C u = 1))) := by
  induction l generalizing s with
  | nil => simp [orFold]
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs with hy
    · have hr := push_refs P s i c hs hc
      obtain ⟨r, hrr, -, -⟩ := push_fst P s i c
      have hc' : Valid P (push P s i c).1 c := by rw [hrr]; exact valid_append P _ _ _ hc
      rw [ih _ hr hc', push_sem P s i c hs hc x u, hrr, vEv_append P _ _ _ _ hc]
      by_cases hui : u = i
      · subst hui; simp only [if_true]
        cases aEv P s.1 x (s.2 u) <;> cases vEv P s.1 x c <;> simp [hy]
      · rw [if_neg hui]; simp [hui]
    · rw [ih s hs hc]
      by_cases hui : u = i
      · subst hui; simp [hy]
      · simp [hui]

end Step

section Gate

variable (P L : ℕ) (C : Circuit)

def stepGate (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) : (List Gate × (ℕ → Option (Option ℕ))) :=
  if deg P L C (P + L + j) = 1 then
    match s.2 (P + L + j) with
    | none => s
    | some c =>
      match (gt C j).op, (gt C j).inputs with
      | GateOp.or, l => orFold P L C j c l s
      | GateOp.and, [a] => if a < P + L + j ∧ deg P L C a = 1 then push P s a c else s
      | GateOp.and, [a, b] =>
          if a < P + L + j ∧ deg P L C a = 1 then
            push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
          else if b < P + L + j ∧ deg P L C b = 1 then
            push P (andTerm P L C j s c a).1 b (andTerm P L C j s c a).2
          else s
      | _, _ => s
  else s

lemma stepGate_id (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (h : deg P L C (P + L + j) ≠ 1 ∨ s.2 (P + L + j) = none) :
    stepGate P L C j s = s := by
  unfold stepGate
  rcases h with h | h
  · rw [if_neg h]
  · split_ifs
    · rw [h]
    · rfl

lemma stepGate_shape (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < C.gates.length) (s : (List Gate × (ℕ → Option (Option ℕ)))) (c : Option ℕ)
    (hd : deg P L C (P + L + j) = 1) (hc : s.2 (P + L + j) = some c) :
    (C.gates[j].op = GateOp.or ∧ stepGate P L C j s = orFold P L C j c C.gates[j].inputs s) ∨
    (∃ a, C.gates[j].op = GateOp.and ∧ C.gates[j].inputs = [a] ∧ a < P + L + j ∧ deg P L C a = 1 ∧
      stepGate P L C j s = push P s a c) ∨
    (∃ a b, C.gates[j].op = GateOp.and ∧ C.gates[j].inputs = [a, b] ∧ a < P + L + j ∧ deg P L C a = 1 ∧
      (b < P + L + j → deg P L C b = 0) ∧
      stepGate P L C j s = push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2) ∨
    (∃ a b, C.gates[j].op = GateOp.and ∧ C.gates[j].inputs = [b, a] ∧ a < P + L + j ∧ deg P L C a = 1 ∧
      (b < P + L + j → deg P L C b = 0) ∧
      stepGate P L C j s = push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2) := by
  have hfj := hfan _ (List.getElem_mem hj)
  rcases op_cases C hm j hj with hop | hop
  · have hdeg := deg_gate_and P L C j hj hop
    have hst : stepGate P L C j s = match GateOp.and, C.gates[j].inputs with
      | GateOp.or, l => orFold P L C j c l s
      | GateOp.and, [a] => if a < P + L + j ∧ deg P L C a = 1 then push P s a c else s
      | GateOp.and, [a, b] =>
          if a < P + L + j ∧ deg P L C a = 1 then
            push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
          else if b < P + L + j ∧ deg P L C b = 1 then
            push P (andTerm P L C j s c a).1 b (andTerm P L C j s c a).2
          else s
      | _, _ => s := by
      unfold stepGate
      rw [if_pos hd, hc, gt_eq C j hj, hop]
    rcases hl : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨e, rest⟩⟩⟩
    · rw [hl] at hdeg; simp at hdeg; omega
    · rw [hl] at hdeg hst
      simp at hdeg
      have ha : a < P + L + j ∧ deg P L C a = 1 := by
        by_cases h : a < P + L + j
        · rw [if_pos h] at hdeg; exact ⟨h, by omega⟩
        · rw [if_neg h] at hdeg; omega
      right; left
      refine ⟨a, hop, rfl, ha.1, ha.2, ?_⟩
      rw [hst]; simp only []; rw [if_pos ha]
    · rw [hl] at hdeg hst
      simp at hdeg
      by_cases ha : a < P + L + j ∧ deg P L C a = 1
      · right; right; left
        refine ⟨a, b, hop, rfl, ha.1, ha.2, ?_, ?_⟩
        · intro hb; rw [if_pos ha.1, if_pos hb] at hdeg; omega
        · rw [hst]; simp only []; rw [if_pos ha]
      · have hb : b < P + L + j ∧ deg P L C b = 1 := by
          by_cases h1 : a < P + L + j
          · rw [if_pos h1] at hdeg
            by_cases h2 : b < P + L + j
            · rw [if_pos h2] at hdeg
              have : deg P L C a ≠ 1 := fun h => ha ⟨h1, h⟩
              have h3 : deg P L C a = 0 := by omega
              exact ⟨h2, by omega⟩
            · rw [if_neg h2] at hdeg; exact absurd ⟨h1, by omega⟩ ha
          · rw [if_neg h1] at hdeg
            by_cases h2 : b < P + L + j
            · rw [if_pos h2] at hdeg; exact ⟨h2, by omega⟩
            · rw [if_neg h2] at hdeg; omega
        right; right; right
        refine ⟨b, a, hop, rfl, hb.1, hb.2, ?_, ?_⟩
        · intro ha'; rw [if_pos ha', if_pos hb.1] at hdeg; omega
        · rw [hst]; simp only []; rw [if_neg ha, if_pos hb]
    · rw [hl] at hfj; simp at hfj
  · left
    refine ⟨hop, ?_⟩
    unfold stepGate
    rw [if_pos hd, hc, gt_eq C j hj, hop]

end Gate

section Main

variable (P L : ℕ) (C : Circuit)

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (hfg : ∀ a ∈ l, f a = true → g a = true) (h : op.eval (l.map f) = true) :
    op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h ⊢
    rintro _ ⟨a, ha, rfl⟩
    exact hfg a ha (h _ ⟨a, ha, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, h2⟩ := h
    exact ⟨_, ⟨a, ha, rfl⟩, hfg a ha h2⟩

lemma val_mono (hm : IsMonotoneCircuit C) (x : Fin P → Bool) (y y' : Fin L → Bool)
    (hy : ∀ u, y u = true → y' u = true) (i : ℕ) (h : val P L C x y i = true) :
    val P L C x y' i = true := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < P
    · rw [val_point P L C x y i h1] at h; rw [val_point P L C x y' i h1]; exact h
    · by_cases h2 : i < P + L
      · rw [val_line P L C x y i (by omega) h2] at h; rw [val_line P L C x y' i (by omega) h2]
        exact hy _ h
      · by_cases h3 : i < P + L + C.gates.length
        · have e : i = P + L + (i - (P + L)) := by omega
          rw [e, val_gate P L C x y _ (by omega)] at h
          rw [e, val_gate P L C x y' _ (by omega)]
          refine eval_mono _ (op_cases C hm _ (by omega)) _ _ _ ?_ h
          intro a _ ha
          by_cases hai : a < P + L + (i - (P + L))
          · rw [if_pos hai] at ha ⊢; exact ih a (by omega) ha
          · rw [if_neg hai] at ha; exact absurd ha (by simp)
        · rw [val_ge P L C x y i (by omega)] at h; exact absurd h (by simp)

lemma phase1_good (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (k : ℕ)
    (hk : k ≤ C.gates.length) : GoodGates (phase1 P L C k) := by
  induction k with
  | zero => simp [phase1, GoodGates]
  | succ k ih =>
    rw [phase1_succ]
    apply goodGates_append _ _ (ih (by omega))
    split_ifs
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      unfold copyGate
      rw [gt_eq C k (by omega)]
      exact ⟨op_cases C hm k (by omega), by simp; exact hfan _ (List.getElem_mem (by omega))⟩
    · simp [GoodGates]

def init : (List Gate × (ℕ → Option (Option ℕ))) := (phase1 P L C C.gates.length,
  fun v => if v = C.output ∧ deg P L C v = 1 ∧ v < P + L + C.gates.length then some none else none)

def S : ℕ → (List Gate × (ℕ → Option (Option ℕ)))
  | 0 => init P L C
  | m + 1 => stepGate P L C (C.gates.length - 1 - m) (S m)

def Yc (m : ℕ) : ℕ :=
  ((Finset.range C.gates.length).filter fun j => C.gates.length - m ≤ j ∧ deg P L C (P + L + j) = 1).card

def F (s : (List Gate × (ℕ → Option (Option ℕ)))) (K : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) : Prop :=
  ∃ v < K, deg P L C v = 1 ∧ aEv P s.1 x (s.2 v) = true ∧ val P L C x y v = true

def Cnt (s : (List Gate × (ℕ → Option (Option ℕ)))) (K : ℕ) : ℕ := ((Finset.range K).filter fun u => s.2 u ≠ none).card

def Inv (m : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) : Prop :=
  Pre P L C s ∧ RefsOK P s ∧ GoodGates s.1 ∧
  s.1.length + Cnt s (P + L + C.gates.length - m) ≤ rank P L C C.gates.length + Yc P L C m + 1 ∧
  (∀ x y, val P L C x y C.output = true ↔
    (val P L C x (fun _ => false) C.output = true ∨ F P L C s (P + L + C.gates.length - m) x y)) ∧
  (∀ v, deg P L C v = 1 → Relation.ReflTransGen (Rel P L C) v C.output →
    v < P + L + C.gates.length - m →
    (v = C.output ∨ ∃ g, Rel P L C v g ∧ Relation.ReflTransGen (Rel P L C) g C.output ∧
      P + L + C.gates.length - m ≤ g) → s.2 v ≠ none)

lemma F_succ (s : (List Gate × (ℕ → Option (Option ℕ)))) (p : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) :
    F P L C s (p + 1) x y ↔ F P L C s p x y ∨
      (deg P L C p = 1 ∧ aEv P s.1 x (s.2 p) = true ∧ val P L C x y p = true) := by
  constructor
  · rintro ⟨v, hv, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · exact Or.inl ⟨v, hv, h⟩
    · exact Or.inr h
  · rintro (⟨v, hv, h⟩ | h)
    · exact ⟨v, by omega, h⟩
    · exact ⟨p, by omega, h⟩

lemma deg_out_le (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) : deg P L C C.output ≤ 1 := hl

lemma inv_zero (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) : Inv P L C 0 (init P L C) := by
  have hdo := deg_out_le P L C hl
  refine ⟨⟨[], by simp [init]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro v c hc
    simp only [init] at hc
    split_ifs at hc
    · simp at hc; subst hc; exact valid_none P _
  · exact phase1_good P L C hm hfan _ le_rfl
  · have h1 : Yc P L C 0 = 0 := by
      unfold Yc; rw [Finset.card_eq_zero]; ext j; simp; omega
    have h2 : Cnt (init P L C) (P + L + C.gates.length - 0) ≤ 1 := by
      unfold Cnt
      have : ((Finset.range (P + L + C.gates.length - 0)).filter fun u => (init P L C).2 u ≠ none) ⊆
          {C.output} := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨-, hu⟩ := hu
        simp only [init] at hu
        split_ifs at hu with h
        · simp [h.1]
        · simp at hu
      exact le_trans (Finset.card_le_card this) (by simp)
    simp only [init, phase1_length] at h2 ⊢
    rw [h1]; omega
  · intro x y
    by_cases ho : deg P L C C.output = 1 ∧ C.output < P + L + C.gates.length
    · constructor
      · intro h; right
        exact ⟨C.output, by omega, ho.1, by simp [init, ho, aEv, vEv], h⟩
      · rintro (h | ⟨v, -, -, ha, h⟩)
        · exact val_mono P L C hm x _ y (by simp) _ h
        · simp only [init] at ha
          split_ifs at ha with hh
          · rw [hh.1] at h; exact h
          · simp [aEv] at ha
    · have hd0 : deg P L C C.output = 0 := by
        by_cases hlt : C.output < P + L + C.gates.length
        · have : deg P L C C.output ≠ 1 := fun h => ho ⟨h, hlt⟩
          omega
        · exact deg_ge P L C _ (by omega)
      rw [val_indep P L C hm x y (fun _ => false) _ hd0]
      constructor
      · intro h; left; exact h
      · rintro (h | ⟨v, -, hv1, ha, -⟩)
        · exact h
        · simp only [init] at ha
          split_ifs at ha with hh
          · obtain ⟨e, h2, h3⟩ := hh
            subst e
            exact absurd ⟨h2, h3⟩ ho
          · simp [aEv] at ha
  · intro v hv1 _ hvK hor
    rcases hor with rfl | ⟨g, ⟨_, i, rfl, _⟩, _, hg⟩
    · simp [init, hv1, show C.output < P + L + C.gates.length by omega]
    · omega

end Main

section Sem

variable (P L : ℕ) (C : Circuit)

lemma val_or (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.or) :
    val P L C x y (P + L + j) = true ↔
      ∃ i ∈ C.gates[j].inputs, i < P + L + j ∧ val P L C x y i = true := by
  rw [val_gate P L C x y j hj, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    by_cases hlt : i < P + L + j
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; exact absurd h (by simp)
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, by rw [if_pos hlt]; exact h⟩

lemma val_and (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.and) :
    val P L C x y (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then val P L C x y i else false).all id := by
  rw [val_gate P L C x y j hj, hop]; rfl

lemma aEv_stable (s : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (hs : RefsOK P s) (x : Fin P → Bool) (u : ℕ) :
    aEv P (s.1 ++ r) x (s.2 u) = aEv P s.1 x (s.2 u) :=
  aEv_append P _ _ _ _ (fun d hd => hs u d hd)

lemma push_case_sem (s s1 : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (h1 : s1.1 = s.1 ++ r) (h2 : s1.2 = s.2)
    (hs : RefsOK P s) (τ : Option ℕ)
    (hτ : Valid P s1.1 τ) (a p : ℕ) (hap : a < p) (hda : deg P L C a = 1) (hdp : deg P L C p = 1)
    (x : Fin P → Bool) (y : Fin L → Bool)
    (hkey : (aEv P s.1 x (s.2 p) = true ∧ val P L C x y p = true) ↔
      (vEv P s1.1 x τ = true ∧ val P L C x y a = true)) :
    (F P L C s p x y ∨ (deg P L C p = 1 ∧ aEv P s.1 x (s.2 p) = true ∧ val P L C x y p = true)) ↔
      F P L C (push P s1 a τ) p x y := by
  have hs1 : RefsOK P s1 := fun v c hc => by
    rw [h2] at hc; rw [h1]; exact valid_append P _ _ _ (hs v c hc)
  have hst : ∀ u, aEv P s1.1 x (s1.2 u) = aEv P s.1 x (s.2 u) := by
    intro u; rw [h1, h2]; exact aEv_stable P s r hs x u
  have hsem := fun u => push_sem P s1 a τ hs1 hτ x u
  constructor
  · rintro (⟨v, hv, hdv, hav, hval⟩ | ⟨-, hcv, hvp⟩)
    · refine ⟨v, hv, hdv, ?_, hval⟩
      rw [hsem v]
      split_ifs with hva
      · subst hva; rw [hst]; simp [hav]
      · rw [hst]; exact hav
    · obtain ⟨h1', h2'⟩ := hkey.mp ⟨hcv, hvp⟩
      refine ⟨a, hap, hda, ?_, h2'⟩
      rw [hsem a, if_pos rfl]; simp [h1']
  · rintro ⟨v, hv, hdv, hav, hval⟩
    rw [hsem v] at hav
    split_ifs at hav with hva
    · subst hva
      rw [hst] at hav
      rcases Bool.or_eq_true_iff.mp hav with h | h
      · exact Or.inl ⟨v, hv, hdv, h, hval⟩
      · obtain ⟨h1', h2'⟩ := hkey.mpr ⟨h, hval⟩
        exact Or.inr ⟨hdp, h1', h2'⟩
    · rw [hst] at hav
      exact Or.inl ⟨v, hv, hdv, hav, hval⟩

lemma cnt_succ (s : (List Gate × (ℕ → Option (Option ℕ)))) (p : ℕ) : Cnt s (p + 1) = Cnt s p + if s.2 p ≠ none then 1 else 0 := by
  unfold Cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma yc_succ (m : ℕ) (hm : m < C.gates.length) :
    Yc P L C (m + 1) = Yc P L C m + if deg P L C (P + L + (C.gates.length - 1 - m)) = 1 then 1 else 0 := by
  unfold Yc
  split_ifs with hd
  · have e : ((Finset.range C.gates.length).filter fun j => C.gates.length - (m + 1) ≤ j ∧ deg P L C (P + L + j) = 1) =
        insert (C.gates.length - 1 - m)
          ((Finset.range C.gates.length).filter fun j => C.gates.length - m ≤ j ∧ deg P L C (P + L + j) = 1) := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases e : j' = C.gates.length - 1 - m
        · left; exact e
        · right; exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨by omega, by omega, hd⟩
        · exact ⟨h1, by omega, h3⟩
    rw [e, Finset.card_insert_of_notMem (by simp; omega)]
  · have e : ((Finset.range C.gates.length).filter fun j => C.gates.length - (m + 1) ≤ j ∧ deg P L C (P + L + j) = 1) =
        ((Finset.range C.gates.length).filter fun j => C.gates.length - m ≤ j ∧ deg P L C (P + L + j) = 1) := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases e : j' = C.gates.length - 1 - m
        · subst e; exact absurd h3 hd
        · exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by omega, h3⟩
    rw [e]; simp

lemma reach_step (hm : IsMonotoneCircuit C) (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (j : ℕ) (hj : j < C.gates.length) (s s' : (List Gate × (ℕ → Option (Option ℕ))))
    (hreach : ∀ v, deg P L C v = 1 → Relation.ReflTransGen (Rel P L C) v C.output →
      v < P + L + j + 1 →
      (v = C.output ∨ ∃ g, Rel P L C v g ∧ Relation.ReflTransGen (Rel P L C) g C.output ∧
        P + L + j + 1 ≤ g) → s.2 v ≠ none)
    (hkeep : ∀ u, s.2 u ≠ none → s'.2 u ≠ none)
    (hhit : deg P L C (P + L + j) = 1 → s.2 (P + L + j) ≠ none →
      ∀ v ∈ C.gates[j].inputs, v < P + L + j → deg P L C v = 1 → s'.2 v ≠ none) :
    ∀ v, deg P L C v = 1 → Relation.ReflTransGen (Rel P L C) v C.output →
      v < P + L + j →
      (v = C.output ∨ ∃ g, Rel P L C v g ∧ Relation.ReflTransGen (Rel P L C) g C.output ∧
        P + L + j ≤ g) → s'.2 v ≠ none := by
  intro v hdv hR hvp hor
  rcases hor with rfl | ⟨g, hRg, hRgo, hg⟩
  · exact hkeep _ (hreach _ hdv hR (by omega) (Or.inl rfl))
  · by_cases hgp : g = P + L + j
    · subst hgp
      have hdo := deg_out_le P L C hl
      have h1 := deg_le_of_rel P L C hm _ _ hRg
      have h2 := deg_le_of_reach P L C hm _ _ hRgo
      have hdp : deg P L C (P + L + j) = 1 := by omega
      have hne : s.2 (P + L + j) ≠ none := by
        apply hreach _ hdp hRgo (by omega)
        rcases Relation.ReflTransGen.cases_head hRgo with h | ⟨c, hc, hc2⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, hc2, by have := hc.1; omega⟩
      obtain ⟨hvlt, i, hi, hmem⟩ := hRg
      have hij : i.val = j := by omega
      have : C.gates.get i = C.gates[j] := by
        rw [List.get_eq_getElem]; congr 1
      rw [this] at hmem
      exact hhit hdp hne v hmem hvlt hdv
    · exact hkeep _ (hreach _ hdv hR (by omega) (Or.inr ⟨g, hRg, hRgo, by omega⟩))

end Sem

section StepInv

variable (P L : ℕ) (C : Circuit)

lemma pre_of (s s' : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (h : s'.1 = s.1 ++ r) (hp : Pre P L C s) : Pre P L C s' := by
  obtain ⟨q, hq⟩ := hp
  exact ⟨q ++ r, by rw [h, hq]; simp⟩

lemma inv_step (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) (m : ℕ) (hmt : m < C.gates.length)
    (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Inv P L C m s) :
    Inv P L C (m + 1) (stepGate P L C (C.gates.length - 1 - m) s) := by
  obtain ⟨hpre, hrefs, hgood, hcnt, hsem, hreach⟩ := hs
  have hYc := yc_succ P L C m hmt
  generalize hjd : C.gates.length - 1 - m = j at hYc ⊢
  have hj : j < C.gates.length := by omega
  have hK : P + L + C.gates.length - m = P + L + j + 1 := by omega
  have hK' : P + L + C.gates.length - (m + 1) = P + L + j := by omega
  rw [hK] at hcnt hsem hreach
  unfold Inv
  rw [hK']
  have hCnt := cnt_succ s (P + L + j)
  have H0 : ∀ x v, v < P + L + j + 1 → deg P L C v = 1 → aEv P s.1 x (s.2 v) = true →
      val P L C x (fun _ => false) v = true → val P L C x (fun _ => false) C.output = true :=
    fun x v hv hd ha h0 => (hsem x (fun _ => false)).mpr (Or.inr ⟨v, hv, hd, ha, h0⟩)
  by_cases hact : deg P L C (P + L + j) = 1 ∧ s.2 (P + L + j) ≠ none
  · obtain ⟨hdp, hne⟩ := hact
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hne
    have hvc : Valid P s.1 c := hrefs _ c hc
    have hcv : ∀ x, aEv P s.1 x (s.2 (P + L + j)) = vEv P s.1 x c := by intro x; rw [hc]; rfl
    rw [if_pos hdp] at hYc
    rw [if_pos hne] at hCnt
    rcases stepGate_shape P L C hm hfan j hj s c hdp hc with
      ⟨hop, hst⟩ | ⟨a, hop, hin, hap, hda, hst⟩ | ⟨a, b, hop, hin, hap, hda, hb, hst⟩ |
      ⟨a, b, hop, hin, hap, hda, hb, hst⟩
    · -- OR gate
      rw [hst]
      obtain ⟨r, hr, hrl, hgr⟩ := orFold_fst P L C j c C.gates[j].inputs s
      have hlen : C.gates[j].inputs.length ≤ 2 := hfan _ (List.getElem_mem hj)
      refine ⟨pre_of P L C s _ r hr hpre, (orFold_refs P L C j c _ s hrefs hvc).1,
        by rw [hr]; exact goodGates_append _ _ hgood hgr, ?_, ?_, ?_⟩
      · have := orFold_count P L C j c C.gates[j].inputs s (P + L + j)
        unfold Cnt at *; omega
      · intro x y
        rw [hsem x y, F_succ]
        have hos := fun u => orFold_sem P L C j c C.gates[j].inputs s hrefs hvc x u
        constructor
        · rintro (h0 | (⟨v, hv, hdv, hav, hval⟩ | ⟨-, hap', hvp⟩))
          · exact Or.inl h0
          · right; refine ⟨v, hv, hdv, ?_, hval⟩; rw [hos v]; simp [hav]
          · rw [hcv] at hap'
            obtain ⟨i, hi, hip, hvi⟩ := (val_or P L C x y j hj hop).mp hvp
            have hdi := deg_le_of_input P L C hm j hj i hi hip
            by_cases hdi1 : deg P L C i = 1
            · right; refine ⟨i, hip, hdi1, ?_, hvi⟩; rw [hos i]; simp [hap', hi, hip, hdi1]
            · left
              have hdi0 : deg P L C i = 0 := by omega
              rw [val_indep P L C hm x y (fun _ => false) i hdi0] at hvi
              apply H0 x (P + L + j) (by omega) hdp (by rw [hcv]; exact hap')
              exact (val_or P L C x _ j hj hop).mpr ⟨i, hi, hip, hvi⟩
        · rintro (h0 | ⟨v, hv, hdv, hav, hval⟩)
          · exact Or.inl h0
          · right
            rw [hos v] at hav
            rcases Bool.or_eq_true_iff.mp hav with h | h
            · exact Or.inl ⟨v, hv, hdv, h, hval⟩
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨h1, h2, -, -⟩ := h
              exact Or.inr ⟨hdp, by rw [hcv]; exact h1, (val_or P L C x y j hj hop).mpr ⟨v, h2, hv, hval⟩⟩
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => orFold_keep P L C j c _ s u hu)
          (fun _ _ v hv hvp hdv => orFold_hit P L C j c _ s v hv ⟨hvp, hdv⟩)
    · -- AND gate, one input
      rw [hst]
      obtain ⟨r, hr, hrl, hgr⟩ := push_fst P s a c
      refine ⟨pre_of P L C s _ r hr hpre, push_refs P s a c hrefs hvc,
        by rw [hr]; exact goodGates_append _ _ hgood hgr, ?_, ?_, ?_⟩
      · have := push_count P s a c (P + L + j)
        unfold Cnt at *; omega
      · intro x y
        rw [hsem x y, F_succ]
        have key := push_case_sem P L C s s [] (by simp) rfl hrefs c hvc a (P + L + j) hap hda hdp x y
          (by rw [hcv, val_and P L C x y j hj hop, hin]; simp [hap])
        rw [key]
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => push_keep P s a c u hu)
          (fun _ _ v hv _ _ => by rw [hin] at hv; simp at hv; subst hv; exact push_snd_self P s v c)
    · -- AND gate, line input first
      rw [hst]
      obtain ⟨r1, hr1, hrl1, hgr1, h2⟩ := andTerm_fst P L C j s c b
      obtain ⟨r, hr, hrl, hgr⟩ := push_fst P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
      have hs1 : RefsOK P (andTerm P L C j s c b).1 := fun v d hd => by
        rw [h2] at hd; rw [hr1]; exact valid_append P _ _ _ (hrefs v d hd)
      have hτ := andTerm_valid P L C j hj s hpre c hvc b hb
      refine ⟨pre_of P L C s _ (r1 ++ r) (by rw [hr, hr1]; simp) hpre, push_refs P _ a _ hs1 hτ,
        by rw [hr, hr1]; exact goodGates_append _ _ (goodGates_append _ _ hgood hgr1) hgr, ?_, ?_, ?_⟩
      · have := push_count P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2 (P + L + j)
        have e1 : (andTerm P L C j s c b).1.1.length = s.1.length + r1.length := by rw [hr1]; simp
        unfold Cnt at *; rw [h2] at this; omega
      · intro x y
        rw [hsem x y, F_succ]
        have key := push_case_sem P L C s (andTerm P L C j s c b).1 r1 hr1 h2 hrefs _ hτ a (P + L + j)
          hap hda hdp x y (by
            rw [hcv, andTerm_val P L C hm j hj s hpre c hvc b hb x y, val_and P L C x y j hj hop, hin]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, if_pos hap,
              Bool.and_true, Bool.and_eq_true]
            tauto)
        rw [key]
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => push_keep P _ a _ u (by rw [h2]; exact hu))
          (fun _ _ v hv hvp hdv => by
            rw [hin] at hv; simp at hv
            rcases hv with rfl | rfl
            · exact push_snd_self P _ v _
            · have := hb hvp; omega)
    · -- AND gate, line input second
      rw [hst]
      obtain ⟨r1, hr1, hrl1, hgr1, h2⟩ := andTerm_fst P L C j s c b
      obtain ⟨r, hr, hrl, hgr⟩ := push_fst P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
      have hs1 : RefsOK P (andTerm P L C j s c b).1 := fun v d hd => by
        rw [h2] at hd; rw [hr1]; exact valid_append P _ _ _ (hrefs v d hd)
      have hτ := andTerm_valid P L C j hj s hpre c hvc b hb
      refine ⟨pre_of P L C s _ (r1 ++ r) (by rw [hr, hr1]; simp) hpre, push_refs P _ a _ hs1 hτ,
        by rw [hr, hr1]; exact goodGates_append _ _ (goodGates_append _ _ hgood hgr1) hgr, ?_, ?_, ?_⟩
      · have := push_count P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2 (P + L + j)
        have e1 : (andTerm P L C j s c b).1.1.length = s.1.length + r1.length := by rw [hr1]; simp
        unfold Cnt at *; rw [h2] at this; omega
      · intro x y
        rw [hsem x y, F_succ]
        have key := push_case_sem P L C s (andTerm P L C j s c b).1 r1 hr1 h2 hrefs _ hτ a (P + L + j)
          hap hda hdp x y (by
            rw [hcv, andTerm_val P L C hm j hj s hpre c hvc b hb x y, val_and P L C x y j hj hop, hin]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, if_pos hap,
              Bool.and_true, Bool.and_eq_true]
            tauto)
        rw [key]
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => push_keep P _ a _ u (by rw [h2]; exact hu))
          (fun _ _ v hv hvp hdv => by
            rw [hin] at hv; simp at hv
            rcases hv with rfl | rfl
            · have := hb hvp; omega
            · exact push_snd_self P _ v _)
  · -- the gate is not processed
    have hst := stepGate_id P L C j s (by
      by_cases h : deg P L C (P + L + j) = 1
      · right; by_contra h'; exact hact ⟨h, h'⟩
      · left; exact h)
    rw [hst]
    refine ⟨hpre, hrefs, hgood, ?_, ?_, ?_⟩
    · split_ifs at hYc hCnt <;> omega
    · intro x y
      rw [hsem x y, F_succ]
      constructor
      · rintro (h0 | h | ⟨hd, ha, -⟩)
        · exact Or.inl h0
        · exact Or.inr h
        · have : s.2 (P + L + j) = none := by by_contra h'; exact hact ⟨hd, h'⟩
          rw [this] at ha; simp [aEv] at ha
      · rintro (h0 | h)
        · exact Or.inl h0
        · exact Or.inr (Or.inl h)
    · exact reach_step P L C hm hl j hj s s hreach (fun u hu => hu)
        (fun hd hne => absurd ⟨hd, hne⟩ hact)

end StepInv

section Final

variable (P L : ℕ) (C : Circuit)

lemma inv_all (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) (m : ℕ) (hmt : m ≤ C.gates.length) :
    Inv P L C m (S P L C m) := by
  induction m with
  | zero => exact inv_zero P L C hm hfan hl
  | succ m ih => exact inv_step P L C hm hfan hl m (by omega) _ (ih (by omega))

def oIdx (s : (List Gate × (ℕ → Option (Option ℕ)))) (u : ℕ) : ℕ :=
  match s.2 u with
  | some (some w) => w
  | _ => P + s.1.length

lemma aEv_read (s : (List Gate × (ℕ → Option (Option ℕ)))) (x : Fin P → Bool) (u : ℕ) :
    aEv P s.1 x (s.2 u) = true ↔
      (s.2 u = some none ∨ (dw s.1 (List.ofFn x)).getD (oIdx P s u) false = true) := by
  unfold oIdx
  rcases h : s.2 u with _ | _ | w
  · simp only [aEv, reduceCtorEq, false_or, Bool.false_eq_true, false_iff]
    rw [dw_getD_ge _ _ _ (by simp)]; simp
  · simp [aEv, vEv]
  · simp [aEv, vEv]

lemma rank_add_yc : rank P L C C.gates.length + Yc P L C C.gates.length ≤ C.gates.length := by
  unfold rank Yc
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range C.gates.length) (fun j => deg P L C (P + L + j) = 0)
  have hsub : ((Finset.range C.gates.length).filter fun j =>
      C.gates.length - C.gates.length ≤ j ∧ deg P L C (P + L + j) = 1) ⊆
      ((Finset.range C.gates.length).filter fun j => ¬ deg P L C (P + L + j) = 0) := by
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, by omega⟩
  have := Finset.card_le_card hsub
  simp only [Finset.card_range] at h
  omega

end Final

end PEqualNP.Outside.L_meta_738

theorem PEqualNP.Outside.L_meta_738 : ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) := by
  intro P L C N hm hfan hl _ hN
  open PEqualNP.Outside.L_meta_738 in
  obtain ⟨-, -, hgood, hcnt, hsem, hreach⟩ := inv_all P L C hm hfan hl C.gates.length le_rfl
  open PEqualNP.Outside.L_meta_738 in
  refine ⟨⟨(S P L C C.gates.length).1, 0⟩,
    Finset.univ.filter (fun u : Fin L => (S P L C C.gates.length).2 (P + u.val) = some none),
    fun u => oIdx P (S P L C C.gates.length) (P + u.val), ?_, ?_, ?_, ?_⟩
  · intro g hg; exact (hgood g hg).1
  · intro g hg; exact (hgood g hg).2
  · open PEqualNP.Outside.L_meta_738 in
    have hN' : N.card ≤ Cnt (S P L C C.gates.length) (P + L + C.gates.length - C.gates.length) := by
      unfold Cnt
      apply Finset.card_le_card_of_injOn (fun u : Fin L => P + u.val)
      · intro u hu
        have hu' : u ∈ N := hu
        have hR := (hN u).mp hu'
        apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by show P + u.val < P + L + C.gates.length - C.gates.length; omega), ?_⟩
        apply hreach (P + u.val) (deg_line P L C _ (by omega) (by omega)) hR (by omega)
        rcases Relation.ReflTransGen.cases_head hR with h | ⟨c, hc, hc2⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, hc2, by obtain ⟨_, i, rfl, _⟩ := hc; omega⟩
      · intro a _ b _ h
        exact Fin.ext (by simpa using h)
    open PEqualNP.Outside.L_meta_738 in
    have hry := rank_add_yc P L C
    show (S P L C C.gates.length).1.length + N.card ≤ C.gates.length + 1
    omega
  · intro x y
    open PEqualNP.Outside.L_meta_738 in
    have e1 : C.eval (List.ofFn x ++ List.ofFn y) = val P L C x y C.output := rfl
    open PEqualNP.Outside.L_meta_738 in
    have e2 : C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) =
        val P L C x (fun _ => false) C.output := rfl
    rw [e1, e2]
    apply Bool.eq_iff_iff.mpr
    rw [hsem x y]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    apply or_congr_right
    constructor
    · rintro ⟨v, hv, hdv, hav, hval⟩
      have hvP : P ≤ v := by
        by_contra h
        open PEqualNP.Outside.L_meta_738 in
        rw [deg_point P L C v (by omega)] at hdv
        omega
      open PEqualNP.Outside.L_meta_738 in
      rw [val_line P L C x y v hvP (by omega)] at hval
      refine ⟨⟨v - P, by omega⟩, hval, ?_⟩
      have ev : P + (v - P) = v := by omega
      open PEqualNP.Outside.L_meta_738 in
      rcases (aEv_read P _ x v).mp hav with h | h
      · left; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [ev]; exact h
      · right; simp only []; rw [ev]; exact h
    · rintro ⟨u, hyu, hu⟩
      open PEqualNP.Outside.L_meta_738 in
      refine ⟨P + u.val, by omega, deg_line P L C _ (by omega) (by omega),
        (aEv_read P _ x _).mpr ?_, ?_⟩
      · rcases hu with h | h
        · left; simpa using h
        · right; exact h
      · open PEqualNP.Outside.L_meta_738 in
        rw [val_line P L C x y (P + u.val) (by omega) (by omega)]
        have : (⟨P + u.val - P, by omega⟩ : Fin L) = u := Fin.ext (by simp)
        rw [this]; exact hyu
