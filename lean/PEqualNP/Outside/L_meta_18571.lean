import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18571_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (gs : List Gate)
    (ops : binaryOps gs) (noEmpty : ∀ g ∈ gs, g.op = GateOp.and → g.inputs ≠ [])
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty := noEmpty gs[j] (List.getElem_mem hj)
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_or {n : ℕ} (gs : List Gate)
    (ops : binaryOps gs) (noEmpty : ∀ g ∈ gs, g.op = GateOp.and → g.inputs ≠ []) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate gs ops noEmpty w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (noEmpty : ∀ g ∈ gs, g.op = GateOp.and → g.inputs ≠ []) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (clean : ∀ x, posRead gs w x = true → edgeTrue G x)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply clean _
  rw [pos_gate gs ops noEmpty w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]

lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A D : ℕ → Bool) (pin : ℕ → Finset (Fin n))
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if D w = true then pin w
      else if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A D pin ha hb (a w)
        else coverCert k N S a b A D pin ha hb (b w)
      else
        coverCert k N S a b A D pin ha hb (a w) ∪ coverCert k N S a b A D pin ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A D : ℕ → Bool) (pin : ℕ → Finset (Fin n)) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (pinsSmall : ∀ w, (pin w).card ≤ 1)
    (pinsHit : ∀ w u v, k ≤ w → w < N → D w = true → G.Adj u v → H w u v →
      u ∈ pin w ∨ v ∈ pin w)
    (handS : ∀ w, k ≤ w → w < N → A w = true → D w = false →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A D pin ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if D w = true then pin w
          else if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, G.Adj u v → H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v adjUV hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        by_cases hd : D w = true
        · rw [ite_eq_left hd]
          exact pinsHit w u v hkw hw hd adjUV hwuv
        rw [ite_eq_right hd]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v adjUV h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v adjUV h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v adjUV hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg (Bool.eq_false_iff.mpr hd)).resolve_left htA) u v adjUV hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v huv (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    have noPin : D w ≠ true := by
      intro h
      rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left h] at hw
      exact (Nat.not_lt_of_ge (pinsSmall w)) hw
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_right noPin, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_right noPin, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_right noPin, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A D : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → D w = false → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      (D w = true ∧ H w x y ∨ D w = false ∧
        ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w)))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        by_cases hd : D w = true
        · exact ⟨w, hkw, hr, hop, Or.inl ⟨hd, hxy⟩⟩
        have hd' : D w = false := Bool.eq_false_iff.mpr hd
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, Or.inr ⟨hd', ?_⟩⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop hd')
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A D : ℕ → Bool) (EGood : Finset (Sym2 (Fin n)))
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hlight : ∀ w, k ≤ w → w < N → A w = true → ∀ c,
      (∀ u ∈ S w, G.Adj c u) → (S w).card ≤ 1)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true → D w = false →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true → D w = false →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, s(u,v) ∈ EGood → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧ D w = false ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    EGood.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ D w = false)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : EGood = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e
      induction e using Sym2.inductionOn with
      | _ u v => exact isEmptyElim u
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ D w = false)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA, hD⟩ : w < N ∧ k ≤ w ∧ A w = true ∧ D w = false := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA hD
        rcases hside w hk hN hA hD with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => exact False.elim ((Nat.not_lt_of_ge (hlight i hk hgood.1 he c hgood.2)) hi)
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : EGood ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        obtain ⟨w,hk,hN,hA,hD,how⟩ := hcover u v he
        have hw : w ∈ AS := by simp [AS,hN,hk,hA,hD]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      EGood.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

end PEqualNP.Outside.L_meta_18571_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18571_aux

namespace PEqualNP.Outside.L_meta_18571_aux
set_option maxHeartbeats 2000000 in
theorem countDonor : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨ (∀ a b c d : Fin n, G.Adj a b → G.Adj c d → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true → (a = c ∧ b = d) ∨ (a = d ∧ b = c))) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops evaluate starForm
  classical
  have correct (x : Fin n → Bool) : (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    rw [evaluate]
    exact decide_eq_true_iff
  by_cases small : G.edgeFinset.card ≤ 1
  · by_cases empty : G.edgeFinset = ∅
    · refine ⟨∅, ?_, by simp [empty]⟩
      intro u v edge
      have member : s(u,v) ∈ G.edgeFinset := G.mem_edgeFinset.mpr edge
      simp [empty] at member
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      induction e using Sym2.inductionOn with
      | _ u v =>
        have uv := G.mem_edgeFinset.mp he
        refine ⟨{u}, ?_, ?_⟩
        · intro a b hab
          have eq := Sym2.eq_iff.mp
            (Finset.card_le_one.mp small s(a,b) (G.mem_edgeFinset.mpr hab) s(u,v) he)
          rcases eq with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp
        · have nonzero : 0 < gs.length := by
            by_contra! noGates
            have rootSmall : clampWire (n+gs.length) out < n+1 := by
              have := root_bound n gs.length out
              omega
            have hit := hit_base gs _ u v rootSmall (root_hits G gs out correct u v uv)
            simp [root_support_empty G gs out correct] at hit
          simp only [Finset.card_singleton]
          omega
  have noEmpty : ∀ g ∈ gs, g.op = GateOp.and → g.inputs ≠ [] := by
    intro g hg hop hempty
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    have fires (x : Fin n → Bool) : (wiresFrom gs (List.ofFn x)).getD (n + i.val) false = true := by
      have eq := getD_wiresFrom_gate gs (List.ofFn x) i.val i.isLt
      change (wiresFrom gs (List.ofFn x)).getD ((List.ofFn x).length + i.val) false =
        (gs.get i).op.eval ((gs.get i).inputs.map fun j =>
          if j < (List.ofFn x).length + i.val then (wiresFrom gs (List.ofFn x)).getD j false
          else false) at eq
      rw [hop, hempty] at eq
      simpa only [List.length_ofFn, List.map_nil, GateOp.eval, List.all_nil] using eq
    rcases starForm i hop with below | oneEdge
    · obtain ⟨u, v, _, hu, _⟩ := below (fun _ => false) (fires _)
      contradiction
    · apply small
      apply Finset.card_le_one.mpr
      intro a ha b hb
      induction a using Sym2.inductionOn with
      | _ u v =>
        induction b using Sym2.inductionOn with
        | _ p q =>
          exact Sym2.eq_iff.mpr (oneEdge u v p q (G.mem_edgeFinset.mp ha)
            (G.mem_edgeFinset.mp hb) (fires _) (fires _))
  let k := n+1
  let N := n+1+gs.length
  let root := clampWire (n+gs.length) out
  let S := supports (n:=n) gs
  let H (w : ℕ) (u v : Fin n) : Prop := posRead gs w (pairBits u v) = true
  let leftWire := firstWire n gs
  let rightWire := secondWire n gs
  let A := andPos n gs
  let below (w : ℕ) := ∀ x : Fin n → Bool, posRead gs w x = true → edgeTrue G x
  let dirty (w : ℕ) : Bool := if A w then decide (¬ below w) else false
  have dirtyTrue (w : ℕ) (ha : A w = true) : dirty w = true ↔ ¬ below w := by simp [dirty, ha]
  have dirtyIsAnd (w : ℕ) (hd : dirty w = true) : A w = true := by
    cases h : A w <;> simp_all [dirty]
  have belowIfClean {w : ℕ} (ha : A w = true) (hw : dirty w = false) : below w := by
    by_contra h
    have := (dirtyTrue w ha).2 h
    simp_all
  have earlier1 (w : ℕ) (lo : k ≤ w) (_ : w < N) : leftWire w < w :=
    clamp_lt _ _ (by dsimp [k] at lo; omega)
  have earlier2 (w : ℕ) (lo : k ≤ w) (_ : w < N) : rightWire w < w :=
    clamp_lt _ _ (by dsimp [k] at lo; omega)
  have ORsupport (w : ℕ) (lo : k ≤ w) (hi : w < N) (ho : A w = false) :
      S w = S (leftWire w) ∪ S (rightWire w) := support_or gs ops noEmpty w lo hi ho
  have ORhit (w : ℕ) (u v : Fin n) (lo : k ≤ w) (hi : w < N) (ho : A w = false)
      (hit : H w u v) : H (leftWire w) u v ∨ H (rightWire w) u v := by
    simp only [A] at ho
    simpa only [H, leftWire, rightWire, pos_gate gs ops noEmpty w lo hi, ho,
      Bool.false_eq_true, ite_false, Bool.or_eq_true] using hit
  have ANDhit (w : ℕ) (u v : Fin n) (lo : k ≤ w) (hi : w < N) (ho : A w = true)
      (hit : H w u v) : H (leftWire w) u v ∧ H (rightWire w) u v := by
    simp only [A] at ho
    simpa only [H, leftWire, rightWire, pos_gate gs ops noEmpty w lo hi, ho, ite_true,
      Bool.and_eq_true] using hit
  have crossing (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true)
      (hd : dirty w = false) : ∀ u ∈ S (leftWire w), ∀ v ∈ S (rightWire w), G.Adj u v :=
    cross_support G gs ops noEmpty w lo hi ha (belowIfClean ha hd)
  have disjoint (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true)
      (hd : dirty w = false) : Disjoint (S (leftWire w)) (S (rightWire w)) := by
    rw [Finset.disjoint_left]
    intro u hu hv
    exact G.loopless.irrefl u (crossing w lo hi ha hd _ hu _ hv)
  have sideSmall (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true)
      (hd : dirty w = false) : (S (leftWire w)).card ≤ 1 ∨ (S (rightWire w)).card ≤ 1 := by
    by_contra! large
    obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp large.1
    obtain ⟨a, ha', b, hb, hab⟩ := Finset.one_lt_card.mp large.2
    have cross := crossing w lo hi ha hd
    exact hc4 u a v b hne hab ⟨cross u hu a ha', (cross v hv a ha').symm,
      cross v hv b hb, (cross u hu b hb).symm⟩
  have unique (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true) (hd : dirty w = true)
      (u v p q : Fin n) (uv : G.Adj u v) (pq : G.Adj p q) (huv : H w u v) (hpq : H w p q) :
      (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
    let j : Fin gs.length := ⟨w-k, by dsimp [N, k] at hi ⊢; omega⟩
    have atGate : w = n + j.val + 1 := by dsimp [j, k] at *; omega
    have op : (gs.get j).op = GateOp.and := by
      have isAnd : andPos n gs (n+j.val+1) = true := by rw [← atGate]; exact ha
      rw [andPos, gateAt_index gs j.val j.isLt] at isAnd
      change (match (gs.get j).op with | GateOp.and => true | _ => false) = true at isAnd
      cases eq : (gs.get j).op <;> simp_all
    rcases starForm j op with clean | oneEdge
    · refine ((dirtyTrue w ha).1 hd ?_).elim
      intro x hx
      apply clean x
      rw [atGate] at hx
      exact hx
    · rw [show H w u v = (posRead gs (n+j.val+1) (pairBits u v) = true) from by rw [← atGate]] at huv
      rw [show H w p q = (posRead gs (n+j.val+1) (pairBits p q) = true) from by rw [← atGate]] at hpq
      exact oneEdge u v p q uv pq huv hpq

  have ANDlight (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true) (c : Fin n)
      (adjacent : ∀ u ∈ S w, G.Adj c u) : (S w).card ≤ 1 := by
    cases hd : dirty w
    · have emptySupport : S w = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact edge_single G u (belowIfClean ha hd _ ((mem_support gs w u).mp hu))
      simp [emptySupport]
    · apply Finset.card_le_one.mpr
      intro u hu v hv
      have hit (z : Fin n) (hz : z ∈ S w) : H w c z := by
        apply pos_mono gs (fun g hg => (ops g hg).1) w (singletonBits z) (pairBits c z) _
          ((mem_support gs w z).mp hz)
        intro i hi
        have eq : i = z := of_decide_eq_true hi
        simp [pairBits, eq]
      rcases unique w lo hi ha hd c u c v (adjacent u hu) (adjacent v hv)
        (hit u hu) (hit v hv) with eq | eq
      · exact eq.2
      · exact (eq.2.trans eq.1)
  let pin (w : ℕ) : Finset (Fin n) :=
    if h : ∃ u v, G.Adj u v ∧ H w u v then {h.choose} else ∅
  have pinSmall (w : ℕ) : (pin w).card ≤ 1 := by
    unfold pin
    split <;> simp
  have pinHit (w : ℕ) (u v : Fin n) (lo : k ≤ w) (hi : w < N)
      (hd : dirty w = true) (uv : G.Adj u v) (hit : H w u v) :
      u ∈ pin w ∨ v ∈ pin w := by
    have existsEdge : ∃ u v, G.Adj u v ∧ H w u v := ⟨u, v, uv, hit⟩
    obtain ⟨q, adj, hq⟩ := existsEdge.choose_spec
    have eq := unique w lo hi (dirtyIsAnd w hd) hd u v existsEdge.choose q uv adj hit hq
    rw [show pin w = {existsEdge.choose} by simp [pin, existsEdge]]
    exact eq.elim (fun h => Or.inl (Finset.mem_singleton.mpr h.1))
      (fun h => Or.inr (Finset.mem_singleton.mpr h.2))
  have rBound : root < N := root_bound n gs.length out
  have rEmpty : S root = ∅ := root_support_empty G gs out correct
  have rHit : ∀ u v, G.Adj u v → H root u v := root_hits G gs out correct
  obtain ⟨T, cover, coverBound⟩ :=
    cover_half n k N root G S H leftWire rightWire A dirty pin rBound rEmpty rHit
      (hit_base gs) earlier1 earlier2 ORsupport ORhit pinSmall pinHit sideSmall ANDhit
      (fun f R B step => dag_union_bound f R B step)
  let goodAND := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ dirty w = false)
  let badAND := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ dirty w = true)
  let allAND := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
  let largeOR := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let smallOR := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)

  let edgeList (w : ℕ) := G.edgeFinset.filter (fun e => ∃ u v, e = s(u,v) ∧ H w u v)
  let badEdges := badAND.biUnion edgeList
  let goodEdges := G.edgeFinset \ badEdges
  have badBound : badEdges.card ≤ badAND.card := by
    calc
      badEdges.card ≤ ∑ w ∈ badAND, (edgeList w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ badAND, 1 := by
        apply Finset.sum_le_sum
        intro w hw
        have ⟨hi, lo, ha, hd⟩ : w < N ∧ k ≤ w ∧ A w = true ∧ dirty w = true := by
          simpa [badAND] using hw
        apply Finset.card_le_one.mpr
        intro e he f hf
        obtain ⟨heG, u, v, rfl, hu⟩ := Finset.mem_filter.mp he
        obtain ⟨hfG, p, q, rfl, hp⟩ := Finset.mem_filter.mp hf
        exact Sym2.eq_iff.mpr (unique w lo hi ha hd u v p q (G.mem_edgeFinset.mp heG)
          (G.mem_edgeFinset.mp hfG) hu hp)
      _ = badAND.card := by simp
  have goodBound : goodEdges.card ≤ goodAND.card + largeOR.card := by
    apply edge_finset_gate_bound n k N G S leftWire rightWire A dirty goodEdges hc4
      (support_base gs) (fun w lo hi => ⟨earlier1 w lo hi, earlier2 w lo hi⟩)
      ANDlight ORsupport crossing sideSmall
    intro u v h
    have uv := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp h).1
    obtain ⟨w, lo, hi, ha, birth⟩ :=
      edge_birth n k N root S H leftWire rightWire A dirty u v rBound (rHit u v uv)
        (by simp [rEmpty]) (by simp [rEmpty]) (hit_base gs) earlier1 earlier2 ORsupport ORhit
        ANDhit disjoint
    rcases birth with ⟨hd, hit⟩ | ⟨hd, cross⟩
    · exfalso
      apply (Finset.mem_sdiff.mp h).2
      exact Finset.mem_biUnion.mpr ⟨w, by simp [badAND, hi, lo, ha, hd],
        Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr uv, u, v, rfl, hit⟩⟩
    · exact ⟨w, lo, hi, ha, hd, cross⟩
  have hbadSub : badEdges ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hw).1
  have edgePartition : goodEdges.card + badEdges.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hbadSub
  have andDisjoint : Disjoint goodAND badAND := by
    rw [Finset.disjoint_left]
    intro w hgood hbad
    have f : dirty w = false := (Finset.mem_filter.mp hgood).2.2.2
    have t : dirty w = true := (Finset.mem_filter.mp hbad).2.2.2
    simp_all
  have andPartition : goodAND.card + badAND.card ≤ allAND.card := by
    rw [← Finset.card_union_of_disjoint andDisjoint]
    apply Finset.card_le_card
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1,
        (Finset.mem_filter.mp h).2.2.1⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1,
        (Finset.mem_filter.mp h).2.2.1⟩
  have total : allAND.card + largeOR.card + smallOR.card ≤ gs.length :=
    gate_partition_count n gs.length A S
  change T.card ≤ 1 + smallOR.card at coverBound
  exact ⟨T, cover, by omega⟩

end PEqualNP.Outside.L_meta_18571_aux
namespace PEqualNP.Outside.L_meta_18571
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
abbrev G : SimpleGraph (Fin 26) := PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x1 : ℕ) => List.filterMap (fun (x2 : ℕ) => if (x1 + (13 : ℕ) - x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] then Option.some (x1 + (1 : ℕ), x2 + (14 : ℕ)) else Option.none) (List.range (12 : ℕ))) (List.range (12 : ℕ)))
def masks : Array Nat := #[0, 17055744, 34127872, 1146880, 2310144, 4620288, 9240576, 18481152, 36962304, 6815744, 13647872, 27295744, 54591488, 0, 1046, 2092, 4184, 176, 354, 708, 1416, 2832, 5664, 3136, 6274, 4356]
def oneCommon : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 14, 18, 18, 24, 18, 0, 14, 24, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 15, 14, 15, 19, 19, 25, 19, 14, 15, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 16, 15, 16, 20, 20, 0, 20, 15, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14, 16, 0, 17, 16, 17, 21, 21, 14, 21, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 15, 15, 17, 0, 18, 17, 18, 22, 22, 15, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 16, 16, 18, 0, 19, 18, 19, 23, 23, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 19, 20, 17, 17, 19, 0, 20, 19, 20, 24, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 25, 20, 21, 18, 18, 20, 0, 21, 20, 21, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 21, 22, 19, 19, 21, 0, 22, 21, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14, 20, 14, 22, 23, 20, 20, 22, 0, 23, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 15, 15, 21, 15, 23, 24, 21, 21, 23, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 16, 16, 22, 16, 24, 25, 22, 22, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 4, 1, 2, 10, 4, 10, 10, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 5, 5, 2, 3, 11, 5, 11, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 4, 6, 6, 3, 4, 12, 6, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 4, 0, 5, 7, 7, 4, 5, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 6, 5, 0, 6, 8, 8, 5, 6, 1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 6, 7, 6, 0, 7, 9, 9, 6, 7, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 3, 3, 7, 8, 7, 0, 8, 10, 10, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 11, 4, 4, 8, 9, 8, 0, 9, 11, 11, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 5, 12, 5, 5, 9, 10, 9, 0, 10, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11, 6, 0, 6, 6, 10, 11, 10, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 11, 12, 7, 1, 7, 7, 11, 12, 11, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 12, 0, 8, 2, 8, 8, 12, 0, 12, 0]
theorem maskAdj : ∀ a b : Fin 26, G.Adj a b ↔ (masks[a.val]!).testBit b.val = true := by decide +kernel
theorem onlyCommon : ∀ a c b : Fin 26, a ≠ c → (masks[a.val]!).testBit b.val = true →
    (masks[c.val]!).testBit b.val = true → b.val = oneCommon[a.val*26+c.val]! := by decide +kernel
theorem girth : ∀ a b c d : Fin 26, a ≠ c → b ≠ d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d ac bd ⟨ab,bc,cd,da⟩
  apply bd
  apply Fin.ext
  exact (onlyCommon a c b ac ((maskAdj ..).mp ab) ((maskAdj ..).mp bc.symm)).trans
    (onlyCommon a c d ac ((maskAdj ..).mp da.symm) ((maskAdj ..).mp cd)).symm
theorem edgeCount : G.edgeFinset.card = 45 := by decide +kernel
def lft (v : Fin 12) : Fin 26 := ⟨v.val+1,by omega⟩
def rgt (v : Fin 12) : Fin 26 := ⟨v.val+14,by omega⟩
theorem matchAdj : ∀ i : Fin 12, G.Adj (lft i) (rgt i) := by decide +kernel
theorem covers (T : Finset (Fin 26)) (h : ∀ a b : Fin 26, G.Adj a b → a ∈ T ∨ b ∈ T) :
    12 ≤ T.card := by
  let f : Fin 12 → Fin 26 := fun i => if lft i ∈ T then lft i else rgt i
  have sub : Set.MapsTo f (Finset.univ : Finset (Fin 12)) T := by
    intro i _; dsimp [f]; split
    · assumption
    · exact (h _ _ (matchAdj i)).resolve_left (by assumption)
  have inj : Function.Injective f := by
    intro i j e
    apply Fin.ext
    have vals := congrArg Fin.val e
    dsimp [f] at vals
    split at vals <;> split at vals <;> simp only [lft,rgt] at vals <;> omega
  simpa using Finset.card_le_card_of_injOn f sub inj.injOn

theorem orderedEdge {a b : Fin 26} (h : G.Adj a b) :
    ∃ u v, u < v ∧ G.Adj u v ∧ pairInput u v = pairInput a b ∧
      ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) := by
  rcases lt_or_gt_of_ne h.ne with ha | ha
  · exact ⟨a,b,ha,h,rfl,Or.inl ⟨rfl,rfl⟩⟩
  · refine ⟨b,a,ha,h.symm,?_,Or.inr ⟨rfl,rfl⟩⟩
    funext k; simp only [pairInput,or_comm]

theorem specialize (bound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨ (∀ a b c d : Fin n, G.Adj a b → G.Adj c d → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true → (a = c ∧ b = d) ∨ (a = d ∧ b = c))) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) :
    let x1 : SimpleGraph (Fin (26 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x1 : ℕ) => List.filterMap (fun (x2 : ℕ) => if (x1 + (13 : ℕ) - x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] then Option.some (x1 + (1 : ℕ), x2 + (14 : ℕ)) else Option.none) (List.range (12 : ℕ))) (List.range (12 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (55 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ → ∃ (x6 : ℕ), PEqualNP.CleanedNonEdge.IsDirtyAnd (26 : ℕ) x1 x2 x6 ∧ ∃ (x7 : Fin (26 : ℕ)) (x8 : Fin (26 : ℕ)) (x9 : Fin (26 : ℕ)) (x10 : Fin (26 : ℕ)), x1.Adj x7 x8 ∧ x1.Adj x9 x10 ∧ x7 < x8 ∧ x9 < x10 ∧ (x7, x8) ≠ (x9, x10) ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
  dsimp only
  intro C hm sz spec
  change circuitFun 26 C = graphFun G ∅ at spec
  by_contra absent
  obtain ⟨T,cv,sz'⟩ := bound 26 G girth C.gates C.output (fun g hg => by
    obtain ⟨hop,har⟩ := hm g hg
    exact ⟨by simpa using hop,har⟩) (fun x => by
    have h := congrFun spec x
    simpa [circuitFun,graphFun] using h) (fun i hop => by
    by_cases dirty : IsDirtyAnd 26 G C i.val
    · right
      intro a b c d ab cd yes yes'
      obtain ⟨u,v,uv,eu,pair,orient⟩ := orderedEdge ab
      obtain ⟨q,r,qr,eqr,pair',orient'⟩ := orderedEdge cd
      by_contra ne
      have distinct : (u,v) ≠ (q,r) := by
        intro he
        have := Prod.ext_iff.mp he
        rcases orient with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          rcases orient' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> grind
      apply absent
      exact ⟨i.val,dirty,u,v,q,r,eu,eqr,uv,qr,distinct,pair ▸ yes,pair' ▸ yes'⟩
    · left
      intro x on
      by_contra no
      apply dirty
      refine ⟨?_,i.isLt,x,on,?_⟩
      · simpa [gateAt,List.getD,i.isLt] using hop
      · simpa [graphFun,no])
  have lb := covers T cv
  rw [edgeCount] at sz'
  change C.gates.length ≤ 55 at sz
  omega

end PEqualNP.Outside.L_meta_18571

theorem PEqualNP.Outside.L_meta_18571 : let x1 : SimpleGraph (Fin (26 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x1 : ℕ) => List.filterMap (fun (x2 : ℕ) => if (x1 + (13 : ℕ) - x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] then Option.some (x1 + (1 : ℕ), x2 + (14 : ℕ)) else Option.none) (List.range (12 : ℕ))) (List.range (12 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (55 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ → ∃ (x6 : ℕ), PEqualNP.CleanedNonEdge.IsDirtyAnd (26 : ℕ) x1 x2 x6 ∧ ∃ (x7 : Fin (26 : ℕ)) (x8 : Fin (26 : ℕ)) (x9 : Fin (26 : ℕ)) (x10 : Fin (26 : ℕ)), x1.Adj x7 x8 ∧ x1.Adj x9 x10 ∧ x7 < x8 ∧ x9 < x10 ∧ (x7, x8) ≠ (x9, x10) ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
  exact PEqualNP.Outside.L_meta_18571.specialize PEqualNP.Outside.L_meta_18571_aux.countDonor
