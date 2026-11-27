import Mathlib
import PEqualNP.Defs

-- Wire semantics and singleton supports adapted from copsrlpond, merged PR 2889.
namespace PEqualNP.Outside.L_meta_4913

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


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool), (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hop

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

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha
  rw [pos_gate G gs ops clean w lo hi,ha]
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


inductive Used (k N r : ℕ) (a b : ℕ → ℕ) : ℕ → Prop where
  | root : Used k N r a b r
  | left {w : ℕ} : Used k N r a b w → k ≤ w → w < N → Used k N r a b (a w)
  | right {w : ℕ} : Used k N r a b w → k ≤ w → w < N → Used k N r a b (b w)

def linearSet {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool) : Finset ℕ :=
  (Finset.Ico k N).filter (fun w => A w = false ∧ (S (a w)).Nonempty ∧ (S (b w)).Nonempty)

noncomputable def productSet {n : ℕ} (k N r : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico k N).filter (fun w => Used k N r a b w ∧ A w = true ∧ (S (a w)).Nonempty ∧ (S (b w)).Nonempty)


theorem used_parent {k N r w : ℕ} {a b : ℕ → ℕ} (h : Used k N r a b w) :
    w = r ∨ ∃ v, Used k N r a b v ∧ k ≤ v ∧ v < N ∧ (a v = w ∨ b v = w) := by
  cases h with
  | root => exact Or.inl rfl
  | left h lo hi => exact Or.inr ⟨_,h,lo,hi,Or.inl rfl⟩
  | right h lo hi => exact Or.inr ⟨_,h,lo,hi,Or.inr rfl⟩

theorem budgetCount {n : ℕ} (k N r : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hor : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hand : ∀ w, k ≤ w → w < N → A w = true → S w = ∅) :
    (linearSet k N S a b A).card + (productSet k N r S a b A).card +
      ((productSet k N r S a b A).card-1) ≤ N-k := by
  classical
  let V := Finset.Ico k N
  let P := productSet k N r S a b A
  let L := linearSet k N S a b A
  let Z := V.filter fun z => Used k N r a b z ∧ S z = ∅
  let Q := Z \ P
  let W := V \ (P ∪ L)
  let pick := fun v => if a v ∈ Z then a v else b v
  change L.card + P.card + (P.card - 1) ≤ N-k
  have zp {v} (h : v ∈ Z) : Used k N r a b v ∧ S v = ∅ := (Finset.mem_filter.mp h).2
  have pp {v} (h : v ∈ P) : v ∈ V ∧ Used k N r a b v ∧ A v = true ∧
      (S (a v)).Nonempty ∧ (S (b v)).Nonempty := Finset.mem_filter.mp h
  have lp {v} (h : v ∈ L) : v ∈ V ∧ A v = false ∧
      (S (a v)).Nonempty ∧ (S (b v)).Nonempty := Finset.mem_filter.mp h
  have pv : P ⊆ V := fun _ h => (pp h).1
  have lv : L ⊆ V := fun _ h => (lp h).1
  have hpz : P ⊆ Z := by
    intro v hv
    obtain ⟨hv,hu,hA,_,_⟩ := pp hv
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hv
    exact Finset.mem_filter.mpr ⟨hv,hu,hand v lo hi hA⟩
  have pld : Disjoint P L := Finset.disjoint_left.mpr fun v hp hl => by
    have ht := (pp hp).2.2.1
    have hf := (lp hl).2.1
    simp_all
  have cover : Z ⊆ insert r ((W.image pick) ∪ Q.image b) := by
    intro z hz
    obtain hroot | ⟨v,hused,lo,hi,he⟩ := used_parent (zp hz).1
    · exact Finset.mem_insert.mpr (Or.inl hroot)
    apply Finset.mem_insert_of_mem
    have hv : v ∈ V := Finset.mem_Ico.mpr ⟨lo,hi⟩
    have noBoth : ¬ ((S (a v)).Nonempty ∧ (S (b v)).Nonempty) := by
      intro h
      rcases he with hleft | hright
      · exact (h.1.ne_empty (hleft ▸ (zp hz).2))
      · exact (h.2.ne_empty (hright ▸ (zp hz).2))
    have hnP : v ∉ P := fun hp => noBoth (pp hp).2.2.2
    have hnL : v ∉ L := fun hl => noBoth (lp hl).2.2
    have hw : v ∈ W := Finset.mem_sdiff.mpr ⟨hv,fun h => (Finset.mem_union.mp h).elim hnP hnL⟩
    by_cases heq : pick v = z
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hw,heq⟩)
    · have leftZ : a v ∈ Z := by
        by_contra h
        rcases he with hleft | hright
        · exact h (hleft ▸ hz)
        · exact heq (by simpa [pick,h] using hright)
      have rb : b v = z := he.resolve_left (fun eq => heq (by simpa [pick,leftZ] using eq))
      have rightZ : b v ∈ Z := rb ▸ hz
      have empty : S v = ∅ := by
        cases aa : A v with
        | false => rw [hor v lo hi aa,(zp leftZ).2,(zp rightZ).2,Finset.empty_union]
        | true => exact hand v lo hi aa
      have hq : v ∈ Q := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hv,hused,empty⟩,hnP⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hq,rb⟩)
  have sz : Z.card ≤ W.card + Q.card + 1 := calc
    Z.card ≤ (insert r ((W.image pick) ∪ Q.image b)).card := Finset.card_le_card cover
    _ ≤ ((W.image pick) ∪ Q.image b).card+1 := Finset.card_insert_le _ _
    _ ≤ (W.image pick).card + (Q.image b).card + 1 := Nat.add_le_add_right (Finset.card_union_le ..) 1
    _ ≤ W.card + Q.card + 1 := Nat.add_le_add_right (Nat.add_le_add Finset.card_image_le Finset.card_image_le) 1
  have zcount : Q.card + P.card = Z.card := Finset.card_sdiff_add_card_eq_card hpz
  have vcount : W.card + (P∪L).card = V.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.union_subset pv lv)
  rw [Finset.card_union_of_disjoint pld] at vcount
  have vlen : V.card = N-k := Nat.card_Ico _ _
  omega

-- Strengthen the edge_birth induction of copsrlpond (merged PR #2889) to the cone of the output.
theorem birthInCone (n k N root w : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hw : w < N) (used : Used k N root a b w) (hit : H w x y)
    (hx : x ∉ S w) (hy : y ∉ S w)
    (hinput : ∀ j u v, j < k → H j u v → u ∈ S j ∨ v ∈ S j)
    (ha : ∀ j, k ≤ j → j < N → a j < j) (hb : ∀ j, k ≤ j → j < N → b j < j)
    (horS : ∀ j, k ≤ j → j < N → A j = false → S j = S (a j) ∪ S (b j))
    (horH : ∀ j u v, k ≤ j → j < N → A j = false → H j u v →
      H (a j) u v ∨ H (b j) u v)
    (handH : ∀ j u v, k ≤ j → j < N → A j = true → H j u v →
      H (a j) u v ∧ H (b j) u v)
    (hdisj : ∀ j, k ≤ j → j < N → A j = true → Disjoint (S (a j)) (S (b j))) :
    ∃ j ∈ productSet k N root S a b A,
      ((x ∈ S (a j) ∧ y ∈ S (b j)) ∨ (y ∈ S (a j) ∧ x ∈ S (b j))) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind j ih =>
    by_cases lo : k ≤ j
    · have hja := ha j lo hw
      have hjb := hb j lo hw
      have ua := Used.left used lo hw
      have ub := Used.right used lo hw
      cases hop : A j with
      | false =>
        rw [horS j lo hw hop, Finset.mem_union] at hx hy
        rcases horH j x y lo hw hop hit with h | h
        · exact ih _ hja (hja.trans hw) ua h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hjb (hjb.trans hw) ub h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have both := handH j x y lo hw hop hit
        by_cases left : x ∈ S (a j) ∨ y ∈ S (a j)
        · by_cases right : x ∈ S (b j) ∨ y ∈ S (b j)
          · have orient : (x ∈ S (a j) ∧ y ∈ S (b j)) ∨ (y ∈ S (a j) ∧ x ∈ S (b j)) := by
              have dis := Finset.disjoint_left.mp (hdisj j lo hw hop)
              rcases left with h | h <;> rcases right with h' | h'
              · exact (dis h h').elim
              · exact .inl ⟨h, h'⟩
              · exact .inr ⟨h, h'⟩
              · exact (dis h h').elim
            refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨lo, hw⟩, used, hop, ?_⟩, orient⟩
            rcases orient with ⟨h,h'⟩ | ⟨h,h'⟩ <;> exact ⟨⟨_,h⟩,⟨_,h'⟩⟩
          · exact ih _ hjb (hjb.trans hw) ub both.2 (fun h => right (.inl h)) (fun h => right (.inr h))
        · exact ih _ hja (hja.trans hw) ua both.1 (fun h => left (.inl h)) (fun h => left (.inr h))
    · exact (hinput j x y (Nat.lt_of_not_ge lo) hit).elim (fun h => (hx h).elim) (fun h => (hy h).elim)

theorem productCover (n : ℕ) (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    PEqualNP.BicliqueBlockCost.IsBlockCover G
      ((productSet (n+1) (n+1+gs.length) (clampWire (n+gs.length) out)
        (supports (n:=n) gs) (firstWire n gs) (secondWire n gs) (andPos n gs)).image
        (fun j => (supports gs (firstWire n gs j), supports gs (secondWire n gs j)))) := by
  classical
  have hd (j : ℕ) (lo : n+1 ≤ j) (hi : j < n+1+gs.length) (hop : andPos n gs j = true) :
      Disjoint (supports (n:=n) gs (firstWire n gs j)) (supports gs (secondWire n gs j)) := by
    apply Finset.disjoint_left.mpr
    intro u h h'
    exact G.loopless.irrefl u (cross_support G gs ops clean j lo hi hop u h u h')
  constructor
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hj, _, hop, hleft, hright⟩ := Finset.mem_filter.mp hj
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hj
    exact ⟨hd j lo hi hop, hleft, hright, cross_support G gs ops clean j lo hi hop⟩
  · intro x y hxy
    let root := clampWire (n+gs.length) out
    have hempty := root_support_empty G gs out heval
    obtain ⟨j, hj, h⟩ := birthInCone n (n+1) (n+1+gs.length) root root (supports gs)
      (fun j x y => posRead gs j (pairBits x y) = true) (firstWire n gs) (secondWire n gs)
      (andPos n gs) x y (root_bound n gs.length out) .root (root_hits G gs out heval x y hxy)
      (by simp [root,hempty]) (by simp [root,hempty]) (hit_base gs)
      (fun j lo _ => clamp_lt j _ (by omega)) (fun j lo _ => clamp_lt j _ (by omega))
      (support_or G gs ops clean)
      (fun j u v lo hi hop h => by
        simpa only [pos_gate G gs ops clean j lo hi,hop,Bool.false_eq_true,ite_false,Bool.or_eq_true] using h)
      (fun j u v lo hi hop h => by
        simpa only [pos_gate G gs ops clean j lo hi,hop,ite_true,Bool.and_eq_true] using h) hd
    exact ⟨_,Finset.mem_image_of_mem _ hj,h⟩

open PEqualNP.SharedBlockCost

private def snocOr (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a,b]⟩], 0⟩

private lemma snoc_or_ok {n : ℕ} (C : Circuit) (hC : IsOrCircuit n C) (a b : ℕ)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) : IsOrCircuit n (snocOr C a b) := by
  intro j hj
  by_cases h : j < C.gates.length
  · simpa only [snocOr, List.getElem_append_left h] using hC j h
  · have eq : j = C.gates.length := by simp [snocOr] at hj; omega
    subst j
    simp [snocOr,isOrOp,ha,hb]

private lemma snoc_or_keep {n : ℕ} (C : Circuit) (a b r : ℕ) (U : Finset (Fin n))
    (hr : ComputesOr n C r U) : ComputesOr n (snocOr C a b) r U := by
  refine ⟨by have := hr.1; simp [snocOr]; omega, ?_⟩
  intro x
  have eq : PEqualNP.BlindGate.wireValue (snocOr C a b) n x r = PEqualNP.BlindGate.wireValue C n x r := by
    change (wiresFrom (C.gates ++ [_]) (List.ofFn x)).getD r false = _
    rw [wiresFrom_append]
    apply getD_wiresFrom_lt
    simpa [length_wiresFrom] using hr.1
  rw [eq]
  exact hr.2 x

private lemma snoc_or_new {n : ℕ} (C : Circuit) (a b : ℕ) (U V : Finset (Fin n))
    (ha : ComputesOr n C a U) (hb : ComputesOr n C b V) :
    ComputesOr n (snocOr C a b) (n + C.gates.length) (U ∪ V) := by
  refine ⟨by simp [snocOr], ?_⟩
  intro x
  let w := wiresFrom C.gates (List.ofFn x)
  have hl : w.length = n + C.gates.length := by simp [w,length_wiresFrom]
  have he : PEqualNP.BlindGate.wireValue (snocOr C a b) n x (n + C.gates.length) =
      (PEqualNP.BlindGate.wireValue C n x a || PEqualNP.BlindGate.wireValue C n x b) := by
    change (wiresFrom (C.gates ++ [_]) (List.ofFn x)).getD (n + C.gates.length) false = _
    rw [wiresFrom_append, ←hl]
    change (w ++ [GateOp.or.eval [w.getD a false, w.getD b false]]).getD w.length false = _
    rw [getD_snoc_eq]
    change GateOp.or.eval [w.getD a false, w.getD b false] = (w.getD a false || w.getD b false)
    simp [GateOp.eval]
  rw [he, Bool.or_eq_true, ha.2 x, hb.2 x]
  simp only [Finset.mem_union]
  grind

private lemma input_or {n : ℕ} (C : Circuit) (j : Fin n) : ComputesOr n C j {j} := by
  refine ⟨by have := j.isLt; omega, ?_⟩
  intro x
  change (wiresFrom C.gates (List.ofFn x)).getD j.val false = true ↔ _
  rw [getD_wiresFrom_lt _ _ _ (by simp)]
  simp [j.isLt]

theorem synthSides {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (ops : binaryOps C.gates)
    (clean : cleanOn G C.gates) :
    ∃ D : Circuit, IsOrCircuit n D ∧ D.gates.length ≤
      (linearSet (n+1) (n+1+C.gates.length) (supports (n:=n) C.gates) (firstWire n C.gates)
        (secondWire n C.gates) (andPos n C.gates)).card ∧
      ∀ w < n+1+C.gates.length, (supports (n:=n) C.gates w).Nonempty →
        ∃ r, ComputesOr n D r (supports (n:=n) C.gates w) := by
  classical
  let N := n+1+C.gates.length
  let S : ℕ → Finset (Fin n) := supports C.gates
  let a := firstWire n C.gates
  let b := secondWire n C.gates
  let A := andPos n C.gates
  let L := linearSet (n+1) N S a b A
  let cost (t : ℕ) := ((Finset.range t).filter (fun w => w ∈ L)).card
  have step (t : ℕ) : cost (t+1) = cost t + (if t ∈ L then 1 else 0) := by
    by_cases h : t ∈ L <;> simp [cost, Finset.range_add_one, Finset.filter_insert, h]
  have run (t : ℕ) (ht : t ≤ N) : ∃ D : Circuit, IsOrCircuit n D ∧ D.gates.length ≤ cost t ∧
      ∀ w < t, (S w).Nonempty → ∃ r, ComputesOr n D r (S w) := by
    induction t with
    | zero => exact ⟨⟨[],0⟩, by intro j hj; simp at hj, by simp [cost], by simp⟩
    | succ t ih =>
      have htN : t < N := by omega
      obtain ⟨D, hD, hlen, seen⟩ := ih (by omega)
      by_cases pay : t ∈ L
      · obtain ⟨hI,hr,hn₁,hn₂⟩ := Finset.mem_filter.mp pay
        have lo : n+1 ≤ t := (Finset.mem_Ico.mp hI).1
        have ha : a t < t := clamp_lt _ _ (by omega)
        have hb : b t < t := clamp_lt _ _ (by omega)
        obtain ⟨r,er⟩ := seen _ ha hn₁
        obtain ⟨s,es⟩ := seen _ hb hn₂
        refine ⟨snocOr D r s, snoc_or_ok D hD _ _ er.1 es.1, ?_, ?_⟩
        · simpa [snocOr,step,pay] using Nat.add_le_add_right hlen 1
        · intro w hw hwS
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with prev | he
          · obtain ⟨p,hp⟩ := seen w prev hwS
            exact ⟨p,snoc_or_keep D r s p (S w) hp⟩
          · subst w
            have eq : S t = S (a t) ∪ S (b t) := support_or G C.gates ops clean t lo htN hr
            rw [eq]
            exact ⟨_,snoc_or_new D r s _ _ er es⟩
      · refine ⟨D,hD,by simpa [step,pay] using hlen,?_⟩
        intro w hw hwS
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with prev | he
        · exact seen w prev hwS
        · subst w
          by_cases lo : n+1 ≤ t
          · cases hr : A t with
            | true =>
              have eq : S t = ∅ := support_and G C.gates clean t lo htN hr
              simp [eq] at hwS
            | false =>
              have eq : S t = S (a t) ∪ S (b t) := support_or G C.gates ops clean t lo htN hr
              have ha : a t < t := clamp_lt _ _ (by omega)
              have hb : b t < t := clamp_lt _ _ (by omega)
              by_cases h₁ : (S (a t)).Nonempty
              · have neg : ¬ (S (b t)).Nonempty := fun h₂ => pay (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨lo,htN⟩,hr,h₁,h₂⟩)
                have single : S t = S (a t) := by simpa [Finset.not_nonempty_iff_eq_empty.mp neg] using eq
                rw [single]
                exact seen _ ha h₁
              · have single : S t = S (b t) := by simpa [Finset.not_nonempty_iff_eq_empty.mp h₁] using eq
                rw [single] at hwS ⊢
                exact seen _ hb hwS
          · cases t with
            | zero => simp [S,supports,posRead] at hwS
            | succ j =>
              have hj : j < n := by omega
              have eq : S (j+1) = {⟨j,hj⟩} := by
                ext u
                simp [S,mem_support,pos_input C.gates j hj,singletonBits,eq_comm]
              rw [eq]
              exact ⟨j,input_or D ⟨j,hj⟩⟩
  obtain ⟨D, ok, le, wires⟩ := run N le_rfl
  refine ⟨D,ok,?_ ,wires⟩
  have eq : (Finset.range N).filter (fun w => w ∈ L) = L := by
    ext w
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).2,h⟩
  simpa only [cost,eq] using le

open PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost

theorem shared_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ops : binaryOps C.gates) (clean : cleanOn G C.gates)
    (heval : ∀ x, C.eval (List.ofFn x) = true ↔ edgeTrue G x) : HasSharedBlockCost G C.size := by
  classical
  let k := n+1
  let N := n+1+C.gates.length
  let r := clampWire (n+C.gates.length) C.output
  let S : ℕ → Finset (Fin n) := supports C.gates
  let a := firstWire n C.gates
  let b := secondWire n C.gates
  let A := andPos n C.gates
  let P := productSet k N r S a b A
  let L := linearSet k N S a b A
  let pair := fun j => (S (a j), S (b j))
  let F := P.image pair
  have hF : IsBlockCover G F := productCover n G C.gates C.output ops clean heval
  obtain ⟨D,hD,hcost,serves⟩ := synthSides G C ops clean
  have count : L.card + P.card + (P.card-1) ≤ N-k :=
    budgetCount k N r S a b A (support_or G C.gates ops clean) (support_and G C.gates clean)
  have plen : F.card ≤ P.card := Finset.card_image_le
  have cost : D.gates.length ≤ L.card := hcost
  have gateRange (j : ℕ) (mem : j ∈ P) : k ≤ j ∧ j < N ∧ (S (a j)).Nonempty ∧ (S (b j)).Nonempty := by
    obtain ⟨range,_,_,left,right⟩ := Finset.mem_filter.mp mem
    exact ⟨(Finset.mem_Ico.mp range).1,(Finset.mem_Ico.mp range).2,left,right⟩
  have earlier (j : ℕ) (hj : k ≤ j) : a j < j ∧ b j < j :=
    ⟨clamp_lt j _ (by dsimp [k] at hj; omega),clamp_lt j _ (by dsimp [k] at hj; omega)⟩
  refine ⟨F,hF,D.gates.length,⟨D,⟨hD,?_⟩,le_rfl⟩,?_⟩
  · intro T hT
    rcases Finset.mem_union.mp hT with hleft | hright
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hleft
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
      have h := gateRange j hj
      obtain ⟨w,hw⟩ := serves (a j) ((earlier j h.1).1.trans h.2.1) h.2.2.1
      exact ⟨w,hw.1,hw⟩
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hright
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
      have h := gateRange j hj
      obtain ⟨w,hw⟩ := serves (b j) ((earlier j h.1).2.trans h.2.1) h.2.2.2
      exact ⟨w,hw.1,hw⟩
  · change D.gates.length + F.card + (F.card - 1) ≤ C.gates.length
    dsimp [N,k] at count
    omega


end PEqualNP.Outside.L_meta_4913

theorem PEqualNP.Outside.L_meta_4913 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Fin x1 → Bool), x3.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x10 : Fin x1 → Bool), (x3.wires (List.ofFn x10)).getD (x1 + x6) Bool.false = Bool.true → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x10 x12 = Bool.true ∧ x10 x13 = Bool.true) → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x3.size := by
  intro n G C ops eval clean
  apply PEqualNP.Outside.L_meta_4913.shared_bound G C ops _ eval
  intro i x ha ht
  exact clean i.val (C.gates.get i) (by simp [List.get_eq_getElem]) ha x ht
