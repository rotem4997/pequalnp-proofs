import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18946

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact Finset.mem_range.mpr (by omega)

theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega

theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

theorem val_zero (hS : Strict n D) (w : ℕ) : val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS _ (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_units (n : ℕ) (D : Dag) : (units n D).card = totalSurplus n D := by
  rw [units, Finset.card_sigma, totalSurplus, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem card_unitsOn (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (unitsOn n D K).card = surplusOn D K := by
  rw [unitsOn, sb_card_units_filter n D (fun w => w ∈ K), Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hK]

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  (∀ x : Fin n → Bool, sem_Edge G x → val D x (outW n D) = true) ∧ (∀ u v : Fin n, val D (fun i => decide (i = u) || decide (i = v)) (outW n D) = true → G u v)

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => hG.2.1 v (hC.2 v v (by simpa only [Bool.or_self] using (show val D (fun i => decide (i = v)) (outW n D) = true from (mem_supp.mp hv)))))

theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := hC.1 _ h2
  rw [← hout] at h3
  exact huz (hC.2 u z h3)

theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, hC.1 _ (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

theorem sem_inelig_or (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {j : ℕ} (hj : j < D.length) (hc : v ∈ supp n D (n + j)) :
    tag D j = false := by
  obtain ⟨e, -, -, -, -, -, -, hmer⟩ := sem_inelig_consumer hG h hC hv
  by_contra ht
  rw [Bool.not_eq_false] at ht
  have hc2 := hc
  rw [sem_supp_and h.1 hj ht, Finset.mem_inter] at hc2
  have : j ∈ merges n D (carrierT n D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sem_mem_carrier1.mpr hc, sem_mem_carrier1.mpr hc2.1, sem_mem_carrier1.mpr hc2.2⟩
  rw [hmer] at this
  exact Finset.notMem_empty _ this

theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

theorem sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {F : Fin n → Fin n → Prop} (hUpper : ∀ x, val D x (outW n D) = true → sem_Edge F x)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ F a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := hC.1 _ h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA (hUpper _ h3)

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

end SemCore

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

theorem sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

theorem sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

theorem sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

end SemCodes

theorem sem_rtg_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a a' b, R a b → R a' b → a = a') {u v c : α}
    (hu : Relation.ReflTransGen R u c) (hv : Relation.ReflTransGen R v c) :
    Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u := by
  induction hu with
  | refl => exact Or.inr hv
  | tail hab hbc ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨b', hvb', hb'c⟩
    · left
      rw [← h]
      exact Relation.ReflTransGen.tail hab hbc
    · have hbb : b' = _ := hfun _ _ _ hb'c hbc
      rw [hbb] at hvb'
      exact ih hvb'

def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

theorem sem_exists_minBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_MinBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b ∧
        ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b ≤ w := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hex
      have hch : sem_Chain n D v.val (Nat.find hex) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hex hu
          by_contra hc
          exact this ⟨by omega, huv⟩)
      exact ⟨Nat.find hex, fun _ => ⟨h1, Finset.Subset.antisymm
        (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2),
        hch, fun w hw1 hw2 => Nat.find_min' hex ⟨hw1, hw2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_minBranch_first {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : sem_FirstBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1, (hb v hv).2.2.1⟩

theorem sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (hx : x ∈ supp n D (n + j)) :
    tag D j = false ∧ ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
  have hnot : ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
    intro hc
    have hm : j ∈ merges n D (carrierT n D {x}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hc.1, sem_mem_carrier1.mpr hc.2⟩
    rw [hM] at hm
    exact Finset.notMem_empty _ hm
  refine ⟨?_, hnot⟩
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx
  exact hnot hx

theorem sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card := by
  have h1 := sem_flow1 hG h hC x
  have h2 := surplus_carrierT_eq h.1 b hb {x}
  have h3 : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ {x}).Nonempty) =
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    refine Finset.filter_congr (fun u _ => ?_)
    constructor
    · rintro ⟨y, hy⟩
      rw [Finset.mem_inter, Finset.mem_singleton] at hy
      exact hy.2 ▸ hy.1
    · intro hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_singleton_self x⟩⟩
  rw [h3] at h2
  omega

theorem sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) :
    ∀ c, (∀ x ∈ X, x ∈ supp n D c) →
      (∀ x ∈ X, ∀ w, c ≤ w → x ∈ supp n D w → fanout D w ≤ 1) →
      ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
        Relation.ReflTransGen (sem_Arm n D X) c (src D e) := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  intro c
  generalize hk : n + D.length - c = k
  induction k using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc hlow
    have hclt := sem_supp_lt (hc x0 hx0)
    have hcne : c ≠ outW n D := by
      intro he
      have := hc x0 hx0
      rw [he, sem_supp_out hG hC] at this
      exact Finset.notMem_empty _ this
    have hf1 : 1 ≤ fanout D c := h.2.1 c (by unfold outW at hcne; omega)
    have hf : fanout D c = 1 := le_antisymm (hlow x0 hx0 c (le_refl c) (hc x0 hx0)) hf1
    obtain ⟨j, hjr⟩ := Finset.card_pos.mp hf1
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hjr
    obtain ⟨hj, hop⟩ := hjr
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = c := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    have hcj : c < n + j := hs ▸ sem_src_lt hS hj s
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hj hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hj ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hc x hx
        · right; rw [h1]; exact hc x hx
      obtain ⟨e, he1, he2⟩ := ih (n + D.length - (n + j)) (by omega) (n + j) rfl hall
        (fun x hx w hw => hlow x hx w (by omega))
      refine ⟨e, he1, Relation.ReflTransGen.head ⟨?_, hf, fun x hx => ⟨hc x hx, hall x hx⟩⟩ he2⟩
      rw [← hs]
      exact sem_step_src hj s
    · refine ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hj, ?_, fun hc2 => hcar ⟨x, hx, hc2⟩⟩, ?_⟩
      · rw [hs]; exact hc x hx
      · rw [hs]

theorem sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (show 1 < (readers D r).card from hf)
  have hread : ∀ j ∈ readers D r, j < D.length ∧ r < n + j ∧ (opA D j = r ∨ opB D j = r) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D r, ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hrj, hop⟩ := hread j hj
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = r := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hjl hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hjl ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hr x hx
        · right; rw [h1]; exact hr x hx
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hC X ⟨x0, hx0⟩ hM (n + j) hall
        (fun x hx w hw => hlow x hx w (by omega))
      exact ⟨e, he1, Or.inr he2⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩⟩
  have hRstep : ∀ a b, sem_Arm n D X a b → sem_step n D a b := fun _ _ hab => hab.1
  have hfun : ∀ a a' b, sem_Arm n D X a b → sem_Arm n D X a' b → a = a' := by
    intro a a' b h1 h2
    by_contra hne2
    obtain ⟨hb1, hb2, hba⟩ := h1.1
    obtain ⟨-, -, hba'⟩ := h2.1
    have hjb : b - n < D.length := by omega
    have hcarb : x0 ∈ supp n D (n + (b - n)) := by
      rw [Nat.add_sub_cancel' hb2]; exact (h1.2.2 x0 hx0).2
    apply (sem_zm_gate hS (hM x0 hx0) hjb hcarb).2
    have ha := (h1.2.2 x0 hx0).1
    have ha' := (h2.2.2 x0 hx0).1
    rcases hba with e1 | e1 <;> rcases hba' with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D r, ∀ jb ∈ readers D r, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm n D X) (n + ja) (n + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨hjla, hrja, -⟩ := hread ja hja
    obtain ⟨hjlb, hrjb, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = r := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS (hM x0 hx0) hjlb (hu2.2.2 x0 hx0).2).2
        have hu := (hu2.2.2 x0 hx0).1
        have hrr := hr x0 hx0
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hrr⟩
        · rw [e1, e2]; exact ⟨hrr, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hP1, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩⟩
  have hsame : Q = P := by
    rcases sem_same_gate hPQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hjP, hxP, hnP⟩ := sem_mem_W.mp (hP1 x0 hx0)
      have hxQ := (sem_mem_W.mp (hQ1 x0 hx0)).2.1
      rw [h1] at hxQ
      apply hnP
      rw [sem_supp_and hS hjP (sem_W_and hS (hP1 x0 hx0)), Finset.mem_inter]
      obtain ⟨j, s⟩ := P
      cases s
      · exact ⟨by simpa [src] using hxP, by simpa [src, sem_bar] using hxQ⟩
      · exact ⟨by simpa [src, sem_bar] using hxQ, by simpa [src] using hxP⟩
  rw [hsame] at hQ2
  obtain ⟨-, hrj1, -⟩ := hread j1 hj1
  obtain ⟨-, hrj2, -⟩ := hread j2 hj2
  rcases hP2 with ⟨hPa, hPb⟩ | hPp <;> rcases hQ2 with ⟨hQa, hQb⟩ | hQp
  · exact hne (hPa.symm.trans hQa)
  · have := sem_rtg_le hS hRstep hQp
    omega
  · have := sem_rtg_le hS hRstep hPp
    omega
  · rcases sem_rtg_comparable hfun hPp hQp with h1 | h1
    · exact hcross j1 hj1 j2 hj2 hne h1
    · exact hcross j2 hj2 j1 hj1 (Ne.symm hne) h1

theorem sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits n D b = {u0}) {x : Fin n} (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D ∧
      x ∈ supp n D u0.1 := by
  have h1 := sem_code_count hG h hC b hb x
  have h2 : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  rw [hres, Finset.card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, Finset.card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have h4 : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
      rw [Finset.singleton_inter_of_notMem hx]
    rw [h4, Finset.card_empty] at h1
    omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp n D u.1)).card := by
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h4
    rw [Finset.mem_filter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2

theorem sem_common_terminals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : sem_MinBranch n D b) (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  have hcard : (residualUnits n D b).card = 1 := by
    have := card_residual hS b hbp
    omega
  obtain ⟨u0, hres⟩ := Finset.card_eq_one.mp hcard
  have hu0 : u0 ∈ residualUnits n D b := by rw [hres]; exact Finset.mem_singleton_self _
  have hu0u : u0 ∈ units n D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.1)
    u0.1 (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, -, hxe, hxr⟩ := sem_saturated hG h hC b hbp hres (hsat x hx)
  by_contra hc
  have hw2 : 2 ≤ fanout D w := by omega
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩,
      ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have hwres : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b :=
      Finset.mem_sdiff.mpr ⟨hwu, hwr⟩
    rw [hres, Finset.mem_singleton] at hwres
    have : w = u0.1 := congrArg Sigma.fst hwres
    omega

end SemArms

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def dag (C : Circuit) : Dag :=
  C.gates.map fun g => (match g.op with | .and => true | _ => false,
    g.inputs.getD 0 0, g.inputs.getD 1 0)

theorem inputs_eq {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.size) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hg : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hl := h.2.2 _ hg
  unfold opnd
  generalize (gateAt C j).inputs = l at hl ⊢
  match l with
  | [] | [_] | _ :: _ :: _ :: _ => simp at hl
  | [a, b] => rfl

theorem dag_length (C : Circuit) : (dag C).length = C.size := by simp [dag, Circuit.size]

theorem dag_gate {C : Circuit} {j : ℕ} (hj : j < C.size) :
    tag (dag C) j = (match (gateAt C j).op with | .and => true | _ => false) ∧
    opA (dag C) j = opnd C j 0 ∧ opB (dag C) j = opnd C j 1 := by
  have hd : j < (dag C).length := by rwa [dag_length]
  rw [tag_eq _ _ hd, opA_eq _ _ hd, opB_eq _ _ hd]
  have hgate : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  simp [opnd, hgate, dag] <;> exact ⟨rfl, rfl, rfl⟩

theorem dag_strict {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hd : ∀ j < C.size, opnd C j 0 ≠ opnd C j 1) : Strict n (dag C) := by
  intro j hj
  rw [dag_length] at hj
  obtain ⟨-, ha, hb⟩ := dag_gate hj
  rw [ha, hb]
  exact ⟨h.2.1 j hj _ (by rw [inputs_eq h hj]; simp),
    h.2.1 j hj _ (by rw [inputs_eq h hj]; simp), hd j hj⟩

theorem dag_fanout {n : ℕ} {C : Circuit} (h : IsAO2 n C) (w : ℕ) :
    fanout (dag C) w = ((Finset.range C.size).filter
      fun j => w ∈ (gateAt C j).inputs).card := by
  unfold fanout readers
  rw [dag_length]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨hj, hw⟩ <;> refine ⟨hj, ?_⟩
  · obtain ⟨-, ha, hb⟩ := dag_gate hj
    simpa [ha, hb, inputs_eq h hj, eq_comm] using hw
  · obtain ⟨-, ha, hb⟩ := dag_gate hj
    simpa [ha, hb, inputs_eq h hj, eq_comm] using hw

theorem dag_wires {n : ℕ} {C : Circuit} (h : IsAO2 n C) (x : Fin n → Bool) :
    wl (dag C) (List.ofFn x) = C.wires (List.ofFn x) := by
  suffices fold_spec : ∀ (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (w : List Bool),
      wl (dag ⟨gs, 0⟩) w = (Circuit.mk gs 0).wires w from
    fold_spec C.gates (fun g hg => ⟨h.1 g hg, h.2.2 g hg⟩) (List.ofFn x)
  intro gs
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro hg w
    obtain ⟨hop, hl⟩ := hg _ (.head _)
    have hpair : ∃ a b, g.inputs = [a, b] := by
      cases he : g.inputs with
      | nil => simp [he] at hl
      | cons a l =>
        cases l with
        | nil => simp [he] at hl
        | cons b tail =>
          cases tail with
          | nil => exact ⟨a, b, rfl⟩
          | cons c tail => simp [he] at hl
    obtain ⟨a, b, hi⟩ := hpair
    have step_eq : wstep w (match g.op with | .and => true | _ => false,
        g.inputs.getD 0 0, g.inputs.getD 1 0) =
        w ++ [g.op.eval (g.inputs.map fun w' => w.getD w' false)] := by
      rcases hop with hop | hop <;> simp [wstep, hop, hi, GateOp.eval] <;> rfl
    change wl (dag ⟨gs, 0⟩) _ = (Circuit.mk gs 0).wires _
    rw [step_eq]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _

theorem dag_live {C : Circuit} (h : IsAO2 14 C)
    (hl : ∀ w < 13 + C.size, ∃ j < C.size, w ∈ (gateAt C j).inputs) :
    Live 14 (dag C) := by
  intro w hw
  rw [dag_length] at hw
  obtain ⟨j, hj, hmem⟩ := hl w (by omega)
  rw [dag_fanout h]
  exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hmem⟩⟩

theorem dag_elig {C : Circuit} (h : IsAO2 14 C)
    (hd : ∀ j < C.size, opnd C j 0 ≠ opnd C j 1) :
    (eligSet 14 (dag C)).card = ((Finset.range 14).filter fun v : ℕ =>
      ∃ w < 13 + C.size, 2 ≤ ((Finset.range C.size).filter
        fun j => w ∈ (gateAt C j).inputs).card ∧
        (C.wires (List.ofFn fun i : Fin 14 => decide (i.val = v))).getD w false = true).card := by
  rw [← Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext v
  rw [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨w, hw, hs⟩ := mem_eligSet.mp hi
    have hlt := lt_of_fanout_pos (D := dag C) (n := 14) (w := w)
    have hstrict := dag_strict h hd
    exact ⟨i.isLt, w, (by have := hlt hstrict (by omega); rw [dag_length] at this; omega),
      (dag_fanout h w) ▸ hw, by
        have hv := mem_supp.mp hs
        unfold val at hv
        rw [dag_wires h] at hv
        change (C.wires (List.ofFn fun k : Fin 14 => decide (k = i))).getD w false = true at hv
        simpa only [Fin.ext_iff] using hv⟩
  · rintro ⟨hv, w, -, hw, hs⟩
    refine ⟨⟨v, hv⟩, mem_eligSet.mpr ⟨w, (dag_fanout h w).symm ▸ hw, mem_supp.mpr ?_⟩, rfl⟩
    unfold val
    rw [dag_wires h]
    change (C.wires (List.ofFn fun k : Fin 14 => decide (k = ⟨v, hv⟩))).getD w false = true
    simpa only [Fin.ext_iff] using hs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev V := Fin 14
abbrev Slot := ℕ × Bool

def leftInc (x y : V) : Prop :=
  x.val < 7 ∧ 7 ≤ y.val ∧ (x.val + 14 - y.val) % 7 ∈ ([0,1,3] : List ℕ)

abbrev fullAdj (x y : V) := leftInc x y ∨ leftInc y x
abbrev cutAdj (x y : V) := fullAdj x y ∧ ¬ (x = 0 ∧ y = 7 ∨ y = 0 ∧ x = 7)

instance (x y : V) : Decidable (leftInc x y) := by unfold leftInc; infer_instance

theorem graphReg : sem_Gr cutAdj := by
  refine ⟨?_,?_,?_,?_⟩ <;>
  decide +kernel

theorem full_of_line : ∀ p l : Fin 7, p ∈ fanoLines l →
    fullAdj (Fin.castAdd 7 p) (Fin.natAdd 7 l) := by decide +kernel

theorem cut_line {x y : V} (h : cutAdj x y) :
    ∃ p l : Fin 7, p ∈ fanoLines l ∧ (p ≠ 0 ∨ l ≠ 0) ∧
      ((x = Fin.castAdd 7 p ∧ y = Fin.natAdd 7 l) ∨
       (y = Fin.castAdd 7 p ∧ x = Fin.natAdd 7 l)) := by
  revert x y
  decide +kernel

theorem graph_bridge {C : Circuit} (ha : IsAO2 14 C) (hs : Strict 14 (dag C))
    (ho : C.output = 13 + C.size)
    (hu : ∀ x : V → Bool, C.eval (List.ofFn x) = true →
      ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (hl : ∀ p l : Fin 7, p ∈ fanoLines l → p ≠ 0 ∨ l ≠ 0 →
      C.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true)
    (hn : C.eval (List.ofFn (pairInput (0 : V) 7)) = false) :
    sem_Comp 14 cutAdj (dag C) ∧
    (∀ x, val (dag C) x (outW 14 (dag C)) = true → sem_Edge fullAdj x) := by
  have ev (x : V → Bool) : val (dag C) x (outW 14 (dag C)) = C.eval (List.ofFn x) := by
    unfold val outW Circuit.eval
    rw [dag_wires ha, dag_length, ho]
    congr 1 <;> omega
  have upper (x : V → Bool) (h : val (dag C) x (outW 14 (dag C)) = true) : sem_Edge fullAdj x := by
    obtain ⟨p,l,hpl,hp,hl'⟩ := hu x (by rwa [← ev x])
    exact ⟨_, _, full_of_line p l hpl, hp, hl'⟩
  refine ⟨⟨?_,?_⟩,upper⟩
  · rintro x ⟨u,v,huv,hu',hv⟩
    obtain ⟨p,l,hpl,hne,hd⟩ := cut_line huv
    apply val_mono hs (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l)) x
    · intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hi with rfl | rfl <;> assumption
    · rw [ev]
      exact hl p l hpl hne
  · intro u v h
    obtain ⟨a,b,hab,ha',hb'⟩ := upper _ h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at ha' hb'
    have symm (j k : V) (hjk : fullAdj j k) : fullAdj k j := hjk.symm
    have irrefl : ∀ j : V, ¬ fullAdj j j := by decide +kernel
    refine ⟨?_,?_⟩
    · rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      all_goals first | exact hab | exact symm _ _ hab | exact False.elim (irrefl _ hab)
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      all_goals
        rw [ev] at h
        generalize hi : (fun i : V => _) = f at h
        have he : f = pairInput (0 : V) 7 := by
          rw [← hi]
          funext i
          simp [pairInput, Bool.decide_or, Bool.or_comm]
        rw [he, hn] at h
        contradiction

def ends (k : ℕ) : V × V := ([(0,11),(0,13),(1,7),(1,8),(1,12),(2,8),(2,9),(2,13),(3,7),(3,9),(3,10),(4,8),(4,10),(4,11),(5,9),(5,11),(5,12),(6,10),(6,12),(6,13)] : List (V × V)).getD k (0,0)

def label (p : ℕ) : V := if p % 2 = 0 then (ends (p / 2)).1 else (ends (p / 2)).2
def port (f : ℕ → Slot) (p : ℕ) : Slot := if p % 2 = 0 then f (p / 2) else sem_bar (f (p / 2))

def bad (x y z : V) : Prop := ¬fullAdj y z ∧ ∃ t, cutAdj x t ∧ ¬fullAdj y t ∧ ¬fullAdj z t
instance (x y z : V) : Decidable (bad x y z) := by unfold bad; infer_instance

structure Ports (tier : Bool) where
  gates : ℕ → Slot
  sets : V → Finset Slot
  lone : Finset V
  incidence : ∀ p, p < 40 → port gates p ∈ sets (label p)
  distinctTerm : (gates 20).1 ≠ (gates 21).1
  small : ∀ x, (sets x).card ≤ 3
  common : ∀ x, 2 < (sets x).card → gates 20 ∈ sets x ∧ gates 21 ∈ sets x
  singleSize : ∀ x ∈ lone, (sets x).card ≤ 1
  privatePort : ∀ x ∈ lone, ∀ y, x ≠ y → Disjoint (sets x) (sets y)
  independent : ∀ x ∈ lone, ∀ y ∈ lone, ¬cutAdj x y
  expose : ∀ x y z, bad x y z → ∃ a ∈ sets x, a ∉ sets y ∧ a ∉ sets z
  many : (if tier then 3 else 2) ≤ lone.card
  allShort : tier = false → ∀ x, (sets x).card ≤ 2

theorem make_ports {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 cutAdj D)
    (hu : ∀ x, val D x (outW 14 D) = true → sem_Edge fullAdj x)
    (he : 11 ≤ (eligSet 14 D).card) (hlen : D.length ≤ 25) :
    ∃ t, Nonempty (Ports t) := by
  classical
  let W := sem_W 14 D
  let E := eligSet 14 D
  let I := ineligSet 14 D
  have htot := surplus_identity h
  have hbp : Bplus 14 D ≤ 12 := by have := Bplus_le_total 14 D; omega
  obtain ⟨b,hb⟩ := sem_exists_minBranch graphReg h.1 hc
  have hpur := sem_minBranch_pure hb
  have hrc := card_residual h.1 b hpur
  have hbe := elig_le_Bplus h.1 b hpur
  have hsize (x : V) : (W x).card ≤ 2 + (residualUnits 14 D b).card := by
    have hf := sem_code_count graphReg h hc b hpur x
    have h1 : (({x} : Finset V) ∩ eligSet 14 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    have h2 := Finset.card_filter_le (residualUnits 14 D b) (fun u => x ∈ supp 14 D u.1)
    dsimp [W]
    omega
  have hdeg (x : V) : (W x).card ≤ 3 := by have := hsize x; omega
  have hI : I.card + E.card = 14 := by
    dsimp [I,E,ineligSet]
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)]
    decide
  let X := Finset.univ.filter fun x => 2 < (W x).card
  have hm : ∀ x, x ∈ X ↔ 2 < (W x).card := fun x => by simp [X]
  obtain ⟨tier,A,B,hAB,hports,hmany,hshort⟩ : ∃ (tier : Bool) (A B : Slot),
      A.1 ≠ B.1 ∧ (∀ x, 2 < (W x).card → A ∈ W x ∧ B ∈ W x) ∧
      (if tier then 3 else 2) ≤ I.card ∧ (tier = false → ∀ x, (W x).card ≤ 2) := by
    by_cases hx : X.Nonempty
    · obtain ⟨x,hx'⟩ := (show X.Nonempty from hx)
      have h3 := (hm x).mp hx'
      have := hsize x
      have heq : Bplus 14 D = (eligSet 14 D).card + 1 := by omega
      obtain ⟨A,B,hab,hp⟩ := sem_common_terminals graphReg h hc b hb heq X hx (fun i hi => (hm i).mp hi)
      exact ⟨true,A,B,hab,fun i hi => hp i ((hm i).mpr hi),by dsimp [E] at hI; simp; omega,by simp⟩
    · refine ⟨false,(0,false),(1,false),by decide,?_,?_,?_⟩
      · intro x ht; exact (hx ⟨x,(hm x).mpr ht⟩).elim
      · dsimp [E] at hI; simp; omega
      · intro _ x; exact Nat.le_of_not_gt (fun ht => hx ⟨x,(hm x).mpr ht⟩)
  have hedge : ∀ i : Fin 20, cutAdj (ends i).1 (ends i).2 := by decide +kernel
  choose f hf using fun i : Fin 20 => sem_edge_slots graphReg h.1 hc (hedge i)
  let g := fun k : ℕ => if hi : k < 20 then f ⟨k,hi⟩ else if k = 20 then A else B
  have gA : g 20 = A := by simp [g]
  have gB : g 21 = B := by simp [g]
  refine ⟨tier,⟨⟨g,W,I,?_,by simpa [gA,gB] using hAB,hdeg,by simpa [gA,gB] using hports,
    ?_,?_,?_,?_,hmany,hshort⟩⟩⟩
  · intro p hp
    have hi : p / 2 < 20 := by omega
    have hh := hf ⟨p/2,hi⟩
    by_cases hp' : p % 2 = 0
    · simpa [port,label,g,hi,hp',W] using hh.1
    · simpa [port,label,g,hi,hp',W] using hh.2.1
  · intro x hx
    obtain ⟨e,-,-,-,-,-,he',-⟩ := sem_inelig_consumer graphReg h hc hx
    simp [W,sem_W,he']
  · intro x hx y hxy
    apply Finset.disjoint_left.mpr
    intro e hex hey
    have hpx := (sem_mem_W.mp hex).2.1
    have hpy := (sem_mem_W.mp hey).2.1
    rw [sem_inelig_pure graphReg h.1 hc hx hpx, Finset.mem_singleton] at hpy
    exact hxy hpy.symm
  · intro x hx y hy hxy
    exact (sem_elig_cover graphReg h hc hxy).elim (sem_mem_inelig.mp hx) (sem_mem_inelig.mp hy)
  · rintro x y z ⟨hyz,t,hxt,hyt,hzt⟩
    let S : Finset V := {y,z,t}
    have ir : ∀ i : V, ¬fullAdj i i := by decide +kernel
    have symm (a b : V) (hab : fullAdj a b) : fullAdj b a := hab.symm
    have hi : ∀ a ∈ S, ∀ c ∈ S, ¬fullAdj a c := by
      simp only [S,Finset.mem_insert,Finset.mem_singleton]
      rintro a (rfl|rfl|rfl) c (rfl|rfl|rfl) <;> first | apply ir | assumption | exact fun hh => hyz (symm _ _ hh) | exact fun hh => hyt (symm _ _ hh) | exact fun hh => hzt (symm _ _ hh)
    obtain ⟨j,s,hj,-,hs,hn,hd⟩ := sem_exposure graphReg h.1 hc hu S hi x ⟨t,by simp [S],hxt⟩
    exact ⟨(j,s),sem_mem_W.mpr ⟨hj,hs,hn⟩,fun hy => Finset.disjoint_left.mp hd (sem_mem_W.mp hy).2.1 (by simp [S]),
      fun hz => Finset.disjoint_left.mp hd (sem_mem_W.mp hz).2.1 (by simp [S])⟩

namespace Rup
noncomputable section
def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

end Soundness
end
end Rup

def flipSlot (s : Slot) (b : Bool) : Slot := if b then sem_bar s else s

def codeBool (v : ℕ) (p : Bool) := 2*v + (if p then 0 else 1)

def pEq (a b : ℕ) (pos : Bool) : ℕ :=
  let i := a/2
  let j := b/2
  let d := (a%2 != b%2)
  if i = j then codeBool 1 (pos != d) else
    codeBool (30 + 2 * Nat.pair (min i j) (max i j) + (if d then 1 else 0)) pos

def pOne (x : V) := codeBool (2 + x.val)
def pShort (x : V) := codeBool (16 + x.val)

def assignment {t} (M : Ports t) (v : ℕ) : Bool :=
  if v < 2 then true else if v < 16 then decide ((⟨(v-2)%14,by omega⟩ : V) ∈ M.lone)
  else if v < 30 then decide ((M.sets ⟨(v-16)%14,by omega⟩).card ≤ 2)
  else
    let ij := Nat.unpair ((v-30)/2)
    decide (M.gates ij.1 = flipSlot (M.gates ij.2) ((v-30)%2 != 0))

variable {t : Bool} (M : Ports t)
def GoodLit (l : ℕ) := Rup.litVal (assignment M) l = true
theorem good_code (v : ℕ) (p : Bool) : GoodLit M (codeBool v p) ↔ assignment M v = p := by
  cases p <;> simp [GoodLit, codeBool,Rup.litVal, Nat.mul_add_div, Nat.add_mod, Nat.mul_mod]
@[simp] theorem good_one (x : V) (p : Bool) :
    GoodLit M (pOne x p) ↔ decide (x ∈ M.lone) = p := by
  rw [pOne,good_code]
  simp [assignment,show ¬(2+x.val < 2) by omega,show 2+x.val < 16 by omega, Nat.mod_eq_of_lt x.isLt]
@[simp] theorem good_short (x : V) (p : Bool) :
    GoodLit M (pShort x p) ↔ decide ((M.sets x).card ≤ 2) = p := by
  rw [pShort,good_code]
  simp [assignment,show ¬(16+x.val < 2) by omega,show ¬(16+x.val < 16) by omega,show 16+x.val < 30 by omega, Nat.mod_eq_of_lt x.isLt]

theorem flip_eq (a b : Slot) (u v : Bool) :
    (flipSlot a u = flipSlot b v) ↔ (a = flipSlot b (u != v)) := by
  cases u <;> cases v <;> simp [flipSlot,sem_bar,Prod.ext_iff]

theorem flip_eq_symm (a b : Slot) (u : Bool) :
    (a = flipSlot b u) ↔ (b = flipSlot a u) := by
  cases u <;> simp [flipSlot,sem_bar,Prod.ext_iff,eq_comm] <;> grind

theorem port_flip (f : ℕ → Slot) (a : ℕ) :
    port f a = flipSlot (f (a/2)) (a%2 != 0) := by by_cases h : a%2=0 <;> simp [port,flipSlot,h]

@[simp] theorem good_eq (a b : ℕ) (p : Bool) :
    GoodLit M (pEq a b p) ↔ decide (port M.gates a = port M.gates b) = p := by
  let i := a/2
  let j := b/2
  let u := (a%2 != 0)
  let v := (b%2 != 0)
  have hd : (a%2 != b%2) = (u != v) := by
    dsimp [u,v]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rcases Nat.mod_two_eq_zero_or_one b with k | k <;> simp [h,k]
  rw [port_flip,port_flip]
  change _ ↔ decide (flipSlot (M.gates i) u = flipSlot (M.gates j) v) = p
  simp only [flip_eq]
  unfold pEq
  rw [hd]
  change GoodLit M (if i=j then _ else _) ↔ _
  split
  · rename_i h
    rw [h,good_code]
    cases u <;> cases v <;> cases p <;> simp [assignment,flipSlot,sem_bar_ne,Ne.symm (sem_bar_ne _)]
  · rw [good_code]
    let k := Nat.pair (min i j) (max i j)
    have hh (n : ℕ) (s : Bool) :
        assignment M (30 + 2*n + (if s then 1 else 0)) =
          decide (M.gates (Nat.unpair n).1 = flipSlot (M.gates (Nat.unpair n).2) s) := by
      let m := 30 + 2*n + (if s then 1 else 0)
      have h30 : 30 ≤ m := by dsimp [m]; omega
      change assignment M m = _
      simp only [assignment,if_neg (show ¬m < 2 by omega),if_neg (show ¬m < 16 by omega),if_neg (show ¬m < 30 by omega)]
      have hv : (m-30)/2 = n := by dsimp [m]; split <;> omega
      have hs : ((m-30)%2 != 0) = s := by cases s <;> simp [m] <;> omega
      rw [hv,hs]
    rw [hh,Nat.unpair_pair]
    change decide (M.gates (min i j) = flipSlot (M.gates (max i j)) _) = p ↔ _
    rcases le_total i j with h | h
    · simp [min_eq_left h,max_eq_right h]
    · simp [min_eq_right h,max_eq_left h,flip_eq_symm (M.gates j) (M.gates i)]

def validClause (M : Ports t) (c : List ℕ) := Rup.ClauseSat (assignment M) c
@[simp] theorem valid_cons (l : ℕ) (c : List ℕ) :
    validClause M (l::c) ↔ GoodLit M l ∨ validClause M c := by
  simp [validClause,GoodLit,Rup.ClauseSat]
@[simp] theorem valid_nil : ¬validClause M [] := by simp [validClause,Rup.ClauseSat]
@[simp] theorem good_true : GoodLit M 2 := by change GoodLit M (codeBool 1 true); rw [good_code]; rfl

theorem smallCover {S : Finset Slot} {a b : Slot} (hs : S.card ≤ 2)
    (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : ∀ c ∈ S, c = a ∨ c = b := by
  intro c hc
  by_contra! hn
  exact (Nat.not_lt.mpr hs) (Finset.two_lt_card_iff.mpr ⟨c,a,b,hc,ha,hb,hn.1,hn.2,hne⟩)

theorem bigCover {S : Finset Slot} {a b c : Slot} (hs : S.card ≤ 3)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ d ∈ S, d = a ∨ d = b ∨ d = c := by
  intro d hd
  by_contra! hn
  exact (Nat.not_lt.mpr hs) (Finset.three_lt_card_iff.mpr
    ⟨d,a,b,c,hd,ha,hb,hc,hn.1,hn.2.1,hn.2.2,hab,hac,hbc⟩)

def guardC (h : Prop) [Decidable h] (c : List ℕ) := if h then c else [2]
theorem guard_ok {t} (M : Ports t) (h : Prop) [Decidable h] (c : List ℕ)
    (hh : h → validClause M c) : validClause M (guardC h c) := by
  by_cases h' : h <;> simp [guardC,h',hh]

def extra (i : ℕ) (y : V) (c : List ℕ) := if i < 40 then c else pShort y true :: c
abbrev owns (i : ℕ) (y : V) := (i < 40 ∧ label i = y) ∨ i = 40 ∨ i = 42

theorem extra_ok {t} (M : Ports t) (i : ℕ) (y : V) (c : List ℕ) (ho : owns i y)
    (hh : port M.gates i ∈ M.sets y → validClause M c) : validClause M (extra i y c) := by
  rcases ho with ⟨hi,rfl⟩ | rfl | rfl
  · simpa [extra,hi] using hh (M.incidence i hi)
  all_goals
    simp [extra]
    by_cases h : (M.sets y).card ≤ 2
    · exact Or.inl h
    · apply Or.inr
      apply hh
      first | exact (M.common y (by omega)).1 | exact (M.common y (by omega)).2

def vert (a : ℕ) : V := ⟨a%14,by omega⟩
def skipped (x y : V) := ((List.finRange 14).filter fun k => k != x && k != y).map (fun k => pOne k true)

def rule (t : Bool) (k a b c d e f : ℕ) : List ℕ :=
  let x := label a
  let y := vert e
  let z := vert f
  match k with
  | 0 => [pEq a b false,pEq b c false,pEq a c true]
  | 1 => guardC (a = 42 ∨ a = 43) [pEq 40 a false]
  | 2 => [pOne y false,pShort y true]
  | 3 => guardC (a < 40 ∧ b < 40 ∧ c < 40 ∧ label b = x ∧ label c = x)
      [pShort x false,pEq a b true,pEq a c true,pEq b c true]
  | 4 => guardC (a < 40 ∧ b < 40 ∧ label b = x) [pOne x false,pEq a b true]
  | 5 => guardC (a < 40 ∧ b < 40 ∧ label b = x)
      [pShort x true,pEq a b true,pEq a 40 true,pEq a 42 true,pEq b 40 true,pEq b 42 true]
  | 6 => guardC (a < 40 ∧ owns b y ∧ x ≠ y)
      (extra b y [pOne x false,pEq a b false])
  | 7 => guardC (a < 40 ∧ b < 40 ∧ label b = x ∧ owns c y ∧ owns d z ∧ bad x y z)
      (extra c y (extra d z [pShort x false,pEq a b true,pEq a c false,pEq b d false]))
  | 8 => guardC (a < 40 ∧ owns c y ∧ bad x y z)
      (extra c y [pShort x true,pEq a 40 true,pEq a 42 true,pShort z true,pEq c a false])
  | 9 => guardC (t = true ∨ y = z) (skipped y z)
  | 10 => guardC (cutAdj y z) [pOne y false,pOne z false]
  | 11 => guardC (t = false) [pShort y true]
  | _ => [2]

theorem rule_ok {t} (M : Ports t) (k a b c d e f : ℕ) : validClause M (rule t k a b c d e f) := by
  have td : port M.gates 40 ≠ port M.gates 42 := fun h => M.distinctTerm (congrArg Prod.fst h)
  have tm (x : V) (hx : 2 < (M.sets x).card) : port M.gates 40 ∈ M.sets x ∧ port M.gates 42 ∈ M.sets x := M.common x hx
  unfold rule
  split
  · simp; grind
  · apply guard_ok
    rintro (rfl|rfl) <;> simp only [valid_cons,valid_nil,or_false,good_eq,decide_eq_false_iff_not]
    · exact td
    · intro h
      have hgate := congrArg (fun q : Slot => q.1) h
      exact M.distinctTerm hgate
  · simp; by_cases hx : vert e ∈ M.lone
    · exact Or.inr ((M.singleSize _ hx).trans (by decide : 1 ≤ 2))
    · exact Or.inl hx
  · apply guard_ok
    rintro ⟨ha,hb,hc,he,hf⟩
    have h1 := M.incidence a ha
    have h2 := he ▸ M.incidence b hb
    have h3 := hf ▸ M.incidence c hc
    simp
    by_contra! hn
    exact (smallCover hn.1 h1 h2 hn.2.1 _ h3).elim (Ne.symm hn.2.2.1) (Ne.symm hn.2.2.2)
  · apply guard_ok
    rintro ⟨ha,hb,he⟩
    simp; by_cases hx : label a ∈ M.lone
    · right
      exact Finset.card_le_one.mp (M.singleSize _ hx) _ (M.incidence a ha) _ (he ▸ M.incidence b hb)
    · exact Or.inl hx
  · apply guard_ok
    rintro ⟨ha,hb,he⟩
    have h1 := M.incidence a ha
    have h2 := he ▸ M.incidence b hb
    simp
    by_contra! hn
    obtain ⟨hA,hB⟩ := tm _ hn.1
    have hh := bigCover (M.small _) h1 hA hB hn.2.2.1 hn.2.2.2.1 td _ h2
    grind
  · apply guard_ok
    rintro ⟨ha,ho,hne⟩
    apply extra_ok _ _ _ _ ho
    intro hb
    simp
    by_cases hx : label a ∈ M.lone
    · right; intro he
      exact Finset.disjoint_left.mp (M.privatePort _ hx _ hne) (M.incidence a ha) (he.symm ▸ hb)
    · exact Or.inl hx
  · apply guard_ok
    rintro ⟨ha,hb,he,ho,hp,hn⟩
    apply extra_ok _ _ _ _ ho; intro hi
    apply extra_ok _ _ _ _ hp; intro hj
    obtain ⟨q,hq,hy,hz⟩ := M.expose _ _ _ hn
    have h1 := M.incidence a ha
    have h2 := he ▸ M.incidence b hb
    simp
    by_contra! hh
    have := smallCover hh.1 h1 h2 hh.2.1 q hq
    grind
  · apply guard_ok
    rintro ⟨ha,ho,hn⟩
    apply extra_ok _ _ _ _ ho; intro hi
    obtain ⟨q,hq,hy,hz⟩ := M.expose _ _ _ hn
    simp
    by_contra! hh
    obtain ⟨hA,hB⟩ := tm _ hh.1
    obtain ⟨hzA,hzB⟩ := tm _ hh.2.2.2.1
    have := bigCover (M.small _) (M.incidence a ha) hA hB hh.2.1 hh.2.2.1 td q hq
    grind
  · apply guard_ok
    intro h
    have hn := M.many
    have hex : ∃ i ∈ M.lone, i ≠ vert e ∧ i ≠ vert f := by
      by_contra! hno
      have sub : M.lone ⊆ {vert e,vert f} := by
        intro i hi
        simp; specialize hno i hi; tauto
      have hb := Finset.card_le_card sub
      rcases h with ht | he
      · subst t
        have hh : ({vert e,vert f} : Finset V).card ≤ 2 := Finset.card_le_two
        simp at hn; omega
      · rw [he] at hb
        simp at hb
        cases t <;> simp_all <;> omega
    obtain ⟨i,hi,h1,h2⟩ := hex
    refine ⟨pOne i true,?_,(good_one M i true).mpr (decide_eq_true hi)⟩
    exact List.mem_map.mpr ⟨i,by simp [h1,h2],rfl⟩
  · apply guard_ok; intro h
    simp; by_cases hx : vert e ∈ M.lone
    · exact Or.inr (fun hy => M.independent _ hx _ hy h)
    · exact Or.inl hx
  · apply guard_ok; intro h; simp [M.allShort h]
  · simp

open Rup

def ruleNumber (t : Bool) (r : ℕ) : List ℕ :=
  rule t (r%16) (r/16%64) (r/1024%64) (r/65536%64) (r/4194304%64)
    (r/268435456%64) (r/17179869184%64)

def propagate (db : ℕ → ℕ) (cap : ℕ) : List ℕ → ℕ → Bool
  | [], _ => false
  | z :: zs, F =>
    let j := z%8192
    let u := z/8192
    let D := db j
    let r := Nat.xor D (Nat.land D F)
    if j < cap then
      if r == 0 then true else
        if r == Nat.shiftLeft 1 u then propagate db cap zs (setBit F (neg u)) else false
    else false

theorem prop_sound (a : ℕ → Bool) (db : ℕ → ℕ) (cap : ℕ) (hdb : ∀ j < cap, MaskSat a (db j)) :
    ∀ zs F, BitsFalse a F → propagate db cap zs F = true → False := by
  intro zs
  induction zs with
  | nil => simp [propagate]
  | cons z zs ih =>
    intro F hF hc
    simp only [propagate] at hc
    split at hc
    · rename_i hj
      obtain ⟨w,hw,hval⟩ := witness_U a hF (hdb _ hj)
      split at hc
      · rename_i h0
        rw [beq_iff_eq.mp h0, bit_zero] at hw
        contradiction
      · split at hc
        · rename_i hs
          rw [beq_iff_eq.mp hs,bit_pow,decide_eq_true_eq] at hw
          subst w
          apply ih _ _ hc
          intro l hl
          rw [bit_setBit,Bool.or_eq_true,decide_eq_true_eq] at hl
          rcases hl with hi | rfl
          · exact hF _ hi
          · rw [litVal_neg,hval]; rfl
        · contradiction
    · contradiction

structure Book where
  count : ℕ
  source : ℕ → ℕ
  learned : ℕ → List ℕ
  hints : ℕ → List ℕ

def matrix (t : Bool) (B : Book) (k : ℕ) : ℕ :=
  if k < B.count then mask (ruleNumber t (B.source k)) else mask (B.learned (k-B.count))

def accepted (t : Bool) (B : Book) (i : ℕ) : Bool :=
  propagate (matrix t B) (B.count+i) (B.hints i) (mask (B.learned i))

def batch (t : Bool) (B : Book) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => batch t B start n && accepted t B (start+n)

def prior {t : Bool} (M : Ports t) (B : Book) (cap : ℕ) : Prop :=
  ∀ j < B.count+cap, MaskSat (assignment M) (matrix t B j)

theorem start_ok {t : Bool} (M : Ports t) (B : Book) : prior M B 0 := by
  intro j hj
  have hj' : j < B.count := by omega
  rw [matrix,if_pos hj']
  exact maskSat_of_clauseSat _ (rule_ok M _ _ _ _ _ _ _)

theorem extend_ok {t : Bool} (M : Ports t) (B : Book) (lo : ℕ) (n : ℕ)
    (hs : prior M B lo) (hc : batch t B lo n = true) : prior M B (lo+n) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    rw [batch,Bool.and_eq_true] at hc
    have hp := ih hc.1
    intro j hj
    by_cases he : j < B.count+(lo+n)
    · exact hp j he
    have heq : j = B.count+(lo+n) := by omega
    subst j
    rw [matrix,if_neg (by omega),Nat.add_sub_cancel_left]
    by_contra hn
    apply prop_sound (assignment M) _ _ hp _ _ _ hc.2
    intro l hl
    cases h : litVal (assignment M) l with
    | false => rfl
    | true => exact (hn ⟨l,hl,h⟩).elim

theorem finish_ok {t : Bool} (M : Ports t) (B : Book) (n : ℕ)
    (hs : prior M B (n+1)) (h : B.learned n = []) : False := by
  obtain ⟨l,hl,-⟩ := hs (B.count+n) (by omega)
  rw [matrix,if_neg (by omega),Nat.add_sub_cancel_left,h] at hl
  change bit 0 l = true at hl
  rw [bit_zero] at hl
  contradiction

def smallsourcep0 : List (ℕ) := [15,2052,536885286,1610651686,530499,6212,8260,536881254,1073764454,1342210182,35208042567,86571098215,87108755559,104305401959,929955,12452,14500,14532,268441766,1073764518,1610651878,277231783,1083586727,1352415431]

def smallsourcep1 : List (ℕ) := [51883946151,86285627559,103507441831,52690301095,87091982503,104313796775,104582625479,1329411,18692,20740,536883494,1342206246,1073766726,1610647878,34678786311,69357818151,1728867,24932,268441958,536881510,805327238,1610647942,86294030695,52161044839]

def smallsourcep2 : List (ℕ) := [2128323,17213456871,17751114183,103767900615,2527779,39460,2662,536885862,277387847,815045159,1083742759,1352702535,17492,2147490902,3221234774,2415938838,2684376342,1518707,11380,23732,1879053430,3221234806,2415932598,3489676470]

def smallsourcep3 : List (ℕ) := [156552735863,225280601207,174320344247,191508602039,157895175287,175394217143,192582474935,226623040631,1920211,19668,29908,2147495126,3489676502,3221259734,123821051095,175377435863,192599258327,2319699,25940,1879065942,2415938902,2147507606,2952818070,225382075735]

def smallsourcep4 : List (ℕ) := [225650904471,31764,157426482615,2458771,33940,1879053462,2147490966,2952822294,156619867287,173824906391,190987994263,2571315,15412,39988,2147495158,2415932662,3221263990,174093737207,140437961783,174362303735,157626219575,208730430711,268435467,536870923]

def smallsourcep5 : List (ℕ) := [805306379,1073741835,1342177291,1610612747,2147483659,2415919115,2684354571,2952790027,3221225483,3489660939,87241523209,191931351049,209379655689,190320738314,207500607498]

def smallsourceg0 : List (List (ℕ)) := [smallsourcep0,smallsourcep1,smallsourcep2,smallsourcep3,smallsourcep4,smallsourcep5]

def smallsource (i : ℕ) : ℕ := (([smallsourceg0].getD (i/384) []).getD (i/24%16) []).getD (i%24) 0

def smalllearnedp0 : List (List ℕ) := [[11],[4,6,8,12,14,16,18,20,22,24,30],[23,277],[25,277],[5,277],[29,277],[19,277],[132,172,277],[4,6,8,12,16,18,20,22,24,28,30],[17,277],[7,277],[13,277],[277],[31],[23],[5,281],[19,281],[17,281],[4,6,12,16,18,20,24],[6,12,20,281],[7],[25],[19,173],[20,173]]

def smalllearnedp1 : List (List ℕ) := [[564],[172],[]]

def smalllearnedg0 : List (List (List ℕ)) := [smalllearnedp0,smalllearnedp1]

def smalllearned (i : ℕ) : List ℕ := (([smalllearnedg0].getD (i/384) []).getD (i/24%16) []).getD (i%24) []

def smallhintsp0 : List (List ℕ) := [[16384,475265,295031,409725,3350562,7217187,7110736,3407904,2302038,2138135,360571,426110,5546020,10297381,10354777,4030497,12886111,12361786,12558366,107],[16384,344186,90247,229507,9011300,213124,7864417,9379943,49],[16384,278646,458880,344186,7110738,9347157,9019442,11640883,11239523,393340,295031,3342417,1843283,1417240,4628507,4554817,1122383,13],[16384,393340,327801,5578845,6430814,6389800,5537882,4628527,78],[16384,475265,524289,2138114,114],[16384,393340,278646,1089637,1122406,851972,9011300,1417227,73],[16384,393340,278646,860221,1089598,1114116,2654268,1417226,79],[16384,278646,393340,860233,1122383,4],[16384,90247,213122,114819,133],[16384,475265,12877877,12558391,113],[16384,393340,851973,1417223,73],[16384,393340,5570601,4628523,77],[16384,458880,360571,475265,41099,57489,106642,139408,155789,172103,188553,204938,237708,254062,65679,2293777,12558356,12886131,12918901,11665460,1417234,1081486,278646,393340,4628499,4554817,1835023,1122380,11247629,105],[16384,278646,458880,360571,12353645,12918896,11247672,11640891,9011299,393340,295031,2130028,2269331,1417237,4628502,4554817,2302063,1835022,1122380,12],[16384,295031,1843283,2269331,2302036,14],[16384,475265,524289,2138114,116],[16384,409725,311416,3416127,4038720,4063263,2654268,3350566,87],[16384,475265,12877877,12558391,115],[16384,2269331,73744,188565,254100,229519,114824,134],[16384,409725,311416,41110,139416,155799,196761,4038747,4071516,3407903,5537882,3350567,86],[16384,409725,344186,458880,1081350,9019401,9347176,9379946,8323120,295031,393340,851973,1417223,1843272,2269331,2293774,4562952,4620353,7118876,88],[16384,295031,393340,327801,5578845,6430814,6389800,5537882,4628527,1843275,2269331,409725,311416,4038747,4071516,3407903,3350567,2302038,14],[16384,278646,2654268,860221,10],[16384,360571,426110,475265,295031,2269331,2138133,12558362,12353643,40963,57499,139318,155805,204956,98457,5546028,10362925,10289241,5570601,12886112,57]]

def smallhintsp1 : List (List ℕ) := [[16384,344186,442495,327801,393340,295031,2269331,57499,172099,1417374,4554817,106538,2302106,1835022,5578826,6398027,6422568,8298542,8331362,458880,278646,860232,1122380,1081348,9019404,9347176,9379946,48],[16384,278646,475265,295031,4620447,2269331,2138134,12558365,12353643,40963,57499,106539,139318,172098,204956,147609,860221,1089598,393340,2302106,1835022,1122380,4],[16384,344186,409725,295031,1409184,163998,1843270,2269331,2293774,7118873,8331352,458880,278646,860228,1122373,1081348,9019403,9347176,9379946,48]]

def smallhintsg0 : List (List (List ℕ)) := [smallhintsp0,smallhintsp1]

def smallhints (i : ℕ) : List ℕ := (([smallhintsg0].getD (i/384) []).getD (i/24%16) []).getD (i%24) []

def smallBook : Book := ⟨135,smallsource,smalllearned,smallhints⟩

def largesourcep0 : List (ℕ) := [15,2623488,172032,2687008,2689024,174080,2818080,2820096,305152,306176,369664,371712,530432,434176,435200,436224,437248,499712,500736,501760,502784,566272,568320,2171904]

def largesourcep1 : List (ℕ) := [631808,633856,667648,1704096,696320,2687136,697344,698368,2828288,699392,761856,762880,763904,764928,827392,828416,829440,830464,892928,893952,894976,896000,958464,959488]

def largesourcep2 : List (ℕ) := [960512,961536,1025024,1026048,1089536,1091584,1092608,1221632,1222656,1223680,1920000,1287168,1288192,1289216,1352704,1354752,1419264,1726464,1468416,1482752,1483776,1484800,1485824,1548288]

def largesourcep3 : List (ℕ) := [1549312,1550336,1551360,1613824,1614848,1615872,1680384,1681408,1682432,1966496,2648064,1745920,2779136,1747968,1811456,1813504,1994752,1875968,1876992,1878016,1879040,1942528,1943552,1944576]

def largesourcep4 : List (ℕ) := [2652160,2008064,2783232,2010112,2073600,2075648,2138112,2139136,2140160,2141184,2200576,2203648,2204672,2206720,2265088,2269184,2270208,2272256,2334720,2336768,2401280,2403328,2467840,2468864]

def largesourcep5 : List (ℕ) := [2531328,2532352,2534400,2818704,303136,305184,306208,369696,371744,530464,434208,435232,436256,437280,499744,500768,501792,502816,565280,566304,567328,568352,630816,631840]

def largesourcep6 : List (ℕ) := [632864,633888,696352,697376,698400,699424,761888,763936,764960,827424,828448,829472,892960,893984,895008,2623712,2635808,959520,2766880,961568,1091616,1092640,1156128,1158176]

def largesourcep7 : List (ℕ) := [1221664,1286176,1287200,1288224,1289248,1352736,1354784,1482784,1483808,1484832,1485856,1548320,1549344,1550368,1613856,1616928,1681440,1744928,1746976,1748000,1811488,1813536,1877024,1879072]

def largesourcep8 : List (ℕ) := [1941536,1942560,1944608,2138144,2139168,2203680,2204704,2205728,2206752,2267168,2269216,2270240,2271264,2272288,2334752,2400288,2401312,2402336,2403360,2465824,2467872,2660384,2532384,2755168]

def largesourcep9 : List (ℕ) := [2791456,2534432,528480,530496,659552,1052768,1183840,1445984,2625632,434240,2693184,2756704,2758720,436288,2824256,499776,500800,501824,502848,2105408,2625664,2629696,565312,2695232]

def largesourcep10 : List (ℕ) := [2756736,2760768,567360,2822272,2826304,630848,632896,696384,697408,698432,699456,761920,762944,763968,764992,827456,829504,894016,895040,896064,958528,960576,1024064,1027136]

def largesourcep11 : List (ℕ) := [1446144,2625792,2637888,1090624,2756864,2768960,1220672,1221696,1222720,1223744,1288256,1351744,1352768,1353792,1354816,1417280,1419328,1482816,1484864,1485888,1548352,1549376,1550400,1551424]

def largesourcep12 : List (ℕ) := [1613888,1615936,1679424,1680448,1681472,1744960,1747008,1748032,1810496,1812544,1813568,1876032,1878080,1941568,1943616,2007104,2009152,2072640,2074688,2075712,2626048,2138176,2141248,2203712]

def largesourcep13 : List (ℕ) := [2205760,2206784,2272320,2334784,2336832,2400320,2401344,2403392,2465856,2467904,2531392,2533440,2596928,2598976,2757248,467040,469088,481376,491616,499808,501856,661632,727168,729184]

def largesourcep14 : List (ℕ) := [792704,858240,860256,923776,925792,989312,1122400,1253472,1448064,1450080,546912,1515616,2103424,2105440,557152,2168960,2170976,2365568,2367584,561248,2627712,2629728,565344,2693248]

def largesourcep15 : List (ℕ) := [2695264,2758784,2760800,567392,2824320,2826336,568416,612448,623712,630880,631904,632928,633952,792736,796768,1251488,1448096,1452128,677984,1841312,1845344,1972384,2107488,2627744]

def largesourcep16 : List (ℕ) := [2631776,2693280,2697312,697440,2758816,2762848,2824352,2828384,699488,863328,734304,740448,761952,762976,764000,765024,929888,1847392,827488,2699360,828512,829536,2824384,2830432]

def largesourcep17 : List (ℕ) := [830560,996448,893024,894048,895072,896096,958560,959584,960608,1024096,1025120,1026144,1027168,1196128,1089632,1090656,1091680,1092704,2693392,1156192,2824464,1158240,1220704,1221728]

def largesourcep18 : List (ℕ) := [1222752,1223776,1286240,1287264,1288288,1289312,1448256,1335392,1351776,1352800,1353824,1354848,1412192,1417312,1418336,1419360,1420384,1710432,1726560,1468512,1857632,2119776,2627936,2644064]

def largesourcep19 : List (ℕ) := [2693472,1483872,2759008,2775136,2840672,1485920,2645088,1548384,1549408,1550432,1551456,1613920,1615968,1679456,1680480,1681504,1682528,1744992,1746016,1747040,1748064,1810528,1811552,1812576]

def largesourcep20 : List (ℕ) := [1813600,1865824,1876064,1877088,2781280,1878112,1879136,1941600,1942624,1943648,1944672,1998944,2628064,2007136,2693600,2008160,2759136,2009184,2010208,2194528,2072672,2073696,2074720,2075744]

def largesourcep21 : List (ℕ) := [2392160,2134112,2138208,2139232,2785376,2140256,2824704,2141280,2200672,2203744,2204768,2205792,2206816,2269280,2270304,2271328,2272352,2460768,2334816,2336864,2337888,2400352,2401376,2402400]

def largesourcep22 : List (ℕ) := [2403424,2465888,2466912,2467936,2531424,2533472,2596960,2597984,2599008,2600032,2759296,2824832,2759312,622720,630912,632960,796800,860320,1452160,678016,696448,2695328,697472,2762880]

def largesourcep23 : List (ℕ) := [698496,699520,761984,763008,764032,765056,2629824,827520,2699392,828544,829568,2830464,830592,1258624,884864,893056,894080,895104,896128,958592,960640,961664,1024128,1025152]

def largesourcep24 : List (ℕ) := [1026176,1027200,1090688,1091712,1156224,1158272,1220736,1221760,1222784,1223808,1286272,1287296,1288320,1289344,1335424,1351808,1352832,1353856,1354880,1401984,1412224,1417344,1418368,1419392]

def largesourcep25 : List (ℕ) := [1420416,2105696,2644096,1482880,1483904,2775168,1484928,1485952,1548416,1549440,1550464,1551488,1613952,1614976,1616000,1617024,1679488,1680512,1681536,1682560,1745024,1746048,1747072,1748096]

def largesourcep26 : List (ℕ) := [1810560,1811584,1812608,1813632,1865856,2125952,1867904,2630080,1876096,1877120,1878144,1879168,1941632,1942656,1943680,2630112,2007168,2008192,2009216,2010240,2072704,2073728,2761200,2074752]

def largesourcep27 : List (ℕ) := [2368000,2392192,2134144,2630144,2654336,2719872,2139264,2761216,2785408,2140288,2826752,2141312,2203776,2204800,2205824,2368032,2394240,2269312,2270336,2271360,2272384,2331776,2333824,2334848]

def largesourcep28 : List (ℕ) := [2335872,2336896,2337920,2398336,2630208,2658432,2401408,2761280,2789504,2403456,2465920,2467968,2468992,2531456,2532480,2533504,2534528,2599040,2761344,2826880,2761360,2826896,733344,739488]

def largesourcep29 : List (ℕ) := [743584,762016,764064,800928,1190080,1192096,805024,1255616,1452224,809120,1716384,813216,1845440,1847456,1976512,2042048,2631872,2633888,827552,2697408,2699424,828576,2762944,829600]

def largesourcep30 : List (ℕ) := [2828480,2830496,830624,871584,893088,894112,895136,896160,940192,2504864,958624,2701472,960672,2832544,1025184,1026208,1027232,1089696,1091744,1092768,1133728,1156256,1158304,2640032]

def largesourcep31 : List (ℕ) := [1220768,1221792,2771104,1222816,1223840,1286304,1287328,1288352,1289376,1351840,1352864,1353888,1354912,1412256,1417376,1418400,1419424,1420448,1466528,2119840,2435424,2632032,2644128,1482912]

def largesourcep32 : List (ℕ) := [2697568,1483936,2763104,2775200,2828640,1485984,1548448,1549472,1550496,1551520,1613984,1615008,1616032,1679520,1680544,1681568,1682592,1734816,1745056,2779296,1747104,1748128,1801376,1811616]

def largesourcep33 : List (ℕ) := [1812640,1813664,2650272,1876128,1877152,1878176,1879200,1941664,1942688,1943712,1944736,2007200,2008224,2009248,2010272,2072736,2073760,2074784,2075808,2138272,2139296,2140320,2141344,2200736]

def largesourcep34 : List (ℕ) := [2203808,2204832,2206880,2265248,2267296,2269344,2270368,2271392,2272416,2331808,2334880,2335904,2336928,2337952,2400416,2401440,2402464,2403488,2465952,2466976,2468000,2469024,2531488,2532512]

def largesourcep35 : List (ℕ) := [2533536,2534560,2598048,2600096,2763392,2828928,2763408,2828944,870592,893120,895168,1192160,1454304,1718464,1847520,2635968,958656,2699488,2701504,960704,2830560,2832576,1027264,1192192]

def largesourcep36 : List (ℕ) := [1067200,1089728,1091776,1092800,1133760,1135808,1155264,1156288,1157312,1158336,1323296,1722560,1788096,1853632,1208512,2443456,2634016,2640064,1220800,1221824,2765088,2771136,1223872,1286336]

def largesourcep37 : List (ℕ) := [1287360,1288384,1289408,1351872,1352896,1353920,1847632,1417408,1418432,1419456,1420480,1482944,1483968,1484992,2830688,1486016,1533120,1548480,1549504,1550528,1551552,1614016,1615040,1616064]

def largesourcep38 : List (ℕ) := [1617088,1679552,1680576,1681600,1682624,1745088,1746112,1747136,1748160,1810624,1811648,1812672,1813696,1994944,2126016,2568640,2634176,2650304,1877184,2765248,2781376,1879232,1941696,1943744]

def largesourcep39 : List (ℕ) := [2007232,2008256,2009280,2010304,2072768,2073792,2074816,2075840,2138304,2139328,2140352,2141376,2203840,2204864,2205888,2206912,2269376,2271424,2334912,2336960,2400448,2401472,2402496,2403520]

def largesourcep40 : List (ℕ) := [2465984,2467008,2468032,2531520,2597056,2598080,2600128,2830976,2765456,2830992,1024224,1026272,1091808,2767136,1222880,1223904,1286368,1351904,1353952,1417440,1418464,1419488,1420512,1482976]

def largesourcep41 : List (ℕ) := [1484000,1485024,1486048,1548512,1549536,1550560,1614048,1616096,1617120,1679584,1681632,1682656,1745120,1747168,1748192,1811680,1812704,1813728,1877216,1879264,1942752,1943776,2007264,2008288]

def largesourcep42 : List (ℕ) := [2009312,2138336,2139360,2140384,2203872,2204896,2205920,2206944,2269408,2270432,2271456,2272480,2334944,2336992,2338016,2400480,2401504,2402528,2403552,2466016,2468064,2636384,2660576,2532576]

def largesourcep43 : List (ℕ) := [2767456,2791648,2534624,1132800,1220864,2705664,2769184,2771200,1222912,2834720,2836736,1286400,2244928,1351936,2707712,1353984,2838784,1417472,1418496,1419520,1483008,1485056,1486080,1548544]

def largesourcep44 : List (ℕ) := [1550592,1614080,1616128,1617152,1682688,1745152,1747200,1813760,1877248,1941760,1944832,2007296,2139392,2203904,2204928,2205952,2206976,2270464,2334976,2466048,1265952,1288480,1335584,1855776]

def largesourcep45 : List (ℕ) := [1345824,2640192,1351968,2705728,2707744,2771264,1354016,2836800,2838816,1417504,1418528,1419552,1420576,1483040,1484064,1485088,1486112,1535264,1548576,1549600,1550624,1551648,1614112,1615136]

def largesourcep46 : List (ℕ) := [1616160,1617184,1680672,1682720,1745184,1747232,1810720,1811744,1812768,1813792,1866016,2116032,2640320,2650400,1877280,2771392,2781472,1879328,1941792,2007328,2008352,2009376,2010400,2075936]

def largesourcep47 : List (ℕ) := [2138400,2139424,2140448,2141472,2203936,2205984,2207008,2271520,2272544,2335008,2338080,2401568,2403616,2466080,2468128,2531616,2598176,2599200,2600224,2771600,1417536,1419584,1466688,1726784]

def largesourcep48 : List (ℕ) := [1483072,1484096,1485120,1486144,1542464,1548608,1549632,1550656,1551680,2187584,2249088,2253120,2384192,2642304,2646336,2707840,1615168,2773376,2777408,1680704,1745216,1747264,1811776,1813824]

def largesourcep49 : List (ℕ) := [1877312,1879360,1941824,1942848,1943872,1944896,2007360,2008384,2010432,2073920,2075968,2139456,2203968,2204992,2206016,2207040,2380320,2459968,2656576,2270528,2773536,2787648,2272576,2336064]

def largesourcep50 : List (ℕ) := [2400576,2401600,2402624,2403648,2466112,2467136,2468160,2533696,2839168,2773648,1532256,1550688,1726848,2253152,1608032,1614176,2711904,1616224,2842976,1679712,1681760,1682784,1993056,1735008]

def largesourcep51 : List (ℕ) := [2644384,1745248,1747296,2840992,1811808,1812832,1813856,1876320,1877344,1878368,1879392,1941856,1942880,1943904,1944928,2007392,2008416,2009440,2010464,2072928,2073952,2074976,2076000,2138464]

def largesourcep52 : List (ℕ) := [2139488,2140512,2141536,2200928,2644496,2204000,2205024,2206048,2207072,2265440,2270560,2271584,2272608,2335072,2336096,2337120,2338144,2400608,2401632,2402656,2403680,2466144,2467168,2468192]

def largesourcep53 : List (ℕ) := [2469216,2532704,2533728,2534752,2598240,2599264,2600288,2841216,1679744,1681792,2255232,1745280,2711968,2713984,1747328,2843040,1811840,1813888,1876352,1877376,1879424,1941888,2008448,2072960]

def largesourcep54 : List (ℕ) := [2075008,2138496,2139520,2140544,2141568,2204032,2205056,2206080,2207104,2394496,2646560,2656640,2270592,2777632,2787712,2272640,2335104,2337152,2401664,2402688,2403712,2466176,2467200,2533760]

def largesourcep55 : List (ℕ) := [2843264,1810848,1812896,1876384,1877408,1878432,1879456,1941920,1942944,1943968,1944992,2648544,2652576,2008480,2779616,2783648,2010528,2072992,2074016,2138528,2139552,2140576,2204064,2205088]

def largesourcep56 : List (ℕ) := [2206112,2207136,2269600,2270624,2272672,2335136,2337184,2400672,2402720,2532768,2533792,2599328,2779776,2779792,1931712,1941952,1944000,2126304,2128320,2652608,2007488,2716128,2718144,2009536]

def largesourcep57 : List (ℕ) := [2847200,2849216,2073024,2074048,2075072,2076096,2134464,2138560,2716160,2720192,2140608,2847232,2851264,2205120,2206144,2267584,2272704,2335168,2337216,2400704,2401728,2403776,2466240,2468288]

def largesourcep58 : List (ℕ) := [2532800,2064864,2073056,2075104,2134496,2652672,2654688,2138592,2720224,2783744,2785760,2140640,2849280,2851296,2204128,2205152,2207200,2335200,2337248,2400736,2401760,2402784,2465248,2466272]

def largesourcep59 : List (ℕ) := [2468320,2532832,2533856,2534880,2597344,2783872,2849408,2783888,2204160,2206208,2270720,2272768,2335232,2337280,2338304,2398720,2654784,2658816,2401792,2789888,2403840,2466304,2468352,2469376]

def largesourcep60 : List (ℕ) := [2531840,2533888,2534912,2597376,2785920,2851456,2785936,2851472,2331168,2337312,2525760,2527776,2656832,2722368,2724384,2787904,2402848,2853440,2855456,2466336,2468384,2722400,2726432,2533920]

def largesourcep61 : List (ℕ) := [2853472,2787984,2466368,2468416,2724448,2726464,2855520,2857536,2598464,2855552,2790032,2792064,673,689,2052,268441606,268443654,536881158,536883206,536885254,805324806,805326854,1073764358,1073766406]

def largesourcep62 : List (ℕ) := [1073768454,1342205958,1342208006,1342210054,1610647558,1610649606,1610651654,1879053318,2147490822,2147494918,2147507206,2415932422,2415938566,2415948806,2684380166,2952817670,2952821766,3221234694,3221259270,3489676294,268443686,536881190,536885286,536911910]

def largesourcep63 : List (ℕ) := [1073764390,1342205990,1610651686,1879053350,1879065638,2147490854,2415938598,2952817702,3221234726,3221259302,17717657640,34689517575,34689648647,18255314952,18423089159,18431477767,34958084103,103617003560,69962696711,69971085319,86974791688,70063620104,70231394311,87150954503]

def largesourcep64 : List (ℕ) := [155862042631,207233875976,268435458,530499,6212,6213,8260,8261,8292,8293,70,2118,536881222,805322822,805324870,1073764422,1073768518,1342210118,1610649670,1610653766,2147494982,2147507270,2415932486,2952817734]

def largesourcep65 : List (ℕ) := [2952821830,3221259334,3489676358,102,2150,536881254,536883302,536885350,805322854,805324902,1073764454,1073768550,1073782886,1073784934,1342206054,1342208102,1342220390,1610647654,1610649702,1610653798,1610655846,1879065702,2147495014,2147507302]

def largesourcep66 : List (ℕ) := [2415932518,2415938662,2415948902,2684380262,2952817766,3221259366,3221263462,3489676390,3489700966,134,536881286,536914054,805324934,805349510,1342206086,1342210182,1610649734,1610653830,2147495046,2415938694,2952817798,537534567,806361159,814749767]

def largesourcep67 : List (ℕ) := [68719476872,68719607944,86033571943,34897264744,34897264776,35073433703,35208042567,35208304711,52161028199,35166093384,52077133928,52077265000,35476873319,69357674599,69366063207,69257003112,35434922088,69257003144,69257265288,69424783463,69433172071,86562709607,86571098183,86571098215]

def largesourcep68 : List (ℕ) := [86571229287,35704012872,86436872296,86437003368,35704012904,35704012936,86573064295,86613041255,103767744615,103616741480,35972710536,37087680583,172441084007,172336218216,189629341799,189646119015,189516087400,206695956584,37581553768,52421466183,52421468231,52345962568,52513740871,69618112583]

def largesourcep69 : List (ℕ) := [52698685543,69525831752,52614791272,69693610055,69701998663,86823147591,86839924807,86839926855,86840057959,86840189031,86705700936,52883882120,86841499719,86841630823,104036571207,104036573255,103885570120,53152579720,138245308488,53687550024,53687550088,53688598664,138276380775,189914945607]

def largesourcep70 : List (ℕ) := [189784916040,207103203399,206964785224,54761422952,224207575111,224144654408,69794660456,69794660488,69962440807,87108755559,70063751240,86974529640,70063751304,104305401959,104154398824,70332448904,70598852712,70598852744,155773706343,155694006376,71137296488,71136247944,71136641160,207233613928]

def largesourcep71 : List (ℕ) := [224413483112,72209334376,72210120840,87377584231,87377715303,87243620456,87243620488,104423489608,104423489640,104423489672,87512318088,88181776487,138783227976,88047550536,138783228008,88047550568,138783228040,88183677031,173142966344,173142966408,89389989992,89391562856,224682573960,104692187272]

def largesourcep72 : List (ℕ) := [104958591080,139051925640,105646989415,105648037991,156231794824,106185039975,190591533192,122428004423,139587158120,139587158152,139765225543,140690137191,208306372680,140660768872,208306634888,140929597544,140931170408,208575594600,208575201416,208575594632,208844161128,209112989832,536870914,929955]

def largesourcep73 : List (ℕ) := [12452,12453,14500,14501,14532,14533,166,2214,268441766,268443814,268478630,805324966,805327014,805347494,805349542,1073764518,1073768614,1073782950,1342206118,1342208166,1342218406,1610649766,1610653862,1610655910]

def largesourcep74 : List (ℕ) := [1879053478,1879065766,2147490982,2147507366,2415938726,2415948966,2684380326,2952791206,2952817830,2952821926,3221234854,3221259430,198,2246,268441798,268443846,805324998,805347526,1073764550,1342206150,1342210246,1879053510,1879065798,2147491014]

def largesourcep75 : List (ℕ) := [2147507398,2415938758,2415948998,2684380358,2952791238,2952817862,2952821958,3221234886,3221259462,2278,1610649830,1610651878,1879053542,2147491046,2147507430,268841127,277231783,277231815,277362855,277362887,17180000488,51615117479,51615248551,814889159]

def largesourcep76 : List (ℕ) := [1075196071,1083586727,1083586759,68719608040,86016798887,86016929959,1352415399,1352415431,1352677543,1352677575,85899477224,1621375143,103079346408,2156345511,2156345543,2157394087,137439084776,2426222759,2695051431,171798823144,3230218407,3230218439,3231791271,3231791303]

def largesourcep77 : List (ℕ) := [3232053415,206158561512,17448698024,51883946151,51892334759,51884077223,51808436392,17986355400,51886305447,18280231079,68988305576,18255052968,18255053000,18255315144,69156090023,69164478631,18431228071,86285627559,86168174760,18523881672,103507441831,103348043944,103348043976,18792972520]

def largesourcep78 : List (ℕ) := [103509670087,154887651496,172067520680,189247389864,52346093768,52690301095,52614791336,69525962952,69525962984,52691480743,52691611815,52959260839,52959391911,86705832136,104045099207,103885701320,53152710888,138274814151,138245439656,53688598696,138245439688,54494167208,189785047240,206964916424]

def largesourcep79 : List (ℕ) := [69794660520,69794922696,87091982503,86974529704,70063489224,70063489256,87093162151,104313796775,104154398888,155694006440,207233613992,207401400487,87243358408,104423489736,121603096776,138782965960,88047550664,138829901991,138830033063,173142704328,104692056232,104692187304,104692187336,105117989031]

def largesourcep80 : List (ℕ) := [106191468743,106193434791,139319115944,139901874343,156766765224,139855724712,139856117928,140124684456,208575201448,157842473160,805306370,1329411,18692,18693,20740,20741,20772,20773,262,2310,268439814,268441862,268443910,536881414]

def largesourcep81 : List (ℕ) := [536883462,1073766662,1342210310,2147495174,2415932678,2684380422,2952817926,3221259526,294,2342,268439846,268441894,268443942,268478758,536881446,536883494,536885542,1073764646,1073766694,1342206246,1342208294,1342210342,1610647846,1879053606]

def largesourcep82 : List (ℕ) := [2147491110,2147495206,2147507494,2415932710,2684380454,2684390694,3221234982,326,2374,268441926,268443974,536881478,536914246,1073764678,1073766726,1342210374,1610647878,1610649926,1879053638,2147491142,2147495238,2147507526,2415949126,2684390726]

def largesourcep83 : List (ℕ) := [2952817990,3221235014,3221266758,268718343,277106951,537678119,546066727,68820160807,17473753351,17482141959,17448567048,34670397703,34678786311,34678917383,17742713127,17751101735,34628436232,17717395752,17717526824,34681276679,69080469767,69088858375,69097246983,69088989479]

def largesourcep84 : List (ℕ) := [69089120551,68988174600,18255184200,86285502727,86293891335,86293893383,86168043784,18523881768,103490537735,103490539783,103347912968,18792710440,18792710472,103492899111,154887520520,19597033800,172067389704,172067520808,189247258888,223606997256,34939359527,34956136743,34897396008,69357687079]

def largesourcep85 : List (ℕ) := [35485272327,69349429543,69357818119,69357818151,69366206759,69257003304,69257134376,35435053384,69359653159,69359784231,86562853159,86571241767,35762491687,86437003560,103759368487,103759499559,103767888167,35972579656,103761334567,103761465639,120817733927,189646262567,189516218664,206733857063]

def largesourcep86 : List (ℕ) := [206834520359,206695956776,206696087848,69895344423,69794791752,70164173095,70164435239,70063489320,70239670567,70433132839,70332318024,71236931847,71236931879,155694137672,207233745224,87377596711,87243358504,104565854503,138812346663,138879455527,138782966056,173142835496,224682311976,105370046727]

def largesourcep87 : List (ℕ) := [105370046759,105370833191,139051794760,106176401703,208306372936,208346304775,1073741826,1728867,24932,24933,26980,26981,27012,27013,358,2406,268441958,268444006,536881510,536883558,536885606,805325158,805327206,805347686]

def largesourcep88 : List (ℕ) := [805349734,1342206310,1342208358,1342210406,1342218598,1610647910,1610649958,1879053670,1879065958,2147491174,2147495270,2415932774,2415938918,2415949158,2684376422,2684390758,2952822118,3221235046,3221259622,3221263718,390,2438,268444038,536883590]

def largesourcep89 : List (ℕ) := [536885638,805325190,805327238,1342210438,1610647942,2147491206,3221235078,3221263750,422,2470,268478886,536881574,536885670,1342206374,1342208422,1342210470,1610647974,2147491238,2147495334,2415932838,2415949222,2415962534,2952822182,3221235110]

def largesourcep90 : List (ℕ) := [3489676710,424,268853607,268855655,268986727,268986759,268829032,17179869608,271083879,537553255,34359738792,806512999,51623518567,806644071,806644103,806617480,1344039271,1344301447,85899346344,1612867943,1612867975,103079215528,2147969383,2147969415]

def largesourcep91 : List (ℕ) := [2148231527,2148231559,137438953896,2417846631,154618823080,171798692264,3221842311,3223415175,206158430632,17482277223,17448698216,17616494951,34678923623,34687312231,17750976871,34628567400,17717395816,17717526952,34796364135,34804752743,51892347239,51808436584,51808567656,17986486664]

def largesourcep92 : List (ℕ) := [51984621927,86294028647,86294030695,86168174952,18524012968,103490675047,103348044136,18792710536,154887651688,19597689256,172067520872,189247390056,20134691240,223607128424,34897265000,35073450343,52161044839,52161175911,52077134184,35166355848,86562728295,86436872552,86437134760,35703882152]

def largesourcep93 : List (ℕ) := [103759372647,103759374695,103616741736,35972579720,120817609063,172336218472,189516087656,206733732199,206695956840,52346225032,52431577447,52967530855,86823430535,52967661927,86831819143,52967792999,86705963400,53236490599,103885832584,53771460967,138245570952,54578340199,189915228551,54845333863]

def largesourcep94 : List (ℕ) := [54846906727,54847168871,206965047688,55115735399,87243489704,87512187272,138783097256,88047550888,88048337320,224682443176,104692056456,105101222247,105639010663,105639666023,156353325447,156231664008,190857937320,140662341992,192200376744,1342177282,2128323,31172,31173,33220]

def largesourcep95 : List (ℕ) := [33221,33252,33253,454,268442054,268444102,536881606,536883654,536885702,805325254,805327302,1073764806,1073766854,1073768902,1610648006,1610650054,1879053766,1879066054,2147491270,2147495366,2147507654,2415932870,2415939014,2684380614]

def largesourcep96 : List (ℕ) := [2952818118,2952831430,3221235142,3489676742,486,268442086,268444134,536881638,536883686,536885734,805325286,805327334,1073764838,1073768934,1073783270,1610650086,1610652134,1879053798,2147491302,2147495398,2147507686,2415932902,2684380646,2952818150]

def largesourcep97 : List (ℕ) := [3221235174,518,2566,268442118,268444166,536881670,536883718,536885766,805325318,1610650118,1879053830,1879066118,2147491334,2147495430,2415932934,2415939078,2684376582,3221235206,3489676806,17213456839,17213456871,17179869640,17179869672,537688519]

def largesourcep98 : List (ℕ) := [34359738856,806517191,806519239,51539608072,68820173287,68719477224,103230243303,137468346855,2149022151,137535455719,137438953960,154618823144,171798692328,17482285511,17482285543,17448698312,17448698344,17448829448,17484513767,17484644839,17742723527,17742725575,17750983111,17750983143]

def largesourcep99 : List (ℕ) := [17751114183,17751114215,17751245255,17751245287,17717526984,34628567528,17717395944,17717527016,34628698632,18019811783,18019942855,18019942887,17986355656,51808567816,18021384647,18288640455,18288640487,18288771527,18288902599,18288902631,18255315400,68988305896,18255053288,18255315432]

def largesourcep100 : List (ℕ) := [68988437000,18826559975,18792841736,103501300167,103501431239,19630227911,19630227943,19597689320,154887782920,19899449799,19899449831,172067521032,172067652104,20168016327,20134691272,189247390184,189247521288,223607259656,34939371975,34897396168,52077265352,52253456839,52253458887,69357830599]

def largesourcep101 : List (ℕ) := [69366217159,69366219207,69257134536,35435184616,103767900615,103767900647,103616872904,35972710920,103769735623,103784677831,172441240007,172336349640,172504154567,189629497799,189516218824,206696088008,37583127016,69635045831,69525963208,52614922760,52615053832,104036729287,53152580104,138291610055]

def largesourcep102 : List (ℕ) := [138245439944,53687812616,189785047496,224144785864,69794922984,104305689063,70332449288,71941292520,224413745640,104692187656,105378185671,105378185703,105378447815,105378447847,105379234247,105379234279,139051926024,156766765544,156767814120,191126503912,191126766056,208306635240,140662342120,208306635272]

def largesourcep103 : List (ℕ) := [157573644744,191396381160,1610612738,2527779,37412,37413,39460,39461,39492,39493,550,2598,268440102,268442150,268444198,536881702,536885798,536914470,805327398,1073764902,1073766950,1342206502,1342210598,1879053862]

def largesourcep104 : List (ℕ) := [2147491366,2147495462,2147507750,2415932966,2415939110,2415949350,2684380710,2952822310,3221235238,3221259814,3489676838,582,2630,268442182,268444230,536881734,536883782,536885830,536914502,805325382,805327430,1073764934,1073766982,1342206534]

def largesourcep105 : List (ℕ) := [1342210630,1879053894,2147491398,2147495494,2147507782,2415932998,2415939142,2415949382,2684376646,2684380742,2952822342,3221235270,3221259846,3489676870,614,2662,268444262,536881766,536885862,1073764966,1073769062,1342208614,2147491430,2147507814]

def largesourcep106 : List (ℕ) := [2415939174,2415949414,2952818278,3221235302,277256743,277256775,277387847,17180000872,545954343,545954375,546085447,34359870056,548051495,815045159,815045191,806617640,1083611687,1083611719,1083742759,1083742791,68719608424,1352440391,1352702535,85899477608]

def largesourcep107 : List (ℕ) := [2156370503,2156632615,2156632647,137439085160,2425199143,2425199175,2425592391,2426247751,154618954344,3230243367,3230243399,3231816263,206158561896,17448829512,34687457863,34628567624,34628698696,34796509735,18020078119,17986486824,18271998503,18288775719,68988437064,18524144200]

def largesourcep108 : List (ℕ) := [154887651912,154887782984,19597034056,154969739815,189360806471,35065076263,35166356008,35435053608,35434922568,35602733607,35602864679,35704013384,35871824423,36297873991,37046387272,37213542951,37373319751,37581554216,206695957064,206696088136,37581554248,37583127112,86840218151,86705963560]

def largesourcep109 : List (ℕ) := [138274968103,138342076967,138245571112,53687550536,53688599112,87108915751,70063751752,138783228488,156767027784,208306635304,208306635336,208475232807,208575201832,208575201864,208845079112,209649074760,17492,86,2134,268441686,268443734,536881238,805324886,805326934]

def largesourcep110 : List (ℕ) := [1073764438,1073766486,1073768534,1342206038,1342208086,1342210134,1610647638,1610651734,2147490902,2147494998,2147507286,2415932502,2415938646,2684376150,2684380246,2952817750,2952821846,3221234774,3221259350,3221263446,3489676374,3489700950,2326,268441878]

def largesourcep111 : List (ℕ) := [268443926,536881430,536883478,805325078,805327126,1073764630,1342210326,1610647830,1610649878,2147491094,2147495190,2147507478,2415938838,2684376342,2684380438,2952822038,37045469464,172426282071,172426413143,37581553752,37749343319,37757731927,71941292120,72109081687]

def largesourcep112 : List (ℕ) := [72117470295,88047288408,88215077975,88585077016,173231588439,139756979287,157117203543,2147483650,1518707,11380,11381,23668,23669,23732,23733,118,268443766,536883318,805324918,805326966,805349494,1073766518,1073768566,1342208118]

def largesourcep113 : List (ℕ) := [1342210166,1610647670,1610649718,1879053430,1879065718,2415932534,2415938678,2415948918,2684380278,2684390518,2952817782,2952821878,3221234806,3221259382,3221263478,3489676406,182,268439734,536883382,536912054,805324982,805327030,805347510,1073766582]

def largesourcep114 : List (ℕ) := [1342208182,1879065782,2415932598,2415938742,2684380342,2684390582,2952817846,2952821942,3221259446,3489676470,374,2422,268439926,268444022,536883574,805325174,805327222,1073766774,1073768822,1073785206,1342206326,1342210422,1610647926,1610649974]

def largesourcep115 : List (ℕ) := [1879053686,2415932790,2415938934,2415949174,2684376438,2684380534,2952818038,2952822134,3221259638,3489676662,51539738744,154618822840,171903573175,2685993336,3230215287,3230227575,17448829048,17742572663,17717395576,34628567224,34628698296,17744538743,51808436408,18021362807]

def largesourcep116 : List (ℕ) := [18013105271,18280242295,18255052920,68988305592,18524143736,154942319735,19596640376,19597688952,154887651512,19596640440,154944416887,154944547959,172172532919,19865862520,172174761143,20134690936,20134429048,20670513272,20670513336,52077133944,35209632951,35476888759,35434922168,36289457271]

def largesourcep117 : List (ℕ) := [36297845879,36239114360,36239900856,36406897783,36415286391,37045469368,37046386872,37045731704,37312594104,37581553784,37583126648,37581553848,37583388856,52614791288,53152710776,189898316983,54494167416,189899758775,54836931703,54836943991,54845320311,54761422968,224207711351,55105772727]

def largesourcep118 : List (ℕ) := [55030251704,70699527287,70598852728,70775024759,70775037047,155748674679,71136641144,71136247992,71312432311,71941292152,207233614008,71941292408,207409798263,72210120888,87904562295,87778721912,173247716471,173247716535,88585339256,173248371895,224745499767,89391562872,89389990072,104958591096]

def largesourcep119 : List (ℕ) := [105126374519,105495986296,105495986360,105495986552,106033774968,122209774711,122209786999,156552735863,156552748151,156577901687,156577913975,156498198648,156674370679,173782936695,173782948983,173824879735,173678067832,173854252151,190971194487,190971206775,190857937016,123501894775,208176229495,208176241783]

def largesourcep120 : List (ℕ) := [208193006711,123552214135,208037806200,225280601207,225217675384,123749728440,157090524279,157091179639,157035593912,157205277815,174320344183,174320344247,174321392759,174215463096,157304815992,174322113719,191508601975,191508602039,157628181623,191509650551,191395332280,157573382520,157895175287,157895187575]

def largesourcep121 : List (ℕ) := [157920341111,157920353399,157840638072,208575201464,158008421495,158164016311,225818389623,158189182135,225755070648,158109466808,158165773431,174589303927,174590221431,174484685176,174590680247,174858394743,174858394807,191664554360,174753251704,175108598903,175125388407,175020507256,208844423544,175196691575]

def largesourcep122 : List (ℕ) := [226087218295,175394217143,175436160183,175289335992,226024292728,192046652535,192046652599,191933120888,192313646199,209112990072,192582474935,192599252151,192469205176,209380245624,226623040631,209649074360,226992544951,226828943544,2415919106,1920211,19668,19669,29908,29909]

def largesourcep123 : List (ℕ) := [30004,30005,214,2262,268441814,268443862,536881366,805322966,805327062,1073764566,1073766614,1073768662,1342208214,1342210262,1610647766,1610649814,1879053526,1879065814,2147491030,2147495126,2147507414,2684376278,2684380374,2684390614]

def largesourcep124 : List (ℕ) := [2952791254,2952817878,2952821974,3221234902,3221259478,3489676502,310,2358,268441910,268443958,536881462,805327158,1073764662,1073768758,1342210358,1610649910,1879053622,1879065910,2147491126,2147495222,2147507510,2684376374,2952817974,2952822070]

def largesourcep125 : List (ℕ) := [3221234998,3221259574,3489676598,470,2518,268442070,268478934,536881622,536885718,805323222,805327318,1073764822,1342208470,1342210518,1610648022,1610650070,1879053782,2147491286,2147495382,2147507670,2952791510,2952818134,2952822230,3221235158]

def largesourcep126 : List (ℕ) := [3221259734,3221266902,3489676758,17179869656,2148234455,206296872151,51808436536,18013113559,51984626999,18524013016,19865600312,20033402167,20041790775,20134429144,20134691288,189379802327,20695698647,20695708887,20670513368,36239900984,37581553880,37583388888,53687812312,55030251736]

def largesourcep127 : List (ℕ) := [70691943735,70599639352,71942865368,72302425303,72319202519,72210120920,87779508536,88047288536,88047550680,88215352535,88585077048,89389990104,104959377720,105227157720,105227419864,105228206296,190721455319,122139246904,122478611671,122479398103,139319116088,123016400087,173783741751,173678854456]

def largesourcep128 : List (ℕ) := [190987990327,190988776663,190988776759,190858723640,208177034551,208038592824,123821051095,123749728472,225218462008,139616548055,139683646679,139683656919,139587158232,174034996439,173946896600,140124684600,191256556759,191256556855,191240041687,191256818903,191126765784,140393775576,191294567639,208344413399]

def largesourcep129 : List (ℕ) := [208445076695,208445863127,208306634968,140662342104,208447108311,225486504152,140929597656,191794345271,174753513944,208982603063,208844161336,175377435863,175289336024,191933383128,192330429751,209113252312,192201949656,192599258327,192469205208,226293121496,209381818840,209787516119,226828943576,2684354562]

def largesourcep130 : List (ℕ) := [2319699,25940,25941,36180,36181,36244,36245,268441942,268443990,536881494,536883542,536885590,805323094,805325142,1073764694,1342206294,1342210390,1610649942,1879053654,1879065942,2147491158,2147495254,2147507542,2415932758]

def largesourcep131 : List (ℕ) := [2415938902,2952818006,2952822102,3221235030,3221263702,3489676630,3489701206,268442006,268444054,536881558,536883606,536885654,805325206,1073764758,1342206358,1342210454,1879053718,1879066006,2147491222,2147495318,2147507606,2415932822,2415938966,2952791446]

def largesourcep132 : List (ℕ) := [2952818070,3221235094,3221263766,3489676694,268442166,268444214,536885814,1073764918,2147491382,2147495478,2415932982,3221263926,3489701430,34628698680,17986486680,51894576471,18524012952,19597033816,20134429080,189362890071,20302237079,223770873175,223770873239,20672086584]

def largesourcep133 : List (ℕ) := [223773101399,86436872760,36239901016,37314298264,189631325527,37490494871,37583389240,53688598936,189899760983,54763258424,70599639384,71943127608,207390018903,72211694136,87779508568,88182590871,88048337304,224846187863,224846187927,89391563320,104959377752,105228206488,139348501847,139365279063]

def largesourcep134 : List (ℕ) := [139365289303,139415610711,139319116120,190971995479,190858723672,208193817943,208038592856,225281402199,225218462040,139587944856,139952612695,139856118104,156767814040,191127552408,140393513368,208462646679,208307421592,140662604344,208475229591,208483618199,225650904471,140931170872,225655098775,191508997463]

def largesourcep135 : List (ℕ) := [157573382552,191510373719,208730819927,208575594840,157842473528,191933120920,209268215191,209112990104,192202211896,192315680087,226456472983,192470778424,209382081080,226561950264,209650647608,226830516792,2952790018,2059283,27668,27669,31764,31765,32180,32181]

def largesourcep136 : List (ℕ) := [268441622,536881174,536883222,536885270,805324822,805326870,1073764374,1073766422,1342205974,1342210070,1610647574,1610649622,1879053334,1879065622,2147490838,2147494934,2147507222,2415932438,2415938582,2415948822,2684380182,2684390422,3221259286,3489664022]

def largesourcep137 : List (ℕ) := [3489700886,2486,268442038,536881590,536883638,536885686,805325238,805327286,1073764790,1073766838,1342206390,1610647990,1879053750,1879066038,2147491254,2147495350,2147507638,2415932854,2415938998,2415949238,2684380598,2684390838,3221235126,3221259702]

def largesourcep138 : List (ℕ) := [3221263798,3489676726,268442102,536881654,536883702,805325302,805327350,1073764854,1342206454,1610648054,2147491318,2147495414,2147507702,2415932918,2415949302,3221259766,3489676790,85899346424,17717526968,17717395960,17717527032,17986486712,18255184312,18524012984]

def largesourcep139 : List (ℕ) := [19597689336,172172405783,19891060151,19865862584,20703308823,20669726744,20837526551,20837530647,172441103383,37087706551,37096095159,37045731768,206834531767,37583127032,53764128183,53688598968,207103491511,55113378839,55029465112,86974792184,70598853048,155815673271,71137296888,71942865400]

def largesourcep140 : List (ℕ) := [72301636631,72209334296,87778722296,88048337336,88047288824,88048337400,89523448855,89389203480,105497035256,156619865527,123769941015,123769945111,139587944888,139685555223,156847537591,156889480631,156767814072,139856773624,139953990679,156890725815,140221447607,208445865399,140662342136,140958198807]

def largesourcep141 : List (ℕ) := [140958202903,140974976023,140974980119,141025307671,141025311767,225650900407,140928811032,225487290808,157157260727,157426482615,157304816056,157962304951,158188399639,158230342679,158230346775,158231133623,158108680216,208982867383,208844423608,175022080504,175393434647,175288549400,209686064151,209786727447]

def largesourcep142 : List (ℕ) := [209786731543,209648287768,226891103255,3221225474,2458771,33940,33941,38036,38037,38420,38421,150,268441750,536881302,536883350,536885398,805324950,1073764502,1073768598,1342206102,1342208150,1879053462,1879065750,2147490966]

def largesourcep143 : List (ℕ) := [2147495062,2147507350,2415932566,2415938710,2415948950,2684376214,2684380310,2684390550,2952817814,2952821910,3489701014,534,2582,268442134,536881686,536883734,536885782,805325334,1073764886,1073768982,1342206486,1342208534,1610652182,1879053846]

def largesourcep144 : List (ℕ) := [2147491350,2147495446,2147507734,2415932950,2415949334,2684380694,2952818198,2952822294,536881750,536912470,1073764950,1610654294,2147491414,2147495510,2147507798,2415933014,2684390998,2952818262,2952822358,3489701462,51539608088,51539739160,85899346456,2147976343]

def largesourcep145 : List (ℕ) := [171945530903,171945661591,17448698008,17717395608,34628698712,17986486424,51808567832,18255184024,18255315096,18524143768,19596640408,19597033624,19597688984,19597689368,172214359191,172214359575,19865862296,19866518104,20134428824,20134690968,20134691352,20672086616,34897265240,35704013400]

def largesourcep146 : List (ℕ) := [36281091223,36281095319,36239114392,172483056791,172483057175,172483318935,37046387288,37314560536,52614922776,52615053848,52883882136,53152580120,53771469975,53771474071,53687550104,53687812632,54494429720,224308532375,224308532759,55030252056,55031824984,70691161239,70707938455,70598852760]

def largesourcep147 : List (ℕ) := [71136641176,71137296920,224577229975,72211694168,87904584855,88047288472,88223483031,173142704280,88585994840,105101231255,104958591128,105126401175,105227157656,105227420184,105227420248,105394967703,105495986776,105664845335,139347723415,122428036247,139364504727,139414836375,139318329496,139494524055]

def largesourcep148 : List (ℕ) := [139486139543,156552762519,156619867287,156498198680,156666008727,173782959255,173824906391,173824906775,173678067864,190987994263,190857937048,225381291159,225217675416,139633071255,139586896024,156888433815,139901899927,139902948887,139953280535,156766765208,139856773656,156934575255,174093472919,174093473303]

def largesourcep149 : List (ℕ) := [174093735063,174093735447,173946634392,173947682968,140125602392,191256560791,140393775640,225649857687,225486241944,140931170904,225652151447,157091206679,157157655703,157036642840,174362301591,174362301975,157427139735,174363350167,174363350551,174216512024,157305471576,157573644824,225919735319,225756119576]

def largesourcep150 : List (ℕ) := [174631523479,174485340760,174900352151,174900352535,174753514008,191665209944,175436174487,226024948312,226456737303,2571315,15412,15413,39988,39989,40180,268441654,268443702,536881206,536883254,805324854,1073764406,1073766454,1342206006,1342210102]

def largesourcep151 : List (ℕ) := [1610647606,1610649654,1879053366,1879065654,2147490870,2147494966,2147507254,2415932470,2684380214,2684390454,2952791094,2952817718,3221234742,3221259318,3221263414,268441846,268443894,536881398,536883446,805325046,805327094,1073764598,1073766646,1342210294]

def largesourcep152 : List (ℕ) := [1610647798,1610649846,1879053558,1879065846,2147491062,2147495158,2147507446,2415932662,2684380406,2684390646,2952791286,2952817910,2952822006,3221234934,3221259510,3221263606,268442230,536881782,536883830,805325430,1073764982,1610650230,1879053942,2147491446]

def largesourcep153 : List (ℕ) := [2147495542,2147507830,2415933046,2684380790,2684391030,2952791670,2952818294,3221235318,3221259894,3221263990,18700344567,19596640504,19772841207,19866518136,20132724792,37312593976,53687550200,54492463160,54763258488,71136248056,88047550712,106032070712,123232926775,139587158264]

def largesourcep154 : List (ℕ) := [156846759159,156767027448,139855724792,139903646775,139903777847,174093737207,173946896632,140125602424,140421184567,140437961783,140488293431,140391809080,208306635000,140662604408,208482835703,157035593976,174362303735,157305471608,157626219575,157571678264,191395332344,208575201528,174485340792,174898388023]

def largesourcep155 : List (ℕ) := [174751547448,191665209976,175022080248,208845079160,175022342776,191931416632,209111285816,17179869193,34359738377,51539607561,68719476745,85899345929,103079215113,120259084297,137438953481,154618822665,171798691849,188978561033,206158430217,34628173833,51808043017,68987912201,86167781385,103347650569]

def largesourcep156 : List (ℕ) := [154887258121,172067127305,189246996489,206426865673,52076478473,69256347657,86436216841,103616086025,120795955209,172335562761,189515431945,69524783113,86704652297,103884521481,138244259849,189783867401,206963736585,224143605769,86973087753,104152956937,121332826121,155692564489,207232172041,224412041225]

def largesourcep157 : List (ℕ) := [104421392393,138781130761,173140869129,121869697033,139049566217,156229435401,190589173769,139318001673,156497870857,173677740041,190857609225,208037478409,225217347593,156766306313,173946175497,208305913865,225485783049,191394480137,208574349321,225754218505,191662915593,208842784777,226022653961,226291089417]

def largesourcep158 : List (ℕ) := [188978561034,223338299402,120527519754,137707388938,206426865674,137975824394,155155693578,223875170314,121064390666,155424129034,172603998218,138512695306,172872433674,190052302858,155960999946,190320738314,207500607498,173409304586,207769042954,224948912138]

def largesourceg0 : List (List (ℕ)) := [largesourcep0,largesourcep1,largesourcep2,largesourcep3,largesourcep4,largesourcep5,largesourcep6,largesourcep7,largesourcep8,largesourcep9,largesourcep10,largesourcep11,largesourcep12,largesourcep13,largesourcep14,largesourcep15]

def largesourceg1 : List (List (ℕ)) := [largesourcep16,largesourcep17,largesourcep18,largesourcep19,largesourcep20,largesourcep21,largesourcep22,largesourcep23,largesourcep24,largesourcep25,largesourcep26,largesourcep27,largesourcep28,largesourcep29,largesourcep30,largesourcep31]

def largesourceg2 : List (List (ℕ)) := [largesourcep32,largesourcep33,largesourcep34,largesourcep35,largesourcep36,largesourcep37,largesourcep38,largesourcep39,largesourcep40,largesourcep41,largesourcep42,largesourcep43,largesourcep44,largesourcep45,largesourcep46,largesourcep47]

def largesourceg3 : List (List (ℕ)) := [largesourcep48,largesourcep49,largesourcep50,largesourcep51,largesourcep52,largesourcep53,largesourcep54,largesourcep55,largesourcep56,largesourcep57,largesourcep58,largesourcep59,largesourcep60,largesourcep61,largesourcep62,largesourcep63]

def largesourceg4 : List (List (ℕ)) := [largesourcep64,largesourcep65,largesourcep66,largesourcep67,largesourcep68,largesourcep69,largesourcep70,largesourcep71,largesourcep72,largesourcep73,largesourcep74,largesourcep75,largesourcep76,largesourcep77,largesourcep78,largesourcep79]

def largesourceg5 : List (List (ℕ)) := [largesourcep80,largesourcep81,largesourcep82,largesourcep83,largesourcep84,largesourcep85,largesourcep86,largesourcep87,largesourcep88,largesourcep89,largesourcep90,largesourcep91,largesourcep92,largesourcep93,largesourcep94,largesourcep95]

def largesourceg6 : List (List (ℕ)) := [largesourcep96,largesourcep97,largesourcep98,largesourcep99,largesourcep100,largesourcep101,largesourcep102,largesourcep103,largesourcep104,largesourcep105,largesourcep106,largesourcep107,largesourcep108,largesourcep109,largesourcep110,largesourcep111]

def largesourceg7 : List (List (ℕ)) := [largesourcep112,largesourcep113,largesourcep114,largesourcep115,largesourcep116,largesourcep117,largesourcep118,largesourcep119,largesourcep120,largesourcep121,largesourcep122,largesourcep123,largesourcep124,largesourcep125,largesourcep126,largesourcep127]

def largesourceg8 : List (List (ℕ)) := [largesourcep128,largesourcep129,largesourcep130,largesourcep131,largesourcep132,largesourcep133,largesourcep134,largesourcep135,largesourcep136,largesourcep137,largesourcep138,largesourcep139,largesourcep140,largesourcep141,largesourcep142,largesourcep143]

def largesourceg9 : List (List (ℕ)) := [largesourcep144,largesourcep145,largesourcep146,largesourcep147,largesourcep148,largesourcep149,largesourcep150,largesourcep151,largesourcep152,largesourcep153,largesourcep154,largesourcep155,largesourcep156,largesourcep157,largesourcep158]

def largesource (i : ℕ) : ℕ := (([largesourceg0,largesourceg1,largesourceg2,largesourceg3,largesourceg4,largesourceg5,largesourceg6,largesourceg7,largesourceg8,largesourceg9].getD (i/384) []).getD (i/24%16) []).getD (i%24) 0

def largelearnedp0 : List (List ℕ) := [[48,54,65,96,105,160,172,1847],[58,96,105,160,172,225,1827],[10,12,14,16,18,20,22,24,26,28,30],[12,14,16,18,20,22,24,26,28,30,173],[48,50,105,396,417,1838,1862],[12,14,16,18,20,22,24,26,28,30,48,105,160,1847],[12,14,16,18,20,22,24,26,28,30,105,160,1847],[12,14,16,18,20,22,24,26,28,30,160,1847],[6,12,14,16,18,20,22,24,26,28,30,1826,1846],[105,172,225,396,404,408,417,1846],[48,50,105,172,174,216,218,224,396,406,408,410,1846,1863],[48,50,105,172,174,216,218,396,404,406,408,410,417,556,580,856,880,1846],[50,105,174,216,218,224,276,324,338,340,342,417,1839,1858],[50,65,105,133,324,384,392,400,417,960,1100,1699,1826,1834,1842],[50,65,105,133,137,174,216,218,224,260,276,324,338,340,342,384,392,400,417,960,1100,1826,1862],[50,65,260,281,1830,1854],[50,65,105,133,137,170,172,174,216,218,260,324,338,340,342,384,392,396,400,404,406,408,410,412,417,556,580,856,880,960,1100,1826,1846],[36,133,214,324,392,410,417,869,1863],[36,46,133,324,493,1834,1858],[36,40,42,565,568,660,680,1265,1849],[36,105,133,137,172,324,493,556,568,660,676,869,1016,1100,1140,1256,1834,1858,1866],[36,105,133,137,172,214,324,342,392,410,417,493,497,556,568,660,676,869,1016,1100,1140,1256],[12,14,16,18,20,22,24,26,28,30,1826,1846],[12,14,16,18,20,22,24,26,28,30,1826]]

def largelearnedp1 : List (List ℕ) := [[6,12,14,16,18,20,22,24,26,28,30],[12,14,16,18,20,22,24,26,28,30,37,50],[12,14,16,18,20,22,24,26,28,30,37],[12,14,16,18,20,22,24,26,28,30],[8,14,16,18,20,22,24,26,28,30,97],[4,14,16,18,20,22,24,26,28,30,36,51,105,417],[36,48,54,342,493,570,584,676,681,781,869,1858],[36,48,54,206,544,570,681,869,1827],[36,48,54,96,105,544,556,781,1663],[14,16,18,20,22,24,26,28,30,36,51,105,417],[36,48,54,65,206,342,493,544,570,584,676,681,781,869],[36,52,162,173,206,224,869,1663],[6,14,16,18,20,22,24,26,28,30,36,51],[14,16,18,20,22,24,26,28,30,36,51],[14,16,18,20,22,24,26,28,30,36,48,54,1827],[4,8,14,16,18,20,22,24,26,28,30,48,50],[14,16,18,20,22,24,26,28,30,36,48,1662],[14,16,18,20,22,24,26,28,30,36,1662],[36,49,50,556,564,681,1663,1844],[14,16,18,20,22,24,26,28,30,36],[5,37,48,50,1663,1830,1846,1854],[14,16,18,20,22,24,26,28,30,48,50,1663],[9,48,54,1663,1846],[14,16,18,20,22,24,26,28,30,48,1663]]

def largelearnedp2 : List (List ℕ) := [[5,37,48,54,556,564,568,580,781,890,1004,1006,1662,1846],[8,14,16,18,20,22,24,26,28,30,48,54,1846],[8,14,16,18,20,22,24,26,28,30,48,1846],[4,8,14,16,18,20,22,24,26,28,30,48],[8,14,16,18,20,22,24,26,28,30,48],[5,37,48,556,564,568,580,781,890,1004,1006,1662],[48,54,225,736,868,896,898,1012,1014,1662,1826,1878,1880,1882,1884,1886],[48,51,225,408,868,961,1016,1144,1880,1884],[48,160,225,408,564,736,756,781,864,866,868,888,890,896,898,980,982,1006,1012,1014,1662,1847],[14,16,18,20,22,24,26,28,30,48,50],[42,48,105,172,277,556,564,681,1846],[14,16,18,20,22,24,26,28,30,48],[50,65,260,281,640,664,1875],[14,16,18,20,22,24,26,28,30],[50,54,65,736,844,896,1141,1715],[50,54,162,204,206,224,256,260,384,736,960,982,984,986,988,996,1012,1504,1508,1564,1714,1827],[50,54,65,162,204,206,224,256,260,384,736,844,866,868,870,872,960,982,984,986,988,996,1012,1141,1504,1508,1564,1714],[50,54,204,225,960,984,1017,1663],[5,50,866,868,870,872,896,982,984,986,988,996,1012,1017,1141,1145,1564],[7,49,225],[4,6,16,18,20,22,24,26,28,30,757],[50,54,736,760,844,868,896,1141,1662,1687],[6,16,18,20,22,24,26,28,30,50,54,225,736,1662],[40,50,54,737,762,984,1014,1145,1851]]

def largelearnedp3 : List (List ℕ) := [[16,18,20,22,24,26,28,30,49,50,54,225,737],[16,18,20,22,24,26,28,30,49,50,54,225],[50,52,54,417,672,785,880,892,1883],[6,8,16,18,20,22,24,26,28,30,50,54],[50,54,56,133,400,417,860,880,1719],[16,18,20,22,24,26,28,30,49,50,54],[4,12,16,18,20,22,24,26,28,30,173],[6,16,18,20,22,24,26,28,30,49,50,1718],[16,18,20,22,24,26,28,30,49,50,1718],[7,49,50,780,784,1141,1678,1704],[16,18,20,22,24,26,28,30,49,50],[36,54,173,224,409,866,870,1719],[13,49,224,280,409,866,870,982,986,1017,1145],[36,54,56,224,409,565,982,986,1887],[16,18,20,22,24,26,28,30,49],[7,48,54,1141,1674,1704,1706,1712,1714],[6,8,12,16,18,20,22,24,26,28,30,54],[7,48,54,972,1004,1006,1012,1014,1141,1723],[8,12,16,18,20,22,24,26,28,30,54],[8,12,16,18,20,22,24,26,28,30],[7,48,54,681,1004,1006,1012,1014,1141,1145],[48,54,65,736,781,960,1012,1887],[8,16,18,20,22,24,26,28,30],[48,50,225,404,497,980,996,1723]]

def largelearnedp4 : List (List ℕ) := [[16,18,20,22,24,26,28,30,1883],[16,18,20,22,24,26,28,30],[15,48,1425,1847,1898],[4,6,10,18,20,22,24,26,28,30,48,50,1847],[4,6,10,14,18,20,22,24,26,28,30,48,50],[50,52,225,1686,1846],[50,52,54,785,896,1268,1272,1425,1883],[13,48,50,56,1017,1272,1425,1573],[4,6,10,18,20,22,24,26,28,30,48,50],[52,54,58,65,160,1216,1236,1425,1683],[6,10,12,18,20,22,24,26,28,30,48,50,1017,1682,1846],[6,10,12,18,20,22,24,26,28,30,48,50,1017,1846],[6,10,12,18,20,22,24,26,28,30,48,50,1846],[50,65,164,1508,1524,1573,1847],[52,58,65,736,781,1504,1556,1739],[6,10,18,20,22,24,26,28,30,48,50],[48,50,105,172,174,216,270,1368,1378,1380,1386,1846,1899],[48,50,56,105,172,174,216,218,270,1368,1376,1378,1380,1382,1386,1425,1846],[10,18,20,22,24,26,28,30,48,50],[7,48,1425,1847,1898],[6,10,14,18,20,22,24,26,28,30,48,1738,1894,1902],[6,10,14,18,20,22,24,26,28,30,59],[13,48,58,1706,1847],[10,18,20,22,24,26,28,30,48,1847]]

def largelearnedp5 : List (List ℕ) := [[6,10,12,14,18,20,22,24,26,28,30,48,58],[48,54,58,65,960,1145,1504,1564,1903],[6,10,12,18,20,22,24,26,28,30,48,58],[6,10,12,18,20,22,24,26,28,30,48],[36,48,261,280,409,1242,1246,1731],[6,10,18,20,22,24,26,28,30,48,59],[6,10,18,20,22,24,26,28,30,48,1731],[6,10,18,20,22,24,26,28,30,48],[48,56,58,105,172,218,268,270,1368,1382,1384,1386,1846,1899],[48,56,58,100,105,137,172,174,218,268,270,556,1360,1368,1376,1378,1382,1384,1386,1400,1425,1846],[36,48,56,174,224,556,566,681,1684,1839,1848],[10,18,20,22,24,26,28,30,48,224,566,1684,1848],[36,48,56,261,280,1382,1386,1425,1685],[10,18,20,22,24,26,28,30,48,1682],[10,18,20,22,24,26,28,30,48],[48,472,493,1228,1256,1425,1839],[48,52,56,480,493,584,586,676,1376,1396,1400,1402,1404,1899],[48,52,56,470,474,476,480,493,497,584,586,676,1124,1366,1368,1370,1372,1376,1396,1400,1402,1404,1420,1425,1838],[48,52,132,136,474,478,497,1368,1370,1374,1396,1735,1838],[18,20,22,24,26,28,30,48],[52,497,1101,1140,1144,1412,1422,1695,1724,1899],[52,493,497,1101,1140,1144,1412,1422,1425,1508,1532,1573,1703,1724,1730],[6,18,20,22,24,26,28,30,52,497,1101,1140,1144,1703,1724,1730,1738],[18,20,22,24,26,28,30,52,132,136,478,1101,1126,1140,1144,1703,1730,1738]]

def largelearnedp6 : List (List ℕ) := [[10,18,20,22,24,26,28,30,35,132,136,1101],[18,20,22,24,26,28,30,52,58,130,132,136,274,1101,1702,1738],[18,20,22,24,26,28,30,52,130,132,136,274,478,1101,1126,1140,1144,1730,1738],[18,20,22,24,26,28,30,57,1730,1738],[10,12,14,18,20,22,24,26,28,30,34,56,58,1830,1854],[18,20,22,24,26,28,30,34,56,58,677,1830,1836,1840,1842,1854,1890],[15,34,56,58,1836,1840,1842,1890],[13,34,49,52,56,1836,1874],[18,20,22,24,26,28,30,34,56,58,1830,1836,1840,1842,1854,1866,1874,1890],[14,18,20,22,24,26,28,30,34,56,59,1836,1874],[18,20,22,24,26,28,30,34,1734],[13,35,49,56,276,280,866,868,870,880,982,986,1017,1145,1372,1378,1425,1734],[52,56,261,280,868,880,1108,1114,1120,1145,1380,1386,1392,1420,1425,1734],[18,20,22,24,26,28,30,59,866,868,870,880,982,986,1017,1108,1114,1120,1145,1734],[15,18,20,22,24,26,28,30,1734],[8,10,12,14,18,20,22,24,26,28,30,56,58,1830,1842],[10,12,18,20,22,24,26,28,30,58,680,784,1734],[18,20,22,24,26,28,30,53,1734],[12,14,18,20,22,24,26,28,30,52,56,59,1842,1866],[11,52,56,58,1412,1422,1842,1866,1890,1899],[12,18,20,22,24,26,28,30,1734],[18,20,22,24,26,28,30,1734],[13,49,52,56,1672,1678,1710],[49,132,136,556,681,1672,1676,1840,1871]]

def largelearnedp7 : List (List ℕ) := [[6,10,12,18,20,22,24,26,28,30,56,136,557,681,1842,1868,1871],[10,18,20,22,24,26,28,30,52,56,681,1842],[34,49,52,136,478,556,560,652,654,680,1672,1676,1702,1704,1708,1710,1836],[10,18,20,22,24,26,28,30,34,52,56,556,1842],[9,49,105],[10,18,20,22,24,26,28,30,35,52,56,1842],[10,18,20,22,24,26,28,30,52,56,1842],[18,20,22,24,26,28,30,52,56,1842],[11,52,56,1702,1843],[8,10,12,18,20,22,24,26,28,30,1101],[8,18,20,22,24,26,28,30,52,56],[18,20,22,24,26,28,30,52,56],[9,49,56,680,784,1573,1690,1704],[18,20,22,24,26,28,30,56,1843],[18,20,22,24,26,28,30,56],[8,10,18,20,22,24,26,28,30],[13,49,52,132,136,1101,1672,1676],[8,18,20,22,24,26,28,30],[18,20,22,24,26,28,30],[34,50,104,266,270,854,858,872,1017,1691],[34,50,104,132,214,222,266,270,281,854,858,862,868,872,1017],[48,50,56,137,172,856,864,1017,1847],[15,104,132,172,176,214,222,225,266,270,277,281],[48,50,137,172,856,864,1017,1683]]

def largelearnedp8 : List (List ℕ) := [[50,137,172,225,856,864,1017],[48,50,137,172,325,330,338,396,404,416,492,1847],[50,137,172,225,325,330,338,396,404,416,492,856,864],[38,48,137,172,398,406,881,1683],[35,104,132,172,225,277,281,325,330,338,404,406,408,416,492,864,868],[34,48,106,132,137,170,172,277,1675],[48,137,225,408,416,492,1674,1838],[34,106,132,137,170,172,225,277,325,408,416,492],[34,48,104,132,136,170,174,178,325,1683],[34,48,104,132,136,170,174,178,277,325],[34,104,132,136,1669,1836,1840],[34,104,132,136,170,174,178,1847],[12,14,20,22,24,26,28,30,1509],[9,20,22,24,26,28,30],[14,20,22,24,26,28,30,53,497,676,1256],[12,14,20,22,24,26,28,30,59],[14,20,22,24,26,28,30,34,59,497,676,1256,1677,1837],[20,22,24,26,28,30,136,1668,1837],[34,104,136,325,392,416,854,862,868,880,1017,1094,1100,1102,1141,1668,1677,1836],[34,132,136,325,416,854,858,868,880,1017,1094,1098,1100,1141,1420,1676,1833,1836],[15,104,132,136,325,392,416,492,1668,1836],[14,20,22,24,26,28,30,34,1668,1676,1832,1836],[14,20,22,24,26,28,30,1265],[12,14,20,22,24,26,28,30,34,1673,1902]]

def largelearnedp9 : List (List ℕ) := [[14,20,22,24,26,28,30,34,38,49,53,1673,1864,1902],[14,20,22,24,26,28,30,38,49,53,136,1692,1836],[14,20,22,24,26,28,30,49,53,136,1692,1836],[12,14,20,22,24,26,28,30,34,52,1668],[20,22,24,26,28,30,49,136,1668],[13,34,49,52,1672,1710],[14,20,22,24,26,28,30,34,49,52,1666,1672,1710,1730],[12,14,20,22,24,26,28,30,34,1666,1738],[14,20,22,24,26,28,30,34,49,1666,1672,1700,1710,1730,1738],[13,34,49,974,1017,1672,1722],[34,416,492,858,868,880,1017,1696,1718,1837],[20,22,24,26,28,30,49,136],[15,104,132,134,136,325,392,416,492,1836],[14,20,22,24,26,28,30,34,38,48,1836,1841],[20,22,24,26,28,30,38,136,1672,1836],[20,22,24,26,28,30,38,136,1836],[14,20,22,24,26,28,30,34,48,52,497,584,1668],[20,22,24,26,28,30,136,1836],[20,22,24,26,28,30,136],[34,56,134,137,416,492,880,1017,1094,1100,1141,1669],[34,56,134,137,325,416,492,880,1017,1094,1100,1141],[56,400,497,860,880,1017,1679],[56,137,400,497,860,880,1017,1100,1120,1141],[56,334,416,492,496,1100,1118,1122,1126,1145,1843]]

def largelearnedp10 : List (List ℕ) := [[15,132,134,137,325,334,416,492],[20,22,24,26,28,30,38,56,1675,1692,1891],[13,38,56,137,325,1692,1706,1720,1724,1726,1890],[20,22,24,26,28,30,35,38,56,1679],[20,22,24,26,28,30,56,496,1679],[12,20,22,24,26,28,30,38,56,1839,1856],[20,22,24,26,28,30,56,496],[38,57,132,137,325,681,1264,1692,1856],[38,48,137,330,556,578,781,1857],[13,38,57,132,137,325,330],[20,22,24,26,28,30,496],[12,20,22,24,26,28,30,38,1856],[12,20,22,24,26,28,30,38],[20,22,24,26,28,30,38],[52,56,137,476,497,560,584,1871],[13,52,56,137,472,476,497],[52,56,58,137,476,1232,1256,1425,1867],[20,22,24,26,28,30,56],[17,57,137],[48,54,460,736,776,781,960,1000,1703,1886],[20,22,24,26,28,30],[35,57,104,136,557,1425],[52,57,104,136,173,224,276,497,557,1230,1425,1836,1894],[14,16,18,22,24,26,28,30,1662,1708,1712,1722,1863,1886]]

def largelearnedp11 : List (List ℕ) := [[14,16,22,24,26,28,30,34,52,1424,1836,1863,1886,1894],[52,65,224,260,276,565,680,736,780,960,1104,1144,1421,1424,1508,1576,1662,1826,1830,1844,1888],[14,16,22,24,26,28,30,52,57,497,1836,1844,1863,1868,1886,1894],[14,16,22,24,26,28,30,52,57,497,1867,1886],[14,16,22,24,26,28,30,52,496,1867],[14,16,22,24,26,28,30,52,57,1867],[34,54,173,974,1017,1836,1886],[15,57,104,136,173,557,565,780,1836,1867,1868],[5,55,1017],[4,18,22,24,26,28,30,34,57,1867],[5,34,55,565,680,780,1867,1868],[17,34,57,136,173,1836,1867],[4,22,24,26,28,30,34,57,1867],[22,24,26,28,30,34,57,1867],[22,24,26,28,30,57,1867],[54,224,408,417,493,557,565,568,676,680,780,880,1140,1144,1256,1698,1702,1862,1866,1868],[5,224,408,417,493,557,565,568,676,680,780,880,1140,1144,1256,1698,1702,1862,1866,1868],[5,55,680,780,1140,1144,1421,1884,1888],[22,24,26,28,30,35,57,1702],[5,34,54,565,780,1826,1872,1876,1878,1886],[4,22,24,26,28,30,34,41,54,57,1832,1840,1878,1886],[34,40,54,57,1715,1832,1840,1876,1880,1884,1886],[4,14,18,22,24,26,28,30,53],[4,14,22,24,26,28,30,34,40,54,1714,1723,1826,1832,1872,1874,1876,1878]]

def largelearnedp12 : List (List ℕ) := [[14,22,24,26,28,30,34,40,54,1702,1714,1826,1832,1866,1872,1874,1876,1878,1886],[22,24,26,28,30,54,57,1702,1869],[15,34,54,57,173,1668,1676,1836],[4,14,18,22,24,26,28,30,54,1702,1866],[19,34,54,565,780,1668,1712,1714,1722],[22,24,26,28,30,54,57,1702],[34,40,57,104,136,557,748,752,856,896,1016,1096,1136,1144,1668,1713],[34,40,57,104,136,173,557,744,748,752,856,896,1013,1016,1096,1136,1144,1668],[5,34,55,57,104,136,173,557,680,748,780,856,1096],[4,14,16,22,24,26,28,30],[17,34,40,57,1669,1840],[22,24,26,28,30,34,40,55,57,1669],[22,24,26,28,30,34,55,57,1669],[22,24,26,28,30,41,57,1702],[34,42,136,173,856,860,972,976,1016,1677],[34,40,136,173,856,860,972,976,1016,1101,1140,1144],[34,40,136,648,652,1101,1230,1234,1256,1264,1673,1702,1866],[17,22,24,26,28,30,57,1702],[34,40,136,737,748,752,1373,1837],[22,24,26,28,30,57,1702],[34,40,56,136,173,856,972,1662,1678,1708,1712,1714,1726,1841],[17,34,40,56,1668,1676,1678,1734,1840],[15,34,56,1372,1678,1726,1734],[34,40,54,56,65,638,736,738,1662,1708,1712,1714]]

def largelearnedp13 : List (List ℕ) := [[22,24,26,28,30,34,40,56,1662,1668,1676,1678,1708,1712,1714,1726,1734],[17,34,56,676,785,1702,1710,1734],[16,22,24,26,28,30,961],[22,24,26,28,30,34,1673,1702],[16,22,24,26,28,30,34,54,56,1826,1840,1842,1872,1876,1878,1886,1898],[15,34,55,56,680,780,1872,1876,1890],[16,22,24,26,28,30,34,56,1826,1840,1842,1872,1876,1878,1886,1890,1898],[22,24,26,28,30,34,1702],[52,54,56,58,652,785,1372,1404,1425,1843],[54,56,65,124,1356,1372,1425,1679],[40,56,562,565,1372,1402,1577,1843],[40,56,133,562,565,1372,1402,1577,1842],[56,133,562,565,652,680,780,1232,1256,1264,1372,1402,1425,1577,1842],[17,56,133,562,565,652,680,780],[41,56,557,680,780,960,1826,1878,1886],[18,22,24,26,28,30,56,124,652,654,752,754,960,976,1100,1372,1843],[22,24,26,28,30,40,1702],[22,24,26,28,30,1702],[56,104,136,173,557,650,652,676,785,1672,1703],[22,24,26,28,30,52,57,133,664,1875],[22,24,26,28,30,52,57,133,664,736,785,1012,1710],[22,24,26,28,30,53,676,736,785,1012,1264],[22,24,26,28,30,41],[34,40,52,785,1703,1872,1874]]

def largelearnedp14 : List (List ℕ) := [[22,24,26,28,30,35,57,1834],[34,40,1703,1711,1872],[22,24,26,28,30,52,57],[22,24,26,28,30,34,57],[22,24,26,28,30,57],[35,40,56,104,136,557,1703,1842],[22,24,26,28,30],[6,16,24,26,28,30,40,56,1684,1696,1848],[34,496,881,1257,1700,1864],[24,26,28,30,34,39,40,56,136,557,1703],[24,26,28,30,34,40,56,104,136,557,1703],[34,38,40,56,104,136,392,396,400,402,409,557,1672],[34,38,40,56,104,136,392,396,400,402,409,557],[34,40,56,392,400,402,1668,1673,1676,1861],[24,26,28,30,34,40,56,104,136,488,493,1256,1673,1702],[24,26,28,30,34,40,56,104,136,557],[34,104,470,474,1668,1672,1867],[17,34,40,52,56,104,470,474,476,478,493,1396,1668,1672],[20,24,26,28,30,34,39,40,56,104,1672],[34,38,40,56,104,136,392,396,400,402,409,1669,1672],[34,38,40,56,133,136,396,402,409,1668,1672,1840],[34,104,132,136,1668,1672,1676,1840],[34,104,392,396,1668,1672,1861],[34,40,56,104,136,1668,1672,1676,1678,1836]]

def largelearnedp15 : List (List ℕ) := [[24,26,28,30,34,40,56,104,136,1672],[24,26,28,30,34,40,56,104,136],[34,56,58,65,130,1360,1374,1425,1841],[34,56,58,65,130,1360,1374,1425,1677],[34,56,58,65,82,1360,1366,1425,1833],[24,26,28,30,34,40,56,136],[24,26,28,30,34,40,56,134,1669,1672],[24,26,28,30,34,40,56,104,134,1672,1836],[17,34,40,56,402,1394,1668,1676,1697,1840],[40,56,58,65,96,100,105,137,160,172,174,218,224,268,270,409,556,869,881,960,1016,1140,1360,1368,1376,1378,1382,1384,1386,1400,1425,1684,1716,1860],[24,26,28,30,34,40,56,1676,1840],[24,26,28,30,34,40,56,1676],[24,26,28,30,34,40,56],[34,38,40,132,325,392,400,409,1677],[34,40,57,104,392,396,400,881,1092,1120,1140,1672,1676,1861],[24,26,28,30,34,40,137],[19,34,40,104,136,1668,1672,1676],[16,24,26,28,30,34,40,104,1668,1672,1676],[16,24,26,28,30,34,40,104,1668,1676,1860],[24,26,28,30,34,40,104,1668,1676,1860],[24,26,28,30,34,40,105,1676,1880],[24,26,28,30,34,40,1676,1860],[24,26,28,30,34,40,1676],[19,34,40,400,409,881,1677]]

def largelearnedp16 : List (List ℕ) := [[34,40,173,216,224,409,1672,1684],[24,26,28,30,34,40],[34,41,57,172,852,856,858,866,881,1016,1140,1264,1274,1372,1420,1425,1573,1672,1677,1716,1730],[17,34,41,172,224,280,409,852,856,858,866,881,1016,1140,1672,1677,1684,1716],[6,16,18,24,26,28,30,172,1677],[18,24,26,28,30,34,172,1677],[17,36,137,1673,1898],[18,24,26,28,30,34,1677],[34,56,881,1100,1140,1372,1676,1681,1840,1842,1888,1890,1898],[16,18,24,26,28,30,34,173,1673],[16,18,24,26,28,30,34,1673],[34,48,681,869,881,890,1130,1140,1421,1716],[34,48,54,57,1420,1676,1840],[34,65,126,736,754,785,1841],[16,18,24,26,28,30,34,57,172],[16,18,24,26,28,30,34,57,1840],[16,18,24,26,28,30,34,57],[16,18,21,24,26,28,30,34],[34,54,56,173,216,224,409,750,762,785,869,1672],[34,36,48,54,65,78,96,206,342,386,392,396,409,416,496,544,556,570,584,676,681,781,869,1672],[16,18,24,26,28,30,34],[48,52,56,58,160,277,1216,1236,1425,1663],[34,48,52,56,564,681,1236,1260,1425,1847],[34,52,56,277,564,681,1236,1260,1425]]

def largelearnedp17 : List (List ℕ) := [[34,58,277,564,681,860,869,881,1140,1234,1236,1260,1264,1274,1372,1420,1425,1573,1676],[34,58,860,869,881,1101,1140,1522,1562,1573,1676],[34,48,52,56,58,65,160,164,277,1216,1220,1236,1425,1573],[5,34,37,41,48,56,58,160,164,277,564,568,580,680,890,1216,1220,1236,1256,1264,1425,1573],[18,24,26,28,30,34,37],[56,58,277,1682,1846],[34,36,224,276,280,409,1238,1242,1246,1731],[34,36,56,224,276,280,409,869,1238,1242,1246,1378,1382,1386,1425],[34,36,56,224,280,409,869,1238,1242,1246,1378,1382,1386,1425,1532,1573,1682,1846],[34,36,57,860,869,872,881,1140,1372,1420,1425,1508,1522,1532,1562,1573,1676],[34,36,56,226,409,1376,1382,1425,1683],[18,24,26,28,30,34],[34,38,170,325,392,406,409,1847],[34,38,56,104,132,134,212,216,220,222,325,1849],[34,38,56,104,132,134,212,216,220,222,325,392,396,400,402,409],[5,34,38,57,78,104,106,132,137,386,392,396,398,400,409,968,1092,1140,1833],[24,26,30,34,137],[34,38,104,132,136,392,396,400,409,1669],[24,26,28,30,34],[17,57,133],[6,16,18,20,24,26,28,30,38,1662,1714],[24,26,28,30,38,57,133,136,1697],[21,24,26,28,30,38,57,133,136],[24,26,28,30,38,57,133,136]]

def largelearnedp18 : List (List ℕ) := [[38,48,54,386,409,544,582,781,1663],[6,16,24,26,28,30,38,105],[38,54,105,398,556,582,781,1697],[38,54,105,398,409,556,582,781],[38,42,846,881,1086,1101,1140,1827],[6,24,26,28,30,38,54,105,556,1826],[5,38,42,55,881,996,1573,1826],[38,42,48,105,398,556,582,781,1861],[24,26,28,30,38,57,136],[4,6,20,24,26,28,30,38,56,105,1710,1734],[4,20,24,26,28,30,38,136,1662,1678,1710,1714,1734],[5,38,56,224,280,1016,1140,1662,1666,1688,1720,1826],[21,35,38,56,409,1678,1680],[24,26,28,30,38,136,1697],[38,56,65,224,260,280,736,960,1016,1140,1662,1826,1830,1844,1852,1884],[5,38,56,224,280,1016,1140,1826,1830,1844,1852,1884,1888,1890],[38,43,56,881,1016,1140,1663,1890],[38,42,1663,1727,1888],[24,26,28,30,38,42,136,1724,1726],[24,26,28,30,38,42,136,1726],[24,26,28,30,38,42,136],[24,26,28,30,38,136],[52,54,56,681,1132,1404,1420,1425,1727],[52,493,681,776,781,785,1012,1124,1132,1136,1145,1404,1420,1425,1577]]

def largelearnedp19 : List (List ℕ) := [[42,52,56,1140,1142,1274,1280,1573,1891],[1016,1140,1144,1414,1418,1724,1735,1888],[52,56,862,1016,1140,1144,1372,1414,1418,1420,1724,1726,1888,1890],[42,52,56,869,1140,1414,1420,1422,1725,1890],[42,52,869,1016,1144,1414,1418,1422,1724,1899],[52,56,869,1016,1140,1142,1144,1274,1280,1414,1418,1420,1422,1425,1573],[4,20,24,26,28,30,136],[52,493,886,1002,1016,1140,1144,1724,1881],[52,493,869,886,1002,1016,1126,1140,1144,1724],[52,493,869,886,1002,1016,1126,1140,1144],[6,18,20,24,26,28,30,53,493,676,1256],[52,54,65,460,493,960,1000,1887],[20,24,26,28,30,136],[6,12,18,26,28,30,52,133,162,173,493,562,565,652,680,780,982,1002,1100,1126],[36,65,133,224,409,565,960,982,986,1100,1145],[24,26,28,30,136],[18,24,26,28,30,54,960,1144,1717,1886],[18,24,26,28,30,54,65,960,1144,1886],[13,53,493],[42,48,881,1140,1421,1716,1724],[42,224,409,565,869,1680,1684],[42,48,105,324,328,493,858,878,881,1716],[42,105,172,224,324,328,409,493,556,858,869,878,881,980,984,1108,1144,1716],[42,224,409,565,756,780,1013,1680,1712]]

def largelearnedp20 : List (List ℕ) := [[12,16,24,26,28,30,493,1144,1886],[24,26,28,30,53,493,1144,1886],[17,38,137,1678,1734],[12,16,24,26,28,30,38,56,105,1839],[12,16,24,26,28,30,38,42,56,1678,1692],[6,12,16,24,26,28,30,38,42,564,1674,1682,1692],[12,16,24,26,28,30,38,42,564,1674,1678,1682,1692,1724],[24,26,28,30,38,42,564,1717],[13,38,42,137,1838,1870],[12,16,24,26,28,30,38,557],[6,16,24,26,28,30,38,42,564],[16,24,26,28,30,38,42,564],[24,26,28,30,38,42,564],[36,38,42,402,409,478,496,677,1679],[17,36,38,42,53,137,402,409,496],[38,42,137,172,176,222,224,402,406,409,565,869,1679],[42,224,336,409,416,480,492,496,565,869,1696],[42,49,137,172,224,404,409,416,492,496,565,869],[24,26,28,30,53,1144,1886],[38,42,48,52,137,218,224,226,409,565,1674],[16,24,26,28,30,38,49,1144,1886],[17,52,137,869,1016,1140,1142,1144],[24,26,28,30,38,1144,1886],[24,26,28,30,1144,1886]]

def largelearnedp21 : List (List ℕ) := [[24,26,28,30,1144],[36,42,137,222,409,986,1145,1887],[16,18,24,26,28,30,49,172,565],[16,18,24,26,28,30,49,172],[18,24,26,28,30,42,49,172,493,1256],[17,36,42,52,137,869,1110,1145,1890],[18,24,26,28,30,42,49,493,676,1256],[36,42,48,56,137,222,869,1110,1145,1890],[16,18,24,26,28,30,36,42,48,493,584,676,1890],[16,18,24,26,28,30,37,48,493,676,1101,1256,1890],[16,18,24,26,28,30,42,493,584,676,1256,1890],[42,48,137,222,224,280,409,866,986,1016,1142,1145,1891],[24,26,28,30,39,42],[42,56,224,409,565,869,1110,1145,1890],[24,26,28,30,42],[16,24,26,28,30,36,1890],[37,137,224,280,409,1100,1104,1145,1890],[24,26,28,30,1890],[24,26,28,30,36],[24,26,28,30],[8,14,20,22,26,28,30,56,1676,1843,1849,1891],[20,26,28,30,56,409,1891],[35,38,56,136,172,226,474,478,482,484,564,586,677,1126,1842,1849,1890],[172,556,564,1682,1838,1846,1870]]

def largelearnedp22 : List (List ℕ) := [[35,56,136,172,226,409,474,478,482,484,496,564,586,677,680,1126,1265,1396,1398,1424,1842,1890],[34,37,40,56,224,409,476,482,496,557,560,584,586,677,1257,1396,1398,1424,1697,1842],[34,37,56,136,224,409,476,478,482,496,557,584,586,677,680,1126,1257,1396,1398,1424,1842,1890],[34,38,48,56,409,476,496,1126,1678,1701,1842,1890],[38,56,172,406,409,474,482,496,556,564,586,1865],[37,56,136,224,409,474,476,478,482,484,496,584,586,677,680,1126,1257,1265,1396,1398,1424,1842,1890],[37,56,136,224,409,474,476,478,482,484,496,584,586,677,680,1126,1257,1265,1396,1398,1424,1890],[26,28,30,56,137,172,176,409,564,1701],[26,28,30,37,56,224,409],[38,40,557,561,562,1679],[38,40,56,137,557],[38,40,56,478,557,584,677,1843],[38,56,557,677,680,1134,1676,1678,1842,1869,1890],[8,20,22,26,28,30,35,56,136,557,1678,1685,1842,1890],[20,22,26,28,30,56,405,409,557,1676,1678],[20,22,26,28,30,56,405,409,557,1676],[20,22,26,28,30,56,405,409,557],[8,20,22,26,28,30,38,56,136,1869,1890],[34,38,40,56,409,496,1126,1676,1678,1701,1842,1890],[34,40,56,405,409,476,496,677,1126,1257,1396,1398,1424,1676,1678,1842,1890],[34,38,56,136,472,478,677,1676,1843],[34,40,56,136,405,409,472,476,478,496,677,1126,1257,1396,1398,1424,1676,1890],[34,40,56,136,405,409,472,476,478,496,652,672,677,1126,1257,1265,1396,1398,1424,1890],[38,48,56,476,562,586,677,781,1677]]

def largelearnedp23 : List (List ℕ) := [[34,48,56,136,472,476,558,586,781,1676,1865],[34,56,136,405,409,472,476,478,496,586,652,672,677,680,784,1126,1257,1265,1396,1398,1424,1890],[6,26,28,30,35,56,225,409,1701,1868],[41,49,225,677,680,784],[15,51,225],[26,28,30,56,136,225,409],[38,56,137,225,405,406,478,482,496,1865],[26,28,30,37,56,409],[38,56,405,1682,1696,1839,1843],[6,20,26,28,30,35,37,49,51,224,280,399,408],[26,28,30,37,38,49,56,137,1676,1698,1843,1861],[6,8,20,26,28,30,38,51,225,408,1692,1696,1839,1860],[26,28,30,38,49,56,137,225,408,1692,1696,1698,1718,1843,1860],[19,38,1692,1696,1839,1860],[6,8,18,20,26,28,30,408],[26,28,30,37,38,49,56,137,1676,1692,1696,1698,1704,1718,1843],[7,38,48,677,680,1682,1704,1706,1712,1839],[9,48,56,1682,1839],[26,28,30,37,38,56,137,1668,1672,1676,1678,1682,1692,1696,1698,1704,1706,1712,1718,1726,1734],[19,38,136,1668,1672,1676],[21,38,56,478,677,1134,1676,1678,1704],[38,49,56,172,225,277,478,564,584,677,680,784,1134,1676,1678,1704],[26,28,30,37,38,56,1864],[48,50,56,277,404,417,658,674,1709]]

def largelearnedp24 : List (List ℕ) := [[48,56,160,225,384,404,408,417,564,736,756,781,864,866,868,888,890,896,898,980,982,1006,1012,1014,1847],[9,48,56,384,417,580,674,677,680,784,1265,1872],[8,26,28,30,37,48,56,396,404,406,410,417,580,880,1846],[26,28,30,37,48,56,384,396,404,406,410,417,580,880,1872],[26,28,30,37,49,51,408,417,880],[8,18,26,28,30,37,49,224,408,869],[7,49,50,56,417,582,674,677,680,784,1424,1572,1872],[6,18,26,28,30,49,50,56,172,408,1872],[26,28,30,37,56,1864],[21,37,50,677,1850,1868,1882],[6,8,26,28,30,37,50,408,1850,1856,1862,1868,1882],[38,56,104,132,325,334,1118,1693,1836,1840,1842,1890],[19,56,677,680,784,1257,1265,1836,1840,1842,1856,1860,1870,1890],[9,41,56,556,677,680,784,1838,1846,1870],[18,20,26,28,30,41,56,408,1838,1842,1846,1870],[7,40,56,1838,1842,1846,1868,1870],[172,556,564,1838,1846,1870],[40,48,56,277,564,566,758,1846,1868,1870,1876],[40,566,758,780,1683,1868,1876],[18,20,26,28,30,56,408,1838,1842,1846,1850,1868,1870,1876],[26,30,37,56],[6,8,18,20,26,28,30,37,51,173],[6,18,26,28,30,37,40,51,557,565,1705,1876],[6,18,20,26,28,30,37,51,565]]

def largelearnedp25 : List (List ℕ) := [[6,18,26,28,30,37,40,51,565,1868],[18,26,28,30,37,40,49,51,565,1868],[7,40,49,57,565,677,680,1404,1424,1572,1868],[21,37,40,50,662,1265,1868],[18,26,28,30,37,40,49,565,1868],[6,18,20,26,28,30,37,40,565,1846,1872],[7,40,49,57,677,1404,1424,1572,1845,1872],[40,50,281,662,1265,1850,1872],[18,26,28,30,37,40,49,565,1846],[19,34,40,136,644,648,652,1709],[38,40,325,565,576,668,680,1873],[26,28,30,37,40,49,565,1870],[19,38,40,564,1672,1682,1692,1704,1870],[18,20,26,28,30,37,38,40,173,1686,1696],[6,8,18,20,26,28,30,50],[6,18,20,26,28,30,38,50,1686,1846],[9,38,40,49,51,1696,1869],[26,28,30,37,38,40,49,1682,1870,1872],[26,28,30,37,40,49,1682,1870,1872],[26,28,30,37,39,40,49,50,564,1850,1862,1868,1876,1882],[7,49,564],[38,50,225,1682,1850],[26,28,30,37,40,49,50,564,1682,1850,1856,1860,1862,1868,1876,1882],[19,38,40,1673,1856]]

def largelearnedp26 : List (List ℕ) := [[26,28,30,37,40,49,51,224,409,564,1856,1860,1868],[26,28,30,37,40,49,51,224,564,1856,1860,1868],[19,40,780,1257,1856,1868,1876],[26,28,30,37,40,49,1682,1870],[18,26,28,30,37,40,49,1871],[26,28,30,37,40,49,1871],[19,40,1257,1683,1700],[26,28,30,37,38,40,49],[26,28,30,37,40,49],[34,38,50,281,342,486,492,677,1693],[34,50,281,325,342,486,492,677,1257],[34,38,416,492,496,881,1257,1857],[26,28,30,37,49],[6,26,28,30,37,38,41,51,1838,1846,1870],[19,38,40,48,1257,1856,1868,1870,1876],[6,18,26,28,30,37,51,173],[6,26,28,30,37,38,51,1838,1846,1856,1868,1870,1876],[26,28,30,37,38,51,1856,1865],[38,48,172,565,677,680,1674,1682,1704,1706],[48,172,556,564,1674,1682,1706,1870],[48,172,556,564,1674,1682,1706],[38,48,172,677,680,1674,1682,1704,1706],[26,28,30,37,38,51,1856],[26,28,30,37,38,51]]

def largelearnedp27 : List (List ℕ) := [[34,38,173,1839],[37,38,48,50,280,1682,1846],[26,28,30,37,38,173],[19,38,50,1683,1856],[26,28,30,38,48,50,172,1683,1838],[38,48,172,474,584,586,677,680,1682,1701],[26,28,30,37,38,1838],[26,28,30,37,38],[26,28,30,37,51,172,1674,1682,1706],[26,28,30,37,172,1682,1701],[26,28,30,48,50,172,404,417,580,1674,1682,1708,1838],[26,28,30,48,50,172,396,404,417,580,1674,1682,1708],[26,28,30,37,50,172,1682],[26,28,30,37,172,1682],[18,20,26,28,30,173,408],[9,48,417,580,674,677,680,784,1683,1698,1708],[26,28,30,37],[7,36,48,417,1674,1680,1684,1698,1844],[20,26,28,30,48,417,1674,1680,1684,1698,1844],[48,416,492,496,1257,1692,1696,1700],[26,28,30,48,1683],[18,20,26,28,30,173,1680,1844],[26,28,30,417,1683],[26,28,30,1683]]

def largelearnedp28 : List (List ℕ) := [[18,26,28,30,38,49,1680,1844,1865],[18,26,28,30,38,49,1680,1844],[19,36,38,40,472,492,557,564,584,1682,1701],[26,28,30,38,49,1680,1844],[19,36,38,1681,1856],[26,28,30,38,49,564,1681],[26,28,30,38,49,1681,1685],[21,38,416,1681,1856,1860],[26,28,30,49,416,1681],[7,49,677,680,1404,1424,1572,1678,1845,1872],[21,38,416,1692,1696,1845],[6,18,20,26,28,30,38,1845],[26,28,30,49,416],[36,38,325,336,480,492,1257,1845],[19,36,38,48,677,680,1682,1844,1856],[19,36,38,48,480,488,677,680,1257,1682],[36,38,48,474,480,584,586,677,680,1682,1701,1844],[36,38,48,677,680,1680,1682,1838,1844,1846,1868,1870],[36,48,416,474,480,482,492,496,584,586,677,680,1257,1682,1844],[26,28,30,416],[26,28,30,38,48,1845],[26,28,30,38,1845],[21,36,408,660,662,674,677,880,1845,1862,1872],[7,36,49,654,677,680,1265,1404,1424,1572,1845,1872]]

def largelearnedp29 : List (List ℕ) := [[26,28,30,1845],[36,41,48,65,96,105,160,172,544,556,677,680,736,784,1682],[26,28,30,48,1709],[36,40,48,105,174,650,660,1265,1682,1684,1708,1844,1846],[26,28,30,48,96,105,133,137,172,174,396,400,556,860,1100,1684,1846],[26,28,30,48,96,105,133,137,172,174,218,396,400,556,860,1100,1846],[7,26,30,48],[26,28,30,48],[26,28,30,41],[6,20,26,28,30],[21,36,40,417,660,664,674,1265,1844],[26,28,30],[36,40,224,276,406,417,565,737,756,760,764,774,1844],[40,226,281,406,408,417,1681],[40,224,226,276,406,417,565,737,756,760,764,774,961,1100,1144,1372,1844],[40,281,408,417,1850,1862],[40,224,276,280,737,760,764,1848,1852,1876],[40,224,226,276,406,417,565,737,756,760,764,774,961,1100,1144,1372],[36,40,224,409,737,756,760,1845],[40,224,276,281,409,565,737,756,760,764,1013],[36,40,224,226,281,336,404,406,408,416,482,656,658,756,760,762,768,772,774,778,784,786,1013,1681],[36,40,224,226,281,336,404,406,408,416,482,565,656,658,737,756,760,762,768,772,774,778,784,786,1013],[40,133,137,166,178,260,278,281,1236,1372,1376,1532,1666,1678,1690,1728,1732,1845],[40,133,137,166,178,260,278,281,565,742,754,766,780,961,1100,1144,1236,1268,1372,1376,1408,1532,1713]]

def largelearnedp30 : List (List ℕ) := [[40,408,737,868,961,1013,1016,1712,1876],[7,20,28,30,40,49,281],[40,224,276,280,565,756,760,764,1877],[7,20,28,30,40,49],[40,48,105,172,556,558,750,758,780,782,961,1100,1144,1372,1713],[7,30,40],[20,22,28,30,40,565,1100,1141,1420,1704,1868],[20,28,30,40,43,565,1848,1868,1882],[40,224,409,565,1681,1848],[25,40,42,1681,1872],[20,24,28,30,40,42,409,565,1681,1848,1856],[6,20,24,28,30,42,225,408,565,1681,1682,1850,1856,1860],[10,20,22,28,30,40,42,565,1832,1868,1872,1898],[20,28,30,40,565,1832,1848,1856,1866,1868,1872,1882,1898],[8,11,20,22,24,28,30,40,1673,1866],[19,40,173,1673,1832],[8,18,20,22,24,28,30,40,1673,1866],[20,24,28,30,40,42,564,1681,1832,1838,1846,1866,1868,1870,1880],[18,20,23,24,28,30,40,42,1868,1872,1874,1880],[8,18,20,22,24,28,30,40,1866,1894],[18,20,24,28,30,40,42,564,1838,1846,1850,1854,1862,1866,1868,1870,1872,1874,1880,1894],[40,42,104,325,552,557,1832,1868],[20,24,28,30,40,42,564,1832,1836,1838,1846,1850,1854,1862,1866,1868,1870,1872,1874,1880,1894],[20,22,24,28,30,40,173,1832,1836,1866,1894]]

def largelearnedp31 : List (List ℕ) := [[19,40,557,1832,1836],[20,24,28,30,40,564,1832,1836,1838,1846,1850,1854,1862,1866,1868,1870,1872,1874,1880,1882,1894],[9,40,492,496,557,1265,1850,1860,1862,1868,1872],[10,16,20,28,30,40,492,496,557,677,1265,1832,1836,1850,1860,1862,1868,1872,1880],[23,25,40,173,961,1844,1872],[20,28,30,40,1877],[19,40,173,748,1013,1876],[40,680,780,784,1713,1868,1872],[6,8,18,20,22,25,28,30],[20,22,28,30,40,173],[8,18,20,22,28,30,40],[9,40,556,737,750,782,961,1013,1016,1876],[23,40,556,756,758,961,1013,1876],[172,556,564,1674,1682,1706],[40,42,48,556,565,1674,1704,1706],[20,22,28,30,40,43,565,1420,1577,1704,1726],[17,20,22,28,30,40,325,416,492,565,576,1692,1704,1726,1730],[20,28,30,40,556,1713],[28,30,40,556],[20,28,30,40,173],[23,40,557,780,961,1013,1876],[20,28,30,40,42,869],[19,40,1668,1837],[20,28,30,40,42]]

def largelearnedp32 : List (List ℕ) := [[9,40,557,737,780,890,898,961,1013,1016,1141,1876],[20,28,30,40],[52,104,325,556,564,748,750,758,782,1230,1270,1573,1713],[650,681,961,972,1016,1144,1230,1264,1420,1425,1720,1837],[34,52,556,564,1228,1230,1236,1260,1731,1836],[34,52,56,104,325,556,564,1226,1228,1230,1236,1260,1425,1836],[172,556,564,1228,1236,1260,1895],[52,56,104,325,556,564,1226,1228,1230,1236,1260,1425,1836],[8,19,20,22,28,30],[6,8,20,22,28,30,48,1730,1894],[8,20,22,28,30,57,172,1730,1894],[8,20,22,28,30,57,1730,1894],[17,52,57,961,1016,1144,1884,1895],[7,57,564,1016,1144,1260,1895],[8,20,22,28,30,57,1730],[8,20,22,28,30,53],[11,48,52,56,137,560,584,681],[8,16,20,22,28,30],[8,20,22,28,30,57],[52,56,556,652,654,681,1016,1132,1134,1144,1230,1232,1234,1264,1280,1282,1414,1418,1425,1731],[8,20,22,28,30],[48,52,1425,1730,1898],[172,472,480,556,564,584,1703],[172,225,404,408,556,564,580,681,864,866,868,888,890,961,982,1006,1016,1144,1838,1870]]

def largelearnedp33 : List (List ℕ) := [[48,225,408,568,580,868,870,888,890,961,986,1006,1016,1144,1871],[48,50,225,568,681,1850,1870],[9,556,580,681,888,890,961,974,1006,1016,1144],[42,48,881,890,961,1006,1016,1707],[42,48,681,881,890,961,1006,1016],[36,42,173,224,869,980,984,1721],[20,28,30],[40,42,224,276,565,570,582,737,756,760,764,888,986,998,1004,1013,1016,1128,1144,1720],[40,42,224,276,557,565,568,570,572,582,737,756,760,764,888,986,998,1004,1013,1016,1128,1144],[40,50,557,890,1141,1704,1718],[40,173,224,276,557,737,756,760,868,880,890,980,1004,1018,1141,1721],[40,224,276,280,565,756,760,764,1013,1712],[28,30],[40,50,136,557,560,1101,1373,1840,1868],[8,20,22,30,40,50,1705,1877],[8,22,30,40,50,565,756,1877],[4,8,12,18,20,22,26,30],[4,8,20,22,30,40,43,50,1877],[40,136,556,564,1096,1098,1101,1106,1130,1725,1844],[8,20,30,40,43,50,281,1877],[8,30,40,50,281,756,1877],[30,40,50,224,281,1877],[58,65,1090,1373,1508,1570,1576,1725,1830,1877],[43,51,281,1140,1144,1421]]

def largelearnedp34 : List (List ℕ) := [[5,281,1373,1570,1576,1725,1877],[19,42,1101,1668,1877],[21,34,40,1672,1877],[4,8,22,30,34,40,42,1877],[30,40,224,281,1877],[27,40,42,224,281,1104,1108,1110,1128,1140,1421,1876],[4,8,20,22,26,30,40,42,173],[34,40,58,65,102,130,136,1373,1837],[5,34,40,42,136,173,281,1096,1373,1421],[34,40,42,136,218,222,281,856,860,1017,1373,1673],[26,30,40,42,173,281],[34,65,130,260,274,281,1677],[5,34,40,274,281,1373],[8,26,30,34,40,42,281],[40,42,58,256,281,736,960,1086,1114,1136,1138,1725,1876],[30,40,42,224,281],[50,54,65,260,281,848,872,1017,1854],[5,50,281,872,988,1017],[4,8,12,22,26,30,35],[34,40,50,274,862,872,1017,1373,1855],[40,224,281],[34,40,43,50,1101,1140,1144,1421,1719,1723,1832,1836,1838,1868,1870,1872],[34,40,50,132,136,138,560,562,652,860,862,976,1017,1101,1140,1144,1421,1841],[4,8,30,34,40,42,50,1662,1712,1714,1716,1720,1883,1884]]

def largelearnedp35 : List (List ℕ) := [[4,8,30,34,40,50,1017],[4,8,30,34,40,50,1662,1712,1714,1716,1720,1883],[34,40,42,50,136,224,1016,1096,1098,1101,1106,1130,1682,1684,1686,1698,1704,1708,1712,1714,1716,1718,1722,1725,1876,1882,1885],[4,30,34,40,50,224,1840],[40,42,50,224,1016,1716,1838,1846,1848,1850,1862,1868,1870,1880,1882,1884],[4,30,34,40,50,224],[8,30,40,50,172,556,756,974,982,1006,1013,1885],[4,30,40,50,224],[4,30,40,42,224,565,1721],[4,8,12,20,22,24,26,30],[4,22,26,30,40,42,224,565,1705],[4,22,30,40,42,224,565,1884],[19,34,40,136,396,400,409,881,1373],[4,10,26,30,34,40,42,224,396,409,565,660,856,881,972,1016],[4,30,40,42,224,565,1884],[23,42,172,556,564,1848],[4,8,30,35,40,42,564,1848,1884],[27,34,40,136,564,1373,1876],[4,8,22,30,34,40,42,564],[4,8,30,40,42,564,1848,1884],[4,30,40,42,224,1884],[4,8,20,22,26,30,40,392,409,496],[34,40,104,132,136,325,392,396,400,409,416,1373],[21,36,38,176,332,400,416,1841]]

def largelearnedp36 : List (List ℕ) := [[4,30,40,43,224],[4,8,22,30,34,40,42,1885],[23,40,42,1716,1885],[4,30,40,224],[40,42,65,565,960,962,1086,1101,1128,1144,1885],[40,42,65,546,736,960,1086,1101,1128,1144,1869,1884],[40,42,65,546,565,736,960,962,1086,1101,1128,1136,1144,1421],[40,65,546,960,1006,1017,1705],[40,65,546,565,736,960,962,1086,1101,1128,1136,1140,1144,1421],[40,54,65,546,960,1006,1017,1869],[40,54,96,98,136,160,544,556,564,960,974,1017,1101,1663],[40,43,54,65,96,98,136,160,544,546,564,960,1101,1140,1144,1421,1704],[40,42,136,162,556,564,1086,1096,1098,1101,1106,1130,1827],[40,42,54,65,96,98,136,160,162,544,556,564,1086,1096,1098,1101,1106,1130,1421],[40,54,65,96,98,136,160,162,544,546,564,960,1086,1096,1098,1101,1106,1128,1130,1140,1144,1421,1704],[40,54,65,96,98,136,160,162,544,546,564,960,1086,1096,1098,1101,1106,1128,1130,1140,1144,1421],[40,42,136,564,980,1004,1013,1096,1098,1101,1106,1128,1130,1144,1725],[30,40,224],[41,42,136,564,972,1004,1013,1101,1836,1838,1846,1870,1884],[4,12,26,30,42,173,224,564,972,1016,1836,1846,1880,1884],[30,42,55,65,224,564,960,1016,1832,1836,1838,1846,1870,1880,1884],[8,20,26,30,42,557,961,1016,1832,1836,1880,1884],[30,42,55,65,224,564,1016,1832,1836,1838,1846,1870,1880,1884],[4,8,30,34,41,42,556,564,1016,1673,1681,1721,1838,1880]]

def largelearnedp37 : List (List ℕ) := [[4,30,42,55,224,556,564,1016,1836,1838,1846,1870,1880,1884],[19,34,42,1673,1832],[4,8,12,18,20,30,34,42,1016,1673,1720,1880,1884],[30,42,55,224,564,1016,1832,1836,1838,1846,1870,1880,1884],[23,41,42,54,136,564,1016,1101,1836,1838,1846,1870,1878,1880,1884,1886],[35,136,564,1101,1373,1838,1846,1870],[22,30,42,224,564,1016,1720,1826,1832,1836,1838,1846,1870,1878,1880,1884,1886],[8,20,22,26,30,34,42,557,1017,1826,1832,1836],[34,42,54,173,1017,1720,1836,1884,1886],[22,30,42,224,564,1720,1826,1832,1836,1838,1846,1870,1878,1880,1884,1886],[22,30,42,55,224,564,1721,1826,1832,1836,1838,1846,1870,1880,1884],[22,30,42,224,564,1826,1832,1836,1838,1846,1870,1878,1880,1884,1886],[30,42,224,564,1889],[30,42,224,564,1724],[42,224,409,565,1101,1104,1108,1724],[27,41,565],[5,41,55,565],[25,41,565],[8,22,30,41,42,55,565,1676],[4,8,12,22,24,26,30,41,42,54,1836,1878],[30,42,224,1724],[5,41,42,565,1662,1714,1722],[42,54,65,96,136,160,544,564,846,960,962,1101,1373,1662,1716,1720,1722],[5,41,42,136,1101,1373,1662,1672,1674,1682,1706,1714,1716,1720,1722]]

def largelearnedp38 : List (List ℕ) := [[4,8,20,26,30,34,41,556,780,857,1674,1838],[19,34,42,1668,1837],[25,34,1373,1728,1837],[4,8,12,18,20,24,26,30],[13,55,65],[4,8,12,20,24,26,30,42,1668,1672,1716],[25,41,42,136,564,1101,1373,1672,1674,1682,1706,1728],[27,41,42,136,564,1101,1672,1674,1682,1706,1720],[4,8,30,41,42,564,1668,1672,1674,1677,1682,1706,1714,1716,1720,1728],[30,42,224],[34,54,978,1017,1373,1840,1886],[34,54,136,173,974,978,1017,1373,1672],[8,30,41,55,1012,1017],[34,54,136,173,974,978,1017,1373],[34,172,556,558,564,1673],[34,44,48,564,781,1378,1402,1421,1683],[34,136,138,172,556,562,564,781,1672,1682,1706],[34,54,136,138,556,558,562,564,781,974,978,1017,1257,1262,1373,1378,1402,1421,1424],[8,25,30,41,960,972,974,980,1004,1012,1017],[48,54,105,556,972,1004,1017,1707],[54,105,556,781,972,1004,1017],[48,50,54,65,96,105,160,172,174,216,218,396,404,406,408,410,417,556,580,856,880],[30,35,224],[34,54,65,126,960,978,1017,1373,1886]]

def largelearnedp39 : List (List ℕ) := [[34,54,65,126,960,978,1017,1373],[172,556,564,972,980,1004,1887],[30,224],[4,24,26,30,565],[35,54,132,136,225,1017,1098,1101,1144,1146,1421,1886],[43,54,225,1140,1144,1421,1719,1723,1850],[54,132,136,222,225,860,978,1017,1098,1101,1140,1144,1146,1373,1421,1886],[42,54,1016,1723,1880,1884],[30,34,54,1720,1826,1876,1878,1880,1882,1884,1886],[30,34,54,1826,1832,1836,1838,1846,1876,1878,1880,1882,1884,1886],[30,54,1841,1886],[35,42,54,132,136,225,1101,1674,1682],[34,54,172,225,1682,1839],[30,54,172,856,1884,1886],[30,49,54,172,1886],[30,54,172,1886],[30,54,1886],[8,30,34,55,857,1837,1884],[8,18,24,30,34,42,55,1720,1884],[8,24,30,34,49,55,857,1685,1884],[30,34,55,173,857,1674,1884],[34,44,1228,1257,1368,1421,1424,1673],[25,34,173,1368,1373,1421],[34,42,136,173,225,856,860,972,976,1101,1686,1840,1850]]

def largelearnedp40 : List (List ℕ) := [[30,34,55,173,1837,1884],[4,8,24,26,30,34,1672,1674,1677,1682,1885],[30,34,55,173,1672,1837],[30,34,55,173,1672],[34,43,217,1101,1140,1144,1421,1685,1886],[30,34,173,1886],[5,34,42,55,1673,1884],[27,34,42,1673,1884],[8,30,34,42,55,172,1673],[11,13,172,225],[172,556,564,974,982,1006,1721],[4,8,13,26,30,34,42,55,172],[4,8,30,34,38,42,44,55,172,474,564,584,586,677,680,784,1000,1720],[19,25,34,42,136,565,652],[4,8,26,30,34,42,55,172],[34,42,172,564,1096,1098,1106,1130,1672,1889],[5,34,42,136,172,564,980,1004,1013,1086,1096,1098,1101,1106,1128,1130,1140,1144,1373,1672,1714,1722],[5,34,42,55,136,172,1096,1098,1101,1106,1128,1130,1136,1140,1144,1373,1421,1672],[4,8,30,34,40,42,961,1004],[8,30,34,42,55,172],[4,30,34,41,42,172,218,408,564,1720,1725],[34,41,42,55,172,174,225,564,1096,1098,1106,1130,1144,1720,1889],[30,34,41,42,55,172,1720],[34,42,172,225,564,982,1096,1098,1106,1130,1144,1421,1721]]

def largelearnedp41 : List (List ℕ) := [[34,40,42,136,218,222,225,281,408,860,868,1101,1673],[30,34,42,55,172],[30,34,1886],[41,43,48,55,172,225,556,856,1101,1140,1144,1421,1886],[42,48,50,105,172,1098,1101,1106,1847],[42,48,105,172,1098,1106,1421,1683],[30,35,41,42,55,1889],[30,41,1886],[40,42,105,172,225,1098,1101,1106,1421],[30,1886],[35,49,132,136,225,1101],[34,50,220,222,225,402,1373,1576,1840,1848,1850,1862],[43,132,136,220,222,225,402,1101,1140,1144,1373,1421,1576,1840,1887],[35,42,132,136,225,1101,1674,1887],[30],[34,42,44,49,132,136,225,1677],[34,42,44,49,132,136,225,1101],[34,42,44,48,225,1839],[34,44,104,132,1101,1672,1737,1836],[34,44,104,132,136,1101,1672,1836],[34,42,44,1368,1421,1837],[34,42,132,136,225,1101,1373,1674],[34,42,136,225,1101,1372,1673],[34,42,48,132,170,178,225,1672,1674,1836,1841]]

def largelearnedp42 : List (List ℕ) := [[34,37,42,132,225,1101,1228,1234,1236,1256,1260,1264,1425,1672,1674,1836],[34,42,132,225,1101,1228,1234,1236,1256,1260,1264,1425,1672,1674,1688,1836],[34,42,132,136,225,1101,1228,1234,1236,1256,1260,1264,1370,1374,1425,1674,1688],[34,42,45,132,136,225,1101,1674],[34,42,132,136,225,1101,1674],[34,42,132,136,225,1101],[34,48,225,1675,1841],[34,37,48,225,1672,1832,1836,1841,1889],[34,48,225,1672,1832,1836,1841,1889],[34,36,49,225,1672,1832,1836,1852],[34,43,132,225,1101,1672,1836,1841],[34,37,43,49,225,1672,1836],[34,43,49,225,1668,1672,1688,1836],[34,36,48,1668,1672,1674,1688,1836],[34,132,136,225,1101,1672,1836],[34,48,225,1101,1673,1676],[6,12,14,20,22,24,26,28],[27,43,1101],[6,12,14,20,22,26,1425],[34,44,136,1101,1673],[34,44,132,136,225,1101],[34,48,52,650,785,1264,1370,1425,1837],[34,132,136,225,1101],[34,136,225,1101,1673,1836]]

def largelearnedp43 : List (List ℕ) := [[14,26,34,45,133,225,1672,1836],[14,26,34,49,133,225,1672,1836],[34,40,42,44,737,752,1841],[34,44,49,133,225,1101,1672,1836],[36,56,133,1677],[34,49,136,225,1101,1836],[45,57,133],[34,48,133,225,1672,1836,1841],[34,136,225,1101,1836],[34,44,1093,1832,1900],[34,136,225,1101],[34,48,56,137,1097,1836],[34,56,137,225,1097,1840],[34,56,137,225,1097],[45,57,137],[6,14,18,20,22,26,28,53,1425],[27,34,1101,1720,1837],[6,10,14,18,20,22,26,28],[11,51,225],[34,36,221,222,225,1101,1841],[19,34,44,1673,1832],[34,173,225,1101],[10,18,34,225,1101],[19,34,44,48,137,1101,1840]]

def largelearnedp44 : List (List ℕ) := [[19,34,44,48,137,1101],[34,225,1101],[34,42,44,50,396,417,1675],[34,42,44,48,50,137,225,1674],[11,34,42,44,137,225,1836],[34,40,42,44,737,750,1675],[34,40,42,44,48,137,225,1674],[18,27,34,42,44,137,225,1836],[18,27,34,42,44,137,225],[18,34,42,44,137,225],[11,42,225,1698,1837],[18,34,42,44,225,1837],[34,136,1737,1836,1840],[10,18,20,22,28,34,42,44,136,1836],[42,44,50,225,408,497,1901],[18,34,42,44,225],[44,565,1680,1844],[34,44,564,1672,1674,1682,1706,1836],[34,44,50,225,1672,1674,1680,1682,1684,1686,1689,1706],[6,18,28,43,51,225],[34,44,50,225,1837],[34,44,50,225,1737],[34,50,564,1674,1683,1687,1836,1838,1846,1870],[34,44,50,225]]

def largelearnedp45 : List (List ℕ) := [[34,44,225,1675],[18,34,44,225],[34,44,168,325,565,1901],[34,44,168,325,565],[34,44,104,325,564,1674,1737],[34,44,225],[34,56,564,1228,1236,1260,1368,1376,1400,1425,1672,1836],[34,225,564,1672],[34,225,564],[34,36,56,1370,1425,1673],[34,36,56,1370,1425,1837],[34,36,569,1382,1735],[34,225],[56,1239,1728,1892],[36,44,56,225,1678,1680,1682,1726,1732,1844,1895,1899],[36,56,225,1425,1678,1680,1682,1686,1724,1726,1728,1732,1734],[56,1424,1728,1732,1899],[20,22,36,56,1424,1678,1724,1726,1730,1732,1734,1893,1898],[36,56,225,1678,1680,1682,1686,1724,1726,1728,1730,1732,1734],[10,14,24,28,49,225,557,1373],[6,10,14,22,24,49,137,556,1668,1841],[13,225,1256,1706,1897],[12,24,36,44,57,136,173,225,1680,1686,1897],[12,24,36,44,57,136,225,556,1674,1680,1682,1686,1706,1897]]

def largelearnedp46 : List (List ℕ) := [[36,44,137,225,556,565,1680,1706],[12,24,36,44,57,225,556,1668,1674,1680,1682,1686,1706,1897],[36,44,137,225,557,564,1682,1706],[19,35,557],[12,24,57,136,225,557,1665,1698,1897],[36,44,57,225,1424,1665,1668,1674,1680,1682,1686,1698,1706,1728,1732,1892],[6,10,14,28,36,44,137,225,557,1680,1682,1706,1893],[6,10,14,28,36,44,137,225,1668,1674,1680,1682,1706,1893],[11,36,225,1698,1893],[36,44,57,225,1424,1665,1668,1674,1680,1682,1686,1698,1706,1728,1732],[36,44,225,565,1425,1680,1686,1706,1712],[19,35,564,1674,1682,1706],[24,28,36,44,225,556,564,1674,1680,1682,1686,1706],[36,44,57,225,1665,1668,1674,1680,1682,1686,1698,1706,1712,1728,1732],[36,225,1665,1668,1674,1678,1680,1682,1686,1698,1706,1712,1724,1726,1728,1730,1732,1734],[6,12,14,18,45,206,225,1100,1372,1660,1665,1686],[11,44,225,1686,1698],[14,18,136,206,225,557,1660,1665,1686,1698,1704,1712],[6,14,18,28,44,48,225,408,561,564,866,868,982,1682,1686,1698,1706],[14,172,206,225,408,564,866,868,982,1660,1665,1674,1682,1686,1698,1704,1706,1712,1734],[225,1689,1734],[50,56,225,1686,1734],[45,50,57,225,1682,1734],[50,225,1686,1734]]

def largelearnedp47 : List (List ℕ) := [[29,35,564,1838,1846,1870],[35,136,564,1373,1838,1846,1870],[44,173,1680,1844],[36,44,50,1421,1687,1896],[44,50,136,225,1734],[44,50,225,1734],[50,137,172,1368,1372,1425,1683,1734],[20,22,35,45,50,172,1683,1734,1839],[45,50,133,1687,1688,1734],[35,50,56,1228,1236,1260,1368,1372,1420,1425,1683,1687,1688,1734],[50,225,1734],[10,14,20,22,35,57,136,1372,1425],[6,18,28,44,51,225,1736],[19,35,136],[51,57,136,225,1372,1736],[51,57,136,225,1736],[7,44,225,1736],[51,57,225,1736],[225,565,1734],[44,51,225,564,1736],[19,35,56,564,1228,1236,1260,1425,1734],[10,14,18,20,22,24,28,557],[6,10,14,18,20,22,24,28],[225,1734]]

def largelearnedp48 : List (List ℕ) := [[7,225],[37,556,1674,1682,1706],[18,36,56,225,1678,1686,1724,1726],[18,24,28,51,225],[18,45,56,225],[18,56,225],[56,225],[19,225],[44,225],[225],[1680,1684,1853],[45,1735],[57,1735],[6,12,14,18,20,22,26,28],[15,57,1372],[13,172,1838,1846,1870],[23,44,1725,1848],[27,44,557,1868,1876],[14,35,44,172,564,1838,1846,1848,1868,1870,1876,1892],[7,44,57,1681,1896],[29,44,1681,1896],[6,12,14,20,22,26,28,1681,1856],[14,35,44,57,172,1838,1844,1846,1848,1856,1868,1870,1876,1892,1896],[35,44,57,172,1901]]

def largelearnedp49 : List (List ℕ) := [[15,44,57,1732,1869],[12,14,20,22,26,28,44,1373,1728,1732],[35,57,172,1372,1377,1682,1846],[26,28,35,44,57,172,565],[6,12,14,18,20,26,28,44,1684,1728],[26,28,35,44,57,172],[29,35,44,172,1674,1680,1682,1706,1732],[27,41,172,1674,1682,1706],[35,44,57,172],[40,44,173,737,756,760,1680,1684],[40,44,737,756,1681],[40,44,173,737,756,760],[12,14,35,44,173,564,566,658,676,681,1264,1845],[27,35,44,173,564],[15,35,44,57,1673],[35,44,57,564,1681],[6,14,18,20,22,26,28,44,1684,1710,1728,1837],[15,35,57,173],[44,52,482,493,1845],[44,52,173,482,493],[35,44,57,656,680,1265,1681],[11,35,44,57],[21,35,44,57,1728,1732,1837],[14,20,22,28,40,44,173,760,1668,1684,1710,1728,1837]]

def largelearnedp50 : List (List ℕ) := [[27,35,41,44,173],[19,35,173],[29,35,173],[6,10,14,18,20,26,28,41,565],[20,35,41,44,57],[23,42,44,980,1104,1144,1720,1845],[35,41,44,57],[35,44,57,1844],[35,44,57],[27,34,1660,1665,1837],[19,34,1668,1837],[20,28,44,57,408,868,1660,1665,1668,1676,1684,1710,1728,1837],[6,12,14,20,22,26,28,1845],[20,28,44,57,1845],[28,44,57,1845],[21,44,57,1844],[44,1424,1728,1732,1901],[34,44,1737,1836,1844],[44,1376,1380,1424,1728,1844,1901],[26,28,44,57,133,1372,1728],[14,20,26,28,34,44,1668,1728,1737,1844],[26,28,44,57,1372,1668,1676,1728],[26,28,44,57,1668,1728,1841],[26,28,44,57,1668,1676,1728]]

def largelearnedp51 : List (List ℕ) := [[15,44,57,1728,1844,1901],[6,12,14,18,20,26,28,44,1677,1728],[26,28,44,57,1668,1728],[34,160,204,737,1901],[27,34,44,1844],[28,44,57,1737],[14,28,44,57,1669,1676],[28,44,57,1728],[13,34,1729,1836,1838,1846,1870],[6,12,14,18,20,24,26,28],[23,34,1729,1848],[6,12,14,20,22,26,28,1729,1853,1856],[28,44,57],[34,44,1232,1373,1729],[44,1376,1380,1424,1728,1901],[44,57],[34,176,220,1101,1689],[34,176,220,1101],[176,1677,1684],[6,14,18,20,1101,1104,1238,1256,1264,1425,1724,1730,1845],[13,172,1228,1236,1425,1730],[42,176,1101,1108,1684,1844],[42,961,984,1685],[57]]

def largelearnedp52 : List (List ℕ) := [[1425,1845],[1684,1845],[1424,1684,1689,1724,1734],[1424,1684,1724,1734],[1424,1735],[1424,1684],[1684,1899],[1684],[1735],[]]

def largelearnedg0 : List (List (List ℕ)) := [largelearnedp0,largelearnedp1,largelearnedp2,largelearnedp3,largelearnedp4,largelearnedp5,largelearnedp6,largelearnedp7,largelearnedp8,largelearnedp9,largelearnedp10,largelearnedp11,largelearnedp12,largelearnedp13,largelearnedp14,largelearnedp15]

def largelearnedg1 : List (List (List ℕ)) := [largelearnedp16,largelearnedp17,largelearnedp18,largelearnedp19,largelearnedp20,largelearnedp21,largelearnedp22,largelearnedp23,largelearnedp24,largelearnedp25,largelearnedp26,largelearnedp27,largelearnedp28,largelearnedp29,largelearnedp30,largelearnedp31]

def largelearnedg2 : List (List (List ℕ)) := [largelearnedp32,largelearnedp33,largelearnedp34,largelearnedp35,largelearnedp36,largelearnedp37,largelearnedp38,largelearnedp39,largelearnedp40,largelearnedp41,largelearnedp42,largelearnedp43,largelearnedp44,largelearnedp45,largelearnedp46,largelearnedp47]

def largelearnedg3 : List (List (List ℕ)) := [largelearnedp48,largelearnedp49,largelearnedp50,largelearnedp51,largelearnedp52]

def largelearned (i : ℕ) : List ℕ := (([largelearnedg0,largelearnedg1,largelearnedg2,largelearnedg3].getD (i/384) []).getD (i/24%16) []).getD (i%24) []

def largehintsp0 : List (List ℕ) := [[16384,15065480,13716284,14966817,13618494,14],[16384,15065104,404271,13716292,15130657,13781856,1384668,13689080,226],[16384,69263,1836760,36507,525766,52880,853508,796187,1320670,1418976,2262746,2139921,487033,14970597,14999559,404271,13651579,1353439,13787283,15125344,828956,13721731,15059780,392],[16384,58909,75488,3729],[16384,13913084,13716275,431],[16384,85734,4032398,1421031,15065480,3409804,3254179,3319718,15262444,413416,7219115,8334338,9350148,3352487,7113603,75523,36508,525766,52881,796187,446180,7874002,9383248,354532,13716255,2697109,13885863,2762647,15229667,13680866,2664340,387716,2691],[16384,397033,1421031,412468,85734,3409804,297724,1846063,2272067,2295511,3352487,3078],[16384,85734,7219115,3319718,15262444,863978,58884,36516,525766,69265,1353439,14999701,3409804,1836760,3352487,420858,2262746,2139921,487033,13651587,6956521,14082238,7087850,15426334,13912969,3188641,168],[16384,36516,525766,69265,2295516,1836760,15164113,85648,3409804,3352487,420858,2262746,2139921,487033,13814830,1713917,13656218,14999559,3715],[16384,404271,420858,13781832,13721987,15059763,13918953,15256572,3219678,15032593,230],[16384,15065521,13716275,13771149,15114991,13803931,15147897,296665,13787523,2272097,13820308,15164278,2305054,1751],[16384,1847021,15265518,13913084,13771501,15060712,15114639,13804407,15147421,296665,13787881,13878285,15024358,2695589,2662621,387717,2272069,13820787,15163800,2305031,1751],[16384,15262738,15024358,387718,13913081,3334884,13771501,15114639,3367780,13804407,15147421,296665,3351392,13820787,15163800,2305031,1751],[16384,13689103,13623351,445768,8334662,13754951,462307,9350626,9383401,354532,379521,13878285,2690],[16384,15229969,15068912,15098221,15032563,13922033,478216,297955,2295511,3714],[16384,487042,13651587,13852833,3711],[16384,397039,4622984,1847021,2272126,15257330,15114991,14999559,15197135,2305779,304855,13764465,13689084,15032593,15221778,387709,2683],[16384,15147897,15221778,387709,13797238,15032593,13683323,257],[16384,13879928,13683323,267],[16384,15311749,13961390,14001343,15344527,2235],[16384,380662,13888124,13952022,429178,10357808,13691513,13721826,15065318,396025,4622984,5581969,338104,13754607,15098100,462258,9383401,354532,15150839,13797236,14001037,15337659,1846063,13771466,15107944,5385359,780],[16384,15265525,15229969,15295552,15027960,387706,13879928,15147267,13797238,870],[16384,85734,4065168,4032398,3409804,52972,1115656,1082886,853508,1421031,3253793,3319718,3352487,1847021,75480,36508,525766,3155872,7874002,2139622,1402388,2663949,3221006,1435182,1779230,1795632,4564514,7022118,3286588,9020991,2779035,3336113,2795416,2811804,3368883,3385256,4761513,7219115,413428,7113603,1762838,4664315,5417981,5547966,10299328,8334338,9350148,298745,2305030,2262743,15196893,404291,487033,13848175,14999559,13651579,161],[16384,15126266,1314539,32]]

def largehintsp1 : List (List ℕ) := [[16384,85648,7219115,14962427,3155872,15261753,69265,2295516,1681148,15163433,3409804,1836760,3352487,420858,2262746,36516,525766,14991366,2139921,487028,13814830,7120643,14082978,6923729,15425628,13912969,883],[16384,85734,3409804,14962427,3155872,15261753,52988,853508,3254179,796187,15065104,397032,1421031,1846063,2272067,2295511,4564514,4622984,75495,36508,525766,2139937,487042,13913096,1681184,15163433,13814830,3352487,883],[16384,413437,85734,3409804,3352487,1846266,2305030,2262743,14962427,7219115,7113603,1320740,15130657,52988,853508,1421031,404291,75480,36508,525766,2139943,487033,13781889,796187,15065104,13716292,387],[16384,85734,4032398,3409804,52988,1082886,2664340,14962427,632330,15032329,2598802,15228982,306942,380662,13888124,13919245,3155872,15261753,412643,3352487,7219115,7113603,1115656,853508,1421031,4564514,9020991,13691513,13721826,796187,15065104,396025,4664112,5417981,5547966,10299328,3778487,15294527,8334338,13754607,1025593,15097878,462258,9350626,3832],[16384,42439,58907,3755],[16384,75478,85661,3352487,4065168,4032398,52907,1115656,1082886,1762838,2664340,3221410,1418781,102044,4565048,9020991,2811804,3368883,4663355,5417047,5548122,10299328,7219115,8334367,9350177,7122681,2947],[16384,15295512,437393,13945978,6423740,14017680,15355003,5432200,15147923,13797243,3990373,895],[16384,15327302,13978367,15147053,13797239,905],[16384,6037570,14049363,15387948,13721614,15059705,6136259,476],[16384,102143,5572656,36609,525766,6391858,75478,798464,4466126,4565048,404278,6038992,453947,13627140,14961982,15327302,13978367,15065104,13716217,457],[16384,14970627,13618494,13803563,15224578,15147880,1911],[16384,13770787,15107922,13803563,15140731,1778037,15049109,389],[16384,75478,85650,3352487,7219115,7113603,36523,525766,102033,6391858,5572656,4032398,1697243,4466742,2811804,4679755,4794430,5548122,6039648,453947,397062,4565048,4630586,1411720,1336793,3409804,1846266,437393,13627143,14961997,15147053,13797243,15114277,13764434,714],[16384,102143,5572656,75478,53000,853508,3419909,92044,36509,525766,6391858,798464,4466742,4564514,404278,6039648,453947,13627140,14961982,15327302,13978367,15065104,13716217,457],[16384,102143,5572656,4466742,15327302,13978367,4565048,13722057,75478,798464,15065104,862969,58884,85650,3409804,4761661,13919302,421641,15256547,3155872,57],[16384,85661,3409804,52907,853508,1418781,1435182,1779230,1795632,3254179,102044,4565048,7022118,3319718,3336113,3352487,3368883,4761661,7219115,15126255,15262444,15060712,392],[16384,421641,75478,36619,525766,102143,6391858,6038992,453947,14961982,3850],[16384,397068,102143,5572656,4565048,863030,58884,75478,85650,3409804,36523,525766,421641,6391858,6039648,453947,14961992,3155872,15261753,13913059,4630586,1411720,1338068,15114277,13764433,3336967,749],[16384,1411720,1338068,13770787,1873],[16384,102143,5572656,13618957,4565048,4630586,6424628,6039648,14049363,6391858,421641,453938,15387923,6219882,15115032,405262,75478,36619,525766,2139622,6072417,14999739,6269028,15197158,2305779,1697243,13803563,6252651,15147931,2123235,13836338,6285424,15180776,1757],[16384,1320393,13787166,1846088,2272097,525766,2139622,2305779,1751],[16384,298767,15607236,14966907,102139,5572656,4466742,13983812,6391858,6039648,453933,15321961,4499511,14999730,4630586,15131397,4696124,15197146,44816,69387,1836760,13781832,1320670,30],[16384,1836760,1320670,13787166,2900],[16384,15607236,14966907,102139,5572656,4466742,13983812,6391858,6039648,453933,15321961,4630586,15131397,77586,798464,13721614,4565048,15065549,863036,58884,85650,4032398,4794430,15295619,5548122,437393,13946002,4065168,13911100,3155872,55]]

def largehintsp2 : List (List ℕ) := [[16384,525766,14961982,4466126,15327302,13978487,13722057,796103,15065104,13787905,1411722,1846100,3352379,13820804,1680842,15163433,13919302,3155404,15261753,412549,14116056,7874002,15458403,8334641,14066900,6940125,15409247,14099676,7890400,15442021,346342,9383222,9341156,2272124,2295511,7120713,3117],[16384,13627155,298764,102143,6391858,4565048,4630586,4663355,4761661,7301197,8235074,8251472,44820,85661,4032398,413451,3409804,3352487,1846266,2305030,2262743,5572656,5548122,437393,13781875,3942331,13951730,15289490,52907,853508,1418781,13721987,15059768,3876793,443],[16384,446229,102143,6391858,6039648,535867,42438,85661,4032398,13627155,298764,413451,3409804,3352487,1846266,2305030,2262743,5572656,5548122,437393,13781875,3942331,13951730,7219115,7113603,8300646,7867577,8334639,354607,15289478,52907,853508,1418781,13721987,15059743,3876793,443],[16384,85661,4032398,102044,6391858,15126294,4630586,15328005,5572656,5548122,437393,13978474,4794430,13952129,3942331,15295220,3218],[16384,15126294,36631,525766,13627155,102143,6391858,6038992,453947,14961982,1320393,33],[16384,525766,6038992,453947,15126292,14961982,1320393,33],[16384,14044347,14116149,7867581,14099770,346426,8334641,9383222,9341156,14083372,420888,3099],[16384,7211907,354609,14092602,14067028,2448],[16384,14966817,15393557,15409954,15426334,15442730,15459110,446234,8334639,15328005,7867577,9383221,421659,13978453,14066900,14099676,346342,14083280,9350171,2276],[16384,69400,2262746,102143,6391858,1836760,1320670,6039648,13627153,4630247,6203112,7087850,7104245,8038123,8054521,3352320,7120643,7284801,7301197,8251472,7350373,7366764,8300646,8317038,15134492,13781857,1418976,13721987,5572656,13984513,15321934,4565048,15065549,863027,1402608,13672699,4548679,15016222,1435378,13705612,4581449,15049169,280069,1125210,1082883,1451745,13754918,4597817,15098463,462302,14082844,15426770,8334357,14066464,15410390,14099240,15443166,346342,9350171,9373924,3319523,13918953,4761661,15262792,7211913,9021778,3561],[16384,13781798,13721987,15059743,13984513,15321890,4530399,15032603,230],[16384,102143,5572656,69400,1836760,6391858,1320670,6039648,13627155,4630247,6203112,7087850,7104245,8038123,8054521,3352320,7120643,413469,7285771,2295516,7302123,8251472,7351314,7367660,8300646,8317038,15134492,2262746,298761,4565048,4663042,4762634,8235074,44825,7211907,92075,52901,853508,1418976,347934,8334355,9350168,9373924,453941,13781844,13984513,15321961,13721987,15059772,461],[16384,14999735,15197152,3827],[16384,298767,397087,102143,5572656,4630586,1846091,2272113,2295511,4565048,1411720,58909,75488,36523,525766,2139928,5253205,5449816,85650,3409804,3352379,420870,15363872,4032398,5548122,437393,14011548,5417047,13820814,15158308,5220436,13623372,6391858,6039648,453947,14961992,1681175,41],[16384,14083372,13623379,14961992,15425628,3112],[16384,15392853,15458403,14109887,13771559,15114277,13804460,15147053,296665,13820841,15163433,2305066,2262743,13853679,15196209,478833,13919332,15261753,3345285,12560222,3609],[16384,14970659,13618504,13770787,14082138,15420456,15115041,13803563,15147943,296665,13819943,15164325,2305066,2262743,13852719,15197163,478833,13647875,3699],[16384,6922328,14082138,15420453,13819943,15158292,7119773,933],[16384,525766,1336793,1680842,1697243,2106827,3155404,6038992,6923729,7874002,12330454,2139622,12363242,453968,14053154,1838884,13627173,14961992,15425628,14076965,15163433,13814804,13779660,7086788,796],[16384,853508,1418781,2863],[16384,75496,108643,3756],[16384,14082978,15420456,14966876,14050198,15394094,3259],[16384,118561,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,44838,6924523,6205224,6234818,13823785,15158292,15123153,15426469,14076965,14050604,15393688,14961851,1310753,75486,6401328,108594,3756],[16384,15377308,14026892,14116153,15459243,3359]]

def largehintsp3 : List (List ℕ) := [[16384,42448,61223,108640,69292,1418976,4630247,4557448,2295516,118436,9373929,6252301,8071432,8317207,2262746,6400890,338035,15167275,13814765,4679432,13968266,15304872,85670,3409804,3352487,13919091,15256553,4777906,1101],[16384,118561,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,44838,61223,6041388,13618986,7874820,1675045,75516,102060,5572656,1310746,13778973,4630586,2895],[16384,15361292,14011560,15262817,13913087,1103],[16384,118561,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,44838,102060,5572656,6424628,85682,3409804,5515353,7219441,7317748,4032398,5548122,437393,15429422,14076960,14017803,15355036,13919326,15256575,1105],[16384,13919326,15256579,13755001,15093219,585],[16384,118561,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,44838,1847085,75480,53039,853508,4564514,5581622,108592,85662,3409804,1082886,3286588,7055597,7219441,9021724,470498,14085936,15420453,15262817,13913091,15098491,13749731,583],[16384,58909,75488,3756],[16384,118561,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,44838,446257,6401327,108594,85670,3409804,1421106,69292,4630247,4557448,7874820,6032569,338035,15420394,7219441,15262817,13913065,2295516,15164325,13814765,3352487,883],[16384,446257,118561,7874820,8300813,6032569,8325349,9341159,53043,1082886,9020991,470498,15420455,7366912,15377713,853508,4564514,5581622,6400827,6434113,337967,14026896,9373929,6253844,13820826,7121135,15164325,2305005,6237504,13804437,7137533,15147943,6270279,13837284,7170307,15180781,296669,1418781,4622984,7301372,15312085,13961408,1115656,4778763,13919307,7219441,15262817,3345285,13763326,1847079,1881],[16384,1418781,4564514,4622984,853508,5581622,337967,1082886,9020991,470498,15304896,15093219,15024372,4548117,287],[16384,118561,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,44838,446257,6401327,108594,1421106,14077748,7055597,13755001,7301372,13968595,6434113,61237,69292,4630247,4557448,7874820,6032569,338035,15304872,2295516,13820834,15158253,4679432,908],[16384,13804454,15140710,13771551,15107923,719],[16384,4565048,4630586,1411720,304955,6391858,8300646,453941,14085943,14116182,15453461,15147950,13797222,15115049,13764435,714],[16384,15147950,13797222,15115049,13764466,714],[16384,413494,118561,8325349,7121135,1846291,75480,7219441,3419138,92044,9373929,3345283,7104763,8055059,2305065,7137533,8087829,110392,52883,1082886,1418781,4564514,4622984,853508,2272067,304855,36510,525766,7874820,453958,9341159,9021724,470498,15462201,14109973,8005894,13755009,15093170,13623393,14962001,1025593,22],[16384,853508,15059772,15024358,4531727,15327515,1082886,9020991,470498,6400889,4548117,15311135,6120983,15376682,329779,5581678,6104592,15393063,6434122,2095],[16384,413487,118417,8325349,85651,3409804,7219441,3074],[16384,13722095,13968603,13984984,14034233,14050613,3899],[16384,53052,853508,118527,8325349,9341159,7972391,8235276,8251668,8300813,8317207,405306,14118717,15453489,15065586,13716284,4564514,13984201,15328474,5581673,4580911,13967824,15312093,5334579,14000598,8284438,15344912,329777,1418781,13787523,8038663,15131430,4622990,796187,13623310,7874820,14966883,6137379,14049754,15394104,6032571,6400887,2169],[16384,446270,118527,8325349,7874820,535878,42438,85662,3409804,52908,853508,1421106,1435182,1779230,1795632,3254179,4564514,7022828,3319718,3336113,3352487,3368883,4761513,7219441,405306,420866,15126255,15262444,15060712,1115656,15090028,1451578,553],[16384,853508,7972391,14118717,15453494,15328474,13978473,4564514,13722057,14148984,1082886,9020991,470505,15486462,15418724,7022118,15065574,2882],[16384,15394104,14044460,14966883,13618494,83],[16384,118561,8325349,102207,6391858,8300646,453935,9373929,9341159,5572656,8235074,8251472,8317038,405306,61248,413487,7121135,7219441,3345283,92071,36530,525766,6039648,7874820,15462209,14110001,8087829,13804460,13623393,4565048,4630586,4663355,4761661,7301197,306969,15140708,14961982,1698773,45],[16384,13919332,15256591,13787940,15125320,748]]

def largehintsp4 : List (List ℕ) := [[16384,69442,1836760,118561,7088366,15131422,405306,8325349,7121135,420883,13781832,1418976,13721987,7022828,15065574,863027,1402608,13672699,7006456,15016238,1435378,13705612,7039226,15049193,280069,1125210,1082883,1451745,13754918,7055597,15098491,462302,9341159,15484259,9021724,3551],[16384,118561,8325349,15429444,405306,69442,1836760,7121135,420883,14076949,7219441,13919326,7088366,13787932,15125320,3319523,15262444,3419132,7203065,13870121,2778865,15213286,7235838,13902946,3335924,15246064,313229,9341159,14140768,9373929,14108024,8038663,8169738,4075331,4032395,7252210,13952152,3942116,15295220,429202,7284979,13984976,4630247,15328005,5581646,7301372,13968595,4646643,15311625,7334143,14001421,5400310,15344400,329777,6400853,6424623,7022828,13722083,1418976,15065480,4557452,5548188,3219],[16384,9341159,11643169,470538,14208508,9054493,15491886,14142964,14075233,11577591,1388],[16384,134981,11667884,11282895,15557441,126790,102055,5572656,6391858,69299,1836760,1320670,6039648,4630586,6203491,7087850,7104245,8038123,8054521,3352320,7120643,7284801,7301197,8251472,7350373,7366764,8300646,8317038,13618972,4466742,13983812,15328005,10365372,437407,2917],[16384,134821,11667884,69299,1836760,15134535,13781832,10135991,14181174,102055,5572656,10365372,437407,15518881,4630586,13984513,15321957,10332603,1260],[16384,15164113,3086],[16384,15394094,14044482,14181699,15525224,3244],[16384,12912042,6424628,7350373,10397800,5572656,10365020,437412,6391858,8300646,453935,15429450,14076949,12789095,14247280,14214588,15552001,7284801,13984976,15321957,11479110,1268],[16384,134981,11667884,12880302,118600,8325349,10430710,9341159,11643169,470538,110411,69304,1836760,15134535,13781832,11282895,14213951,2262746,12560874,487029,15552023,7088366,14082844,15420459,11577591,1389],[16384,14181174,13623326,14961997,15523953,3248],[16384,1846088,75480,118420,9341159,36684,525766,1338067,1680842,1697243,2106827,3155404,6038992,6923729,7874002,12330454,2139622,12363242,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,8300813,7350517,453958,14053154,134981,12823021,3876],[16384,134981,12880302,13782862,12495337,14246727,36684,525766,7874002,453958,12363242,487047,15584905,1320393,13623326,14961982,12330454,122],[16384,134981,12880302,8335183,125157,69268,1836760,36684,525766,12363242,487047,13781856,12495337,14246727,2295516,2139622,2262746,15196893,14995187,15589593,3703],[16384,14999701,487047,13651587,14246102,15590217,3713],[16384,14050633,453947,15387967,13623417,14961997,85],[16384,134981,12880302,36684,525766,1353189,12363242,12495337,15134545,102224,4630586,11667884,1320393,9971156,10135991,5572656,10365372,437407,6391858,6038992,453947,487047,13791053,12330454,12757484,14249810,15584902,12691947,15328507,13978254,14966906,13618494,4466126,68],[16384,15065616,13716275,13787523,2272097,13771149,15115076,13836706,15180804,296667,1846088,13820308,15164351,2305054,1751],[16384,15560532,14208508,13787967,1846088,13771586,13722126,15059594,15114639,13804480,15147421,296665,2272097,2295511,13820861,15163800,3102],[16384,134981,11667884,53075,853508,1418781,1435182,1779230,1795632,2221623,11216426,11282895,11299291,11315664,11332061,11364837,1082886,11249216,470502,15126357,15557441,14208508,1451578,15098409,13749726,678],[16384,1082886,11249216,470502,14208508,853508,1418781,15065480,13716290,13680866,11183634,318],[16384,134943,12880302,478839,12560874,2305664,75484,14181813,429221,10365372,6433970,108596,3732],[16384,134945,12880302,12364263,536199,42438,12560874,2272885,75482,3763],[16384,5572656,4630586,15328005,2932],[16384,134981,11667884,11282895,15557441,61271,10135991,15524664,12495337,15590217,126790,14241624,12691947,13985017,487257,110426,36519,525766,12364263,13656278,69268,1353439,14999701,3707]]

def largehintsp5 : List (List ℕ) := [[16384,134943,12880302,69268,1836760,15134555,13781856,12495337,14246727,36519,525766,1353439,13656211,14995067,12364263,15589593,3703],[16384,15459723,14110006,14966906,13618494,97],[16384,118620,8325349,134981,12880302,9373929,413523,7121135,1846291,75480,36536,525766,7874820,12331494,12822800,453958,15593309,14241417,14116233,15453489,13623417,14961982,99],[16384,479070,134981,12880302,12364263,536199,42438,413523,118617,8325349,7121135,1846291,75480,3768],[16384,13837308,15173424,13804474,15140708,859],[16384,134981,12364263,12560874,2133529,11667884,413523,118617,7121135,7219441,3345283,8325349,2305065,10185720,10217930,1846291,12880302,2272885,304855,14184288,102239,5572656,10365020,437407,15518846,15180797,13829936,15147963,13797220,856],[16384,134981,10135991,13787958,15134555,102239,5572656,10365020,487265,437414,1846093,10152385,13771578,10332229,13985002,15321957,4646986,15115016,10185155,13804474,4679755,15147915,296665,10070453,13722118,4565048,15065549,1411722,10004915,13656267,4499511,14999730,10201528,13853689,4696124,15197146,2133531,2272115,1816],[16384,102239,5572656,134981,11667884,14184290,10365020,437407,15518881,10332229,15328492,13978469,4630586,13787905,15134555,1846093,4646986,13771526,10152385,15115068,4679755,13804425,10185155,15147963,296665,4565048,13722057,10070453,15065608,1411722,4499511,13656240,10004915,14999757,4696124,13853656,10201528,15197179,487265,2133531,2272115,1816],[16384,15065616,13716290,13853087,15197186,2305650,13803931,15147970,13836706,15180804,296669,13787523,1846107,2272127,1751],[16384,15560548,14208508,13787967,1846107,13771586,1081563,11247970,13755046,15093214,1466703,15114797,13804480,1827154,15147578,296665,2272127,2295511,13853696,2236756,15196733,3698],[16384,15114639,13764313,13984518,15327693,2815],[16384,75480,134978,11667884,53091,1115656,853508,828956,11151820,1418781,1435182,1795632,2205215,2221623,4564514,11216426,11282895,11299291,15134555,11332061,11348433,11364837,11479509,1082886,11249216,470502,479077,12880302,12364263,536199,42438,413526,12560874,2272885,2305664,304855,3352420,7120759,7211907,125169,102047,4630586,5572656,15069030,10365372,437407,13716280,13787523,13984201,15321742,13771149,15107801,776],[16384,14214080,13837144,15173424,15557636,3510],[16384,134981,11667884,53091,1115656,853508,828956,11151820,1418781,1435182,1795632,2205215,2221623,4564514,11216426,11282895,11299291,15134555,11332061,11348433,11364837,11479509,1082886,11249216,470502,479077,12364263,12560874,2133529,1846107,4647706,12880302,2305664,2272885,304855,13807464,15142759,15180635,13829936,15065501,13716106,418],[16384,134981,11667884,53091,1115656,13782889,1418781,13721987,1082886,11249216,470502,15059837,11216426,15557136,14208508,11282895,831],[16384,15294907,437397,13946002,15524360,14175393,10232852,13886513,1046],[16384,15295667,13946002,13787890,15131457,13984897,15328500,4622990,13968518,15312119,329917,5581669,6400874,14017680,15361316,6433950,2095],[16384,15560556,14208508,13722126,863032,13672768,13952177,15289490,15016216,13705745,15049151,280069,13755046,15098450,1093086,1125229,1539],[16384,13705745,13952177,15289499,15049151,13738666,15082071,280073,13722126,863032,1539],[16384,134981,11667884,85866,4065168,4032398,3860418,11200985,3893187,11217357,11233754,3876793,10070453,10299328,15069035,3909562,11250126,3942331,11282895,4794301,4810693,5547966,9217983,11446209,11479509,11495900,11512278,11643352,437397,462701,1093094,1125878,3925961,11266531,14217070,14181805,15518881,15295662,13946002,13672727,10054079,15016252,13738581,10119624,15082145,280071,13722041,863032,1539],[16384,15476126,346476,8325348,15426925,7219538,420895,14076960,7186769,1064],[16384,13878294,15560560,15525297,412844,298110,12912042,14247350,15590847,478860,2133529,2305664,3352351,7120679,347275,7219538,2947],[16384,125212,134945,11667884,12880302,12364263,12560874,11577815,11659748,4042609,92046,487257,15518901,10512841,15476117,346476,8325348,10430909,15426920,7219538,420895,14076960,13911100,1118],[16384,58943,397167,13738581,125212,134945,11667884,14132389,4075378,92048,487257,15518901,10119624,15082145,280254,853507,1418847,1846063,75480,4564633,5581622,108592,3732]]

def largehintsp6 : List (List ℕ) := [[16384,58943,397155,853507,1418847,1846063,75480,4564633,5581622,108592,125212,3732],[16384,397167,125212,134945,12880302,14181813,15518903,10119624,15082145,10299834,15295662,4041880,92046,290676,13731515,13705574,10086848,15049227,1418861,4564648,13656207,10004915,14999757,13853246,10201528,15197179,2133531,14123659,9121418,13837297,10217930,15180797,296732,2272886,4630305,2696],[16384,125212,134945,12880302,397167,13954931,479093,12364263,536199,42438,58943,12560874,2272885,75482,102061,5572656,4565048,863030,288259,15518839,85849,4065168,15289457,10299834,1198],[16384,397167,134981,11667884,11250126,1093094,58886,11643352,9014612,1076633,1125878,2256309,12913072,3927489,9235906,9350666,9383443,429942,10299834,10365372,5540912,92094,108634,125159,69268,1418976,4630247,4557448,12880302,290676,487257,15584869,12446190,15049240,5581983,1836760,6400849,6433966,337967,13698710,36519,525766,12364263,14999769,13651558,845293,135],[16384,58882,36519,525766,69268,2262746,13848188,2295516,13812570,1713917,13656218,3686],[16384,92094,108634,118648,9341159,14142885,9373929,14108024,8005894,13755009,1093100,7956753,13672753,58882,397150,134970,11667884,11610383,14214532,15551913,11200985,15016257,8022296,13738628,1543],[16384,9341159,14142885,14075233,7055597,13755001,1125888,7039226,13705703,7072002,13738620,1545],[16384,6424628,14011506,5572656,13976768,4565048,4630586,1411720,13698669,4581449,463],[16384,397167,5549945,126842,134945,10299834,10365372,437296,110459,85880,4032398,13946006,4065168,13911100,3286948,13754951,1125882,3270576,13705650,3303350,13738570,1545],[16384,134945,12880302,12364263,536199,42438,58882,12560874,2272885,75482,397167,11667884,85849,4032398,10299834,437397,110459,3757],[16384,134981,11667884,14181805,12880302,14247350,470903,15551913,11151820,14999762,11233754,15049235,11266531,15082155,11250126,15098537,11348433,15197186,11446740,15295667,11512278,15361316,11643352,15492508,479100,12913072,15582654,12560874,2272894,118653,9341159,14142885,9373929,14108024,8055059,13771559,11299291,15115076,9137762,13837300,11364837,15180804,296667,397167,7956753,13672753,11200985,15016257,7989522,13705716,853509,1418865,1846063,2305636,1751],[16384,4565048,4630586,1411720,5572656,10365020,437407,15552017,15115076,1846091,304855,3354424,420739,13764433,863030,1125228,1082883,15098537,13749682,1469164,555],[16384,15552017,15492508,14142996,13837300,15180804,296755,3352351,13820849,15164351,13919337,15262836,420739,2949],[16384,397167,134981,12880302,12364263,536199,42438,12560874,2272885,75482,11667884,2133529,2305664,11315664,11364837,11413971,11643352,9340242,470538,429952,10299834,10365372,5540912,92094,282494,11250126,11299291,110463,52920,1418781,4564514,4622984,1847079,304855,15551926,15115076,5581983,853508,6400827,6433966,337967,13764456,1082886,15098537,13749682,1467970,555],[16384,397167,9341159,134981,11667884,11643169,470538,9373929,8325349,7104763,8055059,7121135,7137533,8087829,9087262,9136426,7219441,9185568,487297,15552023,15492508,14142991,9120031,13853682,11348433,15197186,2272892,9070885,13771568,11299291,15115076,13837300,11364837,15180804,296667,2305669,1836759,282494,9021724,13755022,11250126,15098537,1093100,1125888,853507,8923418,13656260,11151820,14999762,2133531,1419032,2863],[16384,36511,525766,52884,1082886,13749740,1115656,13713768,828956,13656195,3726],[16384,397162,126850,134886,12880302,11667884,14181805,14247350,470903,15584907,12364263,14999769,12462568,15098544,69507,1836760,4630247,6400849,2262746,12560874,15197194,13848188,2295516,13812570,4679432,13968266,12708335,15312125,6252301,14033818,12773874,15377739,337967,2099],[16384,126850,134945,11667884,10365372,5581983,6433966,10299834,4041877,92046,108592,479108,12364263,12560874,2133529,42470,75537,3743],[16384,134911,12880302,12364263,536199,42438,12560874,2272885,75482,52909,1082886,85663,4032398,13946006,4065168,13911100,3286948,13754951,3560],[16384,4065168,4032398,13946006,13878294,2729878,13754946,9152410,14148652,9014614,9350667,9383444,9168799,14132270,3952],[16384,282494,397167,126850,134911,11667884,14181805,438149,12880302,14247350,470903,15518900,10004915,14999757,10103222,15098524,10299834,15295662,487302,15552017,11577815,11659748,10496446,15492499,94087,69507,1418976,4630247,4557448,1836760,1125206,9021081,2262746,10201528,15197179,13848182,2295516,13812570,1812223,13754929,9086724,14148529,3414],[16384,102280,5572656,126850,134945,11667884,14181805,438149,12880302,14247350,470903,15518900,10365020,15361311,14011552,282494,397167,4565048,863030,1125228,1082883,10103222,15098524,13749736,5351510,613],[16384,4565048,4630586,1411720,5572656,15355040,15320258,4581449,15049169,280173,863030,1125228,1082883,4597817,15098463,3560],[16384,4582113,15049169,863030,288259,1545]]

def largehintsp7 : List (List ℕ) := [[16384,397151,15623621,13968639,13705670,15049162,280231,9021081,14208904,11249309,13755046,134970,11667884,14173614,10496446,14149010,15486294,15057356,8978943,125211,69268,1836760,1418976,487257,2914],[16384,397162,14208905,134970,11512278,14017826,15355040,15320258,11250126,13755046,1093096,1125882,5596346,15312068,58886,11233754,13705745,110474,4566924,11266531,13738666,15077259,863033,11200985,13672768,4582172,15049169,288259,15009285,242],[16384,1418861,15074825,15311454,15344230,329777,15295063,15360618,5540914,4630704,2696],[16384,58882,397155,5582733,108592,14208894,134970,11667884,14173614,10119624,13738655,10103222,13755034,1125882,10086848,13705738,3927453,4599291,5352872,5369247,10299834,13952171,10348994,13968621,10381766,14001440,10365372,14017820,15044494,15081835,9021115,10496446,14149010,15486294,1093096,10054079,13672763,15009287,8962360,125218,69268,1836760,852197,1418976,2863],[16384,1836760,1418976,2863],[16384,14208905,397162,134970,11250126,13755046,1093096,58886,1125882,853507,77712,5582733,108592,36536,525766,11119051,13623412,9023348,11643352,14149018,15486294,118420,8890649,14966889,8325349,7874820,453958,3405],[16384,290705,58882,397162,4558735,14208894,134970,11233754,13705745,15042215,11250126,13755046,1093096,11200985,13672768,11266531,13738666,1125882,15081835,15009287,852197,77712,5582733,108592,118420,9021115,11643352,14149018,15486294,8962360,2338],[16384,397167,14208905,134981,11512278,14017826,85906,4032398,11446209,13952177,15289494,4065168,15254592,5515178,15361105,5581984,11495900,13968629,4777906,15311949,11528673,14001445,5531572,15344723,329777,6433967,6391855,11250126,13755046,1093096,11200985,13672768,3237807,15016210,11266531,13738666,3303350,15082060,280071,1125882,853507,11643352,14149018,9185197,15492203,9014614,4564633,2875],[16384,4032398,3909562,15295058,3222],[16384,58943,125212,3732],[16384,15093651,14208905,134978,11446740,13952177,94100,397167,11233754,13705745,15607236,13755061,11512278,14017826,110474,11643352,14149018,9023381,15491731,9350667,125159,36511,525766,11151820,13656272,52884,1082886,15024372,665099,14999678,12880302,12364263,487047,3720],[16384,69526,2262746,14208905,11347730,13853696,134981,12880302,12560147,487029,15191670,2295516,15156061,15093651,1812223,564],[16384,1418976,4630247,4557448,1836760,6400849,337967,2262746,12560147,487029,15304877,15191676,15123165,4646643,777],[16384,397167,429975,134981,10299834,10365372,5540912,14208901,11528673,14001445,12880302,5368950,15344235,329938,11667884,5581983,6433966,6391855,4565148,863035,58884,11348433,13853696,11495900,13968629,77720,4041877,92046,108592,118420,11463136,13935796,3927157,15278680,313374,4074666,3409803,11413971,13919347,3287008,15262281,412677,3352571,7219221,7113603,2287],[16384,397167,429975,134981,10299834,10365372,5540912,14208901,11528673,14001445,12880302,11348433,13853696,11667884,5581983,11495900,13968629,6433966,77720,4041877,92046,108592,9023381,11250126,13755046,15101849,11643352,14149018,15486294,9301130,15344919,329938,6391855,4565148,863035,58884,118420,11463136,13935796,9235593,15279270,313374,4074666,3409803,11413971,13919347,9185302,15262827,412677,3352571,7219221,7113603,2287],[16384,14208905,134978,12913072,14239164,462746,11250126,11643352,9014612,102293,6391858,58943,125212,36531,525766,6039648,12331494,12757484,11667884,14173614,5572656,10365372,487257,437414,3922],[16384,4565048,4630586,1411720,288351,15075003,15049067,1645],[16384,85915,4032398,14208905,134978,11446740,13952177,11667884,10299834,437397,12880302,462746,11250126,11643352,9014612,58943,397167,1093094,1125878,11233754,13705745,11266531,13738666,110492,125212,36525,525766,12364263,487047,15289496,11151820,13656272,14995080,3811256,174],[16384,69533,2295516,14208905,134981,11348433,13853696,397167,864144,462746,11667884,11250126,1093094,1125878,288259,12880302,2262746,12560874,487029,15191651,11643352,9014612,11266531,13738666,15075006,2256309,576],[16384,13672710,14083050,15420382,15016238,13705633,15049193,1541],[16384,13856671,13820761,15158242,15426469,14076894,13672749,15016194,13705703,1794457,15049116,1541],[16384,15065480,13716314,14082531,15426334,3093],[16384,8325349,7006456,7039226,7072002,7121135,7153904,420905,282528,1115651,7022828,7088366,404310,9341159,9021724,470511,15134625,13781832,14082844,15420437,13721987,15059802,486],[16384,14082844,13721987,15059802,15426022,3093]]

def largehintsp8 : List (List ℕ) := [[16384,404310,13791139,15125320,15426334,14076949,15065480,13716314,483],[16384,15065480,13716314,13869483,15213286,313326,13918639,15262444,4074511,1931],[16384,404310,15134629,13781832,13869797,13721987,15059802,15212973,313326,13918953,15262129,4074511,1931],[16384,13902574,13721987,15059725,15245749,2084],[16384,1115651,3253875,7022205,413606,7211907,3271648,4074509,321419,404350,13791143,15125264,15246064,13895716,15065480,13716237,435],[16384,13787523,13672679,13705547,13738341,15623621,15049244,15081834,15009287,15130877,2802],[16384,314125,412506,4074509,1931],[16384,404350,13725609,15060906,15131016,13781737,15016169,13665930,251],[16384,13705612,13672699,15009418,15048933,13738538,15081714,1545],[16384,13791148,15125234,15016189,13665930,13705441,15049102,13738222,15082028,1545],[16384,13705441,13738222,1545],[16384,15049102,15082028,13676462,15016189,13731335,13705574,1541],[16384,42474,141799,151295,61138,93912,3752],[16384,2262746,151454,2656840,862808,1092193,1402608,1836760,879179,1418976,3352320,3418740,4041333,2295516,2714215,2778865,3319523,3335924,7087850,7120643,290728,1126315,1435378,1468154,397229,4630247,4557448,15134639,15196893,2139921,108600,1763077,2189076,2221845,1451745,1828623,126882,12365744,12560147,486937,13848163,13705633,15042216,13672710,15009429,229],[16384,151454,61138,77745,93912,10357808,108636,141756,3733],[16384,151454,61138,77745,93912,134805,12880302,36539,525766,12365744,3719],[16384,102323,6424628,5367902,14017128,5335133,15360471,438194,3186],[16384,151454,2656840,862808,15016165,1092193,288259,476821,13869322,2697841,15212968,313298,3418740,4041333,4065163,15081835,13731335,5547997,10299369,118708,8325349,7072002,14082684,7039226,15426025,7219171,420895,3038],[16384,14082684,13705574,15009285,15425838,412638,3345283,13754910,15623621,15098547,14148244,15491384,462166,3288580,13902406,15245584,15204620,321499,2010],[16384,15081714,13698569,14082535,15425838,412638,3345283,15204620,15246352,321492,13895642,3255313,430],[16384,8325349,9341159,7006456,8972578,7039226,9005348,9021724,7072002,9038121,7121135,7219441,288259,13742006,11643169,15019959,13698565,14082535,15074823,15426174,312949,4065163,420895,3038],[16384,151454,2656840,476821,102323,6424628,862808,13698565,5335133,14016981,1092193,15074823,5367902,15360618,312949,3418740,4041333,4065163,5547997,10299369,438194,3186],[16384,108636,141756,151295,61138,77745,93912,3733],[16384,58882,77745,151454,93912,134805,12880302,487347,14241381,12913072,14206397,11233754,529]]

def largehintsp9 : List (List ℕ) := [[16384,102331,5548122,10366906,10292272,13928428,5572656,4565048,3877731,440],[16384,58888,77745,92042,151454,2656840,13672713,862808,1092193,288259,15009397,3844701,15278357,12413527,15589701,13709244,1418834,4564602,4622984,108602,134805,12880302,487347,14241381,14173622,36539,525766,682570,14999680,13651558,10004915,203],[16384,315325,151454,2656840,4041333,5547997,10299369,10366906,3120],[16384,58882,77745,151454,93912,134805,12880302,2656840,487347,15009429,10054230,15524156,14175351,36539,525766,682570,14999680,13651558,10004915,203],[16384,151454,862808,1092193,288259,15052725,2656840,13869322,3222108,3418740,4041333,126904,438206,102335,6424628,4565048,4630586,1411720,13698669,5335133,14016981,15354994,13738342,15011769,5302865,292],[16384,6424628,15354994,5572656,15320258,4565048,4630586,1411720,15042157,4581449,465],[16384,58882,77745,151454,93912,110529,36539,525766,134805,11667884,487347,15518901,10004915,14999757,3686],[16384,58882,77745,151454,93912,36539,525766,134805,12880302,487347,15584869,12913072,15549887,11151820,14999762,3686],[16384,102339,4565048,4630586,1411720,430018,5548122,10366906,10292272,151454,2656840,4041333,321513,15271916,5572656,3877731,15049146,1618],[16384,6391858,8300646,453935,15453448,4565048,4630586,1411720,15042160,15106436,5572656,8055585,809],[16384,15426025,412638,3345283,3255313,15245744,4074527,321419,2010],[16384,13668288,151454,682570,13656191,862808,13705441,3844701,13934867,5302865,14016802,10054230,14180667,12413527,14246212,1092193,288259,118724,8325349,7006803,14082349,7039226,7121135,3418740,4041333,7219441,3222108,13902094,15052742,13738222,15074825,7072002,15426174,412638,3345283,9021724,1108556,13754613,15098399,8972885,14147895,9038121,15491734,462166,9341159,3288580,15245896,2656840,321492,2010],[16384,8325349,13668280,7006456,14082349,288259,15077294,7072002,15426174,412638,7121135,7219441,3345283,13902094,321492,15239130,3288102,584],[16384,58941,92042,151395,2656840,1092193,15016178,13665909,682570,13656191,12413527,14246212,102339,5572656,4549200,13984028,15321837,4614225,610],[16384,405447,58888,92042,151395,862808,1092193,288259,1418834,2656840,1108556,3222108,3418740,4041333,126920,15085513,13731337,1140371,13721970,13676462,15009285,879179,15065321,1403469,15130877,13781642,1458730,13754910,15623621,15098547,462235,77745,4564602,4549200,15327518,13978252,4621057,108602,134805,11667884,11250126,3507],[16384,13701066,13721931,15623621,15065627,405447,846546,13656199,12446470,14246422,58888,92042,151395,2656840,862808,288374,1092193,1108556,3222108,3418740,4041333,126920,102339,4630586,1436403,13787532,13672673,15009397,1403469,15130877,4582149,13984207,4549200,15327518,2702],[16384,102335,5572656,151407,2656840,15009418,4548679,15327518,13978349,3861071,15294744,13945969,1153],[16384,315339,405447,151407,3418740,4041333,4065163,2656840,4794332,862808,1092193,288259,5547997,10299369,1108556,3222108,126920,438194,13668300,3861071,13951255,15289457,15077294,13861129,3926061,599],[16384,58888,77745,405447,151407,93912,15044557,13668277,1403469,13787387,15607236,15016262,860388,1092193,15623621,13722140,15065420,288458,1436378,13738222,15081835,1468105,15134639,4549200,13984028,4582114,15327697,4622990,108602,9021112,1108556,13754613,1141464,15098227,8972885,14147895,9005796,15491587,462166,11249345,11636052,125217,141784,3733],[16384,13754613,14147895,15486373,9373009,15451517,7053941,8004212,15098499,413171,15418724,314814,4065163,3036],[16384,13676495,15009426,15491384,14142885,9373009,14108024,7053941,8004212,13755009,15098102,413171,14075233,314814,4065163,3035],[16384,13918791,420895,15256610,14082681,15420455,7250999,15295641,1087],[16384,13758417,420897,15093235,15491731,14142981,9373009,14108024,15262281,13913122,8168538,1124],[16384,15491731,321419,14142912,13870125,15213125,13935780,15271823,13902956,15239053,1086]]

def largehintsp10 : List (List ℕ) := [[16384,9373929,9021724,9169187,9341159,8325349,8972578,7219441,470511,282576,3286644,7055597,9185568,4075474,9201959,9234728,15101907,321419,13749694,13869636,14148238,15486400,15213615,15246445,13895565,13713768,411630,15418724,3271640,435],[16384,151450,2656840,9169518,15213615,477171,13705547,15623621,15049244,1118154,1092193,1108556,2711978,2744662,3418740,4041333,126932,102323,5572656,862808,13746535,13672693,8972885,15016248,280069,4564599,13984201,404332,15321966,9250883,1250],[16384,6391858,5572656,4565048,404332,15321864,4745288,15213600,9383360,8251472,15443166,9267282,15475944,346346,9350644,8325348,15385803,8300646,453939,2034],[16384,151450,61138,77745,92042,1118158,2656840,13713768,2714215,13869483,862808,4564599,13984201,7988879,14098933,9004689,14131714,8988286,14148091,15495125,110550,1092193,1108556,2746984,3418740,4041333,126932,134805,11667884,11216518,14213646,487347,15552023,15517106,36539,525766,828999,13656195,14995049,10004915,205],[16384,1118158,13713768,13738526,13705572,15623621,15082164,15049065,151450,3418740,4041333,321419,290775,3270353,13902259,862808,879179,13672679,15009285,3222108,15245584,3892948,13935038,3844701,15278357,1937],[16384,151450,61138,77745,92042,15623621,13705755,15049036,1118154,2656840,1092193,1108556,2711980,2744662,3418740,4041333,126932,134805,12913072,487347,13862899,11397744,14214195,11217357,15557136,3524],[16384,151450,4041333,1118158,13758424,3418740,321419,15093182,15057261,2746984,15213125,102361,6391858,4565048,15327693,5572656,404332,13978376,4745837,13870111,4810830,13935749,15271823,4778060,13902922,15239053,1086],[16384,362474,428016,11676831,12889252,13672713,15016204,280181,11249287,12922367,2475],[16384,15065517,13716237,13984201,15328288,2824],[16384,6391858,5572656,4565048,4745288,404332,15216604,10365020,13864923,13984799,13722027,15059725,15327693,2824],[16384,462810,151454,61138,77745,92048,1118158,2656840,1092193,2714215,3418740,4041333,321419,110557,1108556,2746984,126932,134805,11667884,11250126,3574],[16384,151454,61138,77745,92042,1118158,2656840,1092193,1108556,2746984,3418740,4041333,126932,134805,11667884,487347,13862899,10250863,14181426,4067294,10299834,437418,15518849,36539,525766,2648678,13656230,14995080,10004915,205],[16384,151454,61138,77745,92042,1118158,2656840,1092193,1108556,2746984,3418740,4041333,126932,134805,11667884,15208415,15008013,10054230,15524156,4067294,10299834,437418,487347,14175413,36539,525766,682570,14999680,13651561,10004915,203],[16384,4067294,151454,2656840,102368,6391858,1118158,2714215,4565048,4745288,5572656,404332,15216604,5548122,437402,13862896,4057708,13952025,15289499,13722027,15059725,3418740,13902860,4088884,15246403,3254257,15262129,1088],[16384,15295619,13946027,15098463,4563288,404335,13749742,592],[16384,5572656,4597817,4794430,15331298,4565048,404332,13978469,13952129,15289499,13722057,15059821,443],[16384,15098450,13749754,14181018,15525038,3252],[16384,1118158,4067290,151450,61138,77745,93912,315361,2656840,4041333,3876816,3909585,5547997,10299369,1092193,1108556,2746984,3418740,126932,438194,110563,134805,11667884,10103222,487347,15298532,13946027,13754960,15093242,36539,525766,3811276,13656237,14995080,1058276,141],[16384,11667884,11250126,3574],[16384,4793471,13984897,15321975,13623358,14115999,14961853,4464705,70],[16384,1118158,4067294,151454,61138,77745,93912,2656840,1092193,1108556,2746984,3418740,4041333,126932,462821,143334,102037,6391858,315361,3778507,6039648,36532,7874002,6367198,8202213,525766,8300646,5572656,4565048,404332,453947,15462209,13955047,5547997,10299369,438194,15289499,3876816,15065531,13716333,14966847,13618494,796103,14],[16384,1082883,11249309,3558],[16384,290793,13698669,14180874,412844,298110,2295511,4620664,3352405,3107],[16384,167713,61139,77525,110299,36526,7874002,85654,3409804,15221778,2598802,14966838,445629,525766,6038992,6434124,5498781,15344676,6317982,15377447,8293561,4557451,6400718,338082,2101]]

def largehintsp11 : List (List ℕ) := [[16384,167912,1411721,13698669,813711,13623314,5319328,14000595,6138530,14033369,7989911,14115316,151531,2656840,862875,13672673,3238478,15016210,444048,58882,77525,93912,110299,36543,6038992,7874002,329337,4557451,6400718,8300706,3257],[16384,13656068,478856,2305666,304855,445773,8293561,354709,14125439,15311619,6434124,337967,13961405,9249531,1247],[16384,167912,5581517,4557451,1411721,862875,1125028,10087065,1845938,2271929,11677674,282604,9021023,11249256,11636052,4622989,61139,77525,110299,1082883,158305,36526,525766,6038992,7874002,85654,3409804,15221778,2598802,14966838,2139622,12363242,2631571,14999717,9054904,6400718,9383401,9168799,15475760,12922347,13619181,4483770,13967432,5236190,14000206,5498781,15344676,329777,5219791,14016588,5482393,15361059,9971156,14180464,10357814,2213],[16384,15254592,167912,3271314,15049140,3336876,15114991,4778687,15311949,15519726,10257520,15623621,13935800,13902905,15279229,15246397,1411721,61139,77525,92078,110299,151190,2656840,862875,288334,3418740,321512,2027],[16384,167902,61139,77525,92048,110299,151190,4041333,4057708,15213595,15623621,13935800,15279229,3418740,321419,13862799,1411721,3893907,15049151,2656840,862875,288334,13698642,2697884,422],[16384,4067312,15454191,15254592,8160358,15623621,13935800,13902905,15279229,15246397,313381,167912,61139,77525,92076,110299,151190,2656840,3418740,2020],[16384,14109960,13698672,500],[16384,8325349,7989522,8202507,15459488,9021724,11643169,11242836,288413,446450,7874820,8300813,6032569,9373929,6384920,15377559,338035,14026871,13698647,6136257,473],[16384,525766,7874002,3398],[16384,58882,167838,77525,110299,4622989,4557451,1411721,862875,1125028,3893907,15049151,6400718,4811456,15312008,126963,134830,11667884,85692,4065168,10087065,1845938,2271929,4032398,10299834,437397,15519722,1198],[16384,6038992,7874002,8293561,525766,6384921,15377559,6434124,337967,14026916,13961368,1225],[16384,11250126,11643352,9014612,12880302,10299834,437368,13698669,13738342,12913072,3927489,15082071,1723],[16384,58882,167912,77525,151541,93912,110299,2656840,862808,1092193,1108556,3222108,1125028,3893907,15049151,3418740,4041333,126920,1411721,143351,3775],[16384,167912,1411721,3893907,15049151,36856,4622989,5581517,6400718,4811456,15312008,454646,13698672,525766,3777997,14966847,13618445,812504,18],[16384,167912,4622989,4557451,1411721,862875,1125028,3893907,15049151,6400718,4811456,15312008,126963,282617,11677673,141740,430065,61139,77525,110299,2664014,158280,85654,5547966,10299328,10357808,4032398,15221784,5498781,15344676,5581517,338085,9021023,11249256,11636052,371261,13994202,1082883,3843663,15032598,387712,13683326,5301867,291],[16384,429204,6433939,337967,13961387,412675,7113603,10357808,5417981,1409402,304969,8334338,354532,15150839,13797228,899],[16384,446459,525766,7874002,8334662,354532,429190,10357808,6038992,6434124,337967,13961379,14001343,412654,7113603,13763326,305006,15337659,13804419,15140716,5417981,911],[16384,525766,6038992,6434124,337967,8335348,354532,14125462,7874002,8293561,15377718,14026964,9317711,1339],[16384,167912,61139,77525,110299,1411721,1125028,9021023,11249256,11636052,125217,4557451,862875,11677673,141740,2664014,158280,85654,4032398,15298554,36526,5581517,6400718,1082883,9350626,9383401,3409804,4622989,1845938,3352487,4664009,7219115,4065168,13919291,15262783,5547966,10299328,15306748,8235727,15443161,9251536,15475937,454653,429204,10357808,412675,7113603,7285451,15410385,354684,14059910,7318526,14001418,15344833,304969,338085,2235],[16384,525766,13618445,6038992,14049363,6434059,5236190,14000206,6055391,14032982,329781,7874002,14114913,8293567,2228],[16384,58882,167912,77525,110299,5581517,6400718,6424623,14044427,4557451,8300706,14116149,8334600,125157,4622989,6121660,13672744,6187199,13738608,1082887,158305,134830,11249350,11677158,2476],[16384,14034217,8300708,14116149,8334600,7366825,14066992,8317100,14099770,346342,9383199,9341156,6121696,13672744,6187234,13738608,1082887,9021084,3554],[16384,167838,61139,77525,110299,134830,11667884,85692,4032398,10299834,3221],[16384,6434059,8318215,14034233,13994037,8275215,14017792,429168,151554,2656840,13665913,6039671,13618363,649801,10]]

def largehintsp12 : List (List ℕ) := [[16384,167912,4622989,6400718,45055,14118915,8293567,14026916,6434059,14001411,5548191,6450438,14017800,429106,6106396,13672741,2664057,158280,4098],[16384,167912,4557451,15040971,813711,14966804,862875,15016165,15298554,5319328,15344084,5335701,15360471,1125028,15081835,6138530,15376859,7023263,15409637,7973539,15442417,7989911,15458806,290814,6154902,15393247,4622989,6400718,45055,339968,14053377,118788,9341159,9021724,1093090,8325349,14109960,7956753,13672753,8022296,13738628,1543],[16384,8325349,7989522,15454194,15418713,9021724,11643169,11242836,15075014,7072002,638],[16384,167838,61139,77525,438274,4041876,92046,110299,3772],[16384,2656840,15009424,6122066,15393065,7957076,15458610,8293567,6105695,15376678,329892,2228],[16384,167912,1411721,4557451,15314949,15049162,290814,13698672,6154902,14049757,15298554,862875,13672673,1125028,13738342,126982,4622989,6400718,6138530,14033369,7989911,14115316,159752,36871,525766,813711,13623314,14961933,6038992,15392853,6434059,5319328,14000595,5236190,15343696,6055391,15376471,329781,7874002,15458403,8293567,2210],[16384,13705689,15042198,15016165,13738604,15081835,1082887,9021084,9350626,14066987,15409637,14132539,15475197,354532,2280],[16384,14037002,15370404,15016230,15049179,13698565,13738342,15082094,1082887,9021084,9350626,4620664,6398402,15312074,13961368,7283140,14066895,15410477,9249221,14132447,15476029,354532,2280],[16384,6038992,7874002,8293561,525766,6106410,6171982,7351621,9317711,8335348,9383248,4620664,338100,13668363,13705441,7941419,14098735,14034227,15370404,15049179,1623],[16384,167912,61139,77525,110299,151214,85695,3800],[16384,11250126,11643352,9014612,11667884,1093094,13738222,1692],[16384,167912,4557451,1411721,862875,1125028,6138530,7023263,8989349,5581517,6400718,45068,13705441,15042135,15081835,143374,118797,7874820,8300813,6032569,8325349,6106409,14033189,15376859,2167],[16384,167912,4557451,1411721,862875,1125028,6138530,7023263,8989349,5581517,6400718,45068,331791,6039667,8300706,7867577,125188,135181,11250126,11643352,9014612,11667884,1093094,13738222,6424623,8334657,9350666,9383241,354532,15074990,13705441,10365093,437422,15042157,363],[16384,446473,167912,4557451,1411721,862875,1125028,6138530,7023263,8989349,5581517,6400718,290814,45068,6039667,8300706,7867577,125188,135181,11250126,11643352,9014612,58882,77525,15298554,11667884,6424623,10365093,437422,4074609,92048,110299,151228,2656840,13676560,8334657,9350666,9383241,354532,15009410,1093094,15081714,3418740,4041862,321419,13731459,15048933,13698642,358],[16384,14066296,13705574,15042146,15409637,14099072,15442417,2278],[16384,354532,13742098,15074972,15049067,13698647,14066146,15409786,14098925,15442562,2278],[16384,14180874,13738342,15074972,15524513,429108,14000595,15344230,5548191,3120],[16384,11667884,11250126,1093094,446473,290814,13676560,1126374,167886,1411721,11643352,9014612,5319328,10086848,5352976,10119624,10299834,15298554,10365372,339985,13709332,15042135,862875,15016165,15081835,13731335,14000740,15344084,5548191,12913072,5369290,14017128,5335701,15360471,429106,4557451,6138530,7023263,8990199,5581517,6400718,45068,125212,2664057,158280,4098],[16384,15376859,14026871,13738604,15081835,1695],[16384,446473,167912,4557451,1411721,862875,1125028,6138530,7023263,8989349,5581517,6400718,290814,45068,143381,118797,7874820,8300813,6032569,9021724,11643169,11242836,8325349,6171971,339985,15052822,13698647,14033369,15370359,13738342,15074975,622],[16384,15098399,5352872,15344230,6172074,15377006,6424629,6188448,15393394,445707,9039265,15491734,9014614,7056804,8007083,9350565,9383340,8327187,8300708,3393],[16384,11667884,15551913,15517106,10103222,15098524,1093063,10054079,15016252,1543],[16384,9341159,15486373,15418724,7055597,15098491,11577591,15557997,3416],[16384,14961933,15343696,15376471,6424629,15392853,3339]]

def largehintsp13 : List (List ℕ) := [[16384,167909,1411721,1125028,7023263,7973539,15085592,9021084,11249311,127002,143385,36877,525766,5236190,6038992,6055391,446491,7874002,8293561,15370404,6186709,15098483,9334054,15492416,3414],[16384,12880302,11667884,14181805,10365372,437422,15518839,15355055,1311],[16384,42450,125188,4109],[16384,471063,167909,813711,13623314,862875,13672673,1125028,13738342,1141392,13754737,5319328,14000595,6138530,14033369,6154902,14049757,9005720,14148097,11233946,14213649,331804,5581517,6400718,6424623,4557451,5548188,5335701,14016981,143389,7876638,6039667,8300706,453817,15387915,14966869,7989911,14115316,15459640,3261],[16384,167909,4622989,6400718,45055,118797,8325349,14109960,8005894,13755009,1093098,7956753,13672753,1411721,7989911,15044594,862875,15016165,8022296,13738628,1543],[16384,9341159,14142885,14075233,7874820,8300813,6032569,8325349,6434113,337967,14026871,7366912,1327],[16384,446496,167909,5581517,6400718,127009,36877,6038992,7876638,8293561,525766,6434124,337967,14026916,6171982,13738604,9021084,6188300,13754993,9334054,14148926,3414],[16384,471063,167909,1411721,13709343,15042161,813711,14966804,1125028,15081835,1141392,15098227,5319328,15344084,6138530,15376859,6154902,15393247,7989911,15458806,9005720,15491587,11233946,15557139,135202,11667884,14208425,11250126,13755046,11643352,14149018,9014614,11266531,13738666,329372,5581517,6400718,427707,14173614,10365372,6433908,2095],[16384,10101400,15524508,14175408,15360615,14011565,10364185,1308],[16384,14213798,13623317,14962001,15556725,3605],[16384,15311459,13961408,15557289,14208459,11297532,13771586,766],[16384,13749703,13967969,15304896,14213798,15551947,11297532,15115076,771],[16384,331815,6424623,5548208,437296,13749736,6170774,14049901,14017796,12879275,12460707,14246574,14181813,15518902,10397881,15394116,15361287,3247],[16384,11667884,12913072,10103222,11250126,10299834,11495900,10365372,15093800,15024372,10037684,15524154,331814,6424623,437422,14175412,15360615,14011567,1308],[16384,6424623,6039667,8300706,453817,14044490,14009605,5220466,13623372,8267937,14116110,3261],[16384,167833,61139,77525,4622989,4614845,15311459,4557451,14966806,5581517,6400718,15393391,15458947,340010,13961408,14001343,15344235,14034121,15377011,6424629,5597889,14017731,15360615,429231,5548242,4041875,92046,110299,9267909,14148837,15491731,11496135,14214389,15557289,11636058,125217,12922918,141744,3734],[16384,471063,167909,61139,77525,282659,862875,1125028,1082883,1411721,1025605,4622989,4614845,5350997,5581517,6400718,143401,7876638,5367404,6170198,6186606,8005213,9021023,11249256,2664014,158280,15101995,13749703,14000745,13967969,15304896,15344833,5548242,4811456,15295624,14017125,5597889,15361220,429106,14033521,15377610,6424629,4041875,92046,108590,14148238,9267909,15492327,14213798,11496135,15557879,11636058,125217,3734],[16384,471063,167909,4622989,282659,862875,1125028,1082883,4614845,1411721,5350997,5581517,6400718,143401,7876638,1025605,5367404,6170198,6186606,8005213,9021023,11249256,2664014,158280,15101995,331820,4557451,6039667,8300706,453817,13749738,13623317,6424623,14049901,15387978,14966869,14115457,15459640,3261],[16384,14017680,437425,15355055,15049175,280173,1082883,15098471,13749736,3909200,592],[16384,158305,167838,1411721,13946903,3959469,13771510,5401263,15115023,296786,1845938,2271929,2295511,3974972,13820796,5581517,4811456,13968518,5597889,15312068,15623621,14001448,15344897,329777,4557451,5417108,15164304,412708,3352379,7120713,61139,77525,110299,3893907,13705661,5335701,15049175,280173,1125028,9021023,11249256,11636052,125217,862875,11677673,141740,85654,7219115,2947],[16384,15364143,281714,445613,7867577,135198,11667884,158305,167838,4557451,862875,1125028,4073],[16384,13946925,412841,298108,4074663,167902,1411721,1845938,3352379,7120713,314496,10292272,7219233,2947],[16384,167912,5581517,6400718,6424623,13946925,4557451,5548188,14017680,862875,1411721,1125028,5335701,3893907,13705661,5351569,462894,6039667,5449877,8300706,10365093,438321,1093680,288259,15354994,15042157,471],[16384,14011506,5538960,13994143,1280]]

def largehintsp14 : List (List ℕ) := [[16384,167912,61139,77525,110299,1411721,1125028,9021023,11249256,11636052,125217,4557451,862875,11677673,141740,2664014,158280,85654,13946878,1082883,3843663,13689108,340018,379518,13888127,4039702,1934],[16384,5538960,14001408,2207],[16384,13946903,167912,4557451,4811456,13968518,340018,15304874,5581517,15344833,5597889,15361220,4549308,15032607,290868,6434867,14020661,5565550,14001299,6400718,15377610,14026805,6374550,14050601,6417090,15393997,445701,1411721,862875,1125028,6138530,7023263,8989349,45068,61139,77525,92104,110299,10365095,10349254,15525103,14175286,10290347,141754,151225,13676559,4532936,15016218,2664057,2632],[16384,430134,13946903,167912,1411721,3893907,13705661,340018,15042135,5319328,15344084,14020661,5547151,6433907,5565551,14001299,6138530,15376859,14026805,6374550,14050601,6154902,15393247,445701,4557451,862875,1125028,7023263,8989349,5581517,6400718,45068,58882,77525,92104,110299,10365095,10292272,141754,151225,13676559,15016165,2664057,2632],[16384,167912,4557451,13946903,4811456,13968518,282679,15028276,4549308,15311135,340018,411816,1411721,3959469,13771510,1403561,15114494,296770,1845938,3352379,7120713,346275,1125028,9021023,11249256,11636052,862875,1082883,9350626,7219597,2947],[16384,1082883,3909240,13754960,3527],[16384,167912,4622989,13946925,4811456,13968518,340018,471096,15304896,4557451,15040971,813711,14966804,1125028,15081835,1141392,15098227,5319328,15344084,6138530,15376859,6154902,15393247,7989911,15458806,9005720,15491587,11233946,15557139,862875,290873,135202,11667884,10087065,15524363,10299834,437380,14175412,1195],[16384,184378,77526,93913,108590,126686,3345284,15246197,313342,7211912,3419057,2664419,158280,296791,7113606,1846171,1419081,174729,3735],[16384,313324,2081],[16384,184378,3992464,13804415,7211912,4074421,3893282,13705661,15042198,1780634,15147413,4090795,13902913,58914,3345284,3860492,13672727,3926031,13738581,3909591,13754960,15081835,11446280,14214321,143385,4155],[16384,184378,4074421,13935740,15623621,15279289,323645,4089839,13902913,15239057,3345284,15139701,3893292,13705661,15042170,1780634,405],[16384,15042170,15245744,13895642,13672718,15016165,13738566,15081835,1082887,13754955,15093191,15024372,878219,234],[16384,13701183,13672673,13902254,15239130,15016208,13738342,15082056,1082887,15098445,13749703,13680879,878219,232],[16384,15016208,15082056,1082887,15098445,13749703,13680879,878284,232],[16384,184351,1780634,13803922,3345284,3222448,13672673,3287992,3304361,13738342,15249473,15147892,3255218,13902254,58916,135227,12880302,10086848,14180874,313306,4074421,5548027,10365372,437296,15518839,296767,1846171,2304933,2262743,2221921,13853089,12560874,487029,15191670,10201528,1019],[16384,13955134,184355,2304933,3345284,3222448,3255218,3287992,3304361,315456,3419057,4074421,4032395,7211912,4007940,10299425,13709378,15042198,3893282,15294911,429186,5548053,10357808,5319822,15344084,13994151,5417886,13804429,1780634,15147413,5450903,13837278,58914,77526,93913,108600,126686,141756,2664419,158280,167575,2206375,15180192,1411721,1846171,304955,1757],[16384,15016216,15049151,1541],[16384,12880302,15298628,13945986,10299834,14181547,15518839,13738581,13754960,14214321,15077401,10119624,673],[16384,184293,3419057,4074421,4032395,58884,77526,93913,108590,126686,3345284,2664404,158280,134807,3860492,7211912,3893282,3909591,3926031,11446280,11667884,10299399,437397,13668421,13951255,15289474,36541,525766,681451,13656191,12880302,12364263,487047,14995046,3811278,174],[16384,13902094,15239130,15049136,15082056,1085358,15098445,13749703,13731337,542],[16384,860378,15016176,15042053,15245744,13895642,13754955,13738221,1140364,15098227,3527],[16384,15042057,15009287,229],[16384,15016208,15049136,1541],[16384,15074825,15009285,1081586,15098399,3527]]

def largehintsp15 : List (List ℕ) := [[16384,184378,3345284,3222448,3255218,3287992,3304361,4567107,174731,323654,13676615,15249482,13895642,13738566,13754955,15044683,15016165,15081835,1082887,4168],[16384,184378,3345284,13701196,3255218,13902254,3222448,13672673,3287992,3304361,13738342,15249473,313306,3419057,4074421,4032395,4007925,10299399,13946946,7211912,3893282,445],[16384,14999697,13651558,14213328,15557291,3497],[16384,14213802,13656207,14995046,15556818,3497],[16384,14999680,13651558,14213328,15556929,3497],[16384,58888,184378,77526,93913,108590,126686,856141,158296,174747,134807,11667884,1089754,36541,525766,681451,11151820,11200985,12880302,12364263,487047,15020112,1074672,11266531,13742159,15085646,13665799,14213440,15551913,13656191,14995046,210],[16384,184378,3345284,3222448,13902094,860384,1118284,174756,323654,15239130,13754613,15093182,3304361,589],[16384,184378,3345284,13676626,15009285,3222448,15245584,1118284,174756,323654,13895642,15098102,13749694,13738341,15081834,3303078,587],[16384,13754955,14214261,4121],[16384,15410272,15147939,296812,4630357,404104,15126373,15557441,14208508,1081563,1451837,15098409,13749703,11247970,678],[16384,1107617,1118289,13705572,13676626,15049065,856147,15016163,1082887,58882,184378,77526,93913,108590,126686,158296,174756,134807,11667884,7211912,7113606,3345284,36541,525766,1025608,794636,1320393,7874002,1058377,827521,11151820,1451609,1417549,1468110,1433934,1828517,1794385,2238042,2203987,2254506,2220373,4597399,4563288,11249311,11215201,1846171,11282895,11299291,11332503,3303078,11430831,13906004,13804400,11348433,11364837,11479509,8334286,9350096,14066781,12880302,12364263,487047,15241301,15098445,13749703,3206055,14999724,13651558,139],[16384,1118289,15077462,15623621,13755060,15098399,314814,13705572,174756,856134,1093063,219],[16384,1118289,13733975,13754910,15623621,15098547,429562,314814,184378,3419057,4074421,4032395,3345284,5548027,6433939,5352872,14000740,347597,7113606,9350096,9021768,9039265,14148244,15486294,9300354,15344919,6172074,14033516,9333125,15377728,2101],[16384,13902406,13672686,15009397,15245584,2010],[16384,15049136,15082056,1115657,13668426,878240,13721831,15402079,7038628,15065578,396057,1418839,4564630,4622984,4533053,13967641,4762457,15311943,2200],[16384,58882,174756,184296,77526,93913,108590,126686,462936,143334,36544,6038992,3345284,7211912,151191,862808,3222448,8956514,3255218,2656840,1092193,3287992,3419057,321492,13742169,13705572,9186233,9350096,15249498,13895642,3173286,13623355,13672718,15009397,649801,14966795,6351789,14050390,6122066,15393065,445627,7874002,6335414,14034004,6105695,15376678,8300708,3257],[16384,1092193,15077449,2656840,15009401,242],[16384,58884,462935,184375,77526,93913,108590,126686,1126491,159836,36549,167575,4622989,1411721,15042135,813711,14966804,6400718,5319328,15344084,6138530,15376859,6154902,15393247,7989911,15458806,4557451,7023561,8989349,5581517,454668,4095],[16384,58884,462935,184375,77526,93913,108590,126686,3345284,13701213,3255218,13902254,313306,3419057,4074421,4032395,158325,1780634,13803922,15147892,296767,1846171,2304933,2262743,174777,3735],[16384,462935,135262,11250126,11643352,9014612,15074972,11667884,1093094,15016178,184375,7113606,7056905,15409786,9350666,354632,14059852,7211912,13894749,3255218,13705646,14131852,15468896,8990199,15049213,1541],[16384,58882,462935,184375,77526,93913,108590,126686,158296,174747,36541,2139622,7211912,8334286,9350096,134807,11667884,11643352,9383443,354532,12880302,525766,12364263,487047,14059923,6974396,13656257,11250126,9014612,15075006,1074672,14999697,7171008,13853676,2256309,15196736,3611],[16384,58882,462935,184375,77526,93913,108590,126686,3345284,7113606,15147892,15410084,864352,13668447,3222448,13902094,313306,3419057,4074421,4032395,158325,1747864,13803775,296767,1846171,2304933,2262743,174777,134807,6990792,14065963,346444,8334286,9350096,9373924,11643260,11677203,2476],[16384,58882,462935,184375,77526,15241313,92069,108590,126686,3345284,15139701,1813411,15082034,9021084,11249311,11636052,141784,9087908,15475634,7113606,15401891,9350096,354660,14125462,1126491,1780634,15049109,13698569,8978938,174757,151191,1093082,1747864,15016192,13665799,855982,2648],[16384,2656840,1092193,3222108,3418740,321507,4185]]

def largehintsp16 : List (List ℕ) := [[16384,304955,15140671,15042123,405],[16384,462936,184375,7211912,13733986,7056335,14066296,8334286,9350096,58882,77526,93913,108590,126686,3345284,3287992,159843,1780634,1126491,13705574,1846171,1813411,13804079,1421412,174729,134807,11667884,11643352,9383443,354532,12880302,36541,525766,12364263,487047,15403411,1074672,13656207,14995046,6974396,194],[16384,1093094,13672686,9014612,354642,15403348,15016236,15049189,853509,1142182,13721970,15065578,396063,4564635,5581622,6400827,15525226,429175,6433966,2095],[16384,13754910,15623621,15098547,12880302,11667884,11250126,10365372,10447301,11643352,10119624,14181023,471142,1142170,13721970,11266531,14213802,15551913,15517106,10070453,15065608,1469851,13787690,10135991,15131448,395914,10086848,15049227,4564647,7111533,10185155,15147963,296779,4630378,2696],[16384,174729,184133,77526,93913,126686,102039,5572656,7113606,36533,525766,1041889,13623320,4565048,4630586,404104,6391858,6039648,453947,14961982,1698698,4466742,4680593,298755,4664220,4762548,7302083,8235074,8251472,3865],[16384,58882,135272,331877,174729,184222,7211912,3345284,6990792,7023561,7039933,1846171,7105471,2304933,1813411,13804079,8334286,9350096,7056335,14066296,13701223,1114470,13754910,15623621,15098547,11667884,11250126,470518,314814,3419057,429562,10299834,4041877,4074421,1931],[16384,11250126,13721931,13754728,15623621,15065627,15098221,11233754,14213649,471014,3416],[16384,1413225,331877,184370,3345284,1813411,13804079,1846171,304955,15140671,1780634,15049109,13698635,1114470,13721931,1797004,15065501,396033,58882,75488,93913,126686,11332503,15557570,143466,174756,102039,5572656,4565048,2924],[16384,1468110,13754923,14142806,9061168,14132624,354703,2471],[16384,331877,184370,7211912,13762943,13742187,3345284,1780634,13803922,1846171,304955,15140671,1813411,15082034,9021029,11249258,1829773,15098426,9350096,9087908,15475634,9104277,15492022,11332503,15557570,462956,11636052,7113606,15401891,354660,14125439,8978938,13721931,15623621,15065627,396034,58909,75488,93913,126686,174757,102039,5572656,1093082,1747864,15016192,13665799,1122660,15607236,15049242,855982,4565048,2870],[16384,58882,331877,184370,77526,93913,126686,1421421,174729,102039,5572656,7113606,36533,525766,812504,13623314,6391858,6039648,453947,14961933,1698698,4466742,4680593,4565048,4630586,404104,298755,4664220,4762548,7302083,8235074,8251472,3865],[16384,354684,15403348,15476066,14125410,15328470,13978349,1254],[16384,9021112,11249345,3412],[16384,14966809,453964,13618445,14049363,15393394,3339],[16384,13742185,58882,184375,77526,93913,126686,174729,102039,6424628,36533,525766,1041889,6039648,6187119,15085681,4565048,4630586,404104,6391858,453947,11636848,5572656,7211912,7113606,7302083,9267282,9350096,14061679,14132575,354659,15468898,6941627,13623389,14961959,8906210,109],[16384,13742187,184375,3345284,1413234,1846171,304955,9021029,11249258,11636052,13709421,15042123,1780634,15147413,13797183,9087908,14132144,7113606,14058400,9350096,354659,15468927,8978941,15623621,13722140,15065420,396034,58882,77526,93913,126686,174757,102039,5572656,1093082,1747864,13672703,1451596,1122637,856137,4565048,2870],[16384,15077491,1413234,13709421,184375,3345284,1846171,304955,15042123,1114475,1813411,15147570,13797183,1797004,13722011,15065420,396033,58882,77526,93913,126686,174756,102039,5572656,4565048,2924],[16384,331877,4557451,1411721,13709421,471156,15042161,813711,14966804,5581517,6400718,6154902,15393247,7989911,15458806,7868458,7973539,15442417,184370,3345284,15303114,4622989,15106819,1845938,304960,7113606,8334286,354607,14092592,1780381,15147413,13797183,8072098,936],[16384,304969,15042123,15147413,13797183,15393247,14044427,6349676,13902934,880],[16384,14970627,13618445,13901883,864004,13672458,15249482,4042502,321419,2010],[16384,58882,176245,184133,77526,93913,126686,102039,8300646,6391858,5572656,7113606,3345284,36533,525766,648663,796103,1698698,3173286,4466742,3222448,3255218,4565048,13709422,2812815,4680593,3419057,4074421,4794430,5548122,6424628,1780634,6154345,1846171,6253459,6039648,453947,471156,1421430,4630586,404104,299127,4664220,4762548,7302083,8235074,8251472,13618969,14049363,7874002,14114913,15462209,15387839,2304933,2262743,1320393,13787166,15125234,6203491,789],[16384,11116654,14213236,15551996,13787166,15125363,11281203,833],[16384,11281203,15557441,14208425,15328005,13978349,11478249,1266],[16384,404337,15134842,13781746,5382906,14017291,14181174,15518881,10364093,15361311,3225]]

def largehintsp17 : List (List ℕ) := [[16384,12912042,437412,462971,9014612,404337,15075000,12477086,15590065,14241405,12493620,12559065,13853703,2256309,15196736,354632,3692],[16384,354642,15074990,15409786,14059852,15590065,14241381,12542879,13804484,929],[16384,12912042,13627513,13656068,14995046,15130773,13781746,12493620,14246727,14214588,12361929,15589593,15558078,3501],[16384,12912042,525766,430206,6433966,6391855,5540912,4565148,8235205,8251597,13618969,11118037,14213236,15551917,4466126,13983812,15321840,11479241,1268],[16384,331877,184370,1846171,2304933,2262743,135288,11667884,58882,77526,93913,12880302,7211912,7113606,7056335,10119624,11250126,13742187,3345284,4630357,10135991,10332603,10365372,9350096,10447301,11643352,2139935,12364263,12560874,486937,5582972,108592,126686,1419067,174729,36541,525766,1320733,9972146,1353502,10004915,4664220,4762548,10299834,7302083,12478963,12806641,9023613,470356,397439,4557448,5548188,437296,6038992,7874002,6400890,8300706,453817,13791053,13853403,15191670,1025480,11119051,13758501,6424623,5351569,11512278,15101988,1093096,681451,11151820,11200985,15020112,1074672,11266531,15085646,13665799,863043,1125246,15044526,2221921,419],[16384,13853403,15196893,3708],[16384,13771578,13804474,15140671,15114959,13837308,15173339,859],[16384,14184578,14214574,15551913,15147970,13797183,13771466,15115076,13837144,15180804,1755],[16384,2265219,479361,3701],[16384,9014612,479357,2133529,15074917,2240022,15180348,354642,13829930,3343214,1814022,15147570,13797183,2302806,856],[16384,13804245,15140671,14213951,15551913,11428719,15246454,884],[16384,135288,11667884,12880302,331877,184370,7113606,3345284,1846171,10152385,11299291,1862542,11282895,11332061,307328,7211912,12364263,7056335,11250126,12478963,13742187,7154642,12560874,9350096,12806641,11643352,471173,13791366,2304933,10185155,10217930,11364837,15126660,15557441,14208425,15147735,13797223,960],[16384,15016189,13665909,13902094,15246064,2010],[16384,15016192,13665909,15049109,15082034,1118126,13754613,15098426,3518],[16384,15151241,15246197,13895642,13705646,13672718,15009397,15048933,13738566,15081714,1115657,13754955,15098102,3518],[16384,525766,15245584,13895642,3204590,13656234,681451,14999680,478822,2139622,12363242,12553753,13796209,2305666,13837144,304976,15173455,2174574,261],[16384,240999,331867,58882,174756,184296,77526,151687,93912,3345284,2656840,862808,1092193,1108556,1747547,3222108,1780634,3255218,1813411,1829773,3287992,3304361,3418740,321492,462986,2714215,110557,126686,143334,36544,6038992,649801,3173286,879179,7940704,8956514,3271592,9350096,15020171,13665909,13623306,13902094,15239130,14966845,6122066,14049576,6351789,15393880,445627,7874002,8293561,13705441,15049136,1418834,13721831,15065525,1403469,13787387,3337130,15134856,395914,4564602,4622984,525766,6401339,2228],[16384,13705441,13902094,15239130,15049136,13738222,15082056,1545],[16384,1126540,331877,184370,3345284,151687,2656840,862808,1092193,3222108,3255218,3287992,3418740,321492,13676685,15009397,15245584,13895642,13705646,15048933,13738566,15081714,1545],[16384,11667884,11250126,3558],[16384,184289,77526,92042,126686,102039,6391858,36533,525766,6039648,453947,15387927,14961946,85],[16384,143503,158305,282740,184376,3345284,13796209,1698698,13623339,6253459,14050201,58888,168080,1411721,9021023,11249256,11636052,9087908,14132144,1846171,13771466,304955,15107902,9054904,15475501,346495,7113606,14058400,9350096,2432],[16384,143503,158305,282740,1411721,9021023,11249256,11636052,184376,3345284,13906065,13804400,1845938,304955,15140692,9087908,15475634,7113606,9350096,354684,14125439,9383401,14099831,8072098,15442858,8300923,9334214,14050623,6253459,15393691,9399756,14116223,8088468,15459246,61139,77525,92042,110299,126686,36549,5581517,6400718,454653,3263],[16384,58888,184376,77526,92042,126686,143503,158305,176274,102039,6391858,3345284,13906065,36533,525766,6039648,453947,15239182,6351789,15393880,14044439,3173286,14966845,13618458,83]]

def largehintsp18 : List (List ℕ) := [[16384,6037570,14049363,15387927,13901883,15239182,6349897,1112],[16384,174747,184289,77526,92042,126686,158296,102039,5572656,7113606,36533,525766,6391858,3345284,3173286,4466742,4778924,4565048,404278,6039648,453947,13627540,14961946,1698698,4680593,4630586,4664220,4762548,7302083,8235074,8251472,306969,3843],[16384,13984842,13722035,404283,15059772,15327693,2824],[16384,13906070,15239182,15065525,404283,13716284,6136259,14049754,6349897,15393880,3372],[16384,15474797,14125397,3170362,15245373,13895712,9184347,1128],[16384,135317,12913072,174747,184289,77526,92042,3345284,3271592,4778924,6402199,108594,126686,158296,36541,525766,13618458,12331494,14246009,12880302,12364263,487047,15584874,7211912,3173286,13901883,15239206,12642800,1145],[16384,6038992,7874002,8293561,525766,14999559,12363242,487047,13651561,13615108,7890400,14098532,15436184,3171804,13901883,15239206,6335812,15377493,1335],[16384,15065525,13716255,13984201,15328332,2824],[16384,282766,1093779,853507,184376,7211912,58888,135317,11250126,11643352,9014612,6941627,11667884,8908184,9350096,8334286,9383443,354532,14971032,4564633,446617,12880302,8170423,45210,77526,92042,126686,158296,174747,102077,6391858,3271592,4778924,5572656,404278,15249563,13895716,13984842,15321864,13722035,15059743,461],[16384,158296,184201,3345284,135317,12913072,15551940,11430366,15246454,13895698,9202606,14148716,11643352,15492508,9383360,8170423,14099555,11626978,15443336,9186233,14132328,11659748,15476126,346346,7211912,14058588,3304361,13754955,11250126,15098537,9014614,9350096,2390],[16384,58888,184270,77526,92042,126686,282766,471196,864413,1082883,158305,102077,5572656,134837,11667884,14181805,10365372,437407,15518900,15361311,3199],[16384,525766,445722,6038992,7874002,8293561,14999559,478825,2139622,2272889,304855,9383248,354532,15436155,12363242,12553753,15173472,8105298,1008],[16384,862875,1125028,1082883,1411721,1845938,304955,15093170,15107902,15040901,1141392,371],[16384,184378,3345284,13796209,9104277,14148532,1698698,13623339,1829773,13754936,5434258,14017425,6253459,14050201,11332503,14214080,282766,1846171,13771466,471196,176288,37022,1731467,13656221,2304933,13837144,8334286,9350096,8072098,14099368,14962847,8889811,15491177,9383360,7890400,15442021,9087908,14132144,8906210,15474797,346346,7113606,1025480,15097878,9014614,2376],[16384,13656068,478825,2272889,445722,8293561,304855,9383248,354532,14092667,8039738,13771555,8105298,13837294,1755],[16384,525766,6038992,7874002,2139622,13619362,8889811,14147687,9383360,7890400,14098532,8906210,14131308,346346,2276],[16384,9373924,8890674,14147687,3520],[16384,8880231,14132624,2355],[16384,282766,58888,184378,3345284,13906081,15239173,9186233,15475818,11643278,9202606,15492205,11430831,15557750,471196,14208346,9021781,3304361,15098445,13749590,11240102,141774,864405,3173286,14966845,3206055,14999724,1846171,3320755,15114987,2304933,3386298,15180750,8334286,9350096,8170423,15443045,45219,77526,92042,125155,9383360,14092522,8012421,1418863,174729,151221,1092193,1539],[16384,184378,3345284,13906081,15239173,14127270,15623621,15492517,471196,8908180,13623404,9039262,13755029,9301432,14017814,9334201,14050623,11660731,14214557,282766,9055679,13771563,176288,37022,8940949,13656262,1846171,2304933,9121219,13837297,8334286,9350096,9383360,14099831,14962847,3173286,61],[16384,14143655,15623621,15476134,13627557,14132624,9021781,13755022,9283979,14017810,9316748,14050620,11643278,14214554,184378,3345284,13906081,15239173,3173286,14966845,3206055,14999724,1846171,3320755,15114987,2304933,3386298,15180750,8334286,471196,14085073,9348449,8170423,15443045,15607236,15492519,45219,168094,282766,9070993,13771568,4256],[16384,348328,184378,7211912,8334286,9350096,3345284,13906081,471196,15239186,9202606,15492205,13627556,9373924,14142912,7113606,9021768,13755022,9283959,14017810,9316729,14050620,11643260,14214554,3173286,14966845,3206055,14999724,1846171,3320755,15114987,2304933,3386298,15180750,15444341,15477110,45219,168094,282766,9070991,13771568,4256],[16384,14214554,14017810,15355037,15557924,3601],[16384,453941,470552,14151850,15486484,12879275,12854679,15590818,15525304,14175411,10364185,14017820,15355037,1300]]

def largehintsp19 : List (List ℕ) := [[16384,15410534,15623621,14132645,15476113,14059752,14181737,15525267,3211],[16384,14099847,354532,15436010,14067054,15403240,1367],[16384,14217389,15551834,15410543,354532,14059752,9021804,15098537,13749590,637],[16384,14149008,14214557,14067039,15403395,15557999,3418],[16384,15410543,14059907,14099796,15443336,15476126,2282],[16384,354532,15495340,14135471,15560880,14208529,14067054,15470765,15410530,12912042,14239164,12838278,14099852,15443323,2278],[16384,58888,184270,77526,93913,126686,315561,3419057,4074421,4032395,158325,102077,5572656,282766,134837,12880302,11667884,7113606,8334286,9350096,9366469,10447814,11594695,12913072,6424628,6391858,3345284,6367228,9218051,9283675,11512278,8300646,9316455,11643352,10299399,437397,9384107,11626978,10496446,11659748,463025,11250126,1093099,853507,3876822,10070453,4565048,404278,15069035,354532,13716255,13984201,15321890,2697173,13885863,13680866,2664404,387716,15223427,4728824,1054],[16384,15443287,15476066,354532,14092522,15295645,13945990,1185],[16384,15413427,354532,14059907,14099796,13952155,15289478,15443106,15475879,2282],[16384,14127284,14067039,354692,15403395,13952165,15289478,3990398,15147905,932],[16384,184222,77526,93913,10357808,108636,126686,141756,3735],[16384,15295648,13946004,14966883,13618509,62],[16384,315561,184270,3419057,4074421,4032395,7113606,7269314,3345284,8218637,9234448,8334286,9350096,5548027,10299399,58888,158325,438454,9375925,37042,525766,3778509,7874002,8202242,453968,15462583,14110027,13952159,15289492,13623393,14961997,63],[16384,207939,184378,7113606,7269314,8334286,9350096,9375925,75495,93913,126686,470505,143401,36549,525766,1698698,1846171,3345284,304955,13627143,7874002,453968,14962001,15458403,14109973,3777997,15294527,13946004,167575,1125028,315561,4074421,8202242,1183],[16384,453968,470505,15462201,14109973,13804460,15140710,13771559,15107954,719],[16384,315561,184378,3419057,4074421,4032395,168120,4622989,1411721,282766,862875,1082883,1338024,4614845,5350997,9021023,8055472,3345284,8218637,9234448,5581517,6400718,58888,110299,158305,430265,5548027,10299399,10357808,4664009,5417886,1845938,304955,4557451,338085,8334286,9350096,77525,93913,126686,141756,36549,525766,7874002,8088468,9384122,354532,15150839,13797207,14001037,15337659,13771466,15107906,5384884,780],[16384,184378,7113606,13796257,8072098,14099368,1698698,13623339,8088468,14115756,14961853,8334286,9350096,354532,7892225,15442021,9087908,14132144,15468778,8896621,42466,9104277,14148532,15492497,462230,1118395,9014679,58943,77526,93913,125185,143334,174756,3765],[16384,184378,7113606,14069948,8334286,9350096,354532,15403398,6941627,14966879,13618471,14114913,7892225,14098532,15443287,15476066,14125290,8896620,42466,14149008,9366469,15492454,462230,1118395,9014679,58943,77526,93913,125161,143334,174756,3765],[16384,5572656,5548122,3217],[16384,15468960,15403408,1378],[16384,305002,15140724,15107947,719],[16384,15403408,15065578,13716255,13885863,15229994,13680866,387716,2691],[16384,397505,4622984,13804448,13766848,14099235,304981,15403379,8332189,15443287,9055038,14132011,9347998,15476066,2282],[16384,338100,15370452,304981,15107944,788]]

def largehintsp20 : List (List ℕ) := [[16384,184378,77526,93913,125161,158325,1118395,174756,36512,525766,7874002,446653,6038992,8293561,3345284,1846171,6204729,7211912,7113606,52887,853508,2663949,1418781,2696736,4564514,7039933,8039738,8072098,9087908,7203777,8334286,9350096,354532,14061762,7089098,13771547,6401339,7351245,14034219,4632771,7105471,13787936,13722088,404104,15059743,15131016,7302083,13984980,15327693,2702],[16384,110782,135364,11667884,10299834,3221],[16384,12913072,471014,15551940,11667884,15517106,15093182,10103222,668],[16384,15024358,53397,632330,14966793,665099,14999678,174740,184288,1846171,1402388,15114494,2304933,2188826,15180039,8334286,9350096,7955992,15442227,8971801,15475001,8955409,15491382,45219,77526,92042,126686,158296,3744],[16384,184378,3345284,1118376,15093197,15057261,3271592,15245749,13895685,3173286,13623355,6351789,14050390,864455,58884,174756,151696,2656840,282764,878279,15016169,15212813,2022],[16384,1118376,282764,174733,184288,77526,92042,125155,151191,2656840,864405,1418830,15206374,2714215,15065517,2779753,15131366,4564599,404104,2698],[16384,463048,53449,9020991,11249216,11636052,15468942,1082886,9072048,15131442,174733,184288,7211912,9350626,1418781,4564514,404104,14061759,7113606,13796257,4680593,13984649,9268677,15328488,2702],[16384,1118376,174733,184289,7113606,13796257,1797004,13722011,1829773,13754936,1862542,13787861,2796441,13869921,9087908,14132144,11332503,14214080,143558,102602,6391858,4680593,13984649,5572656,4565048,404332,15321864,15065549,2829],[16384,6391858,5572656,4565048,404332,13978376,13716237,457],[16384,58914,184378,77526,92042,126686,1118377,282764,864405,2664055,158280,174756,3735],[16384,1118376,282764,174733,184289,77526,92042,7113606,14069963,15403380,7211912,15238240,3271592,15065525,4778924,15328332,110796,125155,151191,2656840,864405,1418830,3419057,15213584,13862886,2714215,13722027,2779753,13787877,3337130,15131376,4567245,404104,2698],[16384,174733,184289,7211912,1118376,53454,1418781,3270193,3337130,4564514,404104,13791143,7113606,14069963,15403380,15238240,15131376,4778924,15328332,13978254,7038514,15065578,13716106,457],[16384,135375,12913072,174733,184289,7113606,14069963,1118376,471014,15403399,11594207,15557999,14208452,15139748,1829773,15098426,13749694,11250126,678],[16384,13935190,15271935,1827381,13804088,15140692,3973994,893],[16384,10299834,10365372,5540912,12880302,3927157,13758673,14209222,11667884,14173614,471014,15093182,15245901,13895670,10283460,1137],[16384,13804088,13766848,13713768,1425805,13787686,15623621,15131469,305002,404189,2779],[16384,13804400,13766848,13869793,305002,15140701,2794335,15213410,13935345,3973994,15278973,321419,1935],[16384,2763585,3943275,13897940,13870092,13796209,13771466,305002,15107947,15213282,13935674,15278835,321419,1935],[16384,184378,3345284,1118395,7113606,3419057,4042949,4074421,321419,8334286,9350096,354532,4624592,108602,3304361,1846171,304981,143570,4567245,1417593,4596057,1450530,1829773,3337130,13758675,13721959,3320755,405717,15059713,1797004,15147421,13797204,15090028,7211912,3271592,13791143,15131016,1469148,15114797,13764438,714],[16384,304981,15059713,15147421,13797204,13771466,15107926,1425807,13787861,15131322,2779],[16384,184378,8334286,9350096,354532,4624591,7113606,3345284,1118377,1846171,3320755,3419057,108602,4042948,4074421,1413333,4567245,377],[16384,12880302,11667884,10447301,11594207,11626978,10496446,11643352,11659748,471014,4273],[16384,184378,7113606,3345284,8334286,9350096,354532,1118377,9366469,438486,143577,4624591,1846171,1797004,1862542,405720,13717719,13803931,13766848,1425805,13787833,304981,15140692,15131351,2779],[16384,315610,184378,3419057,7113606,7269314,3345284,4074421,8218637,9234448,8334286,9350096,438486,4042933,1931]]

def largehintsp21 : List (List ℕ) := [[16384,15454427,15623621,14099854,15443315,184378,8334286,8350660,15410524,9350096,354532,14059750,14132575,15468778,9389440,395686,297352,1846171,2304933,2262743,1118395,3345284,1419067,2942],[16384,15147950,13797213,13754936,15484284,15623621,14099854,14132598,15443315,15476090,9021776,15098515,470478,3533],[16384,9375964,174729,184122,3345284,75495,93913,108602,126686,52887,1082886,36512,525766,7874002,9020991,1846171,853508,8055582,8088468,304981,4282],[16384,4632798,4557448,58914,174729,184122,77526,93913,108600,126686,3735],[16384,135391,11667884,9375964,12880302,174729,184222,9350096,9366469,10447301,10496446,437397,1118392,471014,15495340,14142996,14181778,1846171,2272126,2304933,304855,15518846,7113606,9104277,13804468,15140731,10185155,955],[16384,11667884,471014,14142903,10496446,14181778,13804468,15140724,10185155,15524795,3252],[16384,1413344,58909,75488,184378,93913,125155,9375964,7113606,1118395,9104277,3345284,1829773,8088468,1442125,1846171,304957,15462621,15492477,174756,438454,143585,102039,5572656,4565048,2924],[16384,14142903,14108024,9397617,14099838,15623621,15476134,15443321,7973197,13722095,13804468,15140724,1794385,15065501,2817],[16384,9375964,75478,125155,174727,184088,7113606,1118392,1829773,9104277,463075,9014781,8978781,7963115,15065598,13716226,1139015,9003376,7987699,14098933,15436109,14107118,15623621,1423],[16384,174727,1118392,8978781,15098514,15065452,58943,438454,13716333,9036317,9003359,14131714,15623621,15049244,15475196,125212,184095,7113606,9375964,7963115,8334286,354628,2411],[16384,405730,299236,184378,1846171,2304933,2262743,9375964,1118395,9023717,470525,14142974,3345284,9054044,13787948,8986972,13722107,15059837,1419067,15131016,2854],[16384,15410534,15623621,14132645,14099829,15476113,15443321,14059750,15451517,299229,2262743,8038235,15131430,13781798,800],[16384,184378,3419057,4074421,4032395,3345284,4794361,5548027,10299399,9375964,1118395,1829773,1846171,7105471,2304933,8088468,8334286,9366469,2664404,158280,405730,15495399,135398,11667884,3942388,11282895,7211912,4810787,11446280,11479509,11495900,11512278,437397,471014,15560556,14208464,3876822,10070453,15069035,13716349,11217357,526],[16384,305002,14142903,14108024,13804468,13766848,9397617,14099838,15623621,15476134,15443321,8055205,807],[16384,9375964,184378,7113606,3345284,323816,4624592,1846171,9104277,1118376,1829773,8088468,304981,15462621,15492477,463081,9014781,58943,77526,92042,108602,125155,143334,174756,151191,282766,8978781,864405,2664062,2632],[16384,1118395,9375964,348394,184378,7113606,9350096,9021768,470525,14142903,13755022,3345284,9104277,13804468,15140711,1829773,15098426,429562,314814,15238004,4074421,5548033,10299403,363988,11643260,14214554,11332503,15557570,11242840,11677110,10365469,3120],[16384,2262743,1419067,404350,470525,14142974,13787948,8986972,13722107,15059837,15131016,2943],[16384,9375964,184378,3345284,1118395,348394,7113606,9350096,9021768,1846171,9054578,2304933,307436,135403,11667884,470525,14142903,11643260,14214554,15551926,15517106,9104277,13804468,15140711,10185622,955],[16384,1118395,184378,3345284,15487213,9104277,15147958,9375964,348394,7113606,9350096,9021768,470525,13797223,1829773,13754936,15098515,429562,314814,13894512,4074421,5548032,10299402,363988,11332503,14214080,11643260,15558044,11242840,11677110,10365469,3120],[16384,1118395,299246,184378,1846171,2304933,2262743,15487213,348394,7113606,9350096,9054578,15131438,3345284,1419067,404350,9375964,9021768,470525,13781887,13721987,8988997,15065599,2941],[16384,1819194,15082015,280274,9011859,58943,200677,93914,110300,143073,151192,2656840,1092193,1663],[16384,200943,5540913,9235520,15279270,4074568,321531,13928478,3927096,13754966,13902906,15239186,15139701,3910731,13738575,75520,9192557,125223,191406,15102192,1125822,58888,92071,110300,143073,151192,862808,1092193,3845186,13672723,3877956,13705656,9039290,15082134,288259,4169],[16384,15278973,13928478,13787895,15131351,13984901,13754966,14148772,9014614,4564633,404104,15321742,13722046,15059594,461],[16384,404104,13716106,13984201,2702]]

def largehintsp22 : List (List ℕ) := [[16384,321531,15151346,15246197,13895698,13935674,15271966,10290315,15500460,10084796,15065612,3334867,13787886,10150645,15131453,10347652,15328496,4559091,11249309,10331326,15312107,15336593,338080,13961373,1140427,4612463,13754977,11691177,15558068,14208344,11486453,14198202,15541426,371257,2620],[16384,5514294,14001230,15337631,5579902,15312065,13961362,13738587,5349966,15082086,321517,11249289,13935674,15271906,3875254,15049146,13698682,1140364,13754737,10355850,15500573,11691177,15558068,14208344,11223569,14198202,11510924,15541539,371256,2619],[16384,10355850,4596058,338076,13906165,321543,15239130,10265656,15508591,15344925,13994151,5349966,13738596,5366355,13754985,3288520,15082056,9021059,9299081,14148885,3414],[16384,13902906,15239130,14148772,9014614,13738575,15074947,3288483,584],[16384,15246398,13895698,15065536,15131385,15328391,13783283,750],[16384,1419067,1861507,4630357,291060,4567286,3334867,321543,15282424,13928478,404104,13750519,598],[16384,15094009,15278680,321543,13928478,13902906,15239186,3293773,15623621,13738675,15082015,1419067,13722046,15065454,13787895,1451837,15131177,395914,4630357,4557448,288418,13993101,338067,1702],[16384,174756,15495409,200941,3959865,13787895,3927096,13754966,5540913,4074568,321531,15093182,15131177,4811838,13984901,15057261,13902906,15239186,3293773,3910731,13738575,15082015,280275,58947,75520,92106,110300,9235520,14148772,9383360,125161,143073,191401,151192,2656840,862808,4564599,15327693,404104,2702],[16384,200943,5540913,10357813,10292275,3894327,3910731,3927096,3959865,3976263,4074568,4795462,4811838,9235520,11447372,11463745,5581916,1419067,174729,15495409,11676779,1118458,1451837,4630357,13938939,321531,15271966,1861507,3334867,4559096,15312002,15336593,338080,13961373,15098456,13749694,1139015,4612463,609],[16384,13967969,15623621,15082164,15311453,2206],[16384,4587864,4579657,4612443,13758717,15093182,15623621,13738675,13967962,15304862,611],[16384,5366355,15344235,13994177,5579902,13968575,15304861,4604515,15623621,13738675,15082015,15040971,1130867,1126654,288398,1677],[16384,15344833,338114,13994177,14148885,9014614,15040971,1126654,15081835,288389,1692],[16384,58914,200654,93914,108600,9021081,14142806,9094068,125222,143073,151192,5540913,5581916,338076,1093063,853507,2648],[16384,58914,75520,92071,108600,200677,143073,5540913,3927096,4795462,4074568,321527,5581916,338076,15102207,1093063,9301079,15495409,15315200,13961373,13935744,15271956,3845186,15016213,3910731,15082065,15246398,13895677,13796209,1125822,291073,13665799,15049162,855982,158296,118424,9021059,14142806,8962359,2338],[16384,200677,5540913,13750530,3927096,13935190,4074568,321527,5581916,338076,15271956,15246398,13895677,3293771,15623621,15082164,1126654,288418,1702],[16384,13734147,13754910,15623621,15098547,200677,5540913,4074568,321527,1125822,13705574,3910731,13935183,5581916,338076,15271956,3877956,15049146,288408,1658],[16384,58888,92042,108608,200654,5540913,4795462,15279234,5581916,338114,13928468,9235520,14148772,9383360,125161,143073,151192,862808,3845186,13672723,3877956,13705656,3910731,13738575,282716,1092193,1539],[16384,13902906,15239130,14148772,9014614,15074947,3288483,584],[16384,321542,13938950,15271906,15082065,11249289,15557814,14208344,15246398,13895641,11420789,14198202,15541426,363042,15500460,2595],[16384,15278680,13928418,13705656,15082015,1140364,15049075,1545],[16384,321542,15102216,13750535,15623621,15082164,1140364,13705585,10355850,10117716,14164640,14001434,15337639,5317047,15049172,1545],[16384,13734153,13935183,321542,15271906,15246398,13895641,13754910,15623621,15098547,3288483,582],[16384,13984352,15321864,13935183,15271966,1159]]

def largehintsp23 : List (List ℕ) := [[16384,15049146,15082065,13698569,13984207,15328391,2800],[16384,332042,6391855,4581579,4614351,321542,1835710,4630704,404305,13742347,15282444,13928490,13754966,15102216,4343],[16384,174770,191387,200677,3959865,13787895,3310269,4074568,13902906,5540913,321527,15239185,3367760,3334847,15131376,396123,4567300,15106794,4629250,1411720,75520,92106,110300,9235520,14148772,15495409,9383360,125161,143073,151192,2656840,862808,1614],[16384,6391855,4630704,2897],[16384,8325349,7121135,3091],[16384,174770,191387,200654,10357813,10292275,5540913,3310269,3877956,3910731,3927096,5352545,4074568,5516382,4811838,9235520,11447372,11463745,5581916,6433888,15495409,11676779,282893,58888,75520,92071,110300,321527,15315205,13938958,15271966,15246398,13895697,3367760,13820792,3992634,15164290,412646,127248,143073,151192,862808,1092193,1539],[16384,15246398,13895697,13787886,15131385,396123,13763303,15098456,13749694,1458731,13713768,1417601,2783],[16384,1839356,3310269,200943,5540913,1118481,3927096,3367760,3334847,3959865,4074568,321527,15282450,13928478,13902906,15239185,15106794,13754966,15093182,15057261,1425807,13787895,15131376,1417606,404192,2782],[16384,15239185,3260853,1425803,3334839,15131376,1114478,1417591,404312,2782],[16384,2262743,1411854,75480,92080,191400,200680,110300,7120713,7211907,125169,143073,151192,2656840,862808,1614],[16384,3293773,3260759,15262773,412630,15082015,280275,3354899,2304992,58947,174756,1839381,15057261,15166423,1778070,1417590,2902],[16384,92042,191387,200673,110300,127248,143073,3419130,15206285,2703789,158311,3736],[16384,61223,1411926,75488,92042,174770,191387,200673,110300,143073,15057261,15122822,3318460,15262444,422167,3419141,15206285,2703789,158311,118424,5540913,5581916,6433888,340239,7219223,15420297,7012838,2284],[16384,3418740,2714215,15212973,1933],[16384,191364,200605,93914,110300,143073,36538,118424,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,413478,7219441,2947],[16384,3354899,15249686,1847576,75480,15057261,160025,174756,53530,853508,4564514,6400827,15024358,4548117,15311135,200943,4074568,3894327,15278528,13928337,6368329,14034068,6120983,15376682,329779,5581916,6433888,2095],[16384,1418781,15131016,4564514,15327693,4622990,4580911,15311314,338096,2226],[16384,1836760,1418976,15131016,2907],[16384,200943,5540913,13721959,15093182,405787,15059725,5581916,61724,78109,92042,110300,3354899,174756,151834,2656840,1092193,1108556,2746984,3418740,4041795,126932,143558,191364,36545,862808,879179,15016169,1139015,15049075,280069,796230,14966800,828999,14999685,1418830,15131016,1846107,15241497,3322132,15114987,2714215,15212973,411630,3260853,2304992,2221716,15180196,444402,8335348,8988286,15491583,9350644,7988879,15442423,9004689,15475204,4259],[16384,862808,1092193,288259,15077449,2656840,15009397,242],[16384,4557451,5581517,338076,15304861,4795084,15102207,15487232,15040971,9005720,515],[16384,4557448,340239,15304861,15102207,15487232,15040971,9005860,515],[16384,200943,5540913,13928478,4074568,13902906,3354899,3845186,13672723,3877956,13705656,3910731,13738575,3927096,13754966,3959865,13787895,4041795,13870101,4090941,13919298,4795462,13968512,4811838,13984901,6368329,14034068,7269439,14083226,9235520,14148772,11463745,14214324,1126686,58888,160031,9301079,176416,69914,2262746,1836760,1418976,4630247,5581916,6433888,405793,15125264,3335924,15246064,7219236,3319523,15262444,7087850,15426334,412553,7120643,2947],[16384,13919314,15256572,13787918,15125345,748]]

def largehintsp24 : List (List ℕ) := [[16384,13618972,13918263,15262444,420858,3068],[16384,10290315,2262746,3319523,5400310,1836760,3352320,420858,14004515,14165275,15508766,363066,141756,158324,175829,192214,329932,6391855,224488,240979,257751,200517,11676779,12889196,12913067,1320670,6039678,4630247,6203112,7087850,7104245,8038123,8054521,7120643,7284931,7301341,8251597,7350468,7366878,8300742,8317134,15135012,13781832,11282157,14213951,15552001,13918953,15256572,13935757,15279249,313373,4074568,11413529,1140],[16384,3354899,158324,174727,53530,4564514,853508,1418781,1847021,1435182,1779230,1795632,7022118,413423,2305030,2262743,13781887,13721987,7113603,4630378,13984513,191409,200559,93914,110300,125167,143073,36513,525766,1353509,13656211,2139943,487033,14995067,4498920,15327410,15059596,828956,133],[16384,158324,174727,191409,200559,5540913,3354899,10357813,5532756,5581916,6433888,78117,53530,853508,15126822,1418781,15065480,13716290,5336143,14000598,329932,6391855,796187,13623310,4564514,15262444,413416,7113603,1846266,4630378,4664315,7302120,8235205,8251597,44825,93914,110300,125167,143073,3745],[16384,7113603,75523,158324,1846266,2305030,2262743,174777,53530,1419081,863043,1540],[16384,1419081,4630378,4557448,58914,191364,200762,93914,110300,125167,143073,174729,3736],[16384,1418781,4564514,4622984,338096,13994194,13919314,15256553,13968575,15304896,15106819,1115656,3336970,751],[16384,174729,69914,4630247,4557448,191364,200602,5540913,1836760,5581916,6433888,340239,13994194,13968575,15304872,5433099,13820818,5532756,13919314,2262746,4778767,15262797,15158149,4679432,908],[16384,315682,200943,4041795,4074568,3409803,5540913,15344786,3354899,3155919,3254239,3319799,10292275,3336232,3368988,4761619,7219221,397607,4778025,5532756,5581916,6433888,11676779,12889196,422184,61738,2664413,158280,1413419,75488,168218,4557451,338076,13994194,13919314,15256553,1845938,2271929,2295511,5434450,13820818,15158253,886],[16384,1845938,2271929,2295511,4557451,5581517,338076,13814765,13961384,13697479,1796753,410],[16384,191364,200762,5540913,176429,151834,2656840,4041795,321501,13862894,2812522,13820775,3435115,13919251,2949],[16384,13754948,14148653,9014614,13664522,13738222,280195,1668],[16384,2656840,862808,1092193,2746984,9169518,4041333,321513,13873455,329697,6391855,3418740,13895565,4778204,13984842,396040,280530,1115651,4565148,2936],[16384,6391855,1836760,405775,13978489,1418976,4630247,13783283,769],[16384,191364,200602,5540913,5581916,4565148,6433888,78129,53530,1418781,4630704,853508,6391855,404283,13716290,13787523,4339],[16384,1418781,4564514,1082886,13749703,13680879,1385996,13787384,4624627,4548117,13967645,2240],[16384,13783283,13984513,404104,13716108,387],[16384,13781789,13968135,14033687,6391859,13984513,2937],[16384,13968135,14033687,2099],[16384,340274,61747,69914,2295516,1836760,4646643,6219512,2262746,4630247,397621,6400849,13791542,13820620,412653,7120643,7211907,479361,2139921,12560147,12357145,296662,15274284,191364,200602,12659790,15574199,10292275,12889196,371197,14223876,12627568,13902967,4074568,15246398,5540913,321557,2071],[16384,240979,15274284,200943,3894327,15065536,3927096,15098456,3959865,15131385,3354899,3992634,15164290,4795462,15312002,4811838,15328391,6368329,15377557,10357813,10292275,5540913,3877956,15049146,3910731,15082065,4041795,15213591,4074568,15246398,5581916,6433888,9235520,15492262,160048,168247,7269439,15426716,413997,395911,1845938,77525,7123241,7211907,4622989,4557451,338076,13961408,4762314,13902917,313367,2072],[16384,3346714,92071,200943,110300,1836859,127248,143073,191387,3736],[16384,1409402,75495,168249,1845938,2271929,2295511,3352379,3419142,13697479,2697884,13869478,200943,6433888,5319328,14000595,6138530,14033369,15337525,5483609,15213602,3254942,13902254,5516382,15246416,4041795,4074568,321419,1933],[16384,75495,3346714,92071,108602,1836885,127248,200943,143073,191387,3736]]

def largehintsp25 : List (List ℕ) := [[16384,75495,200943,93914,108602,168251,1411721,1845938,3352379,7120713,7211907,125169,143073,191364,36550,525766,4557451,5540913,4074568,321557,13961373,4516539,13656244,15372602,6088175,14999741,2271929,2295511,2139928,487042,3689],[16384,53564,1847079,853508,1418781,2272067,2295511,3352405,3419142,200943,5540913,7120746,7211907,4074568,321557,13961394,4564514,4729646,13870108,75495,93914,108602,125169,463160,1115656,143334,175827,191364,36513,525766,4516567,13656244,2139937,487042,14995049,2647532,15212711,4762418,13902917,3204590,15245484,1933],[16384,1082886,11249216,12922347,371115,13961402,14001343,9020991,11636052,11480541,14198001,15534654,15344931,2250],[16384,4557451,13961384,13697479,5319328,14000595,15337695,1845938,2271929,2295511,1796753,13820314,15158253,916],[16384,463160,200943,5540913,5581916,11512930,11676779,12889196,61758,75495,93914,108602,143073,10357813,5434450,422205,176447,191362,36538,118424,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,3878],[16384,75495,3346714,92071,108602,200943,143073,422203,191362,36538,118424,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,3878],[16384,9020991,11249216,11636052,1082886,11283932,15541056,12922347,371115,14191166,14124441,13994186,9285093,1297],[16384,13994207,13814765,914],[16384,200943,5540913,15307072,15106819,3943493,15278835,10357813,5385307,15344396,463160,11512930,11676779,12889196,61762,168257,1845938,2271929,2295511,5434450,1411721,15040901,1796753,15163804,414019,3352379,3419142,4041795,4074568,321419,13928468,7120713,7211907,3254942,15245744,13895703,1082],[16384,862808,13672736,13705683,13738596,4188],[16384,15312065,13961394,15213602,13862881,1052],[16384,15131396,151876,2656840,200943,5540913,4729459,5483126,5581916,4041333,321501,15348038,15279249,13928468,13870101,4795462,13968512,15304882,15213597,2017],[16384,2656840,15206369,15008013,4532826,15311130,4565149,879179,15065321,1403469,15130877,1413363,862808,15048933,288334,1618],[16384,58909,75488,3346714,1836859,15239166,3367760,15164282,422201,3046],[16384,3346714,92071,191362,200605,110300,143073,36538,118424,9373929,9341159,8325349,7104763,8055059,7121135,7137533,8071432,8087829,7153904,8104201,8169738,7350517,8300813,12822800,3878],[16384,69962,1836760,15164113,3046],[16384,3352320,7120643,7211907,1836760,4762634,15246407,2071],[16384,200943,5540913,15279249,13928468,3992634,13820800,4074568,13902906,3877956,13705656,4632903,4041795,13870101,4795462,13968512,160072,174733,1421641,4557448,58914,15304861,4647669,15131401,414027,78156,3346714,15239166,15040971,3244464,1846086,2272094,2295511,4025403,13853652,3367760,15164282,15197021,478827,15139701,4653957,4686676,92042,108590,143073,191410,36538,525766,2139622,3706],[16384,200943,10357813,315725,4041795,4074568,3409803,5540913,3352571,7219221,422184,13994207,5581916,13968575,5532756,13919314,15256553,10292275,4778025,15311949,6433888,14034179,6350891,15377497,6391859,5434450,13820818,15164278,7334998,14083341,15426657,7113607,75523,2664413,158280,1839401,4632903,2897],[16384,174733,191362,200680,4041795,4074568,3409803,13913065,10292275,4778025,13968459,6350891,14034007,6391859,5540913,3352571,13820787,7219221,14083166,7113607,75523,2664413,158280,1839401,2897],[16384,1418781,4564514,2696],[16384,13820620,3046],[16384,61776,323919,1847633,75480,174733,151882,2656840,3346734,13895678,3222108,13672718,15016204,280181,1419067,4557448,862808,1655],[16384,2656840,2697841,13869478,862808,288374,2002]]

def largehintsp26 : List (List ℕ) := [[16384,1419067,4557448,200943,5540913,4074568,321531,13961373,13895678,4752453,2272095,2295511,3367760,13820792,13853530,1861507,3334867,13787886,15623621,15328511,15339853,5467219,15197155,478827,13796209,13697479,1769874,2195856,61776,75520,92071,108590,143073,160083,174733,191412,36538,525766,2139622,3704],[16384,3354964,61776,75480,174733,151834,2656840,200943,5540913,4041795,321501,13862881,3418740,13902860,7219223,7113603,4729459,13968412,4565149,1411720,1865],[16384,2656840,4041333,321513,13862881,13664522,4532826,13967641,6105695,14033189,2099],[16384,4632903,61776,200943,93914,108590,15339854,5540913,15271058,3992634,15164290,4041795,15213591,4074568,15246398,4090941,15262788,4795462,15312002,6368329,15377557,7269439,15426716,414034,1839445,127248,143073,10292275,6400849,160086,174733,191387,69272,2295516,2262746,13853403,4025403,15197142,36521,525766,2139921,487033,3691],[16384,15312059,4632896,61776,1846040,75480,174787,414026,1421625,15623621,13968639,200943,5540913,3346714,4074568,321531,4565149,2696],[16384,200943,5581916,15623621,13968639,15312059,5598293,15344837,13994033,151896,2656840,4745837,15213600,5540913,4041333,321501,13862881,5483126,1057],[16384,2656840,4041333,321513,15271962,2779753,13869797,15206369,15008013,3844701,277],[16384,15331673,13783383,4632903,4647668,13968135,200943,5540913,3959865,13935351,15271956,4795462,15312002,4565149,1411720,61776,6400777,6368329,15377557,6213942,75512,10292275,160090,174766,422201,4426],[16384,200943,10357813,15331673,13783383,5401681,14000910,315739,4041795,4074568,3409803,5540913,3352571,7219221,422184,15337695,3319799,13918953,15256553,5532756,1107],[16384,13935637,13820775,15158242,15278978,2018],[16384,321513,13873501,15206354,15279127,13928418,15164265,13814754,896],[16384,15279127,13930556,15246352,13895655,1082],[16384,332124,200943,5540913,5581916,4565148,4630704,1411720,6433888,1847567,3352379,61776,75480,174731,151834,2656840,10292275,6391855,2272122,2295511,2812522,3992634,4041795,863035,288334,414046,7120713,7211907,3418740,4074568,321501,15216991,15016204,13665909,1092193,1125240,93914,110300,125169,143073,191397,36545,525766,13862866,2648678,13656230,6039678,453947,2139928,487042,14995085,845293,15048841,1074672,15081617,4014],[16384,200943,5540913,5581916,4565148,4630704,1413428,75488,405856,174727,151865,6433888,6391855,13978376,10357813,4548827,13672732,4581579,13705679,4614351,13738592,1118495,13722057,2829],[16384,6394198,13978376,2656840,13862881,13664522,4549200,284],[16384,75488,168249,405856,2695],[16384,200943,10292275,340321,405851,160098,1421667,174727,4632891,4559156,13961373,4579657,13722064,13781642,13697479,1436403,396],[16384,463160,200943,3894327,15065536,3959865,15131385,4795462,15312002,4811838,15328391,6368329,15377557,53604,1082886,11249216,12922347,1115656,405856,13716237,11232822,14197266,11447372,15541426,12445240,14230039,12659790,15574199,11676779,12889196,371115,2481],[16384,338096,15304882,15106819,4645560,15131401,15059594,1436382,399],[16384,15125134,15059596,392],[16384,15323495,15065549,15125130,773],[16384,4632934,4559208,338076,15304861,4579657,15065554,15125130,15040971,1436403,398],[16384,200943,5540913,10292275,15282533,405856,13928490,3894327,13722046,3959865,13787895,5581916,4795462,13968512,4811838,13984901,1413481,58909,75488,174727,151865,2656840,3845186,13672723,15016204,862808,288334,1653],[16384,200943,5540913,10292275,15208810,4041795,15279127,405856,13928490,3894327,13722046,3959865,13787895,5581916,4795462,13968512,4811838,13984901,1413481,58909,75488,174727,151865,3845186,13672723,3877956,13705656,3910731,13738575,1118495,2656840,15008013,879179,15065321,2829]]

def largehintsp27 : List (List ℕ) := [[16384,15623621,13705755,15049036,1618],[16384,1846088,2272016,1751],[16384,422251,58909,75488,405856,174727,151882,2656840,862808,288334,15069548,15131015,200943,10292275,5540913,2812522,3992634,4041795,2306398,13783405,1433928,13705612,13713794,15623621,15049244,1618],[16384,2656840,2779753,13869797,2030],[16384,15607236,15131471,13721987,1125133,58888,200873,5540913,3959865,13935351,15271965,4041795,15213591,160111,174766,13816139,69962,2811654,13869927,3368713,13902712,4074568,15246398,3409805,3352320,13919091,4090941,15262788,3068],[16384,13722046,13968512,13984901,4457],[16384,1421678,405856,422251,13791600,200943,10292275,5540913,3894327,4795462,4811838,5581916,13939057,15271978,3959865,15131385,2298221,3992634,15164290,13814759,13716106,1769876,13705547,3877956,15049146,280147,1846088,4630337,15328391,4559091,58910,2272016,75482,174727,151882,2656840,862808,1655],[16384,200943,5540913,15061362,3894327,15278528,422251,13928477,1421678,3959865,13787895,4795462,4811838,5581916,405856,4465],[16384,315755,200943,5540913,4074568,3352571,7219221,7113603,75523,93914,110300,125167,143073,4041795,2664413,158280,174729,191364,52888,3409803,1846266,4630378,405856,4559208,1570],[16384,200943,3894327,13722046,315763,4041795,4074568,3409803,4090941,13919298,405856,4811838,13984901,422260,15256572,5540913,3254239,15065521,3319799,15131372,2698],[16384,158324,174729,191409,200559,5540913,15125130,5401681,15344400,329932,863027,58884,69962,4630247,15262444,13913084,13984838,15328005,4559207,5581916,2204],[16384,15061366,15131016,1846088,75480,158324,174729,53578,853508,191409,200559,4041795,15262129,13913084,3433483,13870099,15623621,15246459,15213582,13878285,4058172,13935642,3894327,15278528,313231,5540913,2664413,1436392,1779230,1795632,2272097,10292275,2779175,2795514,2811931,2695589,15229353,3824],[16384,174729,191362,200680,5540913,13939061,14001294,315763,4041795,4074568,3409803,3254239,3319799,4761619,405856,13717879,13918639,15256572,5532756,15344723,329932,5581916,6433888,6391855,15328328,13978453,4565148,457],[16384,200943,10292275,13939061,14165162,414072,315763,4041795,4074568,3409803,5540913,3352571,1846266,2305030,2262743,13853403,405856,7219221,7113603,75523,93914,110300,125167,143073,2664413,158280,174729,191364,36513,525766,2139943,487033,15191663,10218598,15508478,8334338,9350148,463160,52888,1082886,9020991,9383401,354532,11676779,12889196,11249216,12922347,371115,2615],[16384,58909,75488,4378],[16384,1836760,3352320,420858,15256572,15344723,329932,4630247,13984513,15328328,6400853,2095],[16384,463160,315763,200943,5540913,4074568,3352571,4041795,3409803,2664413,158280,405856,174727,1421690,13783417,4761619,5532756,3319799,13918953,5581916,6433888,5401681,14000910,78203,53530,9020991,11249216,11636052,1082886,9072048,14132017,853508,1435182,1779230,1795632,3254239,4564514,7022118,10292275,3336232,15607236,15131471,3368988,7219221,413423,8334338,9350626,9383401,354532,11676779,12889196,12922347,371115,15468953,13721987,15059743,9004597,516],[16384,853508,15059705,15024358,3221006,15261969,412643,1762838,15147267,1836761,3352420,3066],[16384,307580,61821,75478,158324,414026,191409,200559,93914,110300,143073,118424,8325349,3346714,2786144,7121135,3073],[16384,321419,15271978,15213591,15246398,1933],[16384,200943,10292275,4041795,13771449,15623621,15115086,307580,2779010,13869797,4074568,3336070,13902574,3958663,13935351,3412351,1861509,13804245,3319650,13918953,174727,13717886,1409411,313150,5540913,158324,3346810,2043],[16384,58909,75488,414026,307555,313150,200942,5540913,3346810,4074568,2043],[16384,397696,13771449,15623621,15115086,158324,307552,174763,1421697,862971,58884,75478,414026,191409,200762,93914,110300,143073,118424,8325349,3346714,2786144,7121135,3073],[16384,13771449,15623621,15115086,397696,307552,3420546,200943,4041795,4074568,321419,4646755,6219621,4630358,6400777,5540913,3959865,13935351,15271935,4795462,15312002,6368329,15377557,332086,5581916,6433888,2095]]

def largehintsp28 : List (List ℕ) := [[16384,307552,1419070,4630358,4557448,200942,4795462,15312002,5540913,5581916,338076,13961367,61776,75478,174729,3346714,3976263,15147901,13797204,4653955,2272093,4009037,15180754,13829851,13697479,2195870,13853642,4025403,15197142,478824,92092,110300,143073,191388,36538,525766,2139622,3704],[16384,307552,1419070,4630358,4557448,200942,5540913,15282564,13928447,4795462,13968512,5581916,338076,15304855,61776,75478,174729,3346714,3976263,13804411,15140692,4653957,2272093,4009037,13837265,15173339,15040971,2195872,4025403,13853652,15197131,478824,92042,110300,143073,191388,36538,525766,2139622,3704],[16384,13705656,13870101,13968512,15323464,2656840,3844701,13672723,862808,288375,15009361,4549200,286],[16384,307552,200942,5540913,151941,1419070,4630358,4557448,3877956,13791619,4041333,4795462,5581916,338076,13939078,2656840,862808,288375,15271906,15049146,13698648,15208787,1047],[16384,2656840,2763378,13869793,2008],[16384,61776,75493,92042,307552,200942,110300,5540913,3943493,13935345,15271935,4041795,15213591,160136,174733,414026,3346714,3976263,15147901,13797204,1835722,127248,143073,191387,3736],[16384,307552,200942,5540913,3943493,13935345,4624777,1835722,4653760,5581916,338097,15271956,61223,75521,92042,13959933,108607,13820753,15623621,15164359,412646,127248,143073,174770,191387,151192,15208840,4041795,1047],[16384,2763441,13869793,3320499,13902568,1933],[16384,307552,200942,4041795,4074568,321419,13808010,5540913,3943493,13935345,15271935,3976263,15147901,3352404,3894327,15065536,3927096,15098456,15623621,15131469,3992634,15164290,4795462,15312002,4811838,15328391,6368329,15377557,15213591,160136,15246398,176523,463159,4624777,5581916,11512930,11676779,12889196,15336593,338095,61758,75478,4378],[16384,1082886,1467970,15098413,4624720,338096,471362,3527],[16384,2763441,15213282,3320499,15246059,1933],[16384,75494,92042,307571,200942,110300,414026,3346714,5540913,3943493,15278835,13928447,3976263,13804411,15140692,1835727,127248,143073,191387,3736],[16384,13775244,307552,200942,4041795,4074568,321419,15110535,5540913,3943493,15278835,13928447,3927096,13754966,5581916,11512930,5385307,15344396,11676779,12889196,61837,13870101,13902906,176526,151951,2656840,15206360,2763378,738],[16384,15213282,13862872,13935637,15278835,2057],[16384,13775240,1419070,2656840,13862872,13664522,879179,13721831,4532826,13967641,4549200,13984028,4457],[16384,2656840,2763378,4041333,15118737,15208850,15008013,1403469,15130877,2272016,3844701,15278357,13928447,13771505,13837265,2173540,15180037,1755],[16384,1413489,13771505,1854],[16384,4630358,13978254,1419070,4559091,338076,13961367,13716106,4571600,13705547,462],[16384,321419,13939092,15271935,15065536,15131385,15312002,15328391,13767061,2763514,13869793,15213591,15246398,13895565,1436379,13721997,1411722,13697408,3244462,15336593,4647670,13984518,4557452,338075,2838],[16384,200943,10292275,5540913,3894327,3943493,3959865,405904,13791616,4041795,4074568,4795462,4811838,5581916,307580,15110550,321419,4009037,160147,174727,53647,15278835,13928447,1413489,1565],[16384,307571,200942,5540913,15623621,13787982,15131322,3943165,15278835,13928447,3894327,4795462,4811838,5581916,1413489,4074568,13902906,3412375,2763514,15213282,15246351,3352566,158324,174727,4474],[16384,397720,3412368,307571,200942,5540913,3943493,15278835,13928447,4090941,13919298,3927096,13754966,5581916,11512930,5385307,15344396,11676779,12889196,61837,158324,168335,1411721,15040901,3271314,15262132,13993101,4557451,338074,412649,3976263,13804411,1780381,15147413,3352407,7120748,4074568,13902906,3254942,15245744,7219223,2947],[16384,4557451,5581517,338076,13994163,13820818,1862314,15164118,13919314,412549,13804429,1845938,15147727,7120748,2947],[16384,4624720,338104,13994171,13750669,617]]

def largehintsp29 : List (List ℕ) := [[16384,3412375,315801,200943,5540913,4074568,3352571,307580,75478,158324,5418077,5434450,5532756,7219221,10292275,3336232,15262447,5385307,15344396,176538,53530,853508,1421690,1435182,1779230,1795632,3254239,4564514,7022118,3319799,15131322,3368988,4761619,10357813,5368912,5581916,11512930,11676779,12889196,405915,413423,7113603,15065487,15623621,13787982,13716106,13803931,1847021,15147727,1911],[16384,6391855,453947,13627140,14961982,15065104,4630704,15134436,15327302,4339],[16384,200943,5540913,13927566,3894327,3943493,13791616,15118748,4795462,4811838,5581916,307580,315796,10292275,4074568,3352583,75478,3412375,158324,174727,53530,13722046,13771505,3976263,13804411,4090941,13919298,4477],[16384,1846039,15337659,15147919,13764313,15065560,13716217,397],[16384,3412375,200943,10357813,5336143,13791616,15118748,5418077,14004638,307577,332191,5540913,1321728,5581916,4466812,6433888,6039678,536989,42438,75478,93914,110300,143073,158305,174756,191409,118433,9373929,52922,9341159,7973125,8235205,8251597,8300742,8317134,8325349,6391855,453935,14118717,15453461,15065586,8169738,15262822,7219441,420866,3816],[16384,200943,10292275,5540913,14004638,13935757,14165162,13799840,13722011,13791616,15059594,10087524,15507980,307577,363046,11676779,11643446,5336143,15344088,329907,10357813,5581916,4630712,15327693,13978254,9251015,14148832,8986972,15491583,11479241,14214386,15024358,11184668,15556927,12889196,12913067,15090028,11250205,470530,3418],[16384,241364,3412375,853508,1115656,1082886,796187,1418781,1435182,1795632,3253793,4564514,3286588,7054910,9020991,15126945,15065480,13791616,307577,13716217,13918639,15623621,13771597,15118748,3319650,15262444,412643,13803931,1861509,15147735,3352420,7120759,200943,4041795,2713133,13869483,2779010,15213286,5540913,14004638,13935757,3959865,15278841,313231,4074568,7219221,2947],[16384,61858,307580,75478,3412375,158324,174727,414026,200943,93914,110300,143073,191409,118424,8325349,3346714,2786144,7121135,3073],[16384,397731,200943,5540913,5581916,4565148,4630704,1411720,15118748,3412375,158324,174731,13767041,3346810,4074568,321531,4489],[16384,307580,75478,3412375,158324,414026,200943,93914,110300,143073,191409,118424,8325349,3346714,2786144,7121135,3073],[16384,1411721,13764418,13697408,3271314,13918642,5319328,14000595,15337659,15262803,412643,1780381,13803922,15147919,2206375,13836702,15180767,2295517,3352407,3078],[16384,200943,5540913,10357813,3412375,15118748,5418077,5450851,5532756,307580,340388,176550,53669,397731,4624720,13764456,5385307,14000906,5581916,15311619,11512930,11676779,12889196,471358,15337682,1082886,1467970,13754923,15093170,5368912,619],[16384,13764456,13918957,14033682,15370362,15262809,412643,13804234,15147927,13837018,15180773,2295517,3352407,3078],[16384,13918957,420870,15256553,13820628,15158253,886],[16384,299432,2295511,3352405,13775273,13968126,15311619,460992,346293,11643190,3412],[16384,420870,13814765,13919091,3049],[16384,304855,14026874,13804437,13837284,1757],[16384,8290385,15110570,15377172,15147727,15180508,2298284,15164118,15262447,3346859,304986,14026935,13797207,917],[16384,15377172,14026874,13804437,15147727,1879],[16384,304981,15118766,13764456,14033682,15370362,3375955,13837018,15173464,15238093,6333291,1109],[16384,14000906,14033682,15370423,15344902,5548211,13951734,15295639,14017293,15361289,429106,13869793,15213606,13902568,15246421,313229,13820628,15164316,13918957,15262809,412549,2269883,13837018,6267733,15180773,7153517,7119702,7211907,4074531,10299425,10365115,3120],[16384,13775280,15107944,15377172,14026874,14001411,15344396,5548211,13952150,15295224,14017800,15360783,429106,13870117,15213282,13902932,15246059,313229,13820826,15164118,13919319,15262447,412549,13804437,15147727,7120748,7211907,4074531,10299425,10365115,3120],[16384,15098413,462279,11677158,15508279,15541056,362925,14999704,15196895,478747,12889728,12922347,2475],[16384,13968585,13656252,13754993,13853671,14165314,14198087,15118770,15311619,460992,346293,11643190,3412]]

def largehintsp30 : List (List ℕ) := [[16384,411788,346324,7219593,2947],[16384,217511,8293566,7867580,6032570,4624720,1847079,853508,1418781,2272067,6204218,6237417,6270193,3355055,1862391,2763565,3320625,1115656,3336970,3959564,5385013,5401361,6253788,9020991,11249216,6352094,9383167,3420589,6302949,6335722,6384863,6434028,6450401,299441,7120746,1082886,1370838,2139937,6089945,1467970,6186564,2288376,10136375,11283264,6286557,12560239,4564514,6400827,10398957,11545840,14037427,8334590,15372724,6153780,15065568,15098483,15133459,15312074,15330068,463155,11636052,9317615,15476029,354614,14125462,13961397,9251647,1247],[16384,15115028,15311619,304855,13961390,4661953,13804419,15147927,4694744,13837271,15180773,1757],[16384,2306485,217511,6032570,4624720,1847079,853508,1418781,2272067,6204218,6237417,6270193,15380918,304855,14026874,13804437,13771538,15107944,15147727,13837284,15180508,1757],[16384,13722078,13787927,13984972,4624744,13968585,15059730,15311314,460992,346293,11643190,3412],[16384,175827,241364,405943,217506,8293566,853508,7867580,1418781,4564514,4580911,6153780,9020991,11249216,6221019,6401256,6417632,9383167,14037432,15370454,15065568,6186564,15098483,15131417,15312074,15328462,463155,11636052,13716242,9004597,14131714,9317615,15476029,354614,2454],[16384,61881,75495,428221,362682,460992,11242836,11677194,10299930,10365469,5540912,92094,108602,217509,126687,141774,280728,1093090,1125871,853507,158296,12922382,12880299,207980,3737],[16384,61881,217509,8334590,9383167,9341156,7867580,9021740,11643190,7121199,191366,13963706,7301432,14083283,412650,7219505,3345283,4664345,13804419,1846296,304981,1879],[16384,304981,13797207,714],[16384,5540913,5385307,14000906,2248],[16384,217322,44752,1839548,13787833,15623621,15131469,396055,61879,75520,92071,108602,125155,191387,151230,2656840,3310269,3418740,321491,13862881,2763378,737],[16384,13820620,412656,3419130,217322,44752,75500,92044,108602,127248,191387,151230,2763378,13869793,13796040,13902706,4041333,4074509,321419,1933],[16384,61881,217509,44752,75495,108602,125155,13961397,13763326,209341,134850,11667884,10152385,14181178,6032570,6204647,14033682,15370370,10415331,15525190,429187,151230,2656840,2763378,13869793,6302949,15213606,313313,4041333,5547997,10299834,10365372,3120],[16384,61881,217509,6032570,356795,13961397,13763326,6204647,14033682,15370370,4645560,13787911,209341,3355070,6253788,15164316,6335722,15246421,1847743,191364,86464,3409804,6352094,15262809,2306475,6237417,6270193,2265526,13853403,6286557,15197161,478828,44752,75495,108602,125155,159448,134831,12880302,12560874,3701],[16384,3893187,13951421,217132,44752,58916,108590,126687,4032398,429186,10299328,11676821,141740,159448,3759],[16384,2656840,862808,13672673,288379,1657],[16384,94658,216987,44752,58916,108590,126687,3774],[16384,13968127,4565155,13787833,1413363,13697408,75497,160195,184772,3345284,217322,6032570,6139110,14033369,15370370,6237417,15147927,1846171,304955,13797207,1780634,402],[16384,217322,44752,61881,77526,93913,108590,126686,134857,7113606,14059898,13796257,4664220,13968259,5417886,14001037,5572657,5434258,14017425,429192,10365141,11676831,2476],[16384,216989,44752,61881,108590,126687,85694,4032398,134831,12880302,11667884,10299834,437397,14175365,13952171,3202],[16384,192966,70087,2295516,1418976,4559156,13961379,4712214,13853660,478827,217322,44752,61881,3352320,3420587,92044,108590,125155,134826,12880302,2262746,12560147,3701],[16384,15049162,288375,13698710,13665913,225],[16384,152008,2656840,862808,4532826,4567497,1413428,13775301,13705599,288334,1623],[16384,75488,152007,13709763,280151,2656840,862808,1614]]

def largehintsp31 : List (List ℕ) := [[16384,2656840,862808,288375,13698710,13665913,225],[16384,348618,61881,217509,7867580,8334590,7121199,191366,1421771,4559156,160204,70087,2295516,9383167,9341156,1836760,420888,13814765,4679432,13968266,2216],[16384,2295516,3352320,3420587,321419,13961373,5433099,414019,7120643,7211907,13895703,1836760,4762634,1093],[16384,58914,217509,44752,78286,108636,126687,160204,184012,3345284,321531,13895678,4762548,13968453,2205],[16384,3345284,1846171,304955,13764418,7113606,8334286,354607,4541],[16384,61881,217509,6032570,14942292,634060,15015944,797902,15048719,814272,15065107,1682641,15147048,2600141,15212597,3796165,15294528,4467920,15310917,5221588,15343693,6941896,15425630,11136203,15556726,4633025,1338561,15130660,1699010,15163436,2124995,15196211,3173572,15261756,4484294,15327305,5237959,15360079,6925523,15409243,9989322,15523955,201165,10357813,5540913,4041795,4074568,3157202,15245368,93914,143073,4567503,1413428,44752,75488,108590,126687,7867580,1322191,15114271,192976,151244,13709763,2656840,862808,288334,321501,1618],[16384,2656840,862808,288334,14026916,13705689,6105695,13672741,15009401,15048933,1623],[16384,13968585,14001411,2097],[16384,217509,44752,93914,110300,126687,143073,3788],[16384,58909,217509,44752,75488,108590,126687,8293566,6139110,15380945,160210,209364,134831,11667884,6032570,85694,4032398,10299834,437397,14026893,10415331,14181701,15518851,6384863,13952150,15289474,1198],[16384,61881,209364,216989,44752,108590,126687,134831,11667884,6032570,15380945,85694,4032398,10299834,437397,14026893,10415331,14181701,15518851,6384863,13952150,15289474,1198],[16384,1418976,3352320,7120643,14029236,13722078,4630247,13984972,404104,13783400,13598802,1337079,34],[16384,7113606,15443255,8334286,354680,14092692,13598816,6925260,14065753,15403386,7039933,15065578,3345284,1846171,8037137,13771555,1682336,13803558,4632768,8053526,13787944,7105471,15131426,7302083,15328470,1413363,7089098,15115037,296770,15139748,1863],[16384,404104,4456],[16384,15304885,15106819,1417593,13787904,4645560,15131401,15059594,1436387,399],[16384,61881,217509,8334590,9383167,9341156,7867580,9021740,15307194,9267513,15492327,462281,3598],[16384,13672713,12913072,11643352,356827,15304885,4530440,15016218,280185,75495,152022,862808,1092193,11667884,14214574,11495900,15557879,462288,11250126,1125878,1539],[16384,61881,217509,44752,8293566,7867580,6032570,6155482,6417632,15607236,15377740,8334590,78295,6204647,6221019,192984,152022,93912,108590,126687,1421781,13598802,814272,13721617,1338561,13787170,4484294,13983815,4624857,2656840,3418740,4041333,4729459,2600141,13869108,4467920,13967427,8907977,14147691,9989322,14180466,143836,200386,5540913,5221588,14000203,321501,15337665,5483126,5581916,4422],[16384,61881,174731,217509,6032570,14037469,15380945,362629,460944,346242,7867580,9383167,9021740,11643190,11242836,8293566,477401,297082,8334590,7121199,3346868,411788,9341156,2305069,2139935,12560222,12357145,12922382,2550],[16384,58909,217509,6032570,15380945,184789,3345284,1846171,304955,14026874,4559326,4620664,6204647,6237089,15118766,13764456,786],[16384,7113606,15443255,8334286,354680,14092692,13598816,6925260,14065753,15403386,8234183,13968599,15304867,7285707,1233],[16384,75523,61881,217509,8293566,4559326,7867580,6401256,15380945,192992,152022,2656840,6032570,14026882,6106340,13672741,13968585,15304867,4532826,15016218,862808,288375,1657],[16384,2656840,862808,15016165,288380,1657],[16384,4559326,61881,217509,6032570,15380945,14026882,6401256,13968585,15304867,15040971,6106340,13672741,160226,7123425,191366,70102,2295516,6253788,13820826,1795847,15163804,412653,3352320,7211907,7351531,14066987,1421791,6155482,13722078,4579657,15065554,6221019,13787927,1435378,15131022,395914,1836760,7023431,15409637,2442]]

def largehintsp32 : List (List ℕ) := [[16384,2295516,3352320,7120643,14029236,13598802,1697548,13819946,14083375,1836760,420888,15420394,15164325,3053],[16384,4559326,61881,217509,6032570,15380945,348643,8334590,9383167,9341156,8293566,7867580,6401256,7301432,7367906,78308,192992,152022,2656840,862808,288375,14026871,6139110,13705689,6106340,13672741,15053282,1686],[16384,14181701,13722078,13787927,13984972,1413593,288334,15518839,13705689,15042157,523],[16384,15442417,437407,346428,9341156,15360471,470538,14011552,9283892,14148882,9005367,15491587,3595],[16384,13722118,13787958,13985002,1413593,13705738,1645],[16384,14184936,15518900,15065608,15131448,15328492,1413428,15016252,13665938,13705441,1645],[16384,15065608,15131448,15328492,4404],[16384,283113,1418830,15528426,404104,14175393,13722118,13787958,13985002,4456],[16384,61138,217509,44752,93912,110301,126687,332261,6401256,6434028,5572655,207964,134850,12880302,6032570,4565107,10070453,10086848,11667884,7867580,5335175,7974138,10365060,8334590,9383167,8293566,2656840,862808,6139110,6155482,4630649,6221019,6417632,10415331,437407,14037478,14099764,11643352,15053287,10135991,10332291,10054230,463339,11250126,9014612,1092193,288383,14184936,354604,15518859,15436078,10480889,1410],[16384,217507,44752,110301,126687,160236,209364,134831,11667884,332246,6401256,6434028,5572655,85694,4032398,6032570,5548158,437393,3233],[16384,160236,332246,217508,6032570,6401256,4565107,4630649,404104,53741,1082886,11249216,11677158,44752,110301,126687,143503,6434028,5548158,207921,85666,10299328,3409804,853508,1435182,1779230,1795632,3253793,7022118,3319718,3336113,3352487,3368883,4761723,7219115,4032398,7268294,8219894,1115656,9020991,9235900,8334590,9350626,9383167,5572655,437393,7123125,420739,15126255,3942331,15295220,13945908,10315719,14165167,354532,10153081,15508285,11464125,14197941,11300273,15541061,362925,12889227,12922347,2475],[16384,1413614,332245,217508,44752,58909,110301,126687,160236,209364,134831,12880302,6032570,6434028,5548158,10299834,10365060,437296,281719,397805,6401256,5572655,4565107,863030,1093775,1126374,1539],[16384,11250126,11643352,9014612,354604,14092604,14132599,10512841,15476117,2412],[16384,9020991,11249216,11636052,853508,10069545,15065608,1082886,9350626,354532,405840,13716255,9004597,14131714,10513873,15476117,2464],[16384,160236,332246,217508,44752,15520239,6032570,6401256,4630649,10332291,8334590,9383167,61937,110301,126687,6434028,5548158,207921,134831,7867580,10480889,15443330,430576,11667884,85694,4032398,10299834,3221],[16384,160236,332246,217508,44752,6032570,6434028,5548158,10365060,10292272,92096,110301,126687,141754,207921,3746],[16384,4065168,3909562,15331298,13978469,13754972,15093230,13952129,3988],[16384,160236,332246,217508,44752,110301,126687,438771,207919,85666,6401256,6434028,5572655,52911,1115656,6032570,4597876,4794493,4630649,405840,463348,9020991,11249216,11636052,1418781,10332291,8334590,9383167,15528433,14176750,1082886,10513873,14132628,9350626,354532,15468960,853508,10069545,13722118,15059768,9004597,516],[16384,14176754,135669,11667884,14206381,160236,332246,217508,8334590,11643352,9350666,11594207,9383167,11626978,10512841,14132628,15470765,7867580,10480071,14099841,11250126,9014612,354604,438771,15436092,8293566,15369527,9317615,1341],[16384,14206381,14132628,14017820,15355040,15475992,9343149,14149010,15492372,3595],[16384,160236,332246,217508,6401256,6434028,5572655,135669,11667884,6032570,4565107,10086848,5351541,5367950,10103222,10119624,9283713,9300111,10365372,8334590,11594207,9383167,11626978,10496446,10512841,438771,471542,14184951,15518900,15361311,14011552,13754981,15098524,7073231,11250126,14148882,15492499,9350667,11643352,14132502,15476117,4270],[16384,15525297,3233],[16384,13722041,13787890,13984897,404104,4456],[16384,404299,15126836,15409954,15442730,421659,13978446,14066900,14099676,346342,13919302,15262444,14083280,15426334,7211913,2353]]

def largehintsp33 : List (List ℕ) := [[16384,15164295,15131344,15410390,15443166,421659,13781832,8053447,14099240,346427,7086788,14082844,15426770,9350171,2276],[16384,13978446,13814796,900],[16384,1836760,4663042,1418976,3319523,4630247,7087850,7104245,8054521,3352320,7120643,7137034,8087310,404299,15331836,15061499,1779454,15163800,414205,15442423,15404827,2295516,7039969,490],[16384,14099676,15436090,14066900,15403408,1367],[16384,13988351,15321890,15443166,14092602,15410390,14059920,1364],[16384,13804456,15140724,13771555,15107914,719],[16384,332261,217508,6401256,6434028,5572655,7867580,6032570,4565107,7990514,4761723,7284864,7301259,8252663,8334590,9383167,78334,184824,3345284,7113606,7211912,354607,397824,4630649,1411720,1846171,8039675,8072445,304955,14103041,15436080,15147946,13797213,15115045,13764426,714],[16384,14034227,15370452,2298294,3355055,15436180,15312089,13961397,13820810,15164335,13919307,15262823,412549,14066895,15410519,7121274,7219594,2947],[16384,14094851,13968599,15304867,15147909,15180761,6399174,15377610,2298284,13820845,15164300,412653,14067028,15410385,14132599,15475937,9341160,7121274,3117],[16384,15420394,15304872,1237],[16384,13968599,14083419,414213,3345283,4620664,13771555,304981,15107944,4526],[16384,15380918,304855,2231],[16384,168450,4557451,217511,6032570,8293566,4622989,1845938,2271929,6204647,4664009,4680382,6237417,8088820,4696785,6270193,4778687,8187125,7285451,8236284,9251536,8334590,9383167,6401256,338035,348676,9341156,1411721,8039675,7867580,7121199,7219505,7301828,8350968,14103046,14034227,2298375,420909,15370380,15312074,13961384,6253788,15164316,13814765,906],[16384,288413,13731487,15049162,13698710,358],[16384,233937,9014613,9252226,14132447,9317766,15476029,346464,9350532,9383303,8325348,11636057,7301534,14083283,7367021,15426865,445477,61881,108653,126688,143074,4599145,13738587,6172016,15082094,280220,1092965,1125735,853507,158296,11242839,11480462,14198001,11546001,15541576,363038,11677072,12922259,12880299,207980,224510,36528,4084],[16384,233992,11242839,9014613,1125735,4599145,6172016,15082094,15115028,15311619,4567561,174731,13971978,444606,346293,9350532,9383303,8325348,45044,428221,362682,11677072,10299930,10365469,5540912,92094,108653,126688,143074,280728,1092965,853507,158296,12922259,12880299,207980,224510,3747],[16384,233976,61140,126688,143074,200368,85709,3802],[16384,233937,9014613,6172016,15082094,108653,9383303,7874860,224444,152076,2656840,1092965,288383,13731484,6105695,15016230,13665913,238],[16384,13722114,13787953,13984998,1413593,13705722,15049092,280151,13730444,1627],[16384,233937,9350532,9383303,8325348,9014613,7367021,15426865,191397,37389,525766,7874002,453958,14076965,6038992,6055391,14966871,15623621,14050637,15394090,13618363,6923729,90],[16384,233992,9014613,9317766,15476029,191397,4633099,174733,356879,14125408,9104759,13820853,13730444,1125735,8990080,9006453,9071990,15115028,9268602,4559374,288408,15158242,6243228,15623621,14050637,15394090,445698,13705722,15042198,6128091,108653,8957311,13672757,160226,224476,37388,525766,6038992,3383],[16384,233992,9014613,75480,6197776,15106835,9055617,15475501,174774,356879,14125408,9104759,13820853,15158259,1852118,9088387,13804464,6234819,15147927,296824,1914],[16384,13656262,14247331,15584797,364141,12773924,1355],[16384,8325348,7121276,3113]]

def largehintsp34 : List (List ℕ) := [[16384,525766,8938993,12363242,6088175,14999741,479762,2139622,3714],[16384,2656840,6105695,15016230,1092193,288383,1666],[16384,1411721,6138530,15049179,1623],[16384,233992,9014613,6172016,15082094,13731484,1125735,13705574,11242839,108642,1092965,13672686,160277,176662,217612,6032570,6139110,15052822,1418839,4564630,14942292,814272,15065107,1469789,13787690,1338561,15130660,4484294,15327305,4624627,4599145,13967963,4467920,15310917,2200],[16384,233992,9014613,9317766,15476029,414225,11636057,9350532,9383303,356883,14125408,11242839,12873086,12922259,45588,75480,191397,283159,13730444,1125735,1418843,4564632,9006453,13722114,9071990,13787953,9268602,13984998,4624857,9252226,13968607,15304885,397786,1092965,853507,6400827,1226],[16384,6032570,14026882,13598802,1699010,13819946,8891606,14131302,15468950,15164343,412653,1322191,13770780,15115053,1682641,13803558,15147954,296665,4467920,13967427,15312097,4565155,257607,233992,9006453,15065604,4630709,1338561,13787170,9071990,15131442,9268602,15328488,1413363,3352379,6925523,14065753,15410530,7121274,7219594,2947],[16384,108590,152076,58909,93912,125155,233941,143074,200387,5540913,5286494,1125735,5319770,5352814,9014613,288351,14004549,2656840,4041333,321501,15337665,15016225,13709763,15049172,1618],[16384,14999689,13651558,13738127,15081835,1695],[16384,525766,845293,1074672,2139622,487042,15053339,13698647,13656199,9011850,13738342,15074972,14999697,3686],[16384,13820314,13738342,15074975,15163961,412642,7971297,14098925,8004212,15442562,8071503,7119773,3113],[16384,233895,11242839,9014613,1125735,11636057,8990080,288351,45596,75488,191397,168474,7023263,7973539,7056748,8007025,9350532,9383303,8327187,1796753,1830238,13709853,15042135,6138530,6172016,6041622,15081835,13731484,1043803,13623320,813711,14966804,6188386,14049904,6154902,15393247,445627,14099072,15442417,7874862,14033516,15381015,8300708,3257],[16384,13853246,13656207,487042,14995046,15196323,3683],[16384,525766,1074672,2139622,13742623,15074975,15196736,487042,13848163,13656225,14999697,3686],[16384,1421854,233895,11242839,2256223,45600,58882,108590,174729,191397,152076,93912,125155,143074,200387,5540913,5286494,1125735,5319770,5352814,14004549,2656840,4041333,321501,15337665,5336143,15065560,4729459,5483126,5581916,4632902,5401681,15131408,5598293,15328453,4559156,862808,4532826,15016225,15312065,4553],[16384,13623404,13853685,15191659,14966833,14050623,14034235,6269110,15393766,445627,8300756,3257],[16384,75480,108590,233992,11636057,9055617,9088387,9104759,9252226,15381016,9350532,225817,283169,1092965,1125735,853507,158296,1421854,174729,191397,37388,525766,9014613,2106827,6038992,7874002,8908147,9137528,9317766,9334139,2139622,487042,14135842,15468913,15197175,13848171,13656225,8940916,14999752,4564633,9006453,15065604,9071990,15131442,9268602,15328488,4624692,15312097,13961397,13763326,13812570,1852116,305017,3687],[16384,487042,13848196,14083050,14995187,15425727,3109],[16384,525766,2139622,6956521,454644,15192612,15426539,14076965,6923729,13623386,15156061,1680842,14966825,3400],[16384,233895,9014613,1092965,2664063,158280,1125735,1418847,174729,4620],[16384,15082048,13731487,14082684,15426539,3038],[16384,257607,348707,233992,9350532,9383303,8325348,11242839,2256223,7073123,9014613,7153994,8104267,11636057,422419,45605,75480,108590,191397,7874860,224444,291366,15200807,15164252,13814754,7121224,14082978,15420382,1830238,13738551,15074972,638],[16384,7989659,13705716,4564630,7973182,13722095,8235352,13984984,395916,8251807,13968603,8284522,14001423,5572657,1418839,4630680,8038727,13787940,15126771,2798],[16384,15426174,14076894,14107989,8349006,14099803,15442562,15016178,15049067,15065460,15311454,15327842,15344230,356905,7989665,13705716,1418850,4564635,7973184,13722095,8251810,13968603,4630709,8038734,13787940,8235358,13984984,4569],[16384,191422,15381015,6039671,15410512,6924589,14966876,7350620,15394094,7874862,8300895,453817,3259]]

def largehintsp35 : List (List ℕ) := [[16384,224510,233895,11242839,11636057,9014613,1092965,1125735,1142108,4599145,4615521,5352814,7056748,7073123,8007025,9350532,9383303,15086122,13731487,14123659,13705574,14082684,15420382,1043803,13623320,6172016,14033516,6188386,14049904,14066296,14099072,8349006,15443293,348715,7039386,15049193,4564630,8990080,9006453,9071990,7104924,15115041,9268602,4624910,13967963,7301534,15312085,2200],[16384,8335916,15410512,233992,9350532,9383303,354532,15436006,8350062,1373],[16384,8299831,15410519,7121228,15158151,6236313,15393688,15459699,445631,8078255,6434066,15337525,7219540,15256457,8176743,6401302,15304755,3343222,15147858,296767,1419067,13722114,4630357,13984998,4559321,15040971,2306600,2262743,15131346,396018,5319536,468],[16384,233992,9014613,13731484,8007025,14099072,11242839,14189220,11636057,14124441,1125735,8990080,9006453,9071990,1469789,13787690,1813866,13804079,1830238,13820471,3304800,13918794,9268602,4599145,13967963,5352814,14000740,6172016,14033516,6188386,14049904,75480,8335916,9350532,9383303,354532,191362,15381015,7056748,14066296,7073123,14082684,1043803,13623320,15430189,8023396,14115460,15446574,7874862,15403238,6941651,14966879,8350681,15459676,6039671,8300708,453817,3261],[16384,14092518,7219594,8350120,14083419,13912969,7121274,13814663,3343219,13804369,296791,1419067,4630357,13787853,4559091,13961379,2306600,2262743,396061,8235899,1239],[16384,15077935,233992,1142108,15065460,1469789,15131180,1813866,15147570,1830238,15163961,3304800,15262284,4599145,15311454,4615521,15327842,75480,8335916,7056748,15409786,7073123,15426174,8007025,15442562,9350532,9383303,354532,14062128,14099796,7874862,14083407,6941651,13623389,1043803,14966809,8350681,14116186,8023396,15458951,445629,8300895,6032569,7351261,14034219,6172016,15377006,2167],[16384,15369527,15065591,15131434,15328478,4624692,184843,2946],[16384,233992,9014613,283185,75480,108590,191362,217638,7867580,8293566,1125735,1418847,4564633,7990514,6204647,8056051,8252663,15446578,9383303,354604,14092597,14132599,15468896,13722101,13787944,13984988,4624857,8236284,13968599,15304885,9252226,1249],[16384,61881,75495,108602,125198,233992,143074,9014613,9383303,14132599,15468896,9252226,15312097,13961397,8226007,174799,13763326,9088387,15147954,3355068,191364,9284997,15344915,209341,224508,151216,85699,3800],[16384,152076,61138,93912,233964,126688,143074,3779],[16384,233895,9014613,75495,108612,13763326,1453416,13738532,291366,15074972,5352814,15344230,209341,168501,1411721,1125735,7023263,14103092,8007025,15442562,7973184,7056748,9350532,9383303,8327187,7989911,15049067,8023396,15458951,446450,8300895,6434113,13697408,5319328,14000595,6138530,14033369,15381015,2101],[16384,14103092,8300948,233992,9014613,7874869,224444,13972022,75495,108602,291366,15304856,4599145,15082078,13731484,6188386,14049904,15106819,6172016,14033516,15381015,6219991,15393560,8022423,14115460,6039671,453817,15453375,8055204,809],[16384,862808,1092193,3222108,2656840,3418740,321507,13676685,13742179,13701212,13902254,15074953,15245896,2010],[16384,58882,75520,108602,125169,233895,143074,11242839,1125735,3288427,160312,9014613,7056748,8007025,9350532,9383303,1421331,174729,200394,10357813,4661953,5581916,304981,15150839,13775292,15107907,5540913,4074568,321531,13797204,1813866,13738543,15074917,1453416,552],[16384,61881,75495,184887,93913,108602,125155,233992,143074,7211912,3345284,3255218,7023561,14103092,7973213,5417886,8334286,7874869,224444,283193,1092965,1125735,853507,158296,174747,200394,5540913,10357813,4661953,5581916,304981,15150839,4074421,321531,13797204,3976093,13935483,15271935,13775292,15107926,3943493,755],[16384,7211912,7113606,15410084,404104,14059920,13796257,1797004,13722011,1862542,13787861,4680593,13984649,4456],[16384,174733,233955,9014613,1125735,1418847,4564633,108590,1092965,2664063,158280,193083,217612,7867580,14092597,11242839,7988933,13722101,8293566,14026036,6221019,13787927,6417632,13984972,404104,4456],[16384,6032570,14026871,13598802,797902,13705229,6139110,6171886,15052822,1418839,4564630,814272,13721617,1338561,13787170,4484294,13983815,4569],[16384,108590,174733,233955,11242839,1125735,15381015,225853,152076,2656840,201269,5540913,5286494,5319770,5352814,14004549,13935757,4041333,321501,15271906,3844701,15016213,10292275,11677072,371226,13665928,862808,1092965,3877956,15049146,3911021,15082065,4014],[16384,291388,184894,7113606,15410084,14059852,7211912,13894749,3255218,13705646,174733,233955,9014613,3287992,13738566,15074972,1125735,15049067,1418839,4564630,1142108,15065460,3337130,13787886,1469789,15131180,4615521,15327842,4339],[16384,4633146,233992,9014613,75480,15143487,9088387,15475634,14125408,13730444,1125735,8990080,9006453,9071990,15114959,9268602,4559374,288408,184894,9252226,13968607,15304850,15040971,1769877,2970],[16384,108590,201269,5540913,152076,5286494,233957,1125735,5319770,5352814,291366,14004549,13935757,2656840,3418740,321492,15271906,9014613,1092965,3288427,13742169,10292275,11242839,11677072,371226,15074993,3911021,593],[16384,321492,13742169,15074953,13676685,15009397,242],[16384,1411721,15213123,15245896,13775243,15114792,1125028,288333,1850]]

def largehintsp36 : List (List ℕ) := [[16384,414259,233992,9014613,9350532,7121224,7219538,3345283,9383303,8325348,3222528,4074527,75480,191366,7874860,224444,168513,1411721,1780752,1453416,2731366,3288427,3419138,304955,61881,92071,108590,126688,143074,11242839,862875,1092965,1125735,3255313,291366,2667074,158280,200391,5540913,321531,15086147,10292275,11677072,371226,13731505,13705574,1813866,13804079,4196],[16384,15381015,8299831,233992,9014613,8007025,15082114,13731484,6188386,14049904,4624958,4599145,13967963,15304856,6172016,14033516,6416600,15393997,15623621,14116239,15459699,445631,8226009,6434100,5352814,14000740,15337525,6039671,7867577,14942306,108590,174799,224446,201269,5221471,77],[16384,7113606,8334286,15410519,2426],[16384,356932,15438400,75480,233992,9014613,9383303,15476091,14125408,9350532,14067039,193094,283205,13730444,1125735,1418843,4564632,9006453,13722114,9071990,13787953,9268602,13984998,4624857,9252226,13968607,397786,108590,217638,8293566,6204647,2306600,6237417,6270193,9317766,14034235,2265607,1092965,853507,2883],[16384,15476091,14125408,13623404,14966885,445729,13968607,15304885,8226009,3388],[16384,15475937,14125408,13623404,14966858,445729,14099831,8300948,3257],[16384,15446600,15315529,13961397,13623368,14132447,15468896,14966893,445729,8293561,15377725,14026964,13763326,6204729,786],[16384,14116059,13623368,453958,14961953,15458403,3358],[16384,348746,8325348,8251807,13972043,8300891,453817,15304894,15459549,14109982,14966858,13618465,97],[16384,14966858,13618465,14114913,15459549,3358],[16384,14114913,15453470,13721614,13787166,13983812,1413593,13705234,288351,15042160,502],[16384,8325348,8251807,15315533,4565163,7989659,13627982,14961953,15065104,15130657,15327302,1413428,15048724,15458403,282610,1631],[16384,15114277,14135822,15474797,2400],[16384,14971472,13618465,14131308,15468896,13721614,13787166,13983812,1413593,13705234,11240073,288360,15042135,15106436,9052542,813],[16384,356943,4559441,288409,15304850,11240073,13705670,15042198,11215353,15540751,15082151,13731487,1040407,13623320,14961933,74],[16384,13963858,4596313,13738587,11240073,13623368,14961953,11133034,15540343,15082151,280220,1418847,4564633,15065104,15130657,15623621,15328511,4404],[16384,14099831,15436180,15115045,4559374,13968607,15312089,13730444,288408,2194],[16384,233992,11636057,9014613,37447,525766,796103,812504,1320393,1336793,4466126,4482522,7874002,8906210,1125735,8990080,9006453,6038992,7890400,9252226,9317766,9350532,9383303,4633164,9071990,9268602,447059,8293561,8039738,8236348,354651,14135892,15468950,15377725,14026964,6401339,13968585,15312097,4565155,15065604,6434124,9284997,15344915,5575123,6417696,13984972,15328488,396066,13789987,15131442,1413363,6139191,13705689,15049213,280151,15073936,1628],[16384,6399174,4565154,1413428,288351,14092639,13698658,493],[16384,75488,174733,332352,233892,9014613,1125735,288351,13698658,14098925,14059750,7012834,191433,201269,13721931,15065478,396007,4563320,5581644,6400851,6424623,3168],[16384,7974200,332373,224471,233892,9014613,1125735,8236348,8303190,6032569,42448,108640,1421911,4559156,288409,13698715,75480,174733,14098925,14059750,13959622,6391923,14025928,7341355,191437,152076,2656840,13665922,862808,225],[16384,58914,233893,9014613,1125735,288409,13698715,42450,108600,14092590,14067028,7121228,191366,152076,2656840,13665922,862808,225],[16384,7869016,42450,75480,332373,224471,233892,9014613,174733,4567641,1413428,1125735,288351,14092590,13698658,7963117,13721931,396015,5581671,108592,14067028,7121228,191366,6400885,6424623,207968,4661],[16384,7963117,13721931,396015,8028963,5581672,108592,174731,14067028,7121228,191366,224506,201269,6400886,6424623,3168]]

def largehintsp37 : List (List ℕ) := [[16384,1413428,174731,233986,9014613,1125735,288351,13698658,332352,13762943,75480,14103131,7971308,7874862,8300895,6032569,108640,224444,4695],[16384,2656840,862808,13672673,1666],[16384,14059750,7012834,191433,7874862,224444,4620],[16384,537178,42438,75480,4559452,108600,174733,233986,9014613,1125735,288409,13698715,160349,14094942,7963117,224506,184844,14067028,7121228,2950],[16384,7113606,14059910,13796257,6253459,14050201,8088468,14115756,8293567,7974180,8236325,4694],[16384,1418847,4564633,4404],[16384,332373,75480,174733,233976,9014613,1125735,455263,7973231,14059750,8350121,14116186,8236325,8303190,14044351,11242839,291425,7874862,13618365,6029395,42448,7357744,108652,224440,152076,2656840,13665922,649801,10],[16384,108600,13698715,160349,37388,525766,13959622,4482522,13623368,454644,3341],[16384,7983090,2467],[16384,8327778,75480,174733,233976,11242839,9014613,1125735,291425,224510,4567651,1413428,447076,45044,13698658,160349,102924,7874862,8300895,6032569,2144],[16384,8327775,45044,75480,174733,233976,11242839,9014613,1125735,291425,224510,4567651,1413428,13698658,160349,102924,14058835,7012834,13721931,396007,5581644,2096],[16384,332373,75480,174733,233976,9014613,1125735,14094949,14116210,455270,7974180,8236325,8303190,8318235,14050618,3263],[16384,174733,233986,9014613,15073936,1043803,14966809,1092965,15016178,1125735,15049067,1142108,15065460,1469789,15131180,4615521,15327842,6188386,15393394,7056748,15409786,8007025,15442562,8023396,15458951,184935,332373,8334286,447072,4703],[16384,174733,233986,11636057,15479400,395680,9014613,13738635,15082127,280238,11242839,1125735,1418856,4564637,2696],[16384,304981,15468880,15147954,13797213,15115053,13764459,714],[16384,6032570,6401256,2169],[16384,6038992,7874002,8293561,525766,6401339,2228],[16384,5540913,5581916,2224],[16384,45676,108602,209517,225899,168501,4557451,6400718,6039667,1411721,233706,9014613,291366,15074990,1126540,15049067,13698658,7973539,14098925,8007025,15442562,7874862,8300706,3257],[16384,168501,5581517,6400718,6424623,1411721,291366,13698658,6154902,14049757,3339],[16384,4625001,233992,9014613,9055617,9088387,3355242,332373,13738635,75480,191364,455278,15468912,8990080,15049213,9334139,15394113,108602,209517,225899,37487,525766,8908147,14966893,13618471,1680842,13819943,9104759,15164343,3155404,13918263,9203065,15262830,412549,6940125,14065757,9350532,15410530,7121286,7219602,2947],[16384,525766,455276,14961959,6038992,15392853,7874002,15458403,8293567,6401315,2228],[16384,14961959,15409247,15442021,8325350,15458403,15065104,15130657,15327302,291425,3336],[16384,525766,796103,1320393,4466126,6940125,7874002,7890400,4633201,447090,6038992,8293561,6401339,4565154,1413593,288351,15436127,15042146,7974200,497]]

def largehintsp38 : List (List ℕ) := [[16384,108594,191433,201269,396007,5581644,6424623,3168],[16384,2656840,862808,15016165,1666],[16384,10292275,10071144,15507975,11676779,371226,2587],[16384,233986,61140,184844,93913,126686,143074,3786],[16384,6391858,6039648,3387],[16384,184885,7113606,3345284,152183,2656840,3419057,321492,15403380,7211912,15238240,862808,3222448,3255218,282698,233706,9014613,1092193,1663],[16384,5540913,5581916,4565148,1413593,10292275,11676779,371226,15501879,15271085,3877956,15049146,280169,1631],[16384,7867580,6032570,6401256,4565107,1413593,288351,15436078,15042146,7974138,497],[16384,174733,233986,11242839,9014613,1122661,209530,225915,103033,4565048,1413593,288351,15042146,1433928,15131022,4581449,15327697,395918,5572656,7023436,7973735,7053943,8004223,7990048,8023396,14115460,8335301,4114],[16384,14127728,233992,9014613,13730444,1092965,13672686,1125735,13705574,7056748,14066296,332373,11242839,1043803,13623320,1142108,13721970,1469789,13787690,4615521,13984352,6188386,14049904,8007025,14099072,8023396,14115460,45683,75480,10104175,14164633,4625020,108602,209517,225899,168569,1411721,7023263,7973539,288351,8327186,15042146,7989911,15458806,445704,5581517,6400718,6424623,4557451,8300706,3393],[16384,14109960,13731526,644],[16384,15042160,15081835,15458806,4734],[16384,45044,6401327,108594,6434113,5572655,174797,191438,207964,224510,4661],[16384,13701759,14115316,15453448,13738342,15075014,647],[16384,13721931,13984207,404104,13783400,15623621,15065627,1436378,396],[16384,14197571,15534623,13984513,15321840,1272],[16384,404104,13717864,15623621,15049244,13738354,15321840,15082082,1545],[16384,1421953,13709954,371254,404104,13791875,13980292,9011850,14165230,15501851,10101399,15082139,13731512,608],[16384,224510,233892,11636057,5581916,6433888,6391855,10292275,11242839,1125735,1142108,5540913,4565148,4581579,4614351,8023396,4633197,11300232,10349671,11495633,11676779,455296,283269,9014613,1418847,110300,191438,37414,525766,6039678,1092965,853507,404283,15462209,371226,14109992,13722095,13787940,13984984,4456],[16384,14116056,13722057,15059772,15458802,3377],[16384,404283,13988487,15321975,15459546,14110001,15065549,13716284,495],[16384,15126255,3812],[16384,233992,61140,75480,348797,9350532,9383303,8325348,1092965,1125735,853507,9014613,4564633,7972524,8235352,332373,8300891,455296,6402696,108594,126688,143074,2664063,158280,1418847,174729,7121224,191366,7874860,11242839,7988933,8038727,209542,224444,36528,525766,85658,3409804,796234,1320393,1435315,1779296,1795778,3253888,7022251,3319718,3336113,3352487,3368883,4761513,7219538,420866,397961,5581622,6424623,5515178,7317849,5547966,10299328,4622984,10365112,437296,15429422,14076960,6924587,13623386,14961992,1336793,1680842,1697243,2106827,3155872,6038992,12330454,2139622,12363242,11636057,8055197,8071497,8087910,8104267,8169811,7350618,14050604,12822881,3875],[16384,14109960,13623393,15078014,14966809,3341]]

def largehintsp39 : List (List ℕ) := [[16384,15454859,15082119,13731526,14966883,13618445,24],[16384,15065586,15131430,15328474,4404],[16384,348797,233992,9350532,9383303,8325348,11242839,1043803,9014613,7874860,8023396,291466,332373,8300891,75480,455296,537228,42438,1125735,11636057,7989659,1421953,174729,7121224,191366,7973182,8038727,8235352,209542,224444,102965,6039648,4565048,4630586,15463053,404104,14110001,13623393,15078014,14966809,14050613,6188386,15393394,3259],[16384,75495,108602,1839758,174770,191387,4661],[16384,853507,1418847,404271,14110001,14075222,7972524,13722095,15059772,15131016,13781844,9348433,8349006,14067034,11240073,7038659,15409642,14132607,15475204,346344,7088454,796],[16384,8071549,13820841,7121276,420886,3092],[16384,291472,14109960,14075222,8349006,14067034,15078014,15409786,15163961,357009,7121228,13820834,420849,3056],[16384,14099826,14059750,8350121,1370],[16384,224440,233895,11636057,1839758,11242839,9014613,1092965,1125735,9006453,1830238,7056748,8023396,9350532,9383303,9399677,8336018,354532,8300895,14119571,14044351,7874862,13618365,6029395,42448,14059750,6930525,14083407,412627,7113684,75523,108640,174770,191387,152076,2656840,13738616,15074990,15016178,13665922,649801,10],[16384,1839758,14094996,14116210,8056067,13787944,396009,8088836,13820845,15164113,224440,233895,9014613,9383303,354626,412656,11636057,11242839,1092965,1125735,9006453,1830238,7056748,8023396,9350532,9399677,8336018,14067028,7121228,7219540,3345283,3310269,7941410,13672751,7974180,13705709,853509,1418850,2865],[16384,1839758,224440,233895,1469789,15131180,1043803,14966809,1092965,15016178,1125735,15049067,1142108,15065460,6172016,15377006,6188386,15393394,7056748,15409786,7073123,15426174,8007025,15442562,283285,853507,11636057,11242839,9014613,9006453,1830238,8020614,9350532,9383303,9399677,8336018,354532,1418855,404271,13781844,13716255,387],[16384,853507,1418847,404271,15125332,15059743,15024358,1386078,250],[16384,404203,15125332,392],[16384,224440,233895,11636057,1839758,11242839,9014613,1092965,1125735,9006453,1830238,7056748,8023396,9350532,9383303,9399677,8336018,15086230,15475344,354532,14125424,14067039,14099831,15403238,13722114,9071990,13787953,291479,7874862,8908147,13623404,14116223,14961853,6930527,42461,9366908,14083429,15426896,412627,7113684,75523,8300895,9334139,14050623,15387839,7357746,108652,174729,191387,201269,9317766,14034235,15377706,329897,8990080,13705722,15049189,4564635,9268602,13984998,4624857,4717],[16384,1839758,7023431,15438489,863023,224440,233895,1092965,1125735,7973714,15049201,15086230,288259,13676462,9014613,15475344,11636057,11242839,9006453,1830238,7056748,8023396,9350532,9383303,9399677,8336018,354532,14125377,8990080,13705722,15009285,15623621,14116239,7941410,304],[16384,406170,224440,233891,9014613,15086230,15475344,11636057,1839758,11242839,1092965,1125735,9006453,1830238,7056748,8023396,9350532,9383303,9399677,8336018,354532,14125424,13722114,9071990,13787953,291479,15069848,7023335,15125225,14116223,8056067,15442730,4761],[16384,1413787,224440,233895,11242839,15086230,9014613,1839758,1769846,1125735,288352,13731526,13705574,11636057,1092965,9006453,1830238,7056748,8023396,9350532,9383303,9399677,8336018,354532,15042146,8007025,14099072,14115460,7974180,15442417,7874862,1043803,13623320,14961853,802836,42456,58909,75488,8300895,6188386,14049904,15387839,6029397,108640,126688,143074,13672686,160373,174770,191387,10104175,14164633,209526,3760],[16384,174751,191433,233976,9014613,1125735,15081835,9350532,354621,13731502,8007025,14099072,7874862,8300895,6032569,42448,58918,108640,125164,143074,1092965,13672686,160373,11242839,10104175,14164633,209526,224444,3760],[16384,7874862,8300895,6032569,42448,58882,108640,125155,233992,143074,1839741,174770,191387,224444,3760],[16384,1839758,1411911,174751,191433,233976,9014613,9350532,354621,13763273,13697408,1453416,13738532,15074990,1092965,15016178,160349,14095006,15053469,15409636,14059839,8324436,45044,7963117,224506,332314,1043803,14966809,4567651,13820753,13787851,13721985,15623621,15164359,15131344,15065478,6394484,1769846,2896],[16384,1839758,1769846,75488,15053469,7078267,7111364,174751,191433,233976,9014613,9350532,354632,13698659,15623621,15065627,396006,15409636,14059852,13796257,201375,13763354,7056748,13738616,15074990,5352814,15344230,332221,5540913,5581916,6433888,4367],[16384,14164485,15501851,14197261,15534623,11445416,15279282,1197],[16384,10292275,10071144,11676779,371254,13709985,15042153,15540751,14191125,14160502,13927594,11447372,1200],[16384,412656,13731502,8327186,1769846,7119249,3088]]

def largehintsp40 : List (List ℕ) := [[16384,1839758,233992,9014613,1125735,15623621,13722140,7025312,7971312,7056748,8007025,15106436,15139534,1813866,15082034,13787522,13820620,15065420,15131015,15164113,348835,9350532,9383303,8325348,45044,8300891,75488,340608,1769846,7086460,7119557,420880,4652],[16384,4633231,233614,9014613,9383303,354627,1839758,191387,332350,1092965,13672686,4615521,13984352,6188386,14049904,7056748,14066296,15607236,14099853,10104175,14164633,4732],[16384,15438500,7963121,233992,9014613,15106436,1839758,15139534,1813866,15082034,8028541,8061638,9383303,354633,13731502,15623621,13722140,13787522,75488,11636057,11242839,11218316,209570,224506,37541,525766,7874002,3384],[16384,15053478,329303,345698,233992,9350532,9383303,8325348,9014613,8300891,75488,4736],[16384,8325348,7137637,14082982,15426904,7121224,420880,3038],[16384,58909,75488,1839758,1769846,447132,13701799,1433928,1794442,13820314,15623621,15065627,15163799,233992,11636057,13762943,13796040,9014613,9350532,9383303,357032,412655,13721931,396006,11242839,1453416,13738532,15074994,8007025,15442562,11218316,209570,7025311,7119249,14066146,7056748,15409786,7219540,3345283,92071,126688,143074,1092965,15016178,160349,174770,191387,14095006,7963117,224506,36534,102042,537208,1478],[16384,6038992,7874002,8293561,525766,7974200,14098925,2399],[16384,7867580,7974138,14098925,2350],[16384,174729,233986,9014613,1125735,13738342,15074990,8007025,15442562,45738,1092965,15016178,160349,1839741,191387,225963,102924,4565048,15623621,15065627,4630586,1469789,15131180,4615521,15327842,4404],[16384,5572656,4663355,4032398,3876793,4565048,3942331,4630586,4794430,13955578,404299,5548122,437393,15289490,4065168,15254592,3352487,15164278,3409804,420858,15323645,1155],[16384,13722101,13787944,13984988,404104,4456],[16384,4565048,6039648,8300646,7867577,6424628,7990538,4630586,8056081,8251472,14103214,15436078,14942306,814345,15065107,1338640,15130660,15328478,4404],[16384,174729,233986,12922259,1839741,191387,332350,6391855,1125735,1142108,4565148,13709996,4615521,11636057,11300232,11496842,405775,13791875,13980292,14198006,12708051,14230780,6039678,8300742,7867577,15436090,12823869,15574410,15534513,11611538,1413],[16384,5540913,5287000,5319770,340589,14004549,15337631,2656840,4729459,5483609,5581916,4041795,321501,4422],[16384,111279,174729,1839741,191387,201269,10292275,152076,3418740,4041333,5540913,3894327,58882,233893,1125735,5352814,4633265,4795462,4811838,8203338,5581916,6433888,2656840,321501,11242839,11677072,371226,14095024,8137335,13870123,4074568,332350,6391855,8300742,8170798,13902947,13935774,405775,4479],[16384,15065604,15131442,15328488,4559156,15049213,1691],[16384,15479475,14125377,332372,13623404,11633288,14189976,11231744,13722130,11297583,13787971,11494627,13985014,11576670,14067051,11609460,14099843,4723],[16384,6038992,7874002,8293561,8906210,525766,8039738,8236348,14052622,14118159,4625076,4482522,7890400,6401339,338100,4682],[16384,1839687,191387,4624958,15446597,14092590,13968599,15304856,233992,9014613,8007025,13738624,15074972,4599145,606],[16384,174729,233986,11636057,8990080,9006453,13709996,11242839,9014613,1125735,9071990,9252226,9268602,9317766,9350532,9383303,45749,217778,7867580,8236284,332470,8293566,6401256,4630708,15479475,4565154,404104,14125472,13722114,7990514,8056051,8252663,14103214,15436078,15065591,13787953,15131434,2698],[16384,174729,233986,9014613,13730444,1092965,13672686,1125735,13705574,1142108,13721970,1469789,13787690,4615521,13984352,6188386,14049904,7056748,14066296,10104175,14164633,70268,2262746,2256223,13853246,4559321,15042203,2221845,15196579,478828,12560147,12889717,15303114,1839741,1433993,15131022,396018,10333042,15508715,12463474,14230189,12692352,15574266,11677072,12922259,371115,2479],[16384,13701811,15065604,15131442,15328488,4559156,13959622,15443323,7874862,8300895,6032569,13787532,396009,6400849,2168],[16384,174729,233986,9014613,1839741,70327,1435378,8990080,9006453,4630247,9070331,9268602,9383303,15479481,14125377,1795847,3352320,11636057,11242839,1125735,15082127,13731502,13705574,9252226,9317766,9350532,45749,4792],[16384,14132599,15468898,13701811,13721931,15623621,15065627,13787944,15131442,395914,7963117,2898]]

def largehintsp41 : List (List ℕ) := [[16384,13820314,8986974,14131706,15468865,9101878,15164343,412642,7211907,9347702,15410530,14059860,7023625,482],[16384,70327,2295516,174729,233986,9014613,8990080,9006453,1839741,1125735,1795847,1828623,7056748,3352320,7120643,11636057,4630247,8054521,9070331,9268602,9383303,14103227,340666,13710012,15479475,14125377,9103120,13820853,15116002,4559374,9252226,13968607,15304850,4679432,15164300,412642,7211907,9350532,14067039,15040971,13722114,4579657,15065554,13787953,4646643,15131401,395914,7023431,15409637,2388],[16384,233992,11636057,447132,1421993,348861,9350532,9383303,8325348,11242839,15426904,1839758,9014613,7121224,420883,14076894,7073123,13738620,15075012,1092965,1125735,1142108,4599145,4615521,5352814,7056748,8007025,332330,7039386,13705703,15049067,4564643,15065460,7088454,13787932,1469789,15131180,15327842,4624627,7874860,8300891,6032569,6401327,2169],[16384,8325348,15426904,7121224,420883,14076949,14107989,7973182,13722095,7874860,8300891,6032569,6401327,4630649,7088454,13787932,7285079,13984976,4456],[16384,15475506,14125416,15065480,13716255,514],[16384,14132017,13721987,15059743,15475204,2464],[16384,233992,11242839,9014613,1125735,15073936,1142108,15065460,1469789,15131180,4615521,15327842,4624993,15607236,14132644,13738635,1839754,191387,70254,1767],[16384,283326,233992,9014613,1125735,1418847,4564633,11636057,447132,1839754,7022251,9350532,9383303,1092965,853507,404271,357055,15479490,14125472,9006453,13722114,9071990,13791937,9268602,13984998,4624744,11242839,8908147,13623404,13706937,9334139,14050623,14067039,14099831,9399677,14116223,45683,209517,225899,4751],[16384,404271,13791937,15125271,15475506,14125408,15065480,13716242,514],[16384,233992,11636057,340675,1839701,9014613,283326,1092965,1125735,853507,1418847,9006453,9071990,348868,9350532,9383303,8325348,15426904,404271,7121224,420883,14076949,7285079,13984976,447132,7874860,8300891,6032569,7367021,14034223,15370378,6417693,15328462,5581646,7301534,13968595,6401327,15312074,7334249,14001421,6434113,15344902,2097],[16384,853507,1418847,2863],[16384,13731524,13820471,478237,13918794,3345285,13804079,296767,2304994,2139935,363510,12364278,12560918,3609],[16384,8038727,15131430,8087910,15147950,8071497,15164331,8169811,15262822,8325348,7121224,420883,283335,406214,13781832,853507,7973182,15065586,13716275,1418856,387],[16384,853507,7972524,15065586,406214,2847],[16384,1839758,233992,9383303,15454917,15623621,14099854,15443315,9399677,15476096,11636057,11242839,9014613,1092965,1125735,1813866,1830238,3304800,8023396,15082119,9350532,12922259,357064,14125290,13730444,13820471,1142108,13721970,291529,8071503,15164331,412656,7056748,14066296,8350055,15410524,8325350,7121228,3091],[16384,13672686,250570,12357148,12463711,14230189,15567351,12398166,15016259,13705574,12430935,15049237,853509,1418850,2863],[16384,250570,12357148,13742795,15074990,12463711,15573679,14223863,12553758,13829126,2174530,13672708,15016178,2207300,13705630,15049067,853509,1418850,2863],[16384,250570,12357148,15623621,13705755,15049036,12445373,15573529,14223863,12553758,13829126,2289209,13787870,1418850,15131016,2793],[16384,8988336,1122653,250570,12357148,13631701,1060404,13738122,15074825,667178,13672572,15009285,242],[16384,250570,12357148,14234318,15567351,14975192,667178,15016061,13665797,1060404,15081612,4014],[16384,250570,12357148,8987128,15475197,14125410,12856928,14230944,15567351,12553758,15172617,2207300,416],[16384,250570,12357148,11633288,12922465,371206,406220,15069901,863007,11215203,15053520,13701839,12430935,14230036,15567351,13738342,15074990,12463711,687],[16384,250570,2133530,2207300,13836702,13738342,15074990,2240077,15180348,296732,2305607,1795886,13820314,1828661,15163961,412656,3352351,7120679,7211907,2272837,1419032,13721931,15623621,15065627,1435437,13787532,1468212,15131180,395914,7023431,14066146,15403348,7056407,634],[16384,1140429,15065460,863007,15131180,13781737,13672699,15016178,1541]]

def largehintsp42 : List (List ℕ) := [[16384,250570,12553758,2272837,1402751,2133530,1468212,1418850,4564635,4630305,404104,15086291,13731512,14123659,13787690,13980008,9258214,9036317,14148244,13968612,15125225,4646703,15311625,14181023,15528426,15558066,430585,5540912,5581983,338128,2273],[16384,307924,8988260,1122653,11252433,250570,2133530,15173404,14975138,1060404,15081612,13731337,13754910,1076768,15098000,11264669,14213802,11169321,15556820,462168,1418827,4564568,2221756,15065508,1371681,15130775,4517412,15327413,4624692,1355309,15114388,13764419,1442340,3576],[16384,11252433,13710034,15045333,15081835,13731502,14123659,250570,2133530,2207300,15180192,296732,2305607,9103159,13820853,1795886,15163804,412656,7120679,8334355,13754910,15623621,15098547,14213802,15557139,462168,7056905,14066296,12553758,2272837,1419084,15065420,9070390,13787953,1435437,15131022,395914,7023431,15409637,8007186,14099072,7973714,15442417,2278],[16384,11252433,250570,12889692,12922465,11667883,12357148,10070516,11233800,10119697,11266578,10136056,10299901,10332672,10365442,13832918,2256440,13754943,2240077,13738555,15074990,15098399,11365953,14214147,15557291,462168,2174530,13672708,15016178,1402549,13710034,15049067,853509,1418850,404271,1462995,3507],[16384,250570,12357148,373463,406220,15069901,863007,11252433,13710034,15045327,12430117,15573525,14223863,12553758,13829126,9121358,14132209,8986974,15475197,2369],[16384,13718232,13705547,15623621,15049244,1418850,13787523,404202,15125225,1140429,13738354,15074825,250570,2305607,1435319,1794442,13803931,1860278,15147735,2223671,13836706,2289209,15180512,296669,2133530,2272837,1468212,556],[16384,250570,2133530,13705547,15623621,15049244,2221775,13836706,2240077,15180348,296732,2272837,1419032,13787523,1468212,15131180,2793],[16384,9011857,1089777,1122666,13726426,348888,250570,2133530,2272837,1419032,1140429,15065460,1468212,15131180,13781642,12553758,1402751,13672699,853509,412467,2305607,3352351,7120679,7211907,9350168,2386],[16384,250570,2133530,2240077,15180348,307931,13829916,13726426,1140338,15065460,862969,13665797,2174530,260],[16384,1418827,863023,250570,2133530,13829916,2174530,13672708,1541],[16384,15467151,15016178,398044,250570,9121358,15180787,299741,2133530,2272837,1419032,4630305,4557448,411299,2305607,3352351,7120679,7211907,9350168,2386],[16384,250570,2133530,2272837,1419032,4630305,4557448,411299,2305607,3352351,7120679,7211907,460455,362142,12357148,12922465,11250166,11643398,9014612,9350168,2386],[16384,307935,1418827,863023,250570,2133530,15173404,14975138,667178,15016061,1541],[16384,250570,2133530,15173404,2174530,15016197,853509,2221775,15065508,2809],[16384,348889,15086302,13731337,13672686,250570,2240077,13836859,406240,1140429,13721970,299745,2133530,2272837,1468212,13787690,15125225,12553758,1402751,1435336,855983,1419032,15065480,412467,15155920,2305607,7120679,8334303,9350172,461634,363303,12889692,12922465,11667883,12357148,11643398,9383443,2276],[16384,13721931,15623621,15065627,1780454,1417590,1436378,13787532,15075000,15467151,250570,2133530,2206449,13836702,2240077,15180348,296732,2272837,9070390,15131442,2698],[16384,250570,44753,77527,143075,151217,85700,3800],[16384,7867580,9383167,2348],[16384,207979,241040,4836],[16384,250570,12357148,13738342,15074993,12463711,15573679,14223863,12553758,13829126,2207300,414],[16384,250570,12357148,13710055,15045346,15081835,13731505,12463711,14230189,12430935,15573525,2551],[16384,15360471,14011506,10084873,15524363,14175393,10396930,14050627,1284],[16384,365288,250570,12889692,12922465,11667883,58943,125212,174770,191387,348889,226021,103142,6424628,5335133,12357148,11233800,10365442,5572656,4630586,404299,437407,15053545,13701858,13738342,4835],[16384,250570,44753,58943,77527,125212,143075,1086186,158305,174770,191387,365287,12889692,12922465,11667883,207979,12357148,11250166,348882,226021,240997,102065,8945899,13738342,13672684,11233800,14213649,470502,15551913,12553758,11201069,15016257,427706,15517106,10365442,5581987,2096]]

def largehintsp43 : List (List ℕ) := [[16384,250570,12889692,12922465,11667883,58882,174770,191387,103142,44753,77527,143075,158305,12357148,10299901,207923,240997,85687,11250166,470502,1418865,4781],[16384,250570,44753,61223,77527,373484,1418857,4564638,4622984,108602,143075,158305,174770,191387,240997,200369,85710,3802],[16384,250570,2133530,15377006,14026871,6073907,13639865,13598802,536114,271859,14976505,1060404,140],[16384,125212,217837,6032570,6171886,1418857,4564638,4622984,6401256,338041,357093,15086318,13731502,14033516,15370359,15016176,250570,2133530,2272837,304929,15176413,6270539,997],[16384,13754910,15623621,15098547,3506],[16384,1086186,13710059,365295,250570,12889692,12922465,11667883,8945899,12357148,11643398,470503,1418865,4564647,4622984,2133530,2272837,304929,13742832,125212,217836,6032570,6401256,338041,15074972,860378,13672684,13750347,15623621,692],[16384,250570,12889692,12922465,11667883,12357148,11250166,3558],[16384,15623621,13755060,15098399,462302,373490,1418857,4564638,13726426,250570,12357148,15007985,12398166,15573315,14223863,13631701,1371681,13787286,4517412,13983923,4624744,1355309,13770898,878272,15065321,15125130,15114938,2133530,2272837,304929,1859],[16384,13710059,1086186,406257,15086323,13731512,13664493,8945899,14123316,9036317,13755029,15623621,15098547,462302,373490,1418857,4564638,250570,12357148,12463711,14230189,15567351,12445392,15065625,12512849,15131467,12709460,15328510,4624692,1140429,13721970,13781642,13771449,12496472,15115080,12553758,15172617,2272837,304968,1859],[16384,250570,12357148,13665967,12398166,14229826,2551],[16384,1086186,8945899,15045364,15081835,15016176,250570,12430935,15573525,365301,12889692,12922465,11667883,12357148,11233800,15557139,471794,14208425,12553758,11201069,13672768,394932,329370,427706,14173614,10365442,5581986,6433908,6391855,296545,2133530,2272837,4630305,2897],[16384,13698742,13721931,15623621,15065627,2941],[16384,15049065,398071,1411926,1442125,1802784,250570,2133530,2272837,304920,13698635,1433928,13787532,13754917,13731404,15623621,15098547,3490],[16384,15078136,15623621,13755060,15098399,413171,347597,9011548,14148237,9003338,9036128,15491734,9350565,9383340,8325348,7121221,3091],[16384,250570,12889692,12922465,11667883,12357148,11250166,3574],[16384,250570,44753,77527,143075,207979,85687,103142,4042942,1934],[16384,7867580,7974138,15442417,357093,2350],[16384,250570,44753,77527,143075,200375,102094,3804],[16384,3409804,3352487,3066],[16384,1118966,15040874,58939,15623621,13755060,13820464,15163961,412644,94974,125212,174770,191387,250570,2133530,2207300,15180192,13829916,8105548,14099438,226044,241002,152317,2656840,2174530,13672708,15009361,862808,229],[16384,2656840,862808,13672673,1672],[16384,58943,1769846,1118966,1802576,1442125,1860278,1827361,250570,2133530,2305607,304921,15086335,13731404,13820471,13795886,15623621,15164359,412644,94974,125212,13697381,2240077,13836859,15173404,2174530,15016197,8978781,463609,373498,160512,174770,191387,240999,217853,8105548,15442928,348843,4837],[16384,1118966,58943,125212,174770,191387,240999,217853,357093,8978781,463609,373498,1422081,404310,15069901,250570,44753,77527,110301,143075,200399,5540913,6032570,6434028,338046,13716249,1139015,13738354,6171886,15086318,1692],[16384,250570,12357148,13731505,12463711,14230189,13697381,15012608,12397157,15573315,2551]]

def largehintsp44 : List (List ℕ) := [[16384,8978781,15078147,15040874,15623621,13722140,1139015,15065460,297730,250570,2272837,2305607,1836759,2133530,3352351,3418740,4041333,4010],[16384,1118966,8978781,250570,44753,58943,77527,463609,373498,1422081,404310,160516,86786,111277,125212,143075,174770,191387,208602,240999,216753,357093,15069901,422654,13716314,13705547,15623621,15049244,1709],[16384,250570,12357148,13705547,15623621,15049244,12445373,14230039,13918639,15256558,12643923,15574138,2551],[16384,15069901,2906],[16384,3409804,3254179,422654,13726470,398087,1411926,1769846,13820307,15158255,1442125,1802784,15081834,250570,2133530,2272837,304920,13731404,15623621,15098547,563],[16384,250570,2133530,13705547,15623621,15049244,845481,13639814,14033374,15370359,6073907,14983354,263666,14942292,536114,1524],[16384,15069901,2841],[16384,6032570,6155482,44752,58882,250570,77527,94984,110301,126687,141738,174770,191387,240999,200399,5540913,6434028,338046,13726473,398090,1411926,13698647,15438507,2133530,2207300,13836702,2272837,304920,15173404,8105216,1008],[16384,15045387,15073641,6032570,6171886,332526,6401256,4565107,15623621,13722140,15065420,250570,12357148,12430935,15573525,14223863,12553758,13829126,4714045,13984731,4581510,15327697,395916,6434028,5572655,2924],[16384,250570,12357148,58882,125155,174770,191387,226060,240999,86781,15045384,12430935,15573525,422654,14223888,3409804,3254179,13726470,398087,44753,77527,141738,208602,102065,5572656,4630586,4032398,438462,15133542,13815625,12545618,965],[16384,3409804,3270576,15262132,422654,3054],[16384,58920,250570,12357148,12430935,15573525,14223863,12643923,13919352,94990,125155,174770,191387,9024261,240981,217853,6032570,12332637,13607032,13631701,536114,271862,14943740,797902,15],[16384,250570,12357148,13631701,831020,13705346,1060404,13738122,1545],[16384,58888,125155,217853,6032570,250570,44753,77527,110301,141738,200399,5581916,6401256,12357148,6171886,5540913,6434028,338046,15086318,14234384,15567351,12693081,15312122,12725851,15344935,14037459,12758622,15377738,14975192,536114,271863,2161],[16384,250570,12357148,14975192,3206691,15261867,13913074,1732130,15163550,13814768,883],[16384,1127181,15053583,174770,191387,9024261,240981,86801,4065168,250570,12357148,3352487,422654,15577874,14223888,12643923,13919352,15256538,15078160,3303350,588],[16384,296816,250570,2133530,2272837,1825],[16384,1418857,4564638,4569],[16384,15158262,15123153,1860278,15114966,4633364,15045397,1425806,15065420,395994,1417604,2777],[16384,94974,127248,174770,191387,217853,8334590,9383167,9341156,7867580,7121199,3096],[16384,250570,12357148,12430935,15573525,14223863,12553758,13829126,15607236,13705754,15623621,13722140,12496472,13771590,12512849,13787978,12529242,13804483,12545618,13820869,12709460,13985020,4886],[16384,250570,12553758,13829126,12357148,13631701,831020,13705346,847391,13721734,1355309,13770898,1371681,13787286,1715759,13803673,1732130,13820060,4517412,13983923,4886],[16384,1417602,4559156,13698723,1425804,13771449,15623621,15115086,250570,2133530,2272837,304941,1924],[16384,250570,12357148,14234393,15567351,14975192,1732130,15163550,13814774,13779660,15053592,847391,15065224,1860278,13771476,1355309,15114388,4633364,1371681,15130775,4517412,15327413,13718298,1409411,13705547,1641]]

def largehintsp45 : List (List ℕ) := [[16384,250570,12357148,12447312,14230039,13705547,15623621,15049244,1418857,13787523,404202,15125225,12512849,15573835,2551],[16384,414491,348947,58882,234263,9024261,3413],[16384,250570,12357148,14975192,1355309,15114388,2133530,2272837,304929,13764419,667178,15016061,13665873,247],[16384,250570,12357148,15577886,14223863,13631701,1355309,13770898,2133530,2272837,304929,15107907,667178,13672572,15009361,249],[16384,250570,12357148,13631701,831020,13705346,1371681,13787286,4517412,13983923,15045397,667178,13672572,15009416,229],[16384,152349,250570,12357148,2656840,862808,13726492,1387097,4633375,14234400,15567351,12398166,15016259,13710080,12430935,15049237,1418857,4564638,12447312,15065625,12512849,15131467,12709460,15328510,4404],[16384,1418865,4564647,15528426,15558066,14208425,13722126,13787967,13985010,404104,4456],[16384,250570,44753,58882,77527,365345,12889692,12922465,11667883,12357148,10070516,11217397,10136056,11282937,10332672,11479553,9024261,11250166,11643398,470356,15045410,11233800,15557139,14208425,11315706,13820861,2133530,11365953,13837315,2207300,15180192,296732,2305607,1795886,15163804,412698,94974,2272837,1419032,15623621,13722140,13787967,13985010,4559321,108600,127248,143075,174770,191387,207979,240981,151247,15065420,1435437,15131022,395914,863023,12553758,11201069,13672768,1125206,11266578,13738666,15081835,1085513,2657],[16384,9024261,13701923,250570,2133530,2207300,13836702,365345,12889692,12922465,11667883,12357148,11233800,14213649,11250166,11643398,470356,15551913,11365953,15180804,296732,2272837,1419032,13721931,15623621,15065627,1435437,13787532,11282937,15131457,395914,1141477,13754737,15098537,15492508,14142806,2305607,1795886,13820314,11315706,15164351,412698,3352351,7120679,7211907,3255110,13902254,11430414,15246454,313319,4074509,5548053,11446782,15295667,5335829,14016981,11512323,15361316,10299901,10365442,437296,13945906,9218079,1187],[16384,250570,2133530,14213649,15551913,11365953,15180804,13829916,2207300,414],[16384,250570,2133530,15557139,14208425,11365953,13837315,15173404,2207300,416],[16384,250570,2133530,13804480,15140676,2305607,15180635,13829916,11365953,1027],[16384,365345,250570,12889692,12922465,11667883,4625188,4653760,12357148,11332109,2133530,2272837,304929,14218023,9024261,11250166,11643398,470356,15551926,15147970,13797188,2305607,11365953,12553758,11201069,15016257,11233800,13710117,15053606,15180804,406237,3944],[16384,363073,250570,12357148,12889692,2569],[16384,1419085,250570,2133530,15541691,11364935,15180804,13829932,2223671,13722018,11217431,15065616,10135420,15131448,395914,283425,11250200,15098537,11643435,15492508,9014614,1093042,1125844,4806],[16384,15551926,15517106,11691432,15508916,10154793,15115068,4630386,365354,250570,2133530,11365953,15180804,13829945,12553758,14222341,12889692,10136101,15131448,4714045,13984731,10332713,15328492,395918,283432,10103321,15098524,10496556,15492499,9014614,1093042,1118918,429562,5581643,4697670,13968343,10349123,15312111,5451336,14001118,10381871,15344929,329777,6400849,6424623,10365482,3197],[16384,15541691,250570,12889692,12922465,371115,15501741,11692614,1460],[16384,15541680,250570,12357148,12889692,371196,11250200,15093080,10109602,15525289,429165,11643435,15486298,10503574,9011859,58943,125212,207973,15476113,346448,226021,240979,103140,5572656,10365020,3207],[16384,11678507,15561516,174770,191387,15512365,250570,12889692,12922465,371115,15534509,11300270,15131461,396074,283432,11267484,15098540,11660719,15492511,9014614,1093074,1125844,4806],[16384,283432,1115805,11207010,250570,44753,61223,77527,108600,141774,174770,191387,151247,2656840,862808,1670],[16384,250570,44753,77527,5581676,108592,143075,174756,240999,151247,15040874,332258,6400888,216772,6434028,2095],[16384,5572656,11495507,15328504,4630586,404299,5548122,10365020,437296,2917],[16384,250570,44753,58909,75488,1769846,13804233,15140686,11305918,15107917,1860278,15164118,412645,94974,283425,9021023,11249256,11636052,125217,141778,174770,191387,240981,151247,11273024,1093084,853507,2648],[16384,250570,44753,58888,75478,1422130,4624857,15107952,1860278,15164118,412662,94974,127248,141778,174770,191387,11273024,241037,151247,283425,4653760,4645560,15328008,396075,863024,1082883,2657]]

def largehintsp46 : List (List ℕ) := [[16384,4653760,1417593,404310,15321899,15107952,4645560,776],[16384,1119027,4633396,1413593,1442125,15107917,15131322,396035,15073831,58909,1802784,1860278,15164118,412644,94974,127248,191387,4912],[16384,1417592,404310,15125290,13722056,15059713,392],[16384,2656840,862808,1655],[16384,283432,9021081,11249309,11636052,15467931,250570,44753,58914,77527,125217,143075,160567,174770,191387,240981,216753,7867580,536114,13606914,6032570,85711,422654,271872,6401256,338035,14943741,8891606,104],[16384,15534509,10299942,111409,207923,4559669,1119032,4625206,4653760,15107952,4645560,15328008,396075,11273024,4587864,1442339,1802784,11242992,15164294,412663,94974,127248,240999,4911],[16384,250570,44753,75478,108600,141753,283425,160567,174770,191387,200399,4625206,1409402,15107917,10126135,3177],[16384,4567866,4633396,1413593,1442125,15107917,15131322,396035,15073831,191387,201520,10126135,3177],[16384,3409804,10282933,15262834,422654,3043],[16384,42471,15504185,15541680,11250200,11643435,9014612,58943,75478,95036,283425,125212,240983,1127227,1418847,4564633,4624857,108602,141740,4653760,15107952,4645560,15328008,396075,1086150,158305,174770,191387,10126135,207977,3791],[16384,15107952,250570,44753,4653760,4645560,15328008,396075,61223,75495,15164294,412663,94974,108602,127248,141738,174770,191387,207979,241040,216772,7867580,2133530,2272837,15180508,13829932,2109002,13606958,13631648,6032570,536114,340587,271866,14943741,1322191,31],[16384,2656840,862808,1418830,4567863,4569],[16384,250570,44753,1413593,58909,75478,15107917,15040901,2133530,2272837,15180508,13829932,3403323,13919184,1769846,1860278,15164118,412661,283425,160575,357143,94990,1433928,15065487,396073,5581642,108592,127248,141738,174770,191387,3791],[16384,283425,11670333,4633406,207979,241040,4559680,1127222,9021081,11249309,108600,15545144,11643435,3412],[16384,42471,463662,365377,1094386,58886,75478,250570,12889692,12922465,11667883,283432,1127162,853507,12357148,11250166,11643398,9014612,406214,15059705,3876481,10070516,10299901,4042603,92046,1418847,4564633,4624744,108602,9350666,125159,143075,158296,174770,191387,207979,241040,3791],[16384,250570,44753,77527,143075,174770,191387,12357148,12889692,10299901,207923,240981,85711,3409804,3206691,13918377,12922465,11667883,217830,6032570,532481,422654,271872,11643398,470356,14943745,3173572,15261756,667178,13672572,847391,13721734,1076768,13754510,1355309,13770898,13787851,4517412,13983923,6073907,14033081,8924725,14131395,8941095,14147781,10006065,14164170,10022440,14180558,11152950,14196943,11169321,14213331,299842,2133530,2272837,1419032,13828255,4630387,4559321,6401256,338035,3049],[16384,3409804,422654,15256564,15221778,15158262,2795416,867],[16384,250570,44753,58914,77527,283432,9021081,11249309,108600,373571,95044,143075,174770,191387,240981,200399,5540913,5254704,14000310,216782,6032570,6401256,338035,15370373,6434028,15344902,7867580,532481,271870,2175],[16384,95044,174770,191387,217853,15125290,15328005,330523,6400812,6039668,3258],[16384,4559321,283428,160575,1119045,4587864,404310,58914,240999,365382,250570,12889692,12922465,11667883,471802,15551996,12357148,11217397,15065616,2941],[16384,250570,2133530,13631648,667178,13672572,847391,13721734,1076768,13754510,1355309,13770898,1371681,13787286,1732130,13820060,3206691,13918377,4517412,13983923,6073907,14033081,8924725,14131395,8941095,14147781,10006065,14164170,10022440,14180558,11152950,14196943,299842,12553758,2305607,1697664,536114,13606914,2272837,1419032,4630305,7104305,8054657,3352351,7120679,4501038,13967535,119623,8325349,6975014,14082240,422160,9021724,283432,4559321,7022828,7087910,1126308,11249309,11643169,470356,15420455,15158298,933],[16384,250570,12357148,12553758,13841224,14230534,15158298,12545618,15573958,363024,12889692,12922465,11667883,15123153,2305607,15623621,13804487,15147858,2321978,15180638,296669,2133530,2272837,11282219,15557441,3596],[16384,250570,12889692,12922465,11667883,14181805,283432,12357148,11250166,11643398,9014612,1094386,1127162,406214,15125320,10136056,15524664,429217,58886,125212,853507,158296,174770,191387,1418847,9006503,9072052,348864,226021,240983,4859],[16384,250570,12357148,12553758,13841224,14230534,463689,13787851,373578,15567376,15158262,12545618,966]]

def largehintsp47 : List (List ℕ) := [[16384,11242839,9014613,1125735,4705],[16384,1418856,4564637,4404],[16384,296781,250570,2133530,2272837,1816],[16384,14191147,11322305,13804369,15623621,15147976,1929],[16384,283419,250570,12357148,12553758,13841224,14230534,15567376,15172617,2223671,15065508,13816651,1860278,13771476,15623621,15147976,15114958,4633364,15607236,15164361,15131344,4714045,15328221,11252557,13779660,1422158,4559156,1451604,13754918,2256440,15098433,11365953,15557636,462168,9021081,11636052,11349583,15541249,299855,2133530,2272837,11298616,14197571,395839,10151730,14164795,10202697,15508474,11667885,856041,2856],[16384,1119056,13816651,13779660,1860278,13771476,15623621,15147976,15114958,1422158,13721987,250570,12357148,12553758,13841224,14230534,15567376,15172617,2223671,15065508,404316,2906],[16384,470518,15552012,13721987,404316,15059802,528],[16384,250570,44753,12889692,12922465,11667883,12357148,11217397,11250166,1127250,58888,77527,10136056,14181174,10070516,15524360,404297,429217,10299901,4074666,92048,10365442,6433966,108596,15557136,462332,11643398,9350666,125159,143075,207923,240983,216772,9014612,2272837,13771449,15623621,15115086,2289209,13837022,2223671,15180196,296667,2133530,9070390,14132017,1140427,15081844,15475344,346472,4837],[16384,250570,2305607,13804369,15623621,15147976,12889692,12922465,11667883,471794,15552012,11365953,15180804,296669,12357148,11250166,15098537,13749731,1802801,2133530,1819],[16384,250570,2305607,13804369,15623621,15147976,15552012,11365953,15180804,296669,2133530,2272837,1419032,15065616,4630305,15607236,15131471,11478249,15328500,4559156,1127250,9021081,1451802,13754918,15098537,9053992,14148396,15492508,3414],[16384,283432,365393,13816651,13841224,1094484,250570,12889692,12922465,11667883,13779660,12357148,10070516,11217397,11250166,10136056,10332672,11643398,463701,1125878,853507,9014612,1418847,13721987,174770,191387,15070035,406214,2867],[16384,250570,44753,58888,77527,143075,1093094,853507,158296,207979,241040,216759,102095,3805],[16384,250570,44753,77527,94974,127248,174770,191387,217853,110301,141738,200399,6032570,12357148,357143,15567367,14975192,536114,14950405,271871,13600252,9972949,14164079,10006065,15507660,10299903,3123],[16384,862808,1092193,1539],[16384,58888,283432,160601,240983,365400,94974,127248,174770,191387,11678551,250570,12889692,12922465,2475],[16384,250570,12357148,11244378,12922465,371190,283432,58888,160601,234328,9014613,1092965,406214,15567371,12512849,15131467,13781802,853507,12447312,15065625,13716263,1418856,387],[16384,250570,12357148,405287,15567371,14975192,1371681,15130775,13781802,853508,12445240,15065625,13716263,1418781,387],[16384,250570,12357148,1119067,373498,283432,62300,240999,152408,2656840,862808,1418830,404310,15567371,12512849,15131467,13781802,4567863,12447312,15065625,12709460,15328510,4624692,12496472,15115080,13767444,697],[16384,250570,2133530,13841224,4653760,2305607,304930,414550,12553758,14230534,471901,15173433,2272837,15114972,13764466,13787833,2289209,15131360,11365953,15557636,11677110,12889692,12922465,371115,396074,62300,240979,152408,283432,1119065,4567863,2903],[16384,283425,62300,471901,240979,152408,4567863,250570,12357148,15567380,14975192,847391,15065224,1371681,15130775,4517412,15327413,1413428,2656840,862808,1614],[16384,2656840,862808,1418830,4567863,404104,15551996,15528426,1458],[16384,250570,44753,58914,77527,108600,143075,3791],[16384,250570,44753,77527,217853,110301,143075,3791],[16384,414550,4633438,250570,12553758,13841224,14230534,365407,12889692,12922465,11667883,94974,127248,283432,12357148,10070516,10136056,10332672,471901,160608,174770,191387,10299901,207923,240979,54114,405287,15551996,1418781,4567905,15528426,1458]]

def largehintsp48 : List (List ℕ) := [[16384,14209891,853508,11216426,13722126,405287,1082886,11249216,470496,15059778,1418781,15131016,13781851,250570,2133530,11365953,13837315,2221623,15180196,296752,2272837,11282219,831],[16384,250570,2133530,2272837,1419032,4630305,404104,4456],[16384,250570,2133530,14209891,11365953,13837315,15173433,2321978,15164254,412698,2256440,15098433,9137727,15492086,9014614,9121358,15475699,346448,62308,241033,4887],[16384,62308,94974,127248,174770,191387,4962],[16384,14209891,250570,12357148,12922465,11577861,14083436,11315706,13820861,12889692,10299901,207923,240979,422759,15158298,11250166,13755046,11659795,14132637,11643398,14149018,299878,2133530,2305607,7120679,15426469,8334375,9350188,11594255,9086761,15492019,9383437,12553758,11627056,9103159,15475639,4269],[16384,14209891,250570,12922465,14198202,15623621,15541698,12938837,14230976,373608,15567281,12357148,14975192,1732130,15163550,62308,240979,422744,13814774,11315763,957],[16384,250570,2133530,14209891,11365953,13837315,152425,283432,1119065,2656840,862808,11216518,13722126,1418830,404310,15059837,2223671,15180196,296752,15131016,13781851,11273023,2272837,1835],[16384,463722,14209891,283432,862808,1092193,1115651,2656840,11249287,363991,4858],[16384,283425,463722,14209891,14198202,15623621,15541698,250570,12938837,14230976,62308,160619,241035,422744,11250209,1093092,1125877,853507,11217440,13722126,12922465,15567281,12357148,14975192,847391,15065224,396071,1732130,15163550,13814774,13779660,11299392,13771586,1355309,15114388,1422158,2856],[16384,283432,463722,365420,1094386,1127162,853507,14209891,250570,12889692,12922465,11667883,14173614,12357148,10070516,13722118,10136056,13787958,11250166,11643398,9014612,406214,12938837,14230976,422747,15125320,1418847,15065480,4564633,10332672,13985002,308069,2809],[16384,1848173,250570,2133530,14975138,1355309,15114388,1715759,15147163,2272837,2305607,304855,1753],[16384,250570,2305607,12357148,12922465,11332109,13804480,11365953,13837315,11299338,13771586,15184750,1848173,2272837,304855,15140573,15107803,719],[16384,14198202,15623621,15541698,1848173,250570,2272837,2305607,304855,373615,11692590,14165427,12922465,12938837,14230976,15567281,12889692,15508919,11667885,11250200,1093075,58886,11643435,9350617,125159,9014612,11266612,13738666,12463711,15082159,280165,1125847,4564633,174731,11659829,14132637,12856928,15476129,346448,7219538,191368,226021,103142,11217431,13722126,12447312,15065625,11479592,13985010,12709460,15328510,395916,13706854,160601,241035,439035,3996],[16384,201444,86781,3802],[16384,9021724,11643169,3412],[16384,4565048,4630586,4404],[16384,7113606,9350096,14067039,15410084,354689,2430],[16384,6032570,6401256,338035,13961382,14026885,13598802,4467920,67],[16384,250570,44753,4559156,58914,77527,111475,160567,174729,226165,242508,185201,93913,141738,200395,3345284,1848173,2272837,2305607,304855,13797215,10169247,14164920,10299942,3123],[16384,9020991,11249216,11636052,1082886,11283932,14197566,297515,1848173,250570,2272837,2305607,1751],[16384,11242839,11283853,14197566,297496,1848173,250570,2272837,2305607,1751],[16384,152433,1848173,250570,2272837,2305607,304855,315784,201444,5540913,2656840,4041795,2013],[16384,4625270,13767444,62327,111475,174729,1848173,13804234,250570,2272837,2305607,304855,3352415,191364,242552,217977,7867580,2133530,13837018,15173420,2109002,14950448,14975138,6032570,536114,340587,271867,13600253,1322191,28],[16384,250570,12357148,14975192,847391,15065224,1355309,15114388,1371681,15130775,1715759,15147163,2633259,15212708,4501038,15311025,4517412,15327413,6073907,15376570,10006065,15507660,11152950,15540433,119674,11244402,9341159,9021724,1125871,4625229,1848173,2272837,2305607,304855,14191128,11643169,11283953,13771582,1904]]

def largehintsp49 : List (List ℕ) := [[16384,11244402,9341159,11643169,11480562,15541491,297496,1848173,250570,2272837,2305607,1751],[16384,1848173,250570,2272837,2305607,304855,15534616,58944,201444,10292275,15501862,15271085,11447372,1202],[16384,1093084,1125869,853507,404288,297732,1848173,250570,2272837,2305607,1751],[16384,250570,12357148,15577979,1848173,2272837,2305607,304855,14223867,13631701,10006065,14164170,11152950,14196943,108602,1355309,13770898,15107952,15303426,127868,174729,1715759,13803673,15147727,3352415,191364,11252605,1371681,13787286,15131322,11285374,15541056,11643435,9014612,58943,201444,10292275,152433,2656840,2763378,3943493,4041795,5540913,321501,4497],[16384,250570,44753,77527,185201,93913,141738,200395,10292275,3345284,1848173,2272837,2305607,304855,15140703,10169247,15508409,2598],[16384,250570,12357148,15577979,1848173,2272837,2305607,304855,14223867,13631701,1715759,13803673,10006065,14164170,847391,13721734,4633471,1371681,13787286,4517412,13983923,4559321,58914,108600,160575,174729,119680,11244402,9341159,9021724,1125871,1693],[16384,9014613,1125735,4564633,4624857,308069,15107952,11242839,15534616,15073960,1453416,552],[16384,6032570,6401256,4565107,4633195,404104,4456],[16384,250570,12357148,15577979,1848173,2272837,2305607,304855,14223867,13631701,4501038,13967535,847391,13721734,1355309,13770898,1371681,13787286,4517412,13983923,11152950,14196943,242562,217985,7867580,536114,13606914,6032570,340867,271866,14943741,4467920,15310917,5254704,14000310,5221588,15343693,5572657,4484294,15327305,395989,4565110,8293566,6204647,6237417,6270539,6073907,14033081,4633095,2696],[16384,1848173,250570,2272837,2306600,15110990,15147727,6270539,15184750,15377172,4524],[16384,250570,2133530,14033682,15370373,6073907,14983354,14942292,536114,1848173,2272837,2306600,304855,271864,13633017,1355309,146],[16384,13775750,13800325,14033813,1848173,304966,15370362,15107917,1318939,14950431,84],[16384,250570,44753,58909,75503,141738,15623621,13787982,13721985,2133530,15040901,2207300,15180192,1848173,2272837,2305607,304855,13829932,4714045,13984731,160575,174797,13804376,15147727,3352415,191364,207964,15131322,15065478,15328008,242508,85711,5467710,14017505,15360783,429197,4041873,1934],[16384,44752,58909,75488,110301,126687,141738,6032570,6204647,6237417,332679,6401256,6434028,5572655,4647048,5400713,5548158,10365060,15119240,1848173,250570,2272837,2305607,304855,13764429,1433928,13721997,13787833,13984518,160575,174733,13804234,2133530,13837018,15173420,15147867,3352415,191364,207921,13697408,15623621,15065627,15131469,4714045,15328221,242508,85711,14017293,5467710,15360994,429197,4041873,1934],[16384,11244402,224991,241376,1414017,9341159,9021724,1125871,1640],[16384,250570,44753,1414020,13697408,58923,75502,127882,141738,13787833,13721985,2133530,2207300,13836702,1848173,2272837,2305607,304855,15173420,2829891,15213516,174733,13804234,15147867,3352415,191364,226185,15623621,15065627,15131469,4714045,15328221,242508,103289,4581449,13984207,160575,208604,85687,6424628,5335133,14016981,5467710,15360994,429179,5572656,5548122,4041873,1934],[16384,103296,6424628,1848173,250570,2272837,2305607,304855,5572656,86781,4032398,5548122,437393,15355003,5335133,471],[16384,11244402,9341159,9021724,1125871,1640],[16384,250570,2133530,15295224,13945996,4025916,13837267,1848173,2272837,2305607,304855,15173420,732],[16384,250570,2133530,15119246,13767502,2272837,13837018,13951734,15289484,4025916,15180757,1848173,2305607,304855,1836],[16384,250570,2133530,1414020,13697408,2207300,13836702,14000906,4625291,338104,15337690,5451336,15180767,1848173,2272837,2305607,304855,1827],[16384,4032398,1414020,3958724,430991,5547966,10299328,10357808,5385359,5581969,13775760,1848173,250570,2272837,2305607,304855,15107917,10136720,15508279,14158375,2133530,15180508,13829932,10202697,1016],[16384,4557451,862875,1125028,11677673,10070689,15507975,11217574,15540751,2477],[16384,58917,160226,217996,6032570,6204647,15607236,13705754,13771136,4997]]

def largehintsp50 : List (List ℕ) := [[16384,4633195,5001],[16384,2656840,862808,1614],[16384,9014613,1125735,1631],[16384,250570,44753,75495,108602,143075,209517,3787],[16384,250570,2133530,1414020,58909,95121,127885,160661,226196,242582,4633495,13775755,1848173,2272837,2305607,304855,15107917,15180508,13829932,185085,3345284,15147727,13797215,856],[16384,15442725,15475501,14125290,1848173,15147727,4980],[16384,250570,2133530,1414020,44753,58909,77527,95121,168856,110299,127885,141738,160661,4622989,209517,226196,242582,184008,8039095,9054904,862875,1125028,1082883,4557451,9021081,9383401,7113606,1848173,8072098,2272837,2305607,304855,11249309,11636052,9350626,354684,14103041,15119257,13764426,13837018,15173418,3345284,13804234,15140701,859],[16384,250570,44753,1414020,58909,13767502,75502,95121,340890,108590,127885,141738,160661,1848173,13804234,2133530,2272837,13837018,2305607,304855,15173411,15147867,3352407,191364,4625291,4555129,15049092,15311307,6270539,15377381,226165,242582,200392,10357813,5385307,5581916,5008],[16384,15111067,1414020,15040901,250570,2133530,2272837,15180508,1848173,2305607,304855,340890,13829923,2174530,13672708,13804376,15147727,6236009,5467710,14017505,10202697,14164984,127885,11349583,14197759,177042,242582,185235,3352407,2948],[16384,6032570,797902,14950415,535767,271862,1525],[16384,2656840,862808,15016165,296529,1848173,250570,2272837,2305607,1751],[16384,58924,291740,160670,191364,226205,119692,8325349,250570,6975014,14082240,7039226,15426025,7219441,420739,3038],[16384,201444,10292275,152433,2656840,2763378,3943493,4041795,1848173,250570,2272837,2305607,304855,315793,5540913,2013],[16384,291740,58882,250570,2133530,2272837,15180508,1848173,2305607,304855,13829916,2207300,13705630,2223671,13722018,13631648,2109002,13606958,2174530,13672708,2240077,13738555,13804376,15147727,3352383,7120715,5467710,14017505,10202697,14164984,15053727,15623621,13787982,4714045,13984731,4625173,108602,15303426,11349583,14197759,127868,191364,218016,8293566,6204647,6235973,6270539,14033892,340587,4615],[16384,250570,2133530,2272837,15180508,291740,1848173,2305607,304855,13829916,10202697,14164984,168865,1411721,15607236,13771596,13705599,15042123,10070689,15507975,11349583,14197759,11217574,15540751,11667885,2174530,13672708,862875,15016165,2240077,13738555,1125028,15081835,1082887,11249258,3558],[16384,1411721,15049092,291739,13698665,1125028,9024231,13738342,250570,2133530,2206375,13836702,1848173,2271929,2305607,304855,15173404,14975138,1060404,15081612,11249258,11217574,14197261,11152950,15540433,11643435,3412],[16384,250570,12357148,14975192,10006065,15507660,11152950,15540433,2477],[16384,250570,12357148,13631701,831020,13705346,1848173,2272837,2305607,304855,1418827,4564568,847391,13721734,1355309,13770898,4630339,1371681,13787286,4517412,13983923,4569],[16384,250570,2272837,14193572,13771582,12553758,15607236,14230979,13837317,1848173,2305607,304855,15173339,13804476,4974],[16384,250570,12357148,11283932,15119266,11316705,11677158,15578022,291740,14223863,13631701,1715759,13803673,58882,127858,158305,177059,103296,15045541,1417604,847391,13721734,1355309,13770898,1848173,2272837,2305607,304855,4630339,1371681,13787286,4517412,13983923,4559321,2104],[16384,250570,12357148,13631701,1715759,13803673,58882,15045541,160670,103296,1417604,15623621,13722140,1355309,13770898,1848173,2272837,2305607,304855,4630339,1371681,13787286,4517412,13983923,4559321,2104],[16384,1094567,250570,12357148,15119266,291740,127858,177059,14234536,15567351,14975192,667178,15016061,1060404,15081612,1543],[16384,250570,12357148,12463711,15573679,1848173,2272837,2305607,304855,14223867,15119266,291740,177059,119720,15045541,2133530,2240077,15180348,13829916,13771482,1419066,2223671,13722018,4630339,2289209,13787870,4714045,13984731,4559321,15303114,15607236,13738674,11244457,14197413,4988],[16384,11244457,15086506,291740,1727]]

def largehintsp51 : List (List ℕ) := [[16384,9341159,11643169,11283953,11316739,11677194,5030],[16384,185201,13800320,1802799,2979],[16384,250570,2133530,13734827,2240077,13836859,291740,1848173,2272837,2305607,304855,15173404,10202697,15508474,10365479,58945,12357148,12463711,14230189,15567351,15119266,127916,2174530,15016197,2664017,158280,177059,103341,5367902,14017128,5467710,15360994,10119729,14181023,10219072,15524861,5548122,10299942,437296,3126],[16384,1848173,250570,12357148,14975192,536114,14950405,271863,13600245,13770780,1355309,15114388,13803558,1715759,15147163,2272837,2305607,304855,1753],[16384,250570,12357148,6032570,1322191,1682641,15578031,14223863,15045541,13631701,12332248,13607032,5021],[16384,250570,12357148,13631701,667178,13672572,1060404,13738122,10006065,14164170,15119266,291740,226224,5035],[16384,1089772,250570,12357148,14234545,291740,15567351,14975192,1060404,15081612,1848173,2272837,2305607,304855,9021029,11249258,11636052,11152950,15540433,14191135,11174205,1125851,831020,15048836,855982,13698569,13721931,847391,15065224,396025,58899,158307,15119266,177059,14124441,1715759,15147163,193396,226224,103281,5572656,4565048,2870],[16384,15119266,291740,226224,13669294,250570,12357148,14234545,15567351,127916,13734834,58882,1081582,158305,177059,103341,5572656,11244455,14189220,11528287,14017830,14975192,5271077,15360184,429197,5548122,10006065,15507660,1848173,2272837,2305607,304855,10299942,10365479,3120],[16384,1414003,1848173,250570,2272837,2305607,304855,13698635,5572656,10348623,13985006,396013,4565048,10070884,517],[16384,250570,44753,77527,185060,93913,143075,3787],[16384,3345284,10169247,13804472,296767,1848173,250570,2272837,2304933,1751],[16384,13775737,13800302,201444,10169450,952],[16384,14160819,250570,2133530,12553758,14234545,13837317,291740,1848173,2272837,2305607,304855,15173404,12357148,15567351,14975192,2633259,15212708,58882,831020,15048836,847391,15065224,1371681,15130775,4517412,15327413,111540,15119266,177059,1715759,15147163,193462,226224,119735,11244402,1060404,15081612,13731434,9341159,9021724,10104328,665],[16384,250570,2133530,13738649,15075007,2240077,15180348,1848173,2272837,2305607,304855,13829916,10202697,1016],[16384,15111078,250570,12496472,840],[16384,250570,12357148,234424,11283853,11316623,11677072,11242839,10104175,291740,14169017,15578042,14223863,9014613,12463711,13738669,1848173,2272837,2305607,304855,15074917,1125735,15049067,1453416,15114792,5029],[16384,1848173,250570,2133530,13631648,1355309,13770898,1060404,13738122,2272837,2305607,304855,15074917,15114792,1715759,13803673,15147570,1753],[16384,1848173,250570,2133530,13841340,2272837,2305607,304855,15173404,14975138,1060404,15081612,13731429,13771300,1355309,15114388,13804079,1715759,15147163,1753],[16384,250570,2305607,2240077,13836859,13771300,15184750,1848173,2272837,304855,15140573,15107803,719],[16384,15524668,1848173,250570,2272837,2305607,304855,429182,15475501,346448,226021,241040,185083,14214574,11297593,15557444,462262,365473,12357148,12922465,11643398,9350666,9383443,8325348,3022],[16384,4565048,4630586,10332229,15528426,404104,5572656,10365020,437407,3233],[16384,250570,2305607,13743038,14131852,1848173,2272837,304855,15468880,15147954,9121358,15180787,13829853,13764313,730],[16384,250570,2133530,2305607,13837144,14099368,1848173,2272837,304855,15436080,8105548,15180784,1834],[16384,365499,250570,12889692,12922465,11667883,12357148,11250166,11643398,9014612,1453560,9088519,1094386,58886,1814022,283581,1127162,1418847,10070516,10136056,14218096,14181805,111552,127858,160601,174729,207979,241040,218037,7867580,8072445,357093,13808578,15111105,9055737,10152457,10299901,10365442,14128063,13743038,652]]

def largehintsp52 : List (List ℕ) := [[16384,250570,2133530,2272837,15180508,1848173,2305607,304855,472003,13829945,11365953,14214147,15551926,11289412,11349583,14197759,15541691,12357148,12922465,371210,2626],[16384,11678660,250570,2133530,15607236,13771596,15184750,1848173,2272837,2305607,304855,472003,13829945,13631648,10006065,14164170,11152950,14196943,11169321,14213331,15561516,12889692,12922465,371115,11283926,15541056,15501741,1076768,13754510,8924725,14131395,8941095,14147781,10022440,14180558,15147727,3352423,191364,168749,10126135,2741],[16384,250570,2133530,13631648,10006065,14164170,11152950,14196943,1848173,1355309,13770898,15119301,2272837,2302807,304855,15140569,472003,15561516,12889692,12922465,371115,11316696,15541182,15501741,1076768,13754510,8941095,14147781,10022440,14180558,1419085,174729,185133,10159033,2975],[16384,250570,2133530,13841350,1848173,2272837,2305607,304855,472003,15173433,14975138,12357148,15565015,11169321,15556820,12889692,12922465,371115,11283926,15119301,1715759,15147163,11315070,14160806,13764313,10126133,13787833,1371681,15130775,396030,14197566,11152950,15540433,11250200,1076768,15098000,13749592,1458731,58946,11643435,8941095,15491271,14142810,9011854,125212,174773,3352415,191364,207977,1450533,9086837,349121,226021,240979,103140,5572656,4630586,2796],[16384,250570,12922465,14198202,15623621,15541698,12938837,14230976,373615,15567281,472003,11282994,11315763,14160826,11692614,1459],[16384,14218184,14128071,250570,2133530,9121358,13837297,1848173,2272837,2305607,304855,12889692,12922465,371115,15173420,13767534,14149008,15623621,15492517,472003,9055701,811],[16384,11670473,15517106,1848173,250570,2133530,10219072,15180797,2272837,2305607,304855,472003,13829945,13771482,15119301,15140569,10175419,15623621,14198209,14165420,15541691,15508911,12357148,12889692,371212,2628],[16384,11670473,15561674,1848173,250570,2272837,2305607,304855,472003,14208438,14173614,2133530,10219072,13837308,15173433,13767534,11691432,14165427,15623621,15508921,373615,10152513,826],[16384,13800395,11322304,14198202,15623621,15541698,373615,472003,2629],[16384,13800395,14218188,250570,2133530,2305607,13837144,1848173,2272837,304855,472003,15173433,11365953,15557636,11677110,12889692,12922465,371115,11316696,14197692,11349583,15541249,11643435,9137727,15492086,14142810,11250200,2256440,15098433,13749592,13771466,15114972,1419085,2223671,15065508,4630386,1861512,13787861,2289209,15131360,4714045,15328221,4559091,58914,111475,174733,12553758,15565832,11282301,14160806,10159032,191391,207978,4697670,15311833,6270539,15377381,226165,240979,119524,9021724,654]]

def largehintsg0 : List (List (List ℕ)) := [largehintsp0,largehintsp1,largehintsp2,largehintsp3,largehintsp4,largehintsp5,largehintsp6,largehintsp7,largehintsp8,largehintsp9,largehintsp10,largehintsp11,largehintsp12,largehintsp13,largehintsp14,largehintsp15]

def largehintsg1 : List (List (List ℕ)) := [largehintsp16,largehintsp17,largehintsp18,largehintsp19,largehintsp20,largehintsp21,largehintsp22,largehintsp23,largehintsp24,largehintsp25,largehintsp26,largehintsp27,largehintsp28,largehintsp29,largehintsp30,largehintsp31]

def largehintsg2 : List (List (List ℕ)) := [largehintsp32,largehintsp33,largehintsp34,largehintsp35,largehintsp36,largehintsp37,largehintsp38,largehintsp39,largehintsp40,largehintsp41,largehintsp42,largehintsp43,largehintsp44,largehintsp45,largehintsp46,largehintsp47]

def largehintsg3 : List (List (List ℕ)) := [largehintsp48,largehintsp49,largehintsp50,largehintsp51,largehintsp52]

def largehints (i : ℕ) : List ℕ := (([largehintsg0,largehintsg1,largehintsg2,largehintsg3].getD (i/384) []).getD (i/24%16) []).getD (i%24) []

def largeBook : Book := ⟨3812,largesource,largelearned,largehints⟩

set_option maxHeartbeats 20000000 in
theorem smallBatch0 : batch false smallBook 0 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem smallBatch24 : batch false smallBook 24 3 = true := by decide +kernel

theorem nosmall (M : Ports false) : False := by
  have h0 := start_ok M smallBook
  have h24 := extend_ok M smallBook 0 24 h0 smallBatch0
  have h27 := extend_ok M smallBook 24 3 h24 smallBatch24
  exact finish_ok M smallBook 26 h27 (by rfl)

set_option maxHeartbeats 20000000 in
theorem largeBatch0 : batch true largeBook 0 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch24 : batch true largeBook 24 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch48 : batch true largeBook 48 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch72 : batch true largeBook 72 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch96 : batch true largeBook 96 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch120 : batch true largeBook 120 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch144 : batch true largeBook 144 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch168 : batch true largeBook 168 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch192 : batch true largeBook 192 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch216 : batch true largeBook 216 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch240 : batch true largeBook 240 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch264 : batch true largeBook 264 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch288 : batch true largeBook 288 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch312 : batch true largeBook 312 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch336 : batch true largeBook 336 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch360 : batch true largeBook 360 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch384 : batch true largeBook 384 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch408 : batch true largeBook 408 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch432 : batch true largeBook 432 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch456 : batch true largeBook 456 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch480 : batch true largeBook 480 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch504 : batch true largeBook 504 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch528 : batch true largeBook 528 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch552 : batch true largeBook 552 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch576 : batch true largeBook 576 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch600 : batch true largeBook 600 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch624 : batch true largeBook 624 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch648 : batch true largeBook 648 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch672 : batch true largeBook 672 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch696 : batch true largeBook 696 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch720 : batch true largeBook 720 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch744 : batch true largeBook 744 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch768 : batch true largeBook 768 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch792 : batch true largeBook 792 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch816 : batch true largeBook 816 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch840 : batch true largeBook 840 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch864 : batch true largeBook 864 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch888 : batch true largeBook 888 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch912 : batch true largeBook 912 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch936 : batch true largeBook 936 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch960 : batch true largeBook 960 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch984 : batch true largeBook 984 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1008 : batch true largeBook 1008 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1032 : batch true largeBook 1032 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1056 : batch true largeBook 1056 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1080 : batch true largeBook 1080 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1104 : batch true largeBook 1104 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1128 : batch true largeBook 1128 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1152 : batch true largeBook 1152 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1176 : batch true largeBook 1176 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1200 : batch true largeBook 1200 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1224 : batch true largeBook 1224 24 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem largeBatch1248 : batch true largeBook 1248 10 = true := by decide +kernel

theorem nolarge (M : Ports true) : False := by
  have h0 := start_ok M largeBook
  have h24 := extend_ok M largeBook 0 24 h0 largeBatch0
  have h48 := extend_ok M largeBook 24 24 h24 largeBatch24
  have h72 := extend_ok M largeBook 48 24 h48 largeBatch48
  have h96 := extend_ok M largeBook 72 24 h72 largeBatch72
  have h120 := extend_ok M largeBook 96 24 h96 largeBatch96
  have h144 := extend_ok M largeBook 120 24 h120 largeBatch120
  have h168 := extend_ok M largeBook 144 24 h144 largeBatch144
  have h192 := extend_ok M largeBook 168 24 h168 largeBatch168
  have h216 := extend_ok M largeBook 192 24 h192 largeBatch192
  have h240 := extend_ok M largeBook 216 24 h216 largeBatch216
  have h264 := extend_ok M largeBook 240 24 h240 largeBatch240
  have h288 := extend_ok M largeBook 264 24 h264 largeBatch264
  have h312 := extend_ok M largeBook 288 24 h288 largeBatch288
  have h336 := extend_ok M largeBook 312 24 h312 largeBatch312
  have h360 := extend_ok M largeBook 336 24 h336 largeBatch336
  have h384 := extend_ok M largeBook 360 24 h360 largeBatch360
  have h408 := extend_ok M largeBook 384 24 h384 largeBatch384
  have h432 := extend_ok M largeBook 408 24 h408 largeBatch408
  have h456 := extend_ok M largeBook 432 24 h432 largeBatch432
  have h480 := extend_ok M largeBook 456 24 h456 largeBatch456
  have h504 := extend_ok M largeBook 480 24 h480 largeBatch480
  have h528 := extend_ok M largeBook 504 24 h504 largeBatch504
  have h552 := extend_ok M largeBook 528 24 h528 largeBatch528
  have h576 := extend_ok M largeBook 552 24 h552 largeBatch552
  have h600 := extend_ok M largeBook 576 24 h576 largeBatch576
  have h624 := extend_ok M largeBook 600 24 h600 largeBatch600
  have h648 := extend_ok M largeBook 624 24 h624 largeBatch624
  have h672 := extend_ok M largeBook 648 24 h648 largeBatch648
  have h696 := extend_ok M largeBook 672 24 h672 largeBatch672
  have h720 := extend_ok M largeBook 696 24 h696 largeBatch696
  have h744 := extend_ok M largeBook 720 24 h720 largeBatch720
  have h768 := extend_ok M largeBook 744 24 h744 largeBatch744
  have h792 := extend_ok M largeBook 768 24 h768 largeBatch768
  have h816 := extend_ok M largeBook 792 24 h792 largeBatch792
  have h840 := extend_ok M largeBook 816 24 h816 largeBatch816
  have h864 := extend_ok M largeBook 840 24 h840 largeBatch840
  have h888 := extend_ok M largeBook 864 24 h864 largeBatch864
  have h912 := extend_ok M largeBook 888 24 h888 largeBatch888
  have h936 := extend_ok M largeBook 912 24 h912 largeBatch912
  have h960 := extend_ok M largeBook 936 24 h936 largeBatch936
  have h984 := extend_ok M largeBook 960 24 h960 largeBatch960
  have h1008 := extend_ok M largeBook 984 24 h984 largeBatch984
  have h1032 := extend_ok M largeBook 1008 24 h1008 largeBatch1008
  have h1056 := extend_ok M largeBook 1032 24 h1032 largeBatch1032
  have h1080 := extend_ok M largeBook 1056 24 h1056 largeBatch1056
  have h1104 := extend_ok M largeBook 1080 24 h1080 largeBatch1080
  have h1128 := extend_ok M largeBook 1104 24 h1104 largeBatch1104
  have h1152 := extend_ok M largeBook 1128 24 h1128 largeBatch1128
  have h1176 := extend_ok M largeBook 1152 24 h1152 largeBatch1152
  have h1200 := extend_ok M largeBook 1176 24 h1176 largeBatch1176
  have h1224 := extend_ok M largeBook 1200 24 h1200 largeBatch1200
  have h1248 := extend_ok M largeBook 1224 24 h1224 largeBatch1224
  have h1258 := extend_ok M largeBook 1248 10 h1248 largeBatch1248
  exact finish_ok M largeBook 1257 h1258 (by rfl)

end PEqualNP.Outside.L_meta_18946

open PEqualNP.Outside.L_meta_18946

theorem PEqualNP.Outside.L_meta_18946 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (25 : ℕ) → (1 : ℕ) ≤ x1.size → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x5 < x1.size, PEqualNP.TopForm.opnd x1 x5 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x5 (1 : Fin (2 : ℕ))) → (∀ x6 < (13 : ℕ) + x1.size, ∃ x8 < x1.size, x6 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).inputs) → x1.output = (13 : ℕ) + x1.size → (∀ (x8 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x8) = Bool.true → ∃ (x10 : Fin (7 : ℕ)) (x11 : Fin (7 : ℕ)), x10 ∈ PEqualNP.CircuitLowerBounds.fanoLines x11 ∧ x8 (Fin.castAdd (7 : ℕ) x10) = Bool.true ∧ x8 (Fin.natAdd (7 : ℕ) x11) = Bool.true) → (∀ (x9 x10 : Fin (7 : ℕ)), x9 ∈ PEqualNP.CircuitLowerBounds.fanoLines x10 → x9 ≠ (0 : Fin (7 : ℕ)) ∨ x10 ≠ (0 : Fin (7 : ℕ)) → x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x9) (Fin.natAdd (7 : ℕ) x10))) = Bool.true) → x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)))) = Bool.false → (11 : ℕ) ≤ {x11 ∈ Finset.range (14 : ℕ) | ∃ x12 < (13 : ℕ) + x1.size, (2 : ℕ) ≤ {x13 ∈ Finset.range x1.size | x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs}.card ∧ (x1.wires (List.ofFn fun (x13 : Fin (14 : ℕ)) => Decidable.decide (↑x13 = x11))).getD x12 Bool.false = Bool.true}.card → False) := by
  intro C hmax hmin ha hd hl ho hu hp hn he
  have hs := dag_strict ha hd
  have hlive : StrictLive 14 (dag C) :=
    ⟨hs,dag_live ha hl,by intro hz; have ht := dag_length C; rw [hz] at ht; simp at ht; omega⟩
  obtain ⟨hc,hupper⟩ := graph_bridge ha hs ho hu hp hn
  obtain ⟨t,⟨M⟩⟩ := make_ports hlive hc hupper (by rwa [dag_elig ha hd]) (by rwa [dag_length])
  cases t
  · exact nosmall M
  · exact nolarge M
