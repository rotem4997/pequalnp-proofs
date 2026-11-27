import Mathlib
import PEqualNP.Defs

/-!
L-meta-4805: a monotone circuit with at most s gates agreeing with g on the rows makes
some cube piece enc2 n s g rows ++ enc2Cube n s k satisfiable

Adapted from lean/PEqualNP/Library/LRAT/Link.lean of the pequalnp-proofs repository
(Apache-2.0), together with the wire helpers of lean/PEqualNP/MetaComplexity/Helpers/Shannon.lean
of the same repository. The formula definitions are those of PEqualNP.Defs.LratEncoding.

The road:
1. A circuit with at most `s` gates gives an abstract model (one operation in AND, OR, TRUE
   and two sources per gate, values on rows) valid on every row.
2. Among valid models, one of least measure is in normal form.
3. A valid model in normal form satisfies every clause of `enc`.
4. The measure also orders the gate keys `(s1, s2, op)` lexicographically by position, so a
   least model has no adjacent independent inversion (swapping the two gates lowers the
   measure) and no adjacent duplicate (the later one becomes padding), which gives `fLex`.
5. The cube of the last gate is read off the model.
-/

namespace PEqualNP.Outside.L_meta_4805

open PEqualNP.Defs.LratEncoding PEqualNP.CircuitLowerBounds

/-! Wire helpers -/

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

/-! The abstract model -/

/-- A model: operations `op j` (0 AND, 1 OR, 2 TRUE), sources `s1 j`, `s2 j`, the output source
`so` and the gate values `w j r`, as a plain product. -/
def Model : Type := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)

def Model.op (M : Model) : ℕ → ℕ := M.1
def Model.s1 (M : Model) : ℕ → ℕ := M.2.1
def Model.s2 (M : Model) : ℕ → ℕ := M.2.2.1
def Model.so (M : Model) : ℕ := M.2.2.2.1
def Model.w (M : Model) : ℕ → ℕ → Bool := M.2.2.2.2

/-- Build a model from its five fields. -/
def mkM (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) : Model := (op, s1, s2, so, w)

/-- The value of source `k` for gate `j` on row `r`. -/
def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

/-- The gate operations. -/
def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

/-- A model with `s` gates computing `g` on the rows satisfying `R`. -/
def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, M.op j < 3) ∧ (∀ j < s, M.s1 j ≤ n + j) ∧ (∀ j < s, M.s2 j ≤ n + j) ∧
    M.so ≤ n + s ∧
    (∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)) ∧
    (∀ r, R r → M.sv n s M.so r = g r)

section validAcc
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem Valid.intro (h1 : ∀ j < s, M.op j < 3) (h2 : ∀ j < s, M.s1 j ≤ n + j)
    (h3 : ∀ j < s, M.s2 j ≤ n + j) (h4 : M.so ≤ n + s)
    (h5 : ∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r))
    (h6 : ∀ r, R r → M.sv n s M.so r = g r) : Valid n s g R M :=
  ⟨h1, h2, h3, h4, h5, h6⟩

theorem Valid.op_lt (h : Valid n s g R M) : ∀ j < s, M.op j < 3 := h.1
theorem Valid.s1_le (h : Valid n s g R M) : ∀ j < s, M.s1 j ≤ n + j := h.2.1
theorem Valid.s2_le (h : Valid n s g R M) : ∀ j < s, M.s2 j ≤ n + j := h.2.2.1
theorem Valid.so_le (h : Valid n s g R M) : M.so ≤ n + s := h.2.2.2.1
theorem Valid.w_eq (h : Valid n s g R M) : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r) := h.2.2.2.2.1
theorem Valid.out_eq (h : Valid n s g R M) : ∀ r, R r → M.sv n s M.so r = g r := h.2.2.2.2.2

end validAcc

/-- Gate `j` is padding: `TRUE` reading `F` twice. -/
def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

/-- The normal form. -/
def NF (n s : ℕ) (M : Model) : Prop :=
  (∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j) ∧
  (∀ j < s, M.op j = 2 → M.pad n j) ∧
  (∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j) ∧
  (∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i) ∧
  (∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j) ∧
  (∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)) ∧
  (0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1))

section nfAcc
variable {n s : ℕ} {M : Model}

theorem NF.pre (h : NF n s M) : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := h.1
theorem NF.padOp (h : NF n s M) : ∀ j < s, M.op j = 2 → M.pad n j := h.2.1
theorem NF.noF (h : NF n s M) : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j :=
  h.2.2.1
theorem NF.noPadRd (h : NF n s M) :
    ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := h.2.2.2.1
theorem NF.ord (h : NF n s M) : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := h.2.2.2.2.1
theorem NF.used (h : NF n s M) : ∀ j, j + 1 < s → ¬ M.pad n j →
    ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j) := h.2.2.2.2.2.1
theorem NF.out (h : NF n s M) : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1) := h.2.2.2.2.2.2

end nfAcc

/-! The valuation of a model -/

open Classical in
/-- What variable `(kd, j, a)` says of a model. -/
noncomputable def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

/-- The valuation of a model (checker variable `v + 1` is variable `v`). -/
noncomputable def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
open Classical in
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

/-- Source `e` (1 or 2) of gate `j`. -/
def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

/-! Clauses of `enc` hold in a valid model in normal form -/

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in
/-- A valid model in normal form satisfies every clause of `enc`. -/
theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

end sound

/-! From a circuit to a model -/

section circuit
open PEqualNP.MetaComplexity

/-- The input of row `r`. -/
def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

/-- A wire index read by gate `j`: an index that does not exist yet becomes `F`. -/
def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

/-- Operation and sources of gate `g` at position `j`: `AND []` becomes padding `(TRUE, F, F)`,
`OR []` becomes `OR F F`, a single input is read twice. -/
def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

/-- Gate `j` of `C`, or `AND []` past the end. -/
def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

/-- The model of a circuit: gates past the end are padding. -/
def ofCirc (n s : ℕ) (C : Circuit) : Model :=
  mkM (fun j => (code n (gateAt C j) j).1) (fun j => (code n (gateAt C j) j).2.1)
    (fun j => (code n (gateAt C j) j).2.2)
    (if C.output < n + C.gates.length then C.output else n + s)
    (fun j r => if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true)

theorem ofCirc_op (n s : ℕ) (C : Circuit) (j : ℕ) :
    (ofCirc n s C).op j = (code n (gateAt C j) j).1 := rfl
theorem ofCirc_s1 (n s : ℕ) (C : Circuit) (j : ℕ) :
    (ofCirc n s C).s1 j = (code n (gateAt C j) j).2.1 := rfl
theorem ofCirc_s2 (n s : ℕ) (C : Circuit) (j : ℕ) :
    (ofCirc n s C).s2 j = (code n (gateAt C j) j).2.2 := rfl
theorem ofCirc_so (n s : ℕ) (C : Circuit) :
    (ofCirc n s C).so = if C.output < n + C.gates.length then C.output else n + s := rfl
theorem ofCirc_w (n s : ℕ) (C : Circuit) (j r : ℕ) :
    (ofCirc n s C).w j r =
      if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true := rfl

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

/-- The wire of gate `j` is its operation on the wires before it. -/
theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc_w, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) := by
  refine Valid.intro (fun j _ => (code_le n _ j).1) (fun j _ => (code_le n _ j).2.1)
    (fun j _ => (code_le n _ j).2.2) (by rw [ofCirc_so]; split_ifs <;> omega) ?_ ?_
  · intro j hj r _
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc_w, ofCirc_op, ofCirc_s1, ofCirc_s2, hjl, hga, code, gfun]
  · intro r hr
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

/-! Moving a gate to the front -/

/-- New index of an old wire other than `n + d` when gate `d` moves to the front. -/
def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

/-- A redirected source of a reader at old position `j > d` (`j = s`: the output). Target
`t = 0`: `F`; `t = 1`: the new padding wire `n`; `t = c + 2`: old source `c`. -/
def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

/-- The value of target `t`. -/
def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

/-- Gate `d` moved to the front as padding, its readers redirected to target `t`. -/
def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model :=
  mkM (fun j => if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j)
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j))
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j))
    (rd n d t s M.so)
    (fun j r => if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r)

section mvEq
variable (n s : ℕ) (M : Model) (d t j : ℕ)

theorem mv_op : (mv n s M d t).op j = if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j :=
  rfl
theorem mv_s1 : (mv n s M d t).s1 j =
    if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j) := rfl
theorem mv_s2 : (mv n s M d t).s2 j =
    if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j) := rfl
theorem mv_so : (mv n s M d t).so = rd n d t s M.so := rfl
theorem mv_w (r : ℕ) : (mv n s M d t).w j r =
    if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r := rfl

end mvEq

/-- Some later gate or the output reads gate `d`. -/
def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

/-- A target is admissible for gate `d`. -/
def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv_w,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv_w,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv_w, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv_w, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) := by
  refine Valid.intro ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mv_op]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  · intro j hj
    simp only [mv_s1]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj
    simp only [mv_s2]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · have := hv.so_le
    simp only [mv_so]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj r hr
    by_cases h0 : j = 0
    · subst h0; simp [mv_op, mv_w, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv_op, mv_s1, mv_s2, mv_w, if_neg h0, if_pos h1, Nat.add_sub_cancel]
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv_op, mv_s1, mv_s2, mv_w, if_neg h0, if_neg h1]
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  · intro r hr
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    rw [mv_so, e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv_op, mv_s1, mv_s2]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv_op, mv_s1, mv_s2, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv_op, mv_s1, mv_s2, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

/-! The measure -/

open Classical in
/-- `1` for a gate that is not padding. -/
noncomputable def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

/-- Weighted count of the gates that are not padding: gate `j` weighs `s - j`. -/
def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

/-- The key of gate `j`: its triple `(s1, s2, op)` as one number. -/
def key (n s : ℕ) (M : Model) (j : ℕ) : ℕ := (M.s1 j * (n + s + 1) + M.s2 j) * 3 + M.op j

/-- The base of the key digits. -/
def bb (n s : ℕ) : ℕ := 3 * (n + s + 1) * (n + s + 1)

/-- The digits `a 0, .., a (m - 1)` read in base `B`, the first one most significant. -/
def ks (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => ks B a m * B + a m

/-- The measure. -/
noncomputable def meas (n s : ℕ) (M : Model) : ℕ :=
  bb n s ^ s * muf s (ind n M) + ks (bb n s) (key n s M) s

theorem ks_lt (B : ℕ) (a : ℕ → ℕ) : ∀ m, (∀ i < m, a i < B) → ks B a m < B ^ m := by
  intro m
  induction m with
  | zero => intro _; simp [ks]
  | succ m ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h m (by omega)
    have h3 : (ks B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h3
    simp only [ks, pow_succ]
    omega

theorem ks_congr (B : ℕ) (a b : ℕ → ℕ) : ∀ m, (∀ i < m, b i = a i) → ks B b m = ks B a m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    simp only [ks]
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

theorem ks_lex (B : ℕ) (a b : ℕ → ℕ) (j : ℕ) (heq : ∀ i < j, b i = a i) (hlt : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → ks B b m < ks B a m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro hj hb
    by_cases hjm : j = m
    · subst hjm
      simp only [ks]
      rw [ks_congr B a b j heq]
      omega
    · have h1 := ih (by omega) (fun i hi => hb i (by omega))
      have h2 := hb m (by omega)
      have h3 : (ks B b m + 1) * B ≤ ks B a m * B := Nat.mul_le_mul_right _ h1
      rw [Nat.add_mul, Nat.one_mul] at h3
      simp only [ks]
      omega

theorem key_cmp {a b o a' b' o' W : ℕ} (hb : b < W) (ho : o < 3)
    (h : a < a' ∨ (a = a' ∧ b < b') ∨ (a = a' ∧ b = b' ∧ o < o')) :
    (a * W + b) * 3 + o < (a' * W + b') * 3 + o' := by
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
  · have h1 : (a + 1) * W ≤ a' * W := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · omega
  · omega

theorem key_lt_bb {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s) : key n s M j < bb n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have h4 : (M.s1 j + 1) * (n + s + 1) ≤ (n + s + 1) * (n + s + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h4
  unfold key bb
  rw [Nat.mul_assoc]
  omega

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ks_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ks (bb n s) (key n s M) s < bb n s ^ s :=
  ks_lt _ _ s fun i hi => key_lt_bb hv hi

open Classical in
theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ks_le hv'
  unfold meas
  have : bb n s ^ s * muf s (ind n (mv n s M d t)) + bb n s ^ s ≤
      bb n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

/-! Swapping the sources of a gate -/

/-- Gate `j` with its two sources swapped. -/
def sw (M : Model) (j : ℕ) : Model :=
  mkM M.op (fun i => if i = j then M.s2 j else M.s1 i)
    (fun i => if i = j then M.s1 j else M.s2 i) M.so M.w

theorem sw_op (M : Model) (j : ℕ) : (sw M j).op = M.op := rfl
theorem sw_s1 (M : Model) (j i : ℕ) : (sw M j).s1 i = if i = j then M.s2 j else M.s1 i := rfl
theorem sw_s2 (M : Model) (j i : ℕ) : (sw M j).s2 i = if i = j then M.s1 j else M.s2 i := rfl
theorem sw_so (M : Model) (j : ℕ) : (sw M j).so = M.so := rfl
theorem sw_w (M : Model) (j : ℕ) : (sw M j).w = M.w := rfl

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) := by
  refine Valid.intro hv.op_lt ?_ ?_ hv.so_le ?_ (fun r hr => hv.out_eq r hr)
  · intro i hi
    simp only [sw_s1]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  · intro i hi
    simp only [sw_s2]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  · intro i hi r hr
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw_w, sw_op, sw_s1, sw_s2]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw_op, sw_s1, sw_s2]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

open Classical in
theorem meas_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ks (bb n s) (key n s (sw M j)) s < ks (bb n s) (key n s M) s := by
    apply ks_lex _ _ _ j _ _ s hj (fun i hi => key_lt_bb (valid_sw hv j) hi)
    · intro i hi
      simp only [key, sw_s1, sw_s2, sw_op, if_neg (show ¬ i = j by omega)]
    · simp only [key, sw_s1, sw_s2, sw_op, if_true]
      have := hv.s1_le j hj
      exact key_cmp (by omega) (hv.op_lt j hj) (Or.inl hlt)
  omega

/-! Exchanging two adjacent independent gates -/

/-- The positions of gates `j` and `j + 1` exchanged. -/
def tau (j i : ℕ) : ℕ := if i = j then j + 1 else if i = j + 1 then j else i

/-- The wires `n + j` and `n + j + 1` exchanged. -/
def pi (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

/-- Gates `j` and `j + 1` exchanged, later readers renumbered. -/
def xc (n : ℕ) (M : Model) (j : ℕ) : Model :=
  mkM (fun i => M.op (tau j i))
    (fun i => if i ≤ j + 1 then M.s1 (tau j i) else pi n j (M.s1 i))
    (fun i => if i ≤ j + 1 then M.s2 (tau j i) else pi n j (M.s2 i))
    (pi n j M.so) (fun i r => M.w (tau j i) r)

section xcs
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem xc_op (i : ℕ) : (xc n M j).op i = M.op (tau j i) := rfl
theorem xc_s1 (i : ℕ) :
    (xc n M j).s1 i = if i ≤ j + 1 then M.s1 (tau j i) else pi n j (M.s1 i) := rfl
theorem xc_s2 (i : ℕ) :
    (xc n M j).s2 i = if i ≤ j + 1 then M.s2 (tau j i) else pi n j (M.s2 i) := rfl
theorem xc_so : (xc n M j).so = pi n j M.so := rfl
theorem xc_w (i r : ℕ) : (xc n M j).w i r = M.w (tau j i) r := rfl

theorem tau_lo {i : ℕ} (h : i < j) : tau j i = i := by unfold tau; split_ifs <;> omega
theorem tau_hi {i : ℕ} (h : j + 1 < i) : tau j i = i := by unfold tau; split_ifs <;> omega
theorem tau_j : tau j j = j + 1 := by simp [tau]
theorem tau_j1 : tau j (j + 1) = j := by simp [tau]

theorem sv_mono (M : Model) {i i' k r : ℕ} (hk : k < n + i) (hii : i ≤ i') :
    M.sv n i k r = M.sv n i' k r := by
  unfold Model.sv; split_ifs <;> first | rfl | omega

theorem xc_sv_lo {i k r : ℕ} (hk : k < n + j) : (xc n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  simp only [xc_w]
  split_ifs <;> first | rfl | omega | (congr 1; unfold tau; split_ifs <;> omega)

theorem xc_sv_hi {i k r : ℕ} (hi : j + 1 < i) (hk : k ≤ n + i) :
    (xc n M j).sv n i (pi n j k) r = M.sv n i k r := by
  unfold pi Model.sv
  simp only [xc_w]
  split_ifs <;> first | rfl | omega | (congr 1; unfold tau; split_ifs <;> omega)

variable (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j) (h3 : M.s1 (j + 1) < n + j)
  (h4 : M.s2 (j + 1) < n + j)
include h1 h2 h3 h4

theorem valid_xc (hv : Valid n s g R M) (hj : j + 1 < s) : Valid n s g R (xc n M j) := by
  refine Valid.intro ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [xc_op]; apply hv.op_lt; unfold tau; split_ifs <;> omega
  · intro i hi; simp only [xc_s1]; split_ifs with hij
    · have := hv.s1_le i hi; unfold tau; split_ifs <;> omega
    · have := hv.s1_le i hi; unfold pi; split_ifs <;> omega
  · intro i hi; simp only [xc_s2]; split_ifs with hij
    · have := hv.s2_le i hi; unfold tau; split_ifs <;> omega
    · have := hv.s2_le i hi; unfold pi; split_ifs <;> omega
  · have := hv.so_le; simp only [xc_so]; unfold pi; split_ifs <;> omega
  · intro i hi r hr
    simp only [xc_op, xc_s1, xc_s2, xc_w]
    by_cases hij : i ≤ j + 1
    · simp only [if_pos hij]
      by_cases a : i = j
      · subst a
        rw [tau_j, xc_sv_lo h3, xc_sv_lo h4, sv_mono M h3 (Nat.le_succ i),
          sv_mono M h4 (Nat.le_succ i)]
        exact hv.w_eq (i + 1) hj r hr
      · by_cases b : i = j + 1
        · subst b
          rw [tau_j1, xc_sv_lo h1, xc_sv_lo h2, ← sv_mono M h1 (Nat.le_succ j),
            ← sv_mono M h2 (Nat.le_succ j)]
          exact hv.w_eq j (by omega) r hr
        · have hl : i < j := by omega
          have e1 := hv.s1_le i hi
          have e2 := hv.s2_le i hi
          rw [tau_lo hl, xc_sv_lo (by omega), xc_sv_lo (by omega)]
          exact hv.w_eq i hi r hr
    · rw [if_neg hij, if_neg hij, tau_hi (by omega), xc_sv_hi (by omega) (hv.s1_le i hi),
        xc_sv_hi (by omega) (hv.s2_le i hi)]
      exact hv.w_eq i hi r hr
  · intro r hr
    rw [xc_so, xc_sv_hi (by omega) hv.so_le]
    exact hv.out_eq r hr

theorem pad_xc (i : ℕ) : (xc n M j).pad n i ↔ M.pad n i := by
  unfold Model.pad
  simp only [xc_op, xc_s1, xc_s2]
  by_cases hij : i ≤ j + 1
  · rw [if_pos hij, if_pos hij]
    by_cases a : i = j
    · subst a; rw [tau_j]
      constructor <;> rintro ⟨_, b, _⟩ <;> omega
    · by_cases b : i = j + 1
      · subst b; rw [tau_j1]
        constructor <;> rintro ⟨_, b, _⟩ <;> omega
      · rw [tau_lo (by omega)]
  · rw [if_neg hij, if_neg hij, tau_hi (by omega)]
    unfold pi
    constructor
    · rintro ⟨a, b, c⟩
      refine ⟨a, ?_, ?_⟩
      · split_ifs at b <;> omega
      · split_ifs at c <;> omega
    · rintro ⟨a, b, c⟩
      refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

open Classical in
theorem meas_xc (hv : Valid n s g R M) (hj : j + 1 < s) (hk : key n s M (j + 1) < key n s M j) :
    meas n s (xc n M j) < meas n s M := by
  have hind : ind n (xc n M j) = ind n M := by
    funext i; simp only [ind, pad_xc h1 h2 h3 h4]
  unfold meas
  rw [hind]
  have : ks (bb n s) (key n s (xc n M j)) s < ks (bb n s) (key n s M) s := by
    apply ks_lex _ _ _ j _ _ s (by omega)
      (fun i hi => key_lt_bb (valid_xc h1 h2 h3 h4 hv hj) hi)
    · intro i hi
      simp only [key, xc_op, xc_s1, xc_s2, if_pos (show i ≤ j + 1 by omega), tau_lo hi]
    · simp only [key, xc_op, xc_s1, xc_s2, if_pos (show j ≤ j + 1 by omega), tau_j]
      exact hk
  omega

end xcs

/-! Trivial gates -/

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

/-- A `TRUE` gate is trivial. -/
theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

/-- A gate one of whose sources is `false` on every row is trivial. -/
theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

/-- A gate one of whose sources is `true` on every row is trivial. -/
theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

/-- A gate reading one source twice is trivial. -/
theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

/-! A least model is in normal form and ordered -/

/-- The order of adjacent independent gates, as `fLex` states it. -/
def LexP (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j ∨
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ M.s2 j < M.s2 (j + 1)) ∨
    (M.s1 j = M.s1 (j + 1) ∧ M.s2 j = M.s2 (j + 1) ∧ M.op j ≠ 1 ∧ M.op (j + 1) ≠ 0)

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexP n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  have hxc : ∀ j, j + 1 < s → M.s1 j < n + j → M.s2 j < n + j → M.s1 (j + 1) < n + j →
      M.s2 (j + 1) < n + j → key n s M (j + 1) < key n s M j → False := by
    intro j hj h1 h2 h3 h4 hk
    exact hmin _ (valid_xc h1 h2 h3 h4 hv hj) (meas_xc h1 h2 h3 h4 hv hj hk)
  have hdup : ∀ j, j + 1 < s → ¬ M.pad n (j + 1) → M.s1 j < n + j → M.s2 j < n + j →
      M.s1 (j + 1) = M.s1 j → M.s2 (j + 1) = M.s2 j → M.op (j + 1) = M.op j → False := by
    intro j hj hnp h1 h2 e1 e2 e3
    refine hmv (j + 1) (n + j + 2) hj (Or.inr (Or.inr ⟨by omega, by omega⟩)) ?_ (Or.inl hnp)
    intro _ r hr
    rw [hv.w_eq (j + 1) hj r hr, e1, e2, e3, ← sv_mono M h1 (Nat.le_succ j),
      ← sv_mono M h2 (Nat.le_succ j), ← hv.w_eq j (by omega) r hr]
    simp only [tval, Model.sv, if_neg (show ¬ (n + j + 2 = 0) by omega),
      if_neg (show ¬ (n + j + 2 = 1) by omega), show n + j + 2 - 2 = n + j by omega,
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
      show n + j - n = j by omega]
  refine ⟨M, hv, ⟨pre, padOp, noF, padRd, ord, ?_, ?_⟩, ?_⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega
  · intro j hj
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨hp, hn1, hn2, c1, c2, c3⟩ := hc
    have hp1 : ¬ M.pad n (j + 1) := fun h => hp (pre j hj h)
    have o1 : M.op j < 2 := by
      have := hv.op_lt j (by omega)
      by_contra hc
      exact hp (padOp j (by omega) (by omega))
    have o2 : M.op (j + 1) < 2 := by
      have := hv.op_lt (j + 1) hj
      by_contra hc
      exact hp1 (padOp (j + 1) hj (by omega))
    have f1 := noF j (by omega) hp
    have f2 := noF (j + 1) hj hp1
    have b1 := hv.s1_le j (by omega)
    have b2 := hv.s2_le j (by omega)
    have b3 := hv.s1_le (j + 1) hj
    have b4 := hv.s2_le (j + 1) hj
    by_cases e : M.s1 (j + 1) = M.s1 j ∧ M.s2 (j + 1) = M.s2 j ∧ M.op (j + 1) = M.op j
    · exact hdup j hj hp1 (by omega) (by omega) e.1 e.2.1 e.2.2
    · apply hxc j hj (by omega) (by omega) (by omega) (by omega)
      unfold key
      apply key_cmp (by omega) (by omega)
      omega

/-! The order clauses and the cube -/

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hl : LexP n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have L := hl j (by omega)
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
  · simp (disch := first | omega | (apply wd_lt1; omega)) only [lexBase, List.cons_append,
      List.nil_append, cs_cons, cs_nil, litVal_P, litVal_Q, v_s1, v_s2, v_op, v_pad, or_false,
      Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq, decide_eq_true_eq, ne_eq]
    by_cases hp : M.pad n j
    · simp [hp]
    · simp only [hp, false_or, or_false] at L ⊢
      omega

theorem s_cube {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hs : 0 < s) {k : ℕ} (e1 : k % (n + s) = M.s1 (s - 1)) (e2 : k / (n + s) = M.op (s - 1)) :
    ∀ c ∈ enc2Cube n s k, ClauseSat (val n s M) c := by
  intro c hc
  have b1 := hv.s1_le (s - 1) (by omega)
  have b2 := hv.op_lt (s - 1) (by omega)
  simp only [enc2Cube, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rw [e1]
    simp (disch := first | omega | (apply wd_lt1; omega)) only [cs_cons, cs_nil, litVal_P,
      v_s1, or_false, beq_self_eq_true]
  · rw [e2]
    simp (disch := first | omega | (apply wd_lt1; omega)) only [cs_cons, cs_nil, litVal_P,
      v_op, or_false, beq_self_eq_true]

end PEqualNP.Outside.L_meta_4805

open PEqualNP.Outside.L_meta_4805 PEqualNP.Defs.LratEncoding

theorem PEqualNP.Outside.L_meta_4805 : ∀ (x1 x2 : ℕ) (x3 : ℕ → Bool) (x4 : List ℕ) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x2 → (∀ x7 ∈ x4, x7 < (2 : ℕ) ^ x1) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ x2 → (∀ x10 ∈ x4, x5.eval (List.ofFn fun (x12 : Fin x1) => x10.testBit ↑x12) = x3 x10) → ∃ x11 < PEqualNP.Defs.LratEncoding.enc2CubeCount x1 x2, PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 x1 x2 x3 x4 ++ PEqualNP.Defs.LratEncoding.enc2Cube x1 x2 x11) := by
  intro n s g rows C hs hrows hmono hsz hev
  have hv := valid_ofCirc n s g (· ∈ rows) C hmono hsz (fun r hr => hev r hr)
  obtain ⟨M, hM, hnf, hlex⟩ := exists_nf ⟨_, hv⟩
  have b1 := hM.s1_le (s - 1) (by omega)
  have b2 := hM.op_lt (s - 1) (by omega)
  have hpos : 0 < n + s := by omega
  have e1 : (M.op (s - 1) * (n + s) + M.s1 (s - 1)) % (n + s) = M.s1 (s - 1) := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : (M.op (s - 1) * (n + s) + M.s1 (s - 1)) / (n + s) = M.op (s - 1) := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hk : M.op (s - 1) * (n + s) + M.s1 (s - 1) < enc2CubeCount n s := by
    have : M.op (s - 1) * (n + s) ≤ 2 * (n + s) := Nat.mul_le_mul_right _ (by omega)
    unfold enc2CubeCount
    omega
  refine ⟨_, hk, val n s M, ?_⟩
  intro c hc
  simp only [enc2, List.mem_append] at hc
  rcases hc with (h | h) | h
  · exact enc_sat hrows hM hnf c h
  · exact s_fLex hM hlex c h
  · exact s_cube hM hs e1 e2 c h
