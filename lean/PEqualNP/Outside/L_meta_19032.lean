import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19032

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Is the operation AND, OR or NOT? -/
def isAONB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false


/-- The all-ones column on `n` inputs. -/
def mask (n : ℕ) : ℕ := 2 ^ (2 ^ n) - 1

theorem testBit_mask {n k : ℕ} (hk : k < 2 ^ n) : (mask n).testBit k = true := by
  simp [mask, Nat.testBit_two_pow_sub_one, hk]


/-- The column of a gate, from the columns of the wires before it (a missing wire is `0`). -/
def gateCol (n : ℕ) (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => cs.getD a 0).foldr (· &&& ·) (mask n)
  | GateOp.or => (g.inputs.map fun a => cs.getD a 0).foldr (· ||| ·) 0
  | GateOp.not => mask n ^^^ (g.inputs.map fun a => cs.getD a 0).headD 0
  | _ => 0

/-- Every gate is AND, OR or NOT. -/
def aonB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op

/-- Columns `cs` and wire values `w` agree at digit `k`. -/
def Agree (k : ℕ) (cs : List ℕ) (w : List Bool) : Prop :=
  cs.length = w.length ∧ ∀ j, (cs.getD j 0).testBit k = w.getD j false

theorem agree_snoc {k : ℕ} {cs : List ℕ} {w : List Bool} {c : ℕ} {v : Bool}
    (h : Agree k cs w) (hv : c.testBit k = v) : Agree k (cs ++ [c]) (w ++ [v]) := by
  refine ⟨by simp [h.1], fun j => ?_⟩
  rcases lt_trichotomy j cs.length with hj | hj | hj
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (h.1 ▸ hj)]
    exact h.2 j
  · subst hj
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ h.1.symm.le]
    simp [h.1, hv]
  · have hl := h.1
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem testBit_foldr_and {k : ℕ} {n : ℕ} (hk : k < 2 ^ n) (l : List ℕ) :
    (l.foldr (· &&& ·) (mask n)).testBit k = (l.map fun c => c.testBit k).all id := by
  induction l with
  | nil => simp [testBit_mask hk]
  | cons c l ih => simp [ih]

theorem testBit_foldr_or {k : ℕ} (l : List ℕ) :
    (l.foldr (· ||| ·) 0).testBit k = (l.map fun c => c.testBit k).any id := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

theorem gateCol_spec {n k : ℕ} (hk : k < 2 ^ n) {cs : List ℕ} {w : List Bool}
    (h : Agree k cs w) (g : Gate) (hg : isAONB g.op = true) :
    (gateCol n g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hmap : ((g.inputs.map fun a => cs.getD a 0).map fun c => c.testBit k)
      = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]; exact List.map_congr_left (fun a _ => h.2 a)
  cases hop : g.op with
  | and => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_and hk, hmap]
  | or => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_or, hmap]
  | not =>
    simp only [gateCol, hop, GateOp.eval]
    rw [Nat.testBit_xor, testBit_mask hk, ← hmap]
    cases g.inputs <;> simp
  | mod m => rw [hop] at hg; simp [isAONB] at hg
  | maj => rw [hop] at hg; simp [isAONB] at hg

theorem agree_foldl {n k : ℕ} (hk : k < 2 ^ n) :
    ∀ (gs : List Gate) (cs : List ℕ) (w : List Bool), (∀ g ∈ gs, isAONB g.op = true) →
      Agree k cs w →
      Agree k (gs.foldl (fun cs g => cs ++ [gateCol n g cs]) cs)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil => intro cs w _ h; exact h
  | cons g gs ih =>
    intro cs w hg h
    exact ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (agree_snoc h (gateCol_spec hk h g (hg g List.mem_cons_self)))


/-- The column of left vertex `j`. -/
def lcol (m : ℕ) : ℕ → ℕ
  | 0 => 2 ^ m - 1
  | j + 1 => 2 ^ m * lcol m j

/-- The column of right vertex `v`, over `n` left vertices. -/
def rcol (m v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ v + 2 ^ m * rcol m v k

/-- The target column of the graph whose rows are `rows` (row `u`, bit `v`). -/
def tcol (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + 2 ^ m * tcol m rs

/-- The input columns on the promise rows: the `n` left vertices, then the `m` right vertices. -/
def inCols (n m : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => lcol m i) ++ List.ofFn (fun j : Fin m => rcol m j n)

/-- The columns of all wires of `C` on the promise rows, with the mask of `2 ^ N` rows. -/
def pcols (N : ℕ) (C : Circuit) (n m : ℕ) : List ℕ :=
  C.gates.foldl (fun cs g => cs ++ [gateCol N g cs]) (inCols n m)

theorem lt_two_pow_of_lt {a b c : ℕ} (h : a < 2 ^ b) (hbc : b ≤ c) : a < 2 ^ c :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hbc)

theorem bit_lcol {m v : ℕ} (hv : v < m) : ∀ (j u : ℕ), (lcol m j).testBit (u * m + v) = decide (u = j) := by
  intro j
  induction j with
  | zero =>
    intro u
    cases u with
    | zero => simp [lcol, hv]
    | succ u =>
      simp only [lcol, Nat.testBit_two_pow_sub_one]
      have : m ≤ (u + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos u)
      simp; omega
  | succ j ih =>
    intro u
    rw [lcol, Nat.testBit_two_pow_mul]
    cases u with
    | zero => simp; omega
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      simp only [ge_iff_le, g, decide_true, Bool.true_and, e, ih u]
      simp

theorem bit_rcol {m v v' : ℕ} (hv : v < m) (hv' : v' < m) :
    ∀ (n u : ℕ), (rcol m v n).testBit (u * m + v') = decide (u < n ∧ v' = v) := by
  intro n
  induction n with
  | zero => intro u; simp [rcol]
  | succ n ih =>
    intro u
    have hlt : 2 ^ v < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hv
    rw [rcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v' ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      by_cases h : v' = v
      · subst h; simp
      · simp only [Nat.succ_pos, true_and, h, decide_false]
        exact decide_eq_false (fun e => h e.symm)
    | succ u =>
      have e : (u + 1) * m + v' - m = u * m + v' := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v' ≥ m := by rw [Nat.succ_mul]; omega
      have ne : v ≠ (u + 1) * m + v' := by rw [Nat.succ_mul]; omega
      simp only [g, decide_true, Bool.true_and, e, ih u, ne, decide_false, Bool.or_false]
      simp

theorem bit_tcol {m v : ℕ} (hv : v < m) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ m) → ∀ u : ℕ,
      (tcol m rows).testBit (u * m + v) = (rows.getD u 0).testBit v := by
  intro rows
  induction rows with
  | nil => intro _ u; simp [tcol]
  | cons r rs ih =>
    intro hr u
    have hr0 : r < 2 ^ m := hr r List.mem_cons_self
    rw [tcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hr0, Nat.testBit_or, Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      simp
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      have hz : r.testBit ((u + 1) * m + v) = false :=
        Nat.testBit_lt_two_pow (lt_two_pow_of_lt hr0 (by rw [Nat.succ_mul]; omega))
      simp only [g, decide_true, Bool.true_and, e, ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) u, hz,
        Bool.or_false, List.getD_cons_succ]

theorem agree_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) :
    Agree (u.val * m + v.val) (inCols n m) (oneEach u v) := by
  refine ⟨by simp [inCols, oneEach], fun j => ?_⟩
  by_cases hj : j < n
  · rw [inCols, oneEach, List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    rw [bit_lcol v.isLt j u.val]
    simp [Fin.ext_iff, eq_comm]
  · by_cases hj2 : j < n + m
    · have h1 : (List.ofFn (fun i : Fin n => lcol m i)).length ≤ j := by simp; omega
      have h2 : (List.ofFn (fun i : Fin n => decide (i = u))).length ≤ j := by simp; omega
      rw [inCols, oneEach, List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      rw [bit_rcol (by omega) v.isLt n u.val]
      simp only [u.isLt, true_and]
      simp [Fin.ext_iff]; omega
    · rw [List.getD_eq_default _ _ (by simp [inCols]; omega), List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp

/-- Soundness: if the output column on the promise rows equals the target column, `C` represents the graph. -/
theorem represents_of_pcols {n m N : ℕ} (hN : n * m ≤ 2 ^ N) (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ m) (hg : aonB C = true)
    (h : ((pcols N C n m).getD C.output 0 == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  intro u v
  have hk : u.val * m + v.val < 2 ^ N := by
    have : u.val * m + v.val < (u.val + 1) * m := by rw [Nat.succ_mul]; omega
    have : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    omega
  have hg' : ∀ g ∈ C.gates, isAONB g.op = true := fun g hg2 => List.all_eq_true.mp hg g hg2
  have hA := agree_foldl hk C.gates _ _ hg' (agree_oneEach u v)
  have := hA.2 C.output
  rw [show C.gates.foldl _ (inCols n m) = pcols N C n m from rfl, beq_iff_eq.mp h,
    bit_tcol v.isLt rows hrows u.val] at this
  exact this.symm



def tab : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

def circ : Circuit :=
  { gates := [
    ⟨GateOp.or, [13, 18]⟩,
    ⟨GateOp.or, [11, 30]⟩,
    ⟨GateOp.or, [10, 64]⟩,
    ⟨GateOp.or, [25, 21]⟩,
    ⟨GateOp.or, [26, 4]⟩,
    ⟨GateOp.or, [5, 20]⟩,
    ⟨GateOp.or, [16, 8]⟩,
    ⟨GateOp.or, [27, 13]⟩,
    ⟨GateOp.or, [0, 17]⟩,
    ⟨GateOp.or, [10, 0]⟩,
    ⟨GateOp.or, [31, 72]⟩,
    ⟨GateOp.or, [24, 27]⟩,
    ⟨GateOp.or, [3, 68]⟩,
    ⟨GateOp.or, [28, 8]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [14, 19]⟩,
    ⟨GateOp.or, [25, 22]⟩,
    ⟨GateOp.or, [13, 26]⟩,
    ⟨GateOp.or, [65, 66]⟩,
    ⟨GateOp.or, [1, 69]⟩,
    ⟨GateOp.or, [9, 65]⟩,
    ⟨GateOp.or, [67, 84]⟩,
    ⟨GateOp.or, [22, 81]⟩,
    ⟨GateOp.or, [12, 71]⟩,
    ⟨GateOp.or, [27, 2]⟩,
    ⟨GateOp.or, [23, 2]⟩,
    ⟨GateOp.or, [15, 9]⟩,
    ⟨GateOp.or, [18, 9]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.or, [64, 88]⟩,
    ⟨GateOp.or, [28, 29]⟩,
    ⟨GateOp.or, [0, 80]⟩,
    ⟨GateOp.or, [20, 66]⟩,
    ⟨GateOp.or, [0, 92]⟩,
    ⟨GateOp.or, [0, 69]⟩,
    ⟨GateOp.or, [26, 11]⟩,
    ⟨GateOp.or, [14, 6]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [13, 4]⟩,
    ⟨GateOp.or, [10, 89]⟩,
    ⟨GateOp.or, [17, 85]⟩,
    ⟨GateOp.or, [24, 101]⟩,
    ⟨GateOp.or, [15, 12]⟩,
    ⟨GateOp.or, [77, 82]⟩,
    ⟨GateOp.or, [15, 23]⟩,
    ⟨GateOp.or, [28, 83]⟩,
    ⟨GateOp.or, [6, 73]⟩,
    ⟨GateOp.or, [78, 90]⟩,
    ⟨GateOp.or, [29, 2]⟩,
    ⟨GateOp.or, [70, 86]⟩,
    ⟨GateOp.or, [6, 107]⟩,
    ⟨GateOp.or, [15, 28]⟩,
    ⟨GateOp.or, [3, 70]⟩,
    ⟨GateOp.or, [29, 96]⟩,
    ⟨GateOp.or, [19, 74]⟩,
    ⟨GateOp.or, [21, 68]⟩,
    ⟨GateOp.or, [24, 104]⟩,
    ⟨GateOp.or, [25, 106]⟩,
    ⟨GateOp.or, [24, 79]⟩,
    ⟨GateOp.or, [16, 94]⟩,
    ⟨GateOp.or, [7, 95]⟩,
    ⟨GateOp.or, [43, 58]⟩,
    ⟨GateOp.or, [60, 45]⟩,
    ⟨GateOp.or, [40, 41]⟩,
    ⟨GateOp.or, [59, 39]⟩,
    ⟨GateOp.or, [54, 47]⟩,
    ⟨GateOp.or, [55, 61]⟩,
    ⟨GateOp.or, [39, 62]⟩,
    ⟨GateOp.or, [52, 36]⟩,
    ⟨GateOp.or, [52, 37]⟩,
    ⟨GateOp.or, [63, 125]⟩,
    ⟨GateOp.or, [33, 57]⟩,
    ⟨GateOp.or, [48, 32]⟩,
    ⟨GateOp.or, [62, 126]⟩,
    ⟨GateOp.or, [55, 34]⟩,
    ⟨GateOp.or, [33, 58]⟩,
    ⟨GateOp.or, [46, 44]⟩,
    ⟨GateOp.or, [60, 56]⟩,
    ⟨GateOp.or, [34, 35]⟩,
    ⟨GateOp.or, [35, 132]⟩,
    ⟨GateOp.or, [49, 134]⟩,
    ⟨GateOp.or, [41, 128]⟩,
    ⟨GateOp.or, [47, 37]⟩,
    ⟨GateOp.or, [61, 129]⟩,
    ⟨GateOp.or, [48, 131]⟩,
    ⟨GateOp.or, [42, 127]⟩,
    ⟨GateOp.or, [48, 59]⟩,
    ⟨GateOp.or, [35, 146]⟩,
    ⟨GateOp.or, [54, 53]⟩,
    ⟨GateOp.or, [46, 54]⟩,
    ⟨GateOp.or, [137, 140]⟩,
    ⟨GateOp.or, [53, 38]⟩,
    ⟨GateOp.or, [138, 148]⟩,
    ⟨GateOp.or, [60, 37]⟩,
    ⟨GateOp.or, [45, 43]⟩,
    ⟨GateOp.or, [125, 153]⟩,
    ⟨GateOp.or, [136, 152]⟩,
    ⟨GateOp.or, [53, 131]⟩,
    ⟨GateOp.or, [43, 147]⟩,
    ⟨GateOp.or, [59, 51]⟩,
    ⟨GateOp.or, [42, 130]⟩,
    ⟨GateOp.or, [55, 44]⟩,
    ⟨GateOp.or, [42, 143]⟩,
    ⟨GateOp.or, [63, 130]⟩,
    ⟨GateOp.or, [36, 53]⟩,
    ⟨GateOp.or, [47, 139]⟩,
    ⟨GateOp.or, [51, 36]⟩,
    ⟨GateOp.or, [40, 150]⟩,
    ⟨GateOp.or, [132, 165]⟩,
    ⟨GateOp.or, [133, 154]⟩,
    ⟨GateOp.or, [51, 135]⟩,
    ⟨GateOp.or, [62, 142]⟩,
    ⟨GateOp.or, [45, 145]⟩,
    ⟨GateOp.or, [133, 163]⟩,
    ⟨GateOp.or, [33, 159]⟩,
    ⟨GateOp.or, [40, 32]⟩,
    ⟨GateOp.or, [57, 164]⟩,
    ⟨GateOp.or, [141, 143]⟩,
    ⟨GateOp.or, [39, 180]⟩,
    ⟨GateOp.or, [45, 46]⟩,
    ⟨GateOp.or, [127, 140]⟩,
    ⟨GateOp.or, [60, 54]⟩,
    ⟨GateOp.or, [135, 175]⟩,
    ⟨GateOp.or, [145, 160]⟩,
    ⟨GateOp.or, [128, 130]⟩,
    ⟨GateOp.or, [51, 156]⟩,
    ⟨GateOp.or, [170, 176]⟩,
    ⟨GateOp.or, [151, 188]⟩,
    ⟨GateOp.or, [42, 138]⟩,
    ⟨GateOp.or, [42, 44]⟩,
    ⟨GateOp.or, [50, 41]⟩,
    ⟨GateOp.or, [144, 149]⟩,
    ⟨GateOp.or, [137, 195]⟩,
    ⟨GateOp.or, [148, 169]⟩,
    ⟨GateOp.or, [36, 147]⟩,
    ⟨GateOp.or, [50, 33]⟩,
    ⟨GateOp.or, [62, 136]⟩,
    ⟨GateOp.or, [184, 189]⟩,
    ⟨GateOp.or, [173, 179]⟩,
    ⟨GateOp.or, [157, 168]⟩,
    ⟨GateOp.or, [32, 127]⟩,
    ⟨GateOp.or, [158, 200]⟩,
    ⟨GateOp.or, [141, 142]⟩,
    ⟨GateOp.or, [52, 126]⟩,
    ⟨GateOp.or, [193, 199]⟩,
    ⟨GateOp.or, [50, 60]⟩,
    ⟨GateOp.or, [129, 201]⟩,
    ⟨GateOp.or, [34, 161]⟩,
    ⟨GateOp.or, [48, 38]⟩,
    ⟨GateOp.or, [155, 172]⟩,
    ⟨GateOp.and, [15, 171]⟩,
    ⟨GateOp.and, [108, 209]⟩,
    ⟨GateOp.and, [1, 206]⟩,
    ⟨GateOp.and, [121, 207]⟩,
    ⟨GateOp.and, [115, 186]⟩,
    ⟨GateOp.and, [111, 178]⟩,
    ⟨GateOp.and, [31, 185]⟩,
    ⟨GateOp.and, [119, 146]⟩,
    ⟨GateOp.and, [122, 204]⟩,
    ⟨GateOp.and, [6, 58]⟩,
    ⟨GateOp.and, [75, 191]⟩,
    ⟨GateOp.and, [76, 181]⟩,
    ⟨GateOp.and, [123, 182]⟩,
    ⟨GateOp.and, [100, 192]⟩,
    ⟨GateOp.and, [97, 174]⟩,
    ⟨GateOp.and, [112, 144]⟩,
    ⟨GateOp.and, [103, 197]⟩,
    ⟨GateOp.and, [110, 202]⟩,
    ⟨GateOp.and, [93, 212]⟩,
    ⟨GateOp.and, [105, 205]⟩,
    ⟨GateOp.and, [114, 162]⟩,
    ⟨GateOp.and, [99, 139]⟩,
    ⟨GateOp.and, [124, 208]⟩,
    ⟨GateOp.and, [91, 196]⟩,
    ⟨GateOp.and, [98, 167]⟩,
    ⟨GateOp.and, [113, 211]⟩,
    ⟨GateOp.and, [117, 194]⟩,
    ⟨GateOp.and, [102, 187]⟩,
    ⟨GateOp.and, [118, 213]⟩,
    ⟨GateOp.and, [116, 177]⟩,
    ⟨GateOp.and, [67, 210]⟩,
    ⟨GateOp.and, [87, 198]⟩,
    ⟨GateOp.and, [19, 183]⟩,
    ⟨GateOp.and, [14, 203]⟩,
    ⟨GateOp.and, [109, 190]⟩,
    ⟨GateOp.and, [120, 166]⟩,
    ⟨GateOp.or, [214, 215]⟩,
    ⟨GateOp.or, [216, 217]⟩,
    ⟨GateOp.or, [218, 219]⟩,
    ⟨GateOp.or, [220, 221]⟩,
    ⟨GateOp.or, [222, 223]⟩,
    ⟨GateOp.or, [224, 225]⟩,
    ⟨GateOp.or, [226, 227]⟩,
    ⟨GateOp.or, [228, 229]⟩,
    ⟨GateOp.or, [230, 231]⟩,
    ⟨GateOp.or, [232, 233]⟩,
    ⟨GateOp.or, [234, 235]⟩,
    ⟨GateOp.or, [236, 237]⟩,
    ⟨GateOp.or, [238, 239]⟩,
    ⟨GateOp.or, [240, 241]⟩,
    ⟨GateOp.or, [242, 243]⟩,
    ⟨GateOp.or, [244, 245]⟩,
    ⟨GateOp.or, [246, 247]⟩,
    ⟨GateOp.or, [248, 249]⟩,
    ⟨GateOp.or, [250, 251]⟩,
    ⟨GateOp.or, [252, 253]⟩,
    ⟨GateOp.or, [254, 255]⟩,
    ⟨GateOp.or, [256, 257]⟩,
    ⟨GateOp.or, [258, 259]⟩,
    ⟨GateOp.or, [260, 261]⟩,
    ⟨GateOp.or, [262, 263]⟩,
    ⟨GateOp.or, [264, 265]⟩,
    ⟨GateOp.or, [266, 267]⟩,
    ⟨GateOp.or, [268, 269]⟩,
    ⟨GateOp.or, [270, 271]⟩,
    ⟨GateOp.or, [272, 273]⟩,
    ⟨GateOp.or, [274, 275]⟩,
    ⟨GateOp.or, [277, 278]⟩,
    ⟨GateOp.or, [279, 280]⟩,
    ⟨GateOp.or, [281, 282]⟩,
    ⟨GateOp.or, [283, 276]⟩],
    output := 284 }

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

theorem op_mem : ∀ o : GateOp, okOp o = true →
    o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
  | GateOp.and, _ => by simp
  | GateOp.or, _ => by simp
  | GateOp.not, _ => by simp
  | GateOp.mod _, h => by simp [okOp] at h
  | GateOp.maj, h => by simp [okOp] at h

theorem all_ok : circ.gates.all (fun g => okOp g.op && decide (g.inputs.length ≤ 2)) = true := by
  decide +kernel

theorem fan : FanInTwo circ := by
  intro g hg
  have h := List.all_eq_true.mp all_ok g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨op_mem _ h.1, h.2⟩

theorem size_le : circ.size ≤ 221 := by decide +kernel

theorem hrows : ∀ r ∈ tab, r < 2 ^ 32 := by decide +kernel

theorem hg : aonB circ = true := by decide +kernel

theorem hcol : ((pcols 10 circ 32 32).getD circ.output 0 == tcol 32 tab) = true := by decide +kernel

theorem rep : Represents (fun (u : Fin 32) (v : Fin 32) => (tab.getD u.val 0).testBit v.val) circ :=
  represents_of_pcols (n := 32) (m := 32) (N := 10) (by norm_num) circ tab hrows hg hcol

end PEqualNP.Outside.L_meta_19032

theorem PEqualNP.Outside.L_meta_19032 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 224 ∧ PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_19032.circ, PEqualNP.Outside.L_meta_19032.fan, le_trans PEqualNP.Outside.L_meta_19032.size_le (by norm_num), PEqualNP.Outside.L_meta_19032.rep⟩
