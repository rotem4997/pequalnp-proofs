import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9023

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp only [run, Circuit.wires, List.foldl_append]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem run_read (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)])).getD i false = _
    rw [ih _ (by simp only [List.length_append]; omega), List.getD_append _ _ _ _ hi]

private theorem read_tail (a t : List Bool) (i : ℕ) :
    (a ++ t).getD (a.length + i) false = t.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

private theorem read_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp

private theorem mono_append {gs hs : List Gate}
    (hg : Monotone2 (⟨gs, 0⟩ : Circuit)) (hh : Monotone2 (⟨hs, 0⟩ : Circuit)) :
    Monotone2 (⟨gs ++ hs, 0⟩ : Circuit) := by
  intro g h
  exact (List.mem_append.mp h).elim (hg g) (hh g)

private def orGate (a b : ℕ) : Gate := ⟨.or, [a, b]⟩

private def chain (base acc : ℕ) : List ℕ → List Gate
  | [] => []
  | a :: as => orGate acc a :: chain (base + 1) base as

private def chainWire (base acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: as => base + as.length

private theorem chain_length (base acc : ℕ) (as : List ℕ) :
    (chain base acc as).length = as.length := by
  induction as generalizing base acc with
  | nil => rfl
  | cons a as ih => simp [chain, ih]

private theorem chain_mono (base acc : ℕ) (as : List ℕ) :
    Monotone2 (⟨chain base acc as, 0⟩ : Circuit) := by
  induction as generalizing base acc with
  | nil => simp [chain, Monotone2]
  | cons a as ih =>
    apply mono_append (gs := [orGate acc a]) (hs := chain (base + 1) base as)
    · simp [Monotone2, orGate]
    · exact ih _ _

private theorem chainWire_cons (base acc a : ℕ) (as : List ℕ) :
    chainWire base acc (a :: as) = chainWire (base + 1) base as := by
  cases as <;> simp [chainWire, Nat.add_comm, Nat.add_left_comm]

private theorem chainWire_lt (base acc : ℕ) (as : List ℕ) (hacc : acc < base) :
    chainWire base acc as < base + as.length := by
  cases as <;> simp [chainWire, hacc]

private theorem chain_value (x : List Bool) (acc : ℕ) (as : List ℕ)
    (ha : ∀ a ∈ as, a < x.length) :
    (run (chain x.length acc as) x).getD (chainWire x.length acc as) false =
      (x.getD acc false || as.any (fun a => x.getD a false)) := by
  induction as generalizing x acc with
  | nil => simp [run, Circuit.wires, chain, chainWire]
  | cons a as ih =>
    let value := x.getD acc false || x.getD a false
    let y := x ++ [value]
    have hlen : y.length = x.length + 1 := by simp [y]
    change (run ([orGate acc a] ++ chain (x.length + 1) x.length as) x).getD _ false = _
    rw [run_append, show run [orGate acc a] x = y by simp [run, Circuit.wires, orGate, GateOp.eval, y, value],
      chainWire_cons, ← hlen]
    rw [ih y x.length (fun j hj => by
      have := ha j (List.mem_cons_of_mem _ hj)
      omega)]
    have hv : y.getD x.length false = value := by simp [y]
    have hany : as.any (fun j => y.getD j false) = as.any (fun j => x.getD j false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      apply exists_congr
      intro j
      apply and_congr_right
      intro hj
      rw [show y.getD j false = x.getD j false from
        List.getD_append _ _ _ _ (ha j (List.mem_cons_of_mem _ hj))]
    rw [hv, hany, List.any_cons]
    exact Bool.or_assoc _ _ _

/-- Each task is the list of input wires for one OR. Its first wire seeds the chain. -/
private def batch (base : ℕ) : List (List ℕ) → List Gate
  | [] => []
  | as :: rs => chain base (as.headD 0) as.tail ++ batch (base + as.tail.length) rs

private def batchWire (base : ℕ) : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | as :: _, 0 => chainWire base (as.headD 0) as.tail
  | as :: rs, i + 1 => batchWire (base + as.tail.length) rs i

private theorem batch_length (base : ℕ) (rs : List (List ℕ)) :
    (batch base rs).length = (rs.map fun as => as.tail.length).sum := by
  induction rs generalizing base with
  | nil => rfl
  | cons as rs ih => simp [batch, chain_length, ih]

private theorem batch_mono (base : ℕ) (rs : List (List ℕ)) :
    Monotone2 (⟨batch base rs, 0⟩ : Circuit) := by
  induction rs generalizing base with
  | nil => simp [batch, Monotone2]
  | cons as rs ih => exact mono_append (chain_mono _ _ _) (ih _)

private theorem batch_spec (rs : List (List ℕ)) (base i : ℕ) (hi : i < rs.length)
    (hok : ∀ as ∈ rs, as ≠ [] ∧ ∀ j ∈ as, j < base) :
    batchWire base rs i < base + (batch base rs).length ∧
      ∀ x : List Bool, x.length = base →
        (run (batch base rs) x).getD (batchWire base rs i) false =
          rs[i].any (fun j => x.getD j false) := by
  induction rs generalizing base i with
  | nil => simp at hi
  | cons as rs ih =>
    obtain ⟨hne, hvalid⟩ := hok as (by simp)
    cases as with
    | nil => exact (hne rfl).elim
    | cons a as =>
      let gs := chain base a as
      let hs := batch (base + as.length) rs
      have hg : gs.length = as.length := chain_length _ _ _
      have hd : batch base ((a :: as) :: rs) = gs ++ hs := rfl
      have htail (j : ℕ) (hj : j ∈ as) : j < base := hvalid j (List.mem_cons_of_mem _ hj)
      cases i with
      | zero =>
        have hw : chainWire base a as < base + gs.length := by
          rw [hg]
          exact chainWire_lt _ _ _ (hvalid a (by simp))
        refine ⟨by rw [hd, List.length_append]; change chainWire base a as < _; omega, ?_⟩
        intro x hx
        have hl : (run gs x).length = base + gs.length := by rw [run_length, hx]
        rw [hd, run_append]
        change (run hs (run gs x)).getD (chainWire base a as) false =
          (a :: as).any (fun j => x.getD j false)
        rw [run_read hs _ (hl ▸ hw)]
        simpa only [gs, hx, List.any_cons] using
          chain_value x a as (fun j hj => hx ▸ htail j hj)
      | succ i =>
        obtain ⟨hw, he⟩ := ih (base + as.length) i (by simpa using hi) (fun bs hb => by
          obtain ⟨hn, hb'⟩ := hok bs (List.mem_cons_of_mem _ hb)
          exact ⟨hn, fun j hj => Nat.lt_of_lt_of_le (hb' j hj) (Nat.le_add_right _ _)⟩)
        refine ⟨by simpa only [hd, List.length_append, hg, batchWire, List.tail_cons,
          Nat.add_assoc, hs] using hw, ?_⟩
        intro x hx
        have hl : (run gs x).length = base + as.length := by rw [run_length, hx, hg]
        rw [hd, run_append]
        change (run hs (run gs x)).getD (batchWire (base + as.length) rs i) false = _
        rw [he _ hl, List.getElem_cons_succ]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        apply exists_congr
        intro j
        apply and_congr_right
        intro hj
        rw [run_read gs x (hx ▸ (hok _ (List.mem_cons_of_mem _ (List.getElem_mem _))).2 j hj)]

private theorem group_length {m n : ℕ} (base : ℕ) (f : Fin n → Fin m → ℕ) :
    (batch base (List.ofFn fun i => List.ofFn (f i))).length = n * (m - 1) := by
  rw [batch_length]
  have hmap : (List.ofFn (fun i => List.ofFn (f i))).map (fun as => as.tail.length) =
      List.replicate n (m - 1) := by
    rw [List.map_ofFn, ← List.ofFn_const]
    congr 1
    funext i
    simp
  rw [hmap, List.sum_replicate, Nat.nsmul_eq_mul]

private theorem buildGroups {m n : ℕ} (base : ℕ) (hm : 0 < m) (f : Fin n → Fin m → ℕ)
    (hf : ∀ i j, f i j < base) :
    ∃ (gs : List Gate) (w : Fin n → ℕ), Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length = n * (m - 1) ∧ (∀ i, w i < base + gs.length) ∧
      ∀ (x : List Bool), x.length = base → ∀ i,
        (run gs x).getD (w i) false = true ↔ ∃ j, x.getD (f i j) false = true := by
  let rs := List.ofFn fun i => List.ofFn (f i)
  have hok : ∀ as ∈ rs, as ≠ [] ∧ ∀ j ∈ as, j < base := by
    intro as ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    refine ⟨?_, ?_⟩
    · intro h
      have hlen := congrArg List.length h
      simp [Nat.ne_of_gt hm] at hlen
    · intro j hj
      obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hj
      exact hf i r
  have hspec (i : Fin n) := batch_spec rs base i.val (by simp [rs]) hok
  refine ⟨batch base rs, fun i => batchWire base rs i.val, batch_mono _ _, group_length base f,
    fun i => (hspec i).1, ?_⟩
  intro x hx i
  rw [(hspec i).2 x hx, List.any_eq_true]
  simp only [rs, List.getElem_ofFn, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨_, ⟨j, rfl⟩, hj⟩

private def literalTask (n : ℕ) (f : ℕ → ℕ) (i : ℕ) (b : Bool) : List ℕ :=
  ((List.range n).filter fun j => decide (j.testBit i = b)).map f

private def bitTasks (n : ℕ) (f : ℕ → ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | i :: is => literalTask n f i false :: literalTask n f i true :: bitTasks n f is

private theorem bitTasks_length (n : ℕ) (f : ℕ → ℕ) (is : List ℕ) :
    (bitTasks n f is).length = 2 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [bitTasks, List.length_cons, ih]; omega

private theorem bitTasks_get (n : ℕ) (f : ℕ → ℕ) (is : List ℕ) (i : ℕ)
    (hi : i < is.length) (b : Bool) :
    (bitTasks n f is)[2 * i + b.toNat]'(by rw [bitTasks_length]; cases b <;> simp <;> omega) =
      literalTask n f is[i] b := by
  induction is generalizing i with
  | nil => simp at hi
  | cons j is ih =>
    cases i with
    | zero => cases b <;> rfl
    | succ i =>
      have h : i < is.length := Nat.lt_of_succ_lt_succ hi
      have hs : 2 * (i + 1) + b.toNat = (2 * i + b.toNat) + 1 + 1 := by omega
      rw [getElem_congr_idx hs]
      simpa only [bitTasks, List.getElem_cons_succ] using ih i h

private theorem bitTasks_bound (n : ℕ) (f : ℕ → ℕ) (is : List ℕ) :
    ((bitTasks n f is).map fun as => as.tail.length).sum ≤ is.length * n := by
  induction is with
  | nil => simp [bitTasks]
  | cons i is ih =>
    have hp : (literalTask n f i false).length + (literalTask n f i true).length = n := by
      have hf : (fun j : ℕ => decide (j.testBit i = false)) = (fun j => !j.testBit i) := by
        funext j
        cases j.testBit i <;> rfl
      simp only [literalTask, List.length_map, hf, Bool.decide_eq_true]
      rw [Nat.add_comm, ← List.length_eq_length_filter_add, List.length_range]
    simp only [bitTasks, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul,
      List.length_tail] at *
    omega

private theorem buildBits (d base : ℕ) (f : ℕ → ℕ) (hf : ∀ j < 2 ^ d, f j < base) :
    ∃ (gs : List Gate) (w : Fin d → Bool → ℕ), Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length ≤ d * 2 ^ d ∧ (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : ℕ), x.length = base → u < 2 ^ d →
        (∀ j < 2 ^ d, x.getD (f j) false = decide (j = u)) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.testBit i = b) := by
  let n : ℕ := 2 ^ d
  let rs := bitTasks n f (List.range d)
  have hmem (as : List ℕ) (ha : as ∈ rs) : ∃ i < d, ∃ b, as = literalTask n f i b := by
    have haux (is : List ℕ) (h : as ∈ bitTasks n f is) :
        ∃ i ∈ is, ∃ b, as = literalTask n f i b := by
      induction is with
      | nil => simp [bitTasks] at h
      | cons i is ih =>
        rcases List.mem_cons.mp h with h | h
        · exact ⟨i, by simp, false, h⟩
        rcases List.mem_cons.mp h with h | h
        · exact ⟨i, by simp, true, h⟩
        obtain ⟨j, hj, b, hb⟩ := ih h
        exact ⟨j, List.mem_cons_of_mem _ hj, b, hb⟩
    simpa only [List.mem_range] using haux (List.range d) ha
  have hok : ∀ as ∈ rs, as ≠ [] ∧ ∀ j ∈ as, j < base := by
    intro as ha
    obtain ⟨i, hi, b, rfl⟩ := hmem as ha
    have hnon : ∃ j < n, j.testBit i = b := by
      cases b
      · exact ⟨0, Nat.two_pow_pos _, by simp⟩
      · exact ⟨2 ^ i, Nat.pow_lt_pow_right (by decide) hi, by simp⟩
    obtain ⟨j, hj, hb⟩ := hnon
    have hin : f j ∈ literalTask n f i b :=
      List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true hb⟩, rfl⟩
    refine ⟨fun he => by simp [he] at hin, ?_⟩
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact hf _ (List.mem_range.mp (List.mem_filter.mp hq).1)
  have hspec (i : Fin d) (b : Bool) :=
    batch_spec rs base (2 * i.val + b.toNat) (by
      have hi := i.isLt
      simp only [rs, bitTasks_length, List.length_range]
      have hb : b.toNat < 2 := by cases b <;> decide
      omega) hok
  refine ⟨batch base rs, fun i b => batchWire base rs (2 * i.val + b.toNat), batch_mono _ _,
    ?_, fun i b => (hspec i b).1, ?_⟩
  · rw [batch_length]
    simpa only [rs, List.length_range] using bitTasks_bound n f (List.range d)
  intro x u hx hu hread i b
  rw [(hspec i b).2 x hx]
  have hget := bitTasks_get n f (List.range d) i.val (by simp) b
  simp only [List.getElem_range] at hget
  rw [hget]
  apply Bool.eq_iff_iff.mpr
  simp only [literalTask, List.any_map, List.any_eq_true, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Function.comp_apply]
  constructor
  · rintro ⟨j, ⟨hj, hb⟩, he⟩
    rw [hread j hj, decide_eq_true_eq] at he
    exact he ▸ hb
  · intro hb
    exact ⟨u, ⟨hu, hb⟩, by rw [hread u hu]; simp⟩

private theorem halfEncoder {m d : ℕ} (base : ℕ) (hm : 0 < m)
    (f : Fin (2 ^ d) → Fin m → ℕ) (hf : ∀ i j, f i j < base) :
    ∃ (gs : List Gate) (w : Fin d → Bool → ℕ), Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length ≤ 2 ^ d * m + d * 2 ^ d ∧ (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : ℕ), x.length = base → u < 2 ^ d →
        (∀ i, (∃ j, x.getD (f i j) false = true) ↔ i.val = u) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.testBit i = b) := by
  obtain ⟨groups, g, hgm, hgl, hgr, hge⟩ := buildGroups base hm f hf
  let g' (j : ℕ) := if h : j < 2 ^ d then g ⟨j, h⟩ else 0
  obtain ⟨bits, w, hbm, hbl, hbr, hbe⟩ := buildBits d (base + groups.length) g' (by
    intro j hj
    simpa only [g', dite_eq_left hj] using hgr ⟨j, hj⟩)
  refine ⟨groups ++ bits, w, mono_append hgm hbm, ?_, ?_, ?_⟩
  · have hle := Nat.mul_le_mul_left (2 ^ d) (Nat.sub_le m 1)
    rw [List.length_append, hgl]
    omega
  · intro i b
    simpa only [List.length_append, Nat.add_assoc] using hbr i b
  · intro x u hx hu h i b
    rw [run_append]
    refine hbe _ u (by rw [run_length, hx]) hu (fun j hj => ?_) i b
    apply Bool.eq_iff_iff.mpr
    simp only [g', dite_eq_left hj, hge x hx, h, decide_eq_true_eq]

private theorem rectangle_lt {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.val + m * j.val < m * n := by
  calc
    i.val + m * j.val < m * (j.val + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ m * n := Nat.mul_le_mul_left _ j.isLt

private theorem rectangle_eq {m n : ℕ} (i : Fin m) (j : Fin n) (u : ℕ) :
    i.val + m * j.val = u ↔ i.val = u % m ∧ j.val = u / m := by
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  constructor
  · rintro rfl
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hm,
      Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hi, hj⟩
    rw [hi, hj]
    exact Nat.mod_add_div _ _

private theorem buildEncoder (k base : ℕ) (xs : ℕ → ℕ)
    (hxs : ∀ j < 2 ^ k, xs j < base) :
    ∃ (gs : List Gate) (w : Fin k → Bool → ℕ),
      Monotone2 (⟨gs, 0⟩ : Circuit) ∧ gs.length ≤ 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) ∧
      (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : Fin (2 ^ k)), x.length = base →
        (∀ j < 2 ^ k, x.getD (xs j) false = decide (j = u.val)) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.val.testBit i = b) := by
  let p := k / 2
  let q := (k + 1) / 2
  have hpq : p + q = k := by dsimp [p, q]; omega
  have hpow : 2 ^ p * 2 ^ q = (2 : ℕ) ^ k := by rw [← pow_add, hpq]
  have hle : (2 : ℕ) ^ p ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by dsimp [p, q]; omega)
  let f (i : Fin (2 ^ p)) (j : Fin (2 ^ q)) := xs (i.val + 2 ^ p * j.val)
  have hrect (i : Fin (2 ^ p)) (j : Fin (2 ^ q)) : i.val + 2 ^ p * j.val < 2 ^ k := by
    rw [← hpow]
    exact rectangle_lt i j
  obtain ⟨lo, wlo, hloM, hloS, hloR, hloE⟩ :=
    halfEncoder base (Nat.two_pow_pos q) f (fun i j => hxs _ (hrect i j))
  obtain ⟨hi, whi, hhiM, hhiS, hhiR, hhiE⟩ :=
    halfEncoder (base + lo.length) (Nat.two_pow_pos p) (fun j i => f i j) (fun j i =>
      Nat.lt_of_lt_of_le (hxs _ (hrect i j)) (Nat.le_add_right _ _))
  let w (i : Fin k) (b : Bool) := if h : i.val < p then wlo ⟨i.val, h⟩ b
    else whi ⟨i.val - p, by have := i.isLt; omega⟩ b
  refine ⟨lo ++ hi, w, mono_append hloM hhiM, ?_, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left p hle
    rw [Nat.mul_comm (2 ^ q) (2 ^ p), hpow] at hhiS
    rw [hpow] at hloS
    rw [List.length_append]
    change _ ≤ 2 * 2 ^ k + k * 2 ^ q
    rw [← hpq, Nat.add_mul, hpq]
    omega
  · intro i b
    unfold w
    split
    · have := hloR ⟨i.val, ‹i.val < p›⟩ b
      simp only [List.length_append]
      omega
    · simpa only [List.length_append, Nat.add_assoc] using hhiR _ b
  · intro x u hx hread i b
    have hmod : u.val % 2 ^ p < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
    have hdiv : u.val / 2 ^ p < 2 ^ q := by
      apply Nat.div_lt_of_lt_mul
      rw [hpow]
      exact u.isLt
    have hclass (a : Fin (2 ^ p)) (c : Fin (2 ^ q)) :
        x.getD (f a c) false = true ↔ a.val = u.val % 2 ^ p ∧ c.val = u.val / 2 ^ p := by
      change x.getD (xs (a.val + 2 ^ p * c.val)) false = true ↔ _
      rw [hread _ (hrect a c), decide_eq_true_eq, rectangle_eq a c]
    have hlo (a : Fin (2 ^ p)) :
        (∃ c, x.getD (f a c) false = true) ↔ a.val = u.val % 2 ^ p := by
      simp only [hclass]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨⟨_, hdiv⟩, h, rfl⟩⟩
    have hloLen : (run lo x).length = base + lo.length := by rw [run_length, hx]
    have hhi (c : Fin (2 ^ q)) :
        (∃ a, (run lo x).getD (f a c) false = true) ↔ c.val = u.val / 2 ^ p := by
      have hread' (a : Fin (2 ^ p)) :
          (run lo x).getD (f a c) false = x.getD (f a c) false :=
        run_read lo x (by rw [hx]; exact hxs _ (hrect a c))
      simp only [hread', hclass]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨⟨_, hmod⟩, rfl, h⟩⟩
    rw [run_append]
    unfold w
    split
    · rename_i h
      rw [run_read hi _ (hloLen ▸ hloR ⟨i.val, h⟩ b), hloE x _ hx hmod hlo,
        Nat.testBit_mod_two_pow]
      simp [h]
    · rename_i h
      rw [hhiE _ _ hloLen hdiv hhi, Nat.testBit_div_two_pow]
      have heq : i.val - p + p = i.val := by omega
      simp only [heq]

private def liftWire (n base limit : ℕ) (w : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then w ⟨i, h⟩ else base + min (i - n) limit

private def liftGate (n base limit : ℕ) (w : Fin n → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftWire n base limit w)⟩

private theorem run_lift {n base limit : ℕ} {w : Fin n → ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = base) (hw : ∀ i, w i < base)
    (hread : ∀ i, y.getD (w i) false = x.getD i.val false)
    (gs : List Gate) (t : List Bool) (ht : t.length + gs.length ≤ limit) (i : ℕ) :
    (run (gs.map (liftGate n base limit w)) (y ++ t)).getD (liftWire n base limit w i) false =
      (run gs (x ++ t)).getD i false := by
  have reads (t : List Bool) (hlen : t.length ≤ limit) (j : ℕ) :
      (y ++ t).getD (liftWire n base limit w j) false = (x ++ t).getD j false := by
    unfold liftWire
    split
    · rename_i hj
      rw [List.getD_append _ _ _ _ (hy ▸ hw ⟨j, hj⟩),
        List.getD_append _ _ _ _ (hx ▸ hj)]
      exact hread ⟨j, hj⟩
    · rename_i hj
      rw [← hy, read_tail, List.getD_append_right _ _ _ _ (by omega), hx]
      by_cases h : j - n ≤ limit
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
  induction gs generalizing t with
  | nil => exact reads t (by simpa using ht) i
  | cons g gs ih =>
    let z := g.op.eval (g.inputs.map fun j => (x ++ t).getD j false)
    have ht' : t.length ≤ limit := by omega
    have hz : g.op.eval (g.inputs.map ((fun j => (y ++ t).getD j false) ∘
        liftWire n base limit w)) = z := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro j _
      exact reads t ht' j
    change (run (gs.map (liftGate n base limit w))
      ((y ++ t) ++ [g.op.eval (((g.inputs.map (liftWire n base limit w)).map
        fun j => (y ++ t).getD j false))])).getD _ false =
        (run gs ((x ++ t) ++ [z])).getD i false
    simp only [List.map_map, hz, List.append_assoc]
    apply ih (t ++ [z])
    simp only [List.length_append, List.length_cons, List.length_nil] at *
    omega

private theorem tableIndex_decodes (k u : ℕ) (hu : u < 2 ^ k) :
    tableIndex (fun i : Fin k => u.testBit i) = u := by
  induction k generalizing u with
  | zero =>
    have hz : u = 0 := by simpa using hu
    simp [tableIndex, hz]
  | succ k ih =>
    have hd : u / 2 < 2 ^ k := by
      rw [pow_succ] at hu
      omega
    unfold tableIndex
    rw [Fin.sum_univ_succ]
    have hsum : (∑ i : Fin k, if u.testBit (i.succ.val) = true then 2 ^ (i.succ.val) else 0) =
        2 * tableIndex (fun i : Fin k => (u / 2).testBit i) := by
      rw [tableIndex, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, ← Nat.testBit_div_two, pow_succ]
      split <;> simp [Nat.mul_comm]
    rw [hsum, ih _ hd]
    simp only [Fin.val_zero, pow_zero, Nat.testBit_zero, decide_eq_true_eq]
    split <;> omega

private def joinFin {k l : ℕ} {α : Type} (f : Fin k → α) (g : Fin l → α) : Fin (k + l) → α :=
  Fin.addCases f g

private theorem ofFn_joinFin {k l : ℕ} {α : Type} (f : Fin k → α) (g : Fin l → α) :
    List.ofFn (joinFin f g) = List.ofFn f ++ List.ofFn g := by
  rw [List.ofFn_add]
  have hl (i : Fin k) : joinFin f g (Fin.castLE (Nat.le_add_right k l) i) = f i :=
    Fin.addCases_left i
  have hr (i : Fin l) : joinFin f g (Fin.natAdd k i) = g i := Fin.addCases_right i
  simp only [hl, hr]

private theorem bitGraph {k l : ℕ} (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (u : Fin (2 ^ k)) (v : Fin (2 ^ l)) :
    adjFun A (joinFin (fun i : Fin k => u.val.testBit i) (fun j : Fin l => v.val.testBit j)) =
      A u v := by
  simp only [adjFun, joinFin, Fin.addCases_left, Fin.addCases_right,
    tableIndex_decodes k u.val u.isLt, tableIndex_decodes l v.val v.isLt]
  congr 1
  · apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt
  · apply Fin.ext
    exact Nat.mod_eq_of_lt v.isLt

private theorem assemble (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (h : HasLitSize (k + l) (adjFun A) s) :
    RepSizeAtMost A (s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2)) := by
  obtain ⟨C, hCm, hCs, hCe⟩ := h
  let base : ℕ := 2 ^ k + 2 ^ l
  obtain ⟨gsL, wL, hmL, hsL, hwL, heL⟩ :=
    buildEncoder k base id (fun _ hj => Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
  obtain ⟨gsR, wR, hmR, hsR, hwR, heR⟩ :=
    buildEncoder l (base + gsL.length) (fun j => 2 ^ k + j) (fun j hj => by dsimp [base]; omega)
  let endL := base + gsL.length
  let endR := endL + gsR.length
  let w (b : Bool) := joinFin (fun i => wL i b) (fun j => wR j b)
  let litW := joinFin (w true) (w false)
  let n := (k + l) + (k + l)
  let gs := C.gates.map (liftGate n endR C.gates.length litW)
  have hgm : Monotone2 (⟨gs, 0⟩ : Circuit) := by
    intro g hg
    change g ∈ C.gates.map (liftGate n endR C.gates.length litW) at hg
    obtain ⟨orig, hOrig, hEq⟩ := List.mem_map.mp hg
    rw [← hEq]
    simpa only [liftGate, List.length_map] using hCm orig hOrig
  refine ⟨⟨gsL ++ gsR ++ gs, liftWire n endR C.gates.length litW C.output⟩,
    mono_append (mono_append hmL hmR) hgm, ?_, ?_⟩
  · change C.gates.length ≤ s at hCs
    simp only [Circuit.size, List.length_append, gs, List.length_map]
    omega
  intro u v
  let a := oneEach u v
  let aL := run gsL a
  let aR := run gsR aL
  have ha : a.length = base := by simp [a, base, oneEach]
  have haL : aL.length = endL := by simp only [aL, run_length, ha, endL]
  have haR : aR.length = endR := by simp only [aR, run_length, haL, endR]
  have inL (j : ℕ) (hj : j < 2 ^ k) : a.getD (id j) false = decide (j = u.val) := by
    have hleft : j < (List.ofFn (fun i : Fin (2 ^ k) => decide (i = u))).length := by simp [hj]
    simp only [a, oneEach, id_eq]
    rw [List.getD_append _ _ _ _ hleft]
    exact (read_ofFn _ ⟨j, hj⟩).trans (decide_eq_decide.mpr Fin.ext_iff)
  have inR (j : ℕ) (hj : j < 2 ^ l) : aL.getD (2 ^ k + j) false = decide (j = v.val) := by
    change (run gsL a).getD (2 ^ k + j) false = _
    rw [run_read gsL _ (by rw [ha]; dsimp [base]; omega)]
    have ht := read_tail (List.ofFn fun i : Fin (2 ^ k) => decide (i = u))
      (List.ofFn fun i : Fin (2 ^ l) => decide (i = v)) j
    simp only [List.length_ofFn] at ht
    exact ht.trans ((read_ofFn _ ⟨j, hj⟩).trans (decide_eq_decide.mpr Fin.ext_iff))
  let x := joinFin (fun i : Fin k => u.val.testBit i) (fun j : Fin l => v.val.testBit j)
  have hwl (i : Fin k) (b : Bool) : wL i b < aL.length := haL ▸ hwL i b
  have hbound₁ (i : Fin (k + l)) (b : Bool) : w b i < endR := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hb := hwL j b
      simp only [w, joinFin, Fin.addCases_left, endR, endL]
      omega
    · simpa only [w, joinFin, Fin.addCases_right, endR, endL] using hwR j b
  have hbound (i : Fin n) : litW i < endR := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [litW, joinFin, Fin.addCases_left] using hbound₁ j true
    · simpa only [litW, joinFin, Fin.addCases_right] using hbound₁ j false
  have hlit (i : Fin (k + l)) (b : Bool) : aR.getD (w b i) false = decide (x i = b) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [w, x, joinFin, Fin.addCases_left, aR]
      rw [run_read gsR _ (hwl j b)]
      exact heL a u ha inL j b
    · simp only [w, x, joinFin, Fin.addCases_right]
      exact heR aL v haL inR j b
  let litX := joinFin x (fun i => !x i)
  have hx : List.ofFn litX = List.ofFn x ++ List.ofFn (fun i => !x i) := ofFn_joinFin _ _
  have hread (i : Fin n) : aR.getD (litW i) false = (List.ofFn litX).getD i.val false := by
    rw [read_ofFn]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [litW, litX, joinFin, Fin.addCases_left, hlit]
      cases x j <;> rfl
    · simp only [litW, litX, joinFin, Fin.addCases_right, hlit]
      cases x j <;> rfl
  change (run (gsL ++ gsR ++ gs) a).getD _ false = A u v
  simp only [run_append]
  change (run gs aR).getD _ false = A u v
  have hlift := run_lift (limit := C.gates.length) (x := List.ofFn litX) (y := aR)
    List.length_ofFn haR hbound hread C.gates [] (by simp) C.output
  simp only [List.append_nil] at hlift
  rw [hlift]
  change C.eval (List.ofFn litX) = A u v
  rw [hx, hCe]
  exact bitGraph A u v

end PEqualNP.Outside.L_meta_9023

theorem PEqualNP.Outside.L_meta_9023 :
∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.Represents.HasLitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2)) := by
  exact PEqualNP.Outside.L_meta_9023.assemble
