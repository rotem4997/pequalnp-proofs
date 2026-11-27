import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3313

open PEqualNP.CircuitLowerBounds


-- One evaluation step of a circuit on a list of wire values.
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (wstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [wstep, List.getD]

lemma snoc_lt (T : List ℕ) (a i : ℕ) (h : i < T.length) :
    (T ++ [a]).getD i 0 = T.getD i 0 := by
  simp [List.getD, List.getElem?_append_left h]

lemma snoc_eq (T : List ℕ) (a i : ℕ) (h : i = T.length) : (T ++ [a]).getD i 0 = a := by
  subst h
  simp [List.getD]

lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma ff_ne (b : Bool) (hb : b = false) (h : b = true) {P : Prop} : P := by
  rw [hb] at h
  exact Bool.noConfusion h

-- Truth tables as natural numbers: bit k of the table of a wire is its value on input number k.
def gtab (T : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => Nat.land (T.getD a 0) (T.getD b 0)
  | GateOp.or, [a, b] => Nat.lor (T.getD a 0) (T.getD b 0)
  | _, _ => 0

def okb (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | GateOp.or, [_, _] => true
  | _, _ => false

def tstep (T : List ℕ) (g : Gate) : List ℕ := T ++ [gtab T g]

lemma tb_and (u v k : ℕ) :
    Nat.testBit (Nat.land u v) k = (Nat.testBit u k && (Nat.testBit v k && true)) := by
  show Nat.testBit (u &&& v) k = (Nat.testBit u k && (Nat.testBit v k && true))
  rw [Nat.testBit_and, Bool.and_true]

lemma tb_or (u v k : ℕ) :
    Nat.testBit (Nat.lor u v) k = (Nat.testBit u k || (Nat.testBit v k || false)) := by
  show Nat.testBit (u ||| v) k = (Nat.testBit u k || (Nat.testBit v k || false))
  rw [Nat.testBit_or, Bool.or_false]

lemma ok_op (g : Gate) (h : okb g = true) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> cases op <;>
    first
    | exact ff_ne _ rfl h
    | exact Or.inl rfl
    | exact Or.inr rfl

lemma gtab_spec (T : List ℕ) (g : Gate) (h : okb g = true) (k : ℕ) :
    Nat.testBit (gtab T g) k =
      g.op.eval (g.inputs.map fun i => Nat.testBit (T.getD i 0) k) := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> cases op <;>
    first
    | exact ff_ne _ rfl h
    | exact tb_and (T.getD a 0) (T.getD b 0) k
    | exact tb_or (T.getD a 0) (T.getD b 0) k

def GoodT (w : ℕ → List Bool) (T : List ℕ) : Prop :=
  (∀ k, (w k).length = T.length) ∧ ∀ i k, Nat.testBit (T.getD i 0) k = (w k).getD i false

lemma good_step (w : ℕ → List Bool) (T : List ℕ) (g : Gate) (hg : okb g = true)
    (h : GoodT w T) : GoodT (fun k => wstep (w k) g) (tstep T g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨fun k => ?_, fun i k => ?_⟩
  · show (wstep (w k) g).length = (T ++ [gtab T g]).length
    rw [wstep_len, List.length_append, List.length_singleton, hl k]
  · show Nat.testBit ((T ++ [gtab T g]).getD i 0) k = (wstep (w k) g).getD i false
    by_cases hlt : i < T.length
    · rw [snoc_lt T _ i hlt, wstep_lt _ _ _ (by rw [hl k]; exact hlt)]
      exact hv i k
    · by_cases heq : i = T.length
      · rw [snoc_eq T _ i heq, wstep_last _ _ _ (by rw [hl k]; exact heq), gtab_spec T g hg k]
        have hfun : (fun j => Nat.testBit (T.getD j 0) k) = fun j => (w k).getD j false :=
          funext (fun j => hv j k)
        rw [hfun]
      · rw [List.getD_eq_default (T ++ [gtab T g]) 0
            (by rw [List.length_append, List.length_singleton]; omega),
          List.getD_eq_default (wstep (w k) g) false (by rw [wstep_len, hl k]; omega)]
        exact Nat.zero_testBit k

lemma good_fold (gs : List Gate) (hg : ∀ g ∈ gs, okb g = true) :
    ∀ (w : ℕ → List Bool) (T : List ℕ), GoodT w T →
      GoodT (fun k => gs.foldl wstep (w k)) (gs.foldl tstep T) := by
  induction gs with
  | nil =>
    intro w T h
    exact h
  | cons g gs ih =>
    intro w T h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (good_step w T g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)

lemma getD_map_tb (T : List ℕ) (k i : ℕ) :
    (T.map fun t => Nat.testBit t k).getD i false = Nat.testBit (T.getD i 0) k := by
  by_cases h : i < T.length
  · rw [List.getD_eq_getElem (T.map fun t => Nat.testBit t k) false (by simpa using h),
      List.getD_eq_getElem T 0 h, List.getElem_map]
  · rw [List.getD_eq_default (T.map fun t => Nat.testBit t k) false (by simpa using h),
      List.getD_eq_default T 0 (by omega)]
    exact (Nat.zero_testBit k).symm

lemma good_map (T : List ℕ) : GoodT (fun k => T.map fun t => Nat.testBit t k) T :=
  ⟨fun k => by simp, fun i k => (getD_map_tb T k i).symm⟩

lemma eval_tab (gs : List Gate) (o : ℕ) (hg : gs.all okb = true) (T : List ℕ) (k : ℕ) :
    Circuit.eval ⟨gs, o⟩ (T.map fun t => Nat.testBit t k) =
      Nat.testBit ((gs.foldl tstep T).getD o 0) k := by
  have h := good_fold gs (fun g hgm => List.all_eq_true.mp hg g hgm) _ _ (good_map T)
  exact (h.2 o k).symm

-- The number coding a list of bits, lowest bit first.
def codeN : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (codeN l)

lemma code_lt : ∀ l : List Bool, codeN l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := code_lt l
    have h2 : codeN (b :: l) = 2 * codeN l + b.toNat := Nat.bit_val b (codeN l)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [h2, List.length_cons, pow_succ]
    omega

lemma code_bit : ∀ (l : List Bool) (i : ℕ), Nat.testBit (codeN l) i = l.getD i false
  | [], i => by
    first
    | exact Nat.zero_testBit i
    | simp [codeN]
  | b :: l, 0 => by
    rw [List.getD_cons_zero]
    exact Nat.testBit_bit_zero b (codeN l)
  | b :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact (Nat.testBit_bit_succ i b (codeN l)).trans (code_bit l i)

-- The table, over the 2 ^ m numbers k below 2 ^ m, of bit p of k.
def tabX (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if m = p then 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 else (2 ^ 2 ^ m + 1) * tabX p m

lemma bnd (A t : ℕ) (h : t < A) : A * t + t < A * A := by
  have h1 := Nat.mul_le_mul_left A (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at h1
  omega

lemma tabX_spec (p : ℕ) : ∀ m : ℕ, tabX p m < 2 ^ 2 ^ m ∧
    ∀ k : ℕ, k < 2 ^ m → Nat.testBit (tabX p m) k = Nat.testBit k p := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · show (0 : ℕ) < 2 ^ 2 ^ 0
      exact Nat.two_pow_pos _
    · have hk0 : k = 0 := by simpa using hk
      rw [hk0]
      show Nat.testBit 0 0 = Nat.testBit 0 p
      rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ m ih =>
    obtain ⟨hb, hbits⟩ := ih
    have hA : 0 < 2 ^ 2 ^ m := Nat.two_pow_pos _
    have hpm : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
    have hpow : 2 ^ 2 ^ (m + 1) = 2 ^ 2 ^ m * 2 ^ 2 ^ m := by
      rw [hpm, Nat.pow_add]
    by_cases hmp : m = p
    · have hdef : tabX p (m + 1) = 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 := by
        rw [tabX, if_pos hmp]
      rw [hdef, ← hmp]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bnd (2 ^ 2 ^ m) (2 ^ 2 ^ m - 1) (by omega)
        rw [hpow]
        omega
      · rw [Nat.testBit_two_pow_mul_add (2 ^ 2 ^ m - 1) hA k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt, Nat.zero_testBit, Nat.testBit_lt_two_pow hlt]
        · rw [if_neg hlt, Nat.testBit_two_pow_sub_one]
          have h1 : Nat.testBit k m = true := by
            have h2 := Nat.testBit_two_pow_add_eq (k - 2 ^ m) m
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega,
              Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ m from by omega)] at h2
            exact h2
          rw [h1]
          exact decide_eq_true (by omega)
    · have hdef : tabX p (m + 1) = 2 ^ 2 ^ m * tabX p m + tabX p m := by
        rw [tabX, if_neg hmp]
        ring
      rw [hdef]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bnd (2 ^ 2 ^ m) (tabX p m) hb
        rw [hpow]
        exact h1
      · rw [Nat.testBit_two_pow_mul_add (tabX p m) hb k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt]
          exact hbits k hlt
        · rw [if_neg hlt, hbits (k - 2 ^ m) (by omega)]
          rcases Nat.lt_or_gt_of_ne hmp with hlt2 | hgt
          · have hle : 2 ^ (m + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ p from by omega),
              Nat.testBit_lt_two_pow (show k < 2 ^ p from by omega)]
          · have h2 := Nat.testBit_two_pow_add_gt hgt (k - 2 ^ m)
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega] at h2
            exact h2.symm

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp


def gsC : List Gate := [{ op := GateOp.or, inputs := [3, 9] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.and, inputs := [17, 16] }, { op := GateOp.or, inputs := [18, 0] }, { op := GateOp.or, inputs := [19, 4] }, { op := GateOp.and, inputs := [20, 8] }, { op := GateOp.or, inputs := [19, 6] }, { op := GateOp.and, inputs := [22, 9] }, { op := GateOp.or, inputs := [16, 1] }, { op := GateOp.and, inputs := [24, 10] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [26, 0] }, { op := GateOp.and, inputs := [27, 7] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.or, inputs := [29, 1] }, { op := GateOp.and, inputs := [30, 11] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [32, 6] }, { op := GateOp.and, inputs := [33, 12] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.or, inputs := [35, 4] }, { op := GateOp.and, inputs := [36, 13] }, { op := GateOp.or, inputs := [21, 28] }, { op := GateOp.or, inputs := [38, 23] }, { op := GateOp.or, inputs := [39, 37] }, { op := GateOp.or, inputs := [34, 31] }, { op := GateOp.or, inputs := [40, 25] }, { op := GateOp.or, inputs := [42, 41] }]

def IncL : List (Fin 14 × Fin 14) := [(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)]

def T0 : List ℕ := (List.range 14).map (fun p => tabX p 14)

def incT : List (Fin 14 × Fin 14) → ℕ
  | [] => 0
  | q :: L => Nat.lor (Nat.land (T0.getD (q.1 : ℕ) 0) (T0.getD (q.2 : ℕ) 0)) (incT L)

lemma gs_ok : gsC.all okb = true := by decide +kernel

set_option maxHeartbeats 4000000 in
lemma cert : (gsC.foldl tstep T0).getD 43 0 = incT IncL := by decide +kernel

lemma incT_bit (k : ℕ) : ∀ L : List (Fin 14 × Fin 14), Nat.testBit (incT L) k =
    L.any (fun q => Nat.testBit (T0.getD (q.1 : ℕ) 0) k && Nat.testBit (T0.getD (q.2 : ℕ) 0) k)
  | [] => Nat.zero_testBit k
  | q :: L => by
    show Nat.testBit ((T0.getD (q.1 : ℕ) 0 &&& T0.getD (q.2 : ℕ) 0) ||| incT L) k = _
    rw [Nat.testBit_or, Nat.testBit_and, incT_bit k L, List.any_cons]

lemma T0_map (l : List Bool) (hl : l.length = 14) :
    T0.map (fun t => Nat.testBit t (codeN l)) = l := by
  have hk : codeN l < 2 ^ 14 := by
    have h := code_lt l
    rw [hl] at h
    exact h
  apply List.ext_getElem
  · simp [T0, hl]
  · intro i h1 h2
    simp only [T0, List.getElem_map, List.getElem_range]
    rw [(tabX_spec i 14).2 _ hk, code_bit, List.getD_eq_getElem _ _ h2]

lemma hx (x : Fin 14 → Bool) (i : Fin 14) : (List.ofFn x).getD (i : ℕ) false = x i :=
  ofFn_getD x i i.isLt

lemma any_dec (x : Fin 14 → Bool) :
    IncL.any (fun q => (List.ofFn x).getD (q.1 : ℕ) false && (List.ofFn x).getD (q.2 : ℕ) false) =
    decide (∃ e ∈ IncL, x e.1 = true ∧ x e.2 = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    simp only [Bool.and_eq_true, hx] at h
    exact ⟨q, hq, h⟩
  · rintro ⟨q, hq, h1, h2⟩
    refine ⟨q, hq, ?_⟩
    simp only [Bool.and_eq_true, hx]
    exact ⟨h1, h2⟩

lemma func (x : Fin 14 → Bool) :
    Circuit.eval ⟨gsC, 43⟩ (List.ofFn x) = decide (∃ e ∈ IncL, x e.1 = true ∧ x e.2 = true) := by
  have hl : (List.ofFn x).length = 14 := by simp
  have e1 := eval_tab gsC 43 gs_ok T0 (codeN (List.ofFn x))
  rw [T0_map _ hl, cert, incT_bit] at e1
  have hb : ∀ i, Nat.testBit (T0.getD i 0) (codeN (List.ofFn x)) = (List.ofFn x).getD i false := by
    intro i
    rw [← getD_map_tb T0 (codeN (List.ofFn x)) i, T0_map _ hl]
  simp only [hb] at e1
  rw [e1, any_dec]

set_option maxHeartbeats 4000000 in
theorem main_aux : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 41] }], output := 43 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 30 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1) ++ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1)).Perm (List.range 30) ∧
  (∀ t ∈ ([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) ∧
  (∀ t ∈ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) := by
  intro C hC
  subst hC
  refine ⟨by decide +kernel, rfl, fun x => func x, by decide +kernel, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h | h | h | h | h | h <;> subst h <;>
      exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro t ht
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_3313

theorem PEqualNP.Outside.L_meta_3313 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 41] }], output := 43 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 30 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1) ++ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1)).Perm (List.range 30) ∧
  (∀ t ∈ ([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) ∧
  (∀ t ∈ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) :=
  PEqualNP.Outside.L_meta_3313.main_aux
