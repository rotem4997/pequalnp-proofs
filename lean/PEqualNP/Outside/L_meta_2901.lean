import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2901

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

lemma getD_app_left (l1 l2 : List Bool) (i : ℕ) (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_app_right (l1 l2 : List Bool) (i : ℕ) :
    (l1 ++ l2).getD (l1.length + i) false = l2.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

lemma inp_len (x y : Fin 7 → Bool) : (List.ofFn x ++ List.ofFn y).length = 14 := by
  simp

lemma inp_x (x y : Fin 7 → Bool) (i : ℕ) (h : i < 7) :
    (List.ofFn x ++ List.ofFn y).getD i false = x ⟨i, h⟩ :=
  (getD_app_left _ _ i (by simpa using h)).trans (ofFn_getD x i h)

lemma inp_y (x y : Fin 7 → Bool) (i : ℕ) (h : i < 7) :
    (List.ofFn x ++ List.ofFn y).getD (7 + i) false = y ⟨i, h⟩ := by
  have e := getD_app_right (List.ofFn x) (List.ofFn y) i
  rw [List.length_ofFn] at e
  exact e.trans (ofFn_getD y i h)


lemma ok_len (g : Gate) (h : okb g = true) : g.inputs.length ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> cases op <;>
    first
    | exact ff_ne _ rfl h
    | exact Nat.le_refl 2

def gsC : List Gate := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }]

def IncL : List (ℕ × ℕ) := [(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)]

def T0 : List ℕ := (List.range 14).map (fun p => tabX p 14)

def incT : List (ℕ × ℕ) → ℕ
  | [] => 0
  | q :: L => Nat.lor (Nat.land (T0.getD q.1 0) (T0.getD (7 + q.2) 0)) (incT L)

lemma gs_ok : gsC.all okb = true := by decide +kernel

lemma inc_bound : ∀ q ∈ IncL, q.1 < 7 ∧ q.2 < 7 := by decide +kernel

set_option maxHeartbeats 4000000 in
lemma cert : (gsC.foldl tstep T0).getD 44 0 = incT IncL := by decide +kernel

lemma incT_bit (k : ℕ) : ∀ L : List (ℕ × ℕ), Nat.testBit (incT L) k =
    L.any (fun q => Nat.testBit (T0.getD q.1 0) k && Nat.testBit (T0.getD (7 + q.2) 0) k)
  | [] => Nat.zero_testBit k
  | q :: L => by
    show Nat.testBit ((T0.getD q.1 0 &&& T0.getD (7 + q.2) 0) ||| incT L) k = _
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

lemma any_dec (x y : Fin 7 → Bool) :
    IncL.any (fun q => (List.ofFn x ++ List.ofFn y).getD q.1 false &&
      (List.ofFn x ++ List.ofFn y).getD (7 + q.2) false) =
    decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ IncL ∧ x p = true ∧ y l = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨h1, h2⟩ := inc_bound q hq
    simp only [Bool.and_eq_true] at h
    refine ⟨⟨q.1, h1⟩, ⟨q.2, h2⟩, hq, ?_, ?_⟩
    · exact (inp_x x y q.1 h1).symm.trans h.1
    · exact (inp_y x y q.2 h2).symm.trans h.2
  · rintro ⟨p, l, hm, hx, hy⟩
    refine ⟨((p : ℕ), (l : ℕ)), hm, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨(inp_x x y p.1 p.2).trans hx, (inp_y x y l.1 l.2).trans hy⟩

lemma func (x y : Fin 7 → Bool) :
    Circuit.eval ⟨gsC, 44⟩ (List.ofFn x ++ List.ofFn y) =
    decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ IncL ∧ x p = true ∧ y l = true) := by
  have hl : (List.ofFn x ++ List.ofFn y).length = 14 := inp_len x y
  have e1 := eval_tab gsC 44 gs_ok T0 (codeN (List.ofFn x ++ List.ofFn y))
  rw [T0_map _ hl, cert, incT_bit] at e1
  have hb : ∀ i, Nat.testBit (T0.getD i 0) (codeN (List.ofFn x ++ List.ofFn y)) =
      (List.ofFn x ++ List.ofFn y).getD i false := by
    intro i
    rw [← getD_map_tb T0 (codeN (List.ofFn x ++ List.ofFn y)) i, T0_map _ hl]
  simp only [hb] at e1
  rw [e1, any_dec]

lemma mono : PEqualNP.MetaComplexity.Monotone2 ⟨gsC, 44⟩ := by
  intro g hg
  have h := List.all_eq_true.mp gs_ok g hg
  refine ⟨?_, ok_len g h⟩
  rcases ok_op g h with e | e
  · first
    | exact Or.inl e
    | simp [e]
  · first
    | exact Or.inr e
    | simp [e]

lemma rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 ⟨gsC, 44⟩ := by
  decide +kernel

lemma ex1 : PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false := by
  first
  | decide +kernel
  | decide

lemma ex2 : PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false := by
  first
  | decide +kernel
  | decide

theorem main_aux : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 31 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ x y : Fin 7 → Bool, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)) ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false := by
  intro C hC
  subst hC
  exact ⟨mono, rfl, rb, func, ex1, ex2⟩

end PEqualNP.Outside.L_meta_2901

theorem PEqualNP.Outside.L_meta_2901 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 31 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ x y : Fin 7 → Bool, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)) ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false :=
  PEqualNP.Outside.L_meta_2901.main_aux
