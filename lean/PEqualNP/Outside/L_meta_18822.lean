import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18822

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_step_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
      omega

theorem foldl_step_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (step xs g) i (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem getD_snoc (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

def uvGates : List Gate :=
  (List.range 26).map fun i => ⟨.or, [i, 26 + i]⟩

def orChainAux : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | base, acc, x :: xs => ⟨.or, [acc, x]⟩ :: orChainAux (base + 1) base xs

def orChain (base : ℕ) : List ℕ → List Gate
  | [] => []
  | x :: xs => orChainAux base x xs

def orChainOut (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | _ :: xs => base + xs.length - 1

theorem orChainAux_len (base acc : ℕ) (xs : List ℕ) :
    (orChainAux base acc xs).length = xs.length := by
  induction xs generalizing base acc with
  | nil => rfl
  | cons x xs ih => simp [orChainAux, ih]

theorem orChain_len (base : ℕ) (ws : List ℕ) :
    (orChain base ws).length = ws.length - 1 := by
  cases ws with
  | nil => rfl
  | cons x xs => simp [orChain, orChainAux_len]

theorem foldl_orChainAux (base acc : ℕ) (xs : List ℕ) :
    ∀ (w : List Bool), w.length = base →
      (∀ x ∈ xs, x < base) → acc < base →
      ((orChainAux base acc xs).foldl step w).getD (if xs.isEmpty then acc else base + xs.length - 1) false =
        xs.foldl (fun b x => b || w.getD x false) (w.getD acc false) := by
  induction xs generalizing base acc with
  | nil => intro w _ _ _; simp [orChainAux]
  | cons x xs ih =>
      intro w hlen hxs hacc
      simp only [orChainAux, List.foldl_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hx : x < base := hxs x List.mem_cons_self
      let w' := step w ⟨.or, [acc, x]⟩
      have hw'_len : w'.length = base + 1 := by simp [w', step, hlen]
      have hw'_acc : w'.getD base false = (w.getD acc false || w.getD x false) := by
        simp only [w', step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc w _ base hlen]
      have hxs' : ∀ y ∈ xs, y < base + 1 := fun y hy => by
        have := hxs y (List.mem_cons_of_mem _ hy); omega
      have hsub := ih (base + 1) base w' hw'_len hxs' (by omega)
      have hfold_eq : xs.foldl (fun b y => b || w'.getD y false) (w'.getD base false) =
          xs.foldl (fun b y => b || w.getD y false) (w.getD acc false || w.getD x false) := by
        rw [hw'_acc]
        have hcong : ∀ (l : List ℕ) (b0 : Bool), (∀ y ∈ l, y < base) →
            l.foldl (fun b y => b || w'.getD y false) b0 =
            l.foldl (fun b y => b || w.getD y false) b0 := by
          intro l
          induction l with
          | nil => intro b0 _; rfl
          | cons y ys ihl =>
              intro b0 hyl
              simp only [List.foldl_cons]
              have hy : y < base := hyl y List.mem_cons_self
              have hget : w'.getD y false = w.getD y false := by
                simpa [w', step] using List.getD_append w _ false y (by omega)
              rw [hget]
              exact ihl _ (fun z hz => hyl z (List.mem_cons_of_mem _ hz))
        exact hcong xs _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      cases xs with
      | nil =>
          simp only [List.isEmpty_nil, ↓reduceIte, List.length_nil] at hsub ⊢
          have hidx : base + 1 - 1 = base := by omega
          rw [hidx, hsub, hfold_eq]
      | cons y ys =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hsub ⊢
          have hidx : base + (ys.length + 1 + 1) - 1 = base + 1 + (ys.length + 1) - 1 := by omega
          rw [hidx, hsub, hfold_eq]

theorem foldl_orChain (base : ℕ) (ws : List ℕ) (w : List Bool)
    (hlen : w.length = base) (hne : ws ≠ []) (hlt : ∀ x ∈ ws, x < base) :
    ((orChain base ws).foldl step w).getD (orChainOut base ws) false =
      ws.any (fun x => w.getD x false) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons x xs =>
      have h1 := foldl_orChainAux base x xs w hlen
        (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) (hlt x List.mem_cons_self)
      have hout : orChainOut base (x :: xs) = if xs.isEmpty then x else base + xs.length - 1 := by
        cases xs <;> simp [orChainOut]
      rw [orChain, hout, h1]
      have hany : ∀ (l : List ℕ) (b : Bool),
          l.foldl (fun acc y => acc || w.getD y false) b = (b || l.any (fun y => w.getD y false)) := by
        intro l
        induction l with
        | nil => intro b; simp
        | cons y ys ihl =>
            intro b
            simp only [List.foldl_cons, List.any_cons, ihl, Bool.or_assoc]
      rw [hany, List.any_cons]

def bList0 : List ℕ := [0, 1, 2, 9, 10, 11]
def bList1 : List ℕ := [3, 4, 5, 12, 13, 14]
def bList2 : List ℕ := [6, 7, 8, 15, 16, 17]
def bList3 : List ℕ := [0, 3, 6, 18, 19, 20]
def bList4 : List ℕ := [1, 4, 7, 21, 22, 23]
def bList5 : List ℕ := [2, 5, 8, 24, 25]
def bList6 : List ℕ := [9, 12, 15, 18, 21, 24]
def bList7 : List ℕ := [10, 13, 16, 19, 22, 25]
def bList8 : List ℕ := [11, 14, 17, 20, 23]

def bWires (l : List ℕ) : List ℕ := l.map (fun k => 52 + k)

def topGates : List Gate :=
  [ ⟨GateOp.or, [82, 87]⟩,
    ⟨GateOp.and, [82, 87]⟩,
    ⟨GateOp.or, [121, 92]⟩,
    ⟨GateOp.and, [121, 92]⟩,
    ⟨GateOp.or, [122, 124]⟩,
    ⟨GateOp.or, [97, 102]⟩,
    ⟨GateOp.and, [97, 102]⟩,
    ⟨GateOp.or, [126, 106]⟩,
    ⟨GateOp.and, [126, 106]⟩,
    ⟨GateOp.or, [127, 129]⟩,
    ⟨GateOp.or, [111, 116]⟩,
    ⟨GateOp.and, [111, 116]⟩,
    ⟨GateOp.or, [131, 120]⟩,
    ⟨GateOp.and, [131, 120]⟩,
    ⟨GateOp.or, [132, 134]⟩,
    ⟨GateOp.and, [123, 128]⟩,
    ⟨GateOp.and, [136, 133]⟩,
    ⟨GateOp.or, [125, 130]⟩,
    ⟨GateOp.or, [138, 135]⟩,
    ⟨GateOp.or, [139, 137]⟩ ]

def allGates : List Gate :=
  uvGates ++
  orChain 78 (bWires bList0) ++
  orChain 83 (bWires bList1) ++
  orChain 88 (bWires bList2) ++
  orChain 93 (bWires bList3) ++
  orChain 98 (bWires bList4) ++
  orChain 103 (bWires bList5) ++
  orChain 107 (bWires bList6) ++
  orChain 112 (bWires bList7) ++
  orChain 117 (bWires bList8) ++
  topGates

def circ : Circuit := ⟨allGates, 140⟩

theorem circ_size : circ.size ≤ 89 := by decide

def isMonoGate (g : Gate) : Bool :=
  match g.op with
  | .and => decide (g.inputs.length ≤ 2)
  | .or => decide (g.inputs.length ≤ 2)
  | _ => false

theorem circ_mono : Monotone2 circ := by
  intro g hg
  have hcheck : allGates.all isMonoGate = true := by decide
  have h1 := List.all_eq_true.mp hcheck g hg
  cases hop : g.op with
  | and =>
      simp only [isMonoGate, hop, decide_eq_true_eq] at h1
      exact ⟨by simp, h1⟩
  | or =>
      simp only [isMonoGate, hop, decide_eq_true_eq] at h1
      exact ⟨by simp, h1⟩
  | not => simp [isMonoGate, hop] at h1
  | mod m => simp [isMonoGate, hop] at h1
  | maj => simp [isMonoGate, hop] at h1

theorem oneEach_len (u v : Fin 26) : (oneEach u v).length = 52 := by
  simp [oneEach]

theorem oneEach_getD_left (u v : Fin 26) (i : ℕ) (hi : i < 26) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega : i < (List.ofFn (fun a : Fin 26 => decide (a = u))).length),
    List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
  simp [Fin.ext_iff]

theorem oneEach_getD_right (u v : Fin 26) (i : ℕ) (hi : i < 26) :
    (oneEach u v).getD (26 + i) false = decide (i = v.val) := by
  have h1 : (List.ofFn (fun a : Fin 26 => decide (a = u))).length = 26 := by simp
  simp only [oneEach, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : (List.ofFn (fun a : Fin 26 => decide (a = u))).length ≤ 26 + i),
    h1, Nat.add_sub_cancel_left, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
  simp [Fin.ext_iff]

theorem uv_prefix (u v : Fin 26) :
    ∀ k ≤ 26,
      let wk := ((List.range k).map fun i => (⟨.or, [i, 26 + i]⟩ : Gate)).foldl step (oneEach u v)
      wk.length = 52 + k ∧
      (∀ i < 52, wk.getD i false = (oneEach u v).getD i false) ∧
      (∀ i < k, wk.getD (52 + i) false = (decide (i = u.val) || decide (i = v.val))) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨by simp [oneEach_len], fun i _ => rfl, fun i hi => by omega⟩
  | succ k ih =>
      intro hk
      obtain ⟨hlen, hbase, hprev⟩ := ih (by omega)
      dsimp only
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set wk := ((List.range k).map fun i => (⟨.or, [i, 26 + i]⟩ : Gate)).foldl step (oneEach u v)
      refine ⟨by simp [step, hlen]; omega, ?_, ?_⟩
      · intro i hi
        rw [step, List.getD_append _ _ _ _ (by omega)]
        exact hbase i hi
      · intro i hi
        by_cases hik : i < k
        · rw [step, List.getD_append _ _ _ _ (by omega)]
          exact hprev i hik
        · have heq : i = k := by omega
          subst heq
          simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, getD_snoc wk _ (52 + i) hlen]
          rw [hbase i (by omega), hbase (26 + i) (by omega),
              oneEach_getD_left u v i (by omega), oneEach_getD_right u v i (by omega)]

def inB (l : List ℕ) (u v : Fin 26) : Bool :=
  l.any (fun k => decide (k = u.val) || decide (k = v.val))

theorem eval_bucket (base : ℕ) (l : List ℕ) (u v : Fin 26) (w : List Bool)
    (hlen : w.length = base) (hbase : 78 ≤ base) (hne : l ≠ [])
    (hbound : ∀ k ∈ l, k < 26)
    (hz : ∀ k < 26, w.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val))) :
    ((orChain base (bWires l)).foldl step w).getD (orChainOut base (bWires l)) false = inB l u v := by
  have hne' : bWires l ≠ [] := by cases l with | nil => exact absurd rfl hne | cons _ _ => simp [bWires]
  have hlt : ∀ x ∈ bWires l, x < base := by
    intro x hx
    simp only [bWires, List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have := hbound k hk; omega
  rw [foldl_orChain base (bWires l) w hlen hne' hlt]
  unfold bWires inB
  rw [List.any_map]
  have hcongr : ∀ (xs : List ℕ), (∀ k ∈ xs, k < 26) →
      xs.any (fun k => w.getD (52 + k) false) = xs.any (fun k => decide (k = u.val) || decide (k = v.val)) := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons a as ih =>
        simp only [List.any_cons]
        rw [hz a (hxs a List.mem_cons_self), ih (fun k hk => hxs k (List.mem_cons_of_mem _ hk))]
  exact hcongr l hbound

def p3 (a b c : Bool) : Bool := (a || b) || c
def t3 (a b c : Bool) : Bool := (a && b) || ((a || b) && c)

def topFormula (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Bool :=
  (((t3 b0 b1 b2 || t3 b3 b4 b5) || t3 b6 b7 b8) || ((p3 b0 b1 b2 && p3 b3 b4 b5) && p3 b6 b7 b8))

theorem topFormula_correct : ∀ u v : Fin 26,
    topFormula (inB bList0 u v) (inB bList1 u v) (inB bList2 u v)
      (inB bList3 u v) (inB bList4 u v) (inB bList5 u v)
      (inB bList6 u v) (inB bList7 u v) (inB bList8 u v) = decide (u ≠ v) := by
  decide

theorem step_bin_or (w : List Bool) (a b n : ℕ) (hlen : w.length = n) :
    (step w ⟨.or, [a, b]⟩).getD n false = (w.getD a false || w.getD b false) := by
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, getD_snoc w _ n hlen]

theorem step_bin_and (w : List Bool) (a b n : ℕ) (hlen : w.length = n) :
    (step w ⟨.and, [a, b]⟩).getD n false = (w.getD a false && w.getD b false) := by
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, getD_snoc w _ n hlen]

theorem step_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false :=
  List.getD_append _ _ _ _ hi

theorem eval_top (w : List Bool) (hlen : w.length = 121) :
    (topGates.foldl step w).getD 140 false =
      topFormula (w.getD 82 false) (w.getD 87 false) (w.getD 92 false)
        (w.getD 97 false) (w.getD 102 false) (w.getD 106 false)
        (w.getD 111 false) (w.getD 116 false) (w.getD 120 false) := by
  unfold topGates topFormula p3 t3
  simp only [List.foldl_cons, List.foldl_nil]
  -- Evaluate each of the 20 gates directly using step_bin_or, step_bin_and, step_getD_lt!
  set w0 := w
  have hl0 : w0.length = 121 := hlen
  set w1 := step w0 ⟨GateOp.or, [82, 87]⟩
  have hl1 : w1.length = 122 := by simp [w1, step, hl0]
  set w2 := step w1 ⟨GateOp.and, [82, 87]⟩
  have hl2 : w2.length = 123 := by simp [w2, step, hl1]
  set w3 := step w2 ⟨GateOp.or, [121, 92]⟩
  have hl3 : w3.length = 124 := by simp [w3, step, hl2]
  set w4 := step w3 ⟨GateOp.and, [121, 92]⟩
  have hl4 : w4.length = 125 := by simp [w4, step, hl3]
  set w5 := step w4 ⟨GateOp.or, [122, 124]⟩
  have hl5 : w5.length = 126 := by simp [w5, step, hl4]
  set w6 := step w5 ⟨GateOp.or, [97, 102]⟩
  have hl6 : w6.length = 127 := by simp [w6, step, hl5]
  set w7 := step w6 ⟨GateOp.and, [97, 102]⟩
  have hl7 : w7.length = 128 := by simp [w7, step, hl6]
  set w8 := step w7 ⟨GateOp.or, [126, 106]⟩
  have hl8 : w8.length = 129 := by simp [w8, step, hl7]
  set w9 := step w8 ⟨GateOp.and, [126, 106]⟩
  have hl9 : w9.length = 130 := by simp [w9, step, hl8]
  set w10 := step w9 ⟨GateOp.or, [127, 129]⟩
  have hl10 : w10.length = 131 := by simp [w10, step, hl9]
  set w11 := step w10 ⟨GateOp.or, [111, 116]⟩
  have hl11 : w11.length = 132 := by simp [w11, step, hl10]
  set w12 := step w11 ⟨GateOp.and, [111, 116]⟩
  have hl12 : w12.length = 133 := by simp [w12, step, hl11]
  set w13 := step w12 ⟨GateOp.or, [131, 120]⟩
  have hl13 : w13.length = 134 := by simp [w13, step, hl12]
  set w14 := step w13 ⟨GateOp.and, [131, 120]⟩
  have hl14 : w14.length = 135 := by simp [w14, step, hl13]
  set w15 := step w14 ⟨GateOp.or, [132, 134]⟩
  have hl15 : w15.length = 136 := by simp [w15, step, hl14]
  set w16 := step w15 ⟨GateOp.and, [123, 128]⟩
  have hl16 : w16.length = 137 := by simp [w16, step, hl15]
  set w17 := step w16 ⟨GateOp.and, [136, 133]⟩
  have hl17 : w17.length = 138 := by simp [w17, step, hl16]
  set w18 := step w17 ⟨GateOp.or, [125, 130]⟩
  have hl18 : w18.length = 139 := by simp [w18, step, hl17]
  set w19 := step w18 ⟨GateOp.or, [138, 135]⟩
  have hl19 : w19.length = 140 := by simp [w19, step, hl18]
  set w20 := step w19 ⟨GateOp.or, [139, 137]⟩
  have hl20 : w20.length = 141 := by simp [w20, step, hl19]
  have ha0 : w0.getD 82 false = w.getD 82 false := rfl
  have hb0 : w0.getD 87 false = w.getD 87 false := rfl
  have hv121 : w1.getD 121 false = (w.getD 82 false || w.getD 87 false) := by rw [step_bin_or w0 82 87 121 hl0, ha0, hb0]
  have ha1 : w1.getD 82 false = w.getD 82 false := by rw [step_getD_lt w0 _ 82 (by omega)]
  have hb1 : w1.getD 87 false = w.getD 87 false := by rw [step_getD_lt w0 _ 87 (by omega)]
  have hv122 : w2.getD 122 false = (w.getD 82 false && w.getD 87 false) := by rw [step_bin_and w1 82 87 122 hl1, ha1, hb1]
  have ha2 : w2.getD 121 false = (w.getD 82 false || w.getD 87 false) := by rw [step_getD_lt w1 _ 121 (by omega)]; exact hv121
  have hb2 : w2.getD 92 false = w.getD 92 false := by rw [step_getD_lt w1 _ 92 (by omega), step_getD_lt w0 _ 92 (by omega)]
  have hv123 : w3.getD 123 false = ((w.getD 82 false || w.getD 87 false) || w.getD 92 false) := by rw [step_bin_or w2 121 92 123 hl2, ha2, hb2]
  have ha3 : w3.getD 121 false = (w.getD 82 false || w.getD 87 false) := by rw [step_getD_lt w2 _ 121 (by omega), step_getD_lt w1 _ 121 (by omega)]; exact hv121
  have hb3 : w3.getD 92 false = w.getD 92 false := by rw [step_getD_lt w2 _ 92 (by omega), step_getD_lt w1 _ 92 (by omega), step_getD_lt w0 _ 92 (by omega)]
  have hv124 : w4.getD 124 false = ((w.getD 82 false || w.getD 87 false) && w.getD 92 false) := by rw [step_bin_and w3 121 92 124 hl3, ha3, hb3]
  have ha4 : w4.getD 122 false = (w.getD 82 false && w.getD 87 false) := by rw [step_getD_lt w3 _ 122 (by omega), step_getD_lt w2 _ 122 (by omega)]; exact hv122
  have hb4 : w4.getD 124 false = ((w.getD 82 false || w.getD 87 false) && w.getD 92 false) := hv124
  have hv125 : w5.getD 125 false = ((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) := by rw [step_bin_or w4 122 124 125 hl4, ha4, hb4]
  have ha5 : w5.getD 97 false = w.getD 97 false := by rw [step_getD_lt w4 _ 97 (by omega), step_getD_lt w3 _ 97 (by omega), step_getD_lt w2 _ 97 (by omega), step_getD_lt w1 _ 97 (by omega), step_getD_lt w0 _ 97 (by omega)]
  have hb5 : w5.getD 102 false = w.getD 102 false := by rw [step_getD_lt w4 _ 102 (by omega), step_getD_lt w3 _ 102 (by omega), step_getD_lt w2 _ 102 (by omega), step_getD_lt w1 _ 102 (by omega), step_getD_lt w0 _ 102 (by omega)]
  have hv126 : w6.getD 126 false = (w.getD 97 false || w.getD 102 false) := by rw [step_bin_or w5 97 102 126 hl5, ha5, hb5]
  have ha6 : w6.getD 97 false = w.getD 97 false := by rw [step_getD_lt w5 _ 97 (by omega), step_getD_lt w4 _ 97 (by omega), step_getD_lt w3 _ 97 (by omega), step_getD_lt w2 _ 97 (by omega), step_getD_lt w1 _ 97 (by omega), step_getD_lt w0 _ 97 (by omega)]
  have hb6 : w6.getD 102 false = w.getD 102 false := by rw [step_getD_lt w5 _ 102 (by omega), step_getD_lt w4 _ 102 (by omega), step_getD_lt w3 _ 102 (by omega), step_getD_lt w2 _ 102 (by omega), step_getD_lt w1 _ 102 (by omega), step_getD_lt w0 _ 102 (by omega)]
  have hv127 : w7.getD 127 false = (w.getD 97 false && w.getD 102 false) := by rw [step_bin_and w6 97 102 127 hl6, ha6, hb6]
  have ha7 : w7.getD 126 false = (w.getD 97 false || w.getD 102 false) := by rw [step_getD_lt w6 _ 126 (by omega)]; exact hv126
  have hb7 : w7.getD 106 false = w.getD 106 false := by rw [step_getD_lt w6 _ 106 (by omega), step_getD_lt w5 _ 106 (by omega), step_getD_lt w4 _ 106 (by omega), step_getD_lt w3 _ 106 (by omega), step_getD_lt w2 _ 106 (by omega), step_getD_lt w1 _ 106 (by omega), step_getD_lt w0 _ 106 (by omega)]
  have hv128 : w8.getD 128 false = ((w.getD 97 false || w.getD 102 false) || w.getD 106 false) := by rw [step_bin_or w7 126 106 128 hl7, ha7, hb7]
  have ha8 : w8.getD 126 false = (w.getD 97 false || w.getD 102 false) := by rw [step_getD_lt w7 _ 126 (by omega), step_getD_lt w6 _ 126 (by omega)]; exact hv126
  have hb8 : w8.getD 106 false = w.getD 106 false := by rw [step_getD_lt w7 _ 106 (by omega), step_getD_lt w6 _ 106 (by omega), step_getD_lt w5 _ 106 (by omega), step_getD_lt w4 _ 106 (by omega), step_getD_lt w3 _ 106 (by omega), step_getD_lt w2 _ 106 (by omega), step_getD_lt w1 _ 106 (by omega), step_getD_lt w0 _ 106 (by omega)]
  have hv129 : w9.getD 129 false = ((w.getD 97 false || w.getD 102 false) && w.getD 106 false) := by rw [step_bin_and w8 126 106 129 hl8, ha8, hb8]
  have ha9 : w9.getD 127 false = (w.getD 97 false && w.getD 102 false) := by rw [step_getD_lt w8 _ 127 (by omega), step_getD_lt w7 _ 127 (by omega)]; exact hv127
  have hb9 : w9.getD 129 false = ((w.getD 97 false || w.getD 102 false) && w.getD 106 false) := hv129
  have hv130 : w10.getD 130 false = ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false)) := by rw [step_bin_or w9 127 129 130 hl9, ha9, hb9]
  have ha10 : w10.getD 111 false = w.getD 111 false := by rw [step_getD_lt w9 _ 111 (by omega), step_getD_lt w8 _ 111 (by omega), step_getD_lt w7 _ 111 (by omega), step_getD_lt w6 _ 111 (by omega), step_getD_lt w5 _ 111 (by omega), step_getD_lt w4 _ 111 (by omega), step_getD_lt w3 _ 111 (by omega), step_getD_lt w2 _ 111 (by omega), step_getD_lt w1 _ 111 (by omega), step_getD_lt w0 _ 111 (by omega)]
  have hb10 : w10.getD 116 false = w.getD 116 false := by rw [step_getD_lt w9 _ 116 (by omega), step_getD_lt w8 _ 116 (by omega), step_getD_lt w7 _ 116 (by omega), step_getD_lt w6 _ 116 (by omega), step_getD_lt w5 _ 116 (by omega), step_getD_lt w4 _ 116 (by omega), step_getD_lt w3 _ 116 (by omega), step_getD_lt w2 _ 116 (by omega), step_getD_lt w1 _ 116 (by omega), step_getD_lt w0 _ 116 (by omega)]
  have hv131 : w11.getD 131 false = (w.getD 111 false || w.getD 116 false) := by rw [step_bin_or w10 111 116 131 hl10, ha10, hb10]
  have ha11 : w11.getD 111 false = w.getD 111 false := by rw [step_getD_lt w10 _ 111 (by omega), step_getD_lt w9 _ 111 (by omega), step_getD_lt w8 _ 111 (by omega), step_getD_lt w7 _ 111 (by omega), step_getD_lt w6 _ 111 (by omega), step_getD_lt w5 _ 111 (by omega), step_getD_lt w4 _ 111 (by omega), step_getD_lt w3 _ 111 (by omega), step_getD_lt w2 _ 111 (by omega), step_getD_lt w1 _ 111 (by omega), step_getD_lt w0 _ 111 (by omega)]
  have hb11 : w11.getD 116 false = w.getD 116 false := by rw [step_getD_lt w10 _ 116 (by omega), step_getD_lt w9 _ 116 (by omega), step_getD_lt w8 _ 116 (by omega), step_getD_lt w7 _ 116 (by omega), step_getD_lt w6 _ 116 (by omega), step_getD_lt w5 _ 116 (by omega), step_getD_lt w4 _ 116 (by omega), step_getD_lt w3 _ 116 (by omega), step_getD_lt w2 _ 116 (by omega), step_getD_lt w1 _ 116 (by omega), step_getD_lt w0 _ 116 (by omega)]
  have hv132 : w12.getD 132 false = (w.getD 111 false && w.getD 116 false) := by rw [step_bin_and w11 111 116 132 hl11, ha11, hb11]
  have ha12 : w12.getD 131 false = (w.getD 111 false || w.getD 116 false) := by rw [step_getD_lt w11 _ 131 (by omega)]; exact hv131
  have hb12 : w12.getD 120 false = w.getD 120 false := by rw [step_getD_lt w11 _ 120 (by omega), step_getD_lt w10 _ 120 (by omega), step_getD_lt w9 _ 120 (by omega), step_getD_lt w8 _ 120 (by omega), step_getD_lt w7 _ 120 (by omega), step_getD_lt w6 _ 120 (by omega), step_getD_lt w5 _ 120 (by omega), step_getD_lt w4 _ 120 (by omega), step_getD_lt w3 _ 120 (by omega), step_getD_lt w2 _ 120 (by omega), step_getD_lt w1 _ 120 (by omega), step_getD_lt w0 _ 120 (by omega)]
  have hv133 : w13.getD 133 false = ((w.getD 111 false || w.getD 116 false) || w.getD 120 false) := by rw [step_bin_or w12 131 120 133 hl12, ha12, hb12]
  have ha13 : w13.getD 131 false = (w.getD 111 false || w.getD 116 false) := by rw [step_getD_lt w12 _ 131 (by omega), step_getD_lt w11 _ 131 (by omega)]; exact hv131
  have hb13 : w13.getD 120 false = w.getD 120 false := by rw [step_getD_lt w12 _ 120 (by omega), step_getD_lt w11 _ 120 (by omega), step_getD_lt w10 _ 120 (by omega), step_getD_lt w9 _ 120 (by omega), step_getD_lt w8 _ 120 (by omega), step_getD_lt w7 _ 120 (by omega), step_getD_lt w6 _ 120 (by omega), step_getD_lt w5 _ 120 (by omega), step_getD_lt w4 _ 120 (by omega), step_getD_lt w3 _ 120 (by omega), step_getD_lt w2 _ 120 (by omega), step_getD_lt w1 _ 120 (by omega), step_getD_lt w0 _ 120 (by omega)]
  have hv134 : w14.getD 134 false = ((w.getD 111 false || w.getD 116 false) && w.getD 120 false) := by rw [step_bin_and w13 131 120 134 hl13, ha13, hb13]
  have ha14 : w14.getD 132 false = (w.getD 111 false && w.getD 116 false) := by rw [step_getD_lt w13 _ 132 (by omega), step_getD_lt w12 _ 132 (by omega)]; exact hv132
  have hb14 : w14.getD 134 false = ((w.getD 111 false || w.getD 116 false) && w.getD 120 false) := hv134
  have hv135 : w15.getD 135 false = ((w.getD 111 false && w.getD 116 false) || ((w.getD 111 false || w.getD 116 false) && w.getD 120 false)) := by rw [step_bin_or w14 132 134 135 hl14, ha14, hb14]
  have ha15 : w15.getD 123 false = ((w.getD 82 false || w.getD 87 false) || w.getD 92 false) := by rw [step_getD_lt w14 _ 123 (by omega), step_getD_lt w13 _ 123 (by omega), step_getD_lt w12 _ 123 (by omega), step_getD_lt w11 _ 123 (by omega), step_getD_lt w10 _ 123 (by omega), step_getD_lt w9 _ 123 (by omega), step_getD_lt w8 _ 123 (by omega), step_getD_lt w7 _ 123 (by omega), step_getD_lt w6 _ 123 (by omega), step_getD_lt w5 _ 123 (by omega), step_getD_lt w4 _ 123 (by omega), step_getD_lt w3 _ 123 (by omega)]; exact hv123
  have hb15 : w15.getD 128 false = ((w.getD 97 false || w.getD 102 false) || w.getD 106 false) := by rw [step_getD_lt w14 _ 128 (by omega), step_getD_lt w13 _ 128 (by omega), step_getD_lt w12 _ 128 (by omega), step_getD_lt w11 _ 128 (by omega), step_getD_lt w10 _ 128 (by omega), step_getD_lt w9 _ 128 (by omega), step_getD_lt w8 _ 128 (by omega)]; exact hv128
  have hv136 : w16.getD 136 false = (((w.getD 82 false || w.getD 87 false) || w.getD 92 false) && ((w.getD 97 false || w.getD 102 false) || w.getD 106 false)) := by rw [step_bin_and w15 123 128 136 hl15, ha15, hb15]
  have ha16 : w16.getD 136 false = (((w.getD 82 false || w.getD 87 false) || w.getD 92 false) && ((w.getD 97 false || w.getD 102 false) || w.getD 106 false)) := hv136
  have hb16 : w16.getD 133 false = ((w.getD 111 false || w.getD 116 false) || w.getD 120 false) := by rw [step_getD_lt w15 _ 133 (by omega), step_getD_lt w14 _ 133 (by omega), step_getD_lt w13 _ 133 (by omega)]; exact hv133
  have hv137 : w17.getD 137 false = ((((w.getD 82 false || w.getD 87 false) || w.getD 92 false) && ((w.getD 97 false || w.getD 102 false) || w.getD 106 false)) && ((w.getD 111 false || w.getD 116 false) || w.getD 120 false)) := by rw [step_bin_and w16 136 133 137 hl16, ha16, hb16]
  have ha17 : w17.getD 125 false = ((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) := by rw [step_getD_lt w16 _ 125 (by omega), step_getD_lt w15 _ 125 (by omega), step_getD_lt w14 _ 125 (by omega), step_getD_lt w13 _ 125 (by omega), step_getD_lt w12 _ 125 (by omega), step_getD_lt w11 _ 125 (by omega), step_getD_lt w10 _ 125 (by omega), step_getD_lt w9 _ 125 (by omega), step_getD_lt w8 _ 125 (by omega), step_getD_lt w7 _ 125 (by omega), step_getD_lt w6 _ 125 (by omega), step_getD_lt w5 _ 125 (by omega)]; exact hv125
  have hb17 : w17.getD 130 false = ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false)) := by rw [step_getD_lt w16 _ 130 (by omega), step_getD_lt w15 _ 130 (by omega), step_getD_lt w14 _ 130 (by omega), step_getD_lt w13 _ 130 (by omega), step_getD_lt w12 _ 130 (by omega), step_getD_lt w11 _ 130 (by omega), step_getD_lt w10 _ 130 (by omega)]; exact hv130
  have hv138 : w18.getD 138 false = (((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) || ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false))) := by rw [step_bin_or w17 125 130 138 hl17, ha17, hb17]
  have ha18 : w18.getD 138 false = (((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) || ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false))) := hv138
  have hb18 : w18.getD 135 false = ((w.getD 111 false && w.getD 116 false) || ((w.getD 111 false || w.getD 116 false) && w.getD 120 false)) := by rw [step_getD_lt w17 _ 135 (by omega), step_getD_lt w16 _ 135 (by omega), step_getD_lt w15 _ 135 (by omega)]; exact hv135
  have hv139 : w19.getD 139 false = ((((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) || ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false))) || ((w.getD 111 false && w.getD 116 false) || ((w.getD 111 false || w.getD 116 false) && w.getD 120 false))) := by rw [step_bin_or w18 138 135 139 hl18, ha18, hb18]
  have ha19 : w19.getD 139 false = ((((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) || ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false))) || ((w.getD 111 false && w.getD 116 false) || ((w.getD 111 false || w.getD 116 false) && w.getD 120 false))) := hv139
  have hb19 : w19.getD 137 false = ((((w.getD 82 false || w.getD 87 false) || w.getD 92 false) && ((w.getD 97 false || w.getD 102 false) || w.getD 106 false)) && ((w.getD 111 false || w.getD 116 false) || w.getD 120 false)) := by rw [step_getD_lt w18 _ 137 (by omega), step_getD_lt w17 _ 137 (by omega)]; exact hv137
  have hv140 : w20.getD 140 false = (((((w.getD 82 false && w.getD 87 false) || ((w.getD 82 false || w.getD 87 false) && w.getD 92 false)) || ((w.getD 97 false && w.getD 102 false) || ((w.getD 97 false || w.getD 102 false) && w.getD 106 false))) || ((w.getD 111 false && w.getD 116 false) || ((w.getD 111 false || w.getD 116 false) && w.getD 120 false))) || ((((w.getD 82 false || w.getD 87 false) || w.getD 92 false) && ((w.getD 97 false || w.getD 102 false) || w.getD 106 false)) && ((w.getD 111 false || w.getD 116 false) || w.getD 120 false))) := by rw [step_bin_or w19 139 137 140 hl19, ha19, hb19]
  exact hv140

theorem circ_rep : Represents (fun u v : Fin 26 => decide (u ≠ v)) circ := by
  intro u v
  unfold Circuit.eval Circuit.wires circ allGates
  change ((uvGates ++ orChain 78 (bWires bList0) ++ orChain 83 (bWires bList1) ++
    orChain 88 (bWires bList2) ++ orChain 93 (bWires bList3) ++ orChain 98 (bWires bList4) ++
    orChain 103 (bWires bList5) ++ orChain 107 (bWires bList6) ++ orChain 112 (bWires bList7) ++
    orChain 117 (bWires bList8) ++ topGates).foldl step (oneEach u v)).getD 140 false = decide (u ≠ v)
  simp only [List.foldl_append]
  have huv := uv_prefix u v 26 (Nat.le_refl 26)
  dsimp only at huv
  obtain ⟨hl_uv, _, hz_uv⟩ := huv
  set w0 := uvGates.foldl step (oneEach u v)
  have hlen0 : w0.length = 78 := hl_uv
  have hz0 : ∀ k < 26, w0.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := hz_uv
  set w1 := (orChain 78 (bWires bList0)).foldl step w0
  have hlen1 : w1.length = 83 := by rw [foldl_step_len, hlen0]; decide
  have hz1 : ∀ k < 26, w1.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w0 _ (by omega)]; exact hz0 k hk
  have hb0 : w1.getD 82 false = inB bList0 u v := eval_bucket 78 bList0 u v w0 hlen0 (by omega) (by decide) (by decide) hz0
  set w2 := (orChain 83 (bWires bList1)).foldl step w1
  have hlen2 : w2.length = 88 := by rw [foldl_step_len, hlen1]; decide
  have hz2 : ∀ k < 26, w2.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w1 _ (by omega)]; exact hz1 k hk
  have hb1 : w2.getD 87 false = inB bList1 u v := eval_bucket 83 bList1 u v w1 hlen1 (by omega) (by decide) (by decide) hz1
  set w3 := (orChain 88 (bWires bList2)).foldl step w2
  have hlen3 : w3.length = 93 := by rw [foldl_step_len, hlen2]; decide
  have hz3 : ∀ k < 26, w3.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w2 _ (by omega)]; exact hz2 k hk
  have hb2 : w3.getD 92 false = inB bList2 u v := eval_bucket 88 bList2 u v w2 hlen2 (by omega) (by decide) (by decide) hz2
  set w4 := (orChain 93 (bWires bList3)).foldl step w3
  have hlen4 : w4.length = 98 := by rw [foldl_step_len, hlen3]; decide
  have hz4 : ∀ k < 26, w4.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w3 _ (by omega)]; exact hz3 k hk
  have hb3 : w4.getD 97 false = inB bList3 u v := eval_bucket 93 bList3 u v w3 hlen3 (by omega) (by decide) (by decide) hz3
  set w5 := (orChain 98 (bWires bList4)).foldl step w4
  have hlen5 : w5.length = 103 := by rw [foldl_step_len, hlen4]; decide
  have hz5 : ∀ k < 26, w5.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w4 _ (by omega)]; exact hz4 k hk
  have hb4 : w5.getD 102 false = inB bList4 u v := eval_bucket 98 bList4 u v w4 hlen4 (by omega) (by decide) (by decide) hz4
  set w6 := (orChain 103 (bWires bList5)).foldl step w5
  have hlen6 : w6.length = 107 := by rw [foldl_step_len, hlen5]; decide
  have hz6 : ∀ k < 26, w6.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w5 _ (by omega)]; exact hz5 k hk
  have hb5 : w6.getD 106 false = inB bList5 u v := eval_bucket 103 bList5 u v w5 hlen5 (by omega) (by decide) (by decide) hz5
  set w7 := (orChain 107 (bWires bList6)).foldl step w6
  have hlen7 : w7.length = 112 := by rw [foldl_step_len, hlen6]; decide
  have hz7 : ∀ k < 26, w7.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w6 _ (by omega)]; exact hz6 k hk
  have hb6 : w7.getD 111 false = inB bList6 u v := eval_bucket 107 bList6 u v w6 hlen6 (by omega) (by decide) (by decide) hz6
  set w8 := (orChain 112 (bWires bList7)).foldl step w7
  have hlen8 : w8.length = 117 := by rw [foldl_step_len, hlen7]; decide
  have hz8 : ∀ k < 26, w8.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w7 _ (by omega)]; exact hz7 k hk
  have hb7 : w8.getD 116 false = inB bList7 u v := eval_bucket 112 bList7 u v w7 hlen7 (by omega) (by decide) (by decide) hz7
  set w9 := (orChain 117 (bWires bList8)).foldl step w8
  have hlen9 : w9.length = 121 := by rw [foldl_step_len, hlen8]; decide
  have hz9 : ∀ k < 26, w9.getD (52 + k) false = (decide (k = u.val) || decide (k = v.val)) := fun k hk => by rw [foldl_step_getD_lt _ w8 _ (by omega)]; exact hz8 k hk
  have hb8 : w9.getD 120 false = inB bList8 u v := eval_bucket 117 bList8 u v w8 hlen8 (by omega) (by decide) (by decide) hz8
  have hbf0 : w9.getD 82 false = inB bList0 u v := by rw [foldl_step_getD_lt _ w8 82 (by omega), foldl_step_getD_lt _ w7 82 (by omega), foldl_step_getD_lt _ w6 82 (by omega), foldl_step_getD_lt _ w5 82 (by omega), foldl_step_getD_lt _ w4 82 (by omega), foldl_step_getD_lt _ w3 82 (by omega), foldl_step_getD_lt _ w2 82 (by omega), foldl_step_getD_lt _ w1 82 (by omega)]; exact hb0
  have hbf1 : w9.getD 87 false = inB bList1 u v := by rw [foldl_step_getD_lt _ w8 87 (by omega), foldl_step_getD_lt _ w7 87 (by omega), foldl_step_getD_lt _ w6 87 (by omega), foldl_step_getD_lt _ w5 87 (by omega), foldl_step_getD_lt _ w4 87 (by omega), foldl_step_getD_lt _ w3 87 (by omega), foldl_step_getD_lt _ w2 87 (by omega)]; exact hb1
  have hbf2 : w9.getD 92 false = inB bList2 u v := by rw [foldl_step_getD_lt _ w8 92 (by omega), foldl_step_getD_lt _ w7 92 (by omega), foldl_step_getD_lt _ w6 92 (by omega), foldl_step_getD_lt _ w5 92 (by omega), foldl_step_getD_lt _ w4 92 (by omega), foldl_step_getD_lt _ w3 92 (by omega)]; exact hb2
  have hbf3 : w9.getD 97 false = inB bList3 u v := by rw [foldl_step_getD_lt _ w8 97 (by omega), foldl_step_getD_lt _ w7 97 (by omega), foldl_step_getD_lt _ w6 97 (by omega), foldl_step_getD_lt _ w5 97 (by omega), foldl_step_getD_lt _ w4 97 (by omega)]; exact hb3
  have hbf4 : w9.getD 102 false = inB bList4 u v := by rw [foldl_step_getD_lt _ w8 102 (by omega), foldl_step_getD_lt _ w7 102 (by omega), foldl_step_getD_lt _ w6 102 (by omega), foldl_step_getD_lt _ w5 102 (by omega)]; exact hb4
  have hbf5 : w9.getD 106 false = inB bList5 u v := by rw [foldl_step_getD_lt _ w8 106 (by omega), foldl_step_getD_lt _ w7 106 (by omega), foldl_step_getD_lt _ w6 106 (by omega)]; exact hb5
  have hbf6 : w9.getD 111 false = inB bList6 u v := by rw [foldl_step_getD_lt _ w8 111 (by omega), foldl_step_getD_lt _ w7 111 (by omega)]; exact hb6
  have hbf7 : w9.getD 116 false = inB bList7 u v := by rw [foldl_step_getD_lt _ w8 116 (by omega)]; exact hb7
  have hbf8 : w9.getD 120 false = inB bList8 u v := hb8
  rw [eval_top w9 hlen9, hbf0, hbf1, hbf2, hbf3, hbf4, hbf5, hbf6, hbf7, hbf8]
  exact topFormula_correct u v

end PEqualNP.Outside.L_meta_18822

theorem PEqualNP.Outside.L_meta_18822 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 26 => decide (u ≠ v)) 89 :=
  ⟨PEqualNP.Outside.L_meta_18822.circ, PEqualNP.Outside.L_meta_18822.circ_mono,
   PEqualNP.Outside.L_meta_18822.circ_size, PEqualNP.Outside.L_meta_18822.circ_rep⟩
