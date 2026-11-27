import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9728_aux

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

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

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

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

theorem tr_sum_liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℕ) :
    ∑ w ∈ (Finset.range m).filter (fun w => P (liftP σ w)), g (liftP σ w) =
      ∑ w ∈ (Finset.range m).filter P, g w := by
  refine Finset.sum_nbij' (liftP σ) (liftP σ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ hm a).mpr ha.1, ha.2⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ⁻¹ hm a).mpr ha.1, by rw [tr_liftP_inv']; exact ha.2⟩
  · intro a _; exact liftP_inv σ a
  · intro a _; exact tr_liftP_inv' σ a
  · intro a _; rfl

theorem tr_surplus_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ w, Q (liftP σ w) ↔ P w) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter Q) =
      surplusOn D ((inner n D).filter P) := by
  rcases eq_or_ne D [] with rfl | hne
  · simp [surplusOn, relabel, fanout, readers]
  · have hpos := List.length_pos_iff.mpr hne
    have hm : n ≤ n + D.length - 1 := by omega
    unfold surplusOn inner
    rw [relabel_length]
    exact (tr_sum_liftP σ hm Q (fun w => fanout (relabel σ D) w - 1)).symm.trans
      (Finset.sum_congr (Finset.filter_congr fun w _ => hPQ w)
        fun w _ => by rw [relabel_fanout])

theorem relabel_totalSurplus {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    totalSurplus n (relabel σ D) = totalSurplus n D := by
  simpa [totalSurplus] using
    tr_surplus_filter σ D (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)

theorem relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bplus n (relabel σ D) = Bplus n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bzero n (relabel σ D) = Bzero n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

theorem relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

theorem relabel_pureBranch {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) :
    PureBranch n (relabel σ D) (fun v => liftP σ (b (σ⁻¹ v))) := by
  intro v hv
  rw [relabel_eligSet σ hS, Finset.mem_image] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨hf, hs⟩ := hb u hu
  have e : σ⁻¹ (σ u) = u := by simp
  show 2 ≤ fanout (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) ∧
    supp n (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) = {σ u}
  rw [e, relabel_fanout, relabel_supp σ hS, hs, Finset.image_singleton]
  exact ⟨hf, rfl⟩

def edgeList : List (ℕ × ℕ) :=
  [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def G14Edge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 14) : Prop :=
  (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def adjBits (u : Fin 14) : ℕ :=
  match u.val with | 0 => 1280 | 1 => 8832 | 2 => 12544 | 3 => 6272 | 4 => 11264 | 5 => 5632 | 6 => 2816 | 7 => 10 | 8 => 69 | 9 => 98 | 10 => 49 | 11 => 88 | 12 => 44 | _ => 22

def hc_adjB (u v : Fin 14) : Bool := (adjBits u).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 14, hc_adjB u v = true ↔ Adj u v := by
  decide +kernel

theorem sem_adjB_false {u v : Fin 14} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff]; cases hc_adjB u v <;> decide

theorem adj_symm {u v : Fin 14} (h : Adj u v) : Adj v u := h.symm

theorem adj_irrefl (u : Fin 14) : ¬ Adj u u := by
  revert u; decide +kernel

theorem g14Edge_iff_adj (x : Fin 14 → Bool) :
    G14Edge x ↔ ∃ u v : Fin 14, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩; exact ⟨u, v, Or.inl huv, hx, hy⟩
  · rintro ⟨u, v, huv | hvu, hx, hy⟩
    · exact ⟨u, v, huv, hx, hy⟩
    · exact ⟨v, u, hvu, hy, hx⟩

def g14_nbB (v : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun u => hc_adjB v u = true)

def sem_g14_nb (v : Fin 14) : Finset (Fin 14) := g14_nbB v

theorem g14_nb_eq (v : Fin 14) : sem_g14_nb v = g14_nbB v := rfl

theorem g14_mem_nb {i a : Fin 14} : a ∈ sem_g14_nb i ↔ Adj i a := by
  simp only [sem_g14_nb, g14_nbB, Finset.mem_filter, Finset.mem_univ, true_and, hc_adjB_iff]

theorem degree_two_or_three : ∀ v : Fin 14, (g14_nbB v).card = 2 ∨ (g14_nbB v).card = 3 := by
  decide +kernel

theorem common_nbr_le_one : ∀ u v : Fin 14, u ≠ v →
    (g14_nbB u ∩ g14_nbB v).card ≤ 1 := by
  decide +kernel

theorem sup_g14_inter (i j : Fin 14) (hij : i ≠ j) (P : Finset (Fin 14)) :
    (sem_g14_nb i ∩ (sem_g14_nb j ∩ P)).card ≤ 1 := by
  have hsub : sem_g14_nb i ∩ (sem_g14_nb j ∩ P) ⊆ g14_nbB i ∩ g14_nbB j := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_inter] at hx
    exact Finset.mem_inter.2 ⟨hx.1, hx.2.1⟩
  exact (Finset.card_le_card hsub).trans (common_nbr_le_one i j hij)

theorem nbr_diff_exists : ∀ u v : Fin 14, u ≠ v → ∃ z : Fin 14, Adj u z ∧ ¬ Adj v z := by
  have h : ∀ u v : Fin 14, u ≠ v → ∃ z : Fin 14, hc_adjB u z = true ∧ hc_adjB v z = false := by
    decide +kernel
  intro u v huv
  obtain ⟨z, h1, h2⟩ := h u v huv
  exact ⟨z, (hc_adjB_iff u z).1 h1, sem_adjB_false.1 h2⟩

theorem g14_nb_inj {i j : Fin 14} (h : sem_g14_nb i = sem_g14_nb j) : i = j := by
  by_contra hne
  obtain ⟨z, hiz, hjz⟩ := nbr_diff_exists i j hne
  have h1 : z ∈ sem_g14_nb i := g14_mem_nb.2 hiz
  rw [h, g14_mem_nb] at h1
  exact hjz h1

def hc_mate (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 10 | 1 => 9 | 2 => 13 | 3 => 7 | 4 => 11 | 5 => 12 | 6 => 8 | 7 => 3 | 8 => 6 | 9 => 1 | 10 => 0 | 11 => 4 | 12 => 5 | _ => 2

theorem hc_match2 : ∀ v : Fin 14, hc_adjB v (hc_mate v) = true ∧ hc_mate (hc_mate v) = v := by
  decide +kernel

def IsCover (S : Finset (Fin 14)) : Prop :=
  ∀ u v : Fin 14, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 14)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

theorem cover_card_ge_seven {S : Finset (Fin 14)} (hcov : IsCover S) : 7 ≤ S.card := by
  have hpair : ∀ v : Fin 14, v ∈ S ∨ hc_mate v ∈ S := fun v =>
    hcov v (hc_mate v) ((hc_adjB_iff v (hc_mate v)).1 (hc_match2 v).1)
  have hsub : (Finset.univ : Finset (Fin 14)) ⊆ S ∪ S.image hc_mate := by
    intro v _
    rcases hpair v with hv | hm
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨hc_mate v, hm, (hc_match2 v).2⟩)
  have h14 : 14 ≤ S.card + (S.image hc_mate).card :=
    (by decide : 14 ≤ (Finset.univ : Finset (Fin 14)).card).trans
      ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  have him : (S.image hc_mate).card ≤ S.card := Finset.card_image_le
  omega

def IsAut (σ : Equiv.Perm (Fin 14)) : Prop :=
  ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v

def aut0_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | _ => 13
def aut0_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | _ => 13
def aut0 : Equiv.Perm (Fin 14) :=
  ⟨aut0_fn, aut0_inv, by decide, by decide⟩
theorem aut0_isAut : IsAut aut0 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut1_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | 8 => 10 | 9 => 9 | 10 => 8 | 11 => 12 | 12 => 11 | _ => 13
def aut1_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | 8 => 10 | 9 => 9 | 10 => 8 | 11 => 12 | 12 => 11 | _ => 13
def aut1 : Equiv.Perm (Fin 14) :=
  ⟨aut1_fn, aut1_inv, by decide, by decide⟩
theorem aut1_isAut : IsAut aut1 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut2_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 4 | 7 => 7 | 8 => 10 | 9 => 13 | 10 => 8 | 11 => 11 | 12 => 12 | _ => 9
def aut2_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 4 | 7 => 7 | 8 => 10 | 9 => 13 | 10 => 8 | 11 => 11 | 12 => 12 | _ => 9
def aut2 : Equiv.Perm (Fin 14) :=
  ⟨aut2_fn, aut2_inv, by decide, by decide⟩
theorem aut2_isAut : IsAut aut2 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut3_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 13 | 10 => 10 | 11 => 12 | 12 => 11 | _ => 9
def aut3_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 13 | 10 => 10 | 11 => 12 | 12 => 11 | _ => 9
def aut3 : Equiv.Perm (Fin 14) :=
  ⟨aut3_fn, aut3_inv, by decide, by decide⟩
theorem aut3_isAut : IsAut aut3 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut4_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 11 | 10 => 10 | 11 => 9 | 12 => 13 | _ => 12
def aut4_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 11 | 10 => 10 | 11 => 9 | 12 => 13 | _ => 12
def aut4 : Equiv.Perm (Fin 14) :=
  ⟨aut4_fn, aut4_inv, by decide, by decide⟩
theorem aut4_isAut : IsAut aut4 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut5_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 6 | 5 => 2 | 6 => 5 | 7 => 7 | 8 => 10 | 9 => 12 | 10 => 8 | 11 => 9 | 12 => 13 | _ => 11
def aut5_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 4 | 7 => 7 | 8 => 10 | 9 => 11 | 10 => 8 | 11 => 13 | 12 => 9 | _ => 12
def aut5 : Equiv.Perm (Fin 14) :=
  ⟨aut5_fn, aut5_inv, by decide, by decide⟩
theorem aut5_isAut : IsAut aut5 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut6_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 4 | 7 => 7 | 8 => 10 | 9 => 11 | 10 => 8 | 11 => 13 | 12 => 9 | _ => 12
def aut6_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 6 | 5 => 2 | 6 => 5 | 7 => 7 | 8 => 10 | 9 => 12 | 10 => 8 | 11 => 9 | 12 => 13 | _ => 11
def aut6 : Equiv.Perm (Fin 14) :=
  ⟨aut6_fn, aut6_inv, by decide, by decide⟩
theorem aut6_isAut : IsAut aut6 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut7_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 12 | 10 => 10 | 11 => 13 | 12 => 9 | _ => 11
def aut7_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 12 | 10 => 10 | 11 => 13 | 12 => 9 | _ => 11
def aut7 : Equiv.Perm (Fin 14) :=
  ⟨aut7_fn, aut7_inv, by decide, by decide⟩
theorem aut7_isAut : IsAut aut7 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut8_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 11 | 5 => 12 | 6 => 13 | 7 => 0 | 8 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | 12 => 5 | _ => 6
def aut8_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 11 | 5 => 12 | 6 => 13 | 7 => 0 | 8 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | 12 => 5 | _ => 6
def aut8 : Equiv.Perm (Fin 14) :=
  ⟨aut8_fn, aut8_inv, by decide, by decide⟩
theorem aut8_isAut : IsAut aut8 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut9_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 11 | 3 => 10 | 4 => 9 | 5 => 13 | 6 => 12 | 7 => 0 | 8 => 3 | 9 => 2 | 10 => 1 | 11 => 5 | 12 => 4 | _ => 6
def aut9_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 9 | 3 => 8 | 4 => 12 | 5 => 11 | 6 => 13 | 7 => 0 | 8 => 1 | 9 => 4 | 10 => 3 | 11 => 2 | 12 => 6 | _ => 5
def aut9 : Equiv.Perm (Fin 14) :=
  ⟨aut9_fn, aut9_inv, by decide, by decide⟩
theorem aut9_isAut : IsAut aut9 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut10_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 12 | 3 => 10 | 4 => 13 | 5 => 9 | 6 => 11 | 7 => 0 | 8 => 3 | 9 => 6 | 10 => 1 | 11 => 4 | 12 => 5 | _ => 2
def aut10_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 13 | 3 => 8 | 4 => 11 | 5 => 12 | 6 => 9 | 7 => 0 | 8 => 1 | 9 => 5 | 10 => 3 | 11 => 6 | 12 => 2 | _ => 4
def aut10 : Equiv.Perm (Fin 14) :=
  ⟨aut10_fn, aut10_inv, by decide, by decide⟩
theorem aut10_isAut : IsAut aut10 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut11_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 13 | 3 => 10 | 4 => 12 | 5 => 11 | 6 => 9 | 7 => 0 | 8 => 1 | 9 => 6 | 10 => 3 | 11 => 5 | 12 => 4 | _ => 2
def aut11_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 13 | 3 => 10 | 4 => 12 | 5 => 11 | 6 => 9 | 7 => 0 | 8 => 1 | 9 => 6 | 10 => 3 | 11 => 5 | 12 => 4 | _ => 2
def aut11 : Equiv.Perm (Fin 14) :=
  ⟨aut11_fn, aut11_inv, by decide, by decide⟩
theorem aut11_isAut : IsAut aut11 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut12_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 9 | 3 => 8 | 4 => 12 | 5 => 11 | 6 => 13 | 7 => 0 | 8 => 1 | 9 => 4 | 10 => 3 | 11 => 2 | 12 => 6 | _ => 5
def aut12_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 11 | 3 => 10 | 4 => 9 | 5 => 13 | 6 => 12 | 7 => 0 | 8 => 3 | 9 => 2 | 10 => 1 | 11 => 5 | 12 => 4 | _ => 6
def aut12 : Equiv.Perm (Fin 14) :=
  ⟨aut12_fn, aut12_inv, by decide, by decide⟩
theorem aut12_isAut : IsAut aut12 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut13_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 11 | 3 => 8 | 4 => 13 | 5 => 9 | 6 => 12 | 7 => 0 | 8 => 3 | 9 => 5 | 10 => 1 | 11 => 2 | 12 => 6 | _ => 4
def aut13_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 11 | 3 => 8 | 4 => 13 | 5 => 9 | 6 => 12 | 7 => 0 | 8 => 3 | 9 => 5 | 10 => 1 | 11 => 2 | 12 => 6 | _ => 4
def aut13 : Equiv.Perm (Fin 14) :=
  ⟨aut13_fn, aut13_inv, by decide, by decide⟩
theorem aut13_isAut : IsAut aut13 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut14_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 12 | 3 => 8 | 4 => 9 | 5 => 13 | 6 => 11 | 7 => 0 | 8 => 3 | 9 => 4 | 10 => 1 | 11 => 6 | 12 => 2 | _ => 5
def aut14_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 12 | 3 => 8 | 4 => 9 | 5 => 13 | 6 => 11 | 7 => 0 | 8 => 3 | 9 => 4 | 10 => 1 | 11 => 6 | 12 => 2 | _ => 5
def aut14 : Equiv.Perm (Fin 14) :=
  ⟨aut14_fn, aut14_inv, by decide, by decide⟩
theorem aut14_isAut : IsAut aut14 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def aut15_fn (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 10 | 2 => 13 | 3 => 8 | 4 => 11 | 5 => 12 | 6 => 9 | 7 => 0 | 8 => 1 | 9 => 5 | 10 => 3 | 11 => 6 | 12 => 2 | _ => 4
def aut15_inv (v : Fin 14) : Fin 14 :=
  match v.val with | 0 => 7 | 1 => 8 | 2 => 12 | 3 => 10 | 4 => 13 | 5 => 9 | 6 => 11 | 7 => 0 | 8 => 3 | 9 => 6 | 10 => 1 | 11 => 4 | 12 => 5 | _ => 2
def aut15 : Equiv.Perm (Fin 14) :=
  ⟨aut15_fn, aut15_inv, by decide, by decide⟩
theorem aut15_isAut : IsAut aut15 := by
  intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel

def autOf (k : Fin 16) : Equiv.Perm (Fin 14) :=
  match k.val with
  | 0 => aut0
  | 1 => aut1
  | 2 => aut2
  | 3 => aut3
  | 4 => aut4
  | 5 => aut5
  | 6 => aut6
  | 7 => aut7
  | 8 => aut8
  | 9 => aut9
  | 10 => aut10
  | 11 => aut11
  | 12 => aut12
  | 13 => aut13
  | 14 => aut14
  | _ => aut15

theorem autOf_isAut (k : Fin 16) : IsAut (autOf k) := by
  fin_cases k
  · exact aut0_isAut
  · exact aut1_isAut
  · exact aut2_isAut
  · exact aut3_isAut
  · exact aut4_isAut
  · exact aut5_isAut
  · exact aut6_isAut
  · exact aut7_isAut
  · exact aut8_isAut
  · exact aut9_isAut
  · exact aut10_isAut
  · exact aut11_isAut
  · exact aut12_isAut
  · exact aut13_isAut
  · exact aut14_isAut
  · exact aut15_isAut

theorem g14Edge_aut (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) (x : Fin 14 → Bool) :
    G14Edge (fun i => x (σ i)) ↔ G14Edge x := by
  simp only [g14Edge_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩
    exact ⟨σ u, σ v, (hσ u v).2 huv, hx, hy⟩
  · rintro ⟨u, v, huv, hx, hy⟩
    refine ⟨σ⁻¹ u, σ⁻¹ v, (hσ (σ⁻¹ u) (σ⁻¹ v)).1 ?_, by simpa using hx, by simpa using hy⟩
    simpa using huv

def hc_rep (idx : Fin 68) : Finset (Fin 14) :=
  match idx.val with
  | 0 => ({0, 1} : Finset (Fin 14))
  | 1 => ({0, 2} : Finset (Fin 14))
  | 2 => ({1, 2} : Finset (Fin 14))
  | 3 => ({1, 3} : Finset (Fin 14))
  | 4 => ({2, 4} : Finset (Fin 14))
  | 5 => ({4, 5} : Finset (Fin 14))
  | 6 => ({0, 7} : Finset (Fin 14))
  | 7 => ({2, 7} : Finset (Fin 14))
  | 8 => ({1, 8} : Finset (Fin 14))
  | 9 => ({4, 8} : Finset (Fin 14))
  | 10 => ({2, 9} : Finset (Fin 14))
  | 11 => ({0, 1, 2} : Finset (Fin 14))
  | 12 => ({0, 1, 3} : Finset (Fin 14))
  | 13 => ({1, 2, 3} : Finset (Fin 14))
  | 14 => ({0, 2, 4} : Finset (Fin 14))
  | 15 => ({1, 2, 4} : Finset (Fin 14))
  | 16 => ({2, 3, 4} : Finset (Fin 14))
  | 17 => ({0, 4, 5} : Finset (Fin 14))
  | 18 => ({1, 4, 5} : Finset (Fin 14))
  | 19 => ({2, 4, 5} : Finset (Fin 14))
  | 20 => ({0, 2, 7} : Finset (Fin 14))
  | 21 => ({2, 4, 7} : Finset (Fin 14))
  | 22 => ({4, 5, 7} : Finset (Fin 14))
  | 23 => ({1, 3, 8} : Finset (Fin 14))
  | 24 => ({1, 4, 8} : Finset (Fin 14))
  | 25 => ({4, 5, 8} : Finset (Fin 14))
  | 26 => ({4, 7, 8} : Finset (Fin 14))
  | 27 => ({0, 2, 9} : Finset (Fin 14))
  | 28 => ({2, 3, 9} : Finset (Fin 14))
  | 29 => ({2, 4, 9} : Finset (Fin 14))
  | 30 => ({0, 1, 2, 3} : Finset (Fin 14))
  | 31 => ({0, 1, 2, 4} : Finset (Fin 14))
  | 32 => ({0, 2, 3, 4} : Finset (Fin 14))
  | 33 => ({1, 2, 3, 4} : Finset (Fin 14))
  | 34 => ({0, 1, 4, 5} : Finset (Fin 14))
  | 35 => ({0, 2, 4, 5} : Finset (Fin 14))
  | 36 => ({1, 2, 4, 5} : Finset (Fin 14))
  | 37 => ({1, 3, 4, 5} : Finset (Fin 14))
  | 38 => ({2, 4, 5, 6} : Finset (Fin 14))
  | 39 => ({0, 2, 4, 7} : Finset (Fin 14))
  | 40 => ({0, 4, 5, 7} : Finset (Fin 14))
  | 41 => ({2, 4, 5, 7} : Finset (Fin 14))
  | 42 => ({1, 3, 4, 8} : Finset (Fin 14))
  | 43 => ({1, 4, 5, 8} : Finset (Fin 14))
  | 44 => ({4, 5, 7, 8} : Finset (Fin 14))
  | 45 => ({0, 2, 3, 9} : Finset (Fin 14))
  | 46 => ({0, 2, 4, 9} : Finset (Fin 14))
  | 47 => ({2, 3, 4, 9} : Finset (Fin 14))
  | 48 => ({0, 2, 7, 9} : Finset (Fin 14))
  | 49 => ({2, 4, 7, 9} : Finset (Fin 14))
  | 50 => ({3, 4, 8, 9} : Finset (Fin 14))
  | 51 => ({1, 3, 8, 10} : Finset (Fin 14))
  | 52 => ({0, 1, 2, 3, 4} : Finset (Fin 14))
  | 53 => ({0, 1, 2, 4, 5} : Finset (Fin 14))
  | 54 => ({0, 1, 3, 4, 5} : Finset (Fin 14))
  | 55 => ({1, 2, 3, 4, 5} : Finset (Fin 14))
  | 56 => ({0, 2, 4, 5, 6} : Finset (Fin 14))
  | 57 => ({1, 2, 4, 5, 6} : Finset (Fin 14))
  | 58 => ({0, 2, 4, 5, 7} : Finset (Fin 14))
  | 59 => ({2, 4, 5, 6, 7} : Finset (Fin 14))
  | 60 => ({1, 3, 4, 5, 8} : Finset (Fin 14))
  | 61 => ({0, 2, 3, 4, 9} : Finset (Fin 14))
  | 62 => ({0, 2, 4, 7, 9} : Finset (Fin 14))
  | 63 => ({0, 1, 2, 3, 4, 5} : Finset (Fin 14))
  | 64 => ({0, 1, 2, 4, 5, 6} : Finset (Fin 14))
  | 65 => ({1, 2, 3, 4, 5, 6} : Finset (Fin 14))
  | 66 => ({0, 2, 4, 5, 6, 7} : Finset (Fin 14))
  | _ => ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 14))

def repMask (idx : Fin 68) : ℕ :=
  match idx.val with
  | 0 => 3
  | 1 => 5
  | 2 => 6
  | 3 => 10
  | 4 => 20
  | 5 => 48
  | 6 => 129
  | 7 => 132
  | 8 => 258
  | 9 => 272
  | 10 => 516
  | 11 => 7
  | 12 => 11
  | 13 => 14
  | 14 => 21
  | 15 => 22
  | 16 => 28
  | 17 => 49
  | 18 => 50
  | 19 => 52
  | 20 => 133
  | 21 => 148
  | 22 => 176
  | 23 => 266
  | 24 => 274
  | 25 => 304
  | 26 => 400
  | 27 => 517
  | 28 => 524
  | 29 => 532
  | 30 => 15
  | 31 => 23
  | 32 => 29
  | 33 => 30
  | 34 => 51
  | 35 => 53
  | 36 => 54
  | 37 => 58
  | 38 => 116
  | 39 => 149
  | 40 => 177
  | 41 => 180
  | 42 => 282
  | 43 => 306
  | 44 => 432
  | 45 => 525
  | 46 => 533
  | 47 => 540
  | 48 => 645
  | 49 => 660
  | 50 => 792
  | 51 => 1290
  | 52 => 31
  | 53 => 55
  | 54 => 59
  | 55 => 62
  | 56 => 117
  | 57 => 118
  | 58 => 181
  | 59 => 244
  | 60 => 314
  | 61 => 541
  | 62 => 661
  | 63 => 63
  | 64 => 119
  | 65 => 126
  | 66 => 245
  | _ => 127

def canonI : Finset (Finset (Fin 14)) := Finset.univ.image hc_rep

theorem hc_rep_of_mem {R : Finset (Fin 14)} (h : R ∈ canonI) :
    ∃ idx : Fin 68, hc_rep idx = R := by
  obtain ⟨idx, -, rfl⟩ := Finset.mem_image.1 h
  exact ⟨idx, rfl⟩

def setMask (S : Finset (Fin 14)) : ℕ :=
  (if (0 : Fin 14) ∈ S then 2 ^ 0 else 0) |||
  (if (1 : Fin 14) ∈ S then 2 ^ 1 else 0) |||
  (if (2 : Fin 14) ∈ S then 2 ^ 2 else 0) |||
  (if (3 : Fin 14) ∈ S then 2 ^ 3 else 0) |||
  (if (4 : Fin 14) ∈ S then 2 ^ 4 else 0) |||
  (if (5 : Fin 14) ∈ S then 2 ^ 5 else 0) |||
  (if (6 : Fin 14) ∈ S then 2 ^ 6 else 0) |||
  (if (7 : Fin 14) ∈ S then 2 ^ 7 else 0) |||
  (if (8 : Fin 14) ∈ S then 2 ^ 8 else 0) |||
  (if (9 : Fin 14) ∈ S then 2 ^ 9 else 0) |||
  (if (10 : Fin 14) ∈ S then 2 ^ 10 else 0) |||
  (if (11 : Fin 14) ∈ S then 2 ^ 11 else 0) |||
  (if (12 : Fin 14) ∈ S then 2 ^ 12 else 0) |||
  (if (13 : Fin 14) ∈ S then 2 ^ 13 else 0)

theorem ite_two_pow_testBit (p : Prop) [Decidable p] (k b : ℕ) :
    (if p then 2 ^ k else 0).testBit b = (decide (k = b) && decide p) := by
  split_ifs with hp <;> simp [Nat.testBit_two_pow, hp]

theorem setMask_testBit (S : Finset (Fin 14)) (i : Fin 14) :
    (setMask S).testBit i.val = decide (i ∈ S) := by
  fin_cases i <;>
    (simp only [setMask, Nat.testBit_or, ite_two_pow_testBit]; simp)

theorem ite_two_pow_lt (p : Prop) [Decidable p] (k : ℕ) (hk : k < 14) :
    (if p then 2 ^ k else 0) < 2 ^ 14 := by
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) hk
  · omega

theorem setMask_lt (S : Finset (Fin 14)) : setMask S < 16384 := by
  change setMask S < 2 ^ 14
  unfold setMask
  repeat (apply Nat.or_lt_two_pow)
  all_goals exact ite_two_pow_lt _ _ (by omega)

theorem setMask_inj {S T : Finset (Fin 14)} (h : setMask S = setMask T) : S = T := by
  ext i
  have h1 := congrArg (fun m => m.testBit i.val) h
  rw [setMask_testBit, setMask_testBit] at h1
  simpa using h1

theorem repMask_eq : ∀ idx : Fin 68, setMask (hc_rep idx) = repMask idx := by
  decide +kernel

def findCanonIdx (m : ℕ) : Option (Fin 68) :=
  match m with
  | 3 => some ⟨0, by decide⟩
  | 5 => some ⟨1, by decide⟩
  | 6 => some ⟨2, by decide⟩
  | 10 => some ⟨3, by decide⟩
  | 20 => some ⟨4, by decide⟩
  | 48 => some ⟨5, by decide⟩
  | 129 => some ⟨6, by decide⟩
  | 132 => some ⟨7, by decide⟩
  | 258 => some ⟨8, by decide⟩
  | 272 => some ⟨9, by decide⟩
  | 516 => some ⟨10, by decide⟩
  | 7 => some ⟨11, by decide⟩
  | 11 => some ⟨12, by decide⟩
  | 14 => some ⟨13, by decide⟩
  | 21 => some ⟨14, by decide⟩
  | 22 => some ⟨15, by decide⟩
  | 28 => some ⟨16, by decide⟩
  | 49 => some ⟨17, by decide⟩
  | 50 => some ⟨18, by decide⟩
  | 52 => some ⟨19, by decide⟩
  | 133 => some ⟨20, by decide⟩
  | 148 => some ⟨21, by decide⟩
  | 176 => some ⟨22, by decide⟩
  | 266 => some ⟨23, by decide⟩
  | 274 => some ⟨24, by decide⟩
  | 304 => some ⟨25, by decide⟩
  | 400 => some ⟨26, by decide⟩
  | 517 => some ⟨27, by decide⟩
  | 524 => some ⟨28, by decide⟩
  | 532 => some ⟨29, by decide⟩
  | 15 => some ⟨30, by decide⟩
  | 23 => some ⟨31, by decide⟩
  | 29 => some ⟨32, by decide⟩
  | 30 => some ⟨33, by decide⟩
  | 51 => some ⟨34, by decide⟩
  | 53 => some ⟨35, by decide⟩
  | 54 => some ⟨36, by decide⟩
  | 58 => some ⟨37, by decide⟩
  | 116 => some ⟨38, by decide⟩
  | 149 => some ⟨39, by decide⟩
  | 177 => some ⟨40, by decide⟩
  | 180 => some ⟨41, by decide⟩
  | 282 => some ⟨42, by decide⟩
  | 306 => some ⟨43, by decide⟩
  | 432 => some ⟨44, by decide⟩
  | 525 => some ⟨45, by decide⟩
  | 533 => some ⟨46, by decide⟩
  | 540 => some ⟨47, by decide⟩
  | 645 => some ⟨48, by decide⟩
  | 660 => some ⟨49, by decide⟩
  | 792 => some ⟨50, by decide⟩
  | 1290 => some ⟨51, by decide⟩
  | 31 => some ⟨52, by decide⟩
  | 55 => some ⟨53, by decide⟩
  | 59 => some ⟨54, by decide⟩
  | 62 => some ⟨55, by decide⟩
  | 117 => some ⟨56, by decide⟩
  | 118 => some ⟨57, by decide⟩
  | 181 => some ⟨58, by decide⟩
  | 244 => some ⟨59, by decide⟩
  | 314 => some ⟨60, by decide⟩
  | 541 => some ⟨61, by decide⟩
  | 661 => some ⟨62, by decide⟩
  | 63 => some ⟨63, by decide⟩
  | 119 => some ⟨64, by decide⟩
  | 126 => some ⟨65, by decide⟩
  | 245 => some ⟨66, by decide⟩
  | 127 => some ⟨67, by decide⟩
  | _ => none

theorem findCanonIdx_some (m : ℕ) (idx : Fin 68) (h : findCanonIdx m = some idx) :
    m = repMask idx := by
  unfold findCanonIdx at h
  split at h <;> cases h <;> rfl

def autMask (k : Fin 16) (m : ℕ) : ℕ :=
  (if m.testBit 0 then 2 ^ (autOf k 0).val else 0) |||
  (if m.testBit 1 then 2 ^ (autOf k 1).val else 0) |||
  (if m.testBit 2 then 2 ^ (autOf k 2).val else 0) |||
  (if m.testBit 3 then 2 ^ (autOf k 3).val else 0) |||
  (if m.testBit 4 then 2 ^ (autOf k 4).val else 0) |||
  (if m.testBit 5 then 2 ^ (autOf k 5).val else 0) |||
  (if m.testBit 6 then 2 ^ (autOf k 6).val else 0) |||
  (if m.testBit 7 then 2 ^ (autOf k 7).val else 0) |||
  (if m.testBit 8 then 2 ^ (autOf k 8).val else 0) |||
  (if m.testBit 9 then 2 ^ (autOf k 9).val else 0) |||
  (if m.testBit 10 then 2 ^ (autOf k 10).val else 0) |||
  (if m.testBit 11 then 2 ^ (autOf k 11).val else 0) |||
  (if m.testBit 12 then 2 ^ (autOf k 12).val else 0) |||
  (if m.testBit 13 then 2 ^ (autOf k 13).val else 0)

theorem autMask_testBit (k : Fin 16) (m : ℕ) (i : Fin 14) :
    (autMask k m).testBit i.val = m.testBit ((autOf k)⁻¹ i).val := by
  have hc : ∀ (j : Fin 14), ((autOf k j).val = i.val) ↔ j = (autOf k)⁻¹ i := by
    intro j
    constructor
    · intro h; exact ((Equiv.eq_symm_apply (autOf k)).2 (Fin.ext h))
    · intro h; exact congrArg Fin.val ((Equiv.eq_symm_apply (autOf k)).1 h)
  have hterm : ∀ (j : Fin 14),
      (if m.testBit j.val = true then 2 ^ (autOf k j).val else 0).testBit i.val =
      (decide (j = (autOf k)⁻¹ i) && m.testBit j.val) := by
    intro j; rw [ite_two_pow_testBit, decide_eq_decide.2 (hc j)]; cases m.testBit j.val <;> rfl
  have hexp : (autMask k m).testBit i.val =
      ((decide ((0 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 0) ||
      (decide ((1 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 1) ||
      (decide ((2 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 2) ||
      (decide ((3 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 3) ||
      (decide ((4 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 4) ||
      (decide ((5 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 5) ||
      (decide ((6 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 6) ||
      (decide ((7 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 7) ||
      (decide ((8 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 8) ||
      (decide ((9 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 9) ||
      (decide ((10 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 10) ||
      (decide ((11 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 11) ||
      (decide ((12 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 12) ||
      (decide ((13 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 13)) := by
    change ((if m.testBit (0 : Fin 14).val = true then 2 ^ (autOf k 0).val else 0) |||
      (if m.testBit (1 : Fin 14).val = true then 2 ^ (autOf k 1).val else 0) |||
      (if m.testBit (2 : Fin 14).val = true then 2 ^ (autOf k 2).val else 0) |||
      (if m.testBit (3 : Fin 14).val = true then 2 ^ (autOf k 3).val else 0) |||
      (if m.testBit (4 : Fin 14).val = true then 2 ^ (autOf k 4).val else 0) |||
      (if m.testBit (5 : Fin 14).val = true then 2 ^ (autOf k 5).val else 0) |||
      (if m.testBit (6 : Fin 14).val = true then 2 ^ (autOf k 6).val else 0) |||
      (if m.testBit (7 : Fin 14).val = true then 2 ^ (autOf k 7).val else 0) |||
      (if m.testBit (8 : Fin 14).val = true then 2 ^ (autOf k 8).val else 0) |||
      (if m.testBit (9 : Fin 14).val = true then 2 ^ (autOf k 9).val else 0) |||
      (if m.testBit (10 : Fin 14).val = true then 2 ^ (autOf k 10).val else 0) |||
      (if m.testBit (11 : Fin 14).val = true then 2 ^ (autOf k 11).val else 0) |||
      (if m.testBit (12 : Fin 14).val = true then 2 ^ (autOf k 12).val else 0) |||
      (if m.testBit (13 : Fin 14).val = true then 2 ^ (autOf k 13).val else 0)).testBit i.val = _
    simp only [Nat.testBit_or, hterm]
    rfl
  rw [hexp]
  generalize (autOf k)⁻¹ i = t
  fin_cases t <;> simp

theorem setMask_image_aut (k : Fin 16) (S : Finset (Fin 14)) :
    setMask (S.image (autOf k)) = autMask k (setMask S) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 14
  · have hL : (setMask (S.image (autOf k))).testBit b =
        decide ((⟨b, hb⟩ : Fin 14) ∈ S.image (autOf k)) :=
      setMask_testBit (S.image (autOf k)) ⟨b, hb⟩
    rw [hL]
    have him : (⟨b, hb⟩ : Fin 14) ∈ S.image (autOf k) ↔ (autOf k)⁻¹ ⟨b, hb⟩ ∈ S := by
      constructor
      · intro hmem
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.1 hmem
        have : x = (autOf k)⁻¹ ⟨b, hb⟩ := by rw [← hxi]; simp
        exact this ▸ hx
      · intro hx; exact Finset.mem_image.2 ⟨(autOf k)⁻¹ ⟨b, hb⟩, hx, by simp⟩
    have hR : (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 14).val =
        decide ((autOf k)⁻¹ ⟨b, hb⟩ ∈ S) := by
      rw [autMask_testBit, setMask_testBit]
    change _ = (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 14).val
    rw [hR, decide_eq_decide]
    exact him
  · have hL : (setMask (S.image (autOf k))).testBit b = false :=
      Nat.testBit_lt_two_pow ((setMask_lt _).trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 14 ≤ b)))
    have hltR : autMask k (setMask S) < 2 ^ 14 := by
      unfold autMask
      repeat (apply Nat.or_lt_two_pow)
      all_goals exact ite_two_pow_lt _ _ (Fin.isLt _)
    have hR : (autMask k (setMask S)).testBit b = false :=
      Nat.testBit_lt_two_pow (hltR.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 14 ≤ b)))
    rw [hL, hR]

def isIndepMask (m : ℕ) : Bool :=
  edgeList.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def pop14 (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0) +
  (if m.testBit 10 then 1 else 0) + (if m.testBit 11 then 1 else 0) +
  (if m.testBit 12 then 1 else 0) + (if m.testBit 13 then 1 else 0)

theorem isIndepMask_of_indep {I : Finset (Fin 14)} (hI : IsIndep I) :
    isIndepMask (setMask I) = true := by
  have hedge : ∀ u v : Fin 14, Adj u v →
      !((setMask I).testBit u.val && (setMask I).testBit v.val) = true := by
    intro u v huv
    rw [setMask_testBit, setMask_testBit]
    by_cases hu : u ∈ I <;> by_cases hv : v ∈ I
    · exact absurd huv (hI u hu v hv)
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
  unfold isIndepMask edgeList
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hedge 0 8 (by decide), hedge 0 10 (by decide), hedge 1 7 (by decide), hedge 1 9 (by decide), hedge 1 13 (by decide), hedge 2 8 (by decide), hedge 2 12 (by decide), hedge 2 13 (by decide), hedge 3 7 (by decide), hedge 3 11 (by decide), hedge 3 12 (by decide), hedge 4 10 (by decide), hedge 4 11 (by decide), hedge 4 13 (by decide), hedge 5 9 (by decide), hedge 5 10 (by decide), hedge 5 12 (by decide), hedge 6 8 (by decide), hedge 6 9 (by decide), hedge 6 11 (by decide)⟩

theorem pop14_eq_card (I : Finset (Fin 14)) : pop14 (setMask I) = I.card := by
  have h1 : I.card = ∑ x ∈ (Finset.univ : Finset (Fin 14)), if x ∈ I then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have huniv : (Finset.univ : Finset (Fin 14)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    decide
  rw [h1, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  dsimp only [pop14]
  rw [show (setMask I).testBit 0 = decide ((0 : Fin 14) ∈ I) from setMask_testBit I 0,
      show (setMask I).testBit 1 = decide ((1 : Fin 14) ∈ I) from setMask_testBit I 1,
      show (setMask I).testBit 2 = decide ((2 : Fin 14) ∈ I) from setMask_testBit I 2,
      show (setMask I).testBit 3 = decide ((3 : Fin 14) ∈ I) from setMask_testBit I 3,
      show (setMask I).testBit 4 = decide ((4 : Fin 14) ∈ I) from setMask_testBit I 4,
      show (setMask I).testBit 5 = decide ((5 : Fin 14) ∈ I) from setMask_testBit I 5,
      show (setMask I).testBit 6 = decide ((6 : Fin 14) ∈ I) from setMask_testBit I 6,
      show (setMask I).testBit 7 = decide ((7 : Fin 14) ∈ I) from setMask_testBit I 7,
      show (setMask I).testBit 8 = decide ((8 : Fin 14) ∈ I) from setMask_testBit I 8,
      show (setMask I).testBit 9 = decide ((9 : Fin 14) ∈ I) from setMask_testBit I 9,
      show (setMask I).testBit 10 = decide ((10 : Fin 14) ∈ I) from setMask_testBit I 10,
      show (setMask I).testBit 11 = decide ((11 : Fin 14) ∈ I) from setMask_testBit I 11,
      show (setMask I).testBit 12 = decide ((12 : Fin 14) ∈ I) from setMask_testBit I 12,
      show (setMask I).testBit 13 = decide ((13 : Fin 14) ∈ I) from setMask_testBit I 13]
  simp only [decide_eq_true_eq]
  omega

theorem g14_canon_all : ∀ mL mR : Fin 128,
    let m := mL.val + 128 * mR.val
    isIndepMask m = true → 2 ≤ pop14 m →
    (findCanonIdx (autMask 0 m)).isSome ||
    (findCanonIdx (autMask 1 m)).isSome ||
    (findCanonIdx (autMask 2 m)).isSome ||
    (findCanonIdx (autMask 3 m)).isSome ||
    (findCanonIdx (autMask 4 m)).isSome ||
    (findCanonIdx (autMask 5 m)).isSome ||
    (findCanonIdx (autMask 6 m)).isSome ||
    (findCanonIdx (autMask 7 m)).isSome ||
    (findCanonIdx (autMask 8 m)).isSome ||
    (findCanonIdx (autMask 9 m)).isSome ||
    (findCanonIdx (autMask 10 m)).isSome ||
    (findCanonIdx (autMask 11 m)).isSome ||
    (findCanonIdx (autMask 12 m)).isSome ||
    (findCanonIdx (autMask 13 m)).isSome ||
    (findCanonIdx (autMask 14 m)).isSome ||
    (findCanonIdx (autMask 15 m)).isSome = true := by
  decide +kernel

theorem exists_aut_canon {I : Finset (Fin 14)} (hI : IsIndep I) (hge : 2 ≤ I.card) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  set m := setMask I with hm
  have hlt : m < 16384 := setMask_lt I
  have hmL : m % 128 < 128 := Nat.mod_lt _ (by decide)
  have hmR : m / 128 < 128 := by omega
  have hsplit : m % 128 + 128 * (m / 128) = m := by omega
  have hall := g14_canon_all ⟨m % 128, hmL⟩ ⟨m / 128, hmR⟩
  dsimp only at hall
  rw [hsplit] at hall
  have hres := hall (isIndepMask_of_indep hI) (by rw [pop14_eq_card]; exact hge)
  have hex : ∃ k : Fin 16, (findCanonIdx (autMask k m)).isSome = true := by
    simp only [Bool.or_eq_true] at hres
    rcases hres with (((((((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12) | h13) | h14) | h15)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
    · exact ⟨6, h6⟩
    · exact ⟨7, h7⟩
    · exact ⟨8, h8⟩
    · exact ⟨9, h9⟩
    · exact ⟨10, h10⟩
    · exact ⟨11, h11⟩
    · exact ⟨12, h12⟩
    · exact ⟨13, h13⟩
    · exact ⟨14, h14⟩
    · exact ⟨15, h15⟩
  obtain ⟨k, hk⟩ := hex
  obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.1 hk
  refine ⟨autOf k, autOf_isAut k, Finset.mem_image.2 ⟨idx, Finset.mem_univ _, ?_⟩⟩
  apply setMask_inj
  rw [repMask_eq, setMask_image_aut, ← hm]
  exact (findCanonIdx_some _ _ hidx).symm

theorem g14_not_empty : ¬ G14Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h

theorem g14_not_single (v : Fin 14) : ¬ G14Edge (fun i => decide (i = v)) := by
  rw [g14Edge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab
  exact adj_irrefl v hab

theorem g14_pair {u v : Fin 14} (h : Adj u v) :
    G14Edge (fun i => decide (i = u) || decide (i = v)) :=
  (g14Edge_iff_adj _).2 ⟨u, v, h, by simp, by simp⟩

theorem g14_essential (i : Fin 14) : ∃ x y : Fin 14 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ G14Edge x ∧ ¬ G14Edge y :=
  ⟨fun j => decide (j = i) || decide (j = hc_mate i), fun j => decide (j = hc_mate i),
   fun j hj => by simp [hj], g14_pair ((hc_adjB_iff i (hc_mate i)).1 (hc_match2 i).1),
   g14_not_single (hc_mate i)⟩

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ G14Edge x

theorem g14_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h08 : Adj (0 : Fin 14) 8 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 14) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (g14_pair h08)⟩
      · exact ⟨fun _ => false, fun h => g14_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g14_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := g14_essential i
      refine ⟨x, y, hxy, fun h => hy ((hC y).1 ?_)⟩
      rw [← h]; exact (hC x).2 hx)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem g14_supp_out {D : Dag} (hD : Correct D) : supp 14 D (outW 14 D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun v hv =>
    g14_not_single v ((hD _).mp (mem_supp.mp hv))

theorem g14_relabel (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) :
    StrictLive 14 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 14 (relabel σ D) = totalSurplus 14 D ∧
      Bplus 14 (relabel σ D) = Bplus 14 D ∧ Bzero 14 (relabel σ D) = Bzero 14 D ∧
      eligSet 14 (relabel σ D) = (eligSet 14 D).image σ ∧
      ineligSet 14 (relabel σ D) = (ineligSet 14 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact g14Edge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  simpa [ineligSet] using h

theorem g14_cover_iff_indep (D : Dag) :
    IsCover (eligSet 14 D) ↔ IsIndep (ineligSet 14 D) := by
  constructor
  · intro hcov u hu v hv huv
    have h1 := Finset.mem_sdiff.mp hu
    have h2 := Finset.mem_sdiff.mp hv
    exact (hcov u v huv).elim h1.2 h2.2
  · intro hind u v huv
    by_contra hc; push Not at hc
    exact hind u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.1⟩)
      v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.2⟩) huv

theorem g14_wlog {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hind : IsIndep (ineligSet 14 D)) (hge : 2 ≤ (ineligSet 14 D).card) :
    ∃ D' : Dag, StrictLive 14 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 14 D' = totalSurplus 14 D ∧
      Bplus 14 D' = Bplus 14 D ∧ Bzero 14 D' = Bzero 14 D ∧
      (ineligSet 14 D').card = (ineligSet 14 D).card ∧
      ineligSet 14 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := exists_aut_canon hind hge
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := g14_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, h8 ▸ hmem⟩
  rw [h8, Finset.card_image_of_injective _ σ.injective]

theorem g14_budget {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 25) :
    totalSurplus 14 D = D.length - 13 ∧ totalSurplus 14 D ≤ 12 := by
  have := surplus_identity h
  exact ⟨by omega, by omega⟩

theorem g14_p_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 25)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ 12 ∧ totalSurplus 14 D ≤ 12 := by
  have h1 := cover_card_ge_seven hcov
  have h2 := elig_le_Bplus h.1 b hb
  have h3 := Bplus_le_total 14 D
  have h4 := (g14_budget h hlen).2
  exact ⟨h1, h2, by omega, h4⟩

theorem g14_inelig_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 25)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    (ineligSet 14 D).Nonempty ∧ 2 ≤ (ineligSet 14 D).card ∧ (ineligSet 14 D).card ≤ 7 := by
  obtain ⟨h7, hp, hB, h12⟩ := g14_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 14 D
  exact ⟨Finset.card_pos.1 (by omega), by omega, by omega⟩

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

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
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

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
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

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
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
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

theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
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
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore

theorem sem_g14_second : ∀ u v : Fin 14, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_g14_gr : sem_Gr (fun u v : Fin 14 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, fun u v hne => nbr_diff_exists u v hne, fun u v =>
    let ⟨a, h1, h2⟩ := sem_g14_second u v
    ⟨a, (hc_adjB_iff u a).1 h1, h2⟩⟩

theorem sem_g14_comp {D : Dag} (hD : Correct D) :
    sem_Comp 14 (fun u v : Fin 14 => Adj u v) D :=
  fun x => (hD x).trans (g14Edge_iff_adj x)

theorem exists_pureBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, PureBranch 14 D b :=
  sem_exists_pureBranch sem_g14_gr h.1 (sem_g14_comp hD)

theorem elig_isCover {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    IsCover (eligSet 14 D) :=
  fun _ _ huv => sem_elig_cover sem_g14_gr h (sem_g14_comp hD) huv

theorem g14_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x)
    (hsize : C.size ≤ 25) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 25 ∧
      totalSurplus 14 D ≤ 12 ∧ 2 ≤ (ineligSet 14 D).card ∧ ineligSet 14 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := g14_normalize C hmono hC
  have hlen : D0.length ≤ 25 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h0 hD0
  have hcov := elig_isCover h0 hD0
  obtain ⟨-, hge2, -⟩ := g14_inelig_bounds h0 hlen b hb hcov
  obtain ⟨D, h1, h2, h3, -, -, -, -, h8⟩ :=
    g14_wlog h0 hD0 ((g14_cover_iff_indep D0).mp hcov) hge2
  have hlen' : D.length ≤ 25 := by omega
  obtain ⟨b', hb'⟩ := exists_pureBranch h1 h2
  obtain ⟨-, hge2', -⟩ := g14_inelig_bounds h1 hlen' b' hb' (elig_isCover h1 h2)
  exact ⟨D, h1, h2, hlen', (g14_budget h1 hlen').2, hge2', h8⟩

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

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

theorem sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => Finset.disjoint_left.mp hd h (by simp),
    fun h => Finset.disjoint_left.mp hd h (by simp)⟩

theorem sem_antichain (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x a : Fin n}
    (hxa : x ≠ a) : ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) := by
  obtain ⟨z, hxz, haz⟩ := hG.2.2.1 x a hxa
  obtain ⟨e, he, h1, -⟩ := sem_cover_free hG hS hC (a := a) (b := a) (hG.2.1 a) hxz
    (fun h => haz (hG.1 _ _ h)) (fun h => haz (hG.1 _ _ h))
  exact ⟨e, he, h1⟩

theorem sem_free_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) (hu : u ∈ eligSet n D) (hv : v ∈ eligSet n D) :
    ∃ j, j < D.length ∧ tag D j = true ∧ supp n D (n + j) = ∅ ∧
      (supp n D (opA D j)).Nonempty ∧ (supp n D (opB D j)).Nonempty ∧
      val D (sem_two u v) (n + j) = true ∧
      ∀ i ∈ ineligSet n D, i ∉ supp n D (opA D j) ∧ i ∉ supp n D (opB D j) := by
  classical
  have hS := h.1
  have hex : ∃ w, val D (sem_two u v) w = true ∧ supp n D w = ∅ :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), sem_supp_out hG hC⟩
  obtain ⟨hw1, hw2⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true → (supp n D a).Nonempty := by
    intro a ha hva
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc => Nat.find_min hex ha ⟨hva, hc⟩
  generalize Nat.find hex = w at hw1 hw2 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hs : supp n D w = {⟨w, by omega⟩} := supp_input D ⟨w, by omega⟩
    rw [hs] at hw2
    exact Finset.singleton_ne_empty _ hw2
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  have hdead : ∀ w', w' < n + j → ∀ i ∈ ineligSet n D, i ∈ supp n D w' →
      val D (sem_two u v) w' = false := by
    intro w'
    induction w' using Nat.strong_induction_on with
    | _ w' ih =>
      intro hlt' i hi hiw
      have hpure := sem_inelig_pure hG hS hC hi hiw
      by_cases hn' : w' < n
      · have hs : supp n D w' = {⟨w', hn'⟩} := supp_input D ⟨w', hn'⟩
        rw [hs, Finset.mem_singleton] at hiw
        rw [val_input D _ w' hn', ← hiw]
        have hiu : i ≠ u := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hu)
        have hiv : i ≠ v := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hv)
        simp [sem_two, hiu, hiv]
      · obtain ⟨j', rfl⟩ : ∃ j', w' = n + j' := ⟨w' - n, by omega⟩
        have hj' : j' < D.length := by omega
        obtain ⟨ha', hb', -⟩ := hS j' hj'
        have ht' := sem_inelig_or hG h hC hi hj' hiw
        have hop : ∀ a, a < n + j' → supp n D a ⊆ {i} → val D (sem_two u v) a = false := by
          intro a hlt2 hsub
          by_cases hia : i ∈ supp n D a
          · exact ih a hlt2 (by omega) i hi hia
          · by_contra hc
            rw [Bool.not_eq_false] at hc
            obtain ⟨q, hq⟩ := hmin a (by omega) hc
            have := hsub hq
            rw [Finset.mem_singleton] at this
            exact hia (this ▸ hq)
        rw [sem_supp_or hS hj' ht'] at hpure
        rw [val_gate hS _ j' hj', ht', gop_false,
          hop _ ha' (by rw [← hpure]; exact Finset.subset_union_left),
          hop _ hb' (by rw [← hpure]; exact Finset.subset_union_right)]
        rfl
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1
    simp only [gop_false, Bool.or_eq_true] at hw1
    rw [sem_supp_or hS hj ht, Finset.union_eq_empty] at hw2
    rcases hw1 with h1 | h1
    · have := hmin _ ha h1
      rw [hw2.1] at this
      exact Finset.not_nonempty_empty this
    · have := hmin _ hb h1
      rw [hw2.2] at this
      exact Finset.not_nonempty_empty this
  · rw [ht] at hw1
    simp only [gop_true, Bool.and_eq_true] at hw1
    refine ⟨j, hj, ht, hw2, hmin _ ha hw1.1, hmin _ hb hw1.2, hval, fun i hi => ⟨?_, ?_⟩⟩
    · intro hc
      have := hdead _ ha i hi hc
      rw [hw1.1] at this
      exact Bool.noConfusion this
    · intro hc
      have := hdead _ hb i hi hc
      rw [hw1.2] at this
      exact Bool.noConfusion this

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

theorem sem_all_but_one {α : Type} (J : Finset α) (P : α → Prop)
    (h : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → P i ∨ P j) :
    ∃ J' ⊆ J, J.card ≤ J'.card + 1 ∧ ∀ i ∈ J', P i := by
  classical
  refine ⟨J.filter P, Finset.filter_subset _ _, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have h1 : (J.filter (fun i => ¬ P i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rcases h a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab with h1 | h1
    · exact (Finset.mem_filter.mp ha).2 h1
    · exact (Finset.mem_filter.mp hb).2 h1
  have h2 := Finset.card_filter_add_card_filter_not (s := J) P
  omega

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

theorem sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩

theorem sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
    b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep hrest ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest'⟩
      · have h1 := sem_step_lt hS hstep.1
        have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'

theorem sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b t : ℕ)
    (hdom : b = v.val ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t := by
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

theorem sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
    (hq : Relation.ReflTransGen (sem_step n D) a q) :
    Relation.ReflTransGen (sem_step n D) c q ∨ (sem_Chain n D q c ∧ q ≠ c) := by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hq => Or.inl hq
  | @head a a' hstep hrest ih =>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'', hs, hrest'⟩
    · right
      have h1 := sem_step_lt hS hstep.1
      have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
      refine ⟨?_, by omega⟩
      rw [← heq]
      exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'' := sem_step_unique hstep.1 hs hstep.2
      subst hcc
      exact ih hrest'

theorem sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : sem_Chain n D v.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
    val D x (src D (j, s)) = val D y (src D (j, s)) := by
  by_contra hne
  have hp : Relation.ReflTransGen (sem_step n D) v.val (src D (j, s)) :=
    sem_rtg_mono (fun _ _ h => h.1) (sem_changed_path hS x y v hxy _ hne)
  have hstepc : sem_step n D (src D (j, !s)) (n + j) := sem_step_src hj (!s)
  have hstepq : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
  have hlt1 := sem_src_lt hS hj s
  have hlt2 := sem_src_lt hS hj (!s)
  rcases sem_chain_fork hS hch hp with h1 | ⟨h1, h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c', hs, hrest⟩
    · exact sem_src_ne hS hj s heq.symm
    · have hcc : n + j = c' := sem_step_unique hstepc hs hf
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q', hs, hrest⟩
    · exact h2 heq
    · have hcc : n + j = q' := sem_step_unique hstepq hs.1 hs.2
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h.1) hrest
      omega

theorem sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne

theorem sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind

theorem sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hsupp⟩ := sem_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := Finset.mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, Finset.mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := Finset.mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (Finset.mem_inter.mp this).1

theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

theorem sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩

theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

theorem sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

theorem sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

theorem sem_bzero_unique (hS : Strict n D) (hB0 : Bzero n D ≤ 1) {b b' : ℕ}
    (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) (hf' : 2 ≤ fanout D b')
    (he' : supp n D b' = ∅) : b = b' := by
  by_contra hne
  have hsub : ({b, b'} : Finset ℕ) ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact sem_bzero_mem hS hf he
    · exact sem_bzero_mem hS hf' he'
  have h1 := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at h1
  unfold Bzero surplusOn at hB0
  omega

theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

theorem sem_noempty_chain_out (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) :=
  sem_noempty_unique hG h hC hB0 hi
    (live_reaches_out h i.val (by have := i.isLt; omega))

theorem sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i : Fin n}
    (hch : sem_Chain n D i.val (outW n D)) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, -, hc, hsupp⟩ := sem_exact_at (G := G) hS i (outW n D) hch Bs
    (fun S hS1 hS2 => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hc, hsupp⟩

theorem sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (Finset.mem_filter.mp ha).2 hia
    · exact hBs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine sem_exact_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Finset.mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩

theorem sem_shared_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D ≤ 1) (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b)
    {i j : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hji : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D i.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a)) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D j.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G j a)) := by
  have hS := h.1
  rcases sem_inelig_reach hG h hC hi with h1 | ⟨b, hb1, hb2, hb3⟩
  · exact Or.inl (sem_exact_nbhd hG hS hC Bs hBs h1)
  · rcases sem_inelig_reach hG h hC hj with h1 | ⟨b', hb1', hb2', hb3'⟩
    · exact Or.inr (sem_exact_nbhd hG hS hC Bs hBs h1)
    · have hbb : b' = b := sem_bzero_unique hS hB0 hb2' hb3' hb2 hb3
      rw [hbb] at hb1'
      obtain ⟨k, s, hk, ht, -, hc, hsupp⟩ := sem_shared_exact hG hS hC Bs hBs hb1
        (sem_chain_dom hS hb1') hji
      exact Or.inl ⟨k, s, hk, ht, hc, hsupp⟩

theorem sem_full_support (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : sem_W n D i = {e})
    (hor : ∀ j, Relation.ReflTransGen (sem_step n D) (n + e.1) (n + j) → j ≠ e.1 →
      tag D j = false) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  obtain ⟨e0, hj0, ht0, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi
  have hee : e = e0 := Finset.singleton_injective (he.symm.trans hx0)
  subst hee
  obtain ⟨g, s⟩ := e
  intro t
  refine ⟨fun ht => ?_, fun ht => hnb0 t ht⟩
  by_contra hnt
  have hgate : val D (sem_two i t) (n + g) = true := by
    rw [sem_val_gate_src hS _ hj0 s, ht0, gop_true, Bool.and_eq_true]
    exact ⟨sem_val_of_supp hS (by rw [hsrc0]; exact Finset.mem_singleton_self i)
      (by simp [sem_two]), sem_val_of_supp hS ht (by simp [sem_two])⟩
  have hall : ∀ c, Relation.ReflTransGen (sem_step n D) (n + g) c →
      val D (sem_two i t) c = true := by
    intro c hc
    induction hc with
    | refl => exact hgate
    | tail hab hbc ih =>
      obtain ⟨j, s', hj, rfl, rfl⟩ := sem_step_iff.mp hbc
      have hne : j ≠ g := by
        have := sem_rtg_le hS (fun _ _ h => h) hab
        have := sem_src_lt hS hj s'
        omega
      rw [sem_val_gate_src hS _ hj s', hor j (Relation.ReflTransGen.tail hab hbc) hne,
        gop_false, ih]
      rfl
  have hout := hall _ (live_reaches_out h (n + g) (by omega))
  obtain ⟨u, v, huv, hu, hv⟩ := (hC _).mp hout
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at huv
  · exact hG.2.1 _ huv
  · exact hnt huv
  · exact hnt (hG.1 _ _ huv)
  · exact hG.2.1 _ huv

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩

theorem sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_diff]

theorem sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ eligSet n D) :
    surplusOn D (carrierDiff n D x y) = 1 + ((residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
  have h1 : surplusOn D (carrierDiff n D x y) =
      ((units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
    rw [sb_card_units_filter n D (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      exact sem_mem_diff.mpr hw.2
    · have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, sem_mem_diff.mp hw⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) =
      {(⟨b x, 0⟩ : Σ _ : ℕ, ℕ)} ∪ (residualUnits n D b).filter
        (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · left
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
        have hxv := hu.2.1
        rw [(hb v hv).2, Finset.mem_singleton] at hxv
        rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1, ⟨x, hu.2.1⟩⟩, hr⟩, hu.2⟩
    · rintro (rfl | hu)
      · have hbx := hb x hx
        refine ⟨(Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩))).1, ?_, ?_⟩
        · rw [hbx.2]; exact Finset.mem_singleton_self x
        · rw [hbx.2, Finset.mem_singleton]; exact fun hc => hxy hc.symm
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∉ (residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    intro hc
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h1, h2, Finset.singleton_union, Finset.card_insert_of_notMem h3]
  omega

theorem sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
    (hw : x ∈ supp n D w ∧ y ∈ supp n D w) :
    ∃ j s, j < D.length ∧ tag D j = false ∧ x ∈ supp n D (n + j) ∧ y ∈ supp n D (n + j) ∧
      x ∈ supp n D (src D (j, s)) ∧ y ∉ supp n D (src D (j, s)) ∧
      y ∈ supp n D (src D (j, !s)) ∧ x ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ u, x ∈ supp n D u ∧ y ∈ supp n D u := ⟨w, hw⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → ¬ (x ∈ supp n D u ∧ y ∈ supp n D u) :=
    fun u hu => Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt := sem_supp_lt h1
  have hn : n ≤ f := by
    by_contra hc
    have hs : supp n D f = {⟨f, by omega⟩} := supp_input D ⟨f, by omega⟩
    rw [hs, Finset.mem_singleton] at h1 h2
    exact hxy (h1.trans h2.symm)
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  cases ht : tag D j
  · have h1' := h1
    have h2' := h2
    rw [sem_supp_or hS hj ht, Finset.mem_union] at h1' h2'
    refine ⟨j, ?_⟩
    rcases h1' with hxa | hxb
    · have hya : y ∉ supp n D (opA D j) := fun hc => hna ⟨hxa, hc⟩
      have hyb : y ∈ supp n D (opB D j) := h2'.resolve_left hya
      exact ⟨false, hj, ht, h1, h2, by simpa [src] using hxa, by simpa [src] using hya,
        by simpa [src] using hyb, by simpa [src] using fun hc => hnb ⟨hc, hyb⟩⟩
    · have hyb : y ∉ supp n D (opB D j) := fun hc => hnb ⟨hxb, hc⟩
      have hya : y ∈ supp n D (opA D j) := h2'.resolve_right hyb
      exact ⟨true, hj, ht, h1, h2, by simpa [src] using hxb, by simpa [src] using hyb,
        by simpa [src] using hya, by simpa [src] using fun hc => hna ⟨hc, hya⟩⟩
  · exfalso
    rw [sem_supp_and hS hj ht, Finset.mem_inter] at h1 h2
    exact hna ⟨h1.1, h2.1⟩

theorem sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c z : Fin n} (hxc : x ≠ c)
    (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    surplusOn D (carrierDiff n D x c) = 1 ∧ merges n D (carrierDiff n D x c) = ∅ ∧
      (exitArcs n D (carrierDiff n D x c)).card = 2 ∧
      ∃ e ∈ exitArcs n D (carrierDiff n D x c), tag D e.1 = false ∧ c ∈ supp n D (n + e.1) := by
  have hS := h.1
  have hsur : surplusOn D (carrierDiff n D x c) = 1 := by
    rw [sem_surplus_diff hS b hb hxc hx, Finset.filter_eq_empty_iff.mpr
      (fun u hu hc => hc.2 (hres u hu hc.1)), Finset.card_empty]
  have hfl := carrier_flow_diff h x c hxc
    (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  rw [hsur] at hfl
  obtain ⟨j1, s1, hj1, ht1, hx1, hc1, hxs1, hcs1, -, -⟩ := sem_first_joint hS hxc hw
  have he1 : (j1, s1) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj1, ⟨hxs1, hcs1⟩, fun hc => hc.2 hc1⟩
  have hA : ∀ u ∈ ({c, z} : Finset (Fin n)), ∀ v ∈ ({c, z} : Finset (Fin n)), ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc => hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hA x ⟨z, by simp, hxz⟩
  have he2 : (j2, s2) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj2, ⟨hx2, fun hc => Finset.disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc => hn2 hc.1⟩
  have hne : (j1, s1) ≠ (j2, s2) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    exact hn2 (heq.1 ▸ hx1)
  have h2 : 2 ≤ (exitArcs n D (carrierDiff n D x c)).card :=
    Finset.one_lt_card.mpr ⟨_, he1, _, he2, hne⟩
  exact ⟨hsur, Finset.card_eq_zero.mp (by omega), by omega, (j1, s1), he1, ht1, hc1⟩

theorem sem_and_sibling_nbrs (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {j : ℕ} (hj : j < D.length) (s : Bool) (ht : tag D j = true)
    (hch : sem_Chain n D i.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (hout : n + j ≤ outW n D) {a : Fin n} (hia : G i a) : a ∈ supp n D (src D (j, s)) := by
  have hchg : sem_Chain n D i.val (n + j) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hj (!s), hf⟩
  have hx0 : val D (single a) (outW n D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact sem_single_no_edge hG a ((hC _).mp hc)
  have hy1 : val D (sem_ins i (single a)) (outW n D) = true :=
    (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
  have hgy : val D (sem_ins i (single a)) (n + j) = true := by
    by_contra hc2
    rw [Bool.not_eq_true] at hc2
    have hgx : val D (single a) (n + j) = false := by
      by_contra hc3
      rw [Bool.not_eq_false] at hc3
      rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
      exact Bool.noConfusion hc2
    have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (single a)) (n + j) (outW n D)
      (sem_chain_dom_at hS hchg hout) (hgx.trans hc2.symm)
    rw [hx0, hy1] at h2
    exact Bool.false_ne_true h2
  rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
  have hind := sem_sibling_indep hS i hj s hch hf _ _ (sem_ins_agree i (single a))
  rw [hgy.1] at hind
  exact mem_supp.mpr hind

end SemDiff

def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2

def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1

def sup_CostOK (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ × Bool) ⊕ ℕ) : Prop :=
  Sum.elim (fun e => e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2)
    (fun j => j ∈ merges n D (carrierT n D P) ∧ (supp n D (n + j) ∩ P).card = 1) c

section SupMask

variable {n : ℕ} {D : Dag}

theorem sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩

theorem sup_occ_sub {P M : Finset (Fin n)} (h : sup_Occ n D P M) : M ⊆ P := by
  obtain ⟨w, rfl⟩ := h
  exact Finset.inter_subset_right

theorem sup_mem_carrier {P : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D P ↔ (supp n D w ∩ P).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv⟩ := h
    exact ⟨sem_supp_lt (Finset.mem_inter.mp hv).1, v, hv⟩

theorem sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

theorem sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact Finset.mem_image.mpr ⟨j, hj, hjM⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem sup_triple_parent (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 7)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) ∨
      (∃ A B, A ≠ B ∧ sup_Occ n D P A ∧ sup_Occ n D P B ∧ A.card = 5 ∧ B.card = 5 ∧
        T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, hj, -, hjT, -, -, hpar⟩ := sem_first_mask hS P T (by omega) w hw
  have hoA : sup_Occ n D P (supp n D (opA D j) ∩ P) := sup_occ_wire P _
  have hoB : sup_Occ n D P (supp n D (opB D j) ∩ P) := sup_occ_wire P _
  rcases hpar with ⟨ht, hA, hB⟩ | ⟨-, hA, hB, hun, -, -⟩
  · have hAB : (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) = T := by
      rw [← hjT, sem_supp_and hS hj ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    generalize supp n D (opA D j) ∩ P = A at hoA hA hAB
    generalize supp n D (opB D j) ∩ P = B at hoB hB hAB
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hu : (A ∪ B).card ≤ 7 :=
      (Finset.card_le_card (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    by_cases h4 : A.card = 4
    · exact Or.inr (Or.inl ⟨A, hoA, h4, hA.subset⟩)
    by_cases h4' : B.card = 4
    · exact Or.inr (Or.inl ⟨B, hoB, h4', hB.subset⟩)
    refine Or.inr (Or.inr ⟨A, B, ?_, hoA, hoB, by omega, by omega, hA.subset, hB.subset, hAB⟩)
    intro hEq
    rw [hEq, Finset.inter_self] at hAB
    rw [hAB] at hcB
    omega
  · generalize supp n D (opA D j) ∩ P = A at hoA hA hun
    generalize supp n D (opB D j) ∩ P = B at hoB hB hun
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hc := Finset.card_union_le A B
    rw [hun] at hc
    by_cases h2 : A.card = 2
    · exact Or.inl ⟨A, hoA, h2, hA.subset⟩
    · exact Or.inl ⟨B, hoB, by omega, hB.subset⟩

theorem sup_triple_parent_six (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 6)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) := by
  rcases sup_triple_parent hS (by omega) hT h with h2 | h4 |
    ⟨A, B, -, hoA, hoB, hcA, hcB, -, -, hAB⟩
  · exact Or.inl h2
  · exact Or.inr h4
  · exfalso
    have hu := (Finset.card_le_card
      (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    omega

theorem sup_pair_unique {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A ⊆ T)
    (h2 : A ⊆ T') (hint : T ≠ T' → (T ∩ T').card ≤ 1) : T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.subset_inter h1 h2)
  have h4 := hint hne
  omega

theorem sup_four_unique {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T ⊆ A) (h2 : T' ⊆ A) (hint : T ≠ T' → (T ∩ T').card ≤ 1) :
    T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.union_subset h1 h2)
  have h4 := Finset.card_union_add_card_inter T T'
  have h5 := hint hne
  omega

theorem sup_five_cap {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h3 : T3.card = 3) (hA : A.card ≤ 5) (s1 : T1 ⊆ A) (s2 : T2 ⊆ A) (s3 : T3 ⊆ A)
    (i12 : (T1 ∩ T2).card ≤ 1) (i13 : (T1 ∩ T3).card ≤ 1) (i23 : (T2 ∩ T3).card ≤ 1) :
    False := by
  have hu := Finset.card_le_card (Finset.union_subset (Finset.union_subset s1 s2) s3)
  have e1 := Finset.card_union_add_card_inter T1 T2
  have e2 := Finset.card_union_add_card_inter (T1 ∪ T2) T3
  have e3 : ((T1 ∪ T2) ∩ T3).card ≤ (T1 ∩ T3).card + (T2 ∩ T3).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

theorem sup_aux_exists (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) :
    ∃ Aux : Finset (Finset (Fin n)), L.card ≤ Aux.card ∧ ∀ A ∈ Aux, sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) := by
  classical
  refine ⟨P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)), ?_,
    fun A hA => (Finset.mem_filter.mp hA).2⟩
  generalize hAux : P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)) = Aux
  have hmem : ∀ A, sup_Occ n D P A →
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) → A ∈ Aux := by
    intro A h1 h2
    rw [← hAux]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (sup_occ_sub h1), h1, h2⟩
  have hprop : ∀ A ∈ Aux, (A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5 := by
    intro A hA
    rw [← hAux] at hA
    exact (Finset.mem_filter.mp hA).2.2
  have hrow : ∀ T ∈ L, 2 ≤ ∑ A ∈ Aux,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) := by
    intro T hT
    rcases sup_triple_parent hS hP (h3 T hT).1 (h3 T hT).2 with
      ⟨A, ho, hc, hs⟩ | ⟨A, ho, hc, hs⟩ | ⟨A, B, hne, hoA, hoB, hcA, hcB, hsA, hsB, -⟩
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inl ⟨hc, T, hT, hs⟩)))
      simp [hc, hs]
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inr (Or.inl hc))))
      simp [hc, hs]
    · have hsub : ({A, B} : Finset (Finset (Fin n))) ⊆ Aux := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem _ hoA (Or.inr (Or.inr hcA))
        · exact hmem _ hoB (Or.inr (Or.inr hcB))
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_pair hne]
      simp [hcA, hcB, hsA, hsB]
  have hcol : ∀ A ∈ Aux, ∑ T ∈ L,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) ≤ 2 := by
    intro A hA
    by_cases h5 : A.card = 5
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) = (L.filter (fun T => T ⊆ A)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      by_contra hgt
      obtain ⟨T1, T2, T3, m1, m2, m3, n12, n13, n23⟩ :=
        Finset.two_lt_card_iff.mp (show 2 < (L.filter (fun T => T ⊆ A)).card by omega)
      rw [Finset.mem_filter] at m1 m2 m3
      exact sup_five_cap (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
        (hint _ m1.1 _ m2.1 n12) (hint _ m1.1 _ m3.1 n13) (hint _ m2.1 _ m3.1 n23)
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) =
          2 * (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      have hle : (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro T hT T' hT'
        rw [Finset.mem_filter] at hT hT'
        have c3 := (h3 T hT.1).1
        have c3' := (h3 T' hT'.1).1
        rcases hprop A hA with ⟨h2, -⟩ | h4 | h5'
        · have e1 : A ⊆ T := hT.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : A ⊆ T' := hT'.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_pair_unique h2 e1 e2 (hint T hT.1 T' hT'.1)
        · have e1 : T ⊆ A := hT.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : T' ⊆ A := hT'.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_four_unique c3 c3' h4 e1 e2 (hint T hT.1 T' hT'.1)
        · exact absurd h5' h5
      omega
  have h1 := Finset.card_nsmul_le_sum L _ 2 hrow
  have h2 := Finset.sum_le_card_nsmul Aux _ 2 hcol
  rw [Finset.sum_comm] at h1
  simp only [smul_eq_mul] at h1 h2
  omega

theorem sup_charge (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1)
    (X : Finset (Finset (Fin n)))
    (hX : ∀ M ∈ X, sup_Occ n D P M ∧ 2 ≤ M.card ∧ M ∉ L ∧ M.card ≠ 4 ∧ M.card ≠ 5 ∧
      (M.card = 2 → ∀ T ∈ L, ¬ M ⊆ T)) :
    2 * L.card + X.card ≤ (sup_big n D P).card := by
  classical
  obtain ⟨Aux, hcard, hAux⟩ := sup_aux_exists hS hP L h3 hint
  have hd1 : Disjoint L Aux := by
    rw [Finset.disjoint_left]
    intro T hT hTA
    have := (h3 T hT).1
    rcases (hAux T hTA).2 with ⟨h, -⟩ | h | h <;> omega
  have hd2 : Disjoint (L ∪ Aux) X := by
    rw [Finset.disjoint_left]
    intro M hM hMX
    obtain ⟨-, -, hnL, hn4, hn5, hno⟩ := hX M hMX
    rcases Finset.mem_union.mp hM with h | h
    · exact hnL h
    · rcases (hAux M h).2 with ⟨h2, T, hT, hs⟩ | h4 | h5
      · exact hno h2 T hT hs
      · exact hn4 h4
      · exact hn5 h5
  have hle := sup_card_le_big hS P ((L ∪ Aux) ∪ X) (by
    intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨by have := (h3 M h).1; omega, (h3 M h).2⟩
      · refine ⟨?_, (hAux M h).1⟩
        rcases (hAux M h).2 with ⟨h, -⟩ | h | h <;> omega
    · exact ⟨(hX M h).2.1, (hX M h).1⟩)
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hle
  omega

theorem sup_wit_exists {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {P U X : Finset (Fin n)} (hUP : U ⊆ P)
    (hU : U.card ≤ 2 ∨ (U.card = 3 ∧ ¬ sup_Occ n D P U))
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G a b) (hPX : P \ U ⊆ X) {f : Fin n} (hf : f ∈ U)
    (hnb : ∃ a ∈ X, G f a) : ∃ e, sup_Wit n D P U f e := by
  obtain ⟨j, s, hj, ht, h1, h2, hd⟩ := sem_exposure hG hS hC X hX f hnb
  have hsub : supp n D (src D (j, s)) ∩ P ⊆ U := by
    intro v hv
    rw [Finset.mem_inter] at hv
    by_contra hvU
    exact Finset.disjoint_left.mp hd hv.1 (hPX (Finset.mem_sdiff.mpr ⟨hv.2, hvU⟩))
  refine ⟨(j, s), hj, ht, hUP hf, h1, h2, hsub, ?_⟩
  rcases hU with hU | ⟨hU3, hmiss⟩
  · exact (Finset.card_le_card hsub).trans hU
  · have hne : supp n D (src D (j, s)) ∩ P ≠ U := fun h => hmiss ⟨_, h⟩
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega

theorem sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_erase, Finset.mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩

theorem sup_wit_single {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e)
    (hno : ∀ M, M ⊆ U → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M) :
    supp n D (src D e) ∩ P = {f} := by
  obtain ⟨-, -, hfP, h1, -, hsub, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  have hc2 : (supp n D (src D e) ∩ P).card ≠ 2 :=
    fun h2 => hno _ hsub h2 hfm (sup_occ_wire P _)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hfm)
    (by rw [Finset.card_singleton]; omega)).symm

theorem sup_cost_inl {P : Finset (Fin n)} {e e0 : ℕ × Bool}
    (h : sup_cost n D P e = Sum.inl e0) : e = e0 ∧ supp n D (n + e.1) ∩ P = ∅ := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h, h0⟩

theorem sup_cost_inr {P : Finset (Fin n)} {e : ℕ × Bool} {j : ℕ}
    (h : sup_cost n D P e = Sum.inr j) : e.1 = j ∧ (supp n D (n + e.1) ∩ P).Nonempty := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h, Finset.nonempty_iff_ne_empty.mpr h0⟩

theorem sup_cost_ok (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) : sup_CostOK n D P (sup_cost n D P e) := by
  have hout := sup_wit_out hS h
  obtain ⟨hj, ht, hfP, h1, -, -, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  unfold sup_cost
  split_ifs with h0
  · show e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2
    refine ⟨?_, hc⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr ⟨f, hfm⟩, ?_⟩
    rw [sup_mem_carrier, h0]
    exact Finset.not_nonempty_empty
  · show e.1 ∈ merges n D (carrierT n D P) ∧ (supp n D (n + e.1) ∩ P).card = 1
    have hne : (supp n D (n + e.1) ∩ P).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    have hle := Finset.card_le_card hout
    rw [Finset.card_erase_of_mem hfm] at hle
    have hpos := Finset.card_pos.mpr hne
    refine ⟨?_, by omega⟩
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    have hA := sem_supp_and_sub hS hj ht false hv.1
    have hB := sem_supp_and_sub hS hj ht true hv.1
    rw [sb_src_false] at hA
    rw [sb_src_true] at hB
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr hv⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hA, hv.2⟩⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hB, hv.2⟩⟩⟩

theorem sup_wit_same_pos (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e)
    (hne : (supp n D (n + e.1) ∩ P).Nonempty) : f = f' := by
  by_contra hff
  obtain ⟨q, hq⟩ := hne
  have h1 := sup_wit_out hS h hq
  have h2 := sup_wit_out hS h' hq
  rw [Finset.mem_erase] at h1 h2
  have hsub : ({q, f, f'} : Finset (Fin n)) ⊆ supp n D (src D e) ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact h1.2
    · exact Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
    · exact Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  have hc := Finset.card_le_card hsub
  have h3 : ({q, f, f'} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.1, h2.1⟩
  have := h.2.2.2.2.2.2
  omega

theorem sup_cost_ne_of_disjoint (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hd : Disjoint U U') : sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
  by_cases h0 : supp n D (n + e.1) ∩ P = ∅
  · have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
    rw [hc] at heq
    have he := (sup_cost_inl heq.symm).1
    subst he
    exact Finset.disjoint_left.mp hd (h.2.2.2.2.2.1 hfm) (h'.2.2.2.2.2.1 hfm)
  · have hc : sup_cost n D P e = Sum.inr e.1 := by simp [sup_cost, h0]
    rw [hc] at heq
    have he := (sup_cost_inr heq.symm).1
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have q1 := Finset.mem_of_mem_erase (sup_wit_out hS h hq)
    rw [← he] at hq
    have q2 := Finset.mem_of_mem_erase (sup_wit_out hS h' hq)
    exact Finset.disjoint_left.mp hd (h.2.2.2.2.2.1 q1) (h'.2.2.2.2.2.1 q2)

theorem sup_cost_ne_of_single (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hs : supp n D (src D e) ∩ P = {f}) (hff : f ≠ f') :
    sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have h0 : supp n D (n + e.1) ∩ P = ∅ := by
    have hout := sup_wit_out hS h
    rw [hs, Finset.erase_singleton] at hout
    exact Finset.subset_empty.mp hout
  have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
  rw [hc] at heq
  have he := (sup_cost_inl heq.symm).1
  subst he
  have hm : f' ∈ supp n D (src D e') ∩ P := Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  rw [hs, Finset.mem_singleton] at hm
  exact hff hm.symm

theorem sup_fibre_le (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (c : (ℕ × Bool) ⊕ ℕ) :
    (Lab.filter (fun f => sup_cost n D P (wit f) = c)).card ≤ 2 := by
  rcases c with e0 | j0
  · by_cases hne : (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inl e0)).Nonempty
    · obtain ⟨f0, hf0⟩ := hne
      rw [Finset.mem_filter] at hf0
      have hcard := (hwit f0 hf0.1).2.2.2.2.2.2
      rw [(sup_cost_inl hf0.2).1] at hcard
      refine le_trans (Finset.card_le_card ?_) hcard
      intro f hf
      rw [Finset.mem_filter] at hf
      have hw := hwit f hf.1
      rw [(sup_cost_inl hf.2).1] at hw
      exact Finset.mem_inter.mpr ⟨hw.2.2.2.1, hw.2.2.1⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  · have hinj : Set.InjOn (fun f => (wit f).2)
        (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inr j0) : Set (Fin n)) := by
      intro f hf f' hf' hs
      rw [Finset.mem_coe, Finset.mem_filter] at hf hf'
      obtain ⟨h1, hn1⟩ := sup_cost_inr hf.2
      obtain ⟨h1', -⟩ := sup_cost_inr hf'.2
      have hee : wit f = wit f' := Prod.ext (h1.trans h1'.symm) hs
      have hw' := hwit f' hf'.1
      rw [← hee] at hw'
      exact sup_wit_same_pos hS (hwit f hf.1) hw' hn1
    have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool))
      (fun f => (wit f).2) (fun _ _ => Finset.mem_univ _) hinj
    simpa using hle

theorem sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)

theorem sup_wit_card_single (hS : Strict n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * S.card + (Lab \ S).card ≤
      2 * (Lab.image (fun f => sup_cost n D P (wit f))).card := by
  have h1 : (S.image (fun f => sup_cost n D P (wit f))).card = S.card :=
    Finset.card_image_of_injOn (fun f hf f' hf' heq => by
      by_contra hne
      exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' (hSL hf')) (hsing f hf) hne heq)
  have h2 := sup_wit_card hS (Lab \ S) U wit (fun f hf => hwit f (Finset.mem_sdiff.mp hf).1)
  have hd : Disjoint (S.image (fun f => sup_cost n D P (wit f)))
      ((Lab \ S).image (fun f => sup_cost n D P (wit f))) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨f', hf', heq⟩ := Finset.mem_image.mp hc2
    rw [Finset.mem_sdiff] at hf'
    exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' hf'.1) (hsing f hf)
      (fun h => hf'.2 (h ▸ hf)) heq.symm
  have h3 : (S.image (fun f => sup_cost n D P (wit f)) ∪
      (Lab \ S).image (fun f => sup_cost n D P (wit f))).card ≤
      (Lab.image (fun f => sup_cost n D P (wit f))).card :=
    Finset.card_le_card (Finset.union_subset (Finset.image_subset_image hSL)
      (Finset.image_subset_image Finset.sdiff_subset))
  rw [Finset.card_union_of_disjoint hd, h1] at h3
  omega

theorem sup_master_disj (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (C : Finset ((ℕ × Bool) ⊕ ℕ)) (hC : ∀ c ∈ C, sup_CostOK n D P c)
    (hdis : Disjoint E C.toLeft) :
    (sup_big n D P).card + E.card + C.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  have hl : ∀ e ∈ C.toLeft, e ∈ exitArcs n D (carrierT n D P) ∧
      (supp n D (src D e) ∩ P).card ≤ 2 := fun e he => hC _ (Finset.mem_toLeft.mp he)
  have hr : ∀ j ∈ C.toRight, j ∈ merges n D (carrierT n D P) ∧
      (supp n D (n + j) ∩ P).card = 1 := fun j hj => hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card ≤ (exitArcs n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint hdis]
    refine Finset.card_le_card (fun e he => ?_)
    rcases Finset.mem_union.mp he with h | h
    · exact hE e h
    · exact (hl e h).1
  have h2 : (sup_big n D P).card + C.toRight.card ≤ (merges n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun j hj => ?_)
      rcases Finset.mem_union.mp hj with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (hr j h).1
    · rw [Finset.disjoint_left]
      intro j h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (hr j h2).2
      omega
  have h3 := Finset.card_toLeft_add_card_toRight (u := C)
  omega

theorem sup_count_disj (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (Lab S : Finset (Fin n)) (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f})
    (hdis : ∀ e ∈ E, ∀ f ∈ Lab, e ≠ wit f) :
    2 * ((sup_big n D P).card + E.card) + 2 * S.card + (Lab \ S).card ≤
      2 * ((exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card) := by
  have h1 := sup_wit_card_single hS Lab S U wit hwit hSL hsing
  have hdis' : Disjoint E (Lab.image (fun f => sup_cost n D P (wit f))).toLeft := by
    rw [Finset.disjoint_left]
    intro e he hL
    rw [Finset.mem_toLeft, Finset.mem_image] at hL
    obtain ⟨f, hf, hcf⟩ := hL
    have hwe : wit f = e := by
      unfold sup_cost at hcf
      split at hcf
      · exact Sum.inl.inj hcf
      · exact absurd hcf (by simp)
    exact hdis e he f hf hwe.symm
  have h2 := sup_master_disj P E hE (Lab.image (fun f => sup_cost n D P (wit f))) (by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
    exact sup_cost_ok hS (hwit f hf)) hdis'
  omega

end SupMask

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag} (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

theorem bz_card {n : ℕ} {D : Dag} (hS : Strict n D) (Z : Finset ℕ)
    (hZ : ∀ b ∈ Z, 2 ≤ fanout D b ∧ supp n D b = ∅) : Z.card ≤ Bzero n D := by
  have hsub : Z ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
    fun b hb => sem_bzero_mem hS (hZ b hb).1 (hZ b hb).2
  calc Z.card = ∑ _w ∈ Z, 1 := by simp
    _ ≤ ∑ w ∈ Z, (fanout D w - 1) :=
        Finset.sum_le_sum (fun w hw => by have := (hZ w hw).1; omega)
    _ ≤ Bzero n D := Finset.sum_le_sum_of_subset hsub

theorem cnt_main2 {n : ℕ} {D : Dag} (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L3 : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L3, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L3, ∀ T' ∈ L3, T ≠ T' → (T ∩ T').card ≤ 1)
    (L2 : Finset (Finset (Fin n)))
    (h2 : ∀ M ∈ L2, M.card = 2 ∧ sup_Occ n D P M ∧ ∀ T ∈ L3, ¬ M ⊆ T)
    (E : Finset (ℕ × Bool)) (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL3 : ∀ f ∈ Lab, ∀ T ∈ L3, (U f ∩ T).card ≤ 1)
    (hUL2 : ∀ f ∈ Lab, ∀ M ∈ L2, (U f ∩ M).card ≤ 1)
    (hEdis : ∀ e ∈ E, ∀ f ∈ Lab, ∀ w, sup_Wit n D P (U f) f w → e ≠ w) :
    2 * L3.card + L2.card + E.card + Lab.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  classical
  choose! wit hwit using hw
  let S := Lab.filter (fun f => ∀ M, M ⊆ U f → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M)
  have hSL : S ⊆ Lab := Finset.filter_subset _ _
  have hno : ∀ f ∈ Lab \ S, ∃ M, M ⊆ U f ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ n D P M := by
    intro f hf
    rw [Finset.mem_sdiff, Finset.mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  have hL2dis : Disjoint L2 ((Lab \ S).image pr) := by
    rw [Finset.disjoint_left]
    intro M hM2 hMpr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hMpr
    have hsub := (hpr f hf).1
    have hcard := (hpr f hf).2.1
    have := Finset.card_le_card (Finset.subset_inter hsub (Finset.Subset.refl _))
    have := hUL2 f (Finset.mem_sdiff.1 hf).1 _ hM2
    omega
  have hX := sup_charge hS hP L3 h3 hint (L2 ∪ (Lab \ S).image pr) (by
    intro M hM
    rcases Finset.mem_union.1 hM with hM2 | hMpr
    · obtain ⟨hc, ho, hnoT⟩ := h2 M hM2
      refine ⟨ho, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
        fun _ T hT => hnoT T hT⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hMpr
      obtain ⟨h1, h2', -, h4⟩ := hpr f hf
      refine ⟨h4, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
        fun _ T hT hsub => ?_⟩
      have := Finset.card_le_card (Finset.subset_inter h1 hsub)
      have := hUL3 f (Finset.mem_sdiff.1 hf).1 T hT
      omega)
  rw [Finset.card_union_of_disjoint hL2dis] at hX
  have hcnt := sup_count_disj hS P E hE Lab S U wit hwit hSL
    (fun f hf => sup_wit_single (hwit f (hSL hf)) (Finset.mem_filter.1 hf).2)
    (fun e he f hf => hEdis e he f hf (wit f) (hwit f hf))
  have hfib : (Lab \ S).card ≤ 2 * ((Lab \ S).image pr).card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((Lab \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [Finset.mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine Finset.card_le_card (fun f hf => ?_)
      rw [Finset.mem_filter] at hf
      exact hf.2 ▸ (hpr f hf.1).2.2.1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have := Finset.card_sdiff_add_card_eq_card hSL
  omega

section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) {x c : Fin n} (hxc : x ≠ c) (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) {w : ℕ}
    (hw : x ∈ supp n D w ∧ c ∈ supp n D w) :
    ∃ e0, ∀ e ∈ sem_W n D x, e ≠ e0 → c ∈ supp n D (src D e) := by
  classical
  obtain ⟨z, hxz, hcz⟩ := hG.2.2.1 x c hxc
  obtain ⟨-, -, h2, e1, he1, ht1, -⟩ := sem_diff_two_exits hG h hC b hb hxc hx hres hw hxz hcz
  have hc1 : ((exitArcs n D (carrierDiff n D x c)).erase e1).card = 1 := by
    rw [Finset.card_erase_of_mem he1, h2]
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 hc1
  refine ⟨e0, fun e he hne => ?_⟩
  by_contra hce
  obtain ⟨h1, h4, h5⟩ := sem_mem_W.1 he
  have hm : e ∈ (exitArcs n D (carrierDiff n D x c)).erase e1 :=
    Finset.mem_erase.2 ⟨fun heq => by
      have := sem_W_and h.1 he
      rw [heq, ht1] at this
      exact Bool.false_ne_true this, sem_mem_exit_diff.2 ⟨h1, ⟨h4, hce⟩, fun hc => h5 hc.1⟩⟩
  rw [he0, Finset.mem_singleton] at hm
  exact hne hm

theorem zm_mem (hS : Strict n D) {c : Fin n} (hM : merges n D (carrierT n D {c}) = ∅)
    {e : ℕ × Bool} (he : e.1 < D.length) (ht : tag D e.1 = true)
    (hc : c ∈ supp n D (src D e)) : e ∈ sem_W n D c :=
  sem_mem_W.2 ⟨he, hc, fun hc2 => by
    have := (sem_zm_gate hS hM he hc2).1
    rw [ht] at this
    exact Bool.noConfusion this⟩

theorem gct_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : sem_MinBranch n D b) {u0 : Σ _ : ℕ, ℕ} (hu0 : u0 ∈ residualUnits n D b)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hsat : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅ ∧ x ∈ supp n D u0.1 ∧
      ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → u = u0) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hu0u : u0 ∈ units n D := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (hsat x hx).1) u0.1
    (fun x hx => (hsat x hx).2.1) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, hxr, huniq⟩ := hsat x hx
  have hxe : x ∈ eligSet n D := mem_eligSet.2 ⟨u0.1, hfr, hxr⟩
  by_contra hc
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
      by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have h1 := huniq _ (Finset.mem_sdiff.mpr ⟨hwu, hwr⟩) hxw
    have : w = u0.1 := congrArg Sigma.fst h1
    omega

theorem full_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i v : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool}
    (he : sem_W n D i = {e}) (hiv : G i v)
    (hv : ∀ p ∈ sem_W n D v, p.1 ≠ e.1 → ¬ supp n D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W n D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step n D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := sem_noempty_unique hG h hC hB0 hi hreach2
    have hf : fanout D w = 1 := by
      have h1 := sem_step_fanout hw2
      by_contra hne
      have h2 := sem_branch_empty hG hS hC hi hch (by omega)
      have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
      rw [h2] at h4
      exact Finset.not_nonempty_empty h4
    have hsub : supp n D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp n D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W n D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

end L3bGen

def sideL : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
def sideR : Finset (Fin 14) := {7, 8, 9, 10, 11, 12, 13}

def os_ptL (k : Fin 7) : Fin 14 := ⟨k.val, by omega⟩
def os_ptR (k : Fin 7) : Fin 14 := ⟨7 + k.val, by omega⟩

theorem os_ptL_inj : Function.Injective os_ptL := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simpa [os_ptL] using this)

theorem os_ptR_inj : Function.Injective os_ptR := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; dsimp [os_ptR] at this; omega)

def maskFin7 (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter (fun k : Fin 7 => m.val.testBit k.val)

theorem exists_maskFin7 (S : Finset (Fin 7)) : ∃ m : Fin 128, maskFin7 m = S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by ext k; simp [maskFin7]⟩
  | insert a s _ ih =>
    obtain ⟨m, hm⟩ := ih
    have hpow : 2 ^ a.val < 2 ^ 7 := Nat.pow_lt_pow_right (by omega) a.isLt
    refine ⟨⟨m.val ||| 2 ^ a.val, Nat.or_lt_two_pow m.isLt hpow⟩, ?_⟩
    ext k
    simp only [maskFin7, Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_or,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
    have hmk : m.val.testBit k.val = true ↔ k ∈ s := by
      have := Finset.ext_iff.1 hm k
      simpa [maskFin7] using this
    rw [hmk, Fin.ext_iff]
    tauto

theorem g14_sides : ∀ a b : Fin 14, hc_adjB a b = true →
    decide (a.val < 7) ≠ decide (b.val < 7) := by decide +kernel

theorem sideL_indep : ∀ a ∈ sideL, ∀ b ∈ sideL, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g14_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideL, decide (x.val < 7) = true := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl

theorem sideR_indep : ∀ a ∈ sideR, ∀ b ∈ sideR, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g14_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideR, decide (x.val < 7) = false := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl

theorem g14_lost {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ sem_g14_nb i ⊆ P ∧ ¬ sup_Occ 14 D P (sem_g14_nb i)) :
    J.card ≤ Bzero 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  have hocc : ∀ i ∈ J, ∀ q, (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [Finset.mem_inter, g14_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (g14_mem_nb.2 h1))).2 h1, (hJ i hi).2.1 (g14_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ J, ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases sem_inelig_reach hG h hC (hJ i hi).1 with hch | hb
    · obtain ⟨j, s, -, -, -, hq⟩ := sem_exact_nbhd hG h.1 hC P hP hch
      exact absurd hq (hocc i hi _)
    · exact hb
  choose! br hbr using hb
  have hinj : Set.InjOn br J := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨a, hja, hia⟩ := nbr_diff_exists j i (Ne.symm hne)
    have h1 := sem_shared_exact hG h.1 hC P hP (hbr i hi).1
      (hij ▸ sem_chain_dom h.1 (hbr j hj).1) ⟨a, (hJ j hj).2.1 (g14_mem_nb.2 hja), hja, hia⟩
    obtain ⟨_, _, -, -, -, -, hq⟩ := h1
    exact hocc i hi _ hq
  calc J.card = (J.image br).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Bzero 14 D := bz_card h.1 (J.image br) (fun b hb => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
        exact (hbr i hi).2)

theorem g14_count {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (hP7 : P.card ≤ 7) (hPe : P ⊆ eligSet 14 D)
    (Oc3 Oc2 Ct Iin : Finset (Fin 14))
    (hOc3 : ∀ i ∈ Oc3, sem_g14_nb i ⊆ P ∧ (sem_g14_nb i).card = 3 ∧ sup_Occ 14 D P (sem_g14_nb i))
    (hOc2 : ∀ i ∈ Oc2, sem_g14_nb i ⊆ P ∧ (sem_g14_nb i).card = 2 ∧ sup_Occ 14 D P (sem_g14_nb i))
    (hCt : ∀ c ∈ Ct, c ∉ Oc3 ∧ c ∉ Oc2 ∧
      (sem_g14_nb c ⊆ P → ¬ sup_Occ 14 D P (sem_g14_nb c)))
    (hIin : ∀ i ∈ Iin, i ∈ ineligSet 14 D ∧ sem_g14_nb i ⊆ P) :
    2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun c => sem_g14_nb c ∩ P)).card +
      (eligSet 14 D).card ≤ 2 * P.card + Bplus 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hEinj : Set.InjOn pos Iin := fun i hi j hj hij =>
    hpos.2 i (hIin i hi).1 j (hIin j hj).1 hij
  have hE : ∀ e ∈ Iin.image pos, e ∈ exitArcs 14 D (carrierT 14 D P) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hj, hemp, hnb, -⟩ := hpos.1 i (hIin i hi).1
    have hdeg := degree_two_or_three i
    have hne : (sem_g14_nb i).Nonempty := Finset.card_pos.1 (by dsimp [sem_g14_nb]; omega)
    obtain ⟨a, ha⟩ := hne
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 hj, Finset.mem_univ _⟩,
      sup_mem_carrier.2 ⟨a, Finset.mem_inter.2 ⟨hnb a (g14_mem_nb.1 ha), (hIin i hi).2 ha⟩⟩, ?_⟩
    rw [sup_mem_carrier, hemp, Finset.empty_inter]
    exact Finset.not_nonempty_empty
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_g14_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_g14_nb c ∩ P :=
    fun f hf => Finset.mem_biUnion.1 hf
  choose! ct hct using hlab
  have hmain := cnt_main2 h.1 hP7 (Oc3.image sem_g14_nb)
    (fun T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      exact ⟨(hOc3 i hi).2.1, (hOc3 i hi).2.2⟩)
    (fun T hT T' hT' hne => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT'
      have := sup_g14_inter i j (fun hij => hne (hij ▸ rfl)) Finset.univ
      simpa [sem_g14_nb] using this)
    (Oc2.image sem_g14_nb)
    (fun M hM => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hM
      refine ⟨(hOc2 i hi).2.1, (hOc2 i hi).2.2, fun T hT hsub => ?_⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT
      have hij : i ≠ j := fun h => by
        have h2 := (hOc2 i hi).2.1; have h3 := (hOc3 j hj).2.1; rw [h] at h2; omega
      have hle := sup_g14_inter i j hij Finset.univ
      have hsub' : sem_g14_nb i ⊆ sem_g14_nb i ∩ sem_g14_nb j :=
        Finset.subset_inter (Finset.Subset.refl _) hsub
      have hc := Finset.card_le_card hsub'
      have h2 := (hOc2 i hi).2.1
      simp only [Finset.inter_univ] at hle
      omega)
    (Iin.image pos) hE (Ct.biUnion (fun c => sem_g14_nb c ∩ P)) (fun f => sem_g14_nb (ct f) ∩ P)
    (fun f hf => by
      obtain ⟨hc, hfc⟩ := hct f hf
      refine sup_wit_exists hG h.1 hC (X := insert (ct f) (P \ (sem_g14_nb (ct f) ∩ P)))
        Finset.inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
        ⟨ct f, Finset.mem_insert_self _ _, adj_symm (g14_mem_nb.1 (Finset.mem_inter.1 hfc).1)⟩
      · by_cases hsubP : sem_g14_nb (ct f) ⊆ P
        · rcases degree_two_or_three (ct f) with hd2 | hd3
          · exact Or.inl (by rw [Finset.inter_eq_left.2 hsubP]; dsimp [sem_g14_nb]; omega)
          · rw [Finset.inter_eq_left.2 hsubP]
            exact Or.inr ⟨hd3, (hCt _ hc).2.2 hsubP⟩
        · have hlt : (sem_g14_nb (ct f) ∩ P).card < (sem_g14_nb (ct f)).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left,
              fun heq => hsubP (heq ▸ Finset.inter_subset_right)⟩)
          rcases degree_two_or_three (ct f) with hd2 | hd3 <;> (rw [g14_nb_eq] at hlt ⊢; exact Or.inl (by omega))
      · have hno : ∀ a ∈ P \ (sem_g14_nb (ct f) ∩ P), ¬ Adj (ct f) a := by
          intro a ha hadj
          rw [Finset.mem_sdiff, Finset.mem_inter, g14_mem_nb] at ha
          exact ha.2 ⟨hadj, ha.1⟩
        intro a ha b hb
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · exact adj_irrefl _
        · exact hno b hb
        · exact fun hab => hno a ha (adj_symm hab)
        · exact hPi a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1)
    (fun f hf T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      have h1 := sup_g14_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).1 (hij ▸ hi)) P
      rwa [Finset.inter_comm (sem_g14_nb i)] at h1)
    (fun f hf M hM => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hM
      have h1 := sup_g14_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).2.1 (hij ▸ hi)) P
      rwa [Finset.inter_comm (sem_g14_nb i)] at h1)
    (fun e he f hf w hw hew => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨hc, -⟩ := hct f hf
      have hnbi : sem_g14_nb i ⊆ supp 14 D (src D (pos i)) ∩ P := fun a ha =>
        Finset.mem_inter.2 ⟨(hpos.1 i (hIin i hi).1).2.2.1 a (g14_mem_nb.1 ha), (hIin i hi).2 ha⟩
      have hwsub : supp 14 D (src D (pos i)) ∩ P ⊆ sem_g14_nb (ct f) ∩ P := hew ▸ hw.2.2.2.2.2.1
      by_cases hci : ct f = i
      · rw [hci, Finset.inter_eq_left.2 (hIin i hi).2] at hwsub
        have heq : supp 14 D (src D (pos i)) ∩ P = sem_g14_nb i := Finset.Subset.antisymm hwsub hnbi
        exact (hCt (ct f) hc).2.2 (hci ▸ (hIin i hi).2) ⟨src D (pos i), hci ▸ heq⟩
      · have hle := sup_g14_inter i (ct f) (Ne.symm hci) P
        have hsub' : sem_g14_nb i ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ P) :=
          Finset.subset_inter (Finset.Subset.refl _) (hnbi.trans hwsub)
        have hcard := Finset.card_le_card hsub'
        rcases degree_two_or_three i with hd | hd <;> (rw [g14_nb_eq] at hcard hle; omega))
  have h4 := carrier_flow_union h P (by rw [g14_supp_out hD]; simp)
  have h5 := surplus_carrierT_le h.1 b hb P
  rw [Finset.inter_eq_left.2 hPe] at h5
  rw [Finset.card_image_of_injective _ (fun i j hij => g14_nb_inj hij),
    Finset.card_image_of_injective _ (fun i j hij => g14_nb_inj hij),
    Finset.card_image_of_injOn hEinj] at hmain
  omega

theorem g14_sideR_step {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 14 D
      let P := sideR \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 3)
      let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 2)
      let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptL k ∈ I ∧ g14_nbB (os_ptL k) ⊆ P)
      (∀ k ∈ Oc, g14_nbB (os_ptL k) ⊆ P) ∧
      2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P)).card +
        (14 - I.card) ≤ 2 * P.card + Bplus 14 D ∧
      (Iin \ Oc).card ≤ Bzero 14 D := by
  classical
  set I := ineligSet 14 D with hIdef
  set P := sideR \ I
  have hPl : P ⊆ sideR := Finset.sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideR_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (Finset.card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 14 D := fun a ha => by
    by_contra hne; exact (Finset.mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  let Oc := Finset.univ.filter (fun k : Fin 7 =>
    g14_nbB (os_ptL k) ⊆ P ∧ sup_Occ 14 D P (sem_g14_nb (os_ptL k)))
  obtain ⟨m, hm⟩ := exists_maskFin7 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 3)
  let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 2)
  let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
  let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptL k ∈ I ∧ g14_nbB (os_ptL k) ⊆ P)
  have hcnt := g14_count h hD P hPi hP7 hPe (Oc3.image os_ptL) (Oc2.image os_ptL) (Ct.image os_ptL)
    (Iin.image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g14_nb_eq]; exact ⟨hko.2.1, hk.2, g14_nb_eq _ ▸ hko.2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g14_nb_eq]; exact ⟨hko.2.1, hk.2, g14_nb_eq _ ▸ hko.2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have hnk : k ∉ Oc := (Finset.mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hsub hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h3
        rw [os_ptL_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h2
        rw [os_ptL_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · exact hnk (Finset.mem_filter.2 ⟨Finset.mem_univ k, g14_nb_eq _ ▸ hsub, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      have hki := (Finset.mem_filter.1 hk).2
      exact ⟨hki.1, g14_nb_eq _ ▸ hki.2⟩)
  have hlost := g14_lost h hD P hPi ((Iin \ Oc).image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_sdiff] at hk
      have hki := (Finset.mem_filter.1 hk.1).2
      refine ⟨hki.1, g14_nb_eq _ ▸ hki.2, fun hocc => hk.2 ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hki.2, hocc⟩)
  rw [Finset.card_image_of_injective _ os_ptL_inj] at hlost
  rw [Finset.card_image_of_injective _ os_ptL_inj, Finset.card_image_of_injective _ os_ptL_inj,
    Finset.card_image_of_injective _ os_ptL_inj] at hcnt
  have hLabEq : ((Ct.image os_ptL).biUnion (fun c => sem_g14_nb c ∩ P)) =
      Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter, g14_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptL k, ⟨k, hk, rfl⟩, hx⟩
  rw [hLabEq] at hcnt
  have hel := inelig_card_add 14 D
  rw [← hIdef] at hel
  refine ⟨fun k hk => (Finset.mem_filter.1 hk).2.1, ?_, hlost⟩
  change 2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P)).card +
    (14 - I.card) ≤ 2 * P.card + Bplus 14 D
  omega

abbrev G14 : Fin 14 → Fin 14 → Prop := fun u v => Adj u v

def ru (D : Dag) (b : Fin 14 → ℕ) (x : Fin 14) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1)

theorem res_elig {D : Dag} {b : Fin 14 → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits 14 D b) {x : Fin 14} (hx : x ∈ supp 14 D u.1) : x ∈ eligSet 14 D :=
  mem_eligSet.2 ⟨u.1, by
    have h1 := (mem_units.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1).2
    omega, hx⟩

theorem cc_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) (x : Fin 14) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_g14_gr h (sem_g14_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  unfold ru
  omega

theorem w_bar {n : ℕ} {D : Dag} (hS : Strict n D) {x : Fin n} {e : ℕ × Bool}
    (he : e ∈ sem_W n D x) : sem_bar e ∉ sem_W n D x := by
  intro hb
  obtain ⟨hj, hx, hn⟩ := sem_mem_W.mp he
  have hx' := (sem_mem_W.mp hb).2.1
  apply hn
  rw [sem_supp_and hS hj (sem_W_and hS he), Finset.mem_inter]
  obtain ⟨j, s⟩ := e
  cases s
  · exact ⟨by simpa [src] using hx, by simpa [src, sem_bar] using hx'⟩
  · exact ⟨by simpa [src, sem_bar] using hx', by simpa [src] using hx⟩

theorem as_mem {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i a : Fin 14} (hi : i ∈ ineligSet 14 D) (hia : Adj i a) : pos i ∈ sem_W 14 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

theorem as_priv {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i t : Fin 14} (hi : i ∈ ineligSet 14 D) (ht : sem_bar (pos i) ∈ sem_W 14 D t) : t = i := by
  have := (sem_mem_W.1 ht).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at this
  exact Finset.mem_singleton.1 this

theorem as_W {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i : Fin 14} (hi : i ∈ ineligSet 14 D) :
    sem_W 14 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, -, -, -, h6, -⟩ :=
    sem_inelig_consumer sem_g14_gr h (sem_g14_comp hD) hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 14 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 14 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem full_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos) {i v : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ (pos i).1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_g14_gr h (sem_g14_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
  rwa [sem_bar_bar] at this

theorem pa_card3 {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this

theorem pa_card4 {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd] at this

theorem pa_three {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : s.card ≤ 3) :
    ∀ e ∈ s, e = a ∨ e = b ∨ e = c := by
  intro e he
  by_contra hne
  rw [not_or, not_or] at hne
  have := pa_card3 (s := s.erase e) (Finset.mem_erase.2 ⟨Ne.symm hne.1, ha⟩)
    (Finset.mem_erase.2 ⟨Ne.symm hne.2.1, hb⟩) (Finset.mem_erase.2 ⟨Ne.symm hne.2.2, hc⟩)
    hab hac hbc
  rw [Finset.card_erase_of_mem he] at this
  omega

theorem pa_two {α : Type} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hs : s.card ≤ 2) : ∀ e ∈ s, e = a ∨ e = b := by
  intro e he
  by_contra hne
  rw [not_or] at hne
  have := pa_card3 he ha hb hne.1 hne.2 hab
  omega

theorem pa_ed {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {x y : Fin 14} (hxy : Adj x y) :
    ∃ e ∈ sem_W 14 D x, sem_bar e ∈ sem_W 14 D y ∧
      (∀ i ∈ ineligSet 14 D, e = pos i → y = i) ∧
      ∀ i ∈ ineligSet 14 D, sem_bar e = pos i → x = i := by
  obtain ⟨e, he, hb, -⟩ := sem_edge_slots sem_g14_gr h.1 (sem_g14_comp hD) hxy
  exact ⟨e, he, hb, fun i hi hei => as_priv hpos hi (hei ▸ hb),
    fun i hi hei => as_priv hpos hi (by rw [← hei, sem_bar_bar]; exact he)⟩

theorem g14_deg3_third : ∀ x a b : Fin 14, (g14_nbB x).card = 3 →
    x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem g14_deg3_cover_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14}
    (hd : (g14_nbB x).card = 3) (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 14 D x ∧ a ∉ supp 14 D (src D e) ∧ b ∉ supp 14 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := g14_deg3_third x a b hd hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_g14_gr h.1 (sem_g14_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

theorem ps_nonadj {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i x r : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x) (hir : Adj i r) (hrx : r ≠ x) (hdx : (g14_nbB x).card = 3)
    (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 14 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → ¬ Adj r t → Z ∉ sem_W 14 D t := by
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain sem_g14_gr h.1 (sem_g14_comp hD) (x := x) (a := r) (Ne.symm hrx)
  have hY : pos i ∈ sem_W 14 D x := as_mem hpos hi hix
  have hZY : Z ≠ pos i := fun heq => hZr (heq ▸ (hpos.1 i hi).2.2.1 r hir)
  have hW : sem_W 14 D x = {pos i, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  refine ⟨Z, hZY, hW, fun t htx hrt hZt => ?_⟩
  obtain ⟨f, hf, h1, h2⟩ := g14_deg3_cover_free h hD hdx (Ne.symm hrx) (Ne.symm htx) hrt
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · exact h1 ((hpos.1 i hi).2.2.1 r hir)
  · exact h2 (sem_mem_W.1 hZt).2.1

theorem ps_side {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i x : Fin 14} (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x) (hdx : (g14_nbB x).card = 3) (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 14 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → decide (t.val < 7) = decide (x.val < 7) → Z ∉ sem_W 14 D t := by
  obtain ⟨r, hir, hrx⟩ := sem_g14_gr.2.2.2 i x
  obtain ⟨Z, hZY, hW, hp⟩ := ps_nonadj h hD hpos hi hix hir hrx hdx hc
  refine ⟨Z, hZY, hW, fun t htx hside => hp t htx (fun hadj => ?_)⟩
  have s1 := g14_sides i x ((hc_adjB_iff i x).2 hix)
  have s2 := g14_sides i r ((hc_adjB_iff i r).2 hir)
  have s3 := g14_sides r t ((hc_adjB_iff r t).2 hadj)
  cases h1 : decide (i.val < 7) <;> cases h2 : decide (x.val < 7) <;>
    cases h3 : decide (r.val < 7) <;> cases h4 : decide (t.val < 7) <;> simp_all

theorem two_in_deg3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) {i1 i2 u v : Fin 14}
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) : 3 ≤ (sem_W 14 D u).card := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  by_cases hv : v ∈ ineligSet 14 D
  · exact pa_card3 p1 p2 (as_mem hpos hv (adj_symm h3)) p12
      (fun e => hv1.symm (hpos.2 i1 hi1 v hv e)) (fun e => hv2.symm (hpos.2 i2 hi2 v hv e))
  · obtain ⟨e, he, -, hf, -⟩ := pa_ed h hD hpos h3
    exact pa_card3 p1 p2 he p12 (fun hh => hv (hf i1 hi1 hh.symm ▸ hi1))
      (fun hh => hv (hf i2 hi2 hh.symm ▸ hi2))

theorem full_of_two_in_deg3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i1 i2 u v : Fin 14} (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) (hcu : (sem_W 14 D u).card ≤ 3) :
    (∀ t, t ∈ supp 14 D (src D (pos i1)) → Adj i1 t) ∧
    (∀ t, t ∈ supp 14 D (src D (pos i2)) → Adj i2 t) := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have hfull : ∀ (ia ib : Fin 14), ia ∈ ineligSet 14 D → ib ∈ ineligSet 14 D → ia ≠ ib →
      Adj ia u → Adj ib u → v ≠ ia → v ≠ ib →
      ∀ t, t ∈ supp 14 D (src D (pos ia)) → Adj ia t := by
    intro ia ib hia hib hab hiau hibu hvia hvib t ht
    have pa := as_mem hpos hia hiau
    have pb := as_mem hpos hib hibu
    have pab : pos ia ≠ pos ib := fun e => hab (hpos.2 ia hia ib hib e)
    have hspec : ∀ t, t ∈ supp 14 D (src D (pos ia)) ↔ Adj ia t := by
      refine full_g14 h hD hB0 hpos hia hiau (fun p hp hne1 hsub => ?_)
      by_cases hv : v ∈ ineligSet 14 D
      · have pv := as_mem hpos hv (adj_symm h3)
        have pav : pos ia ≠ pos v := fun e => hvia.symm (hpos.2 ia hia v hv e)
        have pbv : pos ib ≠ pos v := fun e => hvib.symm (hpos.2 ib hib v hv e)
        rcases pa_three pa pb pv pab pav pbv hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ib ∈ supp 14 D (src D (sem_bar (pos ib))) := by
            rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl,
              (hpos.1 ib hib).2.2.2]; exact Finset.mem_singleton_self ib
          exact hab.symm (Finset.mem_singleton.1 (hsub hm))
        · have hm : v ∈ supp 14 D (src D (sem_bar (pos v))) := by
            rw [show src D (sem_bar (pos v)) = src D ((pos v).1, !(pos v).2) from rfl,
              (hpos.1 v hv).2.2.2]; exact Finset.mem_singleton_self v
          exact hvia (Finset.mem_singleton.1 (hsub hm))
      · obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos h3
        have pae : pos ia ≠ e := fun hh => hv (hf ia hia hh.symm ▸ hia)
        have pbe : pos ib ≠ e := fun hh => hv (hf ib hib hh.symm ▸ hib)
        rcases pa_three pa pb he pab pae pbe hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ib ∈ supp 14 D (src D (sem_bar (pos ib))) := by
            rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl,
              (hpos.1 ib hib).2.2.2]; exact Finset.mem_singleton_self ib
          exact hab.symm (Finset.mem_singleton.1 (hsub hm))
        · exact hv (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hia)
    exact (hspec t).1 ht
  exact ⟨hfull i1 i2 hi1 hi2 hne h1 h2 hv1 hv2, hfull i2 i1 hi2 hi1 hne.symm h2 h1 hv2 hv1⟩

theorem pa_m1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos) (z k v iz ik : Fin 14)
    (hiz : iz ∈ ineligSet 14 D) (hik : ik ∈ ineligSet 14 D)
    (hz : z ∉ ineligSet 14 D) (hk : k ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k ∧ (g14_nbB k).card = 3 ∧
      decide (v.val < 7) = decide (k.val < 7))
    (hcz : (sem_W 14 D z).card ≤ 2) (hck : (sem_W 14 D k).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4
  obtain ⟨Dk, -, hWk, hpk⟩ := ps_side h hD hpos hik g2 g6 hck
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos g3
  obtain ⟨e', he', hbe', hg', -⟩ := pa_ed h hD hpos g4
  rw [hWk, Finset.mem_insert, Finset.mem_singleton] at hbe
  have hb : sem_bar e = Dk := hbe.resolve_left (fun hh => hz (hf' ik hik hh ▸ hik))
  rcases pa_two (as_mem hpos hiz g1) he (fun hh => hk (hf iz hiz hh.symm ▸ hiz)) hcz e' he'
    with h1 | h1
  · exact hv (hg' iz hiz h1 ▸ hiz)
  · exact hpk v g5 g7 (by rw [← hb, ← h1]; exact hbe')

theorem ps_side_3star {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    (u k1 k2 v ik1 ik2 : Fin 14)
    (hik1 : ik1 ∈ ineligSet 14 D) (hik2 : ik2 ∈ ineligSet 14 D)
    (hu : u ∉ ineligSet 14 D)
    (hg : hc_adjB u k1 = true ∧ hc_adjB u k2 = true ∧ hc_adjB u v = true ∧
      hc_adjB ik1 k1 = true ∧ hc_adjB ik2 k2 = true ∧
      k1 ≠ k2 ∧ v ≠ k1 ∧ v ≠ k2 ∧
      (g14_nbB k1).card = 3 ∧ (g14_nbB k2).card = 3 ∧
      decide (k1.val < 7) = decide (k2.val < 7) ∧ decide (v.val < 7) = decide (k1.val < 7))
    (hcu : (sem_W 14 D u).card ≤ 2) (hck1 : (sem_W 14 D k1).card ≤ 2)
    (hck2 : (sem_W 14 D k2).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, hk12, hvk1, hvk2, hd1, hd2, hs12, hsv1⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g5
  obtain ⟨D1, -, hW1, hp1⟩ := ps_side h hD hpos hik1 g4 hd1 hck1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_side h hD hpos hik2 g5 hd2 hck2
  obtain ⟨e1, he1, hbe1, -, hf1'⟩ := pa_ed h hD hpos g1
  obtain ⟨e2, he2, hbe2, -, hf2'⟩ := pa_ed h hD hpos g2
  obtain ⟨e3, he3, hbe3, -, -⟩ := pa_ed h hD hpos g3
  rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbe1
  have hb1 : sem_bar e1 = D1 := hbe1.resolve_left (fun hh => hu (hf1' ik1 hik1 hh ▸ hik1))
  rw [hW2, Finset.mem_insert, Finset.mem_singleton] at hbe2
  have hb2 : sem_bar e2 = D2 := hbe2.resolve_left (fun hh => hu (hf2' ik2 hik2 hh ▸ hik2))
  have he12 : e1 ≠ e2 := fun heq => by
    have hD12 : D1 = D2 := by rw [← hb1, ← hb2, heq]
    have hD2in : D2 ∈ sem_W 14 D k2 := by rw [hW2]; simp
    exact hp1 k2 hk12.symm hs12.symm (hD12 ▸ hD2in)
  rcases pa_two he1 he2 he12 hcu e3 he3 with rfl | rfl
  · exact hp1 v hvk1 hsv1 (hb1 ▸ hbe3)
  · exact hp2 v hvk2 (hsv1.trans hs12) (hb2 ▸ hbe3)

def pa_ctx (D : Dag) (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool) : Prop :=
  k4_Pos 14 G14 D pos ∧ (∀ x, (sem_W 14 D x).card ≤ 3) ∧ P ≠ Q ∧
    ∀ x, 3 ≤ (sem_W 14 D x).card → P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x

theorem pa_setup_one {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) : ∃ pos P Q, pa_ctx D pos P Q := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have h1 := card_residual h.1 b hbp
  have hc3 : ∀ x, (sem_W 14 D x).card ≤ 3 := fun x => by
    have h3 := cc_le h hD b hbp x
    have h4 : (ru D b x).card ≤ (residualUnits 14 D b).card := Finset.card_filter_le _ _
    omega
  by_cases hX : (Finset.univ.filter (fun x : Fin 14 => 3 ≤ (sem_W 14 D x).card)).Nonempty
  · obtain ⟨P, Q, hPQ, hall⟩ := sem_common_terminals hG h hC b hb (by omega) _ hX
      (fun x hx => (Finset.mem_filter.1 hx).2)
    exact ⟨pos, P, Q, hpos, hc3, fun hpq => hPQ (hpq ▸ rfl),
      fun x hx => hall x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)⟩
  · refine ⟨pos, (0, false), (0, true), hpos, hc3, by decide, fun x hx => ?_⟩
    exact absurd ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩ hX

theorem hnot33_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool}
    (hctx : pa_ctx D pos P Q) (x y ix iy : Fin 14)
    (hix : ix ∈ ineligSet 14 D) (hiy : iy ∈ ineligSet 14 D)
    (hx : x ∉ ineligSet 14 D) (hy : y ∉ ineligSet 14 D)
    (hg : ix ≠ iy ∧ hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB x y = true ∧
      hc_adjB ix y = false)
    (hsx : 3 ≤ (sem_W 14 D x).card) (hsy : 3 ≤ (sem_W 14 D y).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxyi, g1, g2, g3, g4⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3
  obtain ⟨hPx, hQx⟩ := hsat x hsx
  obtain ⟨hPy, hQy⟩ := hsat y hsy
  obtain ⟨e, hex, hey, hfy, hfx⟩ := pa_ed h hD hpos g3
  have heP : e ≠ P := fun hh => w_bar h.1 (hh ▸ hPy) hey
  have heQ : e ≠ Q := fun hh => w_bar h.1 (hh ▸ hQy) hey
  have hbeP : sem_bar e ≠ P := fun hh => w_bar h.1 hPx (by rw [← hh, sem_bar_bar]; exact hex)
  have hbeQ : sem_bar e ≠ Q := fun hh => w_bar h.1 hQx (by rw [← hh, sem_bar_bar]; exact hex)
  have hpx := as_mem hpos hix g1
  have hpy := as_mem hpos hiy g2
  have hpxe : pos ix ≠ e := fun hh => hy (hfy ix hix hh.symm ▸ hix)
  have hpybe : pos iy ≠ sem_bar e := fun hh => hx (hfx iy hiy hh.symm ▸ hiy)
  have hpxy : pos ix ∈ sem_W 14 D y := by
    rcases pa_three hPx hQx hex hPQ heP.symm heQ.symm (hc3 x) (pos ix) hpx with heq | heq | heq
    · exact heq ▸ hPy
    · exact heq ▸ hQy
    · exact absurd heq hpxe
  have hpyx : pos iy ∈ sem_W 14 D x := by
    rcases pa_three hPy hQy hey hPQ hbeP.symm hbeQ.symm (hc3 y) (pos iy) hpy with heq | heq | heq
    · exact heq ▸ hPx
    · exact heq ▸ hQx
    · exact absurd heq hpybe
  have hpxpy : pos ix ≠ pos iy := fun hh => hxyi (hpos.2 ix hix iy hiy hh)
  have hpye : pos iy ≠ e := fun hh => hy (hfy iy hiy hh.symm ▸ hiy)
  have hWx := pa_three hpx hpyx hex hpxpy hpxe hpye (hc3 x)
  have hfull := full_g14 h hD hB0 hpos hix g1 (fun p hp hne1 hsub => by
    rcases hWx p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : iy ∈ supp 14 D (src D (sem_bar (pos iy))) := by
        rw [show src D (sem_bar (pos iy)) = src D ((pos iy).1, !(pos iy).2) from rfl,
          (hpos.1 iy hiy).2.2.2]; exact Finset.mem_singleton_self iy
      exact hxyi.symm (Finset.mem_singleton.1 (hsub hm))
    · exact hy (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hey).2.1) ▸ hix))
  exact sem_adjB_false.1 g4 ((hfull y).1 (sem_mem_W.1 hpxy).2.1)

theorem elim_alt_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    (a1 a2 b0 b1 b2 ia1 ia2 ib0 ib1 ib2 : Fin 14)
    (hia1 : ia1 ∈ ineligSet 14 D) (hia2 : ia2 ∈ ineligSet 14 D)
    (hib0 : ib0 ∈ ineligSet 14 D) (hib1 : ib1 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (ha1 : a1 ∉ ineligSet 14 D) (ha2 : a2 ∉ ineligSet 14 D)
    (hb0 : b0 ∉ ineligSet 14 D) (hb1 : b1 ∉ ineligSet 14 D) (hb2 : b2 ∉ ineligSet 14 D)
    (hg : ia1 ≠ ia2 ∧ b0 ≠ b1 ∧ b0 ≠ b2 ∧ b1 ≠ b2 ∧
      hc_adjB ia1 a1 = true ∧ hc_adjB ia2 a2 = true ∧
      hc_adjB ib0 b0 = true ∧ hc_adjB ib1 b1 = true ∧ hc_adjB ib2 b2 = true ∧
      hc_adjB a1 b0 = true ∧ hc_adjB a1 b1 = true ∧
      hc_adjB a2 b1 = true ∧ hc_adjB a2 b2 = true ∧
      (g14_nbB b0).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB b2).card = 3 ∧
      decide (b0.val < 7) = decide (b1.val < 7) ∧ decide (b1.val < 7) = decide (b2.val < 7))
    (hsa1 : 3 ≤ (sem_W 14 D a1).card) (hsa2 : 3 ≤ (sem_W 14 D a2).card)
    (hcb0 : (sem_W 14 D b0).card ≤ 2) (hcb1 : (sem_W 14 D b1).card ≤ 2)
    (hcb2 : (sem_W 14 D b2).card ≤ 2) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hi12, h01, h02, h12, ga1, ga2, gb0, gb1, gb2, e10, e11, e21, e22,
    hd0, hd1, hd2, hs01, hs12⟩ := hg
  rw [hc_adjB_iff] at ga1 ga2 gb0 gb1 gb2 e10 e11 e21 e22
  obtain ⟨D0, -, hW0, hp0⟩ := ps_side h hD hpos hib0 gb0 hd0 hcb0
  obtain ⟨D1, -, hW1, hp1⟩ := ps_side h hD hpos hib1 gb1 hd1 hcb1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_side h hD hpos hib2 gb2 hd2 hcb2
  have hD0_in : D0 ∈ sem_W 14 D b0 := by rw [hW0]; simp
  have hD1_in : D1 ∈ sem_W 14 D b1 := by rw [hW1]; simp
  have hD2_in : D2 ∈ sem_W 14 D b2 := by rw [hW2]; simp
  obtain ⟨f10, hf10, hbf10, h10y, h10x⟩ := pa_ed h hD hpos e10
  obtain ⟨f11, hf11, hbf11, h11y, h11x⟩ := pa_ed h hD hpos e11
  obtain ⟨f21, hf21, hbf21, h21y, h21x⟩ := pa_ed h hD hpos e21
  obtain ⟨f22, hf22, hbf22, h22y, h22x⟩ := pa_ed h hD hpos e22
  have hb10 : sem_bar f10 = D0 := by
    rw [hW0, Finset.mem_insert, Finset.mem_singleton] at hbf10
    exact hbf10.resolve_left (fun hh => ha1 (h10x ib0 hib0 hh ▸ hib0))
  have hb11 : sem_bar f11 = D1 := by
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbf11
    exact hbf11.resolve_left (fun hh => ha1 (h11x ib1 hib1 hh ▸ hib1))
  have hb21 : sem_bar f21 = D1 := by
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbf21
    exact hbf21.resolve_left (fun hh => ha2 (h21x ib1 hib1 hh ▸ hib1))
  have hb22 : sem_bar f22 = D2 := by
    rw [hW2, Finset.mem_insert, Finset.mem_singleton] at hbf22
    exact hbf22.resolve_left (fun hh => ha2 (h22x ib2 hib2 hh ▸ hib2))
  have hf11_21 : f11 = f21 := by rw [← sem_bar_bar f11, ← sem_bar_bar f21, hb11, hb21]
  have hD01 : D0 ≠ D1 := fun hh => hp0 b1 h01.symm hs01.symm (hh ▸ hD1_in)
  have hD02 : D0 ≠ D2 := fun hh => hp0 b2 h02.symm (hs01.trans hs12).symm (hh ▸ hD2_in)
  have hD12 : D1 ≠ D2 := fun hh => hp1 b2 h12.symm hs12.symm (hh ▸ hD2_in)
  have h10_11 : f10 ≠ f11 := fun hh => hD01 (by rw [← hb10, ← hb11, hh])
  have h21_22 : f21 ≠ f22 := fun hh => hD12 (by rw [← hb21, ← hb22, hh])
  have hpa1 := as_mem hpos hia1 ga1
  have hpa2 := as_mem hpos hia2 ga2
  have hWa1 := pa_three hpa1 hf10 hf11 (fun hh => hb0 (h10y ia1 hia1 hh.symm ▸ hia1))
    (fun hh => hb1 (h11y ia1 hia1 hh.symm ▸ hia1)) h10_11 (hc3 a1)
  have hWa2 := pa_three hpa2 hf21 hf22 (fun hh => hb1 (h21y ia2 hia2 hh.symm ▸ hia2))
    (fun hh => hb2 (h22y ia2 hia2 hh.symm ▸ hia2)) h21_22 (hc3 a2)
  have honly : ∀ e, e ∈ sem_W 14 D a1 → e ∈ sem_W 14 D a2 → e = f11 := by
    intro e he1 he2
    rcases hWa1 e he1 with rfl | rfl | rfl
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (hpos.2 ia1 hia1 ia2 hia2 hh) hi12
      · exact absurd (h21y ia1 hia1 hh.symm ▸ hia1) hb1
      · exact absurd (h22y ia1 hia1 hh.symm ▸ hia1) hb2
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (h10y ia2 hia2 hh ▸ hia2) hb0
      · exact absurd (by rw [← hb10, ← hb21, hh]) hD01
      · exact absurd (by rw [← hb10, ← hb22, hh]) hD02
    · rfl
  exact hPQ ((honly P (hsat a1 hsa1).1 (hsat a2 hsa2).1).trans
    (honly Q (hsat a1 hsa1).2 (hsat a2 hsa2).2).symm)

theorem pa_card5 {α : Type} [DecidableEq α] {s : Finset α} {a b c d e : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : 5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    Finset.card_insert_of_notMem (by simp [hcd, hce]),
    Finset.card_pair hde] at this

theorem pa_four {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : s.card ≤ 4) : ∀ e ∈ s, e = a ∨ e = b ∨ e = c ∨ e = d := by
  intro e he
  by_contra hne
  rw [not_or, not_or, not_or] at hne
  have := pa_card5 he ha hb hc hd hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 hab hac had hbc hbd hcd
  omega

theorem mem_W_of_pos {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {j t : Fin 14} (hj : j ∈ ineligSet 14 D) (ht : t ∈ supp 14 D (src D (pos j))) :
    pos j ∈ sem_W 14 D t := by
  obtain ⟨h1, h2, -, -⟩ := hpos.1 j hj
  exact sem_mem_W.2 ⟨h1, ht, by rw [h2]; exact Finset.notMem_empty t⟩

theorem pe_co_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {v t j q : Fin 14} (hj : j ∈ ineligSet 14 D) (hv : v ∈ eligSet 14 D)
    (hres : ∀ u ∈ residualUnits 14 D b, v ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    {w : ℕ} (hw : v ∈ supp 14 D w ∧ t ∈ supp 14 D w)
    (hg : (g14_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 14 D (src D (pos j)) := by
  obtain ⟨hdv, hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_g14_gr h (sem_g14_comp hD) b hb hvt hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := g14_deg3_cover_free h hD hdv hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj).2.2.1 q hjq)))

theorem ru_sub_excl {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {v i1 i2 v3 t : Fin 14} (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hv : v ∈ eligSet 14 D)
    (hg : (g14_nbB v).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 v = true ∧ hc_adjB i2 v = true ∧
      hc_adjB v v3 = true ∧ v3 ≠ i1 ∧ v3 ≠ i2)
    (hru1 : (ru D b v).card = 1) (hsub : ru D b v ⊆ ru D b t) (hvt : v ≠ t)
    (hq : ∃ q : Fin 14,
      (hc_adjB i1 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i1 t = false) ∨
      (hc_adjB i2 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i2 t = false)) : False := by
  obtain ⟨hdv, hne, h1, h2, h3, hv1, hv2⟩ := hg
  have hcv : (sem_W 14 D v).card ≤ 3 := by
    have := cc_le h hD b hb v; omega
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 ⟨hne, h1, h2, h3, hv1, hv2⟩ hcv
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D b v).card)
  have hut := hsub hu
  have hres : ∀ u' ∈ residualUnits 14 D b, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
    fun u' hu' hv' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', hv'⟩))).2
  have hw : v ∈ supp 14 D u.1 ∧ t ∈ supp 14 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 hut).2⟩
  obtain ⟨q, ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩⟩ := hq
  · exact sem_adjB_false.1 a4 (hf1 t (pe_co_g14 h hD b hb hpos hi1 hv hres hw ⟨hdv, h1, a1, hvt, a2, a3⟩))
  · exact sem_adjB_false.1 a4 (hf2 t (pe_co_g14 h hD b hb hpos hi2 hv hres hw ⟨hdv, h2, a1, hvt, a2, a3⟩))

theorem pe_co_blow5 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 G14 D pos)
    (a b a1 a2 qa1 qa2 b1 b2 vb : Fin 14)
    (ha : a ∈ eligSet 14 D) (ha1 : a1 ∈ ineligSet 14 D) (ha2 : a2 ∈ ineligSet 14 D)
    (hb1 : b1 ∈ ineligSet 14 D) (hb2 : b2 ∈ ineligSet 14 D)
    (hvb : vb ∉ ineligSet 14 D)
    (hg : a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      (g14_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
      hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true)
    (hAn : 1 ≤ (ru D br a).card) (hsub : ru D br a ⊆ ru D br b) (hBle : (ru D br b).card ≤ 2) :
    False := by
  obtain ⟨hab, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, hda, ga1, ga2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩ := hg
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
  have hres : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 :=
    fun u' hu' ha' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', ha'⟩))).2
  have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
  have hm1 := mem_W_of_pos hpos ha1 (pe_co_g14 h hD br hbr hpos ha1 ha hres hw ⟨hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
  have hm2 := mem_W_of_pos hpos ha2 (pe_co_g14 h hD br hbr hpos ha2 ha hres hw ⟨hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
  have hb1m := as_mem hpos hb1 ((hc_adjB_iff _ _).1 gb1)
  have hb2m := as_mem hpos hb2 ((hc_adjB_iff _ _).1 gb2)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
  have h5 := pa_card5 hm1 hm2 hb1m hb2m hev
    (fun e => ha12 (hpos.2 _ ha1 _ ha2 e))
    (fun e => ha1b1 (hpos.2 _ ha1 _ hb1 e))
    (fun e => ha1b2 (hpos.2 _ ha1 _ hb2 e))
    (fun e => hvb (hfv _ ha1 e.symm ▸ ha1))
    (fun e => ha2b1 (hpos.2 _ ha2 _ hb1 e))
    (fun e => ha2b2 (hpos.2 _ ha2 _ hb2 e))
    (fun e => hvb (hfv _ ha2 e.symm ▸ ha2))
    (fun e => hb12 (hpos.2 _ hb1 _ hb2 e))
    (fun e => hvb (hfv _ hb1 e.symm ▸ hb1))
    (fun e => hvb (hfv _ hb2 e.symm ▸ hb2))
  have hc4 := cc_le h hD br hbr b
  omega

section L3TriGen
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem k4_mem_carrier {T : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D T ↔ (supp n D w ∩ T).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨v, hv⟩
  exact sem_supp_lt (Finset.mem_inter.mp hv).1

theorem k4_mem_exit {T : Finset (Fin n)} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D T) ↔
    e.1 < D.length ∧ (supp n D (src D e) ∩ T).Nonempty ∧
      ¬ (supp n D (n + e.1) ∩ T).Nonempty := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, k4_mem_carrier]

theorem k4_pos_exit {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i ∈ ineligSet n D) (hia : G i a) (haT : a ∈ T) :
    pos i ∈ exitArcs n D (carrierT n D T) := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi
  rw [k4_mem_exit]
  refine ⟨h1, ⟨a, Finset.mem_inter.mpr ⟨h3 a hia, haT⟩⟩, ?_⟩
  rw [h2, Finset.empty_inter]
  exact Finset.not_nonempty_empty

theorem k4_exits_ge {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ ∃ a ∈ T, G i a) :
    J.image pos ⊆ exitArcs n D (carrierT n D T) ∧ (J.image pos).card = J.card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi1, a, haT, hia⟩ := hJ i hi
    exact k4_pos_exit hpos hi1 hia haT
  · exact Finset.card_image_of_injOn
      (fun i hi i' hi' he => hpos.2 i (hJ i hi).1 i' (hJ i' hi').1 he)

theorem k4_budget (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (T : Finset (Fin n)) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card +
      (eligSet n D).card ≤ 2 * T.card + Bplus n D := by
  have h1 := carrier_flow_union h T (by rw [sem_supp_out hG hC, Finset.empty_inter])
  have h2 := surplus_carrierT_le h.1 b hb T
  have h3 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

theorem k4_mask_gate (hS : Strict n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2 ≤ (supp n D w ∩ T).card) :
    ∃ j ∈ merges n D (carrierT n D T), supp n D (n + j) ∩ T = supp n D w ∩ T := by
  obtain ⟨j, -, -, h3, h4, -, -⟩ := sem_first_mask hS T _ h2 w rfl
  exact ⟨j, h4, h3⟩

theorem k4_pair_merges (hS : Strict n D) {T : Finset (Fin n)} (hT : T.card = 3)
    {a b c : Fin n} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {w1 w2 : ℕ} (h1a : a ∈ supp n D w1) (h1b : b ∈ supp n D w1)
    (h2a : a ∈ supp n D w2) (h2c : c ∈ supp n D w2) :
    2 ≤ (merges n D (carrierT n D T)).card := by
  have m1a : a ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1a, ha⟩
  have m1b : b ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1b, hb⟩
  have m2a : a ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2a, ha⟩
  have m2c : c ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2c, hc⟩
  have c1 : 2 ≤ (supp n D w1 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m1a, b, m1b, hab⟩
  have c2 : 2 ≤ (supp n D w2 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m2a, c, m2c, hac⟩
  obtain ⟨j1, hj1, e1⟩ := k4_mask_gate hS T w1 c1
  by_cases heq : supp n D w1 ∩ T = supp n D w2 ∩ T
  · have hfull : supp n D w1 ∩ T = T := by
      refine Finset.eq_of_subset_of_card_le Finset.inter_subset_right ?_
      rw [hT]
      exact Finset.two_lt_card.mpr
        ⟨a, m1a, b, m1b, c, by rw [heq]; exact m2c, hab, hac, hbc⟩
    obtain ⟨j, -, -, h3, h4, -, hcase⟩ := sem_first_mask hS T T (by omega) w1 hfull
    rcases hcase with ⟨-, hA, -⟩ | ⟨-, hA, hB, hU, -, -⟩
    · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA Finset.inter_subset_right).ne
    · have hcard : 3 ≤ (supp n D (opA D j) ∩ T).card + (supp n D (opB D j) ∩ T).card := by
        have := Finset.card_union_le (supp n D (opA D j) ∩ T) (supp n D (opB D j) ∩ T)
        rw [hU, hT] at this
        exact this
      have key : ∀ w, supp n D w ∩ T ⊂ T → 2 ≤ (supp n D w ∩ T).card →
          2 ≤ (merges n D (carrierT n D T)).card := by
        intro w hss hc2
        obtain ⟨j', hj', e'⟩ := k4_mask_gate hS T w hc2
        refine Finset.one_lt_card.mpr ⟨j, h4, j', hj', fun hjj => ?_⟩
        rw [hjj, e'] at h3
        exact hss.ne h3
      by_cases hc2 : 2 ≤ (supp n D (opA D j) ∩ T).card
      · exact key _ hA hc2
      · exact key _ hB (by omega)
  · obtain ⟨j2, hj2, e2⟩ := k4_mask_gate hS T w2 c2
    exact Finset.one_lt_card.mpr ⟨j1, hj1, j2, hj2, fun hjj => heq (by rw [← e1, ← e2, hjj])⟩

theorem tri_exits (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a) :
    J.card + T.card ≤ (exitArcs n D (carrierT n D T)).card := by
  classical
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ T, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w T := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, hg⟩))
  have hdis : Disjoint (J.image pos) (T.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : T.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at this
  exact this

theorem tri_bound (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a)
    {x y z : Fin n} (hT : T = {x, y, z}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {w v : ℕ}
    (hx : x ∈ supp n D w) (hy : y ∈ supp n D w) (hx' : x ∈ supp n D v) (hz : z ∈ supp n D v) :
    J.card + 2 + (eligSet n D).card ≤ 3 + Bplus n D := by
  have hT3 : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have h1 := tri_exits hG h.1 hC hpos T J A hJ hA
  have h2 := k4_pair_merges h.1 hT3 (a := x) (b := y) (c := z) (by simp [hT]) (by simp [hT])
    (by simp [hT]) hxy hxz hyz hx hy hx' hz
  have h4 := carrier_flow_union h T (by rw [sem_supp_out hG hC]; simp)
  have h5 := surplus_carrierT_le h.1 b hb T
  have h6 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

theorem tri_occ (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a)
    (F : Finset (Finset (Fin n))) (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D T M) :
    J.card + F.card + (eligSet n D).card ≤ T.card + Bplus n D := by
  have h1 := tri_exits hG h.1 hC hpos T J A hJ hA
  have h2 := sup_card_le_big h.1 T F hF
  have h3 : (sup_big n D T).card ≤ (merges n D (carrierT n D T)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h4 := carrier_flow_union h T (by rw [sem_supp_out hG hC]; simp)
  have h5 := surplus_carrierT_le h.1 b hb T
  have h6 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

theorem tri_sat (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a)
    (F : Finset (Finset (Fin n))) (hF : ∀ M ∈ F, M.card = 2 ∧ sup_Occ n D T M)
    (hT3 : T.card = 3)
    (hbud : T.card + Bplus n D ≤ J.card + F.card + (eligSet n D).card) :
    (∀ w, ¬ T ⊆ supp n D w) ∧
    (∀ t ∈ T, merges n D (carrierT n D {t}) = ∅ ∧
      ∃ e1, ∀ e ∈ sem_W n D t, e = e1 ∨ e ∈ J.image pos) ∧
    ∀ u ∈ residualUnits n D b, (supp n D u.1 ∩ T).Nonempty := by
  classical
  have hS := h.1
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ T, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w T := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, hg⟩))
  have hdis : Disjoint (J.image pos) (T.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : T.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have hF2 : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D T M :=
    fun M hM => ⟨by rw [(hF M hM).1], (hF M hM).2⟩
  have h2 := sup_card_le_big hS T F hF2
  have h3 : (sup_big n D T).card ≤ (merges n D (carrierT n D T)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h4 := carrier_flow_union h T (by rw [sem_supp_out hG hC]; simp)
  have h5 := surplus_carrierT_le hS b hb T
  have h6 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  have hEx := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at hEx
  have hexeq : J.image pos ∪ T.image w = exitArcs n D (carrierT n D T) :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hsub hsub2) (by
      rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj]; omega)
  have hbig : sup_big n D T = merges n D (carrierT n D T) :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hnofull : ∀ w', ¬ T ⊆ supp n D w' := by
    intro w' hTw
    have hnot : T ∉ F := fun hTF => by have := (hF T hTF).1; omega
    have := sup_card_le_big hS T (insert T F) (fun M hM => by
      rcases Finset.mem_insert.1 hM with rfl | hM
      · exact ⟨by omega, ⟨w', Finset.inter_eq_right.2 hTw⟩⟩
      · exact hF2 M hM)
    rw [Finset.card_insert_of_notMem hnot] at this
    omega
  have hunits : ∀ u ∈ residualUnits n D b, (supp n D u.1 ∩ T).Nonempty := by
    have h7 := surplus_carrierT_eq hS b hb T
    have h8 := card_residual hS b hb
    have heq : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
        residualUnits n D b :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    intro u hu
    rw [← heq] at hu
    exact (Finset.mem_filter.1 hu).2
  have hmask : Set.InjOn (fun j => supp n D (n + j) ∩ T) (sup_big n D T) := by
    have hsubF : F ⊆ (sup_big n D T).image (fun j => supp n D (n + j) ∩ T) := by
      intro M hM
      obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF2 M hM).1 (hF M hM).2
      exact Finset.mem_image.2 ⟨j, hj, hjM⟩
    have := Finset.card_le_card hsubF
    exact Finset.card_image_iff.1 (le_antisymm Finset.card_image_le (by omega))
  have hmemT : ∀ {t : Fin n} {v : ℕ}, t ∈ T → t ∈ supp n D v → v ∈ carrierT n D T :=
    fun ht hv => sup_mem_carrier.2 ⟨_, Finset.mem_inter.2 ⟨hv, ht⟩⟩
  refine ⟨hnofull, fun t ht => ⟨?_, w t, fun e he => ?_⟩, hunits⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [merges, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjl, hj1, hj2, hj3⟩ := hj
    rw [sem_mem_carrier1] at hj1 hj2 hj3
    have hjT : j ∈ sup_big n D T := by
      rw [hbig, merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, hmemT ht hj1, hmemT ht hj2, hmemT ht hj3⟩
    have hM2 : 2 ≤ (supp n D (n + j) ∩ T).card := (Finset.mem_filter.1 hjT).2
    obtain ⟨j0, -, -, hj0M, hj0mer, -, hstr⟩ := sem_first_mask hS T _ hM2 (n + j) rfl
    have hjj : j0 = j :=
      hmask (Finset.mem_filter.2 ⟨hj0mer, by rw [hj0M]; exact hM2⟩) hjT hj0M
    subst hjj
    have hlt : ∀ v, (supp n D v ∩ T).card < 3 := by
      intro v
      by_contra hc
      exact hnofull v (Finset.inter_eq_right.1
        (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)))
    rcases hstr with ⟨-, hA1, -⟩ | ⟨-, hA1, hB1, hU, -, -⟩
    · have := Finset.card_lt_card hA1
      have := hlt (opA D j0)
      omega
    · have hcA := Finset.card_lt_card hA1
      have hcB := Finset.card_lt_card hB1
      have := hlt (n + j0)
      have hA' : ({t} : Finset (Fin n)) = supp n D (opA D j0) ∩ T :=
        Finset.eq_of_subset_of_card_le
          (Finset.singleton_subset_iff.2 (Finset.mem_inter.2 ⟨hj2, ht⟩))
          (by rw [Finset.card_singleton]; omega)
      have hB' : ({t} : Finset (Fin n)) = supp n D (opB D j0) ∩ T :=
        Finset.eq_of_subset_of_card_le
          (Finset.singleton_subset_iff.2 (Finset.mem_inter.2 ⟨hj3, ht⟩))
          (by rw [Finset.card_singleton]; omega)
      rw [← hU, ← hA', ← hB', Finset.union_self, Finset.card_singleton] at hM2
      omega
  · obtain ⟨he1, he2, he3⟩ := sem_mem_W.1 he
    have htag := sem_W_and hS he
    have hexit : e ∈ exitArcs n D (carrierT n D T) := by
      refine k4_mem_exit.2 ⟨he1, ⟨t, Finset.mem_inter.2 ⟨he2, ht⟩⟩, ?_⟩
      rintro ⟨g, hg⟩
      rw [Finset.mem_inter] at hg
      have hop : ∀ s, g ∈ supp n D (src D (e.1, s)) :=
        fun s => sem_supp_and_sub hS he1 htag s hg.1
      have hjT : e.1 ∈ sup_big n D T := by
        rw [hbig, merges, Finset.mem_filter, Finset.mem_range]
        refine ⟨he1, hmemT hg.2 hg.1, hmemT hg.2 ?_, hmemT hg.2 ?_⟩
        · have := hop false
          rwa [sb_src_false] at this
        · have := hop true
          rwa [sb_src_true] at this
      have hM2 : 2 ≤ (supp n D (n + e.1) ∩ T).card := (Finset.mem_filter.1 hjT).2
      have hsubE : supp n D (n + e.1) ∩ T ⊆ T.erase t := fun a ha =>
        Finset.mem_erase.2 ⟨fun hat => he3 (hat ▸ (Finset.mem_inter.1 ha).1),
          (Finset.mem_inter.1 ha).2⟩
      have heqE := Finset.eq_of_subset_of_card_le hsubE
        (by rw [Finset.card_erase_of_mem ht, hT3]; omega)
      apply hnofull (src D e)
      intro a ha
      by_cases hat : a = t
      · rw [hat]; exact he2
      · have : a ∈ supp n D (n + e.1) ∩ T := by
          rw [heqE]; exact Finset.mem_erase.2 ⟨hat, ha⟩
        exact sem_supp_and_sub hS he1 htag e.2 (Finset.mem_inter.1 this).1
    rw [← hexeq, Finset.mem_union] at hexit
    rcases hexit with h1 | h1
    · exact Or.inr h1
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 h1
      left
      by_cases hft : f = t
      · rw [← hfe, hft]
      · exfalso
        exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfe ▸ he2)
          ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hft h.symm, ht⟩))

end L3TriGen

theorem mem_ru {D : Dag} {b : Fin 14 → ℕ} {x : Fin 14} {u : Σ _ : ℕ, ℕ} :
    u ∈ ru D b x ↔ u ∈ residualUnits 14 D b ∧ x ∈ supp 14 D u.1 := Finset.mem_filter

theorem sem_g14_common : ∀ a b x y : Fin 14, a ≠ b →
    hc_adjB a x = true → hc_adjB b x = true → hc_adjB a y = true → hc_adjB b y = true → x = y := by
  decide +kernel

theorem bip_same_side : ∀ w a b : Fin 14,
    hc_adjB w a = true → hc_adjB w b = true → decide (a.val < 7) = decide (b.val < 7) := by
  decide +kernel

theorem pos_bar_mem {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {i : Fin 14} (hi : i ∈ ineligSet 14 D) : i ∈ supp 14 D (src D (sem_bar (pos i))) := by
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, (hpos.1 i hi).2.2.2]
  exact Finset.mem_singleton_self i

theorem ru_one_two_common {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : sem_MinBranch 14 D b) {u0 : Σ _ : ℕ, ℕ} {x : Fin 14}
    (hru : ru D b x = {u0}) (h3 : 3 ≤ (sem_W 14 D x).card) :
    ∃ P Q : ℕ × Bool, P ≠ Q ∧
      ∀ y : Fin 14, y ∈ supp 14 D u0.1 → ru D b y = {u0} → 3 ≤ (sem_W 14 D y).card →
        P ∈ sem_W 14 D y ∧ Q ∈ sem_W 14 D y := by
  classical
  have hbp := sem_minBranch_pure hb
  have hu0m : u0 ∈ ru D b x := by rw [hru]; exact Finset.mem_singleton_self u0
  obtain ⟨hu0r, -⟩ := mem_ru.1 hu0m
  let X := Finset.univ.filter (fun y : Fin 14 => y ∈ supp 14 D u0.1 ∧ ru D b y = {u0} ∧ 3 ≤ (sem_W 14 D y).card)
  have hxX : x ∈ X := Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_ru.1 hu0m).2, hru, h3⟩
  obtain ⟨P, Q, hPQ, hall⟩ := gct_gen sem_g14_gr h (sem_g14_comp hD) b hb hu0r X ⟨x, hxX⟩ (fun y hy => by
    obtain ⟨-, hyu, hruy, hy3⟩ := Finset.mem_filter.1 hy
    have hcc := cc_le h hD b hbp y
    rw [hruy, Finset.card_singleton] at hcc
    refine ⟨Finset.card_eq_zero.1 (by omega), hyu, fun u hu hyu' => ?_⟩
    exact Finset.mem_singleton.1 (hruy ▸ mem_ru.2 ⟨hu, hyu'⟩))
  exact ⟨P, Q, fun he => hPQ (he ▸ rfl), fun y hy1 hy2 hy3 =>
    hall y (Finset.mem_filter.2 ⟨Finset.mem_univ _, hy1, hy2, hy3⟩)⟩

theorem ru_one_two_supp {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : sem_MinBranch 14 D b) {u0 : Σ _ : ℕ, ℕ} {x : Fin 14}
    (hru : ru D b x = {u0}) (h3 : 3 ≤ (sem_W 14 D x).card) :
    ∃ P Q : ℕ × Bool, P ≠ Q ∧ P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x ∧
      ∀ y : Fin 14, y ∈ supp 14 D u0.1 → y ∈ supp 14 D (src D P) ∧ y ∈ supp 14 D (src D Q) := by
  classical
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  have hcc := cc_le h hD b hbp x
  rw [hru, Finset.card_singleton] at hcc
  have hM : merges 14 D (carrierT 14 D {x}) = ∅ := Finset.card_eq_zero.1 (by omega)
  have hu0m : u0 ∈ ru D b x := by rw [hru]; exact Finset.mem_singleton_self u0
  obtain ⟨hu0r, hxu0⟩ := mem_ru.1 hu0m
  have hu0u : u0 ∈ units 14 D := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hu0r).1).1
  have hfr : 2 ≤ fanout D u0.1 := by have := (mem_units.1 hu0u).2; omega
  have hxe : x ∈ eligSet 14 D := res_elig hu0r hxu0
  have hlow : ∀ w, u0.1 < w → x ∈ supp 14 D w → fanout D w ≤ 1 := by
    intro w hrw hxw
    by_contra hc
    have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 14 D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.2 (lt_of_fanout_pos hS (w := w) (by omega)),
        by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
    by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 14 D b
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 hwr
      have hbv : b v = w := congrArg Sigma.fst hveq
      have hsv := (hb v hv).2.1; rw [hbv] at hsv; rw [hsv, Finset.mem_singleton] at hxw
      have hmin := (hb x hxe).2.2.2 u0.1 hfr hxu0
      rw [hxw, hbv] at hmin; omega
    · have h1 : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ ru D b x := mem_ru.2 ⟨Finset.mem_sdiff.2 ⟨hwu, hwr⟩, hxw⟩
      rw [hru, Finset.mem_singleton] at h1
      have : w = u0.1 := congrArg Sigma.fst h1
      omega
  have harm_sub : ∀ {a c : ℕ}, Relation.ReflTransGen (sem_Arm 14 D {x}) a c →
      supp 14 D a ⊆ supp 14 D c := by
    intro a c hp
    induction hp with
    | refl => exact Finset.Subset.refl _
    | @tail u v _ huv ih =>
      obtain ⟨hj, hge, hop⟩ := huv.1
      have hv : 14 + (v - 14) = v := by omega
      have hxv : x ∈ supp 14 D (14 + (v - 14)) := by
        rw [hv]; exact (huv.2.2 x (Finset.mem_singleton_self x)).2
      have htag : tag D (v - 14) = false := (sem_zm_gate hS hM (by omega) hxv).1
      exact ih.trans (by
        rw [← hv, sem_supp_or hS (by omega) htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right)
  have hread : ∀ j ∈ readers D u0.1,
      j < D.length ∧ u0.1 < 14 + j ∧ (opA D j = u0.1 ∨ opB D j = u0.1) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D u0.1, ∃ e : ℕ × Bool, e ∈ sem_W 14 D x ∧
      supp 14 D u0.1 ⊆ supp 14 D (src D e) ∧
      ((e.1 = j ∧ src D e = u0.1) ∨ Relation.ReflTransGen (sem_Arm 14 D {x}) (14 + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hlt, hop⟩ := hread j hj
    by_cases hxj : x ∈ supp 14 D (14 + j)
    · have htag : tag D j = false := (sem_zm_gate hS hM hjl hxj).1
      have hsub1 : supp 14 D u0.1 ⊆ supp 14 D (14 + j) := by
        rw [sem_supp_or hS hjl htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right
      obtain ⟨e, he1, he2⟩ := sem_descent sem_g14_gr h (sem_g14_comp hD) {x}
        ⟨x, Finset.mem_singleton_self x⟩
        (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hM)
        (14 + j) (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hxj)
        (fun y hy w hrw hyw => by rw [Finset.mem_singleton.1 hy] at hyw; exact hlow w (by omega) hyw)
      exact ⟨e, he1 x (Finset.mem_singleton_self x), hsub1.trans (harm_sub he2), Or.inr he2⟩
    · rcases hop with he | he
      · refine ⟨(j, false), sem_mem_W.2 ⟨hjl, by rw [sb_src_false, he]; exact hxu0, hxj⟩,
          by rw [sb_src_false, he], Or.inl ⟨rfl, by rw [sb_src_false, he]⟩⟩
      · refine ⟨(j, true), sem_mem_W.2 ⟨hjl, by rw [sb_src_true, he]; exact hxu0, hxj⟩,
          by rw [sb_src_true, he], Or.inl ⟨rfl, by rw [sb_src_true, he]⟩⟩
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.1 (by exact hfr : 1 < (readers D u0.1).card)
  have hRstep : ∀ a c, sem_Arm 14 D {x} a c → sem_step 14 D a c := fun _ _ hr => hr.1
  have hfun : ∀ a a' c, sem_Arm 14 D {x} a c → sem_Arm 14 D {x} a' c → a = a' := by
    intro a a' c h1 h2
    by_contra hne2
    obtain ⟨hjl, hge1, hop1⟩ := h1.1
    obtain ⟨-, -, hop2⟩ := h2.1
    have hcv : 14 + (c - 14) = c := by omega
    have ha := (h1.2.2 x (Finset.mem_singleton_self x)).1
    have ha' := (h2.2.2 x (Finset.mem_singleton_self x)).1
    have hc := (h1.2.2 x (Finset.mem_singleton_self x)).2
    have hxc : x ∈ supp 14 D (14 + (c - 14)) := by rw [hcv]; exact hc
    apply (sem_zm_gate hS hM (by omega) hxc).2
    rcases hop1 with e1 | e1 <;> rcases hop2 with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D u0.1, ∀ jb ∈ readers D u0.1, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm 14 D {x}) (14 + ja) (14 + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨-, hlta, -⟩ := hread ja hja
    obtain ⟨hjlb, -, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = u0.1 := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS hM hjlb (hu2.2.2 x (Finset.mem_singleton_self x)).2).2
        have hu := (hu2.2.2 x (Finset.mem_singleton_self x)).1
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hxu0⟩
        · rw [e1, e2]; exact ⟨hxu0, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hPx, hPsub, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQx, hQsub, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, hPx, hQx, fun y hy => ⟨hPsub hy, hQsub hy⟩⟩
  rw [← hPQ] at hQ2
  rcases hP2 with ⟨h1, h2⟩ | h1 <;> rcases hQ2 with ⟨h3, h4⟩ | h3
  · exact hne (h1.symm.trans h3)
  · have hle := sem_rtg_le hS hRstep h3
    have := (hread j2 hj2).2.1; rw [h2] at hle; omega
  · have hle := sem_rtg_le hS hRstep h1
    have := (hread j1 hj1).2.1; rw [h4] at hle; omega
  · rcases sem_rtg_comparable hfun h1 h3 with h12 | h21
    · exact hcross j1 hj1 j2 hj2 hne h12
    · exact hcross j2 hj2 j1 hj1 hne.symm h21

theorem w3_ru_one_pure {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (b : Fin 14 → ℕ) (hb : sem_MinBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {u0 : Σ _ : ℕ, ℕ} {a i1 i2 v3 : Fin 14}
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hg : (g14_nbB a).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 a = true ∧ hc_adjB i2 a = true ∧
          hc_adjB a v3 = true ∧ v3 ≠ i1 ∧ v3 ≠ i2)
    (hru : ru D b a = {u0}) : ∀ y, y ∈ supp 14 D u0.1 → y = a := by
  have hbp := sem_minBranch_pure hb
  obtain ⟨hd3, h12, ha1, ha2, hav, hv1, hv2⟩ := hg
  have h3 := two_in_deg3 h hD hpos hi1 hi2 ⟨h12, ha1, ha2, hav, hv1, hv2⟩
  have hle3 : (sem_W 14 D a).card ≤ 3 := by
    have := cc_le h hD b hbp a; rw [hru, Finset.card_singleton] at this; omega
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 ⟨h12, ha1, ha2, hav, hv1, hv2⟩ hle3
  obtain ⟨P, Q, hPQ, hPa, hQa, hsupp⟩ := ru_one_two_supp h hD b hb hru h3
  have hp1 : pos i1 ∈ sem_W 14 D a := as_mem hpos hi1 ((hc_adjB_iff _ _).1 ha1)
  have hp2 : pos i2 ∈ sem_W 14 D a := as_mem hpos hi2 ((hc_adjB_iff _ _).1 ha2)
  have hp12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 _ hi1 _ hi2 e)
  intro y hy
  by_contra hya
  obtain ⟨hyP, hyQ⟩ := hsupp y hy
  by_cases h1in : pos i1 = P ∨ pos i1 = Q
  · by_cases h2in : pos i2 = P ∨ pos i2 = Q
    · have hadj1 : Adj i1 y := hf1 y (by rcases h1in with rfl | rfl <;> assumption)
      have hadj2 : Adj i2 y := hf2 y (by rcases h2in with rfl | rfl <;> assumption)
      exact hya (sem_g14_common i1 i2 y a h12 ((hc_adjB_iff _ _).2 hadj1) ((hc_adjB_iff _ _).2 hadj2) ha1 ha2)
    · rw [not_or] at h2in
      have hadj1 : Adj i1 y := hf1 y (by rcases h1in with rfl | rfl <;> assumption)
      obtain ⟨q, hq2, hqa⟩ := sem_g14_second i2 a
      have hside_ya : decide (y.val < 7) = decide (a.val < 7) := bip_same_side i1 y a ((hc_adjB_iff _ _).2 hadj1) ha1
      have hside_qa : decide (q.val < 7) = decide (a.val < 7) := bip_same_side i2 q a hq2 ha2
      have hnyq : ¬ Adj y q := fun hadj => by
        have h1 := g14_sides y q ((hc_adjB_iff _ _).2 hadj)
        rw [hside_ya, hside_qa] at h1; exact h1 rfl
      obtain ⟨e, he, hny, hnq⟩ := g14_deg3_cover_free h hD hd3 (Ne.symm hya) (Ne.symm hqa) hnyq
      rcases pa_three hPa hQa hp2 hPQ (Ne.symm h2in.1) (Ne.symm h2in.2) hle3 e he with rfl | rfl | rfl
      · exact hny hyP
      · exact hny hyQ
      · exact hnq ((hpos.1 i2 hi2).2.2.1 q ((hc_adjB_iff _ _).1 hq2))
  · rw [not_or] at h1in
    have h2in : pos i2 = P ∨ pos i2 = Q := by
      rcases pa_three hPa hQa hp1 hPQ (Ne.symm h1in.1) (Ne.symm h1in.2) hle3 (pos i2) hp2 with he | he | he
      · exact Or.inl he
      · exact Or.inr he
      · exact absurd he hp12.symm
    have hadj2 : Adj i2 y := hf2 y (by rcases h2in with rfl | rfl <;> assumption)
    obtain ⟨q, hq1, hqa⟩ := sem_g14_second i1 a
    have hside_ya : decide (y.val < 7) = decide (a.val < 7) := bip_same_side i2 y a ((hc_adjB_iff _ _).2 hadj2) ha2
    have hside_qa : decide (q.val < 7) = decide (a.val < 7) := bip_same_side i1 q a hq1 ha1
    have hnyq : ¬ Adj y q := fun hadj => by
      have h1 := g14_sides y q ((hc_adjB_iff _ _).2 hadj)
      rw [hside_ya, hside_qa] at h1; exact h1 rfl
    obtain ⟨e, he, hny, hnq⟩ := g14_deg3_cover_free h hD hd3 (Ne.symm hya) (Ne.symm hqa) hnyq
    rcases pa_three hPa hQa hp1 hPQ (Ne.symm h1in.1) (Ne.symm h1in.2) hle3 e he with rfl | rfl | rfl
    · exact hny hyP
    · exact hny hyQ
    · exact hnq ((hpos.1 i1 hi1).2.2.1 q ((hc_adjB_iff _ _).1 hq1))

def r0_wit (idx : Fin 68) : ℕ × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 :=
  match idx.val with
  | 0 => (2, 2, 8, 13, 12, 0, 1)
  | 1 => (0, 8, 0, 2, 6, 0, 0)
  | 2 => (0, 13, 1, 2, 4, 0, 0)
  | 3 => (2, 2, 12, 13, 8, 3, 1)
  | 4 => (0, 13, 2, 4, 1, 0, 0)
  | 5 => (0, 10, 4, 5, 0, 0, 0)
  | 6 => (0, 0, 0, 0, 0, 0, 0)
  | 7 => (1, 1, 13, 9, 7, 2, 0)
  | 8 => (1, 2, 13, 12, 8, 1, 0)
  | 9 => (1, 2, 13, 12, 8, 4, 0)
  | 10 => (1, 1, 13, 7, 9, 2, 0)
  | 11 => (0, 8, 0, 2, 6, 0, 0)
  | 12 => (2, 2, 8, 12, 13, 0, 3)
  | 13 => (0, 12, 2, 3, 5, 0, 0)
  | 14 => (0, 8, 0, 2, 6, 0, 0)
  | 15 => (0, 13, 1, 2, 4, 0, 0)
  | 16 => (0, 11, 3, 4, 6, 0, 0)
  | 17 => (0, 10, 0, 4, 5, 0, 0)
  | 18 => (0, 9, 1, 5, 6, 0, 0)
  | 19 => (0, 10, 4, 5, 0, 0, 0)
  | 20 => (0, 8, 0, 2, 6, 0, 0)
  | 21 => (0, 13, 2, 4, 1, 0, 0)
  | 22 => (0, 10, 4, 5, 0, 0, 0)
  | 23 => (1, 2, 12, 13, 8, 3, 0)
  | 24 => (0, 13, 1, 4, 2, 0, 0)
  | 25 => (0, 10, 4, 5, 0, 0, 0)
  | 26 => (1, 1, 13, 9, 7, 4, 0)
  | 27 => (0, 8, 0, 2, 6, 0, 0)
  | 28 => (0, 12, 2, 3, 5, 0, 0)
  | 29 => (0, 13, 2, 4, 1, 0, 0)
  | 30 => (0, 8, 0, 2, 6, 0, 0)
  | 31 => (0, 8, 0, 2, 6, 0, 0)
  | 32 => (0, 8, 0, 2, 6, 0, 0)
  | 33 => (0, 11, 3, 4, 6, 0, 0)
  | 34 => (0, 9, 1, 5, 6, 0, 0)
  | 35 => (0, 8, 0, 2, 6, 0, 0)
  | 36 => (0, 9, 1, 5, 6, 0, 0)
  | 37 => (0, 9, 1, 5, 6, 0, 0)
  | 38 => (0, 8, 2, 6, 0, 0, 0)
  | 39 => (0, 8, 0, 2, 6, 0, 0)
  | 40 => (0, 10, 0, 4, 5, 0, 0)
  | 41 => (0, 10, 4, 5, 0, 0, 0)
  | 42 => (0, 11, 3, 4, 6, 0, 0)
  | 43 => (0, 9, 1, 5, 6, 0, 0)
  | 44 => (0, 10, 4, 5, 0, 0, 0)
  | 45 => (0, 8, 0, 2, 6, 0, 0)
  | 46 => (0, 8, 0, 2, 6, 0, 0)
  | 47 => (0, 11, 3, 4, 6, 0, 0)
  | 48 => (0, 1, 7, 9, 13, 0, 0)
  | 49 => (0, 1, 7, 9, 13, 0, 0)
  | 50 => (0, 6, 8, 9, 11, 0, 0)
  | 51 => (1, 2, 12, 13, 8, 3, 0)
  | 52 => (0, 8, 0, 2, 6, 0, 0)
  | 53 => (0, 8, 0, 2, 6, 0, 0)
  | 54 => (0, 9, 1, 5, 6, 0, 0)
  | 55 => (0, 9, 1, 5, 6, 0, 0)
  | 56 => (0, 8, 0, 2, 6, 0, 0)
  | 57 => (0, 8, 2, 6, 0, 0, 0)
  | 58 => (0, 8, 0, 2, 6, 0, 0)
  | 59 => (0, 8, 2, 6, 0, 0, 0)
  | 60 => (0, 9, 1, 5, 6, 0, 0)
  | 61 => (0, 8, 0, 2, 6, 0, 0)
  | 62 => (0, 1, 7, 9, 13, 0, 0)
  | 63 => (0, 8, 0, 2, 6, 0, 0)
  | 64 => (0, 8, 0, 2, 6, 0, 0)
  | 65 => (0, 8, 2, 6, 0, 0, 0)
  | 66 => (0, 8, 0, 2, 6, 0, 0)
  | _ => (0, 8, 0, 2, 6, 0, 0)

theorem r0_wit_ok : ∀ idx : Fin 68, idx.val ≠ 6 →
    let I := hc_rep idx
    let (k, a, b, c, d, e, f) := r0_wit idx
    if k = 0 then
      b ∈ I ∧ c ∈ I ∧ b ≠ c ∧ hc_adjB b a = true ∧ hc_adjB c a = true ∧
        hc_adjB a d = true ∧ d ≠ b ∧ d ≠ c
    else if k = 1 then
      d ∈ I ∧ e ∈ I ∧ a ∉ I ∧ b ∉ I ∧ c ∉ I ∧
        hc_adjB d a = true ∧ hc_adjB e b = true ∧ hc_adjB a b = true ∧
        hc_adjB a c = true ∧ c ≠ b ∧ (g14_nbB b).card = 3 ∧
        decide (c.val < 7) = decide (b.val < 7)
    else
      e ∈ I ∧ f ∈ I ∧ a ∉ I ∧
        hc_adjB a b = true ∧ hc_adjB a c = true ∧ hc_adjB a d = true ∧
        hc_adjB e b = true ∧ hc_adjB f c = true ∧
        b ≠ c ∧ d ≠ b ∧ d ≠ c ∧
        (g14_nbB b).card = 3 ∧ (g14_nbB c).card = 3 ∧
        decide (b.val < 7) = decide (c.val < 7) ∧ decide (d.val < 7) = decide (b.val < 7) := by
  decide +kernel

theorem elim_07_R0 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    (hI : ineligSet 14 D = {0, 7}) (hW2 : ∀ x, (sem_W 14 D x).card ≤ 2) : False := by
  have h0 : (0 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have h7 : (7 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hn6 : (6 : Fin 14) ∉ ineligSet 14 D := by rw [hI]; decide
  have hn2 : (2 : Fin 14) ∉ ineligSet 14 D := by rw [hI]; decide
  have hn9 : (9 : Fin 14) ∉ ineligSet 14 D := by rw [hI]; decide
  have hn5 : (5 : Fin 14) ∉ ineligSet 14 D := by rw [hI]; decide
  obtain ⟨Z8, -, hW8, hp8⟩ := ps_side h hD hpos h0 (by decide : Adj 0 8) (by decide) (hW2 8)
  obtain ⟨Z1, -, hW1, hp1⟩ := ps_side h hD hpos h7 (by decide : Adj 7 1) (by decide) (hW2 1)
  obtain ⟨e68, h68_6, h68_8, -, hf68'⟩ := pa_ed h hD hpos (by decide : Adj 6 8)
  obtain ⟨e28, h28_2, h28_8, -, hf28'⟩ := pa_ed h hD hpos (by decide : Adj 2 8)
  obtain ⟨e69, h69_6, h69_9, -, -⟩ := pa_ed h hD hpos (by decide : Adj 6 9)
  obtain ⟨e91, h91_9, h91_1, -, hf91'⟩ := pa_ed h hD hpos (by decide : Adj 9 1)
  obtain ⟨e95, h95_9, h95_5, -, -⟩ := pa_ed h hD hpos (by decide : Adj 9 5)
  rw [hW8, Finset.mem_insert, Finset.mem_singleton] at h68_8 h28_8
  have hb68 : sem_bar e68 = Z8 := h68_8.resolve_left (fun hh => hn6 (hf68' 0 h0 hh ▸ h0))
  have hb28 : sem_bar e28 = Z8 := h28_8.resolve_left (fun hh => hn2 (hf28' 0 h0 hh ▸ h0))
  have he28_eq : e28 = e68 := by rw [← sem_bar_bar e28, ← sem_bar_bar e68, hb28, hb68]
  rw [hW1, Finset.mem_insert, Finset.mem_singleton] at h91_1
  have hb91 : sem_bar e91 = Z1 := h91_1.resolve_left (fun hh => hn9 (hf91' 7 h7 hh ▸ h7))
  have hne_68_69 : e68 ≠ e69 := fun hh => hp8 9 (by decide) (by decide) (by rw [← hb68, hh]; exact h69_9)
  have hne_91_69 : e91 ≠ sem_bar e69 := fun hh =>
    hp1 6 (by decide) (by decide) (by rw [← hb91, hh, sem_bar_bar]; exact h69_6)
  have he95_eq : e95 = sem_bar e69 := by
    rcases pa_two h91_9 h69_9 hne_91_69 (hW2 9) e95 h95_9 with heq | heq
    · exact absurd (by rw [← hb91, ← heq]; exact h95_5) (hp1 5 (by decide) (by decide))
    · exact heq
  have h69_in5 : e69 ∈ sem_W 14 D 5 := by rw [← sem_bar_bar e69, ← he95_eq]; exact h95_5
  obtain ⟨f, hf, hn2f, hn5f⟩ := g14_deg3_cover_free h hD (by decide : (g14_nbB 6).card = 3)
    (by decide : (6 : Fin 14) ≠ 2) (by decide : (6 : Fin 14) ≠ 5) (by decide : ¬ Adj 2 5)
  rcases pa_two h68_6 h69_6 hne_68_69 (hW2 6) f hf with rfl | rfl
  · exact hn2f (sem_mem_W.1 (he28_eq ▸ h28_2)).2.1
  · exact hn5f (sem_mem_W.1 h69_in5).2.1

theorem elim_R0_all {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card) (idx : Fin 68) (hI : ineligSet 14 D = hc_rep idx) :
    False := by
  classical
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hres : residualUnits 14 D b = ∅ := by
    have h1 := card_residual h.1 b hb
    have h2 := elig_le_Bplus h.1 b hb
    exact Finset.card_eq_zero.1 (by omega)
  have hW2 : ∀ x, (sem_W 14 D x).card ≤ 2 := fun x => by
    have h1 := cc_le h hD b hb x
    unfold ru at h1; rw [hres] at h1
    simp only [Finset.filter_empty, Finset.card_empty] at h1; omega
  by_cases h6 : idx.val = 6
  · have hIeq : ineligSet 14 D = {0, 7} := by
      rw [hI, show idx = ⟨6, by decide⟩ from Fin.ext h6]; decide
    exact elim_07_R0 h hD hpos hIeq hW2
  · have hw := r0_wit_ok idx h6
    dsimp only at hw
    rcases hrw : r0_wit idx with ⟨k, a, b', c, d, e, f⟩
    rw [hrw] at hw
    by_cases hk0 : k = 0
    · simp only [hk0, ↓reduceIte] at hw
      obtain ⟨hi1, hi2, hg⟩ := hw
      have h3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) hg
      have := hW2 a; omega
    · by_cases hk1 : k = 1
      · simp only [hk1, ↓reduceIte] at hw
        obtain ⟨hd, he, ha, hb', hc', hg⟩ := hw
        exact pa_m1 h hD hpos a b' c d e (hI ▸ hd) (hI ▸ he) (hI ▸ ha) (hI ▸ hb') (hI ▸ hc') hg
          (hW2 a) (hW2 b')
      · simp only [hk0, hk1, ↓reduceIte] at hw
        obtain ⟨he, hf, ha, hg⟩ := hw
        exact ps_side_3star h hD hpos a b' c d e f (hI ▸ he) (hI ▸ hf) (hI ▸ ha) hg
          (hW2 a) (hW2 b') (hW2 c)

theorem two_w3_R1_kill {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    {x y i1 i2 vx j1 j2 vy q : Fin 14}
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hj1 : j1 ∈ ineligSet 14 D) (hj2 : j2 ∈ ineligSet 14 D)
    (hg : x ≠ y ∧ q ≠ x ∧ hc_adjB y q = false ∧ (g14_nbB x).card = 3 ∧
          i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x vx = true ∧ vx ≠ i1 ∧ vx ≠ i2 ∧
          j1 ≠ j2 ∧ hc_adjB j1 y = true ∧ hc_adjB j2 y = true ∧ hc_adjB y vy = true ∧ vy ≠ j1 ∧ vy ≠ j2 ∧
          hc_adjB i1 y = false ∧ hc_adjB i1 q = true) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxy, hqx, hnyq, hdx, h12, hx1, hx2, hxv, hv1, hv2, hj12, hy1, hy2, hyv, hvy1, hvy2, hni1y, hq1⟩ := hg
  have hx3 := two_in_deg3 h hD hpos hi1 hi2 ⟨h12, hx1, hx2, hxv, hv1, hv2⟩
  have hy3 := two_in_deg3 h hD hpos hj1 hj2 ⟨hj12, hy1, hy2, hyv, hvy1, hvy2⟩
  obtain ⟨hPx, hQx⟩ := hsat x hx3
  obtain ⟨hPy, hQy⟩ := hsat y hy3
  have hi1_not_Wy : pos i1 ∉ sem_W 14 D y := by
    have hpj1 := as_mem hpos hj1 ((hc_adjB_iff _ _).1 hy1)
    have hpj2 := as_mem hpos hj2 ((hc_adjB_iff _ _).1 hy2)
    have hpj12 : pos j1 ≠ pos j2 := fun e => hj12 (hpos.2 _ hj1 _ hj2 e)
    have hni1j1 : i1 ≠ j1 := fun e => by subst e; rw [hy1] at hni1y; exact Bool.noConfusion hni1y
    have hni1j2 : i1 ≠ j2 := fun e => by subst e; rw [hy2] at hni1y; exact Bool.noConfusion hni1y
    intro hm
    by_cases hvy : vy ∈ ineligSet 14 D
    · have hpvy := as_mem hpos hvy (adj_symm ((hc_adjB_iff _ _).1 hyv))
      have hni1vy : i1 ≠ vy := fun e => by
        subst e
        have := (hc_adjB_iff y i1).1 hyv
        exact sem_adjB_false.1 hni1y (adj_symm this)
      rcases pa_three hpj1 hpj2 hpvy hpj12 (fun e => hvy1.symm (hpos.2 _ hj1 _ hvy e))
          (fun e => hvy2.symm (hpos.2 _ hj2 _ hvy e)) (hc3 y) (pos i1) hm with e | e | e
      · exact hni1j1 (hpos.2 _ hi1 _ hj1 e)
      · exact hni1j2 (hpos.2 _ hi1 _ hj2 e)
      · exact hni1vy (hpos.2 _ hi1 _ hvy e)
    · obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 hyv)
      rcases pa_three hpj1 hpj2 hev hpj12 (fun e => hvy (hfv _ hj1 e.symm ▸ hj1))
          (fun e => hvy (hfv _ hj2 e.symm ▸ hj2)) (hc3 y) (pos i1) hm with e | e | e
      · exact hni1j1 (hpos.2 _ hi1 _ hj1 e)
      · exact hni1j2 (hpos.2 _ hi1 _ hj2 e)
      · exact hvy (hfv _ hi1 e.symm ▸ hi1)
  have hPne : P ≠ pos i1 := fun e => hi1_not_Wy (e ▸ hPy)
  have hQne : Q ≠ pos i1 := fun e => hi1_not_Wy (e ▸ hQy)
  have hpi1 := as_mem hpos hi1 ((hc_adjB_iff _ _).1 hx1)
  obtain ⟨e, he, hny, hnq⟩ := g14_deg3_cover_free h hD hdx hxy hqx.symm (sem_adjB_false.1 hnyq)
  rcases pa_three hPx hQx hpi1 hPQ hPne hQne (hc3 x) e he with rfl | rfl | rfl
  · exact hny (sem_mem_W.1 hPy).2.1
  · exact hny (sem_mem_W.1 hQy).2.1
  · exact hnq ((hpos.1 i1 hi1).2.2.1 q ((hc_adjB_iff _ _).1 hq1))

def r1_wit (idx : Fin 68) : ℕ × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 × Fin 14 :=
  match idx.val with
  | 0 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 1 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 2 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 3 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 4 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 5 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 6 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 7 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 8 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 9 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 10 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 11 => (0, 8, 13, 0, 2, 6, 1, 2, 4, 10, 0)
  | 12 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 13 => (0, 12, 13, 3, 2, 5, 1, 2, 4, 7, 0)
  | 14 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 15 => (2, 13, 1, 2, 4, 3, 11, 12, 7, 4, 2)
  | 16 => (0, 11, 12, 4, 3, 6, 2, 3, 5, 10, 0)
  | 17 => (2, 10, 0, 4, 5, 1, 9, 13, 7, 5, 4)
  | 18 => (0, 9, 10, 1, 5, 6, 4, 5, 0, 7, 0)
  | 19 => (0, 10, 12, 4, 5, 0, 2, 5, 3, 11, 0)
  | 20 => (1, 8, 0, 2, 6, 1, 13, 9, 7, 2, 0)
  | 21 => (1, 13, 2, 4, 1, 3, 11, 12, 7, 4, 0)
  | 22 => (1, 10, 4, 5, 0, 1, 9, 13, 7, 5, 0)
  | 23 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 24 => (1, 13, 1, 4, 2, 6, 9, 11, 8, 1, 0)
  | 25 => (1, 10, 4, 5, 0, 2, 12, 13, 8, 5, 0)
  | 26 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 27 => (1, 8, 0, 2, 6, 1, 13, 7, 9, 2, 0)
  | 28 => (1, 12, 2, 3, 5, 1, 13, 7, 9, 2, 0)
  | 29 => (1, 13, 2, 4, 1, 5, 10, 12, 9, 4, 0)
  | 30 => (0, 8, 12, 0, 2, 6, 2, 3, 5, 10, 0)
  | 31 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 32 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 33 => (0, 11, 12, 4, 3, 6, 2, 3, 5, 10, 0)
  | 34 => (0, 9, 10, 1, 5, 6, 0, 4, 5, 7, 0)
  | 35 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 36 => (0, 9, 10, 1, 5, 6, 4, 5, 0, 7, 0)
  | 37 => (0, 9, 10, 1, 5, 6, 4, 5, 0, 7, 0)
  | 38 => (0, 8, 9, 2, 6, 0, 5, 6, 1, 12, 0)
  | 39 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 40 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 41 => (0, 10, 12, 4, 5, 0, 2, 5, 3, 11, 0)
  | 42 => (0, 11, 13, 3, 4, 6, 1, 4, 2, 7, 0)
  | 43 => (0, 9, 10, 1, 5, 6, 4, 5, 0, 7, 0)
  | 44 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 45 => (0, 8, 12, 0, 2, 6, 2, 3, 5, 10, 0)
  | 46 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 47 => (0, 11, 12, 4, 3, 6, 2, 3, 5, 10, 0)
  | 48 => (0, 1, 8, 7, 9, 13, 0, 2, 6, 3, 0)
  | 49 => (0, 1, 13, 7, 9, 13, 2, 4, 1, 3, 0)
  | 50 => (0, 6, 11, 8, 9, 11, 3, 4, 6, 0, 0)
  | 51 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 52 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 53 => (0, 8, 9, 0, 2, 6, 1, 5, 6, 10, 0)
  | 54 => (0, 9, 10, 1, 5, 6, 0, 4, 5, 7, 0)
  | 55 => (0, 9, 10, 1, 5, 6, 4, 5, 0, 7, 0)
  | 56 => (0, 8, 9, 0, 2, 6, 5, 6, 1, 10, 0)
  | 57 => (0, 8, 9, 2, 6, 0, 1, 5, 6, 12, 0)
  | 58 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 59 => (0, 8, 9, 2, 6, 0, 5, 6, 1, 12, 0)
  | 60 => (0, 9, 10, 1, 5, 6, 4, 5, 0, 7, 0)
  | 61 => (0, 8, 10, 2, 0, 6, 0, 4, 5, 12, 0)
  | 62 => (0, 1, 8, 7, 9, 13, 0, 2, 6, 3, 0)
  | 63 => (0, 8, 9, 0, 2, 6, 1, 5, 6, 10, 0)
  | 64 => (0, 8, 9, 0, 2, 6, 1, 5, 6, 10, 0)
  | 65 => (0, 8, 9, 2, 6, 0, 1, 5, 6, 12, 0)
  | 66 => (0, 8, 9, 0, 2, 6, 5, 6, 1, 10, 0)
  | _ => (0, 8, 9, 0, 2, 6, 1, 5, 6, 10, 0)

theorem r1_wit_ok0a : ∀ idx : Fin 68, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 12 → idx.val ≠ 23 → idx.val ≠ 26 → idx.val ≠ 40 → idx.val ≠ 44 → idx.val ≠ 51 →
    (r1_wit idx).1 = 0 →
    let I := hc_rep idx
    let (_, a1, a2, a3, a4, _, a6, a7, _, a9, _) := r1_wit idx
    a3 ∈ I ∧ a4 ∈ I ∧ a6 ∈ I ∧ a7 ∈ I ∧ a1 ≠ a2 ∧ a9 ≠ a1 ∧ hc_adjB a2 a9 = false ∧ (g14_nbB a1).card = 3 := by
  decide +kernel

theorem r1_wit_ok0b : ∀ idx : Fin 68, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 12 → idx.val ≠ 23 → idx.val ≠ 26 → idx.val ≠ 40 → idx.val ≠ 44 → idx.val ≠ 51 →
    (r1_wit idx).1 = 0 →
    let (_, a1, _, a3, a4, a5, _, _, _, _, _) := r1_wit idx
    a3 ≠ a4 ∧ hc_adjB a3 a1 = true ∧ hc_adjB a4 a1 = true ∧ hc_adjB a1 a5 = true ∧ a5 ≠ a3 ∧ a5 ≠ a4 := by
  decide +kernel

theorem r1_wit_ok0c : ∀ idx : Fin 68, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 12 → idx.val ≠ 23 → idx.val ≠ 26 → idx.val ≠ 40 → idx.val ≠ 44 → idx.val ≠ 51 →
    (r1_wit idx).1 = 0 →
    let (_, _, a2, a3, _, _, a6, a7, a8, a9, _) := r1_wit idx
    a6 ≠ a7 ∧ hc_adjB a6 a2 = true ∧ hc_adjB a7 a2 = true ∧ hc_adjB a2 a8 = true ∧ a8 ≠ a6 ∧ a8 ≠ a7 ∧
    hc_adjB a3 a2 = false ∧ hc_adjB a3 a9 = true := by
  decide +kernel

theorem r1_wit_ok1 : ∀ idx : Fin 68, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 12 → idx.val ≠ 23 → idx.val ≠ 26 → idx.val ≠ 40 → idx.val ≠ 44 → idx.val ≠ 51 →
    (r1_wit idx).1 = 1 →
    let I := hc_rep idx
    let (_, a1, a2, a3, a4, a5, a6, a7, a8, a9, _) := r1_wit idx
    (I.card = 3 ∧ a2 ∈ I ∧ a3 ∈ I ∧ (g14_nbB a1).card = 3 ∧ a2 ≠ a3 ∧ hc_adjB a2 a1 = true ∧ hc_adjB a3 a1 = true ∧ hc_adjB a1 a4 = true ∧ a4 ≠ a2 ∧ a4 ≠ a3) ∧
    (a8 ∈ I ∧ a9 ∈ I ∧ a5 ∉ I ∧ a6 ∉ I ∧ a7 ∉ I ∧ a5 ≠ a1 ∧ a6 ≠ a1) ∧
    (hc_adjB a8 a5 = true ∧ hc_adjB a9 a6 = true ∧ hc_adjB a5 a6 = true ∧
     hc_adjB a5 a7 = true ∧ a7 ≠ a6 ∧ (g14_nbB a6).card = 3 ∧ decide (a7.val < 7) = decide (a6.val < 7)) := by
  decide +kernel

theorem r1_wit_ok2 : ∀ idx : Fin 68, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 12 → idx.val ≠ 23 → idx.val ≠ 26 → idx.val ≠ 40 → idx.val ≠ 44 → idx.val ≠ 51 →
    (r1_wit idx).1 ≠ 0 → (r1_wit idx).1 ≠ 1 →
    let I := hc_rep idx
    let (_, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) := r1_wit idx
    (I.card = 3 ∧ a2 ∈ I ∧ a3 ∈ I ∧ (g14_nbB a1).card = 3 ∧ a2 ≠ a3 ∧ hc_adjB a2 a1 = true ∧ hc_adjB a3 a1 = true ∧ hc_adjB a1 a4 = true ∧ a4 ≠ a2 ∧ a4 ≠ a3) ∧
    (a9 ∈ I ∧ a10 ∈ I ∧ a5 ∉ I ∧ a5 ≠ a1 ∧ a6 ≠ a1 ∧ a7 ≠ a1) ∧
    (hc_adjB a5 a6 = true ∧ hc_adjB a5 a7 = true ∧ hc_adjB a5 a8 = true ∧
     hc_adjB a9 a6 = true ∧ hc_adjB a10 a7 = true ∧ a6 ≠ a7 ∧ a8 ≠ a6 ∧ a8 ≠ a7 ∧
     (g14_nbB a6).card = 3 ∧ (g14_nbB a7).card = 3 ∧ decide (a6.val < 7) = decide (a7.val < 7) ∧ decide (a8.val < 7) = decide (a6.val < 7)) := by
  decide +kernel

theorem hnot33_diff_I {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    (x y ix iy vx qx qy : Fin 14)
    (hix : ix ∈ ineligSet 14 D) (hiy : iy ∈ ineligSet 14 D) (hvx : vx ∉ ineligSet 14 D)
    (hg : x ≠ y ∧ ix ≠ iy ∧ (g14_nbB x).card = 3 ∧ (g14_nbB y).card = 3 ∧
          hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB ix y = false ∧
          hc_adjB x vx = true ∧ hc_adjB ix qx = true ∧ qx ≠ x ∧ hc_adjB y qx = false ∧
          hc_adjB iy qy = true ∧ qy ≠ y ∧ hc_adjB x qy = false)
    (hx3 : 3 ≤ (sem_W 14 D x).card) (hy3 : 3 ≤ (sem_W 14 D y).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxy, hixy, hdx, hdy, g1, g2, g3, g4, g5, hqxx, g6, g7, hqyy, g8⟩ := hg
  obtain ⟨hPx, hQx⟩ := hsat x hx3
  obtain ⟨hPy, hQy⟩ := hsat y hy3
  have hpx := as_mem hpos hix ((hc_adjB_iff _ _).1 g1)
  have hpy := as_mem hpos hiy ((hc_adjB_iff _ _).1 g2)
  by_cases hpxy : pos ix ∈ sem_W 14 D y
  · by_cases hpyx : pos iy ∈ sem_W 14 D x
    · obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 g4)
      have hpxpy : pos ix ≠ pos iy := fun e => hixy (hpos.2 _ hix _ hiy e)
      have hpxe : pos ix ≠ ev := fun e => hvx (hfv _ hix e.symm ▸ hix)
      have hpye : pos iy ≠ ev := fun e => hvx (hfv _ hiy e.symm ▸ hiy)
      have hWx := pa_three hpx hpyx hev hpxpy hpxe hpye (hc3 x)
      have hfull := full_g14 h hD hB0 hpos hix ((hc_adjB_iff _ _).1 g1) (fun p hp hne1 hsub => by
        rcases hWx p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hixy.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hiy)))
        · exact hvx (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1) ▸ hix))
      exact sem_adjB_false.1 g3 ((hfull y).1 (sem_mem_W.1 hpxy).2.1)
    · have hPne : P ≠ pos iy := fun e => hpyx (e ▸ hPx)
      have hQne : Q ≠ pos iy := fun e => hpyx (e ▸ hQx)
      obtain ⟨e, he, hnx, hnq⟩ := g14_deg3_cover_free h hD hdy hxy.symm hqyy.symm (sem_adjB_false.1 g8)
      rcases pa_three hPy hQy hpy hPQ hPne hQne (hc3 y) e he with rfl | rfl | rfl
      · exact hnx (sem_mem_W.1 hPx).2.1
      · exact hnx (sem_mem_W.1 hQx).2.1
      · exact hnq ((hpos.1 iy hiy).2.2.1 qy ((hc_adjB_iff _ _).1 g7))
  · have hPne : P ≠ pos ix := fun e => hpxy (e ▸ hPy)
    have hQne : Q ≠ pos ix := fun e => hpxy (e ▸ hQy)
    obtain ⟨e, he, hny, hnq⟩ := g14_deg3_cover_free h hD hdx hxy hqxx.symm (sem_adjB_false.1 g6)
    rcases pa_three hPx hQx hpx hPQ hPne hQne (hc3 x) e he with rfl | rfl | rfl
    · exact hny (sem_mem_W.1 hPy).2.1
    · exact hny (sem_mem_W.1 hQy).2.1
    · exact hnq ((hpos.1 ix hix).2.2.1 qx ((hc_adjB_iff _ _).1 g5))

theorem elim_12_R1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) (hI : ineligSet 14 D = {0, 1, 3}) : False := by
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  have hpos := hctx.1
  have hm : ∀ v : Fin 14, v ∈ ({0, 1, 3} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({0, 1, 3} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hI ▸ hv

  have hkill_pair : ∀ (u1 u2 c a1 b1 a2 b2 ia1 ib1 ia2 ib2 : Fin 14),
      ia1 ∈ ineligSet 14 D → ib1 ∈ ineligSet 14 D → ia2 ∈ ineligSet 14 D → ib2 ∈ ineligSet 14 D →
      u1 ∉ ineligSet 14 D → u2 ∉ ineligSet 14 D →
      (a1 ≠ b1 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ a2 ≠ b2 ∧
       a1 ≠ c ∧ b1 ≠ c ∧ a2 ≠ c ∧ b2 ≠ c ∧
       hc_adjB u1 a1 = true ∧ hc_adjB u1 b1 = true ∧ hc_adjB u1 c = true ∧
       hc_adjB u2 a2 = true ∧ hc_adjB u2 b2 = true ∧ hc_adjB u2 c = true ∧
       hc_adjB ia1 a1 = true ∧ hc_adjB ib1 b1 = true ∧ hc_adjB ia2 a2 = true ∧ hc_adjB ib2 b2 = true ∧
       (g14_nbB a1).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB a2).card = 3 ∧ (g14_nbB b2).card = 3 ∧
       decide (a1.val < 7) = decide (b1.val < 7) ∧ decide (a1.val < 7) = decide (a2.val < 7) ∧
       decide (a1.val < 7) = decide (b2.val < 7) ∧ decide (a1.val < 7) = decide (c.val < 7)) →
      (sem_W 14 D a1).card ≤ 2 → (sem_W 14 D b1).card ≤ 2 →
      (sem_W 14 D a2).card ≤ 2 → (sem_W 14 D b2).card ≤ 2 → False := by
    intro u1 u2 c a1 b1 a2 b2 ia1 ib1 ia2 ib2 hia1 hib1 hia2 hib2 hu1 hu2 hg la1 lb1 la2 lb2
    obtain ⟨hab1, ha12, ha1b2, hb1a2, hb12, hab2, ha1c, hb1c, ha2c, hb2c,
      gu1a, gu1b, gu1c, gu2a, gu2b, gu2c, gia1, gib1, gia2, gib2,
      hda1, hdb1, hda2, hdb2, hs1, hs2, hs3, hs4⟩ := hg
    have hu1_3 : 3 ≤ (sem_W 14 D u1).card := by
      by_contra hc
      exact ps_side_3star h hD hpos u1 a1 b1 c ia1 ib1 hia1 hib1 hu1
        ⟨gu1a, gu1b, gu1c, gia1, gib1, hab1, ha1c.symm, hb1c.symm, hda1, hdb1, hs1, hs4.symm⟩
        (by omega) la1 lb1
    have hu2_3 : 3 ≤ (sem_W 14 D u2).card := by
      by_contra hc
      exact ps_side_3star h hD hpos u2 a2 b2 c ia2 ib2 hia2 hib2 hu2
        ⟨gu2a, gu2b, gu2c, gia2, gib2, hab2, ha2c.symm, hb2c.symm, hda2, hdb2, hs2.symm.trans hs3,
          hs4.symm.trans hs2⟩ (by omega) la2 lb2
    obtain ⟨Da1, -, hWa1, hpa1⟩ := ps_side h hD hpos hia1 ((hc_adjB_iff _ _).1 gia1) hda1 la1
    obtain ⟨Db1, -, hWb1, hpb1⟩ := ps_side h hD hpos hib1 ((hc_adjB_iff _ _).1 gib1) hdb1 lb1
    obtain ⟨Da2, -, hWa2, hpa2⟩ := ps_side h hD hpos hia2 ((hc_adjB_iff _ _).1 gia2) hda2 la2
    obtain ⟨Db2, -, hWb2, hpb2⟩ := ps_side h hD hpos hib2 ((hc_adjB_iff _ _).1 gib2) hdb2 lb2
    obtain ⟨e1a, h1a_u, h1a_a, -, hf1a'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu1a)
    obtain ⟨e1b, h1b_u, h1b_b, -, hf1b'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu1b)
    obtain ⟨e1c, h1c_u, h1c_c, -, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu1c)
    obtain ⟨e2a, h2a_u, h2a_a, -, hf2a'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu2a)
    obtain ⟨e2b, h2b_u, h2b_b, -, hf2b'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu2b)
    obtain ⟨e2c, h2c_u, h2c_c, -, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu2c)
    rw [hWa1, Finset.mem_insert, Finset.mem_singleton] at h1a_a
    have hba1 : sem_bar e1a = Da1 := h1a_a.resolve_left (fun hh => hu1 (hf1a' ia1 hia1 hh ▸ hia1))
    rw [hWb1, Finset.mem_insert, Finset.mem_singleton] at h1b_b
    have hbb1 : sem_bar e1b = Db1 := h1b_b.resolve_left (fun hh => hu1 (hf1b' ib1 hib1 hh ▸ hib1))
    rw [hWa2, Finset.mem_insert, Finset.mem_singleton] at h2a_a
    have hba2 : sem_bar e2a = Da2 := h2a_a.resolve_left (fun hh => hu2 (hf2a' ia2 hia2 hh ▸ hia2))
    rw [hWb2, Finset.mem_insert, Finset.mem_singleton] at h2b_b
    have hbb2 : sem_bar e2b = Db2 := h2b_b.resolve_left (fun hh => hu2 (hf2b' ib2 hib2 hh ▸ hib2))
    have hDa1_in : Da1 ∈ sem_W 14 D a1 := by rw [hWa1]; simp
    have hDb1_in : Db1 ∈ sem_W 14 D b1 := by rw [hWb1]; simp
    have hDa2_in : Da2 ∈ sem_W 14 D a2 := by rw [hWa2]; simp
    have hDb2_in : Db2 ∈ sem_W 14 D b2 := by rw [hWb2]; simp
    have h1_ab : e1a ≠ e1b := fun hh => hpa1 b1 hab1.symm hs1.symm (by rw [← hba1, hh, hbb1]; exact hDb1_in)
    have h1_ac : e1a ≠ e1c := fun hh => hpa1 c ha1c.symm hs4.symm (by rw [← hba1, hh]; exact h1c_c)
    have h1_bc : e1b ≠ e1c := fun hh => hpb1 c hb1c.symm (hs4.symm.trans hs1) (by rw [← hbb1, hh]; exact h1c_c)
    have h2_ab : e2a ≠ e2b := fun hh => hpa2 b2 hab2.symm (hs3.symm.trans hs2) (by rw [← hba2, hh, hbb2]; exact hDb2_in)
    have h2_ac : e2a ≠ e2c := fun hh => hpa2 c ha2c.symm (hs4.symm.trans hs2) (by rw [← hba2, hh]; exact h2c_c)
    have h2_bc : e2b ≠ e2c := fun hh => hpb2 c hb2c.symm (hs4.symm.trans hs3) (by rw [← hbb2, hh]; exact h2c_c)
    obtain ⟨hPu1, hQu1⟩ := hctx.2.2.2 u1 hu1_3
    obtain ⟨hPu2, hQu2⟩ := hctx.2.2.2 u2 hu2_3
    have hkill_e : ∀ e, e ∈ sem_W 14 D u1 → e ∈ sem_W 14 D u2 → e = e1c := by
      intro e he1 he2
      rcases pa_three h1a_u h1b_u h1c_u h1_ab h1_ac h1_bc (hctx.2.1 u1) e he1 with heq | heq | heq
      · rw [heq] at he2
        rcases pa_three h2a_u h2b_u h2c_u h2_ab h2_ac h2_bc (hctx.2.1 u2) e1a he2 with hh | hh | hh
        · exact absurd (by rw [← hba1, hh, hba2]; exact hDa2_in) (hpa1 a2 ha12.symm hs2.symm)
        · exact absurd (by rw [← hba1, hh, hbb2]; exact hDb2_in) (hpa1 b2 ha1b2.symm hs3.symm)
        · exact absurd (by rw [← hba1, hh]; exact h2c_c) (hpa1 c ha1c.symm hs4.symm)
      · rw [heq] at he2
        rcases pa_three h2a_u h2b_u h2c_u h2_ab h2_ac h2_bc (hctx.2.1 u2) e1b he2 with hh | hh | hh
        · exact absurd (by rw [← hbb1, hh, hba2]; exact hDa2_in) (hpb1 a2 hb1a2.symm (hs2.symm.trans hs1))
        · exact absurd (by rw [← hbb1, hh, hbb2]; exact hDb2_in) (hpb1 b2 hb12.symm (hs3.symm.trans hs1))
        · exact absurd (by rw [← hbb1, hh]; exact h2c_c) (hpb1 c hb1c.symm (hs4.symm.trans hs1))
      · exact heq
    exact hctx.2.2.1 ((hkill_e P hPu1 hPu2).trans (hkill_e Q hQu1 hQu2).symm)
  have hdiff : ∀ (x y ix iy vx qx qy : Fin 14),
      ix ∈ ineligSet 14 D → iy ∈ ineligSet 14 D → vx ∉ ineligSet 14 D →
      (x ≠ y ∧ ix ≠ iy ∧ (g14_nbB x).card = 3 ∧ (g14_nbB y).card = 3 ∧
       hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB ix y = false ∧
       hc_adjB x vx = true ∧ hc_adjB ix qx = true ∧ qx ≠ x ∧ hc_adjB y qx = false ∧
       hc_adjB iy qy = true ∧ qy ≠ y ∧ hc_adjB x qy = false) →
      ¬ (3 ≤ (sem_W 14 D x).card ∧ 3 ≤ (sem_W 14 D y).card) := fun x y ix iy vx qx qy h1 h2 h3 hg ⟨hx, hy⟩ =>
    hnot33_diff_I h hD hB0 hctx x y ix iy vx qx qy h1 h2 h3 hg hx hy
  by_cases hA : 3 ≤ (sem_W 14 D 8).card ∨ 3 ≤ (sem_W 14 D 10).card
  · have l9 : (sem_W 14 D 9).card ≤ 2 := by
      rcases hA with h8 | h10
      · by_contra hc; exact hdiff 8 9 0 1 6 10 13 (hm 0 (by decide)) (hm 1 (by decide)) (hn 6 (by decide)) (by decide) ⟨h8, by omega⟩
      · by_contra hc; exact hdiff 10 9 0 1 5 8 13 (hm 0 (by decide)) (hm 1 (by decide)) (hn 5 (by decide)) (by decide) ⟨h10, by omega⟩
    have l13 : (sem_W 14 D 13).card ≤ 2 := by
      rcases hA with h8 | h10
      · by_contra hc; exact hdiff 8 13 0 1 6 10 9 (hm 0 (by decide)) (hm 1 (by decide)) (hn 6 (by decide)) (by decide) ⟨h8, by omega⟩
      · by_contra hc; exact hdiff 10 13 0 1 5 8 9 (hm 0 (by decide)) (hm 1 (by decide)) (hn 5 (by decide)) (by decide) ⟨h10, by omega⟩
    have l11 : (sem_W 14 D 11).card ≤ 2 := by
      rcases hA with h8 | h10
      · by_contra hc; exact hdiff 8 11 0 3 6 10 12 (hm 0 (by decide)) (hm 3 (by decide)) (hn 6 (by decide)) (by decide) ⟨h8, by omega⟩
      · by_contra hc; exact hdiff 10 11 0 3 5 8 12 (hm 0 (by decide)) (hm 3 (by decide)) (hn 5 (by decide)) (by decide) ⟨h10, by omega⟩
    have l12 : (sem_W 14 D 12).card ≤ 2 := by
      rcases hA with h8 | h10
      · by_contra hc; exact hdiff 8 12 0 3 6 10 11 (hm 0 (by decide)) (hm 3 (by decide)) (hn 6 (by decide)) (by decide) ⟨h8, by omega⟩
      · by_contra hc; exact hdiff 10 12 0 3 5 8 11 (hm 0 (by decide)) (hm 3 (by decide)) (hn 5 (by decide)) (by decide) ⟨h10, by omega⟩
    exact hkill_pair 2 6 8 12 13 9 11 3 1 1 3
      (hm 3 (by decide)) (hm 1 (by decide)) (hm 1 (by decide)) (hm 3 (by decide))
      (hn 2 (by decide)) (hn 6 (by decide)) (by decide) l12 l13 l9 l11
  · have l8 : (sem_W 14 D 8).card ≤ 2 := by omega
    have l10 : (sem_W 14 D 10).card ≤ 2 := by omega
    by_cases hB' : 3 ≤ (sem_W 14 D 9).card ∨ 3 ≤ (sem_W 14 D 13).card
    · have l11 : (sem_W 14 D 11).card ≤ 2 := by
        rcases hB' with h9 | h13
        · by_contra hc; exact hdiff 9 11 1 3 6 13 12 (hm 1 (by decide)) (hm 3 (by decide)) (hn 6 (by decide)) (by decide) ⟨h9, by omega⟩
        · by_contra hc; exact hdiff 13 11 1 3 4 9 12 (hm 1 (by decide)) (hm 3 (by decide)) (hn 4 (by decide)) (by decide) ⟨h13, by omega⟩
      have l12 : (sem_W 14 D 12).card ≤ 2 := by
        rcases hB' with h9 | h13
        · by_contra hc; exact hdiff 9 12 1 3 6 13 11 (hm 1 (by decide)) (hm 3 (by decide)) (hn 6 (by decide)) (by decide) ⟨h9, by omega⟩
        · by_contra hc; exact hdiff 13 12 1 3 4 9 11 (hm 1 (by decide)) (hm 3 (by decide)) (hn 4 (by decide)) (by decide) ⟨h13, by omega⟩
      exact hkill_pair 2 4 13 8 12 10 11 0 3 0 3
        (hm 0 (by decide)) (hm 3 (by decide)) (hm 0 (by decide)) (hm 3 (by decide))
        (hn 2 (by decide)) (hn 4 (by decide)) (by decide) l8 l12 l10 l11
    · have l9 : (sem_W 14 D 9).card ≤ 2 := by omega
      have l13 : (sem_W 14 D 13).card ≤ 2 := by omega
      exact hkill_pair 2 5 12 8 13 9 10 0 1 1 0
        (hm 0 (by decide)) (hm 1 (by decide)) (hm 1 (by decide)) (hm 0 (by decide))
        (hn 2 (by decide)) (hn 5 (by decide)) (by decide) l8 l13 l9 l10

theorem elim_23_26_core {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1)
    (u1 u2 iu a1 b1 a2 b2 ia1 ib1 ia2 ib2 q1a q2a q1b q2b va1 va2 : Fin 14)
    (hiu : iu ∈ ineligSet 14 D) (hia1 : ia1 ∈ ineligSet 14 D) (hib1 : ib1 ∈ ineligSet 14 D)
    (hia2 : ia2 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (hu1 : u1 ∉ ineligSet 14 D) (hu2 : u2 ∉ ineligSet 14 D)
    (ha1 : a1 ∉ ineligSet 14 D) (hb1 : b1 ∉ ineligSet 14 D)
    (ha2 : a2 ∉ ineligSet 14 D) (hb2 : b2 ∉ ineligSet 14 D)
    (hva1 : va1 ∉ ineligSet 14 D) (hva2 : va2 ∉ ineligSet 14 D)
    (hg : a1 ≠ b1 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ a2 ≠ b2 ∧
          ia1 ≠ ib1 ∧ ia2 ≠ ib2 ∧ iu ≠ ia1 ∧ iu ≠ ib1 ∧ iu ≠ ia2 ∧ iu ≠ ib2 ∧
          hc_adjB iu u1 = true ∧ hc_adjB iu u2 = true ∧
          hc_adjB u1 a1 = true ∧ hc_adjB u1 b1 = true ∧
          hc_adjB u2 a2 = true ∧ hc_adjB u2 b2 = true ∧
          hc_adjB ia1 a1 = true ∧ hc_adjB ib1 b1 = true ∧
          hc_adjB ia2 a2 = true ∧ hc_adjB ib2 b2 = true ∧
          hc_adjB iu a1 = false ∧ hc_adjB iu b1 = false ∧ hc_adjB iu a2 = false ∧ hc_adjB iu b2 = false ∧
          hc_adjB ia1 b1 = false ∧ hc_adjB ia2 b2 = false ∧
          hc_adjB a1 va1 = true ∧ hc_adjB ia1 q1a = true ∧ q1a ≠ a1 ∧ hc_adjB b1 q1a = false ∧
          hc_adjB ib1 q2a = true ∧ q2a ≠ b1 ∧ hc_adjB a1 q2a = false ∧
          hc_adjB a2 va2 = true ∧ hc_adjB ia2 q1b = true ∧ q1b ≠ a2 ∧ hc_adjB b2 q1b = false ∧
          hc_adjB ib2 q2b = true ∧ q2b ≠ b2 ∧ hc_adjB a2 q2b = false ∧
          (g14_nbB a1).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB a2).card = 3 ∧ (g14_nbB b2).card = 3 ∧
          decide (a1.val < 7) = decide (b1.val < 7) ∧ decide (a1.val < 7) = decide (a2.val < 7) ∧
          decide (a1.val < 7) = decide (b2.val < 7)) : False := by
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  have hpos := hctx.1
  obtain ⟨hab1, ha12, ha1b2, hb1a2, hb12, hab2, hiab1, hiab2, hiu1, hiub1, hiu2, hiub2,
    gu1i, gu2i, gu1a, gu1b, gu2a, gu2b, gia1, gib1, gia2, gib2,
    hnia1, hnib1, hnia2, hnib2, hniab1, hniab2,
    ga1v, gq1a, hq1a, gq1b, gq2b, hq2b, gq2a,
    ga2v, gq1a2, hq1a2, gq1b2, gq2b2, hq2b2, gq2a2,
    hda1, hdb1, hda2, hdb2, hs1, hs2, hs3⟩ := hg
  have hu1_3 : 3 ≤ (sem_W 14 D u1).card := by
    by_contra hc
    have ha1_3 : 3 ≤ (sem_W 14 D a1).card := by
      by_contra hc1
      exact pa_m1 h hD hpos u1 a1 b1 iu ia1 hiu hia1 hu1 ha1 hb1
        ⟨gu1i, gia1, gu1a, gu1b, hab1.symm, hda1, hs1.symm⟩ (by omega) (by omega)
    have hb1_3 : 3 ≤ (sem_W 14 D b1).card := by
      by_contra hc1
      exact pa_m1 h hD hpos u1 b1 a1 iu ib1 hiu hib1 hu1 hb1 ha1
        ⟨gu1i, gib1, gu1b, gu1a, hab1, hdb1, hs1⟩ (by omega) (by omega)
    exact hnot33_diff_I h hD hB0 hctx a1 b1 ia1 ib1 va1 q1a q2a hia1 hib1 hva1
      ⟨hab1, hiab1, hda1, hdb1, gia1, gib1, hniab1, ga1v, gq1a, hq1a, gq1b, gq2b, hq2b, gq2a⟩ ha1_3 hb1_3
  have hu2_3 : 3 ≤ (sem_W 14 D u2).card := by
    by_contra hc
    have ha2_3 : 3 ≤ (sem_W 14 D a2).card := by
      by_contra hc1
      exact pa_m1 h hD hpos u2 a2 b2 iu ia2 hiu hia2 hu2 ha2 hb2
        ⟨gu2i, gia2, gu2a, gu2b, hab2.symm, hda2, hs3.symm.trans hs2⟩ (by omega) (by omega)
    have hb2_3 : 3 ≤ (sem_W 14 D b2).card := by
      by_contra hc1
      exact pa_m1 h hD hpos u2 b2 a2 iu ib2 hiu hib2 hu2 hb2 ha2
        ⟨gu2i, gib2, gu2b, gu2a, hab2, hdb2, hs2.symm.trans hs3⟩ (by omega) (by omega)
    exact hnot33_diff_I h hD hB0 hctx a2 b2 ia2 ib2 va2 q1b q2b hia2 hib2 hva2
      ⟨hab2, hiab2, hda2, hdb2, gia2, gib2, hniab2, ga2v, gq1a2, hq1a2, gq1b2, gq2b2, hq2b2, gq2a2⟩ ha2_3 hb2_3
  have la1 : (sem_W 14 D a1).card ≤ 2 := by
    by_contra hc
    exact hnot33_pair h hD hB0 hctx u1 a1 iu ia1 hiu hia1 hu1 ha1 ⟨hiu1, gu1i, gia1, gu1a, hnia1⟩ hu1_3 (by omega)
  have lb1 : (sem_W 14 D b1).card ≤ 2 := by
    by_contra hc
    exact hnot33_pair h hD hB0 hctx u1 b1 iu ib1 hiu hib1 hu1 hb1 ⟨hiub1, gu1i, gib1, gu1b, hnib1⟩ hu1_3 (by omega)
  have la2 : (sem_W 14 D a2).card ≤ 2 := by
    by_contra hc
    exact hnot33_pair h hD hB0 hctx u2 a2 iu ia2 hiu hia2 hu2 ha2 ⟨hiu2, gu2i, gia2, gu2a, hnia2⟩ hu2_3 (by omega)
  have lb2 : (sem_W 14 D b2).card ≤ 2 := by
    by_contra hc
    exact hnot33_pair h hD hB0 hctx u2 b2 iu ib2 hiu hib2 hu2 hb2 ⟨hiub2, gu2i, gib2, gu2b, hnib2⟩ hu2_3 (by omega)
  obtain ⟨Da1, -, hWa1, hpa1⟩ := ps_side h hD hpos hia1 ((hc_adjB_iff _ _).1 gia1) hda1 la1
  obtain ⟨Db1, -, hWb1, hpb1⟩ := ps_side h hD hpos hib1 ((hc_adjB_iff _ _).1 gib1) hdb1 lb1
  obtain ⟨Da2, -, hWa2, hpa2⟩ := ps_side h hD hpos hia2 ((hc_adjB_iff _ _).1 gia2) hda2 la2
  obtain ⟨Db2, -, hWb2, hpb2⟩ := ps_side h hD hpos hib2 ((hc_adjB_iff _ _).1 gib2) hdb2 lb2
  obtain ⟨e1a, h1a_u, h1a_a, hfa1, hf1a'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu1a)
  obtain ⟨e1b, h1b_u, h1b_b, hfb1, hf1b'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu1b)
  obtain ⟨e2a, h2a_u, h2a_a, hfa2, hf2a'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu2a)
  obtain ⟨e2b, h2b_u, h2b_b, hfb2, hf2b'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gu2b)
  rw [hWa1, Finset.mem_insert, Finset.mem_singleton] at h1a_a
  have hba1 : sem_bar e1a = Da1 := h1a_a.resolve_left (fun hh => hu1 (hf1a' ia1 hia1 hh ▸ hia1))
  rw [hWb1, Finset.mem_insert, Finset.mem_singleton] at h1b_b
  have hbb1 : sem_bar e1b = Db1 := h1b_b.resolve_left (fun hh => hu1 (hf1b' ib1 hib1 hh ▸ hib1))
  rw [hWa2, Finset.mem_insert, Finset.mem_singleton] at h2a_a
  have hba2 : sem_bar e2a = Da2 := h2a_a.resolve_left (fun hh => hu2 (hf2a' ia2 hia2 hh ▸ hia2))
  rw [hWb2, Finset.mem_insert, Finset.mem_singleton] at h2b_b
  have hbb2 : sem_bar e2b = Db2 := h2b_b.resolve_left (fun hh => hu2 (hf2b' ib2 hib2 hh ▸ hib2))
  have hDa1_in : Da1 ∈ sem_W 14 D a1 := by rw [hWa1]; simp
  have hDb1_in : Db1 ∈ sem_W 14 D b1 := by rw [hWb1]; simp
  have hDa2_in : Da2 ∈ sem_W 14 D a2 := by rw [hWa2]; simp
  have hDb2_in : Db2 ∈ sem_W 14 D b2 := by rw [hWb2]; simp
  have hp1 := as_mem hpos hiu ((hc_adjB_iff _ _).1 gu1i)
  have hp2 := as_mem hpos hiu ((hc_adjB_iff _ _).1 gu2i)
  have h1_ab : e1a ≠ e1b := fun hh => hpa1 b1 hab1.symm hs1.symm (by rw [← hba1, hh, hbb1]; exact hDb1_in)
  have h1_ap : e1a ≠ pos iu := fun hh => ha1 (hfa1 iu hiu hh ▸ hiu)
  have h1_bp : e1b ≠ pos iu := fun hh => hb1 (hfb1 iu hiu hh ▸ hiu)
  have h2_ab : e2a ≠ e2b := fun hh => hpa2 b2 hab2.symm (hs3.symm.trans hs2) (by rw [← hba2, hh, hbb2]; exact hDb2_in)
  have h2_ap : e2a ≠ pos iu := fun hh => ha2 (hfa2 iu hiu hh ▸ hiu)
  have h2_bp : e2b ≠ pos iu := fun hh => hb2 (hfb2 iu hiu hh ▸ hiu)
  obtain ⟨hPu1, hQu1⟩ := hctx.2.2.2 u1 hu1_3
  obtain ⟨hPu2, hQu2⟩ := hctx.2.2.2 u2 hu2_3
  have hkill_e : ∀ e, e ∈ sem_W 14 D u1 → e ∈ sem_W 14 D u2 → e = pos iu := by
    intro e he1 he2
    rcases pa_three h1a_u h1b_u hp1 h1_ab h1_ap h1_bp (hctx.2.1 u1) e he1 with heq | heq | heq
    · rw [heq] at he2
      rcases pa_three h2a_u h2b_u hp2 h2_ab h2_ap h2_bp (hctx.2.1 u2) e1a he2 with hh | hh | hh
      · exact absurd (by rw [← hba1, hh, hba2]; exact hDa2_in) (hpa1 a2 ha12.symm hs2.symm)
      · exact absurd (by rw [← hba1, hh, hbb2]; exact hDb2_in) (hpa1 b2 ha1b2.symm hs3.symm)
      · exact absurd hh h1_ap
    · rw [heq] at he2
      rcases pa_three h2a_u h2b_u hp2 h2_ab h2_ap h2_bp (hctx.2.1 u2) e1b he2 with hh | hh | hh
      · exact absurd (by rw [← hbb1, hh, hba2]; exact hDa2_in) (hpb1 a2 hb1a2.symm (hs2.symm.trans hs1))
      · exact absurd (by rw [← hbb1, hh, hbb2]; exact hDb2_in) (hpb1 b2 hb12.symm (hs3.symm.trans hs1))
      · exact absurd hh h1_bp
    · exact heq
  exact hctx.2.2.1 ((hkill_e P hPu1 hPu2).trans (hkill_e Q hQu1 hQu2).symm)

theorem elim_23_R1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) (hI : ineligSet 14 D = {1, 3, 8}) : False := by
  have hm : ∀ v : Fin 14, v ∈ ({1, 3, 8} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({1, 3, 8} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hI ▸ hv
  exact elim_23_26_core h hD hB0 hB 2 6 8 12 13 11 9 3 1 3 1 7 7 7 7 5 4
    (hm 8 (by decide)) (hm 3 (by decide)) (hm 1 (by decide)) (hm 3 (by decide)) (hm 1 (by decide))
    (hn 2 (by decide)) (hn 6 (by decide)) (hn 12 (by decide)) (hn 13 (by decide))
    (hn 11 (by decide)) (hn 9 (by decide)) (hn 5 (by decide)) (hn 4 (by decide)) (by decide)

theorem elim_26_R1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) (hI : ineligSet 14 D = {4, 7, 8}) : False := by
  have hm : ∀ v : Fin 14, v ∈ ({4, 7, 8} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({4, 7, 8} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hI ▸ hv
  exact elim_23_26_core h hD hB0 hB 13 11 4 1 2 3 6 7 8 7 8 3 0 1 0 9 12
    (hm 4 (by decide)) (hm 7 (by decide)) (hm 8 (by decide)) (hm 7 (by decide)) (hm 8 (by decide))
    (hn 13 (by decide)) (hn 11 (by decide)) (hn 1 (by decide)) (hn 2 (by decide))
    (hn 3 (by decide)) (hn 6 (by decide)) (hn 9 (by decide)) (hn 12 (by decide)) (by decide)

theorem elim_40_44_R1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1)
    (h4 : (4 : Fin 14) ∈ ineligSet 14 D) (h5 : (5 : Fin 14) ∈ ineligSet 14 D) (h7 : (7 : Fin 14) ∈ ineligSet 14 D)
    (hn1 : (1 : Fin 14) ∉ ineligSet 14 D) (hn6 : (6 : Fin 14) ∉ ineligSet 14 D)
    (hn9 : (9 : Fin 14) ∉ ineligSet 14 D) (hn13 : (13 : Fin 14) ∉ ineligSet 14 D) : False := by
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  have h10_3 := two_in_deg3 h hD hpos h4 h5 (by decide : (4 : Fin 14) ≠ 5 ∧ hc_adjB 4 10 = true ∧
    hc_adjB 5 10 = true ∧ hc_adjB 10 0 = true ∧ (0 : Fin 14) ≠ 4 ∧ (0 : Fin 14) ≠ 5)
  obtain ⟨hP10, hQ10⟩ := hsat 10 h10_3
  have hp4 := as_mem hpos h4 (by decide : Adj 4 10)
  have hp5 := as_mem hpos h5 (by decide : Adj 5 10)
  have hp45 : pos 4 ≠ pos 5 := fun e => absurd (hpos.2 _ h4 _ h5 e) (by decide)
  by_cases h1_3 : 3 ≤ (sem_W 14 D 1).card
  · obtain ⟨hP1, hQ1⟩ := hsat 1 h1_3
    have h4in : pos 4 = P ∨ pos 4 = Q := by
      by_contra h4n; rw [not_or] at h4n
      obtain ⟨e, he, hn1e, hn11e⟩ := g14_deg3_cover_free h hD (by decide : (g14_nbB 10).card = 3)
        (by decide : (10 : Fin 14) ≠ 1) (by decide : (10 : Fin 14) ≠ 11) (by decide : ¬ Adj 1 11)
      rcases pa_three hP10 hQ10 hp4 hPQ (Ne.symm h4n.1) (Ne.symm h4n.2) (hc3 10) e he with rfl | rfl | rfl
      · exact hn1e (sem_mem_W.1 hP1).2.1
      · exact hn1e (sem_mem_W.1 hQ1).2.1
      · exact hn11e ((hpos.1 4 h4).2.2.1 11 (by decide))
    have h5in : pos 5 = P ∨ pos 5 = Q := by
      by_contra h5n; rw [not_or] at h5n
      obtain ⟨e, he, hn1e, hn12e⟩ := g14_deg3_cover_free h hD (by decide : (g14_nbB 10).card = 3)
        (by decide : (10 : Fin 14) ≠ 1) (by decide : (10 : Fin 14) ≠ 12) (by decide : ¬ Adj 1 12)
      rcases pa_three hP10 hQ10 hp5 hPQ (Ne.symm h5n.1) (Ne.symm h5n.2) (hc3 10) e he with rfl | rfl | rfl
      · exact hn1e (sem_mem_W.1 hP1).2.1
      · exact hn1e (sem_mem_W.1 hQ1).2.1
      · exact hn12e ((hpos.1 5 h5).2.2.1 12 (by decide))
    have hp4_1 : pos 4 ∈ sem_W 14 D 1 := by rcases h4in with rfl | rfl <;> assumption
    have hp5_1 : pos 5 ∈ sem_W 14 D 1 := by rcases h5in with rfl | rfl <;> assumption
    have hp7_1 := as_mem hpos h7 (by decide : Adj 7 1)
    obtain ⟨e19, he19, -, hf9, -⟩ := pa_ed h hD hpos (by decide : Adj 1 9)
    rcases pa_three hp4_1 hp5_1 hp7_1 hp45 (fun e => absurd (hpos.2 _ h4 _ h7 e) (by decide))
        (fun e => absurd (hpos.2 _ h5 _ h7 e) (by decide)) (hc3 1) e19 he19 with heq | heq | heq
    · exact hn9 (hf9 4 h4 heq ▸ h4)
    · exact hn9 (hf9 5 h5 heq ▸ h5)
    · exact hn9 (hf9 7 h7 heq ▸ h7)
  · have l1 : (sem_W 14 D 1).card ≤ 2 := by omega
    have h9_3 : 3 ≤ (sem_W 14 D 9).card := by
      by_contra hc
      exact pa_m1 h hD hpos 1 9 13 7 5 h7 h5 hn1 hn9 hn13 (by decide) l1 (by omega)
    have h13_3 : 3 ≤ (sem_W 14 D 13).card := by
      by_contra hc
      exact pa_m1 h hD hpos 1 13 9 7 4 h7 h4 hn1 hn13 hn9 (by decide) l1 (by omega)
    obtain ⟨hP9, hQ9⟩ := hsat 9 h9_3
    obtain ⟨hP13, hQ13⟩ := hsat 13 h13_3
    have h4in : pos 4 = P ∨ pos 4 = Q := by
      by_contra h4n; rw [not_or] at h4n
      obtain ⟨e, he, hn9e, hn13e⟩ := g14_deg3_cover_free h hD (by decide : (g14_nbB 10).card = 3)
        (by decide : (10 : Fin 14) ≠ 9) (by decide : (10 : Fin 14) ≠ 13) (by decide : ¬ Adj 9 13)
      rcases pa_three hP10 hQ10 hp4 hPQ (Ne.symm h4n.1) (Ne.symm h4n.2) (hc3 10) e he with rfl | rfl | rfl
      · exact hn9e (sem_mem_W.1 hP9).2.1
      · exact hn9e (sem_mem_W.1 hQ9).2.1
      · exact hn13e ((hpos.1 4 h4).2.2.1 13 (by decide))
    have h5in : pos 5 = P ∨ pos 5 = Q := by
      by_contra h5n; rw [not_or] at h5n
      obtain ⟨e, he, hn13e, hn9e⟩ := g14_deg3_cover_free h hD (by decide : (g14_nbB 10).card = 3)
        (by decide : (10 : Fin 14) ≠ 13) (by decide : (10 : Fin 14) ≠ 9) (by decide : ¬ Adj 13 9)
      rcases pa_three hP10 hQ10 hp5 hPQ (Ne.symm h5n.1) (Ne.symm h5n.2) (hc3 10) e he with rfl | rfl | rfl
      · exact hn13e (sem_mem_W.1 hP13).2.1
      · exact hn13e (sem_mem_W.1 hQ13).2.1
      · exact hn9e ((hpos.1 5 h5).2.2.1 9 (by decide))
    have hp4_9 : pos 4 ∈ sem_W 14 D 9 := by rcases h4in with rfl | rfl <;> assumption
    have hp5_9 : pos 5 ∈ sem_W 14 D 9 := by rcases h5in with rfl | rfl <;> assumption
    obtain ⟨e96, h96_9, h96_6, hf6, -⟩ := pa_ed h hD hpos (by decide : Adj 9 6)
    obtain ⟨e91, h91_9, h91_1, hf1, hf9'⟩ := pa_ed h hD hpos (by decide : Adj 9 1)
    have h91_eq : e91 = e96 := by
      rcases pa_three hp4_9 hp5_9 h96_9 hp45 (fun e => hn6 (hf6 4 h4 e.symm ▸ h4))
          (fun e => hn6 (hf6 5 h5 e.symm ▸ h5)) (hc3 9) e91 h91_9 with he | he | he
      · exact absurd he (fun hh => hn1 (hf1 4 h4 hh ▸ h4))
      · exact absurd he (fun hh => hn1 (hf1 5 h5 hh ▸ h5))
      · exact he
    obtain ⟨Z1, -, hW1, hp1⟩ := ps_side h hD hpos h7 (by decide : Adj 7 1) (by decide) l1
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at h91_1
    have hZ1 : sem_bar e91 = Z1 := h91_1.resolve_left (fun hh => hn9 (hf9' 7 h7 hh ▸ h7))
    exact hp1 6 (by decide) (by decide) (by rw [← hZ1, h91_eq]; exact h96_6)

theorem elim_51_R1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) (hI : ineligSet 14 D = {1, 3, 8, 10}) : False := by
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  have hm : ∀ v : Fin 14, v ∈ ({1, 3, 8, 10} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hI ▸ hv

  have hno_adj33 : ∀ (x y ix iy z w v iz iw : Fin 14),
      ix ∈ ineligSet 14 D → iy ∈ ineligSet 14 D → iz ∈ ineligSet 14 D → iw ∈ ineligSet 14 D →
      x ∉ ineligSet 14 D → y ∉ ineligSet 14 D → z ∉ ineligSet 14 D → w ∉ ineligSet 14 D → v ∉ ineligSet 14 D →
      (ix ≠ iy ∧ iz ≠ ix ∧ iz ≠ iy ∧ iw ≠ ix ∧ iw ≠ iy ∧
       hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB x y = true ∧
       hc_adjB iz z = true ∧ hc_adjB iw w = true ∧ hc_adjB z w = true ∧
       hc_adjB z v = true ∧ v ≠ w ∧ (g14_nbB w).card = 3 ∧
       decide (v.val < 7) = decide (w.val < 7)) →
      3 ≤ (sem_W 14 D x).card → 3 ≤ (sem_W 14 D y).card → False := by
    intro x y ix iy z w v iz iw hix hiy hiz hiw hnx hny hnz hnw hnv hg hx3 hy3
    obtain ⟨hxyi, hzx, hzy, hwx, hwy, gx, gy, gxy, gz, gw, gzw, gzv, hvw, hdw, hsvw⟩ := hg
    obtain ⟨hPx, hQx⟩ := hsat x hx3
    obtain ⟨hPy, hQy⟩ := hsat y hy3
    obtain ⟨e, hex, hey, hfy, hfx⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gxy)
    have heP : e ≠ P := fun hh => w_bar h.1 (hh ▸ hPy) hey
    have heQ : e ≠ Q := fun hh => w_bar h.1 (hh ▸ hQy) hey
    have hbeP : sem_bar e ≠ P := fun hh => w_bar h.1 hPx (by rw [← hh, sem_bar_bar]; exact hex)
    have hbeQ : sem_bar e ≠ Q := fun hh => w_bar h.1 hQx (by rw [← hh, sem_bar_bar]; exact hex)
    have hpx := as_mem hpos hix ((hc_adjB_iff _ _).1 gx)
    have hpy := as_mem hpos hiy ((hc_adjB_iff _ _).1 gy)
    have hpx_PQ : pos ix = P ∨ pos ix = Q := by
      rcases pa_three hPx hQx hex hPQ heP.symm heQ.symm (hc3 x) (pos ix) hpx with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact absurd hh (fun e1 => hny (hfy ix hix e1.symm ▸ hix))
    have hpy_PQ : pos iy = P ∨ pos iy = Q := by
      rcases pa_three hPy hQy hey hPQ hbeP.symm hbeQ.symm (hc3 y) (pos iy) hpy with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact absurd hh (fun e1 => hnx (hfx iy hiy e1.symm ▸ hiy))
    have hpxpy : pos ix ≠ pos iy := fun hh => hxyi (hpos.2 _ hix _ hiy hh)
    have hle2_of_other : ∀ (a b ia : Fin 14), ia ∈ ineligSet 14 D → b ∉ ineligSet 14 D →
        ia ≠ ix → ia ≠ iy → hc_adjB ia a = true → hc_adjB a b = true → (sem_W 14 D a).card ≤ 2 := by
      intro a b ia hia hnb hax hay ga gab
      by_contra h3
      obtain ⟨hPa, hQa⟩ := hsat a (by omega)
      have hpxa : pos ix ∈ sem_W 14 D a := by rcases hpx_PQ with rfl | rfl <;> assumption
      have hpya : pos iy ∈ sem_W 14 D a := by rcases hpy_PQ with rfl | rfl <;> assumption
      have hpia := as_mem hpos hia ((hc_adjB_iff _ _).1 ga)
      obtain ⟨eab, heab, -, hfb, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gab)
      rcases pa_three hpxa hpya hpia hpxpy (fun e1 => hax.symm (hpos.2 _ hix _ hia e1))
          (fun e1 => hay.symm (hpos.2 _ hiy _ hia e1)) (hc3 a) eab heab with hh | hh | hh
      · exact hnb (hfb ix hix hh ▸ hix)
      · exact hnb (hfb iy hiy hh ▸ hiy)
      · exact hnb (hfb ia hia hh ▸ hia)
    have lz := hle2_of_other z w iz hiz hnw hzx hzy gz gzw
    have lw := hle2_of_other w z iw hiw hnz hwx hwy gw ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gzw)))
    exact pa_m1 h hD hpos z w v iz iw hiz hiw hnz hnw hnv ⟨gz, gw, gzw, gzv, hvw, hdw, hsvw⟩ lz lw
  by_cases h11 : 3 ≤ (sem_W 14 D 11).card
  · have l4 : (sem_W 14 D 4).card ≤ 2 := by
      by_contra hc; exact hno_adj33 4 11 10 3 2 13 12 8 1
        (hm 10 (by decide)) (hm 3 (by decide)) (hm 8 (by decide)) (hm 1 (by decide))
        (hn 4 (by decide)) (hn 11 (by decide)) (hn 2 (by decide)) (hn 13 (by decide)) (hn 12 (by decide))
        (by decide) (by omega) h11
    have l6 : (sem_W 14 D 6).card ≤ 2 := by
      by_contra hc; exact hno_adj33 6 11 8 3 5 9 12 10 1
        (hm 8 (by decide)) (hm 3 (by decide)) (hm 10 (by decide)) (hm 1 (by decide))
        (hn 6 (by decide)) (hn 11 (by decide)) (hn 5 (by decide)) (hn 9 (by decide)) (hn 12 (by decide))
        (by decide) (by omega) h11
    have h13 : 3 ≤ (sem_W 14 D 13).card := by
      by_contra hc; exact pa_m1 h hD hpos 4 13 11 10 1
        (hm 10 (by decide)) (hm 1 (by decide)) (hn 4 (by decide)) (hn 13 (by decide)) (hn 11 (by decide))
        (by decide) l4 (by omega)
    have l2 : (sem_W 14 D 2).card ≤ 2 := by
      by_contra hc; exact hno_adj33 2 13 8 1 4 11 13 10 3
        (hm 8 (by decide)) (hm 1 (by decide)) (hm 10 (by decide)) (hm 3 (by decide))
        (hn 2 (by decide)) (hn 13 (by decide)) (hn 4 (by decide)) (hn 11 (by decide)) (hn 13 (by decide))
        (by decide) (by omega) h13
    exact elim_alt_pair h hD ⟨hpos, hc3, hPQ, hsat⟩ 13 11 2 4 6 1 3 8 10 8
      (hm 1 (by decide)) (hm 3 (by decide)) (hm 8 (by decide)) (hm 10 (by decide)) (hm 8 (by decide))
      (hn 13 (by decide)) (hn 11 (by decide)) (hn 2 (by decide)) (hn 4 (by decide)) (hn 6 (by decide))
      (by decide) h13 h11 l2 l4 l6
  · have l11 : (sem_W 14 D 11).card ≤ 2 := by omega
    have h4 : 3 ≤ (sem_W 14 D 4).card := by
      by_contra hc; exact pa_m1 h hD hpos 11 4 6 3 10
        (hm 3 (by decide)) (hm 10 (by decide)) (hn 11 (by decide)) (hn 4 (by decide)) (hn 6 (by decide))
        (by decide) l11 (by omega)
    have h6 : 3 ≤ (sem_W 14 D 6).card := by
      by_contra hc; exact pa_m1 h hD hpos 11 6 4 3 8
        (hm 3 (by decide)) (hm 8 (by decide)) (hn 11 (by decide)) (hn 6 (by decide)) (hn 4 (by decide))
        (by decide) l11 (by omega)
    have l13 : (sem_W 14 D 13).card ≤ 2 := by
      by_contra hc; exact hno_adj33 4 13 10 1 6 11 9 8 3
        (hm 10 (by decide)) (hm 1 (by decide)) (hm 8 (by decide)) (hm 3 (by decide))
        (hn 4 (by decide)) (hn 13 (by decide)) (hn 6 (by decide)) (hn 11 (by decide)) (hn 9 (by decide))
        (by decide) h4 (by omega)
    have l9 : (sem_W 14 D 9).card ≤ 2 := by
      by_contra hc; exact hno_adj33 6 9 8 1 4 11 13 10 3
        (hm 8 (by decide)) (hm 1 (by decide)) (hm 10 (by decide)) (hm 3 (by decide))
        (hn 6 (by decide)) (hn 9 (by decide)) (hn 4 (by decide)) (hn 11 (by decide)) (hn 13 (by decide))
        (by decide) h6 (by omega)
    exact elim_alt_pair h hD ⟨hpos, hc3, hPQ, hsat⟩ 4 6 13 11 9 10 8 1 3 1
      (hm 10 (by decide)) (hm 8 (by decide)) (hm 1 (by decide)) (hm 3 (by decide)) (hm 1 (by decide))
      (hn 4 (by decide)) (hn 6 (by decide)) (hn 13 (by decide)) (hn 11 (by decide)) (hn 9 (by decide))
      (by decide) h4 h6 l13 l11 l9

theorem elim_R1_all {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12)
    (hB : Bplus 14 D = (eligSet 14 D).card + 1) (idx : Fin 68) (hc : 3 ≤ (hc_rep idx).card)
    (hI : ineligSet 14 D = hc_rep idx) : False := by
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  by_cases h12i : idx.val = 12
  · have hIeq : ineligSet 14 D = {0, 1, 3} := by rw [hI, show idx = ⟨12, by decide⟩ from Fin.ext h12i]; decide
    have hc3 : (ineligSet 14 D).card = 3 := by rw [hIeq]; decide
    exact elim_12_R1 h hD (by omega) hB hIeq
  by_cases h23 : idx.val = 23
  · have hIeq : ineligSet 14 D = {1, 3, 8} := by rw [hI, show idx = ⟨23, by decide⟩ from Fin.ext h23]; decide
    have hc3 : (ineligSet 14 D).card = 3 := by rw [hIeq]; decide
    exact elim_23_R1 h hD (by omega) hB hIeq
  by_cases h26 : idx.val = 26
  · have hIeq : ineligSet 14 D = {4, 7, 8} := by rw [hI, show idx = ⟨26, by decide⟩ from Fin.ext h26]; decide
    have hc3 : (ineligSet 14 D).card = 3 := by rw [hIeq]; decide
    exact elim_26_R1 h hD (by omega) hB hIeq
  by_cases h40 : idx.val = 40
  · have hIeq : ineligSet 14 D = {0, 4, 5, 7} := by rw [hI, show idx = ⟨40, by decide⟩ from Fin.ext h40]; decide
    exact elim_40_44_R1 h hD hB (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
  by_cases h44 : idx.val = 44
  · have hIeq : ineligSet 14 D = {4, 5, 7, 8} := by rw [hI, show idx = ⟨44, by decide⟩ from Fin.ext h44]; decide
    exact elim_40_44_R1 h hD hB (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
  by_cases h51 : idx.val = 51
  · have hIeq : ineligSet 14 D = {1, 3, 8, 10} := by rw [hI, show idx = ⟨51, by decide⟩ from Fin.ext h51]; decide
    exact elim_51_R1 h hD hB hIeq
  rcases hrw : r1_wit idx with ⟨k, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  by_cases hk0 : k = 0
  · have hwa := r1_wit_ok0a idx hc h12i h23 h26 h40 h44 h51 (by rw [hrw]; exact hk0)
    have hwb := r1_wit_ok0b idx hc h12i h23 h26 h40 h44 h51 (by rw [hrw]; exact hk0)
    have hwc := r1_wit_ok0c idx hc h12i h23 h26 h40 h44 h51 (by rw [hrw]; exact hk0)
    rw [hrw] at hwa hwb hwc; dsimp only at hwa hwb hwc
    obtain ⟨hi1, hi2, hj1, hj2, hxy, hqx, hnyq, hdx⟩ := hwa
    obtain ⟨h12', hx1, hx2, hxv, hv1, hv2⟩ := hwb
    obtain ⟨hj12, hy1, hy2, hyv, hvy1, hvy2, hni1y, hq1⟩ := hwc
    obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
    exact two_w3_R1_kill h hD hctx (hI ▸ hi1) (hI ▸ hi2) (hI ▸ hj1) (hI ▸ hj2)
      ⟨hxy, hqx, hnyq, hdx, h12', hx1, hx2, hxv, hv1, hv2, hj12, hy1, hy2, hyv, hvy1, hvy2, hni1y, hq1⟩
  · by_cases hk1 : k = 1
    · have hw := r1_wit_ok1 idx hc h12i h23 h26 h40 h44 h51 (by rw [hrw]; exact hk1)
      rw [hrw] at hw; dsimp only at hw
      obtain ⟨⟨hc3, hi1, hi2, hda, h12', ha1, ha2, hav, hv1, hv2⟩, ⟨hiz, hik, hnz, hnk, hnv, hza, hka⟩, hg⟩ := hw
      have hB0 : Bzero 14 D = 0 := by rw [hI, hc3] at hel; omega
      obtain ⟨b, hb⟩ := sem_exists_minBranch sem_g14_gr h.1 (sem_g14_comp hD)
      have hbp := sem_minBranch_pure hb
      obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
      have hR1 : (residualUnits 14 D b).card = 1 := by have := card_residual h.1 b hbp; omega
      obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
      have ha3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) ⟨h12', ha1, ha2, hav, hv1, hv2⟩
      have hrua : ru D b a1 = {u0} := by
        have hcc := cc_le h hD b hbp a1
        have hsub1 : ru D b a1 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
        exact Finset.eq_of_subset_of_card_le hsub1 (by rw [Finset.card_singleton]; omega)
      have hpure := w3_ru_one_pure h hD hB0 b hb hpos (hI ▸ hi1) (hI ▸ hi2)
        ⟨hda, h12', ha1, ha2, hav, hv1, hv2⟩ hrua
      have hle2 : ∀ x : Fin 14, x ≠ a1 → (sem_W 14 D x).card ≤ 2 := fun x hx => by
        have hrux : ru D b x = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
          have hu_eq : u = u0 := Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)
          exact hx (hpure x (hu_eq ▸ (mem_ru.1 hu).2))
        have := cc_le h hD b hbp x; rw [hrux, Finset.card_empty] at this; omega
      exact pa_m1 h hD hpos a5 a6 a7 a8 a9 (hI ▸ hiz) (hI ▸ hik) (hI ▸ hnz) (hI ▸ hnk) (hI ▸ hnv) hg
        (hle2 a5 hza) (hle2 a6 hka)
    · have hw := r1_wit_ok2 idx hc h12i h23 h26 h40 h44 h51 (by rw [hrw]; exact hk0) (by rw [hrw]; exact hk1)
      rw [hrw] at hw; dsimp only at hw
      obtain ⟨⟨hc3, hi1, hi2, hda, h12', ha1, ha2, hav, hv1, hv2⟩, ⟨hik1, hik2, hnu, hua, hk1a, hk2a⟩, hg⟩ := hw
      have hB0 : Bzero 14 D = 0 := by rw [hI, hc3] at hel; omega
      obtain ⟨b, hb⟩ := sem_exists_minBranch sem_g14_gr h.1 (sem_g14_comp hD)
      have hbp := sem_minBranch_pure hb
      obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
      have hR1 : (residualUnits 14 D b).card = 1 := by have := card_residual h.1 b hbp; omega
      obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
      have ha3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) ⟨h12', ha1, ha2, hav, hv1, hv2⟩
      have hrua : ru D b a1 = {u0} := by
        have hcc := cc_le h hD b hbp a1
        have hsub1 : ru D b a1 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
        exact Finset.eq_of_subset_of_card_le hsub1 (by rw [Finset.card_singleton]; omega)
      have hpure := w3_ru_one_pure h hD hB0 b hb hpos (hI ▸ hi1) (hI ▸ hi2)
        ⟨hda, h12', ha1, ha2, hav, hv1, hv2⟩ hrua
      have hle2 : ∀ x : Fin 14, x ≠ a1 → (sem_W 14 D x).card ≤ 2 := fun x hx => by
        have hrux : ru D b x = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
          have hu_eq : u = u0 := Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)
          exact hx (hpure x (hu_eq ▸ (mem_ru.1 hu).2))
        have := cc_le h hD b hbp x; rw [hrux, Finset.card_empty] at this; omega
      exact ps_side_3star h hD hpos a5 a6 a7 a8 a9 a10 (hI ▸ hik1) (hI ▸ hik2) (hI ▸ hnu) hg
        (hle2 a5 hua) (hle2 a6 hk1a) (hle2 a7 hk2a)

def cntB2RIdx (k : Fin 26) : Fin 68 :=
  match k.val with
  | 0 => ⟨30, by decide⟩
  | 1 => ⟨31, by decide⟩
  | 2 => ⟨32, by decide⟩
  | 3 => ⟨33, by decide⟩
  | 4 => ⟨34, by decide⟩
  | 5 => ⟨35, by decide⟩
  | 6 => ⟨36, by decide⟩
  | 7 => ⟨37, by decide⟩
  | 8 => ⟨38, by decide⟩
  | 9 => ⟨41, by decide⟩
  | 10 => ⟨43, by decide⟩
  | 11 => ⟨47, by decide⟩
  | 12 => ⟨52, by decide⟩
  | 13 => ⟨53, by decide⟩
  | 14 => ⟨54, by decide⟩
  | 15 => ⟨55, by decide⟩
  | 16 => ⟨56, by decide⟩
  | 17 => ⟨57, by decide⟩
  | 18 => ⟨59, by decide⟩
  | 19 => ⟨60, by decide⟩
  | 20 => ⟨61, by decide⟩
  | 21 => ⟨63, by decide⟩
  | 22 => ⟨64, by decide⟩
  | 23 => ⟨65, by decide⟩
  | 24 => ⟨66, by decide⟩
  | _ => ⟨67, by decide⟩

theorem cntB2R_ge3 : ∀ k : Fin 26, 3 ≤ (hc_rep (cntB2RIdx k)).card := by decide +kernel

theorem cnt_b2_R_check : ∀ k : Fin 26, ∀ m : Fin 128,
    let I := hc_rep (cntB2RIdx k)
    let P := sideR \ I
    let Oc := maskFin7 m
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    (∀ j ∈ Oc, g14_nbB (os_ptL j) ⊆ P) →
    (2 * P.card + 12 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (12 < (14 - I.card) + 2 + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_cnt_b2_R {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (k : Fin 26)
    (hI : ineligSet 14 D = hc_rep (cntB2RIdx k)) : False := by
  have hel := inelig_card_add 14 D
  have hge3 : 3 ≤ (hc_rep (cntB2RIdx k)).card := cntB2R_ge3 k
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 (cntB2RIdx k) hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 (cntB2RIdx k) hge3 hI
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  rw [hI] at hsub hcnt hlost hel
  have hts := totalSurplus_split 14 D
  rcases cnt_b2_R_check k m hsub with hbad | hbad <;> omega

def tA (T : Finset (Fin 14)) (f : Fin 14) : Finset (Fin 14) :=
  T.erase f ∪ Finset.univ.filter
    (fun a => hc_adjB f a = true ∧ ∀ g ∈ T.erase f, hc_adjB a g = false)

def tOK (T J : Finset (Fin 14)) : Bool :=
  decide (∀ i ∈ J, (∃ a ∈ T, hc_adjB i a = true) ∧
    ∀ f ∈ T, ∃ a ∈ tA T f, hc_adjB i a = true) &&
  decide (∀ f ∈ T, (∀ a ∈ tA T f, ∀ b ∈ tA T f, hc_adjB a b = false) ∧
    ∃ a ∈ tA T f, hc_adjB f a = true) &&
  decide (T.card = 3 ∧ J.card = 3) &&
  decide (∀ i ∈ J, T ⊆ sideR ∧ sem_g14_nb i ⊆ sideR ∧ (sem_g14_nb i ∩ T).card = 2) &&
  decide (∀ i ∈ J, ∀ j ∈ J, sem_g14_nb j ∩ T ⊆ sem_g14_nb i ∩ T → j = i) &&
  decide (∀ t ∈ T, (J.filter (fun i => hc_adjB i t = true)).card ≤ 2 ∧
    ∀ i ∈ J, hc_adjB i t = false → T.erase t ⊆ sem_g14_nb i)

theorem tOK_iff {T J : Finset (Fin 14)} (h : tOK T J = true) :
    (∀ i ∈ J, (∃ a ∈ T, hc_adjB i a = true) ∧ ∀ f ∈ T, ∃ a ∈ tA T f, hc_adjB i a = true) ∧
    (∀ f ∈ T, (∀ a ∈ tA T f, ∀ b ∈ tA T f, hc_adjB a b = false) ∧
      ∃ a ∈ tA T f, hc_adjB f a = true) ∧
    (T.card = 3 ∧ J.card = 3) ∧
    (∀ i ∈ J, T ⊆ sideR ∧ sem_g14_nb i ⊆ sideR ∧ (sem_g14_nb i ∩ T).card = 2) ∧
    (∀ i ∈ J, ∀ j ∈ J, sem_g14_nb j ∩ T ⊆ sem_g14_nb i ∩ T → j = i) ∧
    ∀ t ∈ T, (J.filter (fun i => hc_adjB i t = true)).card ≤ 2 ∧
      ∀ i ∈ J, hc_adjB i t = false → T.erase t ⊆ sem_g14_nb i := by
  simpa only [tOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem tri_hyp {T J : Finset (Fin 14)} {D : Dag} (hOK : tOK T J = true)
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (∀ i ∈ J, i ∈ ineligSet 14 D ∧ (∃ a ∈ T, G14 i a) ∧ ∀ f ∈ T, ∃ a ∈ tA T f, G14 i a) ∧
    ∀ f ∈ T, (∀ a ∈ tA T f, ∀ b ∈ tA T f, ¬ G14 a b) ∧ T.erase f ⊆ tA T f ∧
      ∃ a ∈ tA T f, G14 f a := by
  obtain ⟨h1, h2, -⟩ := tOK_iff hOK
  exact ⟨fun i hi => ⟨hJ i hi, (h1 i hi).1.imp (fun _ ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩),
    fun f hf => ((h1 i hi).2 f hf).imp (fun _ ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩)⟩,
    fun f hf => ⟨fun a ha b hb => sem_adjB_false.1 ((h2 f hf).1 a ha b hb),
      Finset.subset_union_left,
      (h2 f hf).2.imp (fun _ ha => ⟨ha.1, (hc_adjB_iff _ _).1 ha.2⟩)⟩⟩

theorem g14_exact {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {P : Finset (Fin 14)} (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hsub : sem_g14_nb i ⊆ P) :
    sup_Occ 14 D P (sem_g14_nb i) := by
  by_contra hn
  have := g14_lost h hD P hP {i} (fun j hj => by
    rw [Finset.mem_singleton.1 hj]; exact ⟨hi, hsub, hn⟩)
  rw [Finset.card_singleton] at this; omega

theorem tri_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hz : Bzero 14 D ≤ 1)
    {T J : Finset (Fin 14)} (hOK : tOK T J = true) (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (eligSet 14 D).card + 3 ≤ Bplus 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  obtain ⟨hJ', hA'⟩ := tri_hyp hOK hJ
  obtain ⟨-, -, ⟨hT3, hJ3⟩, hside, hinj, -⟩ := tOK_iff hOK
  have hM : ∀ i ∈ J, ∃ M, sup_Occ 14 D T M ∧ sem_g14_nb i ∩ T ⊆ M ∧
      (sup_Occ 14 D sideR (sem_g14_nb i) → M = sem_g14_nb i ∩ T) := by
    intro i hi
    by_cases hx : sup_Occ 14 D sideR (sem_g14_nb i)
    · obtain ⟨w, hw⟩ := hx
      have : supp 14 D w ∩ T = sem_g14_nb i ∩ T := by
        rw [← hw, Finset.inter_assoc, Finset.inter_eq_right.2 (hside i hi).1]
      exact ⟨_, ⟨w, rfl⟩, this ▸ Finset.Subset.refl _, fun _ => this⟩
    · exact ⟨supp 14 D (src D (pos i)) ∩ T, ⟨_, rfl⟩, fun a ha => by
        rw [Finset.mem_inter, g14_mem_nb] at ha
        exact Finset.mem_inter.2 ⟨(hpos.1 i (hJ i hi)).2.2.1 a ha.1, ha.2⟩,
        fun hc => absurd hc hx⟩
  choose! M hM using hM
  have hlost := g14_lost h hD sideR sideR_indep
    (J.filter (fun i => ¬ sup_Occ 14 D sideR (sem_g14_nb i))) (fun i hi => by
      rw [Finset.mem_filter] at hi
      exact ⟨hJ i hi.1, (hside i hi.1).2.1, hi.2⟩)
  have hMinj : Set.InjOn M J := by
    intro i hi j hj hij
    by_contra hne
    have key : ∀ i ∈ J, ∀ j ∈ J, M i = M j → i ≠ j →
        ¬ sup_Occ 14 D sideR (sem_g14_nb i) := by
      intro i hi j hj hij hne hx
      exact hne (hinj i hi j hj (by
        rw [← (hM i hi).2.2 hx, hij]; exact (hM j hj).2.1)).symm
    have h1 : i ∈ J.filter (fun i => ¬ sup_Occ 14 D sideR (sem_g14_nb i)) :=
      Finset.mem_filter.2 ⟨hi, key i hi j hj hij hne⟩
    have h2 : j ∈ J.filter (fun i => ¬ sup_Occ 14 D sideR (sem_g14_nb i)) :=
      Finset.mem_filter.2 ⟨hj, key j hj i hi hij.symm (Ne.symm hne)⟩
    have := Finset.one_lt_card.2 ⟨i, h1, j, h2, hne⟩
    omega
  have := tri_occ hG h hC b hb hpos T J (tA T) hJ' hA' (J.image M) (fun X hX => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hX
    have := Finset.card_le_card (hM i hi).2.1
    rw [(hside i hi).2.2] at this
    exact ⟨this, (hM i hi).1⟩)
  rw [Finset.card_image_of_injOn hMinj] at this
  omega

theorem tri_g14_sat {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (hB : Bplus 14 D ≤ (eligSet 14 D).card + 3) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    {T J : Finset (Fin 14)} (hOK : tOK T J = true) (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D) :
    (∀ t ∈ T, (sem_W 14 D t).card ≤ 3 ∧ merges 14 D (carrierT 14 D {t}) = ∅) ∧
    ∀ u ∈ residualUnits 14 D b, (supp 14 D u.1 ∩ T).Nonempty := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  obtain ⟨hJ', hA'⟩ := tri_hyp hOK hJ
  obtain ⟨-, -, ⟨hT3, hJ3⟩, hside, hinj, hgeo⟩ := tOK_iff hOK
  have hFinj : Set.InjOn (fun i => sem_g14_nb i ∩ T) J :=
    fun i hi j hj hij => hinj j hj i hi (by rw [show sem_g14_nb i ∩ T = sem_g14_nb j ∩ T from hij])
  have hocc : ∀ i ∈ J, sup_Occ 14 D T (sem_g14_nb i ∩ T) := by
    intro i hi
    obtain ⟨w, hw⟩ := g14_exact h hD hB0 sideR_indep (hJ i hi) (hside i hi).2.1
    refine ⟨w, ?_⟩
    rw [← hw, Finset.inter_assoc, Finset.inter_eq_right.2 (hside i hi).1]
  obtain ⟨hnofull, hT, hU⟩ := tri_sat hG h hC b hb hpos T J (tA T) hJ' hA'
    (J.image (fun i => sem_g14_nb i ∩ T)) (fun X hX => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hX
      exact ⟨(hside i hi).2.2, hocc i hi⟩) hT3
    (by rw [Finset.card_image_of_injOn hFinj]; omega)
  refine ⟨fun t ht => ⟨?_, (hT t ht).1⟩, hU⟩
  obtain ⟨e1, he1⟩ := (hT t ht).2
  have hsub : sem_W 14 D t ⊆ insert e1 ((J.filter (fun i => hc_adjB i t = true)).image pos) := by
    intro e he
    rcases he1 e he with rfl | h1
    · exact Finset.mem_insert_self _ _
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h1
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, ?_⟩, rfl⟩)
      by_contra hadj
      rw [Bool.not_eq_true] at hadj
      refine hnofull (src D (pos i)) (fun a ha => ?_)
      by_cases hat : a = t
      · rw [hat]; exact (sem_mem_W.1 he).2.1
      · exact (hpos.1 i (hJ i hi)).2.2.1 a
          (g14_mem_nb.1 ((hgeo t ht).2 i hi hadj (Finset.mem_erase.2 ⟨hat, ha⟩)))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le e1 ((J.filter (fun i => hc_adjB i t = true)).image pos)
  have h4 := Finset.card_image_le (s := J.filter (fun i => hc_adjB i t = true)) (f := pos)
  have h5 := (hgeo t ht).1
  omega

theorem tOK_024 : tOK {8, 10, 13} {0, 2, 4} = true := by decide +kernel

theorem elim_39 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨39, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {0, 2, 4, 7} := by rw [hI]; decide
  rw [hIeq, show ({0, 2, 4, 7} : Finset (Fin 14)).card = 4 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨39, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨39, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have htri := tri_g14 h hD (by omega) tOK_024 (fun i hi => by rw [hIeq]; revert i hi; decide)
  omega

theorem elim_46 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨46, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {0, 2, 4, 9} := by rw [hI]; decide
  rw [hIeq, show ({0, 2, 4, 9} : Finset (Fin 14)).card = 4 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨46, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨46, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have htri := tri_g14 h hD (by omega) tOK_024 (fun i hi => by rw [hIeq]; revert i hi; decide)
  omega

theorem cnt_58_b3_check : ∀ m : Fin 128,
    let I := hc_rep ⟨58, by decide⟩
    let P := sideR \ I
    let Oc := maskFin7 m
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    (∀ j ∈ Oc, g14_nbB (os_ptL j) ⊆ P) →
    (2 * P.card + 12 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (12 < (14 - I.card) + 3 + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_58 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨58, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {0, 2, 4, 5, 7} := by rw [hI]; decide
  rw [hIeq, show ({0, 2, 4, 5, 7} : Finset (Fin 14)).card = 5 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨58, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨58, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have htri := tri_g14 h hD (by omega) tOK_024 (fun i hi => by rw [hIeq]; revert i hi; decide)
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  rw [hI] at hsub hcnt hlost
  have hcard5 : (hc_rep ⟨58, by decide⟩).card = 5 := by decide
  rcases cnt_58_b3_check m hsub with hbad | hbad <;> omega

def sub3b (a b : Bool × Bool × Bool) : Bool :=
  (!a.1 || b.1) && (!a.2.1 || b.2.1) && (!a.2.2 || b.2.2)

theorem antichain4_bool3 : ∀ a b c d : Bool × Bool × Bool,
    sub3b a b = true ∨ sub3b b a = true ∨
    sub3b a c = true ∨ sub3b c a = true ∨
    sub3b a d = true ∨ sub3b d a = true ∨
    sub3b b c = true ∨ sub3b c b = true ∨
    sub3b b d = true ∨ sub3b d b = true ∨
    sub3b c d = true ∨ sub3b d c = true := by decide +kernel

theorem finset_antichain4_of_card3 {α : Type} [DecidableEq α] {R A B C D : Finset α}
    (hR : R.card = 3) (hA : A ⊆ R) (hB : B ⊆ R) (hC : C ⊆ R) (hD : D ⊆ R) :
    A ⊆ B ∨ B ⊆ A ∨ A ⊆ C ∨ C ⊆ A ∨ A ⊆ D ∨ D ⊆ A ∨
    B ⊆ C ∨ C ⊆ B ∨ B ⊆ D ∨ D ⊆ B ∨ C ⊆ D ∨ D ⊆ C := by
  classical
  obtain ⟨u1, u2, u3, -, -, -, hReq⟩ := Finset.card_eq_three.1 hR
  let enc : Finset α → Bool × Bool × Bool := fun S =>
    (decide (u1 ∈ S), decide (u2 ∈ S), decide (u3 ∈ S))
  have hsub : ∀ X Y : Finset α, X ⊆ R → sub3b (enc X) (enc Y) = true → X ⊆ Y := by
    intro X Y hXR hle x hx
    have hxR : x ∈ R := hXR hx
    rw [hReq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hxR
    simp only [sub3b, enc, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hle
    rcases hxR with rfl | rfl | rfl
    · exact hle.1.1.resolve_left (not_not.2 hx)
    · exact hle.1.2.resolve_left (not_not.2 hx)
    · exact hle.2.resolve_left (not_not.2 hx)
  rcases antichain4_bool3 (enc A) (enc B) (enc C) (enc D) with
    h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (hsub A B hA h)
  · exact Or.inr (Or.inl (hsub B A hB h))
  · exact Or.inr (Or.inr (Or.inl (hsub A C hA h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hsub C A hC h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub A D hA h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub D A hD h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub B C hB h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub C B hC h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub B D hB h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub D B hD h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsub C D hC h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsub D C hD h)))))))))))

theorem elim_62 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨62, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {0, 2, 4, 7, 9} := by rw [hI]; decide
  rw [hIeq, show ({0, 2, 4, 7, 9} : Finset (Fin 14)).card = 5 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨62, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨62, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have htri := tri_g14 h hD (by omega) tOK_024 (fun i hi => by rw [hIeq]; revert i hi; decide)
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR3 : (residualUnits 14 D b).card = 3 := by have := card_residual h.1 b hb; omega
  obtain ⟨hT, -⟩ := tri_g14_sat h hD hB0 (by omega) b hb tOK_024 (fun i hi => by rw [hIeq]; revert i hi; decide)
  have hm : ∀ v : Fin 14, v ∈ ({0, 2, 4, 7, 9} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 14, v ∉ ({0, 2, 4, 7, 9} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  have hf8 := full_of_two_in_deg3 h hD hB0 hpos (hm 0 (by decide)) (hm 2 (by decide))
    (by decide : (0 : Fin 14) ≠ 2 ∧ hc_adjB 0 8 = true ∧ hc_adjB 2 8 = true ∧ hc_adjB 8 6 = true ∧ (6 : Fin 14) ≠ 0 ∧ (6 : Fin 14) ≠ 2)
    (hT 8 (by decide)).1
  have hf10 := full_of_two_in_deg3 h hD hB0 hpos (hm 0 (by decide)) (hm 4 (by decide))
    (by decide : (0 : Fin 14) ≠ 4 ∧ hc_adjB 0 10 = true ∧ hc_adjB 4 10 = true ∧ hc_adjB 10 5 = true ∧ (5 : Fin 14) ≠ 0 ∧ (5 : Fin 14) ≠ 4)
    (hT 10 (by decide)).1
  have hne1 : (ru D b 1).Nonempty := Finset.card_pos.1 (by
    have h3 := two_in_deg3 h hD hpos (hm 7 (by decide)) (hm 9 (by decide))
      (by decide : (7 : Fin 14) ≠ 9 ∧ hc_adjB 7 1 = true ∧ hc_adjB 9 1 = true ∧ hc_adjB 1 13 = true ∧ (13 : Fin 14) ≠ 7 ∧ (13 : Fin 14) ≠ 9)
    have := cc_le h hD b hb 1; omega)
  have hne8 : (ru D b 8).Nonempty := Finset.card_pos.1 (by
    have h3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 2 (by decide))
      (by decide : (0 : Fin 14) ≠ 2 ∧ hc_adjB 0 8 = true ∧ hc_adjB 2 8 = true ∧ hc_adjB 8 6 = true ∧ (6 : Fin 14) ≠ 0 ∧ (6 : Fin 14) ≠ 2)
    have := cc_le h hD b hb 8; omega)
  have hne10 : (ru D b 10).Nonempty := Finset.card_pos.1 (by
    have h3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 4 (by decide))
      (by decide : (0 : Fin 14) ≠ 4 ∧ hc_adjB 0 10 = true ∧ hc_adjB 4 10 = true ∧ hc_adjB 10 5 = true ∧ (5 : Fin 14) ≠ 0 ∧ (5 : Fin 14) ≠ 4)
    have := cc_le h hD b hb 10; omega)
  have hne13 : (ru D b 13).Nonempty := Finset.card_pos.1 (by
    have h3 := two_in_deg3 h hD hpos (hm 2 (by decide)) (hm 4 (by decide))
      (by decide : (2 : Fin 14) ≠ 4 ∧ hc_adjB 2 13 = true ∧ hc_adjB 4 13 = true ∧ hc_adjB 13 1 = true ∧ (1 : Fin 14) ≠ 2 ∧ (1 : Fin 14) ≠ 4)
    have := cc_le h hD b hb 13; omega)

  have hkill_full : ∀ (v t j q : Fin 14), j ∈ ineligSet 14 D → v ∈ eligSet 14 D →
      (∀ z, z ∈ supp 14 D (src D (pos j)) → Adj j z) →
      ((g14_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧ v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB j t = false) →
      (ru D b v).Nonempty → ru D b v ⊆ ru D b t → False := by
    intro v t j q hj hv hfull hg hne hsub
    obtain ⟨u, hu⟩ := hne
    have hres : ∀ u' ∈ residualUnits 14 D b, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
      fun u' hu' hv' => (mem_ru.1 (hsub (mem_ru.2 ⟨hu', hv'⟩))).2
    have hw : v ∈ supp 14 D u.1 ∧ t ∈ supp 14 D u.1 := ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub hu)).2⟩
    exact sem_adjB_false.1 hg.2.2.2.2.2.2
      (hfull t (pe_co_g14 h hD b hb hpos hj hv hres hw ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1⟩))
  have hno_8_10 : ¬ ru D b 8 ⊆ ru D b 10 := hkill_full 8 10 2 12 (hm 2 (by decide)) (helig 8 (by decide)) hf8.2 (by decide) hne8
  have hno_10_8 : ¬ ru D b 10 ⊆ ru D b 8 := hkill_full 10 8 4 11 (hm 4 (by decide)) (helig 10 (by decide)) hf10.2 (by decide) hne10
  have hno_8_13 : ¬ ru D b 8 ⊆ ru D b 13 := hkill_full 8 13 0 10 (hm 0 (by decide)) (helig 8 (by decide)) hf8.1 (by decide) hne8
  have hno_13_8 : ¬ ru D b 13 ⊆ ru D b 8 := hkill_full 13 8 4 10 (hm 4 (by decide)) (helig 13 (by decide)) hf10.2 (by decide) hne13
  have hno_10_13 : ¬ ru D b 10 ⊆ ru D b 13 := hkill_full 10 13 0 8 (hm 0 (by decide)) (helig 10 (by decide)) hf8.1 (by decide) hne10
  have hno_13_10 : ¬ ru D b 13 ⊆ ru D b 10 := hkill_full 13 10 2 8 (hm 2 (by decide)) (helig 13 (by decide)) hf8.2 (by decide) hne13
  have hno_8_1 : ¬ ru D b 8 ⊆ ru D b 1 := hkill_full 8 1 0 10 (hm 0 (by decide)) (helig 8 (by decide)) hf8.1 (by decide) hne8
  have hno_10_1 : ¬ ru D b 10 ⊆ ru D b 1 := hkill_full 10 1 0 8 (hm 0 (by decide)) (helig 10 (by decide)) hf8.1 (by decide) hne10
  have hno_13_1 : ¬ ru D b 13 ⊆ ru D b 1 := hkill_full 13 1 2 8 (hm 2 (by decide)) (helig 13 (by decide)) hf8.2 (by decide) hne13

  have hno_1_t : ∀ t ∈ ({8, 10, 13} : Finset (Fin 14)), ¬ ru D b 1 ⊆ ru D b t := by
    intro t ht hs
    have hcard_le : (ru D b 1).card ≤ (ru D b t).card := Finset.card_le_card hs
    have ht_lt3 : (ru D b t).card < 3 := by
      by_contra hge
      have htR : ru D b t = residualUnits 14 D b :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hno_10_8 (by rw [htR]; exact Finset.filter_subset _ _)
      · exact hno_8_10 (by rw [htR]; exact Finset.filter_subset _ _)
      · exact hno_8_13 (by rw [htR]; exact Finset.filter_subset _ _)
    by_cases h1_card : (ru D b 1).card = 1
    · have hc1_le3 : (sem_W 14 D 1).card ≤ 3 := by have := cc_le h hD b hb 1; omega
      have hf1 := full_of_two_in_deg3 h hD hB0 hpos (hm 7 (by decide)) (hm 9 (by decide))
        (by decide : (7 : Fin 14) ≠ 9 ∧ hc_adjB 7 1 = true ∧ hc_adjB 9 1 = true ∧ hc_adjB 1 13 = true ∧ (13 : Fin 14) ≠ 7 ∧ (13 : Fin 14) ≠ 9)
        hc1_le3
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hkill_full 1 8 7 3 (hm 7 (by decide)) (helig 1 (by decide)) hf1.1 (by decide) hne1 hs
      · exact hkill_full 1 10 7 3 (hm 7 (by decide)) (helig 1 (by decide)) hf1.1 (by decide) hne1 hs
      · exact hkill_full 1 13 7 3 (hm 7 (by decide)) (helig 1 (by decide)) hf1.1 (by decide) hne1 hs
    · have h1_pos : 0 < (ru D b 1).card := Finset.card_pos.2 hne1
      have heq : ru D b 1 = ru D b t := Finset.eq_of_subset_of_card_le hs (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hno_8_1 (by rw [heq])
      · exact hno_10_1 (by rw [heq])
      · exact hno_13_1 (by rw [heq])
  rcases finset_antichain4_of_card3 hR3 (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (A := ru D b 1) (B := ru D b 8) (C := ru D b 10) (D := ru D b 13) with
    hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hno_1_t 8 (by decide) hs
  · exact hno_8_1 hs
  · exact hno_1_t 10 (by decide) hs
  · exact hno_10_1 hs
  · exact hno_1_t 13 (by decide) hs
  · exact hno_13_1 hs
  · exact hno_8_10 hs
  · exact hno_10_8 hs
  · exact hno_8_13 hs
  · exact hno_13_8 hs
  · exact hno_10_13 hs
  · exact hno_13_10 hs

theorem finset_pair_incomp {α : Type} [DecidableEq α] {u1 u2 : α} (hne : u1 ≠ u2)
    {A B : Finset α} (hA : A ⊆ {u1, u2}) (hB : B ⊆ {u1, u2})
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) :
    (A = {u1} ∧ B = {u2}) ∨ (A = {u2} ∧ B = {u1}) := by
  have hcases : ∀ S : Finset α, S ⊆ {u1, u2} → S.Nonempty → S = {u1} ∨ S = {u2} ∨ S = {u1, u2} := by
    intro S hS hSn
    by_cases h1 : u1 ∈ S <;> by_cases h2 : u2 ∈ S
    · right; right
      refine Finset.Subset.antisymm hS (fun x hx => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · left
      refine Finset.Subset.antisymm (fun x hx => ?_) (Finset.singleton_subset_iff.2 h1)
      have hx2 := hS hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hx h2
    · right; left
      refine Finset.Subset.antisymm (fun x hx => ?_) (Finset.singleton_subset_iff.2 h2)
      have hx2 := hS hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl
      · exact absurd hx h1
      · exact Finset.mem_singleton_self _
    · obtain ⟨x, hx⟩ := hSn
      have hx2 := hS hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl
      · exact absurd hx h1
      · exact absurd hx h2
  rcases hcases A hA hAn with rfl | rfl | rfl <;> rcases hcases B hB hBn with rfl | rfl | rfl
  · exact absurd (Finset.Subset.refl _) hAB
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd (by simp) hAB
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd (Finset.Subset.refl _) hAB
  · exact absurd (by simp) hAB
  · exact absurd (by simp) hBA
  · exact absurd (by simp) hBA
  · exact absurd (Finset.Subset.refl _) hAB

theorem elim_res2_w3_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (idx : Fin 68) (hI : ineligSet 14 D = hc_rep idx)
    (hc4 : (hc_rep idx).card = 4)
    (a b' ia1 ia2 av ib1 ib2 bv : Fin 14)
    (hia1 : ia1 ∈ ineligSet 14 D) (hia2 : ia2 ∈ ineligSet 14 D)
    (hib1 : ib1 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (hga : (g14_nbB a).card = 3 ∧ ia1 ≠ ia2 ∧ hc_adjB ia1 a = true ∧ hc_adjB ia2 a = true ∧
           hc_adjB a av = true ∧ av ≠ ia1 ∧ av ≠ ia2)
    (hgb : (g14_nbB b').card = 3 ∧ ib1 ≠ ib2 ∧ hc_adjB ib1 b' = true ∧ hc_adjB ib2 b' = true ∧
           hc_adjB b' bv = true ∧ bv ≠ ib1 ∧ bv ≠ ib2)
    (z k v iz ik : Fin 14)
    (hiz : iz ∈ ineligSet 14 D) (hik : ik ∈ ineligSet 14 D)
    (hnz : z ∉ ineligSet 14 D) (hnk : k ∉ ineligSet 14 D) (hnv : v ∉ ineligSet 14 D)
    (hpm : z ≠ a ∧ z ≠ b' ∧ k ≠ a ∧ k ≠ b' ∧
           hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
           hc_adjB z v = true ∧ v ≠ k ∧ (g14_nbB k).card = 3 ∧
           decide (v.val < 7) = decide (k.val < 7))
    (hno_ab : ∀ (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) (pos : Fin 14 → ℕ × Bool),
      Bzero 14 D = 0 → k4_Pos 14 G14 D pos → (residualUnits 14 D br).card = 2 →
      (ru D br a).Nonempty → ru D br a ⊆ ru D br b' → False)
    (hno_ba : ∀ (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) (pos : Fin 14 → ℕ × Bool),
      Bzero 14 D = 0 → k4_Pos 14 G14 D pos → (residualUnits 14 D br).card = 2 →
      (ru D br b').Nonempty → ru D br b' ⊆ ru D br a → False) : False := by
  have hel := inelig_card_add 14 D
  rw [hI, hc4] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 idx hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 idx (by omega) hI
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g14_gr h.1 (sem_g14_comp hD)
  have hbr := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
  have hnea : (ru D br a).Nonempty := Finset.card_pos.1 (by
    have h3 := two_in_deg3 h hD hpos hia1 hia2 hga.2
    have := cc_le h hD br hbr a; omega)
  have hneb : (ru D br b').Nonempty := Finset.card_pos.1 (by
    have h3 := two_in_deg3 h hD hpos hib1 hib2 hgb.2
    have := cc_le h hD br hbr b'; omega)
  have hpair := finset_pair_incomp hu12 (hReq ▸ Finset.filter_subset _ _) (hReq ▸ Finset.filter_subset _ _)
    hnea hneb (fun hs => hno_ab br hbr pos hB0 hpos hR2 hnea hs) (fun hs => hno_ba br hbr pos hB0 hpos hR2 hneb hs)
  have hclean : ∀ ua ub, residualUnits 14 D br = {ua, ub} → ru D br a = {ua} → ru D br b' = {ub} → False := by
    intro ua ub hR' hra hrb
    have hpa := w3_ru_one_pure h hD hB0 br hbm hpos hia1 hia2 hga hra
    have hpb := w3_ru_one_pure h hD hB0 br hbm hpos hib1 hib2 hgb hrb
    have hle2 : ∀ x : Fin 14, x ≠ a → x ≠ b' → (sem_W 14 D x).card ≤ 2 := fun x hxa hxb => by
      have hrux : ru D br x = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
        obtain ⟨huR, hxu⟩ := mem_ru.1 hu
        rw [hR', Finset.mem_insert, Finset.mem_singleton] at huR
        rcases huR with rfl | rfl
        · exact hxa (hpa x hxu)
        · exact hxb (hpb x hxu)
      have := cc_le h hD br hbr x; rw [hrux, Finset.card_empty] at this; omega
    exact pa_m1 h hD hpos z k v iz ik hiz hik hnz hnk hnv hpm.2.2.2.2
      (hle2 z hpm.1 hpm.2.1) (hle2 k hpm.2.2.1 hpm.2.2.2.1)
  rcases hpair with ⟨ha1, hb2⟩ | ⟨ha2, hb1⟩
  · exact hclean u1 u2 hReq ha1 hb2
  · exact hclean u2 u1 (by rw [hReq, Finset.pair_comm]) ha2 hb1

theorem elim_48 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨48, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0, 2, 7, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 14, v ∈ ({0, 2, 7, 9} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({0, 2, 7, 9} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hel : ∀ v : Fin 14, v ∉ ({0, 2, 7, 9} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_w3_pair h hD h12 ⟨48, by decide⟩ hI (by decide) 1 8 7 9 13 0 2 6
    (hm 7 (by decide)) (hm 9 (by decide)) (hm 0 (by decide)) (hm 2 (by decide)) (by decide) (by decide)
    3 12 11 7 2 (hm 7 (by decide)) (hm 2 (by decide)) (hn 3 (by decide)) (hn 12 (by decide)) (hn 11 (by decide)) (by decide)
    (fun br hbr pos _ hpos hR2 hne hs => pe_co_blow5 h hD br hbr hpos 1 8 7 9 3 5 0 2 6
      (hel 1 (by decide)) (hm 7 (by decide)) (hm 9 (by decide)) (hm 0 (by decide)) (hm 2 (by decide)) (hn 6 (by decide))
      (by decide) (Finset.card_pos.2 hne) hs (by have := Finset.card_filter_le (residualUnits 14 D br) (fun u => (8 : Fin 14) ∈ supp 14 D u.1); unfold ru; omega))
    (fun br hbr pos _ hpos hR2 hne hs => pe_co_blow5 h hD br hbr hpos 8 1 0 2 10 12 7 9 13
      (hel 8 (by decide)) (hm 0 (by decide)) (hm 2 (by decide)) (hm 7 (by decide)) (hm 9 (by decide)) (hn 13 (by decide))
      (by decide) (Finset.card_pos.2 hne) hs (by have := Finset.card_filter_le (residualUnits 14 D br) (fun u => (1 : Fin 14) ∈ supp 14 D u.1); unfold ru; omega))

theorem elim_49 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨49, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {2, 4, 7, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 14, v ∈ ({2, 4, 7, 9} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({2, 4, 7, 9} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hel : ∀ v : Fin 14, v ∉ ({2, 4, 7, 9} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_w3_pair h hD h12 ⟨49, by decide⟩ hI (by decide) 1 13 7 9 13 2 4 1
    (hm 7 (by decide)) (hm 9 (by decide)) (hm 2 (by decide)) (hm 4 (by decide)) (by decide) (by decide)
    3 11 12 7 4 (hm 7 (by decide)) (hm 4 (by decide)) (hn 3 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (by decide)
    (fun br hbr pos _ hpos hR2 hne hs => pe_co_blow5 h hD br hbr hpos 1 13 7 9 3 5 2 4 1
      (hel 1 (by decide)) (hm 7 (by decide)) (hm 9 (by decide)) (hm 2 (by decide)) (hm 4 (by decide)) (hn 1 (by decide))
      (by decide) (Finset.card_pos.2 hne) hs (by have := Finset.card_filter_le (residualUnits 14 D br) (fun u => (13 : Fin 14) ∈ supp 14 D u.1); unfold ru; omega))
    (fun br hbr pos _ hpos hR2 hne hs => pe_co_blow5 h hD br hbr hpos 13 1 2 4 8 10 7 9 13
      (hel 13 (by decide)) (hm 2 (by decide)) (hm 4 (by decide)) (hm 7 (by decide)) (hm 9 (by decide)) (hn 13 (by decide))
      (by decide) (Finset.card_pos.2 hne) hs (by have := Finset.card_filter_le (residualUnits 14 D br) (fun u => (1 : Fin 14) ∈ supp 14 D u.1); unfold ru; omega))

theorem elim_50 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨50, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {3, 4, 8, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 14, v ∈ ({3, 4, 8, 9} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({3, 4, 8, 9} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hel : ∀ v : Fin 14, v ∉ ({3, 4, 8, 9} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_w3_pair h hD h12 ⟨50, by decide⟩ hI (by decide) 6 11 8 9 11 3 4 6
    (hm 8 (by decide)) (hm 9 (by decide)) (hm 3 (by decide)) (hm 4 (by decide)) (by decide) (by decide)
    1 13 7 9 4 (hm 9 (by decide)) (hm 4 (by decide)) (hn 1 (by decide)) (hn 13 (by decide)) (hn 7 (by decide)) (by decide)
    (fun br hbr pos _ hpos hR2 hne hs => pe_co_blow5 h hD br hbr hpos 6 11 8 9 0 1 3 4 6
      (hel 6 (by decide)) (hm 8 (by decide)) (hm 9 (by decide)) (hm 3 (by decide)) (hm 4 (by decide)) (hn 6 (by decide))
      (by decide) (Finset.card_pos.2 hne) hs (by have := Finset.card_filter_le (residualUnits 14 D br) (fun u => (11 : Fin 14) ∈ supp 14 D u.1); unfold ru; omega))
    (fun br hbr pos _ hpos hR2 hne hs => pe_co_blow5 h hD br hbr hpos 11 6 3 4 7 10 8 9 11
      (hel 11 (by decide)) (hm 3 (by decide)) (hm 4 (by decide)) (hm 8 (by decide)) (hm 9 (by decide)) (hn 11 (by decide))
      (by decide) (Finset.card_pos.2 hne) hs (by have := Finset.card_filter_le (residualUnits 14 D br) (fun u => (6 : Fin 14) ∈ supp 14 D u.1); unfold ru; omega))

theorem shared_w3_no_sub {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    (hR2 : (residualUnits 14 D br).card = 2)
    (a b i0 ia ib va vb qa qb : Fin 14)
    (ha : a ∈ eligSet 14 D) (hb : b ∈ eligSet 14 D)
    (hi0 : i0 ∈ ineligSet 14 D) (hia : ia ∈ ineligSet 14 D) (hib : ib ∈ ineligSet 14 D)
    (hvb : vb ∉ ineligSet 14 D)
    (hg : a ≠ b ∧ i0 ≠ ia ∧ i0 ≠ ib ∧ ia ≠ ib ∧
          (g14_nbB a).card = 3 ∧ (g14_nbB b).card = 3 ∧
          hc_adjB i0 a = true ∧ hc_adjB ia a = true ∧ hc_adjB a va = true ∧ va ≠ i0 ∧ va ≠ ia ∧
          hc_adjB i0 b = true ∧ hc_adjB ib b = true ∧ hc_adjB b vb = true ∧
          hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB b qa = false ∧ hc_adjB ia b = false ∧
          hc_adjB ib qb = true ∧ b ≠ qb ∧ hc_adjB a qb = false ∧ hc_adjB ib a = false)
    (hne : (ru D br a).Nonempty) (hsub : ru D br a ⊆ ru D br b) : False := by
  obtain ⟨hab, h0a, h0b, habi, hda, hdb, g0a, gaa, gva, hva0, hvaa, g0b, gbb, gvb,
    gqa, haqa, gbqa, gnab, gqb, hbqb, gaqb, gnba⟩ := hg
  have hle2 : (ru D br a).card ≤ 2 := by
    have := Finset.card_filter_le (residualUnits 14 D br) (fun u => a ∈ supp 14 D u.1); unfold ru; omega
  have hble2 : (ru D br b).card ≤ 2 := by
    have := Finset.card_filter_le (residualUnits 14 D br) (fun u => b ∈ supp 14 D u.1); unfold ru; omega
  have hposa : 0 < (ru D br a).card := Finset.card_pos.2 hne
  by_cases ha1 : (ru D br a).card = 1
  · exact ru_sub_excl h hD hB0 br hbr hpos hi0 hia ha
      ⟨hda, h0a, g0a, gaa, gva, hva0, hvaa⟩ ha1 hsub hab ⟨qa, Or.inr ⟨gqa, haqa, gbqa, gnab⟩⟩
  · have ha2 : (ru D br a).card = 2 := by omega
    have heq : ru D br a = ru D br b := Finset.eq_of_subset_of_card_le hsub (by omega)
    obtain ⟨u, hu⟩ := hne
    have hres1 : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 :=
      fun u' hu' ha' => (mem_ru.1 (hsub (mem_ru.2 ⟨hu', ha'⟩))).2
    have hres2 : ∀ u' ∈ residualUnits 14 D br, b ∈ supp 14 D u'.1 → a ∈ supp 14 D u'.1 :=
      fun u' hu' hb' => (mem_ru.1 (by rw [heq]; exact mem_ru.2 ⟨hu', hb'⟩)).2
    have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 := ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub hu)).2⟩
    have hpa_in_b := mem_W_of_pos hpos hia (pe_co_g14 h hD br hbr hpos hia ha hres1 hw ⟨hda, gaa, gqa, hab, haqa, gbqa⟩)
    have ha_in_pb := pe_co_g14 h hD br hbr hpos hib hb hres2 ⟨hw.2, hw.1⟩ ⟨hdb, gbb, gqb, hab.symm, hbqb, gaqb⟩
    have hp0_in_b := as_mem hpos hi0 ((hc_adjB_iff _ _).1 g0b)
    have hpb_in_b := as_mem hpos hib ((hc_adjB_iff _ _).1 gbb)
    obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
    have hWb_le4 : (sem_W 14 D b).card ≤ 4 := by have := cc_le h hD br hbr b; omega
    have hWb := pa_four hpb_in_b hp0_in_b hpa_in_b hev
      (fun e => h0b.symm (hpos.2 _ hib _ hi0 e))
      (fun e => habi.symm (hpos.2 _ hib _ hia e))
      (fun e => hvb (hfv _ hib e.symm ▸ hib))
      (fun e => h0a (hpos.2 _ hi0 _ hia e))
      (fun e => hvb (hfv _ hi0 e.symm ▸ hi0))
      (fun e => hvb (hfv _ hia e.symm ▸ hia))
      hWb_le4
    have hfull := full_g14 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gbb) (fun p hp hne1 hsub' => by
      rcases hWb p hp with rfl | rfl | rfl | rfl
      · exact hne1 rfl
      · exact h0b (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hi0)))
      · exact habi (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hia)))
      · exact hvb (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbev).2.1) ▸ hib))
    exact sem_adjB_false.1 gnba ((hfull a).1 ha_in_pb)

theorem elim_42 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨42, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {1, 3, 4, 8} := by rw [hI]; decide
  have hm : ∀ v : Fin 14, v ∈ ({1, 3, 4, 8} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({1, 3, 4, 8} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hel : ∀ v : Fin 14, v ∉ ({1, 3, 4, 8} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_w3_pair h hD h12 ⟨42, by decide⟩ hI (by decide) 11 13 3 4 6 1 4 2
    (hm 3 (by decide)) (hm 4 (by decide)) (hm 1 (by decide)) (hm 4 (by decide)) (by decide) (by decide)
    2 12 13 8 3 (hm 8 (by decide)) (hm 3 (by decide)) (hn 2 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) (by decide)
    (fun br hbr pos hB0 hpos hR2 hne hs => shared_w3_no_sub h hD hB0 br hbr hpos hR2 11 13 4 3 1 6 2 12 9
      (hel 11 (by decide)) (hel 13 (by decide)) (hm 4 (by decide)) (hm 3 (by decide)) (hm 1 (by decide)) (hn 2 (by decide))
      (by decide) hne hs)
    (fun br hbr pos hB0 hpos hR2 hne hs => shared_w3_no_sub h hD hB0 br hbr hpos hR2 13 11 4 1 3 2 6 9 12
      (hel 13 (by decide)) (hel 11 (by decide)) (hm 4 (by decide)) (hm 1 (by decide)) (hm 3 (by decide)) (hn 6 (by decide))
      (by decide) hne hs)

theorem elim_45 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨45, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0, 2, 3, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 14, v ∈ ({0, 2, 3, 9} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({0, 2, 3, 9} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hel : ∀ v : Fin 14, v ∉ ({0, 2, 3, 9} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_w3_pair h hD h12 ⟨45, by decide⟩ hI (by decide) 8 12 0 2 6 2 3 5
    (hm 0 (by decide)) (hm 2 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (by decide) (by decide)
    1 13 7 9 2 (hm 9 (by decide)) (hm 2 (by decide)) (hn 1 (by decide)) (hn 13 (by decide)) (hn 7 (by decide)) (by decide)
    (fun br hbr pos hB0 hpos hR2 hne hs => shared_w3_no_sub h hD hB0 br hbr hpos hR2 8 12 2 0 3 6 5 10 11
      (hel 8 (by decide)) (hel 12 (by decide)) (hm 2 (by decide)) (hm 0 (by decide)) (hm 3 (by decide)) (hn 5 (by decide))
      (by decide) hne hs)
    (fun br hbr pos hB0 hpos hR2 hne hs => shared_w3_no_sub h hD hB0 br hbr hpos hR2 12 8 2 3 0 5 6 11 10
      (hel 12 (by decide)) (hel 8 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (hm 0 (by decide)) (hn 6 (by decide))
      (by decide) hne hs)

theorem elim_40_44_sing {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (br : Fin 14 → ℕ) (hbm : sem_MinBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {ua ub : Σ _ : ℕ, ℕ} (hR' : residualUnits 14 D br = {ua, ub}) (hru10 : ru D br 10 = {ua})
    (h4 : (4 : Fin 14) ∈ ineligSet 14 D) (h5 : (5 : Fin 14) ∈ ineligSet 14 D) (h7 : (7 : Fin 14) ∈ ineligSet 14 D)
    (hn1 : (1 : Fin 14) ∉ ineligSet 14 D) (hn2 : (2 : Fin 14) ∉ ineligSet 14 D)
    (hn3 : (3 : Fin 14) ∉ ineligSet 14 D) (hn6 : (6 : Fin 14) ∉ ineligSet 14 D)
    (hn9 : (9 : Fin 14) ∉ ineligSet 14 D) (hn11 : (11 : Fin 14) ∉ ineligSet 14 D)
    (hn12 : (12 : Fin 14) ∉ ineligSet 14 D) (hn13 : (13 : Fin 14) ∉ ineligSet 14 D) : False := by
  have hbr := sem_minBranch_pure hbm
  have hp10 := w3_ru_one_pure h hD hB0 br hbm hpos h4 h5
    (by decide : (g14_nbB 10).card = 3 ∧ (4 : Fin 14) ≠ 5 ∧ hc_adjB 4 10 = true ∧ hc_adjB 5 10 = true ∧ hc_adjB 10 0 = true ∧ (0 : Fin 14) ≠ 4 ∧ (0 : Fin 14) ≠ 5) hru10
  have hru_sub_ub : ∀ y : Fin 14, y ≠ 10 → ru D br y ⊆ {ub} := fun y hy u hu => by
    obtain ⟨huR, hyu⟩ := mem_ru.1 hu
    rw [hR', Finset.mem_insert, Finset.mem_singleton] at huR
    rcases huR with rfl | rfl
    · exact absurd (hp10 y hyu) hy
    · exact Finset.mem_singleton_self _
  have hle3 : ∀ y : Fin 14, y ≠ 10 → (sem_W 14 D y).card ≤ 3 := fun y hy => by
    have h1 := cc_le h hD br hbr y
    have h2 := Finset.card_le_card (hru_sub_ub y hy)
    rw [Finset.card_singleton] at h2; omega
  have hru_eq_ub : ∀ y : Fin 14, y ≠ 10 → 3 ≤ (sem_W 14 D y).card → ru D br y = {ub} := fun y hy h3 => by
    have h1 := cc_le h hD br hbr y
    exact Finset.eq_of_subset_of_card_le (hru_sub_ub y hy) (by rw [Finset.card_singleton]; omega)

  have hget_PQ : ∀ (y1 y2 : Fin 14), y1 ≠ 10 → y2 ≠ 10 →
      3 ≤ (sem_W 14 D y1).card → 3 ≤ (sem_W 14 D y2).card →
      ∃ P Q : ℕ × Bool, P ≠ Q ∧ P ∈ sem_W 14 D y1 ∧ Q ∈ sem_W 14 D y1 ∧
        P ∈ sem_W 14 D y2 ∧ Q ∈ sem_W 14 D y2 := by
    intro y1 y2 hy1 hy2 h1 h2
    have hru1 := hru_eq_ub y1 hy1 h1
    have hru2 := hru_eq_ub y2 hy2 h2
    obtain ⟨P, Q, hPQ, hall⟩ := ru_one_two_common h hD br hbm hru1 h1
    have hy1m : y1 ∈ supp 14 D ub.1 := (mem_ru.1 (by rw [hru1]; exact Finset.mem_singleton_self _)).2
    have hy2m : y2 ∈ supp 14 D ub.1 := (mem_ru.1 (by rw [hru2]; exact Finset.mem_singleton_self _)).2
    obtain ⟨hP1, hQ1⟩ := hall y1 hy1m hru1 h1
    obtain ⟨hP2, hQ2⟩ := hall y2 hy2m hru2 h2
    exact ⟨P, Q, hPQ, hP1, hQ1, hP2, hQ2⟩

  have hnot33_adj : ∀ (x y ix iy : Fin 14), x ≠ 10 → y ≠ 10 →
      ix ∈ ineligSet 14 D → iy ∈ ineligSet 14 D → x ∉ ineligSet 14 D → y ∉ ineligSet 14 D →
      (ix ≠ iy ∧ hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB x y = true ∧ hc_adjB ix y = false) →
      3 ≤ (sem_W 14 D x).card → 3 ≤ (sem_W 14 D y).card → False := by
    intro x y ix iy hx10 hy10 hix hiy hnx hny hg hsx hsy
    obtain ⟨P, Q, hPQ, hPx, hQx, hPy, hQy⟩ := hget_PQ x y hx10 hy10 hsx hsy
    obtain ⟨hxyi, g1, g2, g3, g4⟩ := hg
    rw [hc_adjB_iff] at g1 g2 g3
    obtain ⟨e, hex, hey, hfy, hfx⟩ := pa_ed h hD hpos g3
    have heP : e ≠ P := fun hh => w_bar h.1 (hh ▸ hPy) hey
    have heQ : e ≠ Q := fun hh => w_bar h.1 (hh ▸ hQy) hey
    have hbeP : sem_bar e ≠ P := fun hh => w_bar h.1 hPx (by rw [← hh, sem_bar_bar]; exact hex)
    have hbeQ : sem_bar e ≠ Q := fun hh => w_bar h.1 hQx (by rw [← hh, sem_bar_bar]; exact hex)
    have hpx := as_mem hpos hix g1
    have hpy := as_mem hpos hiy g2
    have hpxe : pos ix ≠ e := fun hh => hny (hfy ix hix hh.symm ▸ hix)
    have hpybe : pos iy ≠ sem_bar e := fun hh => hnx (hfx iy hiy hh.symm ▸ hiy)
    have hpxy : pos ix ∈ sem_W 14 D y := by
      rcases pa_three hPx hQx hex hPQ heP.symm heQ.symm (hle3 x hx10) (pos ix) hpx with heq | heq | heq
      · exact heq ▸ hPy
      · exact heq ▸ hQy
      · exact absurd heq hpxe
    have hpyx : pos iy ∈ sem_W 14 D x := by
      rcases pa_three hPy hQy hey hPQ hbeP.symm hbeQ.symm (hle3 y hy10) (pos iy) hpy with heq | heq | heq
      · exact heq ▸ hPx
      · exact heq ▸ hQx
      · exact absurd heq hpybe
    have hpxpy : pos ix ≠ pos iy := fun hh => hxyi (hpos.2 ix hix iy hiy hh)
    have hpye : pos iy ≠ e := fun hh => hny (hfy iy hiy hh.symm ▸ hiy)
    have hWx := pa_three hpx hpyx hex hpxpy hpxe hpye (hle3 x hx10)
    have hfull := full_g14 h hD hB0 hpos hix g1 (fun p hp hne1 hsub => by
      rcases hWx p hp with rfl | rfl | rfl
      · exact hne1 rfl
      · exact hxyi.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hiy)))
      · exact hny (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hey).2.1) ▸ hix))
    exact sem_adjB_false.1 g4 ((hfull y).1 (sem_mem_W.1 hpxy).2.1)

  have hkill_diff_ub : ∀ (x y ix iy vx qx qy : Fin 14), x ≠ 10 → y ≠ 10 →
      ix ∈ ineligSet 14 D → iy ∈ ineligSet 14 D → vx ∉ ineligSet 14 D →
      (x ≠ y ∧ ix ≠ iy ∧ (g14_nbB x).card = 3 ∧ (g14_nbB y).card = 3 ∧
       hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB ix y = false ∧
       hc_adjB x vx = true ∧ hc_adjB ix qx = true ∧ qx ≠ x ∧ hc_adjB y qx = false ∧
       hc_adjB iy qy = true ∧ qy ≠ y ∧ hc_adjB x qy = false) →
      3 ≤ (sem_W 14 D x).card → 3 ≤ (sem_W 14 D y).card → False := by
    intro x y ix iy vx qx qy hx10 hy10 hix hiy hvx hg hx3 hy3
    obtain ⟨P, Q, hPQ, hPx, hQx, hPy, hQy⟩ := hget_PQ x y hx10 hy10 hx3 hy3
    obtain ⟨hxy, hixy, hdx, hdy, g1, g2, g3, g4, g5, hqxx, g6, g7, hqyy, g8⟩ := hg
    have hpx := as_mem hpos hix ((hc_adjB_iff _ _).1 g1)
    have hpy := as_mem hpos hiy ((hc_adjB_iff _ _).1 g2)
    by_cases hpxy : pos ix ∈ sem_W 14 D y
    · by_cases hpyx : pos iy ∈ sem_W 14 D x
      · obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 g4)
        have hpxpy : pos ix ≠ pos iy := fun e => hixy (hpos.2 _ hix _ hiy e)
        have hpxe : pos ix ≠ ev := fun e => hvx (hfv _ hix e.symm ▸ hix)
        have hpye : pos iy ≠ ev := fun e => hvx (hfv _ hiy e.symm ▸ hiy)
        have hWx := pa_three hpx hpyx hev hpxpy hpxe hpye (hle3 x hx10)
        have hfull := full_g14 h hD hB0 hpos hix ((hc_adjB_iff _ _).1 g1) (fun p hp hne1 hsub => by
          rcases hWx p hp with rfl | rfl | rfl
          · exact hne1 rfl
          · exact hixy.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hiy)))
          · exact hvx (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1) ▸ hix))
        exact sem_adjB_false.1 g3 ((hfull y).1 (sem_mem_W.1 hpxy).2.1)
      · have hPne : P ≠ pos iy := fun e => hpyx (e ▸ hPx)
        have hQne : Q ≠ pos iy := fun e => hpyx (e ▸ hQx)
        obtain ⟨e, he, hnx, hnq⟩ := g14_deg3_cover_free h hD hdy hxy.symm hqyy.symm (sem_adjB_false.1 g8)
        rcases pa_three hPy hQy hpy hPQ hPne hQne (hle3 y hy10) e he with rfl | rfl | rfl
        · exact hnx (sem_mem_W.1 hPx).2.1
        · exact hnx (sem_mem_W.1 hQx).2.1
        · exact hnq ((hpos.1 iy hiy).2.2.1 qy ((hc_adjB_iff _ _).1 g7))
    · have hPne : P ≠ pos ix := fun e => hpxy (e ▸ hPy)
      have hQne : Q ≠ pos ix := fun e => hpxy (e ▸ hQy)
      obtain ⟨e, he, hny, hnq⟩ := g14_deg3_cover_free h hD hdx hxy hqxx.symm (sem_adjB_false.1 g6)
      rcases pa_three hPx hQx hpx hPQ hPne hQne (hle3 x hx10) e he with rfl | rfl | rfl
      · exact hny (sem_mem_W.1 hPy).2.1
      · exact hny (sem_mem_W.1 hQy).2.1
      · exact hnq ((hpos.1 ix hix).2.2.1 qx ((hc_adjB_iff _ _).1 g5))
  have h1_3 : 3 ≤ (sem_W 14 D 1).card := by
    by_contra hc
    have h9_3 : 3 ≤ (sem_W 14 D 9).card := by
      by_contra hc1; exact pa_m1 h hD hpos 1 9 13 7 5 h7 h5 hn1 hn9 hn13 (by decide) (by omega) (by omega)
    have h13_3 : 3 ≤ (sem_W 14 D 13).card := by
      by_contra hc1; exact pa_m1 h hD hpos 1 13 9 7 4 h7 h4 hn1 hn13 hn9 (by decide) (by omega) (by omega)
    exact hkill_diff_ub 9 13 5 4 6 10 10 (by decide) (by decide) h5 h4 hn6 (by decide) h9_3 h13_3
  have h3_3 : 3 ≤ (sem_W 14 D 3).card := by
    by_contra hc
    have h11_3 : 3 ≤ (sem_W 14 D 11).card := by
      by_contra hc1; exact pa_m1 h hD hpos 3 11 12 7 4 h7 h4 hn3 hn11 hn12 (by decide) (by omega) (by omega)
    have h12_3 : 3 ≤ (sem_W 14 D 12).card := by
      by_contra hc1; exact pa_m1 h hD hpos 3 12 11 7 5 h7 h5 hn3 hn12 hn11 (by decide) (by omega) (by omega)
    exact hkill_diff_ub 11 12 4 5 6 10 10 (by decide) (by decide) h4 h5 hn6 (by decide) h11_3 h12_3
  have l9 : (sem_W 14 D 9).card ≤ 2 := by
    by_contra hc; exact hnot33_adj 1 9 7 5 (by decide) (by decide) h7 h5 hn1 hn9 (by decide) h1_3 (by omega)
  have l13 : (sem_W 14 D 13).card ≤ 2 := by
    by_contra hc; exact hnot33_adj 1 13 7 4 (by decide) (by decide) h7 h4 hn1 hn13 (by decide) h1_3 (by omega)
  have l11 : (sem_W 14 D 11).card ≤ 2 := by
    by_contra hc; exact hnot33_adj 3 11 7 4 (by decide) (by decide) h7 h4 hn3 hn11 (by decide) h3_3 (by omega)
  have l12 : (sem_W 14 D 12).card ≤ 2 := by
    by_contra hc; exact hnot33_adj 3 12 7 5 (by decide) (by decide) h7 h5 hn3 hn12 (by decide) h3_3 (by omega)
  obtain ⟨D9, -, hW9, hp9⟩ := ps_side h hD hpos h5 (by decide : Adj 5 9) (by decide) l9
  obtain ⟨D13, -, hW13, hp13⟩ := ps_side h hD hpos h4 (by decide : Adj 4 13) (by decide) l13
  obtain ⟨D11, -, hW11, hp11⟩ := ps_side h hD hpos h4 (by decide : Adj 4 11) (by decide) l11
  obtain ⟨D12, -, hW12, hp12⟩ := ps_side h hD hpos h5 (by decide : Adj 5 12) (by decide) l12
  obtain ⟨e19, h19_1, h19_9, hf9, hf19'⟩ := pa_ed h hD hpos (by decide : Adj 1 9)
  obtain ⟨e113, h113_1, h113_13, hf13, hf113'⟩ := pa_ed h hD hpos (by decide : Adj 1 13)
  obtain ⟨e311, h311_3, h311_11, hf11, hf311'⟩ := pa_ed h hD hpos (by decide : Adj 3 11)
  obtain ⟨e312, h312_3, h312_12, hf12, hf312'⟩ := pa_ed h hD hpos (by decide : Adj 3 12)
  rw [hW9, Finset.mem_insert, Finset.mem_singleton] at h19_9
  have hb9 : sem_bar e19 = D9 := h19_9.resolve_left (fun hh => hn1 (hf19' 5 h5 hh ▸ h5))
  rw [hW13, Finset.mem_insert, Finset.mem_singleton] at h113_13
  have hb13 : sem_bar e113 = D13 := h113_13.resolve_left (fun hh => hn1 (hf113' 4 h4 hh ▸ h4))
  rw [hW11, Finset.mem_insert, Finset.mem_singleton] at h311_11
  have hb11 : sem_bar e311 = D11 := h311_11.resolve_left (fun hh => hn3 (hf311' 4 h4 hh ▸ h4))
  rw [hW12, Finset.mem_insert, Finset.mem_singleton] at h312_12
  have hb12 : sem_bar e312 = D12 := h312_12.resolve_left (fun hh => hn3 (hf312' 5 h5 hh ▸ h5))
  have hD9_in : D9 ∈ sem_W 14 D 9 := by rw [hW9]; simp
  have hD13_in : D13 ∈ sem_W 14 D 13 := by rw [hW13]; simp
  have hD11_in : D11 ∈ sem_W 14 D 11 := by rw [hW11]; simp
  have hD12_in : D12 ∈ sem_W 14 D 12 := by rw [hW12]; simp
  have hp7_1 := as_mem hpos h7 (by decide : Adj 7 1)
  have hp7_3 := as_mem hpos h7 (by decide : Adj 7 3)
  have h1_913 : e19 ≠ e113 := fun hh => hp9 13 (by decide) (by decide) (by rw [← hb9, hh, hb13]; exact hD13_in)
  have h1_9p : e19 ≠ pos 7 := fun hh => hn9 (hf9 7 h7 hh ▸ h7)
  have h1_13p : e113 ≠ pos 7 := fun hh => hn13 (hf13 7 h7 hh ▸ h7)
  have h3_1112 : e311 ≠ e312 := fun hh => hp11 12 (by decide) (by decide) (by rw [← hb11, hh, hb12]; exact hD12_in)
  have h3_11p : e311 ≠ pos 7 := fun hh => hn11 (hf11 7 h7 hh ▸ h7)
  have h3_12p : e312 ≠ pos 7 := fun hh => hn12 (hf12 7 h7 hh ▸ h7)
  obtain ⟨P, Q, hPQ, hP1, hQ1, hP3, hQ3⟩ := hget_PQ 1 3 (by decide) (by decide) h1_3 h3_3
  have hkill_e : ∀ e, e ∈ sem_W 14 D 1 → e ∈ sem_W 14 D 3 → e = pos 7 := by
    intro e he1 he3
    rcases pa_three h19_1 h113_1 hp7_1 h1_913 h1_9p h1_13p (hle3 1 (by decide)) e he1 with heq | heq | heq
    · rw [heq] at he3
      rcases pa_three h311_3 h312_3 hp7_3 h3_1112 h3_11p h3_12p (hle3 3 (by decide)) e19 he3 with hh | hh | hh
      · exact absurd (by rw [← hb9, hh, hb11]; exact hD11_in) (hp9 11 (by decide) (by decide))
      · exact absurd (by rw [← hb9, hh, hb12]; exact hD12_in) (hp9 12 (by decide) (by decide))
      · exact absurd hh h1_9p
    · rw [heq] at he3
      rcases pa_three h311_3 h312_3 hp7_3 h3_1112 h3_11p h3_12p (hle3 3 (by decide)) e113 he3 with hh | hh | hh
      · exact absurd (by rw [← hb13, hh, hb11]; exact hD11_in) (hp13 11 (by decide) (by decide))
      · exact absurd (by rw [← hb13, hh, hb12]; exact hD12_in) (hp13 12 (by decide) (by decide))
      · exact absurd hh h1_13p
    · exact heq
  exact hPQ ((hkill_e P hP1 hP3).trans (hkill_e Q hQ1 hQ3).symm)

theorem full_of_le2 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos) {i x y : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hy : y ∉ ineligSet 14 D) (hix : Adj i x) (hxy : Adj x y)
    (hle2 : (sem_W 14 D x).card ≤ 2) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) → Adj i t := by
  have hpi := as_mem hpos hi hix
  obtain ⟨e, he, hbe, hfy, -⟩ := pa_ed h hD hpos hxy
  have hne : pos i ≠ e := fun hh => hy (hfy i hi hh.symm ▸ hi)
  have hfull := full_g14 h hD hB0 hpos hi hix (fun p hp hne1 hsub => by
    rcases pa_two hpi he hne hle2 p hp with rfl | rfl
    · exact hne1 rfl
    · exact hy (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hi))
  exact fun t ht => (hfull t).1 ht

theorem elim_40_44_both_le2 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (br : Fin 14 → ℕ) (hbm : sem_MinBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos 14 G14 D pos)
    {u1 u2 : Σ _ : ℕ, ℕ} (hu12 : u1 ≠ u2) (hReq : residualUnits 14 D br = {u1, u2})
    (h4 : (4 : Fin 14) ∈ ineligSet 14 D) (h5 : (5 : Fin 14) ∈ ineligSet 14 D) (h7 : (7 : Fin 14) ∈ ineligSet 14 D)
    (hn1 : (1 : Fin 14) ∉ ineligSet 14 D) (hn2 : (2 : Fin 14) ∉ ineligSet 14 D)
    (hn3 : (3 : Fin 14) ∉ ineligSet 14 D) (hn6 : (6 : Fin 14) ∉ ineligSet 14 D)
    (hn9 : (9 : Fin 14) ∉ ineligSet 14 D) (hn11 : (11 : Fin 14) ∉ ineligSet 14 D)
    (hn12 : (12 : Fin 14) ∉ ineligSet 14 D) (hn13 : (13 : Fin 14) ∉ ineligSet 14 D)
    (l1 : (sem_W 14 D 1).card ≤ 2) (l3 : (sem_W 14 D 3).card ≤ 2) : False := by
  have hbr := sem_minBranch_pure hbm
  have helig : ∀ v : Fin 14, v ∉ ineligSet 14 D → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (sem_mem_inelig.2 hc)
  obtain ⟨Z1, -, hW1, hp1⟩ := ps_side h hD hpos h7 (by decide : Adj 7 1) (by decide) l1
  obtain ⟨Z3, -, hW3, hp3⟩ := ps_side h hD hpos h7 (by decide : Adj 7 3) (by decide) l3
  obtain ⟨e91, h91_9, h91_1, hf1_9, hf9'⟩ := pa_ed h hD hpos (by decide : Adj 9 1)
  obtain ⟨e96, h96_9, h96_6, hf6_9, -⟩ := pa_ed h hD hpos (by decide : Adj 9 6)
  obtain ⟨e131, h131_13, h131_1, hf1_13, hf13'⟩ := pa_ed h hD hpos (by decide : Adj 13 1)
  obtain ⟨e132, h132_13, h132_2, hf2_13, -⟩ := pa_ed h hD hpos (by decide : Adj 13 2)
  obtain ⟨e113, h113_11, h113_3, hf3_11, hf11'⟩ := pa_ed h hD hpos (by decide : Adj 11 3)
  obtain ⟨e116, h116_11, h116_6, hf6_11, -⟩ := pa_ed h hD hpos (by decide : Adj 11 6)
  obtain ⟨e123, h123_12, h123_3, hf3_12, hf12'⟩ := pa_ed h hD hpos (by decide : Adj 12 3)
  obtain ⟨e122, h122_12, h122_2, hf2_12, -⟩ := pa_ed h hD hpos (by decide : Adj 12 2)
  have h91_1' := h91_1; have h131_1' := h131_1
  rw [hW1, Finset.mem_insert, Finset.mem_singleton] at h91_1' h131_1'
  have hb91 : sem_bar e91 = Z1 := h91_1'.resolve_left (fun hh => hn9 (hf9' 7 h7 hh ▸ h7))
  have hb131 : sem_bar e131 = Z1 := h131_1'.resolve_left (fun hh => hn13 (hf13' 7 h7 hh ▸ h7))
  have he131_eq : e131 = e91 := by rw [← sem_bar_bar e131, ← sem_bar_bar e91, hb131, hb91]
  have h113_3' := h113_3; have h123_3' := h123_3
  rw [hW3, Finset.mem_insert, Finset.mem_singleton] at h113_3' h123_3'
  have hb113 : sem_bar e113 = Z3 := h113_3'.resolve_left (fun hh => hn11 (hf11' 7 h7 hh ▸ h7))
  have hb123 : sem_bar e123 = Z3 := h123_3'.resolve_left (fun hh => hn12 (hf12' 7 h7 hh ▸ h7))
  have hp5_9 := as_mem hpos h5 (by decide : Adj 5 9)
  have hp5_12 := as_mem hpos h5 (by decide : Adj 5 12)
  have hp4_11 := as_mem hpos h4 (by decide : Adj 4 11)
  have hp4_13 := as_mem hpos h4 (by decide : Adj 4 13)
  have hZ1_in : Z1 ∈ sem_W 14 D 1 := by rw [hW1]; simp
  have hZ3_in : Z3 ∈ sem_W 14 D 3 := by rw [hW3]; simp

  have h9_12 : pos 5 ≠ e91 := fun hh => hn1 (hf1_9 5 h5 hh.symm ▸ h5)
  have h9_13 : pos 5 ≠ e96 := fun hh => hn6 (hf6_9 5 h5 hh.symm ▸ h5)
  have h9_23 : e91 ≠ e96 := fun hh => hp1 6 (by decide) (by decide) (by rw [← hb91, hh]; exact h96_6)
  have h11_12 : pos 4 ≠ e113 := fun hh => hn3 (hf3_11 4 h4 hh.symm ▸ h4)
  have h11_13 : pos 4 ≠ e116 := fun hh => hn6 (hf6_11 4 h4 hh.symm ▸ h4)
  have h11_23 : e113 ≠ e116 := fun hh => hp3 6 (by decide) (by decide) (by rw [← hb113, hh]; exact h116_6)
  have h12_12 : pos 5 ≠ e123 := fun hh => hn3 (hf3_12 5 h5 hh.symm ▸ h5)
  have h12_13 : pos 5 ≠ e122 := fun hh => hn2 (hf2_12 5 h5 hh.symm ▸ h5)
  have h12_23 : e123 ≠ e122 := fun hh => hp3 2 (by decide) (by decide) (by rw [← hb123, hh]; exact h122_2)
  have h13_12 : pos 4 ≠ e131 := fun hh => hn1 (hf1_13 4 h4 hh.symm ▸ h4)
  have h13_13 : pos 4 ≠ e132 := fun hh => hn2 (hf2_13 4 h4 hh.symm ▸ h4)
  have h13_23 : e131 ≠ e132 := fun hh => hp1 2 (by decide) (by decide) (by rw [← hb131, hh]; exact h132_2)
  have h9_3 : 3 ≤ (sem_W 14 D 9).card := pa_card3 hp5_9 h91_9 h96_9 h9_12 h9_13 h9_23
  have h11_3 : 3 ≤ (sem_W 14 D 11).card := pa_card3 hp4_11 h113_11 h116_11 h11_12 h11_13 h11_23
  have h12_3 : 3 ≤ (sem_W 14 D 12).card := pa_card3 hp5_12 h123_12 h122_12 h12_12 h12_13 h12_23
  have h13_3 : 3 ≤ (sem_W 14 D 13).card := pa_card3 hp4_13 h131_13 h132_13 h13_12 h13_13 h13_23
  have hne9 : (ru D br 9).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 9; omega)
  have hne11 : (ru D br 11).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 11; omega)
  have hne12 : (ru D br 12).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 12; omega)
  have hne13 : (ru D br 13).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 13; omega)

  have hkill_cross : ∀ (v t iv it nv1 nv2 nt1 nt2 : Fin 14) (ev1 ev2 et1 et2 : ℕ × Bool),
      iv ∈ ineligSet 14 D → it ∈ ineligSet 14 D →
      v ∉ ineligSet 14 D → t ∉ ineligSet 14 D →
      nv1 ∉ ineligSet 14 D → nv2 ∉ ineligSet 14 D → nt1 ∉ ineligSet 14 D → nt2 ∉ ineligSet 14 D →
      (v ≠ t ∧ iv ≠ it ∧ (g14_nbB v).card = 3 ∧ (g14_nbB t).card = 3 ∧
       hc_adjB iv v = true ∧ hc_adjB it t = true ∧ hc_adjB iv t = false ∧ hc_adjB it v = false ∧
       hc_adjB iv 10 = true ∧ v ≠ 10 ∧ hc_adjB t 10 = false ∧
       hc_adjB it 10 = true ∧ t ≠ 10 ∧ hc_adjB v 10 = false) →
      (ev1 ∈ sem_W 14 D v ∧ ev2 ∈ sem_W 14 D v ∧
       sem_bar ev1 ∈ sem_W 14 D nv1 ∧ sem_bar ev2 ∈ sem_W 14 D nv2 ∧
       pos iv ≠ ev1 ∧ pos iv ≠ ev2 ∧ ev1 ≠ ev2) →
      (et1 ∈ sem_W 14 D t ∧ et2 ∈ sem_W 14 D t ∧
       sem_bar et1 ∈ sem_W 14 D nt1 ∧ sem_bar et2 ∈ sem_W 14 D nt2 ∧
       pos it ≠ et1 ∧ pos it ≠ et2 ∧ et1 ≠ et2 ∧ pos iv ≠ et1 ∧ pos iv ≠ et2) →
      (ru D br v).Nonempty → ru D br v ⊆ ru D br t → False := by
    intro v t iv it nv1 nv2 nt1 nt2 ev1 ev2 et1 et2 hiv hit hnv hnt hnv1 hnv2 hnt1 hnt2 hg hvs hts hne hsub
    obtain ⟨hvt, hivit, hdv, hdt, giv, git, gnivt, gnitv, giv10, hv10, gnt10, git10, ht10, gnv10⟩ := hg
    obtain ⟨u, hu⟩ := hne
    have hres : ∀ u' ∈ residualUnits 14 D br, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
      fun u' hu' hv' => (mem_ru.1 (hsub (mem_ru.2 ⟨hu', hv'⟩))).2
    have hw : v ∈ supp 14 D u.1 ∧ t ∈ supp 14 D u.1 := ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub hu)).2⟩
    have htv := pe_co_g14 h hD br hbr hpos hiv (helig v hnv) hres hw ⟨hdv, giv, giv10, hvt, hv10, gnt10⟩
    have hcardv : (ru D br v).card ≤ 2 := by
      have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br v ⊆ {u1, u2})
      rw [Finset.card_pair hu12] at this; exact this
    have hcardt : (ru D br t).card ≤ 2 := by
      have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br t ⊆ {u1, u2})
      rw [Finset.card_pair hu12] at this; exact this
    have hposv : 0 < (ru D br v).card := Finset.card_pos.2 ⟨u, hu⟩
    by_cases hv1 : (ru D br v).card = 1
    · have hWv3 : (sem_W 14 D v).card ≤ 3 := by have := cc_le h hD br hbr v; omega
      have hWv := pa_three (as_mem hpos hiv ((hc_adjB_iff _ _).1 giv)) hvs.1 hvs.2.1
        hvs.2.2.2.2.1 hvs.2.2.2.2.2.1 hvs.2.2.2.2.2.2 hWv3
      have hfull := full_g14 h hD hB0 hpos hiv ((hc_adjB_iff _ _).1 giv) (fun p hp hne1 hsub' => by
        rcases hWv p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hnv1 (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hvs.2.2.1).2.1) ▸ hiv)
        · exact hnv2 (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hvs.2.2.2.1).2.1) ▸ hiv))
      exact sem_adjB_false.1 gnivt ((hfull t).1 htv)
    · have heq : ru D br v = ru D br t := Finset.eq_of_subset_of_card_le hsub (by omega)
      have hres2 : ∀ u' ∈ residualUnits 14 D br, t ∈ supp 14 D u'.1 → v ∈ supp 14 D u'.1 :=
        fun u' hu' ht' => (mem_ru.1 (by rw [heq]; exact mem_ru.2 ⟨hu', ht'⟩)).2
      have hvt' := pe_co_g14 h hD br hbr hpos hit (helig t hnt) hres2 ⟨hw.2, hw.1⟩ ⟨hdt, git, git10, hvt.symm, ht10, gnv10⟩
      have hWt4 : (sem_W 14 D t).card ≤ 4 := by have := cc_le h hD br hbr t; omega
      have hWt := pa_four (as_mem hpos hit ((hc_adjB_iff _ _).1 git)) (mem_W_of_pos hpos hiv htv) hts.1 hts.2.1
        (fun e => hivit.symm (hpos.2 _ hit _ hiv e)) hts.2.2.2.2.1 hts.2.2.2.2.2.1
        hts.2.2.2.2.2.2.2.1 hts.2.2.2.2.2.2.2.2 hts.2.2.2.2.2.2.1 hWt4
      have hfull := full_g14 h hD hB0 hpos hit ((hc_adjB_iff _ _).1 git) (fun p hp hne1 hsub' => by
        rcases hWt p hp with rfl | rfl | rfl | rfl
        · exact hne1 rfl
        · exact hivit (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hiv)))
        · exact hnt1 (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hts.2.2.1).2.1) ▸ hit)
        · exact hnt2 (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hts.2.2.2.1).2.1) ▸ hit))
      exact sem_adjB_false.1 gnitv ((hfull v).1 hvt')
  have hno_9_11 : ¬ ru D br 9 ⊆ ru D br 11 := hkill_cross 9 11 5 4 1 6 3 6 e91 e96 e113 e116
    h5 h4 hn9 hn11 hn1 hn6 hn3 hn6 (by decide)
    ⟨h91_9, h96_9, h91_1, h96_6, h9_12, h9_13, h9_23⟩
    ⟨h113_11, h116_11, h113_3, h116_6, h11_12, h11_13, h11_23, fun hh => hn3 (hf3_11 5 h5 hh.symm ▸ h5), fun hh => hn6 (hf6_11 5 h5 hh.symm ▸ h5)⟩ hne9
  have hno_11_9 : ¬ ru D br 11 ⊆ ru D br 9 := hkill_cross 11 9 4 5 3 6 1 6 e113 e116 e91 e96
    h4 h5 hn11 hn9 hn3 hn6 hn1 hn6 (by decide)
    ⟨h113_11, h116_11, h113_3, h116_6, h11_12, h11_13, h11_23⟩
    ⟨h91_9, h96_9, h91_1, h96_6, h9_12, h9_13, h9_23, fun hh => hn1 (hf1_9 4 h4 hh.symm ▸ h4), fun hh => hn6 (hf6_9 4 h4 hh.symm ▸ h4)⟩ hne11
  have hno_12_11 : ¬ ru D br 12 ⊆ ru D br 11 := hkill_cross 12 11 5 4 3 2 3 6 e123 e122 e113 e116
    h5 h4 hn12 hn11 hn3 hn2 hn3 hn6 (by decide)
    ⟨h123_12, h122_12, h123_3, h122_2, h12_12, h12_13, h12_23⟩
    ⟨h113_11, h116_11, h113_3, h116_6, h11_12, h11_13, h11_23, fun hh => hn3 (hf3_11 5 h5 hh.symm ▸ h5), fun hh => hn6 (hf6_11 5 h5 hh.symm ▸ h5)⟩ hne12
  have hno_11_12 : ¬ ru D br 11 ⊆ ru D br 12 := hkill_cross 11 12 4 5 3 6 3 2 e113 e116 e123 e122
    h4 h5 hn11 hn12 hn3 hn6 hn3 hn2 (by decide)
    ⟨h113_11, h116_11, h113_3, h116_6, h11_12, h11_13, h11_23⟩
    ⟨h123_12, h122_12, h123_3, h122_2, h12_12, h12_13, h12_23, fun hh => hn3 (hf3_12 4 h4 hh.symm ▸ h4), fun hh => hn2 (hf2_12 4 h4 hh.symm ▸ h4)⟩ hne11

  have hsame912 : ∃ ua, ru D br 9 = {ua} ∧ ru D br 12 = {ua} := by
    rcases finset_pair_incomp hu12 (hReq ▸ Finset.filter_subset _ _) (hReq ▸ Finset.filter_subset _ _)
        hne9 hne11 hno_9_11 hno_11_9 with ⟨h9, h11⟩ | ⟨h9, h11⟩
    · rcases finset_pair_incomp hu12 (hReq ▸ Finset.filter_subset _ _) (hReq ▸ Finset.filter_subset _ _)
          hne12 hne11 hno_12_11 hno_11_12 with ⟨h12', _⟩ | ⟨_, hbad⟩
      · exact ⟨u1, h9, h12'⟩
      · exact absurd (Finset.singleton_injective (h11.symm.trans hbad)) hu12.symm
    · rcases finset_pair_incomp hu12 (hReq ▸ Finset.filter_subset _ _) (hReq ▸ Finset.filter_subset _ _)
          hne12 hne11 hno_12_11 hno_11_12 with ⟨_, hbad⟩ | ⟨h12', _⟩
      · exact absurd (Finset.singleton_injective (h11.symm.trans hbad)) hu12
      · exact ⟨u2, h9, h12'⟩
  obtain ⟨ua, hru9, hru12⟩ := hsame912
  have h9le3 : (sem_W 14 D 9).card ≤ 3 := by have := cc_le h hD br hbr 9; rw [hru9, Finset.card_singleton] at this; omega
  have h12le3 : (sem_W 14 D 12).card ≤ 3 := by have := cc_le h hD br hbr 12; rw [hru12, Finset.card_singleton] at this; omega
  obtain ⟨P, Q, hPQ, hall⟩ := ru_one_two_common h hD br hbm hru9 h9_3
  have h9ua : 9 ∈ supp 14 D ua.1 := (mem_ru.1 (by rw [hru9]; exact Finset.mem_singleton_self _)).2
  have h12ua : 12 ∈ supp 14 D ua.1 := (mem_ru.1 (by rw [hru12]; exact Finset.mem_singleton_self _)).2
  obtain ⟨hP9, hQ9⟩ := hall 9 h9ua hru9 h9_3
  obtain ⟨hP12, hQ12⟩ := hall 12 h12ua hru12 h12_3

  have he91_not12 : e91 ∉ sem_W 14 D 12 := by
    intro hm
    rcases pa_three hp5_12 h123_12 h122_12 h12_12 h12_13 h12_23 h12le3 e91 hm with hh | hh | hh
    · exact h9_12 hh.symm
    · exact hp1 3 (by decide) (by decide) (by rw [← hb91, hh, hb123]; exact hZ3_in)
    · exact hp1 2 (by decide) (by decide) (by rw [← hb91, hh]; exact h122_2)
  have hPne : P ≠ e91 := fun hh => he91_not12 (hh ▸ hP12)
  have hQne : Q ≠ e91 := fun hh => he91_not12 (hh ▸ hQ12)

  obtain ⟨e, he, hn12e, hn13e⟩ := g14_deg3_cover_free h hD (by decide : (g14_nbB 9).card = 3)
    (by decide : (9 : Fin 14) ≠ 12) (by decide : (9 : Fin 14) ≠ 13) (by decide : ¬ Adj 12 13)
  rcases pa_three hP9 hQ9 h91_9 hPQ hPne hQne h9le3 e he with rfl | rfl | rfl
  · exact hn12e (sem_mem_W.1 hP12).2.1
  · exact hn12e (sem_mem_W.1 hQ12).2.1
  · exact hn13e (sem_mem_W.1 (he131_eq ▸ h131_13)).2.1

theorem elim_40 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨40, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {0, 4, 5, 7} := by rw [hI]; decide
  rw [hIeq, show ({0, 4, 5, 7} : Finset (Fin 14)).card = 4 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨40, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨40, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g14_gr h.1 (sem_g14_comp hD)
  have hbr := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
  have hm : ∀ v : Fin 14, v ∈ ({0, 4, 5, 7} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({0, 4, 5, 7} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 14, v ∉ ({0, 4, 5, 7} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  have h10_3 := two_in_deg3 h hD hpos (u := 10) (v := 0) (hm 4 (by decide)) (hm 5 (by decide)) (by decide)
  have hne10 : (ru D br 10).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 10; omega)
  have hsub10 : ru D br 10 ⊆ {u1, u2} := hReq ▸ Finset.filter_subset _ _
  by_cases hu1m : u1 ∈ ru D br 10 <;> by_cases hu2m : u2 ∈ ru D br 10
  · have hru10_eq : ru D br 10 = {u1, u2} := by
      refine Finset.Subset.antisymm hsub10 (fun u hu => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    by_cases h13 : (sem_W 14 D 1).card ≤ 2 ∧ (sem_W 14 D 3).card ≤ 2
    · exact elim_40_44_both_le2 h hD hB0 br hbm hpos hu12 hReq
        (hm 4 (by decide)) (hm 5 (by decide)) (hm 7 (by decide))
        (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 6 (by decide))
        (hn 9 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) h13.1 h13.2
    ·
      have hp7_10 : pos 7 ∈ sem_W 14 D 10 := by
        by_cases l1 : (sem_W 14 D 1).card ≤ 2
        · have h3_3 : 3 ≤ (sem_W 14 D 3).card := by omega
          obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 3; omega : 0 < (ru D br 3).card)
          have hsub3 : ru D br 3 ⊆ ru D br 10 := by rw [hru10_eq, ← hReq]; exact Finset.filter_subset _ _
          have hres : ∀ u' ∈ residualUnits 14 D br, (3 : Fin 14) ∈ supp 14 D u'.1 → 10 ∈ supp 14 D u'.1 :=
            fun u' hu' h3' => (mem_ru.1 (hsub3 (mem_ru.2 ⟨hu', h3'⟩))).2
          exact mem_W_of_pos hpos (hm 7 (by decide)) (pe_co_g14 h hD br hbr hpos (hm 7 (by decide)) (helig 3 (by decide))
            hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub3 hu)).2⟩ (by decide : (g14_nbB 3).card = 3 ∧ hc_adjB 7 3 = true ∧ hc_adjB 7 1 = true ∧ (3 : Fin 14) ≠ 10 ∧ (3 : Fin 14) ≠ 1 ∧ hc_adjB 10 1 = false))
        · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 1; omega : 0 < (ru D br 1).card)
          have hsub1 : ru D br 1 ⊆ ru D br 10 := by rw [hru10_eq, ← hReq]; exact Finset.filter_subset _ _
          have hres : ∀ u' ∈ residualUnits 14 D br, (1 : Fin 14) ∈ supp 14 D u'.1 → 10 ∈ supp 14 D u'.1 :=
            fun u' hu' h1' => (mem_ru.1 (hsub1 (mem_ru.2 ⟨hu', h1'⟩))).2
          exact mem_W_of_pos hpos (hm 7 (by decide)) (pe_co_g14 h hD br hbr hpos (hm 7 (by decide)) (helig 1 (by decide))
            hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub1 hu)).2⟩ (by decide : (g14_nbB 1).card = 3 ∧ hc_adjB 7 1 = true ∧ hc_adjB 7 3 = true ∧ (1 : Fin 14) ≠ 10 ∧ (1 : Fin 14) ≠ 3 ∧ hc_adjB 10 3 = false))

      have h1_3 : 3 ≤ (sem_W 14 D 1).card := by
        by_contra hc
        have hf7 := full_of_le2 h hD hB0 hpos (x := 1) (hm 7 (by decide)) (hn 9 (by decide)) (by decide) (by decide) (by omega)
        exact absurd (hf7 10 (sem_mem_W.1 hp7_10).2.1) (by decide)

      have hp0_10 := as_mem hpos (hm 0 (by decide)) (by decide : Adj 0 10)
      have hp4_10 := as_mem hpos (hm 4 (by decide)) (by decide : Adj 4 10)
      have hp5_10 := as_mem hpos (hm 5 (by decide)) (by decide : Adj 5 10)
      have h10_le4 : (sem_W 14 D 10).card ≤ 4 := by have := cc_le h hD br hbr 10; rw [hru10_eq, Finset.card_pair hu12] at this; omega
      have hW10 := pa_four hp0_10 hp4_10 hp5_10 hp7_10
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 4 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 5 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 7 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 4 (by decide)) _ (hm 5 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 4 (by decide)) _ (hm 7 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 5 (by decide)) _ (hm 7 (by decide)) e) (by decide)) h10_le4
      have hfull_045 : ∀ j ∈ ({0, 4, 5} : Finset (Fin 14)), ∀ t, t ∈ supp 14 D (src D (pos j)) → Adj j t := by
        intro j hj t ht
        have hsub045 : ∀ a ∈ ({0, 4, 5} : Finset (Fin 14)), a ∈ ({0, 4, 5, 7} : Finset (Fin 14)) ∧ Adj a 10 ∧ a ≠ 7 := by decide
        have hjI : j ∈ ineligSet 14 D := hm j (hsub045 j hj).1
        have hj10 : Adj j 10 := (hsub045 j hj).2.1
        have h7j : j ≠ 7 := (hsub045 j hj).2.2
        have hf := full_g14 h hD hB0 hpos hjI hj10 (fun p hp hne1 hsub => by
          rcases hW10 p hp with rfl | rfl | rfl | rfl
          · by_cases h0j : j = 0
            · exact hne1 (by rw [h0j])
            · exact h0j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 0 (by decide))))).symm
          · by_cases h4j : j = 4
            · exact hne1 (by rw [h4j])
            · exact h4j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 4 (by decide))))).symm
          · by_cases h5j : j = 5
            · exact hne1 (by rw [h5j])
            · exact h5j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 5 (by decide))))).symm
          · exact h7j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 7 (by decide))))).symm)
        exact (hf t).1 ht

      have h1_card1 : (ru D br 1).card = 1 := by
        have hpos1 : 0 < (ru D br 1).card := by have := cc_le h hD br hbr 1; omega
        have hle2 : (ru D br 1).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br 1 ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        by_contra hne1
        have hru1R : ru D br 1 = {u1, u2} := Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega)
        have hsub10_1 : ru D br 10 ⊆ ru D br 1 := by rw [hru10_eq, hru1R]
        have hres : ∀ u' ∈ residualUnits 14 D br, (10 : Fin 14) ∈ supp 14 D u'.1 → 1 ∈ supp 14 D u'.1 :=
          fun u' hu' h10' => (mem_ru.1 (hsub10_1 (mem_ru.2 ⟨hu', h10'⟩))).2
        have h1_in4 := pe_co_g14 h hD br hbr hpos (hm 4 (by decide)) (helig 10 (by decide)) hres
          ⟨(mem_ru.1 hu1m).2, (mem_ru.1 (hsub10_1 hu1m)).2⟩ (by decide : (g14_nbB 10).card = 3 ∧ hc_adjB 4 10 = true ∧ hc_adjB 4 11 = true ∧ (10 : Fin 14) ≠ 1 ∧ (10 : Fin 14) ≠ 11 ∧ hc_adjB 1 11 = false)
        exact absurd (hfull_045 4 (by decide) 1 h1_in4) (by decide)
      obtain ⟨u0, hru1⟩ := Finset.card_eq_one.1 h1_card1
      have hu0_in10 : u0 ∈ ru D br 10 := by
        rw [hru10_eq]; exact (hReq ▸ Finset.filter_subset _ _ : ru D br 1 ⊆ {u1, u2}) (by rw [hru1]; exact Finset.mem_singleton_self _)
      obtain ⟨P, Q, hPQ, -, -, hsupp⟩ := ru_one_two_supp h hD br hbm hru1 h1_3

      obtain ⟨P, Q, hPQ, hP1, hQ1, hsupp⟩ := ru_one_two_supp h hD br hbm hru1 h1_3
      have hM10 : merges 14 D (carrierT 14 D {10}) = ∅ := by
        have hcc10 := cc_le h hD br hbr 10
        have h4_10 : 4 ≤ (sem_W 14 D 10).card := pa_card4 hp0_10 hp4_10 hp5_10 hp7_10
          (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 4 (by decide)) e) (by decide))
          (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 5 (by decide)) e) (by decide))
          (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 7 (by decide)) e) (by decide))
          (fun e => absurd (hpos.2 _ (hm 4 (by decide)) _ (hm 5 (by decide)) e) (by decide))
          (fun e => absurd (hpos.2 _ (hm 4 (by decide)) _ (hm 7 (by decide)) e) (by decide))
          (fun e => absurd (hpos.2 _ (hm 5 (by decide)) _ (hm 7 (by decide)) e) (by decide))
        rw [hru10_eq, Finset.card_pair hu12] at hcc10
        exact Finset.card_eq_zero.1 (by omega)
      obtain ⟨h10P, h10Q⟩ := hsupp 10 (mem_ru.1 hu0_in10).2
      have hP10 : P ∈ sem_W 14 D 10 := zm_mem h.1 hM10 (sem_mem_W.1 hP1).1 (sem_W_and h.1 hP1) h10P
      have hQ10 : Q ∈ sem_W 14 D 10 := zm_mem h.1 hM10 (sem_mem_W.1 hQ1).1 (sem_W_and h.1 hQ1) h10Q
      have hkill_10 : ∀ e, e ∈ sem_W 14 D 1 → e ∈ sem_W 14 D 10 → e = pos 7 := by
        intro e he1 he10
        rcases hW10 e he10 with rfl | rfl | rfl | rfl
        · exact absurd (hfull_045 0 (by decide) 1 (sem_mem_W.1 he1).2.1) (by decide)
        · exact absurd (hfull_045 4 (by decide) 1 (sem_mem_W.1 he1).2.1) (by decide)
        · exact absurd (hfull_045 5 (by decide) 1 (sem_mem_W.1 he1).2.1) (by decide)
        · rfl
      exact hPQ ((hkill_10 P hP1 hP10).trans (hkill_10 Q hQ1 hQ10).symm)
  · have hru10 : ru D br 10 = {u1} := by
      refine Finset.Subset.antisymm (fun u hu => ?_) (Finset.singleton_subset_iff.2 hu1m)
      have hm' := hsub10 hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hu hu2m
    exact elim_40_44_sing h hD hB0 br hbm hpos hReq hru10
      (hm 4 (by decide)) (hm 5 (by decide)) (hm 7 (by decide))
      (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 6 (by decide))
      (hn 9 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide))
  · have hru10 : ru D br 10 = {u2} := by
      refine Finset.Subset.antisymm (fun u hu => ?_) (Finset.singleton_subset_iff.2 hu2m)
      have hm' := hsub10 hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with rfl | rfl
      · exact absurd hu hu1m
      · exact Finset.mem_singleton_self _
    exact elim_40_44_sing h hD hB0 br hbm hpos (by rw [hReq, Finset.pair_comm]) hru10
      (hm 4 (by decide)) (hm 5 (by decide)) (hm 7 (by decide))
      (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 6 (by decide))
      (hn 9 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide))
  · obtain ⟨u, hu⟩ := hne10
    have hm' := hsub10 hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
    rcases hm' with rfl | rfl
    · exact absurd hu hu1m
    · exact absurd hu hu2m

theorem elim_44 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨44, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {4, 5, 7, 8} := by rw [hI]; decide
  rw [hIeq, show ({4, 5, 7, 8} : Finset (Fin 14)).card = 4 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨44, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨44, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g14_gr h.1 (sem_g14_comp hD)
  have hbr := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
  have hm : ∀ v : Fin 14, v ∈ ({4, 5, 7, 8} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({4, 5, 7, 8} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 14, v ∉ ({4, 5, 7, 8} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  have h10_3 := two_in_deg3 h hD hpos (u := 10) (v := 0) (hm 4 (by decide)) (hm 5 (by decide)) (by decide)
  have hne10 : (ru D br 10).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 10; omega)
  have hsub10 : ru D br 10 ⊆ {u1, u2} := hReq ▸ Finset.filter_subset _ _
  by_cases hu1m : u1 ∈ ru D br 10 <;> by_cases hu2m : u2 ∈ ru D br 10
  · have hru10_eq : ru D br 10 = {u1, u2} := by
      refine Finset.Subset.antisymm hsub10 (fun u hu => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    by_cases h13 : (sem_W 14 D 1).card ≤ 2 ∧ (sem_W 14 D 3).card ≤ 2
    · exact elim_40_44_both_le2 h hD hB0 br hbm hpos hu12 hReq
        (hm 4 (by decide)) (hm 5 (by decide)) (hm 7 (by decide))
        (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 6 (by decide))
        (hn 9 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) h13.1 h13.2
    ·
      have hp7_10 : pos 7 ∈ sem_W 14 D 10 := by
        by_cases l1 : (sem_W 14 D 1).card ≤ 2
        · have h3_3 : 3 ≤ (sem_W 14 D 3).card := by omega
          obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 3; omega : 0 < (ru D br 3).card)
          have hsub3 : ru D br 3 ⊆ ru D br 10 := by rw [hru10_eq, ← hReq]; exact Finset.filter_subset _ _
          have hres : ∀ u' ∈ residualUnits 14 D br, (3 : Fin 14) ∈ supp 14 D u'.1 → 10 ∈ supp 14 D u'.1 :=
            fun u' hu' h3' => (mem_ru.1 (hsub3 (mem_ru.2 ⟨hu', h3'⟩))).2
          exact mem_W_of_pos hpos (hm 7 (by decide)) (pe_co_g14 h hD br hbr hpos (hm 7 (by decide)) (helig 3 (by decide))
            hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub3 hu)).2⟩ (by decide : (g14_nbB 3).card = 3 ∧ hc_adjB 7 3 = true ∧ hc_adjB 7 1 = true ∧ (3 : Fin 14) ≠ 10 ∧ (3 : Fin 14) ≠ 1 ∧ hc_adjB 10 1 = false))
        · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 1; omega : 0 < (ru D br 1).card)
          have hsub1 : ru D br 1 ⊆ ru D br 10 := by rw [hru10_eq, ← hReq]; exact Finset.filter_subset _ _
          have hres : ∀ u' ∈ residualUnits 14 D br, (1 : Fin 14) ∈ supp 14 D u'.1 → 10 ∈ supp 14 D u'.1 :=
            fun u' hu' h1' => (mem_ru.1 (hsub1 (mem_ru.2 ⟨hu', h1'⟩))).2
          exact mem_W_of_pos hpos (hm 7 (by decide)) (pe_co_g14 h hD br hbr hpos (hm 7 (by decide)) (helig 1 (by decide))
            hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub1 hu)).2⟩ (by decide : (g14_nbB 1).card = 3 ∧ hc_adjB 7 1 = true ∧ hc_adjB 7 3 = true ∧ (1 : Fin 14) ≠ 10 ∧ (1 : Fin 14) ≠ 3 ∧ hc_adjB 10 3 = false))
      have h1_3 : 3 ≤ (sem_W 14 D 1).card := by
        by_contra hc
        have hf7 := full_of_le2 h hD hB0 hpos (x := 1) (hm 7 (by decide)) (hn 9 (by decide)) (by decide) (by decide) (by omega)
        exact absurd (hf7 10 (sem_mem_W.1 hp7_10).2.1) (by decide)

      have hp4_10 := as_mem hpos (hm 4 (by decide)) (by decide : Adj 4 10)
      have hp5_10 := as_mem hpos (hm 5 (by decide)) (by decide : Adj 5 10)
      obtain ⟨e100, h100_10, h100_0, hf0_10, -⟩ := pa_ed h hD hpos (by decide : Adj 10 0)
      have h10_le4 : (sem_W 14 D 10).card ≤ 4 := by have := cc_le h hD br hbr 10; rw [hru10_eq, Finset.card_pair hu12] at this; omega
      have h45 : pos 4 ≠ pos 5 := fun e => absurd (hpos.2 _ (hm 4 (by decide)) _ (hm 5 (by decide)) e) (by decide)
      have h47 : pos 4 ≠ pos 7 := fun e => absurd (hpos.2 _ (hm 4 (by decide)) _ (hm 7 (by decide)) e) (by decide)
      have h57 : pos 5 ≠ pos 7 := fun e => absurd (hpos.2 _ (hm 5 (by decide)) _ (hm 7 (by decide)) e) (by decide)
      have h4e : pos 4 ≠ e100 := fun e => hn 0 (by decide) (hf0_10 4 (hm 4 (by decide)) e.symm ▸ hm 4 (by decide))
      have h5e : pos 5 ≠ e100 := fun e => hn 0 (by decide) (hf0_10 5 (hm 5 (by decide)) e.symm ▸ hm 5 (by decide))
      have h7e : pos 7 ≠ e100 := fun e => hn 0 (by decide) (hf0_10 7 (hm 7 (by decide)) e.symm ▸ hm 7 (by decide))
      have hW10 := pa_four hp4_10 hp5_10 hp7_10 h100_10 h45 h47 h4e h57 h5e h7e h10_le4
      have hM10 : merges 14 D (carrierT 14 D {10}) = ∅ := by
        have hcc10 := cc_le h hD br hbr 10
        have h4_10 : 4 ≤ (sem_W 14 D 10).card := pa_card4 hp4_10 hp5_10 hp7_10 h100_10 h45 h47 h4e h57 h5e h7e
        rw [hru10_eq, Finset.card_pair hu12] at hcc10
        exact Finset.card_eq_zero.1 (by omega)
      have hfull_45 : ∀ j ∈ ({4, 5} : Finset (Fin 14)), ∀ t, t ∈ supp 14 D (src D (pos j)) → Adj j t := by
        intro j hj t ht
        have hsub45 : ∀ a ∈ ({4, 5} : Finset (Fin 14)), a ∈ ({4, 5, 7, 8} : Finset (Fin 14)) ∧ Adj a 10 ∧ a ≠ 7 := by decide
        have hjI : j ∈ ineligSet 14 D := hm j (hsub45 j hj).1
        have hj10 : Adj j 10 := (hsub45 j hj).2.1
        have h7j : j ≠ 7 := (hsub45 j hj).2.2
        have hf := full_g14 h hD hB0 hpos hjI hj10 (fun p hp hne1 hsub => by
          rcases hW10 p hp with rfl | rfl | rfl | rfl
          · by_cases h4j : j = 4
            · exact hne1 (by rw [h4j])
            · exact h4j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 4 (by decide))))).symm
          · by_cases h5j : j = 5
            · exact hne1 (by rw [h5j])
            · exact h5j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 5 (by decide))))).symm
          · exact h7j (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 7 (by decide))))).symm
          · exact hn 0 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 h100_0).2.1) ▸ hjI))
        exact (hf t).1 ht

      have h1_card1 : (ru D br 1).card = 1 := by
        have hpos1 : 0 < (ru D br 1).card := by have := cc_le h hD br hbr 1; omega
        have hle2 : (ru D br 1).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br 1 ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        by_contra hne1
        have hru1R : ru D br 1 = {u1, u2} := Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega)
        have hsub10_1 : ru D br 10 ⊆ ru D br 1 := by rw [hru10_eq, hru1R]
        have hres : ∀ u' ∈ residualUnits 14 D br, (10 : Fin 14) ∈ supp 14 D u'.1 → 1 ∈ supp 14 D u'.1 :=
          fun u' hu' h10' => (mem_ru.1 (hsub10_1 (mem_ru.2 ⟨hu', h10'⟩))).2
        have h1_in4 := pe_co_g14 h hD br hbr hpos (hm 4 (by decide)) (helig 10 (by decide)) hres
          ⟨(mem_ru.1 hu1m).2, (mem_ru.1 (hsub10_1 hu1m)).2⟩ (by decide : (g14_nbB 10).card = 3 ∧ hc_adjB 4 10 = true ∧ hc_adjB 4 11 = true ∧ (10 : Fin 14) ≠ 1 ∧ (10 : Fin 14) ≠ 11 ∧ hc_adjB 1 11 = false)
        exact absurd (hfull_45 4 (by decide) 1 h1_in4) (by decide)
      obtain ⟨u0, hru1⟩ := Finset.card_eq_one.1 h1_card1
      have hu0_in10 : u0 ∈ ru D br 10 := by
        rw [hru10_eq]; exact (hReq ▸ Finset.filter_subset _ _ : ru D br 1 ⊆ {u1, u2}) (by rw [hru1]; exact Finset.mem_singleton_self _)
      obtain ⟨P1, Q1, hPQ1, hP1, hQ1, hsupp1⟩ := ru_one_two_supp h hD br hbm hru1 h1_3
      obtain ⟨h10P1, h10Q1⟩ := hsupp1 10 (mem_ru.1 hu0_in10).2
      have hP1_10 : P1 ∈ sem_W 14 D 10 := zm_mem h.1 hM10 (sem_mem_W.1 hP1).1 (sem_W_and h.1 hP1) h10P1
      have hQ1_10 : Q1 ∈ sem_W 14 D 10 := zm_mem h.1 hM10 (sem_mem_W.1 hQ1).1 (sem_W_and h.1 hQ1) h10Q1
      have he100_in_1 : e100 ∈ sem_W 14 D 1 := by
        rcases hW10 P1 hP1_10 with rfl | rfl | rfl | rfl
        · exact absurd (hfull_45 4 (by decide) 1 (sem_mem_W.1 hP1).2.1) (by decide)
        · exact absurd (hfull_45 5 (by decide) 1 (sem_mem_W.1 hP1).2.1) (by decide)
        · rcases hW10 Q1 hQ1_10 with rfl | rfl | rfl | rfl
          · exact absurd (hfull_45 4 (by decide) 1 (sem_mem_W.1 hQ1).2.1) (by decide)
          · exact absurd (hfull_45 5 (by decide) 1 (sem_mem_W.1 hQ1).2.1) (by decide)
          · exact absurd rfl hPQ1
          · exact hQ1
        · exact hP1

      have l2 : (sem_W 14 D 2).card ≤ 2 := by
        by_contra hc
        obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 2; omega : 0 < (ru D br 2).card)
        have hsub2 : ru D br 2 ⊆ ru D br 10 := by rw [hru10_eq, ← hReq]; exact Finset.filter_subset _ _
        have hres : ∀ u' ∈ residualUnits 14 D br, (2 : Fin 14) ∈ supp 14 D u'.1 → 10 ∈ supp 14 D u'.1 :=
          fun u' hu' h2' => (mem_ru.1 (hsub2 (mem_ru.2 ⟨hu', h2'⟩))).2
        have hp8_10 := mem_W_of_pos hpos (hm 8 (by decide)) (pe_co_g14 h hD br hbr hpos (hm 8 (by decide)) (helig 2 (by decide))
          hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub2 hu)).2⟩ (by decide : (g14_nbB 2).card = 3 ∧ hc_adjB 8 2 = true ∧ hc_adjB 8 6 = true ∧ (2 : Fin 14) ≠ 10 ∧ (2 : Fin 14) ≠ 6 ∧ hc_adjB 10 6 = false))
        rcases hW10 (pos 8) hp8_10 with hh | hh | hh | hh
        · exact absurd (hpos.2 _ (hm 8 (by decide)) _ (hm 4 (by decide)) hh) (by decide)
        · exact absurd (hpos.2 _ (hm 8 (by decide)) _ (hm 5 (by decide)) hh) (by decide)
        · exact absurd (hpos.2 _ (hm 8 (by decide)) _ (hm 7 (by decide)) hh) (by decide)
        · exact hn 0 (by decide) (hf0_10 8 (hm 8 (by decide)) hh.symm ▸ hm 8 (by decide))
      have l6 : (sem_W 14 D 6).card ≤ 2 := by
        by_contra hc
        obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 6; omega : 0 < (ru D br 6).card)
        have hsub6 : ru D br 6 ⊆ ru D br 10 := by rw [hru10_eq, ← hReq]; exact Finset.filter_subset _ _
        have hres : ∀ u' ∈ residualUnits 14 D br, (6 : Fin 14) ∈ supp 14 D u'.1 → 10 ∈ supp 14 D u'.1 :=
          fun u' hu' h6' => (mem_ru.1 (hsub6 (mem_ru.2 ⟨hu', h6'⟩))).2
        have hp8_10 := mem_W_of_pos hpos (hm 8 (by decide)) (pe_co_g14 h hD br hbr hpos (hm 8 (by decide)) (helig 6 (by decide))
          hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub6 hu)).2⟩ (by decide : (g14_nbB 6).card = 3 ∧ hc_adjB 8 6 = true ∧ hc_adjB 8 2 = true ∧ (6 : Fin 14) ≠ 10 ∧ (6 : Fin 14) ≠ 2 ∧ hc_adjB 10 2 = false))
        rcases hW10 (pos 8) hp8_10 with hh | hh | hh | hh
        · exact absurd (hpos.2 _ (hm 8 (by decide)) _ (hm 4 (by decide)) hh) (by decide)
        · exact absurd (hpos.2 _ (hm 8 (by decide)) _ (hm 5 (by decide)) hh) (by decide)
        · exact absurd (hpos.2 _ (hm 8 (by decide)) _ (hm 7 (by decide)) hh) (by decide)
        · exact hn 0 (by decide) (hf0_10 8 (hm 8 (by decide)) hh.symm ▸ hm 8 (by decide))

      have h9_3 : 3 ≤ (sem_W 14 D 9).card := by
        by_contra hc; exact pa_m1 h hD hpos 6 9 11 8 5 (hm 8 (by decide)) (hm 5 (by decide))
          (hn 6 (by decide)) (hn 9 (by decide)) (hn 11 (by decide)) (by decide) l6 (by omega)
      have h11_3 : 3 ≤ (sem_W 14 D 11).card := by
        by_contra hc; exact pa_m1 h hD hpos 6 11 9 8 4 (hm 8 (by decide)) (hm 4 (by decide))
          (hn 6 (by decide)) (hn 11 (by decide)) (hn 9 (by decide)) (by decide) l6 (by omega)
      have h12_3 : 3 ≤ (sem_W 14 D 12).card := by
        by_contra hc; exact pa_m1 h hD hpos 2 12 13 8 5 (hm 8 (by decide)) (hm 5 (by decide))
          (hn 2 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) (by decide) l2 (by omega)
      have hne9 : (ru D br 9).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 9; omega)
      have hne11 : (ru D br 11).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 11; omega)
      have hne12 : (ru D br 12).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr 12; omega)

      have hkill_45 : ∀ (v t j : Fin 14), j ∈ ({4, 5} : Finset (Fin 14)) → v ∉ ({4, 5, 7, 8} : Finset (Fin 14)) →
          ((g14_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j 10 = true ∧ v ≠ t ∧ v ≠ 10 ∧ hc_adjB t 10 = false ∧ hc_adjB j t = false) →
          (ru D br v).Nonempty → ru D br v ⊆ ru D br t → False := by
        intro v t j hj hv hg hne hs
        obtain ⟨u, hu⟩ := hne
        have hres : ∀ u' ∈ residualUnits 14 D br, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
          fun u' hu' hv' => (mem_ru.1 (hs (mem_ru.2 ⟨hu', hv'⟩))).2
        have hsub45' : ∀ a ∈ ({4, 5} : Finset (Fin 14)), a ∈ ({4, 5, 7, 8} : Finset (Fin 14)) := by decide
        have hjI : j ∈ ineligSet 14 D := hm j (hsub45' j hj)
        exact sem_adjB_false.1 hg.2.2.2.2.2.2 (hfull_45 j hj t (pe_co_g14 h hD br hbr hpos hjI (helig v hv)
          hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hs hu)).2⟩ ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1⟩))
      have hno_9_11 : ¬ ru D br 9 ⊆ ru D br 11 := hkill_45 9 11 5 (by decide) (by decide) (by decide) hne9
      have hno_11_9 : ¬ ru D br 11 ⊆ ru D br 9 := hkill_45 11 9 4 (by decide) (by decide) (by decide) hne11
      have hno_12_11 : ¬ ru D br 12 ⊆ ru D br 11 := hkill_45 12 11 5 (by decide) (by decide) (by decide) hne12
      have hno_11_12 : ¬ ru D br 11 ⊆ ru D br 12 := hkill_45 11 12 4 (by decide) (by decide) (by decide) hne11

      have hru9_sing : ∃ ua, ru D br 9 = {ua} := by
        rcases finset_pair_incomp hu12 (hReq ▸ Finset.filter_subset _ _) (hReq ▸ Finset.filter_subset _ _)
            hne9 hne11 hno_9_11 hno_11_9 with ⟨h9, _⟩ | ⟨h9, _⟩
        · exact ⟨u1, h9⟩
        · exact ⟨u2, h9⟩
      obtain ⟨ua, hru9⟩ := hru9_sing
      have hua_in10 : ua ∈ ru D br 10 := by
        rw [hru10_eq]; exact (hReq ▸ Finset.filter_subset _ _ : ru D br 9 ⊆ {u1, u2}) (by rw [hru9]; exact Finset.mem_singleton_self _)
      obtain ⟨P9, Q9, hPQ9, hP9, hQ9, hsupp9⟩ := ru_one_two_supp h hD br hbm hru9 h9_3
      obtain ⟨h10P9, h10Q9⟩ := hsupp9 10 (mem_ru.1 hua_in10).2
      have hP9_10 : P9 ∈ sem_W 14 D 10 := zm_mem h.1 hM10 (sem_mem_W.1 hP9).1 (sem_W_and h.1 hP9) h10P9
      have hQ9_10 : Q9 ∈ sem_W 14 D 10 := zm_mem h.1 hM10 (sem_mem_W.1 hQ9).1 (sem_W_and h.1 hQ9) h10Q9

      obtain ⟨Z6, -, hW6, hp6⟩ := ps_side h hD hpos (hm 8 (by decide)) (by decide : Adj 8 6) (by decide) l6
      obtain ⟨e96, h96_9, h96_6, hf6_9, hf96'⟩ := pa_ed h hD hpos (by decide : Adj 9 6)
      obtain ⟨e91, h91_9, h91_1, hf1_9, -⟩ := pa_ed h hD hpos (by decide : Adj 9 1)
      rw [hW6, Finset.mem_insert, Finset.mem_singleton] at h96_6
      have hb96 : sem_bar e96 = Z6 := h96_6.resolve_left (fun hh => hn 9 (by decide) (hf96' 8 (hm 8 (by decide)) hh ▸ hm 8 (by decide)))
      have hp5_9 := as_mem hpos (hm 5 (by decide)) (by decide : Adj 5 9)
      have h9le3 : (sem_W 14 D 9).card ≤ 3 := by have := cc_le h hD br hbr 9; rw [hru9, Finset.card_singleton] at this; omega
      have h9_ne1 : pos 5 ≠ e96 := fun hh => hn 6 (by decide) (hf6_9 5 (hm 5 (by decide)) hh.symm ▸ hm 5 (by decide))
      have h9_ne2 : pos 5 ≠ e91 := fun hh => hn 1 (by decide) (hf1_9 5 (hm 5 (by decide)) hh.symm ▸ hm 5 (by decide))
      have h9_ne3 : e96 ≠ e91 := fun hh => hp6 1 (by decide) (by decide) (by rw [← hb96, hh]; exact h91_1)
      have hW9 := pa_three hp5_9 h96_9 h91_9 h9_ne1 h9_ne2 h9_ne3 h9le3
      have hnot_p7_9 : pos 7 ∉ sem_W 14 D 9 := fun hm7 => by
        rcases hW9 (pos 7) hm7 with hh | hh | hh
        · exact absurd (hpos.2 _ (hm 7 (by decide)) _ (hm 5 (by decide)) hh) (by decide)
        · exact hn 6 (by decide) (hf6_9 7 (hm 7 (by decide)) hh.symm ▸ hm 7 (by decide))
        · exact hn 1 (by decide) (hf1_9 7 (hm 7 (by decide)) hh.symm ▸ hm 7 (by decide))
      have he100_in_9 : e100 ∈ sem_W 14 D 9 := by
        rcases hW10 P9 hP9_10 with rfl | rfl | rfl | rfl
        · exact absurd (hfull_45 4 (by decide) 9 (sem_mem_W.1 hP9).2.1) (by decide)
        · rcases hW10 Q9 hQ9_10 with rfl | rfl | rfl | rfl
          · exact absurd (hfull_45 4 (by decide) 9 (sem_mem_W.1 hQ9).2.1) (by decide)
          · exact absurd rfl hPQ9
          · exact absurd hQ9 hnot_p7_9
          · exact hQ9
        · exact absurd hP9 hnot_p7_9
        · exact hP9

      rcases hW9 e100 he100_in_9 with hh | hh | hh
      · exact h5e hh.symm
      · exact hp6 0 (by decide) (by decide) (by rw [← hb96, ← hh]; exact h100_0)
      · exact w_bar h.1 he100_in_1 (hh ▸ h91_1)
  · have hru10 : ru D br 10 = {u1} := by
      refine Finset.Subset.antisymm (fun u hu => ?_) (Finset.singleton_subset_iff.2 hu1m)
      have hm' := hsub10 hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hu hu2m
    exact elim_40_44_sing h hD hB0 br hbm hpos hReq hru10
      (hm 4 (by decide)) (hm 5 (by decide)) (hm 7 (by decide))
      (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 6 (by decide))
      (hn 9 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide))
  · have hru10 : ru D br 10 = {u2} := by
      refine Finset.Subset.antisymm (fun u hu => ?_) (Finset.singleton_subset_iff.2 hu2m)
      have hm' := hsub10 hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with rfl | rfl
      · exact absurd hu hu1m
      · exact Finset.mem_singleton_self _
    exact elim_40_44_sing h hD hB0 br hbm hpos (by rw [hReq, Finset.pair_comm]) hru10
      (hm 4 (by decide)) (hm 5 (by decide)) (hm 7 (by decide))
      (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 6 (by decide))
      (hn 9 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide))
  · obtain ⟨u, hu⟩ := hne10
    have hm' := hsub10 hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
    rcases hm' with rfl | rfl
    · exact absurd hu hu1m
    · exact absurd hu hu2m

def blkI (v : Fin 14) : Fin 14 :=
  if v = 2 ∨ v = 6 then 8 else if v = 4 ∨ v = 5 then 10 else if v = 9 ∨ v = 13 then 1 else 3

theorem blkI_pe_wit : ∀ v t : Fin 14,
    v ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
    t ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
    blkI v ≠ blkI t →
    ∃ q : Fin 14, blkI v ∈ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ v ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧
      (g14_nbB v).card = 3 ∧ hc_adjB (blkI v) v = true ∧ hc_adjB (blkI v) q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false := by
  decide +kernel

theorem blkI_sing_wit : ∀ v t : Fin 14,
    v ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
    t ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
    blkI v ≠ blkI t →
    ∃ y : Fin 14, blkI v ∈ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ blkI t ∈ ({1, 3, 8, 10} : Finset (Fin 14)) ∧
      y ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ hc_adjB (blkI t) t = true ∧ hc_adjB t y = true ∧ hc_adjB (blkI t) v = false := by
  decide +kernel

theorem blkI_in_I : ∀ v : Fin 14, v ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
    blkI v ∈ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ hc_adjB (blkI v) v = true ∧
    ∃ y : Fin 14, y ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ hc_adjB v y = true := by
  decide +kernel

theorem elim_51 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h12 : totalSurplus 14 D ≤ 12) (hI : ineligSet 14 D = hc_rep ⟨51, by decide⟩) : False := by
  have hel := inelig_card_add 14 D
  have hIeq : ineligSet 14 D = {1, 3, 8, 10} := by rw [hI]; decide
  rw [hIeq, show ({1, 3, 8, 10} : Finset (Fin 14)).card = 4 from by decide] at hel
  by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
  · exact elim_R0_all h hD h0 ⟨51, by decide⟩ hI
  by_cases h1 : Bplus 14 D = (eligSet 14 D).card + 1
  · exact elim_R1_all h hD h12 h1 ⟨51, by decide⟩ (by decide) hI
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g14_gr h.1 (sem_g14_comp hD)
  have hbr := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g14_gr h (sem_g14_comp hD)
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
  have hm : ∀ v : Fin 14, v ∈ ({1, 3, 8, 10} : Finset (Fin 14)) → v ∈ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 14, v ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → v ∉ ineligSet 14 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 14, v ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → v ∈ eligSet 14 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  have hpe : ∀ (v t : Fin 14),
      v ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      t ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      blkI v ≠ blkI t → (ru D br v).Nonempty → ru D br v ⊆ ru D br t →
      pos (blkI v) ∈ sem_W 14 D t := by
    intro v t hv ht hblk hne hs
    obtain ⟨u, hu⟩ := hne
    have hres : ∀ u' ∈ residualUnits 14 D br, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
      fun u' hu' hv' => (mem_ru.1 (hs (mem_ru.2 ⟨hu', hv'⟩))).2
    obtain ⟨q, hiI, hvI, hg⟩ := blkI_pe_wit v t hv ht hblk
    exact mem_W_of_pos hpos (hm (blkI v) hiI)
      (pe_co_g14 h hD br hbr hpos (hm (blkI v) hiI) (helig v hvI) hres ⟨(mem_ru.1 hu).2, (mem_ru.1 (hs hu)).2⟩ hg)
  have hno_eq_sing : ∀ (v t : Fin 14),
      v ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      t ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      blkI v ≠ blkI t → (ru D br v).Nonempty → ru D br v ⊆ ru D br t → (ru D br t).card = 1 → False := by
    intro v t hv ht hblk hnev hs ht1
    have hcardv : (ru D br v).card = 1 := by
      have h1 := Finset.card_pos.2 hnev; have h2 := Finset.card_le_card hs; omega
    have heq : ru D br v = ru D br t := Finset.eq_of_subset_of_card_le hs (by omega)
    have hpv_t := hpe v t hv ht hblk hnev hs
    have hpt_v := hpe t v ht hv hblk.symm (by rw [← heq]; exact hnev) (by rw [heq])
    obtain ⟨y, hivI, hitI, hyI, gtt, gty, gniv⟩ := blkI_sing_wit v t hv ht hblk
    have hpt_t := as_mem hpos (hm (blkI t) hitI) ((hc_adjB_iff _ _).1 gtt)
    obtain ⟨ey, hey, hbey, hfy, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gty)
    have hWt3 : (sem_W 14 D t).card ≤ 3 := by have := cc_le h hD br hbr t; omega
    have hWt := pa_three hpt_t hpv_t hey
      (fun e => hblk.symm (hpos.2 _ (hm _ hitI) _ (hm _ hivI) e))
      (fun e => hn y hyI (hfy _ (hm _ hitI) e.symm ▸ hm _ hitI))
      (fun e => hn y hyI (hfy _ (hm _ hivI) e.symm ▸ hm _ hivI)) hWt3
    have hfull := full_g14 h hD hB0 hpos (hm (blkI t) hitI) ((hc_adjB_iff _ _).1 gtt) (fun p hp hne1 hsub' => by
      rcases hWt p hp with rfl | rfl | rfl
      · exact hne1 rfl
      · exact hblk (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm _ hivI))))
      · exact hn y hyI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbey).2.1) ▸ hm _ hitI))
    exact sem_adjB_false.1 gniv ((hfull v).1 (sem_mem_W.1 hpt_v).2.1)
  have hno_R_all3 : ∀ (t v1 v2 v3 : Fin 14),
      t ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      v1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      v2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      v3 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      (blkI t ≠ blkI v1 ∧ blkI t ≠ blkI v2 ∧ blkI t ≠ blkI v3 ∧
       blkI v1 ≠ blkI v2 ∧ blkI v1 ≠ blkI v3 ∧ blkI v2 ≠ blkI v3) →
      ru D br t = {u1, u2} → (ru D br v1).Nonempty → (ru D br v2).Nonempty → (ru D br v3).Nonempty → False := by
    intro t v1 v2 v3 ht hv1 hv2 hv3 hdiff hrt hn1 hn2 hn3
    have hsub : ∀ v, ru D br v ⊆ ru D br t := fun v => by rw [hrt, ← hReq]; exact Finset.filter_subset _ _
    have hp1 := hpe v1 t hv1 ht hdiff.1.symm hn1 (hsub v1)
    have hp2 := hpe v2 t hv2 ht hdiff.2.1.symm hn2 (hsub v2)
    have hp3 := hpe v3 t hv3 ht hdiff.2.2.1.symm hn3 (hsub v3)
    obtain ⟨hi0, gtt, y, hyI, gty⟩ := blkI_in_I t ht
    have hi1 := (blkI_in_I v1 hv1).1
    have hi2 := (blkI_in_I v2 hv2).1
    have hi3 := (blkI_in_I v3 hv3).1
    have hp0 := as_mem hpos (hm _ hi0) ((hc_adjB_iff _ _).1 gtt)
    obtain ⟨ey, hey, -, hfy, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gty)
    have h5 := pa_card5 hp0 hp1 hp2 hp3 hey
      (fun e => hdiff.1 (hpos.2 _ (hm _ hi0) _ (hm _ hi1) e))
      (fun e => hdiff.2.1 (hpos.2 _ (hm _ hi0) _ (hm _ hi2) e))
      (fun e => hdiff.2.2.1 (hpos.2 _ (hm _ hi0) _ (hm _ hi3) e))
      (fun e => hn y hyI (hfy _ (hm _ hi0) e.symm ▸ hm _ hi0))
      (fun e => hdiff.2.2.2.1 (hpos.2 _ (hm _ hi1) _ (hm _ hi2) e))
      (fun e => hdiff.2.2.2.2.1 (hpos.2 _ (hm _ hi1) _ (hm _ hi3) e))
      (fun e => hn y hyI (hfy _ (hm _ hi1) e.symm ▸ hm _ hi1))
      (fun e => hdiff.2.2.2.2.2 (hpos.2 _ (hm _ hi2) _ (hm _ hi3) e))
      (fun e => hn y hyI (hfy _ (hm _ hi2) e.symm ▸ hm _ hi2))
      (fun e => hn y hyI (hfy _ (hm _ hi3) e.symm ▸ hm _ hi3))
    have hc4 := cc_le h hD br hbr t; rw [hrt, Finset.card_pair hu12] at hc4; omega

  have hno_3sing : ∀ (v1 v2 v3 : Fin 14),
      v1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      v2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      v3 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      blkI v1 ≠ blkI v2 → blkI v1 ≠ blkI v3 → blkI v2 ≠ blkI v3 →
      (ru D br v1).card = 1 → (ru D br v2).card = 1 → (ru D br v3).card = 1 → False := by
    intro v1 v2 v3 hv1 hv2 hv3 h12 h13 h23 c1 c2 c3
    have hsing : ∀ v, (ru D br v).card = 1 → ru D br v = {u1} ∨ ru D br v = {u2} := fun v cv => by
      obtain ⟨u, hu⟩ := Finset.card_eq_one.1 cv
      have huR : u ∈ ({u1, u2} : Finset (Σ _ : ℕ, ℕ)) := hReq ▸ (mem_ru.1 (by rw [hu]; exact Finset.mem_singleton_self _)).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at huR
      rcases huR with rfl | rfl <;> simp [hu]
    rcases hsing v1 c1 with h1 | h1 <;> rcases hsing v2 c2 with h2 | h2 <;> rcases hsing v3 c3 with h3 | h3
    · exact hno_eq_sing v1 v2 hv1 hv2 h12 (by rw [h1]; simp) (by rw [h1, h2]) c2
    · exact hno_eq_sing v1 v2 hv1 hv2 h12 (by rw [h1]; simp) (by rw [h1, h2]) c2
    · exact hno_eq_sing v1 v3 hv1 hv3 h13 (by rw [h1]; simp) (by rw [h1, h3]) c3
    · exact hno_eq_sing v2 v3 hv2 hv3 h23 (by rw [h2]; simp) (by rw [h2, h3]) c3
    · exact hno_eq_sing v2 v3 hv2 hv3 h23 (by rw [h2]; simp) (by rw [h2, h3]) c3
    · exact hno_eq_sing v1 v3 hv1 hv3 h13 (by rw [h1]; simp) (by rw [h1, h3]) c3
    · exact hno_eq_sing v1 v2 hv1 hv2 h12 (by rw [h1]; simp) (by rw [h1, h2]) c2
    · exact hno_eq_sing v1 v2 hv1 hv2 h12 (by rw [h1]; simp) (by rw [h1, h2]) c2

  have hkill_empty_block : ∀ (x1 x2 c1 c2 a1 a2 b1 b2 ix ic ia ib : Fin 14),
      ix ∈ ineligSet 14 D → ic ∈ ineligSet 14 D → ia ∈ ineligSet 14 D → ib ∈ ineligSet 14 D →
      (x1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧ x2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
       c1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧ c2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
       a1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧ a2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
       b1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧ b2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
       blkI x1 = ix ∧ blkI x2 = ix ∧ blkI c1 = ic ∧ blkI c2 = ic ∧
       blkI a1 = ia ∧ blkI a2 = ia ∧ blkI b1 = ib ∧ blkI b2 = ib) →
      (ix ≠ ic ∧ ix ≠ ia ∧ ix ≠ ib ∧ ic ≠ ia ∧ ic ≠ ib ∧ ia ≠ ib ∧
       x1 ≠ x2 ∧ c1 ≠ c2 ∧ a1 ≠ a2 ∧ b1 ≠ b2 ∧
       x1 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ x2 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧
       c1 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ c2 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧
       a1 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ a2 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧
       b1 ∉ ({1, 3, 8, 10} : Finset (Fin 14)) ∧ b2 ∉ ({1, 3, 8, 10} : Finset (Fin 14))) →
      (hc_adjB ix x1 = true ∧ hc_adjB ix x2 = true ∧ hc_adjB ic c1 = true ∧ hc_adjB ic c2 = true ∧
       hc_adjB ia a1 = true ∧ hc_adjB ia a2 = true ∧ hc_adjB ib b1 = true ∧ hc_adjB ib b2 = true ∧
       hc_adjB x1 a1 = true ∧ hc_adjB x1 b1 = true ∧ hc_adjB x2 a2 = true ∧ hc_adjB x2 b2 = true ∧
       hc_adjB c1 a1 = true ∧ hc_adjB c1 b2 = true ∧ hc_adjB c2 a2 = true ∧ hc_adjB c2 b1 = true) →
      (hc_adjB ia c1 = false ∧ hc_adjB ia c2 = false ∧ hc_adjB ib c1 = false ∧ hc_adjB ib c2 = false ∧
       hc_adjB ic a1 = false ∧ hc_adjB ic a2 = false ∧ hc_adjB ic b1 = false ∧ hc_adjB ic b2 = false ∧
       hc_adjB ia b1 = false ∧ hc_adjB ia b2 = false ∧ hc_adjB ib a1 = false ∧ hc_adjB ib a2 = false ∧
       (g14_nbB x1).card = 3 ∧ (g14_nbB x2).card = 3 ∧ (g14_nbB c1).card = 3 ∧ (g14_nbB c2).card = 3 ∧
       (g14_nbB a1).card = 3 ∧ (g14_nbB a2).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB b2).card = 3 ∧
       decide (x1.val < 7) = decide (x2.val < 7) ∧ decide (x1.val < 7) = decide (c1.val < 7) ∧
       decide (x1.val < 7) = decide (c2.val < 7) ∧ decide (a1.val < 7) = decide (a2.val < 7) ∧
       decide (a1.val < 7) = decide (b1.val < 7) ∧ decide (a1.val < 7) = decide (b2.val < 7)) →
      (sem_W 14 D x1).card ≤ 2 → (sem_W 14 D x2).card ≤ 2 → False := by
    intro x1 x2 c1 c2 a1 a2 b1 b2 ix ic ia ib hix hic hia hib hg1 hg2 hg3 hg4 lx1 lx2
    obtain ⟨hx1, hx2, hc1, hc2, ha1, ha2, hb1, hb2, bx1, bx2, bc1, bc2, ba1, ba2, bb1, bb2⟩ := hg1
    obtain ⟨hxic, hxia, hxib, hcia, hcib, haib, hx12, hc12, ha12, hb12,
      hnx1, hnx2, hnc1, hnc2, hna1, hna2, hnb1, hnb2⟩ := hg2
    obtain ⟨gx1, gx2, gc1, gc2, ga1, ga2, gb1, gb2, g11, g1b1, g22, g2b2, gc1a1, gc1b2, gc2a2, gc2b1⟩ := hg3
    obtain ⟨gniac1, gniac2, gnibc1, gnibc2, gnica1, gnica2, gnicb1, gnicb2, gniab1, gniab2, gniba1, gniba2,
      hdx1, hdx2, hdc1, hdc2, hda1, hda2, hdb1, hdb2,
      hsx12, hsxc1, hsxc2, hsa12, hsab1, hsab2⟩ := hg4

    have ha1_3 : 3 ≤ (sem_W 14 D a1).card := by
      by_contra hc; exact pa_m1 h hD hpos x1 a1 b1 ix ia hix hia (hn _ hnx1) (hn _ hna1) (hn _ hnb1)
        ⟨gx1, ga1, g11, g1b1, by intro hh; exact haib (by rw [← ba1, ← bb1, hh]), hda1, hsab1.symm⟩ lx1 (by omega)
    have hb1_3 : 3 ≤ (sem_W 14 D b1).card := by
      by_contra hc; exact pa_m1 h hD hpos x1 b1 a1 ix ib hix hib (hn _ hnx1) (hn _ hnb1) (hn _ hna1)
        ⟨gx1, gb1, g1b1, g11, by intro hh; exact haib (by rw [← ba1, ← bb1, hh]), hdb1, hsab1⟩ lx1 (by omega)
    have ha2_3 : 3 ≤ (sem_W 14 D a2).card := by
      by_contra hc; exact pa_m1 h hD hpos x2 a2 b2 ix ia hix hia (hn _ hnx2) (hn _ hna2) (hn _ hnb2)
        ⟨gx2, ga2, g22, g2b2, by intro hh; exact haib (by rw [← ba2, ← bb2, hh]), hda2, hsab2.symm.trans hsa12⟩ lx2 (by omega)
    have hb2_3 : 3 ≤ (sem_W 14 D b2).card := by
      by_contra hc; exact pa_m1 h hD hpos x2 b2 a2 ix ib hix hib (hn _ hnx2) (hn _ hnb2) (hn _ hna2)
        ⟨gx2, gb2, g2b2, g22, by intro hh; exact haib (by rw [← ba2, ← bb2, hh]), hdb2, hsa12.symm.trans hsab2⟩ lx2 (by omega)
    have hnea1 : (ru D br a1).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr a1; omega)
    have hnea2 : (ru D br a2).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr a2; omega)
    have hneb1 : (ru D br b1).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr b1; omega)
    have hneb2 : (ru D br b2).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr b2; omega)

    obtain ⟨Zx1, -, hWx1, hpx1⟩ := ps_side h hD hpos hix ((hc_adjB_iff _ _).1 gx1) hdx1 lx1
    obtain ⟨Zx2, -, hWx2, hpx2⟩ := ps_side h hD hpos hix ((hc_adjB_iff _ _).1 gx2) hdx2 lx2
    have hZx1_in : Zx1 ∈ sem_W 14 D x1 := by rw [hWx1]; simp
    have hZx2_in : Zx2 ∈ sem_W 14 D x2 := by rw [hWx2]; simp

    have hkill_c_both_le2 : (sem_W 14 D c1).card ≤ 2 → (sem_W 14 D c2).card ≤ 2 → False := by
      intro lc1 lc2
      obtain ⟨Zc1, -, hWc1, hpc1⟩ := ps_side h hD hpos hic ((hc_adjB_iff _ _).1 gc1) hdc1 lc1
      obtain ⟨Zc2, -, hWc2, hpc2⟩ := ps_side h hD hpos hic ((hc_adjB_iff _ _).1 gc2) hdc2 lc2
      have hZc1_in : Zc1 ∈ sem_W 14 D c1 := by rw [hWc1]; simp
      have hZc2_in : Zc2 ∈ sem_W 14 D c2 := by rw [hWc2]; simp

      have hfull_of_card1 : ∀ (p u1' u2' ip : Fin 14) (Zu1 : ℕ × Bool),
          ip ∈ ineligSet 14 D → p ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
          u1' ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → u2' ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
          hc_adjB ip p = true → hc_adjB p u1' = true → hc_adjB p u2' = true →
          sem_W 14 D u1' = {pos ix, Zu1} →
          (∀ t, t ≠ u1' → decide (t.val < 7) = decide (u1'.val < 7) → Zu1 ∉ sem_W 14 D t) →
          u1' ≠ u2' → decide (u2'.val < 7) = decide (u1'.val < 7) →
          (ru D br p).card = 1 → ∀ t, t ∈ supp 14 D (src D (pos ip)) → Adj ip t := by
        intro p u1' u2' ip Zu1 hip hpI hu1 hu2 gip gp1 gp2 hWu1 hpu1 hu12 hsu12 cp1
        obtain ⟨ep1, hep1_p, hep1_u, hf1, hf1'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gp1)
        obtain ⟨ep2, hep2_p, hep2_u, hf2, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gp2)
        have hep1_u' := hep1_u
        rw [hWu1, Finset.mem_insert, Finset.mem_singleton] at hep1_u'
        have hbp1 : sem_bar ep1 = Zu1 := hep1_u'.resolve_left (fun hh => hn p hpI (hf1' ix hix hh ▸ hix))
        have hWp3 : (sem_W 14 D p).card ≤ 3 := by have := cc_le h hD br hbr p; omega
        have hWp := pa_three (as_mem hpos hip ((hc_adjB_iff _ _).1 gip)) hep1_p hep2_p
          (fun hh => hn u1' hu1 (hf1 ip hip hh.symm ▸ hip))
          (fun hh => hn u2' hu2 (hf2 ip hip hh.symm ▸ hip))
          (fun hh => hpu1 u2' hu12.symm hsu12 (by rw [← hbp1, hh]; exact hep2_u)) hWp3
        have hf := full_g14 h hD hB0 hpos hip ((hc_adjB_iff _ _).1 gip) (fun e he hne_e hsub' => by
          rcases hWp e he with rfl | rfl | rfl
          · exact hne_e rfl
          · exact hn u1' hu1 (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hep1_u).2.1) ▸ hip)
          · exact hn u2' hu2 (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hep2_u).2.1) ▸ hip))
        exact fun t ht => (hf t).1 ht

      have hcard1_pair : ∀ (p q ux uc vx vc ip iq : Fin 14) (Zux Zvx : ℕ × Bool),
          ip ∈ ineligSet 14 D → iq ∈ ineligSet 14 D →
          p ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) → q ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
          p ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → q ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
          ux ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → uc ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
          vx ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → vc ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
          blkI p = ip → blkI q = iq → ip ≠ iq →
          hc_adjB ip p = true → hc_adjB p ux = true → hc_adjB p uc = true → hc_adjB ip q = false →
          hc_adjB iq q = true → hc_adjB q vx = true → hc_adjB q vc = true → hc_adjB iq p = false →
          sem_W 14 D ux = {pos ix, Zux} → (∀ t, t ≠ ux → decide (t.val < 7) = decide (ux.val < 7) → Zux ∉ sem_W 14 D t) →
          ux ≠ uc → decide (uc.val < 7) = decide (ux.val < 7) →
          sem_W 14 D vx = {pos ix, Zvx} → (∀ t, t ≠ vx → decide (t.val < 7) = decide (vx.val < 7) → Zvx ∉ sem_W 14 D t) →
          vx ≠ vc → decide (vc.val < 7) = decide (vx.val < 7) →
          (ru D br p).Nonempty → (ru D br q).Nonempty → (ru D br p).card = 1 := by
        intro p q ux uc vx vc ip iq Zux Zvx hip hiq hp hq hpI hqI hux huc hvx hvc bp bq hipq
          gip gp1 gp2 gnipq giq gq1 gq2 gniqp hWux hpux huxc hsuxc hWvx hpvx hvxc hsvxc hnp hnq
        have hple2 : (ru D br p).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br p ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        have hqle2 : (ru D br q).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br q ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        have hposp : 0 < (ru D br p).card := Finset.card_pos.2 hnp
        have hposq : 0 < (ru D br q).card := Finset.card_pos.2 hnq
        by_contra hne1
        have hpR : ru D br p = {u1, u2} := Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega)
        have hsub_qp : ru D br q ⊆ ru D br p := by rw [hpR, ← hReq]; exact Finset.filter_subset _ _
        have hpq_p := hpe q p hq hp (by rw [bp, bq]; exact hipq.symm) hnq hsub_qp
        by_cases hq1 : (ru D br q).card = 1
        · have hfq := hfull_of_card1 q vx vc iq Zvx hiq hqI hvx hvc giq gq1 gq2 hWvx hpvx hvxc hsvxc hq1
          exact sem_adjB_false.1 gniqp (hfq p (bq ▸ (sem_mem_W.1 hpq_p).2.1))
        · have hqR : ru D br q = {u1, u2} := Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega)
          have hpp_q := hpe p q hp hq (by rw [bp, bq]; exact hipq) hnp (by rw [hqR, ← hReq]; exact Finset.filter_subset _ _)
          obtain ⟨ep1, hep1_p, hep1_u, hf1, hf1'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gp1)
          obtain ⟨ep2, hep2_p, hep2_u, hf2, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gp2)
          have hep1_u' := hep1_u
          rw [hWux, Finset.mem_insert, Finset.mem_singleton] at hep1_u'
          have hbp1 : sem_bar ep1 = Zux := hep1_u'.resolve_left (fun hh => hn p hpI (hf1' ix hix hh ▸ hix))
          have hWp4 : (sem_W 14 D p).card ≤ 4 := by have := cc_le h hD br hbr p; rw [hpR, Finset.card_pair hu12] at this; omega
          have hWp := pa_four (as_mem hpos hip ((hc_adjB_iff _ _).1 gip)) (bq ▸ hpq_p) hep1_p hep2_p
            (fun hh => hipq (hpos.2 _ hip _ hiq hh))
            (fun hh => hn ux hux (hf1 ip hip hh.symm ▸ hip))
            (fun hh => hn uc huc (hf2 ip hip hh.symm ▸ hip))
            (fun hh => hn ux hux (hf1 iq hiq hh.symm ▸ hiq))
            (fun hh => hn uc huc (hf2 iq hiq hh.symm ▸ hiq))
            (fun hh => hpux uc huxc.symm hsuxc (by rw [← hbp1, hh]; exact hep2_u)) hWp4
          have hfp := full_g14 h hD hB0 hpos hip ((hc_adjB_iff _ _).1 gip) (fun e he hne_e hsub' => by
            rcases hWp e he with rfl | rfl | rfl | rfl
            · exact hne_e rfl
            · exact hipq.symm (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hiq)))
            · exact hn ux hux (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hep1_u).2.1) ▸ hip)
            · exact hn uc huc (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hep2_u).2.1) ▸ hip))
          exact sem_adjB_false.1 gnipq ((hfp q).1 (bp ▸ (sem_mem_W.1 hpp_q).2.1))
      have ha1_1 : (ru D br a1).card = 1 := hcard1_pair a1 b1 x1 c1 x1 c2 ia ib Zx1 Zx1 hia hib ha1 hb1 hna1 hnb1 hnx1 hnc1 hnx1 hnc2 ba1 bb1 haib ga1 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g11))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc1a1))) gniab1 gb1 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g1b1))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc2b1))) gniba1 hWx1 hpx1 (fun hh => hxic (by rw [← bx1, ← bc1, hh])) hsxc1.symm hWx1 hpx1 (fun hh => hxic (by rw [← bx1, ← bc2, hh])) hsxc2.symm hnea1 hneb1
      have ha2_1 : (ru D br a2).card = 1 := hcard1_pair a2 b2 x2 c2 x2 c1 ia ib Zx2 Zx2 hia hib ha2 hb2 hna2 hnb2 hnx2 hnc2 hnx2 hnc1 ba2 bb2 haib ga2 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g22))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc2a2))) gniab2 gb2 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g2b2))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc1b2))) gniba2 hWx2 hpx2 (fun hh => hxic (by rw [← bx2, ← bc2, hh])) (hsxc2.symm.trans hsx12) hWx2 hpx2 (fun hh => hxic (by rw [← bx2, ← bc1, hh])) (hsxc1.symm.trans hsx12) hnea2 hneb2
      have hb1_1 : (ru D br b1).card = 1 := hcard1_pair b1 a1 x1 c2 x1 c1 ib ia Zx1 Zx1 hib hia hb1 ha1 hnb1 hna1 hnx1 hnc2 hnx1 hnc1 bb1 ba1 haib.symm gb1 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g1b1))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc2b1))) gniba1 ga1 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g11))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc1a1))) gniab1 hWx1 hpx1 (fun hh => hxic (by rw [← bx1, ← bc2, hh])) hsxc2.symm hWx1 hpx1 (fun hh => hxic (by rw [← bx1, ← bc1, hh])) hsxc1.symm hneb1 hnea1

      have hsame_a : ∃ ua, ru D br a1 = {ua} ∧ ru D br a2 = {ua} := by
        have hsing : ∀ v, (ru D br v).card = 1 → ru D br v = {u1} ∨ ru D br v = {u2} := fun v cv => by
          obtain ⟨u, hu⟩ := Finset.card_eq_one.1 cv
          have huR : u ∈ ({u1, u2} : Finset (Σ _ : ℕ, ℕ)) := hReq ▸ (mem_ru.1 (by rw [hu]; exact Finset.mem_singleton_self _)).1
          simp only [Finset.mem_insert, Finset.mem_singleton] at huR
          rcases huR with rfl | rfl <;> simp [hu]
        rcases hsing a1 ha1_1 with h1 | h1 <;> rcases hsing a2 ha2_1 with h2 | h2 <;> rcases hsing b1 hb1_1 with h3 | h3
        · exact absurd (by rw [h1, h3]) (fun hs => hno_eq_sing a1 b1 ha1 hb1 (by rw [ba1, bb1]; exact haib) hnea1 hs hb1_1)
        · exact ⟨u1, h1, h2⟩
        · exact absurd (by rw [h1, h3]) (fun hs => hno_eq_sing a1 b1 ha1 hb1 (by rw [ba1, bb1]; exact haib) hnea1 hs hb1_1)
        · exact absurd (by rw [h2, h3]) (fun hs => hno_eq_sing a2 b1 ha2 hb1 (by rw [ba2, bb1]; exact haib) hnea2 hs hb1_1)
        · exact absurd (by rw [h2, h3]) (fun hs => hno_eq_sing a2 b1 ha2 hb1 (by rw [ba2, bb1]; exact haib) hnea2 hs hb1_1)
        · exact absurd (by rw [h1, h3]) (fun hs => hno_eq_sing a1 b1 ha1 hb1 (by rw [ba1, bb1]; exact haib) hnea1 hs hb1_1)
        · exact ⟨u2, h1, h2⟩
        · exact absurd (by rw [h1, h3]) (fun hs => hno_eq_sing a1 b1 ha1 hb1 (by rw [ba1, bb1]; exact haib) hnea1 hs hb1_1)
      obtain ⟨ua, hrua1, hrua2⟩ := hsame_a
      obtain ⟨P, Q, hPQ, hall⟩ := ru_one_two_common h hD br hbm hrua1 ha1_3
      have ha1ua : a1 ∈ supp 14 D ua.1 := (mem_ru.1 (by rw [hrua1]; exact Finset.mem_singleton_self _)).2
      have ha2ua : a2 ∈ supp 14 D ua.1 := (mem_ru.1 (by rw [hrua2]; exact Finset.mem_singleton_self _)).2
      obtain ⟨hPa1, hQa1⟩ := hall a1 ha1ua hrua1 ha1_3
      obtain ⟨hPa2, hQa2⟩ := hall a2 ha2ua hrua2 ha2_3

      obtain ⟨e1x, h1x_a, h1x_x, hf1x, hf1x'⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 g11))
      obtain ⟨e1c, h1c_a, h1c_c, hf1c, hf1c'⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gc1a1))
      obtain ⟨e2x, h2x_a, h2x_x, hf2x, hf2x'⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 g22))
      obtain ⟨e2c, h2c_a, h2c_c, hf2c, hf2c'⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gc2a2))
      rw [hWx1, Finset.mem_insert, Finset.mem_singleton] at h1x_x
      have hb1x : sem_bar e1x = Zx1 := h1x_x.resolve_left (fun hh => hn a1 hna1 (hf1x' ix hix hh ▸ hix))
      rw [hWc1, Finset.mem_insert, Finset.mem_singleton] at h1c_c
      have hb1c : sem_bar e1c = Zc1 := h1c_c.resolve_left (fun hh => hn a1 hna1 (hf1c' ic hic hh ▸ hic))
      rw [hWx2, Finset.mem_insert, Finset.mem_singleton] at h2x_x
      have hb2x : sem_bar e2x = Zx2 := h2x_x.resolve_left (fun hh => hn a2 hna2 (hf2x' ix hix hh ▸ hix))
      rw [hWc2, Finset.mem_insert, Finset.mem_singleton] at h2c_c
      have hb2c : sem_bar e2c = Zc2 := h2c_c.resolve_left (fun hh => hn a2 hna2 (hf2c' ic hic hh ▸ hic))
      have ha1le3 : (sem_W 14 D a1).card ≤ 3 := by have := cc_le h hD br hbr a1; omega
      have ha2le3 : (sem_W 14 D a2).card ≤ 3 := by have := cc_le h hD br hbr a2; omega
      have hWa1 := pa_three (as_mem hpos hia ((hc_adjB_iff _ _).1 ga1)) h1x_a h1c_a
        (fun hh => hn x1 hnx1 (hf1x ia hia hh.symm ▸ hia))
        (fun hh => hn c1 hnc1 (hf1c ia hia hh.symm ▸ hia))
        (fun hh => hpx1 c1 (fun e => hxic (by rw [← bx1, ← bc1, e])) hsxc1.symm (by rw [← hb1x, hh, hb1c]; exact hZc1_in)) ha1le3
      have hWa2 := pa_three (as_mem hpos hia ((hc_adjB_iff _ _).1 ga2)) h2x_a h2c_a
        (fun hh => hn x2 hnx2 (hf2x ia hia hh.symm ▸ hia))
        (fun hh => hn c2 hnc2 (hf2c ia hia hh.symm ▸ hia))
        (fun hh => hpx2 c2 (fun e => hxic (by rw [← bx2, ← bc2, e])) (hsxc2.symm.trans hsx12) (by rw [← hb2x, hh, hb2c]; exact hZc2_in)) ha2le3
      have hkill_e : ∀ e, e ∈ sem_W 14 D a1 → e ∈ sem_W 14 D a2 → e = pos ia := by
        intro e he1 he2
        rcases hWa1 e he1 with heq | heq | heq
        · exact heq
        · rw [heq] at he2
          rcases hWa2 e1x he2 with hh | hh | hh
          · exact absurd hh.symm (fun hh' => hn x1 hnx1 (hf1x ia hia hh'.symm ▸ hia))
          · exact absurd (by rw [← hb1x, hh, hb2x]; exact hZx2_in) (hpx1 x2 hx12.symm hsx12.symm)
          · exact absurd (by rw [← hb1x, hh, hb2c]; exact hZc2_in) (hpx1 c2 (fun hh' => hxic (by rw [← bx1, ← bc2, hh'])) hsxc2.symm)
        · rw [heq] at he2
          rcases hWa2 e1c he2 with hh | hh | hh
          · exact absurd hh.symm (fun hh' => hn c1 hnc1 (hf1c ia hia hh'.symm ▸ hia))
          · exact absurd (by rw [← hb1c, hh, hb2x]; exact hZx2_in) (hpc1 x2 (fun hh' => hxic (by rw [← bx2, ← bc1, hh'])) (hsx12.symm.trans hsxc1))
          · exact absurd (by rw [← hb1c, hh, hb2c]; exact hZc2_in) (hpc1 c2 hc12.symm (hsxc2.symm.trans hsxc1))
      exact hPQ ((hkill_e P hPa1 hPa2).trans (hkill_e Q hQa1 hQa2).symm)

    have hkill_c_pos : ∀ (c a_adj b_opp c_other xa xb : Fin 14) (Zxa Zxb : ℕ × Bool),
        c ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
        a_adj ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
        b_opp ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
        c ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → a_adj ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
        b_opp ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → c_other ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
        xa ∉ ({1, 3, 8, 10} : Finset (Fin 14)) → xb ∉ ({1, 3, 8, 10} : Finset (Fin 14)) →
        blkI c = ic → blkI a_adj = ia → blkI b_opp = ib →
        hc_adjB ic c = true → hc_adjB ia a_adj = true → hc_adjB ib b_opp = true →
        hc_adjB c a_adj = true → hc_adjB a_adj xa = true → hc_adjB b_opp xb = true → hc_adjB b_opp c_other = true →
        hc_adjB ic a_adj = false → hc_adjB ic b_opp = false → hc_adjB ia b_opp = false → hc_adjB ib a_adj = false →
        sem_W 14 D xa = {pos ix, Zxa} → (∀ t, t ≠ xa → decide (t.val < 7) = decide (xa.val < 7) → Zxa ∉ sem_W 14 D t) →
        xa ≠ c → decide (c.val < 7) = decide (xa.val < 7) →
        sem_W 14 D xb = {pos ix, Zxb} → (∀ t, t ≠ xb → decide (t.val < 7) = decide (xb.val < 7) → Zxb ∉ sem_W 14 D t) →
        xb ≠ c_other → decide (c_other.val < 7) = decide (xb.val < 7) →
        (ru D br c).Nonempty → (ru D br a_adj).Nonempty → (ru D br b_opp).Nonempty →
        3 ≤ (sem_W 14 D a_adj).card → False := by
      intro c a_adj b_opp c_other xa xb Zxa Zxb hc_m ha_m hb_m hcI haI hbI hcoI hxaI hxbI
        bc ba bb gic gia gib gca gaxa gbxb gbco gnica gnicb gniab gniba hWxa hpxa hxac hsxac hWxb hpxb hxbco hsxbco hnc hna hnb ha3

      have hno_R_a : ru D br a_adj ≠ {u1, u2} := by
        intro haR
        have hpb_a := hpe b_opp a_adj hb_m ha_m (by rw [ba, bb]; exact haib.symm) hnb (by rw [haR, ← hReq]; exact Finset.filter_subset _ _)
        have hpc_a := hpe c a_adj hc_m ha_m (by rw [ba, bc]; exact hcia) hnc (by rw [haR, ← hReq]; exact Finset.filter_subset _ _)
        obtain ⟨eax, heax_a, heax_x, hfx, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gaxa)
        have hWa4 : (sem_W 14 D a_adj).card ≤ 4 := by have := cc_le h hD br hbr a_adj; rw [haR, Finset.card_pair hu12] at this; omega
        have hWa := pa_four (as_mem hpos hia ((hc_adjB_iff _ _).1 gia)) (bb ▸ hpb_a) (bc ▸ hpc_a) heax_a
          (fun hh => haib (hpos.2 _ hia _ hib hh))
          (fun hh => hcia.symm (hpos.2 _ hia _ hic hh))
          (fun hh => hn xa hxaI (hfx ia hia hh.symm ▸ hia))
          (fun hh => hcib.symm (hpos.2 _ hib _ hic hh))
          (fun hh => hn xa hxaI (hfx ib hib hh.symm ▸ hib))
          (fun hh => hn xa hxaI (hfx ic hic hh.symm ▸ hic)) hWa4
        have hfa := full_g14 h hD hB0 hpos hia ((hc_adjB_iff _ _).1 gia) (fun e he hne_e hsub' => by
          rcases hWa e he with rfl | rfl | rfl | rfl
          · exact hne_e rfl
          · exact haib.symm (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hib)))
          · exact hcia (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hic)))
          · exact hn xa hxaI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 heax_x).2.1) ▸ hia))
        have hb1 : (ru D br b_opp).card = 1 := by
          have hble2 : (ru D br b_opp).card ≤ 2 := by
            have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br b_opp ⊆ {u1, u2})
            rw [Finset.card_pair hu12] at this; exact this
          have hposb : 0 < (ru D br b_opp).card := Finset.card_pos.2 hnb
          by_contra hne1
          have hbR : ru D br b_opp = {u1, u2} := Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega)
          have hpa_b := hpe a_adj b_opp ha_m hb_m (by rw [ba, bb]; exact haib) hna (by rw [hbR, ← hReq]; exact Finset.filter_subset _ _)
          exact sem_adjB_false.1 gniab ((hfa b_opp).1 (ba ▸ (sem_mem_W.1 hpa_b).2.1))

        obtain ⟨ebx, hebx_b, hebx_x, hfxb, hfxb'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gbxb)
        obtain ⟨ebc, hebc_b, hebc_c, hfcb, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gbco)
        have hebx_x' := hebx_x
        rw [hWxb, Finset.mem_insert, Finset.mem_singleton] at hebx_x'
        have hbbx : sem_bar ebx = Zxb := hebx_x'.resolve_left (fun hh => hn b_opp hbI (hfxb' ix hix hh ▸ hix))
        have hWb3 : (sem_W 14 D b_opp).card ≤ 3 := by have := cc_le h hD br hbr b_opp; omega
        have hWb := pa_three (as_mem hpos hib ((hc_adjB_iff _ _).1 gib)) hebx_b hebc_b
          (fun hh => hn xb hxbI (hfxb ib hib hh.symm ▸ hib))
          (fun hh => hn c_other hcoI (hfcb ib hib hh.symm ▸ hib))
          (fun hh => hpxb c_other hxbco.symm hsxbco (by rw [← hbbx, hh]; exact hebc_c)) hWb3
        have hfb := full_g14 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gib) (fun e he hne_e hsub' => by
          rcases hWb e he with rfl | rfl | rfl
          · exact hne_e rfl
          · exact hn xb hxbI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hebx_x).2.1) ▸ hib)
          · exact hn c_other hcoI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hebc_c).2.1) ▸ hib))
        exact sem_adjB_false.1 gniba ((hfb a_adj).1 (bb ▸ (sem_mem_W.1 hpb_a).2.1))
      have hno_R_b : ru D br b_opp ≠ {u1, u2} := by
        intro hbR
        have hpa_b := hpe a_adj b_opp ha_m hb_m (by rw [ba, bb]; exact haib) hna (by rw [hbR, ← hReq]; exact Finset.filter_subset _ _)
        have hpc_b := hpe c b_opp hc_m hb_m (by rw [bb, bc]; exact hcib) hnc (by rw [hbR, ← hReq]; exact Finset.filter_subset _ _)
        obtain ⟨ebx, hebx_b, hebx_x, hfxb, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gbxb)
        have hWb4 : (sem_W 14 D b_opp).card ≤ 4 := by have := cc_le h hD br hbr b_opp; rw [hbR, Finset.card_pair hu12] at this; omega
        have hWb := pa_four (as_mem hpos hib ((hc_adjB_iff _ _).1 gib)) (ba ▸ hpa_b) (bc ▸ hpc_b) hebx_b
          (fun hh => haib.symm (hpos.2 _ hib _ hia hh))
          (fun hh => hcib.symm (hpos.2 _ hib _ hic hh))
          (fun hh => hn xb hxbI (hfxb ib hib hh.symm ▸ hib))
          (fun hh => hcia.symm (hpos.2 _ hia _ hic hh))
          (fun hh => hn xb hxbI (hfxb ia hia hh.symm ▸ hia))
          (fun hh => hn xb hxbI (hfxb ic hic hh.symm ▸ hic)) hWb4
        have hfb := full_g14 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gib) (fun e he hne_e hsub' => by
          rcases hWb e he with rfl | rfl | rfl | rfl
          · exact hne_e rfl
          · exact haib (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hia)))
          · exact hcib (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hic)))
          · exact hn xb hxbI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hebx_x).2.1) ▸ hib))
        have ha1' : (ru D br a_adj).card = 1 := by
          have hale2 : (ru D br a_adj).card ≤ 2 := by
            have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br a_adj ⊆ {u1, u2})
            rw [Finset.card_pair hu12] at this; exact this
          have hposa : 0 < (ru D br a_adj).card := Finset.card_pos.2 hna
          by_contra hne1
          exact hno_R_a (Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega))
        obtain ⟨eax, heax_a, heax_x, hfxa, hfxa'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gaxa)
        obtain ⟨eac, heac_a, heac_c, hfca, -⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gca))
        have heax_x' := heax_x
        rw [hWxa, Finset.mem_insert, Finset.mem_singleton] at heax_x'
        have hbax : sem_bar eax = Zxa := heax_x'.resolve_left (fun hh => hn a_adj haI (hfxa' ix hix hh ▸ hix))
        have hWa3 : (sem_W 14 D a_adj).card ≤ 3 := by have := cc_le h hD br hbr a_adj; omega
        have hWa := pa_three (as_mem hpos hia ((hc_adjB_iff _ _).1 gia)) heax_a heac_a
          (fun hh => hn xa hxaI (hfxa ia hia hh.symm ▸ hia))
          (fun hh => hn c hcI (hfca ia hia hh.symm ▸ hia))
          (fun hh => hpxa c hxac.symm hsxac (by rw [← hbax, hh]; exact heac_c)) hWa3
        have hfa := full_g14 h hD hB0 hpos hia ((hc_adjB_iff _ _).1 gia) (fun e he hne_e hsub' => by
          rcases hWa e he with rfl | rfl | rfl
          · exact hne_e rfl
          · exact hn xa hxaI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 heax_x).2.1) ▸ hia)
          · exact hn c hcI (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 heac_c).2.1) ▸ hia))
        exact sem_adjB_false.1 gniab ((hfa b_opp).1 (ba ▸ (sem_mem_W.1 hpa_b).2.1))

      have ha1' : (ru D br a_adj).card = 1 := by
        have hale2 : (ru D br a_adj).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br a_adj ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        have hposa : 0 < (ru D br a_adj).card := Finset.card_pos.2 hna
        by_contra hne1
        exact hno_R_a (Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega))
      have hb1' : (ru D br b_opp).card = 1 := by
        have hble2 : (ru D br b_opp).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br b_opp ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        have hposb : 0 < (ru D br b_opp).card := Finset.card_pos.2 hnb
        by_contra hne1
        exact hno_R_b (Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega))

      have hcR : ru D br c = {u1, u2} := by
        have hcle2 : (ru D br c).card ≤ 2 := by
          have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br c ⊆ {u1, u2})
          rw [Finset.card_pair hu12] at this; exact this
        have hposc : 0 < (ru D br c).card := Finset.card_pos.2 hnc
        by_contra hneR
        have hc1' : (ru D br c).card = 1 := by
          by_contra hne1; exact hneR (Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega))
        exact hno_3sing a_adj b_opp c ha_m hb_m hc_m (by rw [ba, bb]; exact haib) (by rw [ba, bc]; exact hcia.symm) (by rw [bb, bc]; exact hcib.symm) ha1' hb1' hc1'

      have hpa_c := hpe a_adj c ha_m hc_m (by rw [ba, bc]; exact hcia.symm) hna (by rw [hcR, ← hReq]; exact Finset.filter_subset _ _)
      have hpb_c := hpe b_opp c hb_m hc_m (by rw [bb, bc]; exact hcib.symm) hnb (by rw [hcR, ← hReq]; exact Finset.filter_subset _ _)
      obtain ⟨eca, heca_c, heca_a, hfa_c, hfc_a⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gca)
      obtain ⟨eax, heax_a, heax_x, hfx_a, hfa_x⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gaxa)
      rw [hWxa, Finset.mem_insert, Finset.mem_singleton] at heax_x
      have hbax : sem_bar eax = Zxa := heax_x.resolve_left (fun hh => hn a_adj haI (hfa_x ix hix hh ▸ hix))
      have hWc4 : (sem_W 14 D c).card ≤ 4 := by have := cc_le h hD br hbr c; rw [hcR, Finset.card_pair hu12] at this; omega
      have hWc_card4 : 4 ≤ (sem_W 14 D c).card := pa_card4 (as_mem hpos hic ((hc_adjB_iff _ _).1 gic)) (ba ▸ hpa_c) (bb ▸ hpb_c) heca_c
        (fun hh => hcia (hpos.2 _ hic _ hia hh))
        (fun hh => hcib (hpos.2 _ hic _ hib hh))
        (fun hh => hn a_adj haI (hfa_c ic hic hh.symm ▸ hic))
        (fun hh => haib (hpos.2 _ hia _ hib hh))
        (fun hh => hn a_adj haI (hfa_c ia hia hh.symm ▸ hia))
        (fun hh => hn a_adj haI (hfa_c ib hib hh.symm ▸ hib))
      have hMc : merges 14 D (carrierT 14 D {c}) = ∅ := by
        have hcc := cc_le h hD br hbr c; rw [hcR, Finset.card_pair hu12] at hcc
        exact Finset.card_eq_zero.1 (by omega)
      have hWc := pa_four (as_mem hpos hic ((hc_adjB_iff _ _).1 gic)) (ba ▸ hpa_c) (bb ▸ hpb_c) heca_c
        (fun hh => hcia (hpos.2 _ hic _ hia hh))
        (fun hh => hcib (hpos.2 _ hic _ hib hh))
        (fun hh => hn a_adj haI (hfa_c ic hic hh.symm ▸ hic))
        (fun hh => haib (hpos.2 _ hia _ hib hh))
        (fun hh => hn a_adj haI (hfa_c ia hia hh.symm ▸ hia))
        (fun hh => hn a_adj haI (hfa_c ib hib hh.symm ▸ hib)) hWc4
      have hWa3 : (sem_W 14 D a_adj).card ≤ 3 := by have := cc_le h hD br hbr a_adj; omega
      have hWa := pa_three (as_mem hpos hia ((hc_adjB_iff _ _).1 gia)) heax_a heca_a
        (fun hh => hn xa hxaI (hfx_a ia hia hh.symm ▸ hia))
        (fun hh => hn c hcI (hfc_a ia hia hh.symm ▸ hia))
        (fun hh => hpxa c hxac.symm hsxac (by rw [← hbax, hh, sem_bar_bar]; exact heca_c)) hWa3
      obtain ⟨ua, hrua⟩ := Finset.card_eq_one.1 ha1'
      have hua_inc : ua ∈ ru D br c := by
        rw [hcR]; exact (hReq ▸ Finset.filter_subset _ _ : ru D br a_adj ⊆ {u1, u2}) (by rw [hrua]; exact Finset.mem_singleton_self _)
      obtain ⟨P, Q, hPQ, hPa, hQa, hsupp⟩ := ru_one_two_supp h hD br hbm hrua ha3
      obtain ⟨hcP, hcQ⟩ := hsupp c (mem_ru.1 hua_inc).2
      have hPc : P ∈ sem_W 14 D c := zm_mem h.1 hMc (sem_mem_W.1 hPa).1 (sem_W_and h.1 hPa) hcP
      have hQc : Q ∈ sem_W 14 D c := zm_mem h.1 hMc (sem_mem_W.1 hQa).1 (sem_W_and h.1 hQa) hcQ
      have hkill_ac : ∀ e, e ∈ sem_W 14 D a_adj → e ∈ sem_W 14 D c → e = pos ia := by
        intro e hea hec
        rcases hWa e hea with heq | heq | heq
        · exact heq
        · rw [heq] at hec
          rcases hWc eax hec with hh | hh | hh | hh
          · exact absurd hh.symm (fun hh' => hn xa hxaI (hfx_a ic hic hh'.symm ▸ hic))
          · exact absurd hh.symm (fun hh' => hn xa hxaI (hfx_a ia hia hh'.symm ▸ hia))
          · exact absurd hh.symm (fun hh' => hn xa hxaI (hfx_a ib hib hh'.symm ▸ hib))
          · exact absurd (hh ▸ heca_a) (w_bar h.1 heax_a)
        · rw [heq] at hec
          rcases hWc (sem_bar eca) hec with hh | hh | hh | hh
          · exact absurd hh.symm (fun hh' => hn c hcI (hfc_a ic hic hh'.symm ▸ hic))
          · exact absurd hh.symm (fun hh' => hn c hcI (hfc_a ia hia hh'.symm ▸ hia))
          · exact absurd hh.symm (fun hh' => hn c hcI (hfc_a ib hib hh'.symm ▸ hib))
          · exact (w_bar h.1 heca_c (hh.symm ▸ heca_c)).elim
      exact hPQ ((hkill_ac P hPa hPc).trans (hkill_ac Q hQa hQc).symm)

    by_cases lc1 : (sem_W 14 D c1).card ≤ 2
    · by_cases lc2 : (sem_W 14 D c2).card ≤ 2
      · exact hkill_c_both_le2 lc1 lc2
      · have hne_c2 : (ru D br c2).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr c2; omega)
        exact hkill_c_pos c2 a2 b2 c1 x2 x2 Zx2 Zx2 hc2 ha2 hb2 hnc2 hna2 hnb2 hnc1 hnx2 hnx2
          bc2 ba2 bb2 gc2 ga2 gb2 gc2a2 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g22)))
          ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g2b2))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc1b2)))
          gnica2 gnicb2 gniab2 gniba2 hWx2 hpx2 (fun hh => hxic (by rw [← bx2, ← bc2, hh])) (hsxc2.symm.trans hsx12)
          hWx2 hpx2 (fun hh => hxic (by rw [← bx2, ← bc1, hh])) (hsxc1.symm.trans hsx12) hne_c2 hnea2 hneb2 ha2_3
    · have hne_c1 : (ru D br c1).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr c1; omega)
      exact hkill_c_pos c1 a1 b1 c2 x1 x1 Zx1 Zx1 hc1 ha1 hb1 hnc1 hna1 hnb1 hnc2 hnx1 hnx1
        bc1 ba1 bb1 gc1 ga1 gb1 gc1a1 ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g11)))
        ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 g1b1))) ((hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gc2b1)))
        gnica1 gnicb1 gniab1 gniba1 hWx1 hpx1 (fun hh => hxic (by rw [← bx1, ← bc1, hh])) hsxc1.symm
        hWx1 hpx1 (fun hh => hxic (by rw [← bx1, ← bc2, hh])) hsxc2.symm hne_c1 hnea1 hneb1 ha1_3

  by_cases hB0_e : (sem_W 14 D 2).card ≤ 2 ∧ (sem_W 14 D 6).card ≤ 2
  · exact hkill_empty_block 2 6 4 5 13 9 12 11 8 10 1 3
      (hm 8 (by decide)) (hm 10 (by decide)) (hm 1 (by decide)) (hm 3 (by decide))
      (by decide) (by decide) (by decide) (by decide) hB0_e.1 hB0_e.2
  by_cases hB1_e : (sem_W 14 D 4).card ≤ 2 ∧ (sem_W 14 D 5).card ≤ 2
  · exact hkill_empty_block 4 5 2 6 13 9 11 12 10 8 1 3
      (hm 10 (by decide)) (hm 8 (by decide)) (hm 1 (by decide)) (hm 3 (by decide))
      (by decide) (by decide) (by decide) (by decide) hB1_e.1 hB1_e.2
  by_cases hB2_e : (sem_W 14 D 13).card ≤ 2 ∧ (sem_W 14 D 9).card ≤ 2
  · exact hkill_empty_block 13 9 12 11 2 6 4 5 1 3 8 10
      (hm 1 (by decide)) (hm 3 (by decide)) (hm 8 (by decide)) (hm 10 (by decide))
      (by decide) (by decide) (by decide) (by decide) hB2_e.1 hB2_e.2
  by_cases hB3_e : (sem_W 14 D 12).card ≤ 2 ∧ (sem_W 14 D 11).card ≤ 2
  · exact hkill_empty_block 12 11 13 9 2 6 5 4 3 1 8 10
      (hm 3 (by decide)) (hm 1 (by decide)) (hm 8 (by decide)) (hm 10 (by decide))
      (by decide) (by decide) (by decide) (by decide) hB3_e.1 hB3_e.2

  have hget : ∀ a b : Fin 14, ¬ ((sem_W 14 D a).card ≤ 2 ∧ (sem_W 14 D b).card ≤ 2) →
      ∃ v, (v = a ∨ v = b) ∧ (ru D br v).Nonempty := by
    intro a b hnot
    by_cases ha : (sem_W 14 D a).card ≤ 2
    · exact ⟨b, Or.inr rfl, Finset.card_pos.1 (by have := cc_le h hD br hbr b; omega)⟩
    · exact ⟨a, Or.inl rfl, Finset.card_pos.1 (by have := cc_le h hD br hbr a; omega)⟩
  obtain ⟨v0, hv0, hnv0⟩ := hget 2 6 hB0_e
  obtain ⟨v1, hv1, hnv1⟩ := hget 4 5 hB1_e
  obtain ⟨v2, hv2, hnv2⟩ := hget 13 9 hB2_e
  obtain ⟨v3, hv3, hnv3⟩ := hget 12 11 hB3_e
  have hv0m : v0 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) := by rcases hv0 with rfl | rfl <;> decide
  have hv1m : v1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) := by rcases hv1 with rfl | rfl <;> decide
  have hv2m : v2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) := by rcases hv2 with rfl | rfl <;> decide
  have hv3m : v3 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) := by rcases hv3 with rfl | rfl <;> decide
  have hb0 : blkI v0 = 8 := by rcases hv0 with rfl | rfl <;> decide
  have hb1 : blkI v1 = 10 := by rcases hv1 with rfl | rfl <;> decide
  have hb2 : blkI v2 = 1 := by rcases hv2 with rfl | rfl <;> decide
  have hb3 : blkI v3 = 3 := by rcases hv3 with rfl | rfl <;> decide
  have hcard1 : ∀ (v : Fin 14), v ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) →
      (ru D br v).Nonempty →
      (∃ w1 w2 w3 : Fin 14, w1 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
        w2 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
        w3 ∈ ({2, 4, 5, 6, 9, 11, 12, 13} : Finset (Fin 14)) ∧
        (blkI v ≠ blkI w1 ∧ blkI v ≠ blkI w2 ∧ blkI v ≠ blkI w3 ∧
         blkI w1 ≠ blkI w2 ∧ blkI w1 ≠ blkI w3 ∧ blkI w2 ≠ blkI w3) ∧
        (ru D br w1).Nonempty ∧ (ru D br w2).Nonempty ∧ (ru D br w3).Nonempty) →
      (ru D br v).card = 1 := by
    intro v hvm hnv ⟨w1, w2, w3, hw1, hw2, hw3, hdiff, hnw1, hnw2, hnw3⟩
    have hle2 : (ru D br v).card ≤ 2 := by
      have := Finset.card_le_card (hReq ▸ Finset.filter_subset _ _ : ru D br v ⊆ {u1, u2})
      rw [Finset.card_pair hu12] at this; exact this
    have hposv : 0 < (ru D br v).card := Finset.card_pos.2 hnv
    by_contra hne1
    exact hno_R_all3 v w1 w2 w3 hvm hw1 hw2 hw3 hdiff
      (Finset.eq_of_subset_of_card_le (hReq ▸ Finset.filter_subset _ _) (by rw [Finset.card_pair hu12]; omega))
      hnw1 hnw2 hnw3
  have c0 : (ru D br v0).card = 1 := hcard1 v0 hv0m hnv0 ⟨v1, v2, v3, hv1m, hv2m, hv3m, by rw [hb0, hb1, hb2, hb3]; decide, hnv1, hnv2, hnv3⟩
  have c1 : (ru D br v1).card = 1 := hcard1 v1 hv1m hnv1 ⟨v0, v2, v3, hv0m, hv2m, hv3m, by rw [hb0, hb1, hb2, hb3]; decide, hnv0, hnv2, hnv3⟩
  have c2 : (ru D br v2).card = 1 := hcard1 v2 hv2m hnv2 ⟨v0, v1, v3, hv0m, hv1m, hv3m, by rw [hb0, hb1, hb2, hb3]; decide, hnv0, hnv1, hnv3⟩
  exact hno_3sing v0 v1 v2 hv0m hv1m hv2m (by rw [hb0, hb1]; decide) (by rw [hb0, hb2]; decide) (by rw [hb1, hb2]; decide) c0 c1 c2

theorem g14_orbit_partition : ∀ idx : Fin 68,
    (hc_rep idx).card ≤ 3 ∨
    (∃ k : Fin 26, cntB2RIdx k = idx) ∨
    idx.val = 39 ∨ idx.val = 40 ∨ idx.val = 42 ∨ idx.val = 44 ∨
    idx.val = 45 ∨ idx.val = 46 ∨ idx.val = 48 ∨ idx.val = 49 ∨
    idx.val = 50 ∨ idx.val = 51 ∨ idx.val = 58 ∨ idx.val = 62 := by
  decide +kernel

theorem g14_lb_26 (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) (hsize : C.size ≤ 25) :
    False := by
  obtain ⟨D, h, hD, -, h12, -, hmem⟩ := g14_wlog_canon C hmono hC hsize
  obtain ⟨idx, hI⟩ := hc_rep_of_mem hmem
  have hI' : ineligSet 14 D = hc_rep idx := hI.symm
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases g14_orbit_partition idx with
    hle3 | ⟨k, rfl⟩ | h39 | h40 | h42 | h44 | h45 | h46 | h48 | h49 | h50 | h51 | h58 | h62
  · by_cases h0 : Bplus 14 D ≤ (eligSet 14 D).card
    · exact elim_R0_all h hD h0 idx hI'
    · have hc3 : 3 ≤ (hc_rep idx).card := by rw [← hI'] at hle3 ⊢; omega
      exact elim_R1_all h hD h12 (by rw [hI'] at hel; omega) idx hc3 hI'
  · exact elim_cnt_b2_R h hD h12 k hI'
  · exact elim_39 h hD h12 ((show idx = ⟨39, by decide⟩ from Fin.ext h39) ▸ hI')
  · exact elim_40 h hD h12 ((show idx = ⟨40, by decide⟩ from Fin.ext h40) ▸ hI')
  · exact elim_42 h hD h12 ((show idx = ⟨42, by decide⟩ from Fin.ext h42) ▸ hI')
  · exact elim_44 h hD h12 ((show idx = ⟨44, by decide⟩ from Fin.ext h44) ▸ hI')
  · exact elim_45 h hD h12 ((show idx = ⟨45, by decide⟩ from Fin.ext h45) ▸ hI')
  · exact elim_46 h hD h12 ((show idx = ⟨46, by decide⟩ from Fin.ext h46) ▸ hI')
  · exact elim_48 h hD h12 ((show idx = ⟨48, by decide⟩ from Fin.ext h48) ▸ hI')
  · exact elim_49 h hD h12 ((show idx = ⟨49, by decide⟩ from Fin.ext h49) ▸ hI')
  · exact elim_50 h hD h12 ((show idx = ⟨50, by decide⟩ from Fin.ext h50) ▸ hI')
  · exact elim_51 h hD h12 ((show idx = ⟨51, by decide⟩ from Fin.ext h51) ▸ hI')
  · exact elim_58 h hD h12 ((show idx = ⟨58, by decide⟩ from Fin.ext h58) ▸ hI')
  · exact elim_62 h hD h12 ((show idx = ⟨62, by decide⟩ from Fin.ext h62) ▸ hI')

end PEqualNP.Outside.L_meta_9728_aux

theorem PEqualNP.Outside.L_meta_9728 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 25 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)))) := by
  rintro ⟨C, hmono, hsize, hC⟩
  exact PEqualNP.Outside.L_meta_9728_aux.g14_lb_26 C hmono hC hsize
