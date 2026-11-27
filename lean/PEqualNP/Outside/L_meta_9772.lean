import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9772_aux
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
  [(0, 6), (0, 8), (0, 12), (1, 7), (1, 11), (1, 12), (2, 6), (2, 10), (2, 11), (3, 9), (3, 10), (3, 12), (4, 8), (4, 9), (4, 11), (5, 7), (5, 8), (5, 10)]

def G13Edge (x : Fin 13 → Bool) : Prop :=
  ∃ u v : Fin 13, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 13) : Prop :=
  (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def adjBits (u : Fin 13) : ℕ :=
  match u.val with
  | 0 => 4416 | 1 => 6272 | 2 => 3136 | 3 => 5632 | 4 => 2816 | 5 => 1408 | 6 => 5 | 7 => 34 | 8 => 49 | 9 => 24 | 10 => 44 | 11 => 22 | _ => 11

def hc_adjB (u v : Fin 13) : Bool := (adjBits u).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 13, hc_adjB u v = true ↔ Adj u v := by
  decide +kernel

theorem sem_adjB_false {u v : Fin 13} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff]; cases hc_adjB u v <;> decide

theorem adj_symm {u v : Fin 13} (h : Adj u v) : Adj v u := h.symm

theorem adj_irrefl (u : Fin 13) : ¬ Adj u u := by
  revert u; decide +kernel

theorem g13Edge_iff_adj (x : Fin 13 → Bool) :
    G13Edge x ↔ ∃ u v : Fin 13, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩; exact ⟨u, v, Or.inl huv, hx, hy⟩
  · rintro ⟨u, v, huv | hvu, hx, hy⟩
    · exact ⟨u, v, huv, hx, hy⟩
    · exact ⟨v, u, hvu, hy, hx⟩

def g13_nbB (v : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun u => hc_adjB v u = true)

def sem_g13_nb (v : Fin 13) : Finset (Fin 13) := g13_nbB v

theorem g13_nb_eq (v : Fin 13) : sem_g13_nb v = g13_nbB v := rfl

theorem g13_mem_nb {i a : Fin 13} : a ∈ sem_g13_nb i ↔ Adj i a := by
  simp only [sem_g13_nb, g13_nbB, Finset.mem_filter, Finset.mem_univ, true_and, hc_adjB_iff]

theorem degree_two_or_three : ∀ v : Fin 13, (g13_nbB v).card = 2 ∨ (g13_nbB v).card = 3 := by
  decide +kernel

theorem common_nbr_le_one : ∀ u v : Fin 13, u ≠ v →
    (g13_nbB u ∩ g13_nbB v).card ≤ 1 := by
  decide +kernel

theorem sup_g13_inter (i j : Fin 13) (hij : i ≠ j) (P : Finset (Fin 13)) :
    (sem_g13_nb i ∩ (sem_g13_nb j ∩ P)).card ≤ 1 := by
  have hsub : sem_g13_nb i ∩ (sem_g13_nb j ∩ P) ⊆ g13_nbB i ∩ g13_nbB j := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_inter] at hx
    exact Finset.mem_inter.2 ⟨hx.1, hx.2.1⟩
  exact (Finset.card_le_card hsub).trans (common_nbr_le_one i j hij)

theorem nbr_diff_exists : ∀ u v : Fin 13, u ≠ v → ∃ z : Fin 13, Adj u z ∧ ¬ Adj v z := by
  have h : ∀ u v : Fin 13, u ≠ v → ∃ z : Fin 13, hc_adjB u z = true ∧ hc_adjB v z = false := by
    decide +kernel
  intro u v huv
  obtain ⟨z, h1, h2⟩ := h u v huv
  exact ⟨z, (hc_adjB_iff u z).1 h1, sem_adjB_false.1 h2⟩

theorem g13_nb_inj {i j : Fin 13} (h : sem_g13_nb i = sem_g13_nb j) : i = j := by
  by_contra hne
  obtain ⟨z, hiz, hjz⟩ := nbr_diff_exists i j hne
  have h1 : z ∈ sem_g13_nb i := g13_mem_nb.2 hiz
  rw [h, g13_mem_nb] at h1
  exact hjz h1

def hc_nbr (v : Fin 13) : Fin 13 :=
  match v.val with
  | 0 => 6 | 1 => 7 | 2 => 6 | 3 => 9 | 4 => 8 | 5 => 7 | 6 => 0 | 7 => 1 | 8 => 0 | 9 => 3 | 10 => 2 | 11 => 1 | _ => 0

theorem hc_nbr_adj : ∀ v : Fin 13, hc_adjB v (hc_nbr v) = true := by
  decide +kernel

def IsCover (S : Finset (Fin 13)) : Prop :=
  ∀ u v : Fin 13, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 13)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

def IsAut (σ : Equiv.Perm (Fin 13)) : Prop :=
  ∀ u v : Fin 13, Adj (σ u) (σ v) ↔ Adj u v

def autFn (k : Fin 24) (v : Fin 13) : Fin 13 :=
  match k.val with
  | 0 => match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | _ => 12
  | 1 => match v.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 9 | 8 => 8 | 9 => 7 | 10 => 11 | 11 => 10 | _ => 12
  | 2 => match v.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 6 | 7 => 9 | 8 => 12 | 9 => 7 | 10 => 10 | 11 => 11 | _ => 8
  | 3 => match v.val with | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 6 | 7 => 7 | 8 => 12 | 9 => 9 | 10 => 11 | 11 => 10 | _ => 8
  | 4 => match v.val with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 2 | 6 => 7 | 7 => 6 | 8 => 11 | 9 => 9 | 10 => 10 | 11 => 8 | _ => 12
  | 5 => match v.val with | 0 => 1 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 0 | 6 => 7 | 7 => 6 | 8 => 12 | 9 => 9 | 10 => 8 | 11 => 10 | _ => 11
  | 6 => match v.val with | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 0 | 4 => 2 | 5 => 4 | 6 => 7 | 7 => 9 | 8 => 11 | 9 => 6 | 10 => 8 | 11 => 10 | _ => 12
  | 7 => match v.val with | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 3 | 6 => 7 | 7 => 9 | 8 => 12 | 9 => 6 | 10 => 10 | 11 => 8 | _ => 11
  | 8 => match v.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 10 | 9 => 9 | 10 => 8 | 11 => 12 | _ => 11
  | 9 => match v.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 4 | 6 => 6 | 7 => 9 | 8 => 11 | 9 => 7 | 10 => 8 | 11 => 12 | _ => 10
  | 10 => match v.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 3 | 6 => 6 | 7 => 9 | 8 => 10 | 9 => 7 | 10 => 12 | 11 => 8 | _ => 11
  | 11 => match v.val with | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 1 | 6 => 6 | 7 => 7 | 8 => 11 | 9 => 9 | 10 => 12 | 11 => 8 | _ => 10
  | 12 => match v.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 2 | 6 => 9 | 7 => 6 | 8 => 10 | 9 => 7 | 10 => 11 | 11 => 8 | _ => 12
  | 13 => match v.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 9 | 7 => 7 | 8 => 10 | 9 => 6 | 10 => 8 | 11 => 11 | _ => 12
  | 14 => match v.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 0 | 6 => 9 | 7 => 6 | 8 => 12 | 9 => 7 | 10 => 8 | 11 => 11 | _ => 10
  | 15 => match v.val with | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 12 | 9 => 6 | 10 => 11 | 11 => 8 | _ => 10
  | 16 => match v.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 2 | 6 => 9 | 7 => 6 | 8 => 11 | 9 => 7 | 10 => 10 | 11 => 12 | _ => 8
  | 17 => match v.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 9 | 7 => 7 | 8 => 8 | 9 => 6 | 10 => 10 | 11 => 12 | _ => 11
  | 18 => match v.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0 | 6 => 9 | 7 => 6 | 8 => 8 | 9 => 7 | 10 => 12 | 11 => 10 | _ => 11
  | 19 => match v.val with | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 11 | 9 => 6 | 10 => 12 | 11 => 10 | _ => 8
  | 20 => match v.val with | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 2 | 6 => 7 | 7 => 6 | 8 => 10 | 9 => 9 | 10 => 11 | 11 => 12 | _ => 8
  | 21 => match v.val with | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 0 | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 9 | 10 => 12 | 11 => 11 | _ => 10
  | 22 => match v.val with | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4 | 6 => 7 | 7 => 9 | 8 => 8 | 9 => 6 | 10 => 11 | 11 => 12 | _ => 10
  | _ => match v.val with | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 3 | 6 => 7 | 7 => 9 | 8 => 10 | 9 => 6 | 10 => 12 | 11 => 11 | _ => 8

def autInv (k : Fin 24) (v : Fin 13) : Fin 13 :=
  match k.val with
  | 0 => match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | _ => 12
  | 1 => match v.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 9 | 8 => 8 | 9 => 7 | 10 => 11 | 11 => 10 | _ => 12
  | 2 => match v.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 6 | 7 => 9 | 8 => 12 | 9 => 7 | 10 => 10 | 11 => 11 | _ => 8
  | 3 => match v.val with | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 6 | 7 => 7 | 8 => 12 | 9 => 9 | 10 => 11 | 11 => 10 | _ => 8
  | 4 => match v.val with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 2 | 6 => 7 | 7 => 6 | 8 => 11 | 9 => 9 | 10 => 10 | 11 => 8 | _ => 12
  | 5 => match v.val with | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 2 | 6 => 7 | 7 => 6 | 8 => 10 | 9 => 9 | 10 => 11 | 11 => 12 | _ => 8
  | 6 => match v.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 2 | 6 => 9 | 7 => 6 | 8 => 10 | 9 => 7 | 10 => 11 | 11 => 8 | _ => 12
  | 7 => match v.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 2 | 6 => 9 | 7 => 6 | 8 => 11 | 9 => 7 | 10 => 10 | 11 => 12 | _ => 8
  | 8 => match v.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 10 | 9 => 9 | 10 => 8 | 11 => 12 | _ => 11
  | 9 => match v.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 3 | 6 => 6 | 7 => 9 | 8 => 10 | 9 => 7 | 10 => 12 | 11 => 8 | _ => 11
  | 10 => match v.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 4 | 6 => 6 | 7 => 9 | 8 => 11 | 9 => 7 | 10 => 8 | 11 => 12 | _ => 10
  | 11 => match v.val with | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 1 | 6 => 6 | 7 => 7 | 8 => 11 | 9 => 9 | 10 => 12 | 11 => 8 | _ => 10
  | 12 => match v.val with | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 0 | 4 => 2 | 5 => 4 | 6 => 7 | 7 => 9 | 8 => 11 | 9 => 6 | 10 => 8 | 11 => 10 | _ => 12
  | 13 => match v.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 9 | 7 => 7 | 8 => 10 | 9 => 6 | 10 => 8 | 11 => 11 | _ => 12
  | 14 => match v.val with | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 3 | 6 => 7 | 7 => 9 | 8 => 10 | 9 => 6 | 10 => 12 | 11 => 11 | _ => 8
  | 15 => match v.val with | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 11 | 9 => 6 | 10 => 12 | 11 => 10 | _ => 8
  | 16 => match v.val with | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 3 | 6 => 7 | 7 => 9 | 8 => 12 | 9 => 6 | 10 => 10 | 11 => 8 | _ => 11
  | 17 => match v.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 9 | 7 => 7 | 8 => 8 | 9 => 6 | 10 => 10 | 11 => 12 | _ => 11
  | 18 => match v.val with | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4 | 6 => 7 | 7 => 9 | 8 => 8 | 9 => 6 | 10 => 11 | 11 => 12 | _ => 10
  | 19 => match v.val with | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 12 | 9 => 6 | 10 => 11 | 11 => 8 | _ => 10
  | 20 => match v.val with | 0 => 1 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 0 | 6 => 7 | 7 => 6 | 8 => 12 | 9 => 9 | 10 => 8 | 11 => 10 | _ => 11
  | 21 => match v.val with | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 0 | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 9 | 10 => 12 | 11 => 11 | _ => 10
  | 22 => match v.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0 | 6 => 9 | 7 => 6 | 8 => 8 | 9 => 7 | 10 => 12 | 11 => 10 | _ => 11
  | _ => match v.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 0 | 6 => 9 | 7 => 6 | 8 => 12 | 9 => 7 | 10 => 8 | 11 => 11 | _ => 10

theorem aut_left_inv : ∀ k : Fin 24, ∀ v : Fin 13, autInv k (autFn k v) = v := by
  decide +kernel

theorem aut_right_inv : ∀ k : Fin 24, ∀ v : Fin 13, autFn k (autInv k v) = v := by
  decide +kernel

def autOf (k : Fin 24) : Equiv.Perm (Fin 13) :=
  ⟨autFn k, autInv k, aut_left_inv k, aut_right_inv k⟩

theorem autOf_isAut_aux : ∀ k : Fin 24, ∀ u v : Fin 13,
    hc_adjB (autFn k u) (autFn k v) = hc_adjB u v := by
  decide +kernel

theorem autOf_isAut (k : Fin 24) : IsAut (autOf k) := by
  intro u v
  rw [← hc_adjB_iff, ← hc_adjB_iff]
  change hc_adjB (autFn k u) (autFn k v) = true ↔ hc_adjB u v = true
  rw [autOf_isAut_aux k u v]

theorem g13Edge_aut (σ : Equiv.Perm (Fin 13)) (hσ : IsAut σ) (x : Fin 13 → Bool) :
    G13Edge (fun i => x (σ i)) ↔ G13Edge x := by
  simp only [g13Edge_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩
    exact ⟨σ u, σ v, (hσ u v).2 huv, hx, hy⟩
  · rintro ⟨u, v, huv, hx, hy⟩
    refine ⟨σ⁻¹ u, σ⁻¹ v, (hσ (σ⁻¹ u) (σ⁻¹ v)).1 ?_, by simpa using hx, by simpa using hy⟩
    simpa using huv

def hc_rep (idx : Fin 44) : Finset (Fin 13) :=
  match idx.val with
  | 0 => ({0, 1} : Finset (Fin 13))
  | 1 => ({0, 2} : Finset (Fin 13))
  | 2 => ({1, 6} : Finset (Fin 13))
  | 3 => ({6, 7} : Finset (Fin 13))
  | 4 => ({1, 8} : Finset (Fin 13))
  | 5 => ({6, 8} : Finset (Fin 13))
  | 6 => ({8, 10} : Finset (Fin 13))
  | 7 => ({0, 1, 2} : Finset (Fin 13))
  | 8 => ({0, 1, 3} : Finset (Fin 13))
  | 9 => ({1, 2, 3} : Finset (Fin 13))
  | 10 => ({1, 3, 6} : Finset (Fin 13))
  | 11 => ({3, 4, 6} : Finset (Fin 13))
  | 12 => ({3, 6, 7} : Finset (Fin 13))
  | 13 => ({1, 2, 8} : Finset (Fin 13))
  | 14 => ({1, 6, 8} : Finset (Fin 13))
  | 15 => ({6, 7, 8} : Finset (Fin 13))
  | 16 => ({6, 7, 9} : Finset (Fin 13))
  | 17 => ({1, 8, 10} : Finset (Fin 13))
  | 18 => ({6, 8, 10} : Finset (Fin 13))
  | 19 => ({7, 8, 10} : Finset (Fin 13))
  | 20 => ({8, 10, 11} : Finset (Fin 13))
  | 21 => ({0, 1, 2, 3} : Finset (Fin 13))
  | 22 => ({0, 2, 3, 4} : Finset (Fin 13))
  | 23 => ({1, 3, 4, 6} : Finset (Fin 13))
  | 24 => ({3, 4, 6, 7} : Finset (Fin 13))
  | 25 => ({1, 2, 3, 8} : Finset (Fin 13))
  | 26 => ({1, 3, 6, 8} : Finset (Fin 13))
  | 27 => ({3, 6, 7, 8} : Finset (Fin 13))
  | 28 => ({6, 7, 8, 9} : Finset (Fin 13))
  | 29 => ({1, 6, 8, 10} : Finset (Fin 13))
  | 30 => ({6, 7, 8, 10} : Finset (Fin 13))
  | 31 => ({6, 8, 9, 10} : Finset (Fin 13))
  | 32 => ({6, 8, 10, 11} : Finset (Fin 13))
  | 33 => ({8, 10, 11, 12} : Finset (Fin 13))
  | 34 => ({0, 1, 2, 3, 4} : Finset (Fin 13))
  | 35 => ({1, 3, 4, 5, 6} : Finset (Fin 13))
  | 36 => ({1, 6, 8, 9, 10} : Finset (Fin 13))
  | 37 => ({6, 7, 8, 9, 10} : Finset (Fin 13))
  | 38 => ({6, 7, 8, 10, 11} : Finset (Fin 13))
  | 39 => ({6, 8, 10, 11, 12} : Finset (Fin 13))
  | 40 => ({0, 1, 2, 3, 4, 5} : Finset (Fin 13))
  | 41 => ({6, 7, 8, 9, 10, 11} : Finset (Fin 13))
  | 42 => ({6, 7, 8, 10, 11, 12} : Finset (Fin 13))
  | _ => ({6, 7, 8, 9, 10, 11, 12} : Finset (Fin 13))

def canonI : Finset (Finset (Fin 13)) := Finset.univ.image hc_rep

theorem hc_rep_of_mem {I : Finset (Fin 13)} (h : I ∈ canonI) :
    ∃ idx : Fin 44, hc_rep idx = I := by
  obtain ⟨idx, -, heq⟩ := Finset.mem_image.1 h
  exact ⟨idx, heq⟩

def repMask (idx : Fin 44) : ℕ :=
  match idx.val with
  | 0 => 3
  | 1 => 5
  | 2 => 66
  | 3 => 192
  | 4 => 258
  | 5 => 320
  | 6 => 1280
  | 7 => 7
  | 8 => 11
  | 9 => 14
  | 10 => 74
  | 11 => 88
  | 12 => 200
  | 13 => 262
  | 14 => 322
  | 15 => 448
  | 16 => 704
  | 17 => 1282
  | 18 => 1344
  | 19 => 1408
  | 20 => 3328
  | 21 => 15
  | 22 => 29
  | 23 => 90
  | 24 => 216
  | 25 => 270
  | 26 => 330
  | 27 => 456
  | 28 => 960
  | 29 => 1346
  | 30 => 1472
  | 31 => 1856
  | 32 => 3392
  | 33 => 7424
  | 34 => 31
  | 35 => 122
  | 36 => 1858
  | 37 => 1984
  | 38 => 3520
  | 39 => 7488
  | 40 => 63
  | 41 => 4032
  | 42 => 7616
  | _ => 8128

def findCanonIdx (m : ℕ) : Option (Fin 44) :=
  match m with
  | 3 => some ⟨0, by decide⟩
  | 5 => some ⟨1, by decide⟩
  | 66 => some ⟨2, by decide⟩
  | 192 => some ⟨3, by decide⟩
  | 258 => some ⟨4, by decide⟩
  | 320 => some ⟨5, by decide⟩
  | 1280 => some ⟨6, by decide⟩
  | 7 => some ⟨7, by decide⟩
  | 11 => some ⟨8, by decide⟩
  | 14 => some ⟨9, by decide⟩
  | 74 => some ⟨10, by decide⟩
  | 88 => some ⟨11, by decide⟩
  | 200 => some ⟨12, by decide⟩
  | 262 => some ⟨13, by decide⟩
  | 322 => some ⟨14, by decide⟩
  | 448 => some ⟨15, by decide⟩
  | 704 => some ⟨16, by decide⟩
  | 1282 => some ⟨17, by decide⟩
  | 1344 => some ⟨18, by decide⟩
  | 1408 => some ⟨19, by decide⟩
  | 3328 => some ⟨20, by decide⟩
  | 15 => some ⟨21, by decide⟩
  | 29 => some ⟨22, by decide⟩
  | 90 => some ⟨23, by decide⟩
  | 216 => some ⟨24, by decide⟩
  | 270 => some ⟨25, by decide⟩
  | 330 => some ⟨26, by decide⟩
  | 456 => some ⟨27, by decide⟩
  | 960 => some ⟨28, by decide⟩
  | 1346 => some ⟨29, by decide⟩
  | 1472 => some ⟨30, by decide⟩
  | 1856 => some ⟨31, by decide⟩
  | 3392 => some ⟨32, by decide⟩
  | 7424 => some ⟨33, by decide⟩
  | 31 => some ⟨34, by decide⟩
  | 122 => some ⟨35, by decide⟩
  | 1858 => some ⟨36, by decide⟩
  | 1984 => some ⟨37, by decide⟩
  | 3520 => some ⟨38, by decide⟩
  | 7488 => some ⟨39, by decide⟩
  | 63 => some ⟨40, by decide⟩
  | 4032 => some ⟨41, by decide⟩
  | 7616 => some ⟨42, by decide⟩
  | 8128 => some ⟨43, by decide⟩
  | _ => none

theorem findCanonIdx_some (m : ℕ) (idx : Fin 44) (h : findCanonIdx m = some idx) :
    repMask idx = m := by
  unfold findCanonIdx at h
  split at h <;> cases h <;> rfl

def setMask (S : Finset (Fin 13)) : ℕ :=
  (if (0 : Fin 13) ∈ S then 1 else 0) ||| (if (1 : Fin 13) ∈ S then 2 else 0) |||
  (if (2 : Fin 13) ∈ S then 4 else 0) ||| (if (3 : Fin 13) ∈ S then 8 else 0) |||
  (if (4 : Fin 13) ∈ S then 16 else 0) ||| (if (5 : Fin 13) ∈ S then 32 else 0) |||
  (if (6 : Fin 13) ∈ S then 64 else 0) ||| (if (7 : Fin 13) ∈ S then 128 else 0) |||
  (if (8 : Fin 13) ∈ S then 256 else 0) ||| (if (9 : Fin 13) ∈ S then 512 else 0) |||
  (if (10 : Fin 13) ∈ S then 1024 else 0) ||| (if (11 : Fin 13) ∈ S then 2048 else 0) |||
  (if (12 : Fin 13) ∈ S then 4096 else 0)

theorem ite_two_pow_testBit (p : Prop) [Decidable p] (k b : ℕ) :
    (if p then 2 ^ k else 0).testBit b = (decide (k = b) && decide p) := by
  by_cases hp : p
  · simp [hp, Nat.testBit_two_pow]
  · simp [hp]

theorem ite_two_pow_lt (p : Prop) [Decidable p] (k : ℕ) (hk : k < 13) :
    (if p then 2 ^ k else 0) < 2 ^ 13 := by
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) hk
  · decide

theorem setMask_lt (S : Finset (Fin 13)) : setMask S < 8192 := by
  have h : setMask S < 2 ^ 13 := by
    unfold setMask
    repeat (apply Nat.or_lt_two_pow)
    all_goals split_ifs <;> decide
  exact h

theorem setMask_testBit (S : Finset (Fin 13)) (i : Fin 13) :
    (setMask S).testBit i.val = decide (i ∈ S) := by
  have h : setMask S =
      (if (0 : Fin 13) ∈ S then 2 ^ 0 else 0) ||| (if (1 : Fin 13) ∈ S then 2 ^ 1 else 0) |||
      (if (2 : Fin 13) ∈ S then 2 ^ 2 else 0) ||| (if (3 : Fin 13) ∈ S then 2 ^ 3 else 0) |||
      (if (4 : Fin 13) ∈ S then 2 ^ 4 else 0) ||| (if (5 : Fin 13) ∈ S then 2 ^ 5 else 0) |||
      (if (6 : Fin 13) ∈ S then 2 ^ 6 else 0) ||| (if (7 : Fin 13) ∈ S then 2 ^ 7 else 0) |||
      (if (8 : Fin 13) ∈ S then 2 ^ 8 else 0) ||| (if (9 : Fin 13) ∈ S then 2 ^ 9 else 0) |||
      (if (10 : Fin 13) ∈ S then 2 ^ 10 else 0) ||| (if (11 : Fin 13) ∈ S then 2 ^ 11 else 0) |||
      (if (12 : Fin 13) ∈ S then 2 ^ 12 else 0) := rfl
  rw [h]
  simp only [Nat.testBit_or, ite_two_pow_testBit]
  fin_cases i <;> simp

theorem setMask_inj {S T : Finset (Fin 13)} (h : setMask S = setMask T) : S = T := by
  ext i
  have := congrArg (fun m => m.testBit i.val) h
  rw [setMask_testBit, setMask_testBit] at this
  exact decide_eq_decide.1 this

theorem repMask_eq : ∀ idx : Fin 44, setMask (hc_rep idx) = repMask idx := by
  decide +kernel

def autMask (k : Fin 24) (m : ℕ) : ℕ :=
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
  (if m.testBit 12 then 2 ^ (autOf k 12).val else 0)

theorem autMask_testBit (k : Fin 24) (m : ℕ) (i : Fin 13) :
    (autMask k m).testBit i.val = m.testBit ((autOf k)⁻¹ i).val := by
  have hc : ∀ (j : Fin 13), ((autOf k j).val = i.val) ↔ j = (autOf k)⁻¹ i := by
    intro j
    constructor
    · intro h; exact ((Equiv.eq_symm_apply (autOf k)).2 (Fin.ext h))
    · intro h; exact congrArg Fin.val ((Equiv.eq_symm_apply (autOf k)).1 h)
  have hterm : ∀ (j : Fin 13),
      (if m.testBit j.val = true then 2 ^ (autOf k j).val else 0).testBit i.val =
      (decide (j = (autOf k)⁻¹ i) && m.testBit j.val) := by
    intro j; rw [ite_two_pow_testBit, decide_eq_decide.2 (hc j)]; cases m.testBit j.val <;> rfl
  have hexp : (autMask k m).testBit i.val =
      ((decide ((0 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 0) ||
      (decide ((1 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 1) ||
      (decide ((2 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 2) ||
      (decide ((3 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 3) ||
      (decide ((4 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 4) ||
      (decide ((5 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 5) ||
      (decide ((6 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 6) ||
      (decide ((7 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 7) ||
      (decide ((8 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 8) ||
      (decide ((9 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 9) ||
      (decide ((10 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 10) ||
      (decide ((11 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 11) ||
      (decide ((12 : Fin 13) = (autOf k)⁻¹ i) && m.testBit 12)) := by
    change ((if m.testBit (0 : Fin 13).val = true then 2 ^ (autOf k 0).val else 0) |||
      (if m.testBit (1 : Fin 13).val = true then 2 ^ (autOf k 1).val else 0) |||
      (if m.testBit (2 : Fin 13).val = true then 2 ^ (autOf k 2).val else 0) |||
      (if m.testBit (3 : Fin 13).val = true then 2 ^ (autOf k 3).val else 0) |||
      (if m.testBit (4 : Fin 13).val = true then 2 ^ (autOf k 4).val else 0) |||
      (if m.testBit (5 : Fin 13).val = true then 2 ^ (autOf k 5).val else 0) |||
      (if m.testBit (6 : Fin 13).val = true then 2 ^ (autOf k 6).val else 0) |||
      (if m.testBit (7 : Fin 13).val = true then 2 ^ (autOf k 7).val else 0) |||
      (if m.testBit (8 : Fin 13).val = true then 2 ^ (autOf k 8).val else 0) |||
      (if m.testBit (9 : Fin 13).val = true then 2 ^ (autOf k 9).val else 0) |||
      (if m.testBit (10 : Fin 13).val = true then 2 ^ (autOf k 10).val else 0) |||
      (if m.testBit (11 : Fin 13).val = true then 2 ^ (autOf k 11).val else 0) |||
      (if m.testBit (12 : Fin 13).val = true then 2 ^ (autOf k 12).val else 0)).testBit i.val = _
    simp only [Nat.testBit_or, hterm]
    rfl
  rw [hexp]
  generalize (autOf k)⁻¹ i = t
  fin_cases t <;> simp

theorem setMask_image_aut (k : Fin 24) (S : Finset (Fin 13)) :
    setMask (S.image (autOf k)) = autMask k (setMask S) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 13
  · have hL : (setMask (S.image (autOf k))).testBit b =
        decide ((⟨b, hb⟩ : Fin 13) ∈ S.image (autOf k)) :=
      setMask_testBit (S.image (autOf k)) ⟨b, hb⟩
    rw [hL]
    have him : (⟨b, hb⟩ : Fin 13) ∈ S.image (autOf k) ↔ (autOf k)⁻¹ ⟨b, hb⟩ ∈ S := by
      constructor
      · intro hmem
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.1 hmem
        have : x = (autOf k)⁻¹ ⟨b, hb⟩ := by rw [← hxi]; simp
        exact this ▸ hx
      · intro hx; exact Finset.mem_image.2 ⟨(autOf k)⁻¹ ⟨b, hb⟩, hx, by simp⟩
    have hR : (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 13).val =
        decide ((autOf k)⁻¹ ⟨b, hb⟩ ∈ S) := by
      rw [autMask_testBit, setMask_testBit]
    change _ = (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 13).val
    rw [hR, decide_eq_decide]
    exact him
  · have hL : (setMask (S.image (autOf k))).testBit b = false :=
      Nat.testBit_lt_two_pow ((setMask_lt _).trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 13 ≤ b)))
    have hltR : autMask k (setMask S) < 2 ^ 13 := by
      unfold autMask
      repeat (apply Nat.or_lt_two_pow)
      all_goals exact ite_two_pow_lt _ _ (Fin.isLt _)
    have hR : (autMask k (setMask S)).testBit b = false :=
      Nat.testBit_lt_two_pow (hltR.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 13 ≤ b)))
    rw [hL, hR]

def isIndepMask (m : ℕ) : Bool :=
  edgeList.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def pop13 (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0) +
  (if m.testBit 10 then 1 else 0) + (if m.testBit 11 then 1 else 0) +
  (if m.testBit 12 then 1 else 0)

theorem isIndepMask_of_indep {I : Finset (Fin 13)} (hI : IsIndep I) :
    isIndepMask (setMask I) = true := by
  have hedge : ∀ u v : Fin 13, Adj u v →
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
  exact ⟨hedge 0 6 (by decide), hedge 0 8 (by decide), hedge 0 12 (by decide), hedge 1 7 (by decide), hedge 1 11 (by decide), hedge 1 12 (by decide), hedge 2 6 (by decide), hedge 2 10 (by decide), hedge 2 11 (by decide), hedge 3 9 (by decide), hedge 3 10 (by decide), hedge 3 12 (by decide), hedge 4 8 (by decide), hedge 4 9 (by decide), hedge 4 11 (by decide), hedge 5 7 (by decide), hedge 5 8 (by decide), hedge 5 10 (by decide)⟩

theorem pop13_eq_card (I : Finset (Fin 13)) : pop13 (setMask I) = I.card := by
  have h1 : I.card = ∑ x ∈ (Finset.univ : Finset (Fin 13)), if x ∈ I then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have huniv : (Finset.univ : Finset (Fin 13)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    decide
  rw [h1, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  dsimp only [pop13]
  rw [show (setMask I).testBit 0 = decide ((0 : Fin 13) ∈ I) from setMask_testBit I 0, show (setMask I).testBit 1 = decide ((1 : Fin 13) ∈ I) from setMask_testBit I 1, show (setMask I).testBit 2 = decide ((2 : Fin 13) ∈ I) from setMask_testBit I 2, show (setMask I).testBit 3 = decide ((3 : Fin 13) ∈ I) from setMask_testBit I 3, show (setMask I).testBit 4 = decide ((4 : Fin 13) ∈ I) from setMask_testBit I 4, show (setMask I).testBit 5 = decide ((5 : Fin 13) ∈ I) from setMask_testBit I 5, show (setMask I).testBit 6 = decide ((6 : Fin 13) ∈ I) from setMask_testBit I 6, show (setMask I).testBit 7 = decide ((7 : Fin 13) ∈ I) from setMask_testBit I 7, show (setMask I).testBit 8 = decide ((8 : Fin 13) ∈ I) from setMask_testBit I 8, show (setMask I).testBit 9 = decide ((9 : Fin 13) ∈ I) from setMask_testBit I 9, show (setMask I).testBit 10 = decide ((10 : Fin 13) ∈ I) from setMask_testBit I 10, show (setMask I).testBit 11 = decide ((11 : Fin 13) ∈ I) from setMask_testBit I 11, show (setMask I).testBit 12 = decide ((12 : Fin 13) ∈ I) from setMask_testBit I 12]
  simp only [decide_eq_true_eq]
  omega

def hasCanonAut (m : ℕ) : Bool :=
  (List.finRange 24).any (fun k => (findCanonIdx (autMask k m)).isSome)

theorem g13_canon_all : ∀ mL : Fin 64, ∀ mR : Fin 128,
    let m := mL.val + 64 * mR.val
    isIndepMask m = true → 2 ≤ pop13 m → hasCanonAut m = true := by
  decide +kernel

theorem exists_aut_canon {I : Finset (Fin 13)} (hI : IsIndep I) (hge : 2 ≤ I.card) :
    ∃ σ : Equiv.Perm (Fin 13), IsAut σ ∧ I.image σ ∈ canonI := by
  set m := setMask I with hm
  have hlt : m < 8192 := setMask_lt I
  have hmL : m % 64 < 64 := Nat.mod_lt _ (by decide)
  have hmR : m / 64 < 128 := by omega
  have hsplit : m % 64 + 64 * (m / 64) = m := by omega
  have hall := g13_canon_all ⟨m % 64, hmL⟩ ⟨m / 64, hmR⟩
  dsimp only at hall
  rw [hsplit] at hall
  have hres := hall (isIndepMask_of_indep hI) (by rw [pop13_eq_card]; exact hge)
  rw [hasCanonAut, List.any_eq_true] at hres
  obtain ⟨k, -, hk⟩ := hres
  obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.1 hk
  refine ⟨autOf k, autOf_isAut k, Finset.mem_image.2 ⟨idx, Finset.mem_univ _, ?_⟩⟩
  apply setMask_inj
  rw [repMask_eq, setMask_image_aut, ← hm]
  exact findCanonIdx_some _ _ hidx

theorem g13_not_empty : ¬ G13Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h

theorem g13_not_single (v : Fin 13) : ¬ G13Edge (fun i => decide (i = v)) := by
  rw [g13Edge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab
  exact adj_irrefl v hab

theorem g13_pair {u v : Fin 13} (h : Adj u v) :
    G13Edge (fun i => decide (i = u) || decide (i = v)) :=
  (g13Edge_iff_adj _).2 ⟨u, v, h, by simp, by simp⟩

theorem g13_essential (i : Fin 13) : ∃ x y : Fin 13 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ G13Edge x ∧ ¬ G13Edge y :=
  ⟨fun j => decide (j = i) || decide (j = hc_nbr i), fun j => decide (j = hc_nbr i),
   fun j hj => by simp [hj], g13_pair ((hc_adjB_iff i (hc_nbr i)).1 (hc_nbr_adj i)),
   g13_not_single (hc_nbr i)⟩

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 13 → Bool, val D x (outW 13 D) = true ↔ G13Edge x

theorem g13_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 13 → Bool, C.eval (List.ofFn x) = true ↔ G13Edge x) :
    ∃ D : Dag, StrictLive 13 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h06 : Adj (0 : Fin 13) 6 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 13) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (g13_pair h06)⟩
      · exact ⟨fun _ => false, fun h => g13_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g13_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := g13_essential i
      refine ⟨x, y, hxy, fun h => hy ((hC y).1 ?_)⟩
      rw [← h]; exact (hC x).2 hx)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem g13_supp_out {D : Dag} (hD : Correct D) : supp 13 D (outW 13 D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun v hv =>
    g13_not_single v ((hD _).mp (mem_supp.mp hv))

theorem g13_relabel (σ : Equiv.Perm (Fin 13)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 13 D) (hD : Correct D) :
    StrictLive 13 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 13 (relabel σ D) = totalSurplus 13 D ∧
      Bplus 13 (relabel σ D) = Bplus 13 D ∧ Bzero 13 (relabel σ D) = Bzero 13 D ∧
      eligSet 13 (relabel σ D) = (eligSet 13 D).image σ ∧
      ineligSet 13 (relabel σ D) = (ineligSet 13 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact g13Edge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  simpa [ineligSet] using h

theorem g13_cover_iff_indep (D : Dag) :
    IsCover (eligSet 13 D) ↔ IsIndep (ineligSet 13 D) := by
  constructor
  · intro hcov u hu v hv huv
    have h1 := Finset.mem_sdiff.mp hu
    have h2 := Finset.mem_sdiff.mp hv
    exact (hcov u v huv).elim h1.2 h2.2
  · intro hind u v huv
    by_contra hc; push Not at hc
    exact hind u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.1⟩)
      v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.2⟩) huv

theorem g13_budget {D : Dag} (h : StrictLive 13 D) (hlen : D.length ≤ 23) :
    totalSurplus 13 D = D.length - 12 ∧ totalSurplus 13 D ≤ 11 := by
  have := surplus_identity h
  exact ⟨by omega, by omega⟩

theorem g13_inelig_ge2 {D : Dag} (h : StrictLive 13 D) (hlen : D.length ≤ 23)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) :
    2 ≤ (ineligSet 13 D).card := by
  have h2 := elig_le_Bplus h.1 b hb
  have h3 := Bplus_le_total 13 D
  have h4 := (g13_budget h hlen).2
  have hc := inelig_card_add 13 D
  omega


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


theorem sem_g13_second : ∀ u v : Fin 13, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_g13_gr : sem_Gr (fun u v : Fin 13 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, nbr_diff_exists, fun u v => by
    obtain ⟨a, h1, h2⟩ := sem_g13_second u v
    exact ⟨a, (hc_adjB_iff u a).mp h1, h2⟩⟩

theorem sem_g13_comp {D : Dag} (hD : Correct D) : sem_Comp 13 (fun u v : Fin 13 => Adj u v) D :=
  fun x => (hD x).trans (g13Edge_iff_adj x)

theorem exists_pureBranch {D : Dag} (h : StrictLive 13 D) (hD : Correct D) :
    ∃ b : Fin 13 → ℕ, PureBranch 13 D b :=
  sem_exists_pureBranch sem_g13_gr h.1 (sem_g13_comp hD)

theorem elig_isCover {D : Dag} (h : StrictLive 13 D) (hD : Correct D) :
    IsCover (eligSet 13 D) :=
  fun _ _ huv => sem_elig_cover sem_g13_gr h (sem_g13_comp hD) huv


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

def sideL : Finset (Fin 13) := {0, 1, 2, 3, 4, 5}
def sideR : Finset (Fin 13) := {6, 7, 8, 9, 10, 11, 12}

def os_ptL (k : Fin 6) : Fin 13 := ⟨k.val, by omega⟩
def os_ptR (k : Fin 7) : Fin 13 := ⟨6 + k.val, by omega⟩

theorem os_ptL_inj : Function.Injective os_ptL := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simpa [os_ptL] using this)

theorem os_ptR_inj : Function.Injective os_ptR := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; dsimp [os_ptR] at this; omega)

def maskFin6 (m : Fin 64) : Finset (Fin 6) :=
  Finset.univ.filter (fun k : Fin 6 => m.val.testBit k.val)

theorem exists_maskFin6 (S : Finset (Fin 6)) : ∃ m : Fin 64, maskFin6 m = S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by ext k; simp [maskFin6]⟩
  | insert a s _ ih =>
    obtain ⟨m, hm⟩ := ih
    have hpow : 2 ^ a.val < 2 ^ 6 := Nat.pow_lt_pow_right (by omega) a.isLt
    refine ⟨⟨m.val ||| 2 ^ a.val, Nat.or_lt_two_pow m.isLt hpow⟩, ?_⟩
    ext k
    simp only [maskFin6, Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_or,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
    have hmk : m.val.testBit k.val = true ↔ k ∈ s := by
      have := Finset.ext_iff.1 hm k
      simpa [maskFin6] using this
    rw [hmk, Fin.ext_iff]
    tauto

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

theorem g13_sides : ∀ a b : Fin 13, hc_adjB a b = true →
    decide (a.val < 6) ≠ decide (b.val < 6) := by decide +kernel

theorem sideL_indep : ∀ a ∈ sideL, ∀ b ∈ sideL, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g13_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideL, decide (x.val < 6) = true := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl

theorem sideR_indep : ∀ a ∈ sideR, ∀ b ∈ sideR, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g13_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideR, decide (x.val < 6) = false := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl

theorem g13_lost {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (P : Finset (Fin 13))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 13))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 13 D ∧ sem_g13_nb i ⊆ P ∧ ¬ sup_Occ 13 D P (sem_g13_nb i)) :
    J.card ≤ Bzero 13 D := by
  classical
  have hG := sem_g13_gr
  have hC := sem_g13_comp hD
  have hocc : ∀ i ∈ J, ∀ q, (∀ a ∈ P, (a ∈ supp 13 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2 ⟨q, ?_⟩
    ext a
    rw [Finset.mem_inter, g13_mem_nb]
    exact ⟨fun h1 => (hq a h1.2).1 h1.1,
      fun h1 => ⟨(hq a ((hJ i hi).2.1 (g13_mem_nb.2 h1))).2 h1, (hJ i hi).2.1 (g13_mem_nb.2 h1)⟩⟩
  have hb : ∀ i ∈ J, ∃ b, sem_Chain 13 D i.val b ∧ 2 ≤ fanout D b ∧ supp 13 D b = ∅ := by
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
      (hij ▸ sem_chain_dom h.1 (hbr j hj).1) ⟨a, (hJ j hj).2.1 (g13_mem_nb.2 hja), hja, hia⟩
    obtain ⟨_, _, -, -, -, -, hq⟩ := h1
    exact hocc i hi _ hq
  calc J.card = (J.image br).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Bzero 13 D := bz_card h.1 (J.image br) (fun b hb => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
        exact (hbr i hi).2)

abbrev G13 : Fin 13 → Fin 13 → Prop := fun u v => Adj u v

theorem extra_exit_of_elig_edge {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (P : Finset (Fin 13)) (hPe : P ⊆ eligSet 13 D)
    {v a : Fin 13} (hv : v ∈ eligSet 13 D) (ha : a ∈ P) (hva : Adj v a) :
    ∃ e ∈ exitArcs 13 D (carrierT 13 D P), ∀ i ∈ ineligSet 13 D, e ≠ pos i := by
  classical
  have hS := h.1
  have hG := sem_g13_gr
  have hC := sem_g13_comp hD
  have hex : ∃ w, val D (sem_two v a) w = true ∧ val D (single v) w = false ∧ supp 13 D w ∩ P = ∅ := by
    refine ⟨outW 13 D, (hC _).2 (sem_two_edge hva), ?_, by rw [g13_supp_out hD]; simp⟩
    cases h0 : val D (single v) (outW 13 D)
    · rfl
    · exact absurd ((hD _).1 h0) (g13_not_single v)
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → val D (sem_two v a) u = true →
      val D (single v) u = false → (supp 13 D u ∩ P).Nonempty := by
    intro u hu h1 h2
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc => Nat.find_min hex hu ⟨h1, h2, hc⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < 13 + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : 13 ≤ w := by
    by_contra hc
    have hc' : w < 13 := by omega
    rw [val_input D _ w hc'] at hw1 hw2
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h1 | h1
    · simp [single, h1] at hw2
    · have hs : supp 13 D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
      have hm : a ∈ supp 13 D w ∩ P := Finset.mem_inter.2 ⟨by rw [hs, Finset.mem_singleton]; exact h1.symm, ha⟩
      rw [hw3] at hm; exact Finset.notMem_empty _ hm
  obtain ⟨j, rfl⟩ : ∃ j, w = 13 + j := ⟨w - 13, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha', hb', -⟩ := hS j hj
  have hdead : ∀ w', w' < 13 + j → ∀ i ∈ ineligSet 13 D, i ∈ supp 13 D w' →
      val D (sem_two v a) w' = false := by
    intro w'
    induction w' using Nat.strong_induction_on with
    | _ w' ih =>
      intro hlt' i hi hiw
      have hpure := sem_inelig_pure hG hS hC hi hiw
      by_cases hn' : w' < 13
      · have hs : supp 13 D w' = {⟨w', hn'⟩} := supp_input D ⟨w', hn'⟩
        rw [hs, Finset.mem_singleton] at hiw
        rw [val_input D _ w' hn', ← hiw]
        have hiv : i ≠ v := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hv)
        have hia : i ≠ a := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hPe ha)
        simp [sem_two, hiv, hia]
      · obtain ⟨j', rfl⟩ : ∃ j', w' = 13 + j' := ⟨w' - 13, by omega⟩
        have hj' : j' < D.length := by omega
        obtain ⟨ha1, hb1, -⟩ := hS j' hj'
        have ht' := sem_inelig_or hG h hC hi hj' hiw
        have hop : ∀ u, u < 13 + j' → supp 13 D u ⊆ {i} → val D (sem_two v a) u = false := by
          intro u hlt2 hsub
          by_cases hiu : i ∈ supp 13 D u
          · exact ih u hlt2 (by omega) i hi hiu
          · by_contra hc
            rw [Bool.not_eq_false] at hc
            have hvu : val D (single v) u = false := by
              cases h0 : val D (single v) u
              · rfl
              · have hvs := hsub (mem_supp.2 h0)
                rw [Finset.mem_singleton] at hvs
                exact absurd (hvs ▸ hv) (sem_mem_inelig.mp hi)
            obtain ⟨q, hq⟩ := hmin u (by omega) hc hvu
            have hqi := hsub (Finset.mem_inter.1 hq).1
            rw [Finset.mem_singleton] at hqi
            exact hiu (hqi ▸ (Finset.mem_inter.1 hq).1)
        rw [sem_supp_or hS hj' ht'] at hpure
        rw [val_gate hS _ j' hj', ht', gop_false,
          hop _ ha1 (by rw [← hpure]; exact Finset.subset_union_left),
          hop _ hb1 (by rw [← hpure]; exact Finset.subset_union_right)]
        rfl
  rw [val_gate hS _ j hj] at hw1 hw2
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2
    simp only [gop_false, Bool.or_eq_true, Bool.or_eq_false_iff] at hw1 hw2
    have hsu := sem_supp_or hS hj ht
    rw [hsu, Finset.union_inter_distrib_right, Finset.union_eq_empty] at hw3
    rcases hw1 with h1 | h1
    · obtain ⟨q, hq⟩ := hmin _ ha' h1 hw2.1
      rw [hw3.1] at hq; exact Finset.notMem_empty _ hq
    · obtain ⟨q, hq⟩ := hmin _ hb' h1 hw2.2
      rw [hw3.2] at hq; exact Finset.notMem_empty _ hq
  · rw [ht] at hw1 hw2
    simp only [gop_true, Bool.and_eq_true, Bool.and_eq_false_iff] at hw1 hw2
    have hside : ∃ s : Bool, val D (single v) (src D (j, s)) = false ∧
        val D (sem_two v a) (src D (j, s)) = true ∧ val D (sem_two v a) (src D (j, !s)) = true := by
      rcases hw2 with h2 | h2
      · exact ⟨false, by simpa [src] using h2, by simpa [src] using hw1.1, by simpa [src] using hw1.2⟩
      · exact ⟨true, by simpa [src] using h2, by simpa [src] using hw1.2, by simpa [src] using hw1.1⟩
    obtain ⟨s, hs0, hs1, hsb1⟩ := hside
    have hneP := hmin _ (sem_src_lt hS hj s) hs1 hs0
    refine ⟨(j, s), ?_, fun i hi heq => ?_⟩
    · rw [exitArcs, Finset.mem_filter]
      refine ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 hj, Finset.mem_univ _⟩,
        sup_mem_carrier.2 hneP, ?_⟩
      rw [sup_mem_carrier, hw3]
      exact Finset.not_nonempty_empty
    · have hi_in : i ∈ supp 13 D (src D (j, !s)) := by
        have hp := (hpos.1 i hi).2.2.2
        rw [← heq] at hp
        rw [hp]
        exact Finset.mem_singleton_self i
      have hd := hdead _ (sem_src_lt hS hj (!s)) i hi hi_in
      rw [hsb1] at hd
      exact Bool.noConfusion hd

theorem g13_count {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (P : Finset (Fin 13))
    (hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (hP7 : P.card ≤ 7) (hPe : P ⊆ eligSet 13 D)
    (Oc3 Oc2 Ct Iin : Finset (Fin 13))
    (hOc3 : ∀ i ∈ Oc3, sem_g13_nb i ⊆ P ∧ (sem_g13_nb i).card = 3 ∧ sup_Occ 13 D P (sem_g13_nb i))
    (hOc2 : ∀ i ∈ Oc2, sem_g13_nb i ⊆ P ∧ (sem_g13_nb i).card = 2 ∧ sup_Occ 13 D P (sem_g13_nb i))
    (hCt : ∀ c ∈ Ct, c ∉ Oc3 ∧ c ∉ Oc2 ∧
      (sem_g13_nb c ⊆ P → ¬ sup_Occ 13 D P (sem_g13_nb c)))
    (hIin : ∀ i ∈ Iin, i ∈ ineligSet 13 D ∧ sem_g13_nb i ⊆ P) :
    2 * Oc3.card + Oc2.card + Iin.card +
      (if (Ct.biUnion (fun c => sem_g13_nb c ∩ P)) = ∅ ∧ (∃ v ∈ Oc3 ∪ Oc2, v ∉ ineligSet 13 D) then 1 else 0) +
      (Ct.biUnion (fun c => sem_g13_nb c ∩ P)).card +
      (eligSet 13 D).card ≤ 2 * P.card + Bplus 13 D := by
  classical
  have hG := sem_g13_gr
  have hC := sem_g13_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have hEinj : Set.InjOn pos Iin := fun i hi j hj hij =>
    hpos.2 i (hIin i hi).1 j (hIin j hj).1 hij
  have hE0 : ∀ e ∈ Iin.image pos, e ∈ exitArcs 13 D (carrierT 13 D P) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hj, hemp, hnb, -⟩ := hpos.1 i (hIin i hi).1
    have hdeg := degree_two_or_three i
    have hne : (sem_g13_nb i).Nonempty := Finset.card_pos.1 (by dsimp [sem_g13_nb]; omega)
    obtain ⟨a, ha⟩ := hne
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 hj, Finset.mem_univ _⟩,
      sup_mem_carrier.2 ⟨a, Finset.mem_inter.2 ⟨hnb a (g13_mem_nb.1 ha), (hIin i hi).2 ha⟩⟩, ?_⟩
    rw [sup_mem_carrier, hemp, Finset.empty_inter]
    exact Finset.not_nonempty_empty
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_g13_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_g13_nb c ∩ P :=
    fun f hf => Finset.mem_biUnion.1 hf
  choose! ct hct using hlab
  have hcore : ∀ (E : Finset (ℕ × Bool)),
      (∀ e ∈ E, e ∈ exitArcs 13 D (carrierT 13 D P)) →
      (∀ e ∈ E, ∀ f ∈ Ct.biUnion (fun c => sem_g13_nb c ∩ P), ∀ w, sup_Wit 13 D P (sem_g13_nb (ct f) ∩ P) f w → e ≠ w) →
      2 * Oc3.card + Oc2.card + E.card + (Ct.biUnion (fun c => sem_g13_nb c ∩ P)).card +
        (eligSet 13 D).card ≤ 2 * P.card + Bplus 13 D := by
    intro E hE hEdis
    have hmain := cnt_main2 h.1 hP7 (Oc3.image sem_g13_nb)
      (fun T hT => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
        exact ⟨(hOc3 i hi).2.1, (hOc3 i hi).2.2⟩)
      (fun T hT T' hT' hne => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT'
        have := sup_g13_inter i j (fun hij => hne (hij ▸ rfl)) Finset.univ
        simpa [sem_g13_nb] using this)
      (Oc2.image sem_g13_nb)
      (fun M hM => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hM
        refine ⟨(hOc2 i hi).2.1, (hOc2 i hi).2.2, fun T hT hsub => ?_⟩
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT
        have hij : i ≠ j := fun h => by
          have h2 := (hOc2 i hi).2.1; have h3 := (hOc3 j hj).2.1; rw [h] at h2; omega
        have hle := sup_g13_inter i j hij Finset.univ
        have hsub' : sem_g13_nb i ⊆ sem_g13_nb i ∩ sem_g13_nb j :=
          Finset.subset_inter (Finset.Subset.refl _) hsub
        have hc := Finset.card_le_card hsub'
        have h2 := (hOc2 i hi).2.1
        simp only [Finset.inter_univ] at hle
        omega)
      E hE (Ct.biUnion (fun c => sem_g13_nb c ∩ P)) (fun f => sem_g13_nb (ct f) ∩ P)
      (fun f hf => by
        obtain ⟨hc, hfc⟩ := hct f hf
        refine sup_wit_exists hG h.1 hC (X := insert (ct f) (P \ (sem_g13_nb (ct f) ∩ P)))
          Finset.inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
          ⟨ct f, Finset.mem_insert_self _ _, adj_symm (g13_mem_nb.1 (Finset.mem_inter.1 hfc).1)⟩
        · by_cases hsubP : sem_g13_nb (ct f) ⊆ P
          · rcases degree_two_or_three (ct f) with hd2 | hd3
            · exact Or.inl (by rw [Finset.inter_eq_left.2 hsubP]; dsimp [sem_g13_nb]; omega)
            · rw [Finset.inter_eq_left.2 hsubP]
              exact Or.inr ⟨hd3, (hCt _ hc).2.2 hsubP⟩
          · have hlt : (sem_g13_nb (ct f) ∩ P).card < (sem_g13_nb (ct f)).card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left,
                fun heq => hsubP (heq ▸ Finset.inter_subset_right)⟩)
            rcases degree_two_or_three (ct f) with hd2 | hd3 <;> (rw [g13_nb_eq] at hlt ⊢; exact Or.inl (by omega))
        · have hno : ∀ a ∈ P \ (sem_g13_nb (ct f) ∩ P), ¬ Adj (ct f) a := by
            intro a ha hadj
            rw [Finset.mem_sdiff, Finset.mem_inter, g13_mem_nb] at ha
            exact ha.2 ⟨hadj, ha.1⟩
          intro a ha b hb
          rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
          · exact adj_irrefl _
          · exact hno b hb
          · exact fun hab => hno a ha (adj_symm hab)
          · exact hPi a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1)
      (fun f hf T hT => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
        have h1 := sup_g13_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).1 (hij ▸ hi)) P
        rwa [Finset.inter_comm (sem_g13_nb i)] at h1)
      (fun f hf M hM => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hM
        have h1 := sup_g13_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).2.1 (hij ▸ hi)) P
        rwa [Finset.inter_comm (sem_g13_nb i)] at h1)
      hEdis
    have h4 := carrier_flow_union h P (by rw [g13_supp_out hD]; simp)
    have h5 := surplus_carrierT_le h.1 b hb P
    rw [Finset.inter_eq_left.2 hPe] at h5
    rw [Finset.card_image_of_injective _ (fun i j hij => g13_nb_inj hij),
      Finset.card_image_of_injective _ (fun i j hij => g13_nb_inj hij)] at hmain
    omega
  split_ifs with hcond
  · obtain ⟨hLab0, v, hvU, hvnot⟩ := hcond
    have hve : v ∈ eligSet 13 D := by
      by_contra hne; exact hvnot (sem_mem_inelig.2 hne)
    have hvsub : sem_g13_nb v ⊆ P := by
      rcases Finset.mem_union.1 hvU with h3 | h2
      · exact (hOc3 v h3).1
      · exact (hOc2 v h2).1
    have hne : (sem_g13_nb v).Nonempty := Finset.card_pos.1 (by
      have := degree_two_or_three v; dsimp [sem_g13_nb]; omega)
    obtain ⟨a, ha⟩ := hne
    obtain ⟨ex, hex, hexnot⟩ := extra_exit_of_elig_edge h hD hpos P hPe hve (hvsub ha) (g13_mem_nb.1 ha)
    have hnotmem : ex ∉ Iin.image pos := by
      intro hm
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.1 hm
      exact hexnot i (hIin i hi).1 heq.symm
    have hres := hcore (insert ex (Iin.image pos))
      (fun e he => by
        rcases Finset.mem_insert.1 he with rfl | he
        · exact hex
        · exact hE0 e he)
      (fun _ _ f hf => by rw [hLab0] at hf; exact absurd hf (Finset.notMem_empty _))
    rw [Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injOn hEinj] at hres
    omega
  · have hres := hcore (Iin.image pos) hE0 (fun e he f hf w hw hew => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨hc, -⟩ := hct f hf
      have hnbi : sem_g13_nb i ⊆ supp 13 D (src D (pos i)) ∩ P := fun a ha =>
        Finset.mem_inter.2 ⟨(hpos.1 i (hIin i hi).1).2.2.1 a (g13_mem_nb.1 ha), (hIin i hi).2 ha⟩
      have hwsub : supp 13 D (src D (pos i)) ∩ P ⊆ sem_g13_nb (ct f) ∩ P := hew ▸ hw.2.2.2.2.2.1
      by_cases hci : ct f = i
      · rw [hci, Finset.inter_eq_left.2 (hIin i hi).2] at hwsub
        have heq : supp 13 D (src D (pos i)) ∩ P = sem_g13_nb i := Finset.Subset.antisymm hwsub hnbi
        exact (hCt (ct f) hc).2.2 (hci ▸ (hIin i hi).2) ⟨src D (pos i), hci ▸ heq⟩
      · have hle := sup_g13_inter i (ct f) (Ne.symm hci) P
        have hsub' : sem_g13_nb i ⊆ sem_g13_nb i ∩ (sem_g13_nb (ct f) ∩ P) :=
          Finset.subset_inter (Finset.Subset.refl _) (hnbi.trans hwsub)
        have hcard := Finset.card_le_card hsub'
        rcases degree_two_or_three i with hd | hd <;> (rw [g13_nb_eq] at hcard hle; omega))
    rw [Finset.card_image_of_injOn hEinj] at hres
    omega

theorem g13_sideR_step {D : Dag} (h : StrictLive 13 D) (hD : Correct D) :
    ∃ m : Fin 64,
      let I := ineligSet 13 D
      let P := sideR \ I
      let Oc := maskFin6 m
      let Oc3 := Oc.filter (fun k => (g13_nbB (os_ptL k)).card = 3)
      let Oc2 := Oc.filter (fun k => (g13_nbB (os_ptL k)).card = 2)
      let Ct := (Finset.univ : Finset (Fin 6)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 6 => os_ptL k ∈ I ∧ g13_nbB (os_ptL k) ⊆ P)
      let Lab := Ct.biUnion (fun k => g13_nbB (os_ptL k) ∩ P)
      let extra := if Lab = ∅ ∧ (∃ k ∈ Oc, os_ptL k ∉ I) then 1 else 0
      (∀ k ∈ Oc, g13_nbB (os_ptL k) ⊆ P) ∧
      (∀ k ∈ Oc, sup_Occ 13 D P (sem_g13_nb (os_ptL k))) ∧
      2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card +
        (13 - I.card) ≤ 2 * P.card + Bplus 13 D ∧
      (Iin \ Oc).card ≤ Bzero 13 D := by
  classical
  set I := ineligSet 13 D with hIdef
  set P := sideR \ I
  have hPl : P ⊆ sideR := Finset.sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideR_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (Finset.card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 13 D := fun a ha => by
    by_contra hne; exact (Finset.mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  let Oc := Finset.univ.filter (fun k : Fin 6 =>
    g13_nbB (os_ptL k) ⊆ P ∧ sup_Occ 13 D P (sem_g13_nb (os_ptL k)))
  obtain ⟨m, hm⟩ := exists_maskFin6 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g13_nbB (os_ptL k)).card = 3)
  let Oc2 := Oc.filter (fun k => (g13_nbB (os_ptL k)).card = 2)
  let Ct := (Finset.univ : Finset (Fin 6)) \ Oc
  let Iin := Finset.univ.filter (fun k : Fin 6 => os_ptL k ∈ I ∧ g13_nbB (os_ptL k) ⊆ P)
  have hcnt := g13_count h hD P hPi hP7 hPe (Oc3.image os_ptL) (Oc2.image os_ptL) (Ct.image os_ptL)
    (Iin.image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g13_nb_eq]; exact ⟨hko.2.1, hk.2, g13_nb_eq _ ▸ hko.2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g13_nb_eq]; exact ⟨hko.2.1, hk.2, g13_nb_eq _ ▸ hko.2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have hnk : k ∉ Oc := (Finset.mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hsub hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h3
        rw [os_ptL_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h2
        rw [os_ptL_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · exact hnk (Finset.mem_filter.2 ⟨Finset.mem_univ k, g13_nb_eq _ ▸ hsub, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      have hki := (Finset.mem_filter.1 hk).2
      exact ⟨hki.1, g13_nb_eq _ ▸ hki.2⟩)
  have hlost := g13_lost h hD P hPi ((Iin \ Oc).image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_sdiff] at hk
      have hki := (Finset.mem_filter.1 hk.1).2
      refine ⟨hki.1, g13_nb_eq _ ▸ hki.2, fun hocc => hk.2 ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hki.2, hocc⟩)
  rw [Finset.card_image_of_injective _ os_ptL_inj] at hlost
  rw [Finset.card_image_of_injective _ os_ptL_inj, Finset.card_image_of_injective _ os_ptL_inj,
    Finset.card_image_of_injective _ os_ptL_inj] at hcnt
  have hLabEq : ((Ct.image os_ptL).biUnion (fun c => sem_g13_nb c ∩ P)) =
      Ct.biUnion (fun k => g13_nbB (os_ptL k) ∩ P) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter, g13_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptL k, ⟨k, hk, rfl⟩, hx⟩
  have hUeq : (∃ v ∈ Oc3.image os_ptL ∪ Oc2.image os_ptL, v ∉ ineligSet 13 D) ↔
      (∃ k ∈ Oc, os_ptL k ∉ I) := by
    constructor
    · rintro ⟨v, hv, hvn⟩
      rcases Finset.mem_union.1 hv with h3 | h2
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h3
        exact ⟨k, (Finset.mem_filter.1 hk).1, hvn⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
        exact ⟨k, (Finset.mem_filter.1 hk).1, hvn⟩
    · rintro ⟨k, hk, hkn⟩
      rcases degree_two_or_three (os_ptL k) with hd2 | hd3
      · exact ⟨os_ptL k, Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨hk, hd2⟩, rfl⟩), hkn⟩
      · exact ⟨os_ptL k, Finset.mem_union_left _ (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨hk, hd3⟩, rfl⟩), hkn⟩
  rw [hLabEq] at hcnt
  simp only [hUeq] at hcnt
  have hel := inelig_card_add 13 D
  rw [← hIdef] at hel
  refine ⟨fun k hk => (Finset.mem_filter.1 hk).2.1, fun k hk => (Finset.mem_filter.1 hk).2.2, ?_, hlost⟩
  change 2 * Oc3.card + Oc2.card + Iin.card +
    (if (Ct.biUnion (fun k => g13_nbB (os_ptL k) ∩ P)) = ∅ ∧ (∃ k ∈ Oc, os_ptL k ∉ I) then 1 else 0) +
    (Ct.biUnion (fun k => g13_nbB (os_ptL k) ∩ P)).card + (13 - I.card) ≤ 2 * P.card + Bplus 13 D
  omega

theorem g13_sideL_step {D : Dag} (h : StrictLive 13 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 13 D
      let P := sideL \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g13_nbB (os_ptR k)).card = 3)
      let Oc2 := Oc.filter (fun k => (g13_nbB (os_ptR k)).card = 2)
      let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ g13_nbB (os_ptR k) ⊆ P)
      let Lab := Ct.biUnion (fun k => g13_nbB (os_ptR k) ∩ P)
      let extra := if Lab = ∅ ∧ (∃ k ∈ Oc, os_ptR k ∉ I) then 1 else 0
      (∀ k ∈ Oc, g13_nbB (os_ptR k) ⊆ P) ∧
      (∀ k ∈ Oc, sup_Occ 13 D P (sem_g13_nb (os_ptR k))) ∧
      2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card +
        (13 - I.card) ≤ 2 * P.card + Bplus 13 D ∧
      (Iin \ Oc).card ≤ Bzero 13 D := by
  classical
  set I := ineligSet 13 D with hIdef
  set P := sideL \ I
  have hPl : P ⊆ sideL := Finset.sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideL_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (Finset.card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 13 D := fun a ha => by
    by_contra hne; exact (Finset.mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  let Oc := Finset.univ.filter (fun k : Fin 7 =>
    g13_nbB (os_ptR k) ⊆ P ∧ sup_Occ 13 D P (sem_g13_nb (os_ptR k)))
  obtain ⟨m, hm⟩ := exists_maskFin7 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g13_nbB (os_ptR k)).card = 3)
  let Oc2 := Oc.filter (fun k => (g13_nbB (os_ptR k)).card = 2)
  let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
  let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ g13_nbB (os_ptR k) ⊆ P)
  have hcnt := g13_count h hD P hPi hP7 hPe (Oc3.image os_ptR) (Oc2.image os_ptR) (Ct.image os_ptR)
    (Iin.image os_ptR)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g13_nb_eq]; exact ⟨hko.2.1, hk.2, g13_nb_eq _ ▸ hko.2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter] at hk
      have hko := Finset.mem_filter.1 hk.1
      rw [g13_nb_eq]; exact ⟨hko.2.1, hk.2, g13_nb_eq _ ▸ hko.2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have hnk : k ∉ Oc := (Finset.mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hsub hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h3
        rw [os_ptR_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 h2
        rw [os_ptR_inj heq] at hk'; exact hnk (Finset.mem_filter.1 hk').1
      · exact hnk (Finset.mem_filter.2 ⟨Finset.mem_univ k, g13_nb_eq _ ▸ hsub, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      have hki := (Finset.mem_filter.1 hk).2
      exact ⟨hki.1, g13_nb_eq _ ▸ hki.2⟩)
  have hlost := g13_lost h hD P hPi ((Iin \ Oc).image os_ptR)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_sdiff] at hk
      have hki := (Finset.mem_filter.1 hk.1).2
      refine ⟨hki.1, g13_nb_eq _ ▸ hki.2, fun hocc => hk.2 ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hki.2, hocc⟩)
  rw [Finset.card_image_of_injective _ os_ptR_inj] at hlost
  rw [Finset.card_image_of_injective _ os_ptR_inj, Finset.card_image_of_injective _ os_ptR_inj,
    Finset.card_image_of_injective _ os_ptR_inj] at hcnt
  have hLabEq : ((Ct.image os_ptR).biUnion (fun c => sem_g13_nb c ∩ P)) =
      Ct.biUnion (fun k => g13_nbB (os_ptR k) ∩ P) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter, g13_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptR k, ⟨k, hk, rfl⟩, hx⟩
  have hUeq : (∃ v ∈ Oc3.image os_ptR ∪ Oc2.image os_ptR, v ∉ ineligSet 13 D) ↔
      (∃ k ∈ Oc, os_ptR k ∉ I) := by
    constructor
    · rintro ⟨v, hv, hvn⟩
      rcases Finset.mem_union.1 hv with h3 | h2
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h3
        exact ⟨k, (Finset.mem_filter.1 hk).1, hvn⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
        exact ⟨k, (Finset.mem_filter.1 hk).1, hvn⟩
    · rintro ⟨k, hk, hkn⟩
      rcases degree_two_or_three (os_ptR k) with hd2 | hd3
      · exact ⟨os_ptR k, Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨hk, hd2⟩, rfl⟩), hkn⟩
      · exact ⟨os_ptR k, Finset.mem_union_left _ (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨hk, hd3⟩, rfl⟩), hkn⟩
  rw [hLabEq] at hcnt
  simp only [hUeq] at hcnt
  have hel := inelig_card_add 13 D
  rw [← hIdef] at hel
  refine ⟨fun k hk => (Finset.mem_filter.1 hk).2.1, fun k hk => (Finset.mem_filter.1 hk).2.2, ?_, hlost⟩
  change 2 * Oc3.card + Oc2.card + Iin.card +
    (if (Ct.biUnion (fun k => g13_nbB (os_ptR k) ∩ P)) = ∅ ∧ (∃ k ∈ Oc, os_ptR k ∉ I) then 1 else 0) +
    (Ct.biUnion (fun k => g13_nbB (os_ptR k) ∩ P)).card + (13 - I.card) ≤ 2 * P.card + Bplus 13 D
  omega

def ru (D : Dag) (b : Fin 13 → ℕ) (x : Fin 13) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 13 D b).filter (fun u => x ∈ supp 13 D u.1)

theorem cc_le {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (b : Fin 13 → ℕ)
    (hb : PureBranch 13 D b) (x : Fin 13) :
    (sem_W 13 D x).card + (merges 13 D (carrierT 13 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_g13_gr h (sem_g13_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 13)) ∩ eligSet 13 D ⊆ {x})
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

theorem as_mem {D : Dag} {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {i a : Fin 13} (hi : i ∈ ineligSet 13 D) (hia : Adj i a) : pos i ∈ sem_W 13 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

theorem as_priv {D : Dag} {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {i t : Fin 13} (hi : i ∈ ineligSet 13 D) (ht : sem_bar (pos i) ∈ sem_W 13 D t) : t = i := by
  have := (sem_mem_W.1 ht).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at this
  exact Finset.mem_singleton.1 this

theorem as_W {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {pos : Fin 13 → ℕ × Bool}
    (hpos : k4_Pos 13 G13 D pos) {i : Fin 13} (hi : i ∈ ineligSet 13 D) :
    sem_W 13 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, -, -, -, h6, -⟩ :=
    sem_inelig_consumer sem_g13_gr h (sem_g13_comp hD) hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 13 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 13 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem full_g13 {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hB0 : Bzero 13 D = 0)
    {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos) {i v : Fin 13}
    (hi : i ∈ ineligSet 13 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 13 D v, p.1 ≠ (pos i).1 → ¬ supp 13 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 13 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_g13_gr h (sem_g13_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
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

theorem pa_four {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : s.card ≤ 4) : ∀ e ∈ s, e = a ∨ e = b ∨ e = c ∨ e = d := by
  intro e he
  by_contra hne
  rw [not_or, not_or, not_or] at hne
  have := pa_card5 he ha hb hc hd hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 hab hac had hbc hbd hcd
  omega

theorem pa_two {α : Type} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hs : s.card ≤ 2) : ∀ e ∈ s, e = a ∨ e = b := by
  intro e he
  by_contra hne
  rw [not_or] at hne
  have := pa_card3 he ha hb hne.1 hne.2 hab
  omega

theorem pa_ed {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {pos : Fin 13 → ℕ × Bool}
    (hpos : k4_Pos 13 G13 D pos) {x y : Fin 13} (hxy : Adj x y) :
    ∃ e ∈ sem_W 13 D x, sem_bar e ∈ sem_W 13 D y ∧
      (∀ i ∈ ineligSet 13 D, e = pos i → y = i) ∧
      ∀ i ∈ ineligSet 13 D, sem_bar e = pos i → x = i := by
  obtain ⟨e, he, hb, -⟩ := sem_edge_slots sem_g13_gr h.1 (sem_g13_comp hD) hxy
  exact ⟨e, he, hb, fun i hi hei => as_priv hpos hi (hei ▸ hb),
    fun i hi hei => as_priv hpos hi (by rw [← hei, sem_bar_bar]; exact he)⟩

theorem g13_deg3_third : ∀ x a b : Fin 13, (g13_nbB x).card = 3 →
    x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem g13_deg3_cover_free {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {x a b : Fin 13}
    (hd : (g13_nbB x).card = 3) (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 13 D x ∧ a ∉ supp 13 D (src D e) ∧ b ∉ supp 13 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := g13_deg3_third x a b hd hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_g13_gr h.1 (sem_g13_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

theorem ps_nonadj {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {pos : Fin 13 → ℕ × Bool}
    (hpos : k4_Pos 13 G13 D pos) {i x r : Fin 13} (hi : i ∈ ineligSet 13 D)
    (hix : Adj i x) (hir : Adj i r) (hrx : r ≠ x) (hdx : (g13_nbB x).card = 3)
    (hc : (sem_W 13 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 13 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → ¬ Adj r t → Z ∉ sem_W 13 D t := by
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain sem_g13_gr h.1 (sem_g13_comp hD) (x := x) (a := r) (Ne.symm hrx)
  have hY : pos i ∈ sem_W 13 D x := as_mem hpos hi hix
  have hZY : Z ≠ pos i := fun heq => hZr (heq ▸ (hpos.1 i hi).2.2.1 r hir)
  have hW : sem_W 13 D x = {pos i, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  refine ⟨Z, hZY, hW, fun t htx hrt hZt => ?_⟩
  obtain ⟨f, hf, h1, h2⟩ := g13_deg3_cover_free h hD hdx (Ne.symm hrx) (Ne.symm htx) hrt
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · exact h1 ((hpos.1 i hi).2.2.1 r hir)
  · exact h2 (sem_mem_W.1 hZt).2.1

theorem ps_side {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {pos : Fin 13 → ℕ × Bool}
    (hpos : k4_Pos 13 G13 D pos) {i x : Fin 13} (hi : i ∈ ineligSet 13 D)
    (hix : Adj i x) (hdx : (g13_nbB x).card = 3) (hc : (sem_W 13 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 13 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → decide (t.val < 6) = decide (x.val < 6) → Z ∉ sem_W 13 D t := by
  obtain ⟨r, hir, hrx⟩ := sem_g13_gr.2.2.2 i x
  obtain ⟨Z, hZY, hW, hp⟩ := ps_nonadj h hD hpos hi hix hir hrx hdx hc
  refine ⟨Z, hZY, hW, fun t htx hside => hp t htx (fun hadj => ?_)⟩
  have s1 := g13_sides i x ((hc_adjB_iff i x).2 hix)
  have s2 := g13_sides i r ((hc_adjB_iff i r).2 hir)
  have s3 := g13_sides r t ((hc_adjB_iff r t).2 hadj)
  cases h1 : decide (i.val < 6) <;> cases h2 : decide (x.val < 6) <;>
    cases h3 : decide (r.val < 6) <;> cases h4 : decide (t.val < 6) <;> simp_all

theorem two_in_deg3 {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {pos : Fin 13 → ℕ × Bool}
    (hpos : k4_Pos 13 G13 D pos) {i1 i2 u v : Fin 13}
    (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) : 3 ≤ (sem_W 13 D u).card := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  by_cases hv : v ∈ ineligSet 13 D
  · exact pa_card3 p1 p2 (as_mem hpos hv (adj_symm h3)) p12
      (fun e => hv1.symm (hpos.2 i1 hi1 v hv e)) (fun e => hv2.symm (hpos.2 i2 hi2 v hv e))
  · obtain ⟨e, he, -, hf, -⟩ := pa_ed h hD hpos h3
    exact pa_card3 p1 p2 he p12 (fun hh => hv (hf i1 hi1 hh.symm ▸ hi1))
      (fun hh => hv (hf i2 hi2 hh.symm ▸ hi2))

theorem full_of_two_in_deg3 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB0 : Bzero 13 D = 0) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {i1 i2 u v : Fin 13} (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) (hcu : (sem_W 13 D u).card ≤ 3) :
    (∀ t, t ∈ supp 13 D (src D (pos i1)) → Adj i1 t) ∧
    (∀ t, t ∈ supp 13 D (src D (pos i2)) → Adj i2 t) := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have hfull : ∀ (ia ib : Fin 13), ia ∈ ineligSet 13 D → ib ∈ ineligSet 13 D → ia ≠ ib →
      Adj ia u → Adj ib u → v ≠ ia → v ≠ ib →
      ∀ t, t ∈ supp 13 D (src D (pos ia)) → Adj ia t := by
    intro ia ib hia hib hab hiau hibu hvia hvib t ht
    have pa := as_mem hpos hia hiau
    have pb := as_mem hpos hib hibu
    have pab : pos ia ≠ pos ib := fun e => hab (hpos.2 ia hia ib hib e)
    have hspec : ∀ t, t ∈ supp 13 D (src D (pos ia)) ↔ Adj ia t := by
      refine full_g13 h hD hB0 hpos hia hiau (fun p hp hne1 hsub => ?_)
      by_cases hv : v ∈ ineligSet 13 D
      · have pv := as_mem hpos hv (adj_symm h3)
        have pav : pos ia ≠ pos v := fun e => hvia.symm (hpos.2 ia hia v hv e)
        have pbv : pos ib ≠ pos v := fun e => hvib.symm (hpos.2 ib hib v hv e)
        rcases pa_three pa pb pv pab pav pbv hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ib ∈ supp 13 D (src D (sem_bar (pos ib))) := by
            rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl,
              (hpos.1 ib hib).2.2.2]; exact Finset.mem_singleton_self ib
          exact hab.symm (Finset.mem_singleton.1 (hsub hm))
        · have hm : v ∈ supp 13 D (src D (sem_bar (pos v))) := by
            rw [show src D (sem_bar (pos v)) = src D ((pos v).1, !(pos v).2) from rfl,
              (hpos.1 v hv).2.2.2]; exact Finset.mem_singleton_self v
          exact hvia (Finset.mem_singleton.1 (hsub hm))
      · obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos h3
        have pae : pos ia ≠ e := fun hh => hv (hf ia hia hh.symm ▸ hia)
        have pbe : pos ib ≠ e := fun hh => hv (hf ib hib hh.symm ▸ hib)
        rcases pa_three pa pb he pab pae pbe hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ib ∈ supp 13 D (src D (sem_bar (pos ib))) := by
            rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl,
              (hpos.1 ib hib).2.2.2]; exact Finset.mem_singleton_self ib
          exact hab.symm (Finset.mem_singleton.1 (hsub hm))
        · exact hv (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hia)
    exact (hspec t).1 ht
  exact ⟨hfull i1 i2 hi1 hi2 hne h1 h2 hv1 hv2, hfull i2 i1 hi2 hi1 hne.symm h2 h1 hv2 hv1⟩

theorem pa_m1 {D : Dag} (h : StrictLive 13 D) (hD : Correct D) {pos : Fin 13 → ℕ × Bool}
    (hpos : k4_Pos 13 G13 D pos) (z k v iz ik : Fin 13)
    (hiz : iz ∈ ineligSet 13 D) (hik : ik ∈ ineligSet 13 D)
    (hz : z ∉ ineligSet 13 D) (hk : k ∉ ineligSet 13 D) (hv : v ∉ ineligSet 13 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k ∧ (g13_nbB k).card = 3 ∧
      decide (v.val < 6) = decide (k.val < 6))
    (hcz : (sem_W 13 D z).card ≤ 2) (hck : (sem_W 13 D k).card ≤ 2) : False := by
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

theorem ps_side_3star {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (u k1 k2 v ik1 ik2 : Fin 13)
    (hik1 : ik1 ∈ ineligSet 13 D) (hik2 : ik2 ∈ ineligSet 13 D)
    (hu : u ∉ ineligSet 13 D)
    (hg : hc_adjB u k1 = true ∧ hc_adjB u k2 = true ∧ hc_adjB u v = true ∧
      hc_adjB ik1 k1 = true ∧ hc_adjB ik2 k2 = true ∧
      k1 ≠ k2 ∧ v ≠ k1 ∧ v ≠ k2 ∧
      (g13_nbB k1).card = 3 ∧ (g13_nbB k2).card = 3 ∧
      decide (k1.val < 6) = decide (k2.val < 6) ∧ decide (v.val < 6) = decide (k1.val < 6))
    (hcu : (sem_W 13 D u).card ≤ 2) (hck1 : (sem_W 13 D k1).card ≤ 2)
    (hck2 : (sem_W 13 D k2).card ≤ 2) : False := by
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
    have hD2in : D2 ∈ sem_W 13 D k2 := by rw [hW2]; simp
    exact hp1 k2 hk12.symm hs12.symm (hD12 ▸ hD2in)
  rcases pa_two he1 he2 he12 hcu e3 he3 with rfl | rfl
  · exact hp1 v hvk1 hsv1 (hb1 ▸ hbe3)
  · exact hp2 v hvk2 (hsv1.trans hs12) (hb2 ▸ hbe3)

def tight_wit (idx : Fin 44) : Fin 3 × Fin 13 × Fin 13 × Fin 13 × Fin 13 × Fin 13 × Fin 13 :=
  match idx.val with
  | 0 => (0, 12, 0, 1, 3, 0, 0)
  | 1 => (2, 1, 11, 12, 7, 2, 0)
  | 2 => (1, 0, 12, 8, 6, 1, 0)
  | 3 => (2, 8, 0, 5, 4, 6, 7)
  | 4 => (1, 0, 12, 6, 8, 1, 0)
  | 5 => (0, 0, 6, 8, 12, 0, 0)
  | 6 => (0, 5, 8, 10, 7, 0, 0)
  | 7 => (0, 11, 1, 2, 4, 0, 0)
  | 8 => (0, 12, 0, 1, 3, 0, 0)
  | 9 => (0, 10, 2, 3, 5, 0, 0)
  | 10 => (0, 12, 1, 3, 0, 0, 0)
  | 11 => (1, 0, 8, 12, 6, 4, 0)
  | 12 => (1, 0, 12, 8, 6, 3, 0)
  | 13 => (0, 11, 1, 2, 4, 0, 0)
  | 14 => (0, 0, 6, 8, 12, 0, 0)
  | 15 => (0, 0, 6, 8, 12, 0, 0)
  | 16 => (2, 8, 0, 4, 5, 6, 9)
  | 17 => (0, 5, 8, 10, 7, 0, 0)
  | 18 => (0, 0, 6, 8, 12, 0, 0)
  | 19 => (0, 5, 7, 8, 10, 0, 0)
  | 20 => (0, 2, 10, 11, 6, 0, 0)
  | 21 => (0, 10, 2, 3, 5, 0, 0)
  | 22 => (0, 8, 0, 4, 5, 0, 0)
  | 23 => (0, 11, 1, 4, 2, 0, 0)
  | 24 => (1, 0, 8, 12, 6, 4, 0)
  | 25 => (0, 10, 2, 3, 5, 0, 0)
  | 26 => (0, 0, 6, 8, 12, 0, 0)
  | 27 => (0, 0, 6, 8, 12, 0, 0)
  | 28 => (0, 0, 6, 8, 12, 0, 0)
  | 29 => (0, 0, 6, 8, 12, 0, 0)
  | 30 => (0, 0, 6, 8, 12, 0, 0)
  | 31 => (0, 0, 6, 8, 12, 0, 0)
  | 32 => (0, 0, 6, 8, 12, 0, 0)
  | 33 => (0, 0, 8, 12, 6, 0, 0)
  | 34 => (0, 8, 0, 4, 5, 0, 0)
  | 35 => (0, 8, 4, 5, 0, 0, 0)
  | 36 => (0, 0, 6, 8, 12, 0, 0)
  | 37 => (0, 0, 6, 8, 12, 0, 0)
  | 38 => (0, 0, 6, 8, 12, 0, 0)
  | 39 => (0, 0, 6, 8, 12, 0, 0)
  | 40 => (0, 8, 0, 4, 5, 0, 0)
  | 41 => (0, 0, 6, 8, 12, 0, 0)
  | 42 => (0, 0, 6, 8, 12, 0, 0)
  | _ => (0, 0, 6, 8, 12, 0, 0)

theorem tight_wit_ok : ∀ idx : Fin 44,
    let I := hc_rep idx
    let (m, a, b, c, d, e, f) := tight_wit idx
    if m.val = 0 then
      b ∈ I ∧ c ∈ I ∧ b ≠ c ∧ hc_adjB b a = true ∧ hc_adjB c a = true ∧
        hc_adjB a d = true ∧ d ≠ b ∧ d ≠ c
    else if m.val = 1 then
      d ∈ I ∧ e ∈ I ∧ a ∉ I ∧ b ∉ I ∧ c ∉ I ∧
        hc_adjB d a = true ∧ hc_adjB e b = true ∧ hc_adjB a b = true ∧
        hc_adjB a c = true ∧ c ≠ b ∧ (g13_nbB b).card = 3 ∧
        decide (c.val < 6) = decide (b.val < 6)
    else
      e ∈ I ∧ f ∈ I ∧ a ∉ I ∧
        hc_adjB a b = true ∧ hc_adjB a c = true ∧ hc_adjB a d = true ∧
        hc_adjB e b = true ∧ hc_adjB f c = true ∧
        b ≠ c ∧ d ≠ b ∧ d ≠ c ∧
        (g13_nbB b).card = 3 ∧ (g13_nbB c).card = 3 ∧
        decide (b.val < 6) = decide (c.val < 6) ∧ decide (d.val < 6) = decide (b.val < 6) := by
  decide +kernel

theorem tight_le_all {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB : Bplus 13 D ≤ (eligSet 13 D).card) (idx : Fin 44) (hI : ineligSet 13 D = hc_rep idx) :
    False := by
  classical
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hres : residualUnits 13 D b = ∅ := by
    have h1' := card_residual h.1 b hb
    have h2' := elig_le_Bplus h.1 b hb
    exact Finset.card_eq_zero.1 (by omega)
  have hW2 : ∀ x, (sem_W 13 D x).card ≤ 2 := fun x => by
    have h1' := cc_le h hD b hb x
    unfold ru at h1'
    rw [hres] at h1'
    simp only [Finset.filter_empty, Finset.card_empty] at h1'
    omega
  have hw := tight_wit_ok idx
  dsimp only at hw
  rcases htw : tight_wit idx with ⟨m, a, b', c, d, e, f⟩
  rw [htw] at hw
  fin_cases m
  · simp only [↓reduceIte] at hw
    obtain ⟨hi1, hi2, hg⟩ := hw
    have h3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) hg
    have := hW2 a; omega
  · simp only [↓reduceIte] at hw
    obtain ⟨hd, he, ha, hb', hc', hg⟩ := hw
    exact pa_m1 h hD hpos a b' c d e (hI ▸ hd) (hI ▸ he) (hI ▸ ha) (hI ▸ hb') (hI ▸ hc') hg
      (hW2 a) (hW2 b')
  · simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte] at hw
    obtain ⟨he, hf, ha, hg⟩ := hw
    exact ps_side_3star h hD hpos a b' c d e f (hI ▸ he) (hI ▸ hf) (hI ▸ ha) hg
      (hW2 a) (hW2 b') (hW2 c)

def sideR_dead_idx (k : Fin 11) : Fin 44 :=
  match k.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | 4 => ⟨4, by decide⟩
  | 5 => ⟨5, by decide⟩
  | 6 => ⟨6, by decide⟩
  | 7 => ⟨9, by decide⟩
  | 8 => ⟨21, by decide⟩
  | 9 => ⟨22, by decide⟩
  | _ => ⟨34, by decide⟩

theorem sideR_dead_comb : ∀ k : Fin 11, ∀ m : Fin 64,
    let I := hc_rep (sideR_dead_idx k)
    let P := sideR \ I
    let Oc := maskFin6 m
    (∀ j ∈ Oc, g13_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g13_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g13_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 6)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 6 => os_ptL j ∈ I ∧ g13_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g13_nbB (os_ptL j) ∩ P)
    let extra := if Lab = ∅ ∧ (∃ j ∈ Oc, os_ptL j ∉ I) then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card + (13 - I.card) + (Iin \ Oc).card) ∨
    (11 < (14 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_sideR_dead {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (k : Fin 11)
    (hI : ineligSet 13 D = hc_rep (sideR_dead_idx k)) : False := by
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) (sideR_dead_idx k) hI
  obtain ⟨m, hsub, -, hcnt, hlost⟩ := g13_sideR_step h hD
  have hcomb := sideR_dead_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 13 D
  have hel := inelig_card_add 13 D
  rcases hcomb hsub with h1 | h2 <;> omega

def sideL_dead_idx (k : Fin 12) : Fin 44 :=
  match k.val with
  | 0 => ⟨18, by decide⟩
  | 1 => ⟨20, by decide⟩
  | 2 => ⟨30, by decide⟩
  | 3 => ⟨31, by decide⟩
  | 4 => ⟨32, by decide⟩
  | 5 => ⟨33, by decide⟩
  | 6 => ⟨37, by decide⟩
  | 7 => ⟨38, by decide⟩
  | 8 => ⟨39, by decide⟩
  | 9 => ⟨41, by decide⟩
  | 10 => ⟨42, by decide⟩
  | _ => ⟨43, by decide⟩

theorem sideL_dead_comb : ∀ k : Fin 12, ∀ m : Fin 128,
    let I := hc_rep (sideL_dead_idx k)
    let P := sideL \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g13_nbB (os_ptR j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g13_nbB (os_ptR j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g13_nbB (os_ptR j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptR j ∈ I ∧ g13_nbB (os_ptR j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g13_nbB (os_ptR j) ∩ P)
    let extra := if Lab = ∅ ∧ (∃ j ∈ Oc, os_ptR j ∉ I) then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card + (13 - I.card) + (Iin \ Oc).card) ∨
    (11 < (14 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_sideL_dead {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (k : Fin 12)
    (hI : ineligSet 13 D = hc_rep (sideL_dead_idx k)) : False := by
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) (sideL_dead_idx k) hI
  obtain ⟨m, hsub, -, hcnt, hlost⟩ := g13_sideL_step h hD
  have hcomb := sideL_dead_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 13 D
  have hel := inelig_card_add 13 D
  rcases hcomb hsub with h1 | h2 <;> omega

theorem Lprime_comb : ∀ m : Fin 64,
    let I := hc_rep ⟨40, by decide⟩
    let P := sideR \ I
    let Oc := maskFin6 m
    (∀ j ∈ Oc, g13_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g13_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g13_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 6)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 6 => os_ptL j ∈ I ∧ g13_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g13_nbB (os_ptL j) ∩ P)
    let extra := if Lab = ∅ ∧ (∃ j ∈ Oc, os_ptL j ∉ I) then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card + (13 - I.card) + (Iin \ Oc).card) ∨
    (Oc = Finset.univ ∧ 2 * P.card + 11 = 2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card + (13 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem g13_Lprime_forced {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hlen : D.length ≤ 23) (hI : ineligSet 13 D = sideL) :
    D.length = 23 ∧ Bplus 13 D = 11 ∧ Bzero 13 D = 0 ∧
      ∀ k : Fin 6, sup_Occ 13 D sideR (sem_g13_nb (os_ptL k)) := by
  have hrep40 : hc_rep ⟨40, by decide⟩ = sideL := by decide +kernel
  have hI40 : ineligSet 13 D = hc_rep ⟨40, by decide⟩ := hI.trans hrep40.symm
  obtain ⟨m, hsub, hocc, hcnt, hlost⟩ := g13_sideR_step h hD
  have hcomb := Lprime_comb m
  dsimp only at hcomb hsub hocc hcnt hlost
  rw [← hI40] at hcomb
  have hts := totalSurplus_split 13 D
  have hbud := g13_budget h hlen
  have hPeq : sideR \ ineligSet 13 D = sideR := by rw [hI]; decide +kernel
  rcases hcomb hsub with hbad | ⟨hall, heq⟩
  · omega
  · have hIin0 : (Finset.univ.filter (fun j : Fin 6 => os_ptL j ∈ ineligSet 13 D ∧ g13_nbB (os_ptL j) ⊆ sideR \ ineligSet 13 D) \ maskFin6 m).card = 0 := by
      rw [hall]; simp
    have hB11 : Bplus 13 D = 11 := by omega
    have hB0 : Bzero 13 D = 0 := by omega
    have h23 : D.length = 23 := by omega
    refine ⟨h23, hB11, hB0, fun k => ?_⟩
    have := hocc k (by rw [hall]; exact Finset.mem_univ k)
    rwa [hPeq] at this

def pa_ctx (D : Dag) (pos : Fin 13 → ℕ × Bool) (P Q : ℕ × Bool) : Prop :=
  k4_Pos 13 G13 D pos ∧ (∀ x, (sem_W 13 D x).card ≤ 3) ∧ P ≠ Q ∧
    ∀ x, 3 ≤ (sem_W 13 D x).card → P ∈ sem_W 13 D x ∧ Q ∈ sem_W 13 D x

theorem pa_setup_one {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB : Bplus 13 D = (eligSet 13 D).card + 1) : ∃ pos P Q, pa_ctx D pos P Q := by
  classical
  have hG := sem_g13_gr
  have hC := sem_g13_comp hD
  obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have h1 := card_residual h.1 b hbp
  have hc3 : ∀ x, (sem_W 13 D x).card ≤ 3 := fun x => by
    have h3 := cc_le h hD b hbp x
    have h4 : (ru D b x).card ≤ (residualUnits 13 D b).card := Finset.card_filter_le _ _
    omega
  by_cases hX : (Finset.univ.filter (fun x : Fin 13 => 3 ≤ (sem_W 13 D x).card)).Nonempty
  · obtain ⟨P, Q, hPQ, hall⟩ := sem_common_terminals hG h hC b hb (by omega) _ hX
      (fun x hx => (Finset.mem_filter.1 hx).2)
    exact ⟨pos, P, Q, hpos, hc3, fun hpq => hPQ (hpq ▸ rfl),
      fun x hx => hall x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)⟩
  · refine ⟨pos, (0, false), (0, true), hpos, hc3, by decide, fun x hx => ?_⟩
    exact absurd ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩ hX

theorem res1_setup_c3 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (idx : Fin 44) (hI : ineligSet 13 D = hc_rep idx)
    (hc3 : (ineligSet 13 D).card = 3) :
    Bzero 13 D = 0 ∧ Bplus 13 D = (eligSet 13 D).card + 1 ∧ ∃ pos P Q, pa_ctx D pos P Q := by
  have hel := inelig_card_add 13 D
  have hts := totalSurplus_split 13 D
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) idx hI
  have hB1 : Bplus 13 D = (eligSet 13 D).card + 1 := by omega
  have hB0 : Bzero 13 D = 0 := by omega
  exact ⟨hB0, hB1, pa_setup_one h hD hB1⟩

theorem two_in_deg3_pick_PQ {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB0 : Bzero 13 D = 0) {pos : Fin 13 → ℕ × Bool} {P Q : ℕ × Bool}
    (hctx : pa_ctx D pos P Q) {i1 i2 x v3 : Fin 13}
    (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x v3 = true ∧
      v3 ≠ i1 ∧ v3 ≠ i2) :
    ((∀ t, 3 ≤ (sem_W 13 D t).card → Adj i1 t) ∨
     (∀ t, 3 ≤ (sem_W 13 D t).card → Adj i2 t)) := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  have h3 := two_in_deg3 h hD hpos hi1 hi2 hg
  obtain ⟨hPx, hQx⟩ := hsat x h3
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 hg (hc3 x)
  obtain ⟨hne, h1, h2, h3e, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3e
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  have hpick : pos i1 = P ∨ pos i1 = Q ∨ pos i2 = P ∨ pos i2 = Q := by
    by_contra hno
    push Not at hno
    have h4 := pa_card4 p1 p2 hPx hQx p12 hno.1 hno.2.1 hno.2.2.1 hno.2.2.2 hPQ
    have := hc3 x; omega
  rcases hpick with e | e | e | e
  · exact Or.inl (fun t ht => hf1 t (sem_mem_W.1 (e ▸ (hsat t ht).1)).2.1)
  · exact Or.inl (fun t ht => hf1 t (sem_mem_W.1 (e ▸ (hsat t ht).2)).2.1)
  · exact Or.inr (fun t ht => hf2 t (sem_mem_W.1 (e ▸ (hsat t ht).1)).2.1)
  · exact Or.inr (fun t ht => hf2 t (sem_mem_W.1 (e ▸ (hsat t ht).2)).2.1)

theorem mem_W_of_pos {D : Dag} {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {j t : Fin 13} (hj : j ∈ ineligSet 13 D) (ht : t ∈ supp 13 D (src D (pos j))) :
    pos j ∈ sem_W 13 D t := by
  obtain ⟨h1, h2, -, -⟩ := hpos.1 j hj
  exact sem_mem_W.2 ⟨h1, ht, by rw [h2]; exact Finset.notMem_empty t⟩

theorem pe_co_g13 {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (b : Fin 13 → ℕ)
    (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {v t j q : Fin 13} (hj : j ∈ ineligSet 13 D) (hv : v ∈ eligSet 13 D)
    (hres : ∀ u ∈ residualUnits 13 D b, v ∈ supp 13 D u.1 → t ∈ supp 13 D u.1)
    {w : ℕ} (hw : v ∈ supp 13 D w ∧ t ∈ supp 13 D w)
    (hg : (g13_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 13 D (src D (pos j)) := by
  obtain ⟨hdv, hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_g13_gr h (sem_g13_comp hD) b hb hvt hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := g13_deg3_cover_free h hD hdv hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj).2.2.1 q hjq)))

theorem pe_co_of_sub {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (b : Fin 13 → ℕ)
    (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {v t j q : Fin 13} (hj : j ∈ ineligSet 13 D) (hv : v ∈ eligSet 13 D)
    (hvn : 1 ≤ (ru D b v).card) (hsub : ru D b v ⊆ ru D b t)
    (hg : (g13_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 13 D (src D (pos j)) := by
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D b v).card)
  have hres : ∀ u' ∈ residualUnits 13 D b, v ∈ supp 13 D u'.1 → t ∈ supp 13 D u'.1 :=
    fun u' hu' hv' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', hv'⟩))).2
  have hw : v ∈ supp 13 D u.1 ∧ t ∈ supp 13 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
  exact pe_co_g13 h hD b hb hpos hj hv hres hw hg

theorem ru_sub_excl {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hB0 : Bzero 13 D = 0)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {v i1 i2 v3 t : Fin 13} (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hv : v ∈ eligSet 13 D)
    (hg : (g13_nbB v).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 v = true ∧ hc_adjB i2 v = true ∧
      hc_adjB v v3 = true ∧ v3 ≠ i1 ∧ v3 ≠ i2)
    (hru1 : (ru D b v).card = 1) (hsub : ru D b v ⊆ ru D b t) (hvt : v ≠ t)
    (hq : ∃ q : Fin 13,
      (hc_adjB i1 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i1 t = false) ∨
      (hc_adjB i2 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i2 t = false)) : False := by
  obtain ⟨hdv, hne, h1, h2, h3, hv1, hv2⟩ := hg
  have hcv : (sem_W 13 D v).card ≤ 3 := by
    have := cc_le h hD b hb v; omega
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 ⟨hne, h1, h2, h3, hv1, hv2⟩ hcv
  obtain ⟨q, ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩⟩ := hq
  · exact sem_adjB_false.1 a4 (hf1 t (pe_co_of_sub h hD b hb hpos hi1 hv (by omega) hsub ⟨hdv, h1, a1, hvt, a2, a3⟩))
  · exact sem_adjB_false.1 a4 (hf2 t (pe_co_of_sub h hD b hb hpos hi2 hv (by omega) hsub ⟨hdv, h2, a1, hvt, a2, a3⟩))

theorem elim_adj_w3_p1 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB1 : Bplus 13 D = (eligSet 13 D).card + 1)
    (x y ix1 ix2 iy1 iy2 : Fin 13)
    (hix1 : ix1 ∈ ineligSet 13 D) (hix2 : ix2 ∈ ineligSet 13 D)
    (hiy1 : iy1 ∈ ineligSet 13 D) (hiy2 : iy2 ∈ ineligSet 13 D)
    (hx : x ∉ ineligSet 13 D) (hy : y ∉ ineligSet 13 D)
    (hg : ix1 ≠ ix2 ∧ iy1 ≠ iy2 ∧ ix1 ≠ iy1 ∧ ix1 ≠ iy2 ∧ ix2 ≠ iy1 ∧ ix2 ≠ iy2 ∧
      hc_adjB ix1 x = true ∧ hc_adjB ix2 x = true ∧ hc_adjB iy1 y = true ∧ hc_adjB iy2 y = true ∧
      hc_adjB x y = true) : False := by
  obtain ⟨h12, h34, h13, h14, h23, h24, gx1, gx2, gy1, gy2, gxy⟩ := hg
  rw [hc_adjB_iff] at gx1 gx2 gy1 gy2 gxy
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨H, hHx, hHy, hfy, hfx⟩ := pa_ed h hD hpos gxy
  have px1 := as_mem hpos hix1 gx1; have px2 := as_mem hpos hix2 gx2
  have py1 := as_mem hpos hiy1 gy1; have py2 := as_mem hpos hiy2 gy2
  have nx : pos ix1 ≠ pos ix2 := fun e => h12 (hpos.2 _ hix1 _ hix2 e)
  have ny : pos iy1 ≠ pos iy2 := fun e => h34 (hpos.2 _ hiy1 _ hiy2 e)
  have hx1H : pos ix1 ≠ H := fun e => hy (hfy _ hix1 e.symm ▸ hix1)
  have hx2H : pos ix2 ≠ H := fun e => hy (hfy _ hix2 e.symm ▸ hix2)
  have hy1H : pos iy1 ≠ sem_bar H := fun e => hx (hfx _ hiy1 e.symm ▸ hiy1)
  have hy2H : pos iy2 ≠ sem_bar H := fun e => hx (hfx _ hiy2 e.symm ▸ hiy2)
  have hWx := pa_three px1 px2 hHx nx hx1H hx2H (hc3 x)
  have hWy := pa_three py1 py2 hHy ny hy1H hy2H (hc3 y)
  have h3x := pa_card3 px1 px2 hHx nx hx1H hx2H
  have h3y := pa_card3 py1 py2 hHy ny hy1H hy2H
  have hdisj : ∀ e ∈ sem_W 13 D x, e ∉ sem_W 13 D y := by
    intro e hex hey
    rcases hWx e hex with rfl | rfl | rfl <;> rcases hWy _ hey with he | he | he
    · exact h13 (hpos.2 _ hix1 _ hiy1 he)
    · exact h14 (hpos.2 _ hix1 _ hiy2 he)
    · exact hx (hfx _ hix1 he.symm ▸ hix1)
    · exact h23 (hpos.2 _ hix2 _ hiy1 he)
    · exact h24 (hpos.2 _ hix2 _ hiy2 he)
    · exact hx (hfx _ hix2 he.symm ▸ hix2)
    · exact hy (hfy _ hiy1 he ▸ hiy1)
    · exact hy (hfy _ hiy2 he ▸ hiy2)
    · exact w_bar h.1 hHx (he ▸ hHx)
  exact hdisj P (hsat x h3x).1 (hsat y h3y).1

theorem elim_tri_w3_p1 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB1 : Bplus 13 D = (eligSet 13 D).card + 1)
    (x y z i1 i2 i3 vx vy vz : Fin 13)
    (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D) (hi3 : i3 ∈ ineligSet 13 D)
    (hvx : vx ∉ ineligSet 13 D) (hvy : vy ∉ ineligSet 13 D) (hvz : vz ∉ ineligSet 13 D)
    (hg : i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 ∧
      hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB i1 y = true ∧ hc_adjB i3 y = true ∧ hc_adjB y vy = true ∧
      hc_adjB i2 z = true ∧ hc_adjB i3 z = true ∧ hc_adjB z vz = true) : False := by
  obtain ⟨h12, h13, h23, gx1, gx2, gxv, gy1, gy3, gyv, gz2, gz3, gzv⟩ := hg
  rw [hc_adjB_iff] at gx1 gx2 gxv gy1 gy3 gyv gz2 gz3 gzv
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨Hx, hHx, -, hfx, -⟩ := pa_ed h hD hpos gxv
  obtain ⟨Hy, hHy, -, hfy, -⟩ := pa_ed h hD hpos gyv
  obtain ⟨Hz, hHz, -, hfz, -⟩ := pa_ed h hD hpos gzv
  have px1 := as_mem hpos hi1 gx1; have px2 := as_mem hpos hi2 gx2
  have py1 := as_mem hpos hi1 gy1; have py3 := as_mem hpos hi3 gy3
  have pz2 := as_mem hpos hi2 gz2; have pz3 := as_mem hpos hi3 gz3
  have n12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 _ hi1 _ hi2 e)
  have n13 : pos i1 ≠ pos i3 := fun e => h13 (hpos.2 _ hi1 _ hi3 e)
  have n23 : pos i2 ≠ pos i3 := fun e => h23 (hpos.2 _ hi2 _ hi3 e)
  have hx1 : pos i1 ≠ Hx := fun e => hvx (hfx _ hi1 e.symm ▸ hi1)
  have hx2 : pos i2 ≠ Hx := fun e => hvx (hfx _ hi2 e.symm ▸ hi2)
  have hy1 : pos i1 ≠ Hy := fun e => hvy (hfy _ hi1 e.symm ▸ hi1)
  have hy3 : pos i3 ≠ Hy := fun e => hvy (hfy _ hi3 e.symm ▸ hi3)
  have hz2 : pos i2 ≠ Hz := fun e => hvz (hfz _ hi2 e.symm ▸ hi2)
  have hz3 : pos i3 ≠ Hz := fun e => hvz (hfz _ hi3 e.symm ▸ hi3)
  have hWx := pa_three px1 px2 hHx n12 hx1 hx2 (hc3 x)
  have hWy := pa_three py1 py3 hHy n13 hy1 hy3 (hc3 y)
  have hWz := pa_three pz2 pz3 hHz n23 hz2 hz3 (hc3 z)
  have h3x := pa_card3 px1 px2 hHx n12 hx1 hx2
  have h3y := pa_card3 py1 py3 hHy n13 hy1 hy3
  have h3z := pa_card3 pz2 pz3 hHz n23 hz2 hz3
  have honly : ∀ e, e ∈ sem_W 13 D x → e ∈ sem_W 13 D y → e ∈ sem_W 13 D z → e = Hx := by
    intro e hex hey hez
    rcases hWx e hex with rfl | rfl | rfl
    · rcases hWz _ hez with h | h | h
      · exact absurd h n12
      · exact absurd h n13
      · exact absurd (hfz _ hi1 h.symm ▸ hi1) hvz
    · rcases hWy _ hey with h | h | h
      · exact absurd h.symm n12
      · exact absurd h n23
      · exact absurd (hfy _ hi2 h.symm ▸ hi2) hvy
    · rfl
  exact hPQ ((honly P (hsat x h3x).1 (hsat y h3y).1 (hsat z h3z).1).trans
    (honly Q (hsat x h3x).2 (hsat y h3y).2 (hsat z h3z).2).symm)

theorem elim_share_w3_ps_p1 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB1 : Bplus 13 D = (eligSet 13 D).card + 1)
    (x y i0 i1 i2 vx vy iv : Fin 13)
    (hi0 : i0 ∈ ineligSet 13 D) (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hiv : iv ∈ ineligSet 13 D) (hvx : vx ∉ ineligSet 13 D) (hvy : vy ∉ ineligSet 13 D)
    (hg : i0 ≠ i1 ∧ i0 ≠ i2 ∧ i1 ≠ i2 ∧ vx ≠ vy ∧
      hc_adjB i0 x = true ∧ hc_adjB i1 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB i0 y = true ∧ hc_adjB i2 y = true ∧ hc_adjB y vy = true ∧
      hc_adjB iv vx = true ∧ (g13_nbB vx).card = 3 ∧
      decide (vy.val < 6) = decide (vx.val < 6)) : False := by
  obtain ⟨h01, h02, h12, hvxy, gx0, gx1, gxv, gy0, gy2, gyv, giv, hdvx, hsv⟩ := hg
  rw [hc_adjB_iff] at gx0 gx1 gxv gy0 gy2 gyv giv
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨Hx, hHx, hbx, hfx, hfx'⟩ := pa_ed h hD hpos gxv
  obtain ⟨Hy, hHy, hby, hfy, -⟩ := pa_ed h hD hpos gyv
  have px0 := as_mem hpos hi0 gx0; have px1 := as_mem hpos hi1 gx1
  have py0 := as_mem hpos hi0 gy0; have py2 := as_mem hpos hi2 gy2
  have n01 : pos i0 ≠ pos i1 := fun e => h01 (hpos.2 _ hi0 _ hi1 e)
  have n02 : pos i0 ≠ pos i2 := fun e => h02 (hpos.2 _ hi0 _ hi2 e)
  have n12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 _ hi1 _ hi2 e)
  have hx0 : pos i0 ≠ Hx := fun e => hvx (hfx _ hi0 e.symm ▸ hi0)
  have hx1 : pos i1 ≠ Hx := fun e => hvx (hfx _ hi1 e.symm ▸ hi1)
  have hy0 : pos i0 ≠ Hy := fun e => hvy (hfy _ hi0 e.symm ▸ hi0)
  have hy2 : pos i2 ≠ Hy := fun e => hvy (hfy _ hi2 e.symm ▸ hi2)
  have hWx := pa_three px0 px1 hHx n01 hx0 hx1 (hc3 x)
  have hWy := pa_three py0 py2 hHy n02 hy0 hy2 (hc3 y)
  have h3x := pa_card3 px0 px1 hHx n01 hx0 hx1
  have h3y := pa_card3 py0 py2 hHy n02 hy0 hy2
  have hxy_in : ∀ e, e ∈ sem_W 13 D x → e ∈ sem_W 13 D y → e = pos i0 ∨ (e = Hx ∧ Hx = Hy) := by
    intro e hex hey
    rcases hWx e hex with rfl | rfl | rfl
    · exact Or.inl rfl
    · rcases hWy _ hey with h | h | h
      · exact absurd h.symm n01
      · exact absurd h n12
      · exact absurd (hfy _ hi1 h.symm ▸ hi1) hvy
    · rcases hWy _ hey with h | h | h
      · exact absurd h.symm hx0
      · exact absurd (hfx _ hi2 h ▸ hi2) hvx
      · exact Or.inr ⟨rfl, h⟩
  have hHxEq : (P = Hx ∨ Q = Hx) ∧ Hx = Hy := by
    rcases hxy_in P (hsat x h3x).1 (hsat y h3y).1 with hP0 | ⟨hPH, hxy⟩
    · rcases hxy_in Q (hsat x h3x).2 (hsat y h3y).2 with hQ0 | ⟨hQH, hxy⟩
      · exact absurd (hP0.trans hQ0.symm) hPQ
      · exact ⟨Or.inr hQH, hxy⟩
    · exact ⟨Or.inl hPH, hxy⟩
  have hcvx : (sem_W 13 D vx).card ≤ 2 := by
    by_contra hlt
    have hge : 3 ≤ (sem_W 13 D vx).card := by omega
    have hHin : Hx ∈ sem_W 13 D vx := by
      rcases hHxEq.1 with rfl | rfl
      · exact (hsat vx hge).1
      · exact (hsat vx hge).2
    exact w_bar h.1 hHin hbx
  obtain ⟨Z, -, hWvx, hpvx⟩ := ps_side h hD hpos hiv giv hdvx hcvx
  have hbxZ : sem_bar Hx = Z := by
    rw [hWvx, Finset.mem_insert, Finset.mem_singleton] at hbx
    exact hbx.resolve_left (fun hh => by
      have hxI : x = iv := hfx' iv hiv hh
      have hxnot : x ∉ ineligSet 13 D := fun hxin =>
        (g13_cover_iff_indep D).1 (elig_isCover h hD) _ hxin _ hi0 (adj_symm gx0)
      exact hxnot (hxI ▸ hiv))
  exact hpvx vy hvxy.symm hsv (by rw [← hbxZ, hHxEq.2]; exact hby)

theorem elim_no_i0_pa {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (idx : Fin 44) (hI : ineligSet 13 D = hc_rep idx)
    (hc3 : (ineligSet 13 D).card = 3)
    (x i1 i2 v3 : Fin 13)
    (z1 k1 w1 iz1 ik1 : Fin 13) (z2 k2 w2 iz2 ik2 : Fin 13)
    (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hiz1 : iz1 ∈ ineligSet 13 D) (hik1 : ik1 ∈ ineligSet 13 D)
    (hz1 : z1 ∉ ineligSet 13 D) (hk1 : k1 ∉ ineligSet 13 D) (hw1 : w1 ∉ ineligSet 13 D)
    (hiz2 : iz2 ∈ ineligSet 13 D) (hik2 : ik2 ∈ ineligSet 13 D)
    (hz2 : z2 ∉ ineligSet 13 D) (hk2 : k2 ∉ ineligSet 13 D) (hw2 : w2 ∉ ineligSet 13 D)
    (hg : (i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x v3 = true ∧ v3 ≠ i1 ∧ v3 ≠ i2) ∧
      (hc_adjB i1 z1 = false ∧ hc_adjB i1 k1 = false ∧
       hc_adjB iz1 z1 = true ∧ hc_adjB ik1 k1 = true ∧ hc_adjB z1 k1 = true ∧
       hc_adjB z1 w1 = true ∧ w1 ≠ k1 ∧ (g13_nbB k1).card = 3 ∧ decide (w1.val < 6) = decide (k1.val < 6)) ∧
      (hc_adjB i2 z2 = false ∧ hc_adjB i2 k2 = false ∧
       hc_adjB iz2 z2 = true ∧ hc_adjB ik2 k2 = true ∧ hc_adjB z2 k2 = true ∧
       hc_adjB z2 w2 = true ∧ w2 ≠ k2 ∧ (g13_nbB k2).card = 3 ∧ decide (w2.val < 6) = decide (k2.val < 6))) : False := by
  obtain ⟨hB0, -, pos, P, Q, hctx⟩ := res1_setup_c3 h hD h11 idx hI hc3
  obtain ⟨hgx, ⟨hnz1, hnk1, hgp1⟩, ⟨hnz2, hnk2, hgp2⟩⟩ := hg
  rcases two_in_deg3_pick_PQ h hD hB0 hctx hi1 hi2 hgx with hall | hall
  · have hcz : (sem_W 13 D z1).card ≤ 2 := by by_contra hlt; exact sem_adjB_false.1 hnz1 (hall z1 (by omega))
    have hck : (sem_W 13 D k1).card ≤ 2 := by by_contra hlt; exact sem_adjB_false.1 hnk1 (hall k1 (by omega))
    exact pa_m1 h hD hctx.1 z1 k1 w1 iz1 ik1 hiz1 hik1 hz1 hk1 hw1 hgp1 hcz hck
  · have hcz : (sem_W 13 D z2).card ≤ 2 := by by_contra hlt; exact sem_adjB_false.1 hnz2 (hall z2 (by omega))
    have hck : (sem_W 13 D k2).card ≤ 2 := by by_contra hlt; exact sem_adjB_false.1 hnk2 (hall k2 (by omega))
    exact pa_m1 h hD hctx.1 z2 k2 w2 iz2 ik2 hiz2 hik2 hz2 hk2 hw2 hgp2 hcz hck

theorem two_diff_I_kill {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hB0 : Bzero 13 D = 0)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {a c ia ic qa qc va : Fin 13}
    (ha : a ∈ eligSet 13 D) (hc : c ∈ eligSet 13 D)
    (hia : ia ∈ ineligSet 13 D) (hic : ic ∈ ineligSet 13 D) (hva : va ∉ ineligSet 13 D)
    (hg : a ≠ c ∧ ia ≠ ic ∧ (g13_nbB a).card = 3 ∧ (g13_nbB c).card = 3 ∧
      hc_adjB ia a = true ∧ hc_adjB ic c = true ∧ hc_adjB a va = true ∧
      hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB c qa = false ∧
      hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB a qc = false ∧ hc_adjB ia c = false)
    (han : 1 ≤ (ru D b a).card) (hcn : 1 ≤ (ru D b c).card)
    (hs1 : ru D b a ⊆ ru D b c) (hs2 : ru D b c ⊆ ru D b a) (hWa3 : (sem_W 13 D a).card ≤ 3) : False := by
  obtain ⟨hac, hiac, hda, hdc, gia, gic, gva, gqa, haqa, gcqa, gqc, hcqc, gaqc, gniac⟩ := hg
  have hpc_in_a := mem_W_of_pos hpos hic (pe_co_of_sub h hD b hb hpos hic hc hcn hs2 ⟨hdc, gic, gqc, hac.symm, hcqc, gaqc⟩)
  have hc_in_pa := pe_co_of_sub h hD b hb hpos hia ha han hs1 ⟨hda, gia, gqa, hac, haqa, gcqa⟩
  have hpa := as_mem hpos hia ((hc_adjB_iff _ _).1 gia)
  obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gva)
  have hWa := pa_three hpa hpc_in_a hev
    (fun e => hiac (hpos.2 _ hia _ hic e))
    (fun e => hva (hfv _ hia e.symm ▸ hia))
    (fun e => hva (hfv _ hic e.symm ▸ hic))
    hWa3
  have hfull := full_g13 h hD hB0 hpos hia ((hc_adjB_iff _ _).1 gia) (fun p hp hne1 hsub => by
    rcases hWa p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : ic ∈ supp 13 D (src D (sem_bar (pos ic))) := by
        rw [show src D (sem_bar (pos ic)) = src D ((pos ic).1, !(pos ic).2) from rfl,
          (hpos.1 ic hic).2.2.2]; exact Finset.mem_singleton_self ic
      exact hiac.symm (Finset.mem_singleton.1 (hsub hm))
    · exact hva (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1) ▸ hia))
  exact sem_adjB_false.1 gniac ((hfull c).1 hc_in_pa)

theorem same_side_cap_I {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {P Q : ℕ × Bool} (hPQ : P ≠ Q)
    (a1 a2 i0 u1 u2 v1 v2 iu1 iu2 iv1 iv2 : Fin 13)
    (hi0 : i0 ∈ ineligSet 13 D) (hiu1 : iu1 ∈ ineligSet 13 D) (hiu2 : iu2 ∈ ineligSet 13 D)
    (hiv1 : iv1 ∈ ineligSet 13 D) (hiv2 : iv2 ∈ ineligSet 13 D)
    (ha1 : a1 ∉ ineligSet 13 D) (ha2 : a2 ∉ ineligSet 13 D)
    (hg : hc_adjB i0 a1 = true ∧ hc_adjB i0 a2 = true ∧
      hc_adjB a1 u1 = true ∧ hc_adjB a1 u2 = true ∧
      hc_adjB a2 v1 = true ∧ hc_adjB a2 v2 = true ∧
      hc_adjB iu1 u1 = true ∧ hc_adjB iu2 u2 = true ∧
      hc_adjB iv1 v1 = true ∧ hc_adjB iv2 v2 = true ∧
      (g13_nbB u1).card = 3 ∧ (g13_nbB u2).card = 3 ∧ (g13_nbB v1).card = 3 ∧ (g13_nbB v2).card = 3 ∧
      u1 ≠ u2 ∧ v1 ≠ v2 ∧ u1 ≠ v1 ∧ u1 ≠ v2 ∧ u2 ≠ v1 ∧ u2 ≠ v2 ∧
      decide (u2.val < 6) = decide (u1.val < 6) ∧ decide (v1.val < 6) = decide (u1.val < 6) ∧
      decide (v2.val < 6) = decide (u1.val < 6))
    (hca1 : (sem_W 13 D a1).card ≤ 3) (hca2 : (sem_W 13 D a2).card ≤ 3)
    (hPa1 : P ∈ sem_W 13 D a1) (hQa1 : Q ∈ sem_W 13 D a1)
    (hPa2 : P ∈ sem_W 13 D a2) (hQa2 : Q ∈ sem_W 13 D a2)
    (hcu1 : (sem_W 13 D u1).card ≤ 2) (hcu2 : (sem_W 13 D u2).card ≤ 2)
    (hcv1 : (sem_W 13 D v1).card ≤ 2) (hcv2 : (sem_W 13 D v2).card ≤ 2) : False := by
  obtain ⟨g01, g02, gu1, gu2, gv1, gv2, giu1, giu2, giv1, giv2, hdu1, hdu2, hdv1, hdv2,
    nu12, nv12, nu1v1, nu1v2, nu2v1, nu2v2, hs1, hs2, hs3⟩ := hg
  rw [hc_adjB_iff] at g01 g02 gu1 gu2 gv1 gv2 giu1 giu2 giv1 giv2
  obtain ⟨Du1, -, hWu1, hpu1⟩ := ps_side h hD hpos hiu1 giu1 hdu1 hcu1
  obtain ⟨Du2, -, hWu2, hpu2⟩ := ps_side h hD hpos hiu2 giu2 hdu2 hcu2
  obtain ⟨Dv1, -, hWv1, hpv1⟩ := ps_side h hD hpos hiv1 giv1 hdv1 hcv1
  obtain ⟨Dv2, -, hWv2, hpv2⟩ := ps_side h hD hpos hiv2 giv2 hdv2 hcv2
  obtain ⟨fu1, hfu1, hbu1, hfu1y, hfu1x⟩ := pa_ed h hD hpos gu1
  obtain ⟨fu2, hfu2, hbu2, hfu2y, hfu2x⟩ := pa_ed h hD hpos gu2
  obtain ⟨fv1, hfv1, hbv1, hfv1y, hfv1x⟩ := pa_ed h hD hpos gv1
  obtain ⟨fv2, hfv2, hbv2, hfv2y, hfv2x⟩ := pa_ed h hD hpos gv2
  have hb1 : sem_bar fu1 = Du1 := by rw [hWu1, Finset.mem_insert, Finset.mem_singleton] at hbu1; exact hbu1.resolve_left (fun hh => ha1 (hfu1x _ hiu1 hh ▸ hiu1))
  have hb2 : sem_bar fu2 = Du2 := by rw [hWu2, Finset.mem_insert, Finset.mem_singleton] at hbu2; exact hbu2.resolve_left (fun hh => ha1 (hfu2x _ hiu2 hh ▸ hiu2))
  have hb3 : sem_bar fv1 = Dv1 := by rw [hWv1, Finset.mem_insert, Finset.mem_singleton] at hbv1; exact hbv1.resolve_left (fun hh => ha2 (hfv1x _ hiv1 hh ▸ hiv1))
  have hb4 : sem_bar fv2 = Dv2 := by rw [hWv2, Finset.mem_insert, Finset.mem_singleton] at hbv2; exact hbv2.resolve_left (fun hh => ha2 (hfv2x _ hiv2 hh ▸ hiv2))
  have hDu2_in : Du2 ∈ sem_W 13 D u2 := by rw [hWu2]; simp
  have hDv1_in : Dv1 ∈ sem_W 13 D v1 := by rw [hWv1]; simp
  have hDv2_in : Dv2 ∈ sem_W 13 D v2 := by rw [hWv2]; simp
  have hfu12 : fu1 ≠ fu2 := fun hh => hpu1 u2 nu12.symm hs1 (by rw [← hb1, hh, hb2]; exact hDu2_in)
  have hfv12 : fv1 ≠ fv2 := fun hh => hpv1 v2 nv12.symm (hs3.trans hs2.symm) (by rw [← hb3, hh, hb4]; exact hDv2_in)
  have hu1_ni : u1 ∉ ineligSet 13 D := fun h' => (g13_cover_iff_indep D).1 (elig_isCover h hD) _ h' _ hiu1 (adj_symm giu1)
  have hu2_ni : u2 ∉ ineligSet 13 D := fun h' => (g13_cover_iff_indep D).1 (elig_isCover h hD) _ h' _ hiu2 (adj_symm giu2)
  have hv1_ni : v1 ∉ ineligSet 13 D := fun h' => (g13_cover_iff_indep D).1 (elig_isCover h hD) _ h' _ hiv1 (adj_symm giv1)
  have hv2_ni : v2 ∉ ineligSet 13 D := fun h' => (g13_cover_iff_indep D).1 (elig_isCover h hD) _ h' _ hiv2 (adj_symm giv2)
  have hWa1 := pa_three (as_mem hpos hi0 g01) hfu1 hfu2
    (fun hh => hu1_ni (hfu1y _ hi0 hh.symm ▸ hi0)) (fun hh => hu2_ni (hfu2y _ hi0 hh.symm ▸ hi0)) hfu12 hca1
  have hWa2 := pa_three (as_mem hpos hi0 g02) hfv1 hfv2
    (fun hh => hv1_ni (hfv1y _ hi0 hh.symm ▸ hi0)) (fun hh => hv2_ni (hfv2y _ hi0 hh.symm ▸ hi0)) hfv12 hca2
  have honly : ∀ e, e ∈ sem_W 13 D a1 → e ∈ sem_W 13 D a2 → e = pos i0 := by
    intro e he1 he2
    rcases hWa1 e he1 with rfl | rfl | rfl
    · rfl
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (hfu1y _ hi0 hh ▸ hi0) hu1_ni
      · exact absurd (by rw [← hb1, hh, hb3]; exact hDv1_in) (hpu1 v1 nu1v1.symm hs2)
      · exact absurd (by rw [← hb1, hh, hb4]; exact hDv2_in) (hpu1 v2 nu1v2.symm hs3)
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (hfu2y _ hi0 hh ▸ hi0) hu2_ni
      · exact absurd (by rw [← hb2, hh, hb3]; exact hDv1_in) (hpu2 v1 nu2v1.symm (hs2.trans hs1.symm))
      · exact absurd (by rw [← hb2, hh, hb4]; exact hDv2_in) (hpu2 v2 nu2v2.symm (hs3.trans hs1.symm))
  exact hPQ ((honly P hPa1 hPa2).trans (honly Q hQa1 hQa2).symm)

theorem same_side_cap_free {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    {P Q : ℕ × Bool} (hPQ : P ≠ Q)
    (a1 a2 u1 u2 v1 v2 f1 f2 iu1 iu2 iv1 iv2 : Fin 13)
    (hiu1 : iu1 ∈ ineligSet 13 D) (hiu2 : iu2 ∈ ineligSet 13 D)
    (hiv1 : iv1 ∈ ineligSet 13 D) (hiv2 : iv2 ∈ ineligSet 13 D)
    (ha1 : a1 ∉ ineligSet 13 D) (ha2 : a2 ∉ ineligSet 13 D)
    (hg : hc_adjB a1 u1 = true ∧ hc_adjB a1 u2 = true ∧ hc_adjB a1 f1 = true ∧
      hc_adjB a2 v1 = true ∧ hc_adjB a2 v2 = true ∧ hc_adjB a2 f2 = true ∧
      hc_adjB iu1 u1 = true ∧ hc_adjB iu2 u2 = true ∧
      hc_adjB iv1 v1 = true ∧ hc_adjB iv2 v2 = true ∧
      (g13_nbB u1).card = 3 ∧ (g13_nbB u2).card = 3 ∧ (g13_nbB v1).card = 3 ∧ (g13_nbB v2).card = 3 ∧
      u1 ≠ u2 ∧ v1 ≠ v2 ∧ u1 ≠ v1 ∧ u1 ≠ v2 ∧ u2 ≠ v1 ∧ u2 ≠ v2 ∧
      u1 ≠ f1 ∧ u2 ≠ f1 ∧ u1 ≠ f2 ∧ u2 ≠ f2 ∧ v1 ≠ f1 ∧ v2 ≠ f1 ∧ v1 ≠ f2 ∧ v2 ≠ f2 ∧
      decide (u2.val < 6) = decide (u1.val < 6) ∧ decide (v1.val < 6) = decide (u1.val < 6) ∧
      decide (v2.val < 6) = decide (u1.val < 6) ∧ decide (f1.val < 6) = decide (u1.val < 6) ∧
      decide (f2.val < 6) = decide (u1.val < 6))
    (hca1 : (sem_W 13 D a1).card ≤ 3) (hca2 : (sem_W 13 D a2).card ≤ 3)
    (hPa1 : P ∈ sem_W 13 D a1) (hQa1 : Q ∈ sem_W 13 D a1)
    (hPa2 : P ∈ sem_W 13 D a2) (hQa2 : Q ∈ sem_W 13 D a2)
    (hcu1 : (sem_W 13 D u1).card ≤ 2) (hcu2 : (sem_W 13 D u2).card ≤ 2)
    (hcv1 : (sem_W 13 D v1).card ≤ 2) (hcv2 : (sem_W 13 D v2).card ≤ 2) : False := by
  obtain ⟨gu1, gu2, gf1, gv1, gv2, gf2, giu1, giu2, giv1, giv2, hdu1, hdu2, hdv1, hdv2,
    nu12, nv12, nu1v1, nu1v2, nu2v1, nu2v2, nu1f1, nu2f1, nu1f2, nu2f2, nv1f1, nv2f1, nv1f2, nv2f2,
    hs1, hs2, hs3, hs4, hs5⟩ := hg
  rw [hc_adjB_iff] at gu1 gu2 gf1 gv1 gv2 gf2 giu1 giu2 giv1 giv2
  obtain ⟨Du1, -, hWu1, hpu1⟩ := ps_side h hD hpos hiu1 giu1 hdu1 hcu1
  obtain ⟨Du2, -, hWu2, hpu2⟩ := ps_side h hD hpos hiu2 giu2 hdu2 hcu2
  obtain ⟨Dv1, -, hWv1, hpv1⟩ := ps_side h hD hpos hiv1 giv1 hdv1 hcv1
  obtain ⟨Dv2, -, hWv2, hpv2⟩ := ps_side h hD hpos hiv2 giv2 hdv2 hcv2
  obtain ⟨fu1, hfu1, hbu1, -, hfu1x⟩ := pa_ed h hD hpos gu1
  obtain ⟨fu2, hfu2, hbu2, -, hfu2x⟩ := pa_ed h hD hpos gu2
  obtain ⟨ff1, hff1, hbf1, -, -⟩ := pa_ed h hD hpos gf1
  obtain ⟨fv1, hfv1, hbv1, -, hfv1x⟩ := pa_ed h hD hpos gv1
  obtain ⟨fv2, hfv2, hbv2, -, hfv2x⟩ := pa_ed h hD hpos gv2
  obtain ⟨ff2, hff2, hbf2, -, -⟩ := pa_ed h hD hpos gf2
  have hb1 : sem_bar fu1 = Du1 := by rw [hWu1, Finset.mem_insert, Finset.mem_singleton] at hbu1; exact hbu1.resolve_left (fun hh => ha1 (hfu1x _ hiu1 hh ▸ hiu1))
  have hb2 : sem_bar fu2 = Du2 := by rw [hWu2, Finset.mem_insert, Finset.mem_singleton] at hbu2; exact hbu2.resolve_left (fun hh => ha1 (hfu2x _ hiu2 hh ▸ hiu2))
  have hb3 : sem_bar fv1 = Dv1 := by rw [hWv1, Finset.mem_insert, Finset.mem_singleton] at hbv1; exact hbv1.resolve_left (fun hh => ha2 (hfv1x _ hiv1 hh ▸ hiv1))
  have hb4 : sem_bar fv2 = Dv2 := by rw [hWv2, Finset.mem_insert, Finset.mem_singleton] at hbv2; exact hbv2.resolve_left (fun hh => ha2 (hfv2x _ hiv2 hh ▸ hiv2))
  have hDu2_in : Du2 ∈ sem_W 13 D u2 := by rw [hWu2]; simp
  have hDv1_in : Dv1 ∈ sem_W 13 D v1 := by rw [hWv1]; simp
  have hDv2_in : Dv2 ∈ sem_W 13 D v2 := by rw [hWv2]; simp
  have hWa1 := pa_three hfu1 hfu2 hff1
    (fun hh => hpu1 u2 nu12.symm hs1 (by rw [← hb1, hh, hb2]; exact hDu2_in))
    (fun hh => hpu1 f1 nu1f1.symm hs4 (by rw [← hb1, hh]; exact hbf1))
    (fun hh => hpu2 f1 nu2f1.symm (hs4.trans hs1.symm) (by rw [← hb2, hh]; exact hbf1)) hca1
  have hWa2 := pa_three hfv1 hfv2 hff2
    (fun hh => hpv1 v2 nv12.symm (hs3.trans hs2.symm) (by rw [← hb3, hh, hb4]; exact hDv2_in))
    (fun hh => hpv1 f2 nv1f2.symm (hs5.trans hs2.symm) (by rw [← hb3, hh]; exact hbf2))
    (fun hh => hpv2 f2 nv2f2.symm (hs5.trans hs3.symm) (by rw [← hb4, hh]; exact hbf2)) hca2
  have honly : ∀ e, e ∈ sem_W 13 D a1 → e ∈ sem_W 13 D a2 → e = ff1 := by
    intro e he1 he2
    rcases hWa1 e he1 with rfl | rfl | rfl
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (by rw [← hb1, hh, hb3]; exact hDv1_in) (hpu1 v1 nu1v1.symm hs2)
      · exact absurd (by rw [← hb1, hh, hb4]; exact hDv2_in) (hpu1 v2 nu1v2.symm hs3)
      · exact absurd (by rw [← hb1, hh]; exact hbf2) (hpu1 f2 nu1f2.symm hs5)
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (by rw [← hb2, hh, hb3]; exact hDv1_in) (hpu2 v1 nu2v1.symm (hs2.trans hs1.symm))
      · exact absurd (by rw [← hb2, hh, hb4]; exact hDv2_in) (hpu2 v2 nu2v2.symm (hs3.trans hs1.symm))
      · exact absurd (by rw [← hb2, hh]; exact hbf2) (hpu2 f2 nu2f2.symm (hs5.trans hs1.symm))
    · rfl
  exact hPQ ((honly P hPa1 hPa2).trans (honly Q hQa1 hQa2).symm)

theorem pe_co_blow5_r1 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (a1 a2 c i1 i2 ic1 ic2 vc q1 q2 : Fin 13)
    (ha1 : a1 ∈ eligSet 13 D) (ha2 : a2 ∈ eligSet 13 D)
    (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D)
    (hic1 : ic1 ∈ ineligSet 13 D) (hic2 : ic2 ∈ ineligSet 13 D) (hvc : vc ∉ ineligSet 13 D)
    (hg : a1 ≠ c ∧ a2 ≠ c ∧ i1 ≠ i2 ∧ i1 ≠ ic1 ∧ i1 ≠ ic2 ∧ i2 ≠ ic1 ∧ i2 ≠ ic2 ∧ ic1 ≠ ic2 ∧
      (g13_nbB a1).card = 3 ∧ (g13_nbB a2).card = 3 ∧
      hc_adjB i1 a1 = true ∧ hc_adjB i1 q1 = true ∧ a1 ≠ q1 ∧ hc_adjB c q1 = false ∧
      hc_adjB i2 a2 = true ∧ hc_adjB i2 q2 = true ∧ a2 ≠ q2 ∧ hc_adjB c q2 = false ∧
      hc_adjB ic1 c = true ∧ hc_adjB ic2 c = true ∧ hc_adjB c vc = true)
    (h1n : 1 ≤ (ru D b a1).card) (h2n : 1 ≤ (ru D b a2).card)
    (hs1 : ru D b a1 ⊆ ru D b c) (hs2 : ru D b a2 ⊆ ru D b c) (hcle : (ru D b c).card ≤ 2) : False := by
  obtain ⟨ha1c, ha2c, n12, n1c1, n1c2, n2c1, n2c2, nc12, hd1, hd2,
    ga1, gq1, hq1, gcq1, ga2, gq2, hq2, gcq2, gc1, gc2, gvc⟩ := hg
  have m1 := mem_W_of_pos hpos hi1 (pe_co_of_sub h hD b hb hpos hi1 ha1 h1n hs1 ⟨hd1, ga1, gq1, ha1c, hq1, gcq1⟩)
  have m2 := mem_W_of_pos hpos hi2 (pe_co_of_sub h hD b hb hpos hi2 ha2 h2n hs2 ⟨hd2, ga2, gq2, ha2c, hq2, gcq2⟩)
  have mc1 := as_mem hpos hic1 ((hc_adjB_iff _ _).1 gc1)
  have mc2 := as_mem hpos hic2 ((hc_adjB_iff _ _).1 gc2)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvc)
  have h5 := pa_card5 m1 m2 mc1 mc2 hev
    (fun e => n12 (hpos.2 _ hi1 _ hi2 e)) (fun e => n1c1 (hpos.2 _ hi1 _ hic1 e))
    (fun e => n1c2 (hpos.2 _ hi1 _ hic2 e)) (fun e => hvc (hfv _ hi1 e.symm ▸ hi1))
    (fun e => n2c1 (hpos.2 _ hi2 _ hic1 e)) (fun e => n2c2 (hpos.2 _ hi2 _ hic2 e))
    (fun e => hvc (hfv _ hi2 e.symm ▸ hi2)) (fun e => nc12 (hpos.2 _ hic1 _ hic2 e))
    (fun e => hvc (hfv _ hic1 e.symm ▸ hic1)) (fun e => hvc (hfv _ hic2 e.symm ▸ hic2))
  have hc4 := cc_le h hD b hb c
  omega

theorem sideR_r2_comb : ∀ idx : Fin 44, (idx.val = 25 ∨ idx.val = 35) → ∀ m : Fin 64,
    let I := hc_rep idx
    let P := sideR \ I
    let Oc := maskFin6 m
    (∀ j ∈ Oc, g13_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g13_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g13_nbB (os_ptL j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 6)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 6 => os_ptL j ∈ I ∧ g13_nbB (os_ptL j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g13_nbB (os_ptL j) ∩ P)
    let extra := if Lab = ∅ ∧ (∃ j ∈ Oc, os_ptL j ∉ I) then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card + (13 - I.card) + (Iin \ Oc).card) ∨
    (11 < (15 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem sideL_r2_comb : ∀ idx : Fin 44, (idx.val = 28 ∨ idx.val = 29 ∨ idx.val = 36) → ∀ m : Fin 128,
    let I := hc_rep idx
    let P := sideL \ I
    let Oc := maskFin7 m
    (∀ j ∈ Oc, g13_nbB (os_ptR j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g13_nbB (os_ptR j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g13_nbB (os_ptR j)).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptR j ∈ I ∧ g13_nbB (os_ptR j) ⊆ P)
    let Lab := Ct.biUnion (fun j => g13_nbB (os_ptR j) ∩ P)
    let extra := if Lab = ∅ ∧ (∃ j ∈ Oc, os_ptR j ∉ I) then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + extra + Lab.card + (13 - I.card) + (Iin \ Oc).card) ∨
    (11 < (15 - I.card) + (Iin \ Oc).card) := by
  decide +kernel

theorem elim_sideR_r2 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (idx : Fin 44) (hI : ineligSet 13 D = hc_rep idx)
    (hidx : idx.val = 25 ∨ idx.val = 35) (hB2 : (eligSet 13 D).card + 2 ≤ Bplus 13 D) : False := by
  obtain ⟨m, hsub, -, hcnt, hlost⟩ := g13_sideR_step h hD
  have hcomb := sideR_r2_comb idx hidx m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 13 D
  have hel := inelig_card_add 13 D
  rcases hcomb hsub with h1 | h2 <;> omega

theorem elim_sideL_r2 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (idx : Fin 44) (hI : ineligSet 13 D = hc_rep idx)
    (hidx : idx.val = 28 ∨ idx.val = 29 ∨ idx.val = 36) (hB2 : (eligSet 13 D).card + 2 ≤ Bplus 13 D) : False := by
  obtain ⟨m, hsub, -, hcnt, hlost⟩ := g13_sideL_step h hD
  have hcomb := sideL_r2_comb idx hidx m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 13 D
  have hel := inelig_card_add 13 D
  rcases hcomb hsub with h1 | h2 <;> omega

theorem elim_7 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨7, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {0, 1, 2} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({0, 1, 2} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, -⟩ := res1_setup_c3 h hD h11 ⟨7, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have h11n : 1 ≤ (ru D b 11).card := by
    have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (1 : Fin 13) ∈ _) (by rw [hIeq]; decide : (2 : Fin 13) ∈ _) (u := 11) (v := 4) (by decide)
    have := cc_le h hD b hb 11; omega
  have h12n : 1 ≤ (ru D b 12).card := by
    have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (0 : Fin 13) ∈ _) (by rw [hIeq]; decide : (1 : Fin 13) ∈ _) (u := 12) (v := 3) (by decide)
    have := cc_le h hD b hb 12; omega
  have h11eq : ru D b 11 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have h12eq : ru D b 12 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  exact ru_sub_excl h hD hB0 b hb hpos (i1 := 1) (i2 := 2) (t := 12) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (hE 11 (by decide)) (v3 := 4) (by decide) (by rw [h11eq, hR1]) (by rw [h11eq, h12eq])
    (by decide) ⟨10, Or.inr (by decide)⟩

theorem elim_15 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨15, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {6, 7, 8} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({6, 7, 8} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, -⟩ := res1_setup_c3 h hD h11 ⟨15, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have h0n : 1 ≤ (ru D b 0).card := by
    have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (6 : Fin 13) ∈ _) (by rw [hIeq]; decide : (8 : Fin 13) ∈ _) (u := 0) (v := 12) (by decide)
    have := cc_le h hD b hb 0; omega
  have h5n : 1 ≤ (ru D b 5).card := by
    have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (7 : Fin 13) ∈ _) (by rw [hIeq]; decide : (8 : Fin 13) ∈ _) (u := 5) (v := 10) (by decide)
    have := cc_le h hD b hb 5; omega
  have h0eq : ru D b 0 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have h5eq : ru D b 5 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  exact ru_sub_excl h hD hB0 b hb hpos (i1 := 6) (i2 := 8) (t := 5) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (hE 0 (by decide)) (v3 := 12) (by decide) (by rw [h0eq, hR1]) (by rw [h0eq, h5eq])
    (by decide) ⟨2, Or.inl (by decide)⟩

theorem elim_8 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨8, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {0, 1, 3} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({0, 1, 3} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, -⟩ := res1_setup_c3 h hD h11 ⟨8, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have h12n : 1 ≤ (ru D b 12).card := by
    have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (0 : Fin 13) ∈ _) (by rw [hIeq]; decide : (1 : Fin 13) ∈ _) (u := 12) (v := 3) (by decide)
    have := cc_le h hD b hb 12; omega
  have h12eq : ru D b 12 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hle2 : ∀ t : Fin 13, (t = 5 ∨ t = 8 ∨ t = 10) → (sem_W 13 D t).card ≤ 2 := by
    intro t ht
    by_contra hlt
    have htn : 1 ≤ (ru D b t).card := by have := cc_le h hD b hb t; omega
    have hteq : ru D b t = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    rcases ht with rfl | rfl | rfl
    · exact ru_sub_excl h hD hB0 b hb hpos (i1 := 0) (i2 := 1) (t := 5) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 12 (by decide)) (v3 := 3) (by decide) (by rw [h12eq, hR1]) (by rw [h12eq, hteq]) (by decide) ⟨6, Or.inl (by decide)⟩
    · exact ru_sub_excl h hD hB0 b hb hpos (i1 := 0) (i2 := 1) (t := 8) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 12 (by decide)) (v3 := 3) (by decide) (by rw [h12eq, hR1]) (by rw [h12eq, hteq]) (by decide) ⟨7, Or.inr (by decide)⟩
    · exact ru_sub_excl h hD hB0 b hb hpos (i1 := 0) (i2 := 1) (t := 10) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 12 (by decide)) (v3 := 3) (by decide) (by rw [h12eq, hR1]) (by rw [h12eq, hteq]) (by decide) ⟨6, Or.inl (by decide)⟩
  exact ps_side_3star h hD hpos 5 8 10 7 0 3
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
    (hle2 5 (Or.inl rfl)) (hle2 8 (Or.inr (Or.inl rfl))) (hle2 10 (Or.inr (Or.inr rfl)))

theorem elim_19 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨19, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {7, 8, 10} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({7, 8, 10} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, -⟩ := res1_setup_c3 h hD h11 ⟨19, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have h5n : 1 ≤ (ru D b 5).card := by
    have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (7 : Fin 13) ∈ _) (by rw [hIeq]; decide : (8 : Fin 13) ∈ _) (u := 5) (v := 10) (by decide)
    have := cc_le h hD b hb 5; omega
  have h5eq : ru D b 5 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hle2 : ∀ t : Fin 13, (t = 11 ∨ t = 1 ∨ t = 2) → (sem_W 13 D t).card ≤ 2 := by
    intro t ht
    by_contra hlt
    have htn : 1 ≤ (ru D b t).card := by have := cc_le h hD b hb t; omega
    have hteq : ru D b t = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    rcases ht with rfl | rfl | rfl
    · exact ru_sub_excl h hD hB0 b hb hpos (i1 := 7) (i2 := 8) (t := 11) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 5 (by decide)) (v3 := 10) (by decide) (by rw [h5eq, hR1]) (by rw [h5eq, hteq]) (by decide) ⟨0, Or.inr (by decide)⟩
    · exact ru_sub_excl h hD hB0 b hb hpos (i1 := 7) (i2 := 8) (t := 1) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 5 (by decide)) (v3 := 10) (by decide) (by rw [h5eq, hR1]) (by rw [h5eq, hteq]) (by decide) ⟨0, Or.inr (by decide)⟩
    · exact ru_sub_excl h hD hB0 b hb hpos (i1 := 7) (i2 := 8) (t := 2) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (hE 5 (by decide)) (v3 := 10) (by decide) (by rw [h5eq, hR1]) (by rw [h5eq, hteq]) (by decide) ⟨1, Or.inl (by decide)⟩
  exact ps_side_3star h hD hpos 11 1 2 4 7 10
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
    (hle2 11 (Or.inl rfl)) (hle2 1 (Or.inr (Or.inl rfl))) (hle2 2 (Or.inr (Or.inr rfl)))

theorem elim_10 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨10, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 3, 6} := by rw [hI]; decide +kernel
  exact elim_no_i0_pa h hD h11 ⟨10, by decide⟩ hI (by rw [hIeq]; decide)
    12 1 3 0 2 10 11 6 3 2 11 10 6 1
    (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide)

theorem elim_13 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨13, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 2, 8} := by rw [hI]; decide +kernel
  exact elim_no_i0_pa h hD h11 ⟨13, by decide⟩ hI (by rw [hIeq]; decide)
    11 1 2 4 5 10 7 8 2 0 12 6 8 1
    (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide)

theorem elim_14 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨14, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 6, 8} := by rw [hI]; decide +kernel
  exact elim_no_i0_pa h hD h11 ⟨14, by decide⟩ hI (by rw [hIeq]; decide)
    0 6 8 12 4 11 9 8 1 2 11 10 6 1
    (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide)

theorem elim_17 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨17, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 8, 10} := by rw [hI]; decide +kernel
  exact elim_no_i0_pa h hD h11 ⟨17, by decide⟩ hI (by rw [hIeq]; decide)
    5 8 10 7 2 11 6 10 1 0 12 6 8 1
    (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by decide)

theorem elim_11 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨11, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {3, 4, 6} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({3, 4, 6} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, pos, P, Q, hctx⟩ := res1_setup_c3 h hD h11 ⟨11, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have hru_eq : ∀ x, 3 ≤ (sem_W 13 D x).card → ru D b x = residualUnits 13 D b := fun x hx => by
    have := cc_le h hD b hb x
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hkill_pair : ∀ (a c ia ic qa qc va : Fin 13),
      a ∉ ({3, 4, 6} : Finset (Fin 13)) → c ∉ ({3, 4, 6} : Finset (Fin 13)) →
      ia ∈ ({3, 4, 6} : Finset (Fin 13)) → ic ∈ ({3, 4, 6} : Finset (Fin 13)) → va ∉ ({3, 4, 6} : Finset (Fin 13)) →
      (a ≠ c ∧ ia ≠ ic ∧ (g13_nbB a).card = 3 ∧ (g13_nbB c).card = 3 ∧
        hc_adjB ia a = true ∧ hc_adjB ic c = true ∧ hc_adjB a va = true ∧
        hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB c qa = false ∧
        hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB a qc = false ∧ hc_adjB ia c = false) →
      3 ≤ (sem_W 13 D a).card → 3 ≤ (sem_W 13 D c).card → False := fun a c ia ic qa qc va ha hc hia hic hva hg h3a h3c =>
    two_diff_I_kill h hD hB0 b hb hctx.1 (hE a ha) (hE c hc) (hIeq ▸ hia) (hIeq ▸ hic) (hIeq ▸ hva) hg
      (by rw [hru_eq a h3a, hR1]) (by rw [hru_eq c h3c, hR1])
      (by rw [hru_eq a h3a, hru_eq c h3c]) (by rw [hru_eq a h3a, hru_eq c h3c]) (hctx.2.1 a)
  have h8 : (sem_W 13 D 8).card ≤ 2 := by
    by_contra hlt
    have h0 : (sem_W 13 D 0).card ≤ 2 := by
      by_contra h0; exact hkill_pair 0 8 6 4 2 9 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    have h12 : (sem_W 13 D 12).card ≤ 2 := by
      by_contra h12; exact hkill_pair 12 8 3 4 9 9 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    exact pa_m1 h hD hctx.1 0 12 8 6 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h0 h12
  have h12 : (sem_W 13 D 12).card ≤ 2 := by
    by_contra hlt
    have h0 : (sem_W 13 D 0).card ≤ 2 := by
      by_contra h0; exact hkill_pair 0 12 6 3 2 9 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    exact pa_m1 h hD hctx.1 0 8 12 6 4 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h0 h8
  have h10 : (sem_W 13 D 10).card ≤ 2 := by
    by_contra hlt
    have h2 : (sem_W 13 D 2).card ≤ 2 := by
      by_contra h2; exact hkill_pair 2 10 6 3 0 9 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    have h11' : (sem_W 13 D 11).card ≤ 2 := by
      by_contra h11'; exact hkill_pair 11 10 4 3 9 9 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    exact pa_m1 h hD hctx.1 2 11 10 6 4 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h2 h11'
  have h11' : (sem_W 13 D 11).card ≤ 2 := by
    by_contra hlt
    have h2 : (sem_W 13 D 2).card ≤ 2 := by
      by_contra h2; exact hkill_pair 2 11 6 4 0 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    exact pa_m1 h hD hctx.1 2 10 11 6 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h2 h10
  have h0_3 : 3 ≤ (sem_W 13 D 0).card := by
    by_contra h0; exact pa_m1 h hD hctx.1 0 8 12 6 4 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h8
  have h2_3 : 3 ≤ (sem_W 13 D 2).card := by
    by_contra h2; exact pa_m1 h hD hctx.1 2 10 11 6 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h10
  exact same_side_cap_I h hD hctx.1 hctx.2.2.1 0 2 6 8 12 10 11 4 3 3 4
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
    (hctx.2.1 0) (hctx.2.1 2) (hctx.2.2.2 0 h0_3).1 (hctx.2.2.2 0 h0_3).2 (hctx.2.2.2 2 h2_3).1 (hctx.2.2.2 2 h2_3).2
    h8 h12 h10 h11'

theorem elim_12 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨12, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {3, 6, 7} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({3, 6, 7} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, pos, P, Q, hctx⟩ := res1_setup_c3 h hD h11 ⟨12, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have hru_eq : ∀ x, 3 ≤ (sem_W 13 D x).card → ru D b x = residualUnits 13 D b := fun x hx => by
    have := cc_le h hD b hb x
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hkill_pair : ∀ (a c ia ic qa qc va : Fin 13),
      a ∉ ({3, 6, 7} : Finset (Fin 13)) → c ∉ ({3, 6, 7} : Finset (Fin 13)) →
      ia ∈ ({3, 6, 7} : Finset (Fin 13)) → ic ∈ ({3, 6, 7} : Finset (Fin 13)) → va ∉ ({3, 4, 6} : Finset (Fin 13)) ∨ va ∉ ({3, 6, 7} : Finset (Fin 13)) →
      va ∉ ({3, 6, 7} : Finset (Fin 13)) →
      (a ≠ c ∧ ia ≠ ic ∧ (g13_nbB a).card = 3 ∧ (g13_nbB c).card = 3 ∧
        hc_adjB ia a = true ∧ hc_adjB ic c = true ∧ hc_adjB a va = true ∧
        hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB c qa = false ∧
        hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB a qc = false ∧ hc_adjB ia c = false) →
      3 ≤ (sem_W 13 D a).card → 3 ≤ (sem_W 13 D c).card → False := fun a c ia ic qa qc va ha hc hia hic _ hva hg h3a h3c =>
    two_diff_I_kill h hD hB0 b hb hctx.1 (hE a ha) (hE c hc) (hIeq ▸ hia) (hIeq ▸ hic) (hIeq ▸ hva) hg
      (by rw [hru_eq a h3a, hR1]) (by rw [hru_eq c h3c, hR1])
      (by rw [hru_eq a h3a, hru_eq c h3c]) (by rw [hru_eq a h3a, hru_eq c h3c]) (hctx.2.1 a)
  by_cases h12 : 3 ≤ (sem_W 13 D 12).card
  · have h0 : (sem_W 13 D 0).card ≤ 2 := by
      by_contra h0; exact hkill_pair 0 12 6 3 2 9 8 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide) (by decide) (by omega) h12
    have h1 : (sem_W 13 D 1).card ≤ 2 := by
      by_contra h1; exact hkill_pair 1 12 7 3 5 9 11 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide) (by decide) (by omega) h12
    have h2 : (sem_W 13 D 2).card ≤ 2 := by
      by_contra h2
      have h5 : (sem_W 13 D 5).card ≤ 2 := by
        by_contra h5; exact hkill_pair 2 5 6 7 0 1 10 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide) (by decide) (by omega) (by omega)
      have h10 : (sem_W 13 D 10).card ≤ 2 := by
        by_contra h10; exact hkill_pair 2 10 6 3 0 9 11 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide) (by decide) (by omega) (by omega)
      exact pa_m1 h hD hctx.1 5 10 8 7 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h5 h10
    have h5 : (sem_W 13 D 5).card ≤ 2 := by
      by_contra h5
      have h10 : (sem_W 13 D 10).card ≤ 2 := by
        by_contra h10; exact hkill_pair 5 10 7 3 1 9 8 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide) (by decide) (by omega) (by omega)
      exact pa_m1 h hD hctx.1 2 10 11 6 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h2 h10
    have h8_3 : 3 ≤ (sem_W 13 D 8).card := by
      by_contra h8; exact ps_side_3star h hD hctx.1 8 0 5 4 6 7 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h0 h5
    have h11_3 : 3 ≤ (sem_W 13 D 11).card := by
      by_contra h11'; exact ps_side_3star h hD hctx.1 11 1 2 4 7 6 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h1 h2
    exact same_side_cap_free h hD hctx.1 hctx.2.2.1 8 11 0 5 1 2 4 4 6 7 7 6
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (hctx.2.1 8) (hctx.2.1 11) (hctx.2.2.2 8 h8_3).1 (hctx.2.2.2 8 h8_3).2 (hctx.2.2.2 11 h11_3).1 (hctx.2.2.2 11 h11_3).2
      h0 h5 h1 h2
  · have h12c : (sem_W 13 D 12).card ≤ 2 := by omega
    have h0_3 : 3 ≤ (sem_W 13 D 0).card := by
      by_contra h0; exact pa_m1 h hD hctx.1 0 12 8 6 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h12c
    have h1_3 : 3 ≤ (sem_W 13 D 1).card := by
      by_contra h1; exact pa_m1 h hD hctx.1 1 12 11 7 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h12c
    exact hkill_pair 0 1 6 7 2 5 8 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide) (by decide) h0_3 h1_3

theorem elim_16 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨16, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {6, 7, 9} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({6, 7, 9} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, hB1, pos, P, Q, hctx⟩ := res1_setup_c3 h hD h11 ⟨16, by decide⟩ hI (by rw [hIeq]; decide)
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
  have hru_eq : ∀ x, 3 ≤ (sem_W 13 D x).card → ru D b x = residualUnits 13 D b := fun x hx => by
    have := cc_le h hD b hb x
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hkill_pair : ∀ (a c ia ic qa qc va : Fin 13),
      a ∉ ({6, 7, 9} : Finset (Fin 13)) → c ∉ ({6, 7, 9} : Finset (Fin 13)) →
      ia ∈ ({6, 7, 9} : Finset (Fin 13)) → ic ∈ ({6, 7, 9} : Finset (Fin 13)) → va ∉ ({6, 7, 9} : Finset (Fin 13)) →
      (a ≠ c ∧ ia ≠ ic ∧ (g13_nbB a).card = 3 ∧ (g13_nbB c).card = 3 ∧
        hc_adjB ia a = true ∧ hc_adjB ic c = true ∧ hc_adjB a va = true ∧
        hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB c qa = false ∧
        hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB a qc = false ∧ hc_adjB ia c = false) →
      3 ≤ (sem_W 13 D a).card → 3 ≤ (sem_W 13 D c).card → False := fun a c ia ic qa qc va ha hc hia hic hva hg h3a h3c =>
    two_diff_I_kill h hD hB0 b hb hctx.1 (hE a ha) (hE c hc) (hIeq ▸ hia) (hIeq ▸ hic) (hIeq ▸ hva) hg
      (by rw [hru_eq a h3a, hR1]) (by rw [hru_eq c h3c, hR1])
      (by rw [hru_eq a h3a, hru_eq c h3c]) (by rw [hru_eq a h3a, hru_eq c h3c]) (hctx.2.1 a)
  have hkill_0215 : (sem_W 13 D 0).card ≤ 2 → (sem_W 13 D 2).card ≤ 2 → (sem_W 13 D 1).card ≤ 2 → (sem_W 13 D 5).card ≤ 2 → False := by
    intro h0 h2 h1 h5
    have h8_3 : 3 ≤ (sem_W 13 D 8).card := by
      by_contra h8; exact ps_side_3star h hD hctx.1 8 0 5 4 6 7 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h0 h5
    have h11_3 : 3 ≤ (sem_W 13 D 11).card := by
      by_contra h11'; exact ps_side_3star h hD hctx.1 11 1 2 4 7 6 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h1 h2
    exact same_side_cap_free h hD hctx.1 hctx.2.2.1 8 11 0 5 1 2 4 4 6 7 7 6
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (hctx.2.1 8) (hctx.2.1 11) (hctx.2.2.2 8 h8_3).1 (hctx.2.2.2 8 h8_3).2 (hctx.2.2.2 11 h11_3).1 (hctx.2.2.2 11 h11_3).2
      h0 h5 h1 h2
  have hkill_0234 : (sem_W 13 D 0).card ≤ 2 → (sem_W 13 D 2).card ≤ 2 → (sem_W 13 D 3).card ≤ 2 → (sem_W 13 D 4).card ≤ 2 → False := by
    intro h0 h2 h3 h4
    have h8_3 : 3 ≤ (sem_W 13 D 8).card := by
      by_contra h8; exact ps_side_3star h hD hctx.1 8 0 4 5 6 9 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h0 h4
    have h10_3 : 3 ≤ (sem_W 13 D 10).card := by
      by_contra h10; exact ps_side_3star h hD hctx.1 10 2 3 5 6 9 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h2 h3
    exact same_side_cap_free h hD hctx.1 hctx.2.2.1 8 10 0 4 2 3 5 5 6 9 6 9
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (hctx.2.1 8) (hctx.2.1 10) (hctx.2.2.2 8 h8_3).1 (hctx.2.2.2 8 h8_3).2 (hctx.2.2.2 10 h10_3).1 (hctx.2.2.2 10 h10_3).2
      h0 h4 h2 h3
  have hkill_1534 : (sem_W 13 D 1).card ≤ 2 → (sem_W 13 D 5).card ≤ 2 → (sem_W 13 D 3).card ≤ 2 → (sem_W 13 D 4).card ≤ 2 → False := by
    intro h1 h5 h3 h4
    have h10_3 : 3 ≤ (sem_W 13 D 10).card := by
      by_contra h10; exact ps_side_3star h hD hctx.1 10 3 5 2 9 7 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h3 h5
    have h11_3 : 3 ≤ (sem_W 13 D 11).card := by
      by_contra h11'; exact ps_side_3star h hD hctx.1 11 1 4 2 7 9 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) h1 h4
    exact same_side_cap_free h hD hctx.1 hctx.2.2.1 10 11 3 5 1 4 2 2 9 7 7 9
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (hctx.2.1 10) (hctx.2.1 11) (hctx.2.2.2 10 h10_3).1 (hctx.2.2.2 10 h10_3).2 (hctx.2.2.2 11 h11_3).1 (hctx.2.2.2 11 h11_3).2
      h3 h5 h1 h4
  by_cases h0 : 3 ≤ (sem_W 13 D 0).card
  · exact hkill_1534
      (by by_contra hc; exact hkill_pair 0 1 6 7 2 5 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h0 (by omega))
      (by by_contra hc; exact hkill_pair 0 5 6 7 2 1 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h0 (by omega))
      (by by_contra hc; exact hkill_pair 0 3 6 9 2 4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h0 (by omega))
      (by by_contra hc; exact hkill_pair 0 4 6 9 2 3 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h0 (by omega))
  · by_cases h2 : 3 ≤ (sem_W 13 D 2).card
    · exact hkill_1534
        (by by_contra hc; exact hkill_pair 2 1 6 7 0 5 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 (by omega))
        (by by_contra hc; exact hkill_pair 2 5 6 7 0 1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 (by omega))
        (by by_contra hc; exact hkill_pair 2 3 6 9 0 4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 (by omega))
        (by by_contra hc; exact hkill_pair 2 4 6 9 0 3 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 (by omega))
    · by_cases h1 : 3 ≤ (sem_W 13 D 1).card
      · exact hkill_0234 (by omega) (by omega)
          (by by_contra hc; exact hkill_pair 1 3 7 9 5 4 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 (by omega))
          (by by_contra hc; exact hkill_pair 1 4 7 9 5 3 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 (by omega))
      · by_cases h5 : 3 ≤ (sem_W 13 D 5).card
        · exact hkill_0234 (by omega) (by omega)
            (by by_contra hc; exact hkill_pair 5 3 7 9 1 4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h5 (by omega))
            (by by_contra hc; exact hkill_pair 5 4 7 9 1 3 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h5 (by omega))
        · exact hkill_0215 (by omega) (by omega) (by omega) (by omega)

theorem elim_25 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨25, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 2, 3, 8} := by rw [hI]; decide +kernel
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨25, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_tri_w3_p1 h hD hB1 10 11 12 2 3 1 5 4 0
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · exact elim_sideR_r2 h hD h11 ⟨25, by decide⟩ hI (Or.inl rfl) (by omega)

theorem elim_28 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨28, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {6, 7, 8, 9} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({6, 7, 8, 9} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨28, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · obtain ⟨b, hb⟩ := exists_pureBranch h hD
    obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
    have hR1 : (residualUnits 13 D b).card = 1 := by have := card_residual h.1 b hb; omega
    have h0n : 1 ≤ (ru D b 0).card := by
      have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (6 : Fin 13) ∈ _) (by rw [hIeq]; decide : (8 : Fin 13) ∈ _) (u := 0) (v := 12) (by decide)
      have := cc_le h hD b hb 0; omega
    have h5n : 1 ≤ (ru D b 5).card := by
      have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (7 : Fin 13) ∈ _) (by rw [hIeq]; decide : (8 : Fin 13) ∈ _) (u := 5) (v := 10) (by decide)
      have := cc_le h hD b hb 5; omega
    have h4n : 1 ≤ (ru D b 4).card := by
      have := two_in_deg3 h hD hpos (by rw [hIeq]; decide : (8 : Fin 13) ∈ _) (by rw [hIeq]; decide : (9 : Fin 13) ∈ _) (u := 4) (v := 11) (by decide)
      have := cc_le h hD b hb 4; omega
    have h0eq : ru D b 0 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have h5eq : ru D b 5 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have h4eq : ru D b 4 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    exact pe_co_blow5_r1 h hD b hb hpos 0 5 4 6 7 8 9 11 2 1
      (hE 0 (by decide)) (hE 5 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) h0n h5n (by rw [h0eq, h4eq]) (by rw [h5eq, h4eq]) (by rw [h4eq, hR1]; omega)
  · exact elim_sideL_r2 h hD h11 ⟨28, by decide⟩ hI (Or.inl rfl) (by omega)

theorem elim_29 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨29, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 6, 8, 10} := by rw [hI]; decide +kernel
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨29, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_tri_w3_p1 h hD hB1 0 2 5 6 8 10 12 11 7
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · exact elim_sideL_r2 h hD h11 ⟨29, by decide⟩ hI (Or.inr (Or.inl rfl)) (by omega)

theorem elim_35 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨35, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 3, 4, 5, 6} := by rw [hI]; decide +kernel
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨35, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_share_w3_ps_p1 h hD hB1 8 10 5 4 3 0 2 6
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · exact elim_sideR_r2 h hD h11 ⟨35, by decide⟩ hI (Or.inr rfl) (by omega)

theorem elim_36 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨36, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 6, 8, 9, 10} := by rw [hI]; decide +kernel
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨36, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_tri_w3_p1 h hD hB1 0 2 5 6 8 10 12 11 7
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · exact elim_sideL_r2 h hD h11 ⟨36, by decide⟩ hI (Or.inr (Or.inr rfl)) (by omega)

theorem elim_res2_2w3_pa {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hB0 : Bzero 13 D = 0) (hB2 : Bplus 13 D = (eligSet 13 D).card + 2)
    (a b a1 a2 va b1 b2 vb z k w iz ik : Fin 13)
    (ha : a ∈ eligSet 13 D) (hb' : b ∈ eligSet 13 D)
    (ha1 : a1 ∈ ineligSet 13 D) (ha2 : a2 ∈ ineligSet 13 D)
    (hb1 : b1 ∈ ineligSet 13 D) (hb2 : b2 ∈ ineligSet 13 D) (_hvb : vb ∉ ineligSet 13 D)
    (hiz : iz ∈ ineligSet 13 D) (hik : ik ∈ ineligSet 13 D)
    (hz : z ∉ ineligSet 13 D) (hk : k ∉ ineligSet 13 D) (hw : w ∉ ineligSet 13 D)
    (hno_ab_eq : ∀ (br : Fin 13 → ℕ), PureBranch 13 D br → ∀ (pos : Fin 13 → ℕ × Bool), k4_Pos 13 G13 D pos →
      (residualUnits 13 D br).card = 2 → ru D br a = residualUnits 13 D br → ru D br b = residualUnits 13 D br → False)
    (hg : a ≠ b ∧ a1 ≠ a2 ∧ b1 ≠ b2 ∧
      (g13_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧ hc_adjB a va = true ∧ va ≠ a1 ∧ va ≠ a2 ∧
      (g13_nbB b).card = 3 ∧ hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true ∧ vb ≠ b1 ∧ vb ≠ b2 ∧
      hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧ hc_adjB z w = true ∧
      w ≠ k ∧ (g13_nbB k).card = 3 ∧ decide (w.val < 6) = decide (k.val < 6) ∧
      z ≠ a ∧ z ≠ b ∧ k ≠ a ∧ k ≠ b)
    (hqa : ∀ t, (t = b ∨ t = z ∨ t = k) → ∃ q : Fin 13,
      (hc_adjB a1 q = true ∧ a ≠ q ∧ hc_adjB t q = false ∧ hc_adjB a1 t = false) ∨
      (hc_adjB a2 q = true ∧ a ≠ q ∧ hc_adjB t q = false ∧ hc_adjB a2 t = false))
    (hqb : ∀ t, (t = a ∨ t = z ∨ t = k) → ∃ q : Fin 13,
      (hc_adjB b1 q = true ∧ b ≠ q ∧ hc_adjB t q = false ∧ hc_adjB b1 t = false) ∨
      (hc_adjB b2 q = true ∧ b ≠ q ∧ hc_adjB t q = false ∧ hc_adjB b2 t = false)) : False := by
  classical
  obtain ⟨br, hbr⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hR2 : (residualUnits 13 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨hab, ha12, hb12, hda, ga1, ga2, gva, hva1, hva2, hdb, gb1, gb2, gvb, hvb1, hvb2,
    giz, gik, gzk, gzw, hwk, hdk, hsw, hza, hzb, hka, hkb⟩ := hg
  have hAn : 1 ≤ (ru D br a).card := by
    have := two_in_deg3 h hD hpos ha1 ha2 ⟨ha12, ga1, ga2, gva, hva1, hva2⟩
    have := cc_le h hD br hbr a; omega
  have hBn : 1 ≤ (ru D br b).card := by
    have := two_in_deg3 h hD hpos hb1 hb2 ⟨hb12, gb1, gb2, gvb, hvb1, hvb2⟩
    have := cc_le h hD br hbr b; omega
  have hAle : (ru D br a).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
  have hBle : (ru D br b).card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR2
  have hA1 : (ru D br a).card = 1 := by
    by_contra hne
    have hAR : ru D br a = residualUnits 13 D br := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    by_cases hB2' : (ru D br b).card = 2
    · exact hno_ab_eq br hbr pos hpos hR2 hAR (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega))
    · exact ru_sub_excl h hD hB0 br hbr hpos hb1 hb2 hb' ⟨hdb, hb12, gb1, gb2, gvb, hvb1, hvb2⟩
        (by omega) ((Finset.filter_subset _ _).trans hAR.symm.subset) hab.symm (hqb a (Or.inl rfl))
  have hB1 : (ru D br b).card = 1 := by
    by_contra hne
    have hBR : ru D br b = residualUnits 13 D br := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    exact ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 ha ⟨hda, ha12, ga1, ga2, gva, hva1, hva2⟩
      hA1 ((Finset.filter_subset _ _).trans hBR.symm.subset) hab (hqa b (Or.inl rfl))
  obtain ⟨ua, hua⟩ := Finset.card_eq_one.1 hA1
  obtain ⟨ub, hub⟩ := Finset.card_eq_one.1 hB1
  have huab : ua ≠ ub := fun hh =>
    ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 ha ⟨hda, ha12, ga1, ga2, gva, hva1, hva2⟩
      hA1 (by rw [hua, hub, hh]) hab (hqa b (Or.inl rfl))
  have hRu : residualUnits 13 D br = {ua, ub} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [Finset.card_pair huab, hR2])
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (Finset.filter_subset _ _) (show u ∈ ru D br a by rw [hua]; exact Finset.mem_singleton_self _)
    · exact (Finset.filter_subset _ _) (show u ∈ ru D br b by rw [hub]; exact Finset.mem_singleton_self _)
  have hemp : ∀ t : Fin 13, (t = z ∨ t = k) → (sem_W 13 D t).card ≤ 2 := by
    intro t ht
    have hta : a ≠ t := by rcases ht with rfl | rfl <;> [exact hza.symm; exact hka.symm]
    have htb : b ≠ t := by rcases ht with rfl | rfl <;> [exact hzb.symm; exact hkb.symm]
    have h0 : ru D br t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro u hu
      have huR : u ∈ residualUnits 13 D br := (Finset.filter_subset _ _) hu
      rw [hRu, Finset.mem_insert, Finset.mem_singleton] at huR
      rcases huR with rfl | rfl
      · exact ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 ha ⟨hda, ha12, ga1, ga2, gva, hva1, hva2⟩
          hA1 (by rw [hua, Finset.singleton_subset_iff]; exact hu) hta (hqa t (Or.inr ht))
      · exact ru_sub_excl h hD hB0 br hbr hpos hb1 hb2 hb' ⟨hdb, hb12, gb1, gb2, gvb, hvb1, hvb2⟩
          hB1 (by rw [hub, Finset.singleton_subset_iff]; exact hu) htb (hqb t (Or.inr ht))
    have hc := cc_le h hD br hbr t
    rw [h0, Finset.card_empty] at hc
    omega
  exact pa_m1 h hD hpos z k w iz ik hiz hik hz hk hw ⟨giz, gik, gzk, gzw, hwk, hdk, hsw⟩
    (hemp z (Or.inl rfl)) (hemp k (Or.inr rfl))

theorem hsame_kill_r2 {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hB0 : Bzero 13 D = 0)
    (br : Fin 13 → ℕ) (hbr : PureBranch 13 D br) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (a b i0 ia ib vb qab qba : Fin 13)
    (ha : a ∈ eligSet 13 D) (hb : b ∈ eligSet 13 D)
    (hi0 : i0 ∈ ineligSet 13 D) (hia : ia ∈ ineligSet 13 D) (hib : ib ∈ ineligSet 13 D) (hvb : vb ∉ ineligSet 13 D)
    (hg : a ≠ b ∧ (g13_nbB a).card = 3 ∧ (g13_nbB b).card = 3 ∧
      i0 ≠ ia ∧ i0 ≠ ib ∧ ia ≠ ib ∧ vb ≠ i0 ∧ vb ≠ ia ∧ vb ≠ ib ∧
      hc_adjB i0 a = true ∧ hc_adjB ia a = true ∧ hc_adjB i0 b = true ∧ hc_adjB ib b = true ∧
      hc_adjB b vb = true ∧ hc_adjB ia qab = true ∧ a ≠ qab ∧ hc_adjB b qab = false ∧
      hc_adjB ib qba = true ∧ b ≠ qba ∧ hc_adjB a qba = false ∧ hc_adjB ib a = false)
    (hR2 : (residualUnits 13 D br).card = 2)
    (haR : ru D br a = residualUnits 13 D br) (hbR : ru D br b = residualUnits 13 D br) : False := by
  obtain ⟨hab, hda, hdb, d0a, d0b, dab, v0, va, vb', g0a, gaa, g0b, gbb, gv, gq1, hq1, gnq1, gq2, hq2, gnq2, gnba⟩ := hg
  have hpa_in_b := mem_W_of_pos hpos hia (pe_co_of_sub h hD br hbr hpos hia ha (by rw [haR, hR2]; omega) (by rw [haR, hbR]) ⟨hda, gaa, gq1, hab, hq1, gnq1⟩)
  have ha_in_pb := pe_co_of_sub h hD br hbr hpos hib hb (by rw [hbR, hR2]; omega) (by rw [haR, hbR]) ⟨hdb, gbb, gq2, hab.symm, hq2, gnq2⟩
  have hp0_in_b := as_mem hpos hi0 ((hc_adjB_iff _ _).1 g0b)
  have hpb_in_b := as_mem hpos hib ((hc_adjB_iff _ _).1 gbb)
  obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gv)
  have hWb_le4 : (sem_W 13 D b).card ≤ 4 := by have := cc_le h hD br hbr b; rw [hbR, hR2] at this; omega
  have hWb := pa_four hpb_in_b hp0_in_b hpa_in_b hev
    (fun e => d0b.symm (hpos.2 _ hib _ hi0 e))
    (fun e => dab.symm (hpos.2 _ hib _ hia e))
    (fun e => hvb (hfv _ hib e.symm ▸ hib))
    (fun e => d0a (hpos.2 _ hi0 _ hia e))
    (fun e => hvb (hfv _ hi0 e.symm ▸ hi0))
    (fun e => hvb (hfv _ hia e.symm ▸ hia))
    hWb_le4
  have hfull := full_g13 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gbb) (fun p hp hne1 hsub => by
    rcases hWb p hp with rfl | rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : i0 ∈ supp 13 D (src D (sem_bar (pos i0))) := by
        rw [show src D (sem_bar (pos i0)) = src D ((pos i0).1, !(pos i0).2) from rfl,
          (hpos.1 i0 hi0).2.2.2]; exact Finset.mem_singleton_self i0
      exact d0b (Finset.mem_singleton.1 (hsub hm))
    · have hm : ia ∈ supp 13 D (src D (sem_bar (pos ia))) := by
        rw [show src D (sem_bar (pos ia)) = src D ((pos ia).1, !(pos ia).2) from rfl,
          (hpos.1 ia hia).2.2.2]; exact Finset.mem_singleton_self ia
      exact dab (Finset.mem_singleton.1 (hsub hm))
    · exact vb' (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1)))
  exact sem_adjB_false.1 gnba ((hfull a).1 ha_in_pb)

theorem elim_23 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨23, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 3, 4, 6} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({1, 3, 4, 6} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨23, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_share_w3_ps_p1 h hD hB1 11 12 1 4 3 2 0 6
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hel := inelig_card_add 13 D
    have hts := totalSurplus_split 13 D
    have hc4 : (ineligSet 13 D).card = 4 := by rw [hIeq]; decide
    exact elim_res2_2w3_pa h hD (by omega) (by omega)
      11 12 1 4 2 1 3 0 0 8 12 6 4
      (hE 11 (by decide)) (hE 12 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (fun br hbr pos hpos hR2 haR hbR =>
        hsame_kill_r2 h hD (by omega) br hbr hpos 11 12 1 4 3 0 8 10
          (hE 11 (by decide)) (hE 12 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by decide) hR2 haR hbR)
      (by decide) (by decide +kernel) (by decide +kernel)

theorem elim_26 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨26, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {1, 3, 6, 8} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({1, 3, 6, 8} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨26, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_adj_w3_p1 h hD hB1 0 12 6 8 1 3
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hel := inelig_card_add 13 D
    have hts := totalSurplus_split 13 D
    have hc4 : (ineligSet 13 D).card = 4 := by rw [hIeq]; decide
    exact elim_res2_2w3_pa h hD (by omega) (by omega)
      0 12 6 8 12 1 3 0 2 10 11 6 3
      (hE 0 (by decide)) (hE 12 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (fun br hbr pos hpos hR2 haR hbR =>
        pe_co_blow5_r1 h hD br hbr hpos 0 0 12 6 8 1 3 0 2 4
          (hE 0 (by decide)) (hE 0 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by decide) (by rw [haR, hR2]; omega) (by rw [haR, hR2]; omega) (by rw [haR, hbR]) (by rw [haR, hbR]) (by rw [hbR, hR2]))
      (by decide) (by decide +kernel) (by decide +kernel)

theorem elim_27 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨27, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {3, 6, 7, 8} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({3, 6, 7, 8} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨27, by decide⟩ hI
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · exact elim_share_w3_ps_p1 h hD hB1 0 5 8 6 7 12 10 3
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  · have hel := inelig_card_add 13 D
    have hts := totalSurplus_split 13 D
    have hc4 : (ineligSet 13 D).card = 4 := by rw [hIeq]; decide
    exact elim_res2_2w3_pa h hD (by omega) (by omega)
      0 5 6 8 12 7 8 10 1 12 11 7 3
      (hE 0 (by decide)) (hE 5 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (fun br hbr pos hpos hR2 haR hbR =>
        hsame_kill_r2 h hD (by omega) br hbr hpos 0 5 8 6 7 10 2 1
          (hE 0 (by decide)) (hE 5 (by decide))
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by decide) hR2 haR hbR)
      (by decide) (by decide +kernel) (by decide +kernel)

theorem c8_le2_pos_kill {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (x c ix ic u v iu qc : Fin 13)
    (hc : c ∈ eligSet 13 D)
    (hix : ix ∈ ineligSet 13 D) (hic : ic ∈ ineligSet 13 D) (hiu : iu ∈ ineligSet 13 D)
    (hx : x ∉ ineligSet 13 D) (hu : u ∉ ineligSet 13 D) (hv : v ∉ ineligSet 13 D)
    (hg : x ≠ c ∧ ix ≠ ic ∧ u ≠ v ∧ (g13_nbB c).card = 3 ∧ (g13_nbB u).card = 3 ∧
      hc_adjB ix x = true ∧ hc_adjB ic c = true ∧ hc_adjB x u = true ∧ hc_adjB x v = true ∧
      hc_adjB iu u = true ∧ hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB x qc = false ∧
      decide (v.val < 6) = decide (u.val < 6))
    (hcn : 1 ≤ (ru D b c).card) (hsub : ru D b c ⊆ ru D b x)
    (hWx3 : (sem_W 13 D x).card ≤ 3) (hWu2 : (sem_W 13 D u).card ≤ 2) : False := by
  obtain ⟨hxc, hixc, huv, hdc, hdu, gix, gic, gxu, gxv, giu, gqc, hcqc, gxqc, hsuv⟩ := hg
  rw [hc_adjB_iff] at gix gxu gxv giu
  have hpx := as_mem hpos hix gix
  have hpc := mem_W_of_pos hpos hic (pe_co_of_sub h hD b hb hpos hic hc hcn hsub ⟨hdc, gic, gqc, hxc.symm, hcqc, gxqc⟩)
  obtain ⟨Du, -, hWu, hpu⟩ := ps_side h hD hpos hiu giu hdu hWu2
  obtain ⟨eu, heu, hbu, hfu, hfux⟩ := pa_ed h hD hpos gxu
  obtain ⟨ev, hev, hbv, hfv, -⟩ := pa_ed h hD hpos gxv
  have hbuD : sem_bar eu = Du := by
    rw [hWu, Finset.mem_insert, Finset.mem_singleton] at hbu
    exact hbu.resolve_left (fun hh => hx (hfux _ hiu hh ▸ hiu))
  have h4 := pa_card4 hpx hpc heu hev
    (fun e => hixc (hpos.2 _ hix _ hic e))
    (fun e => hu (hfu _ hix e.symm ▸ hix))
    (fun e => hv (hfv _ hix e.symm ▸ hix))
    (fun e => hu (hfu _ hic e.symm ▸ hic))
    (fun e => hv (hfv _ hic e.symm ▸ hic))
    (fun e => hpu v huv.symm hsuv (by rw [← hbuD, e]; exact hbv))
  omega

theorem c8_le2_full_kill {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hB0 : Bzero 13 D = 0)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (x a ix u v iu qx : Fin 13)
    (hx : x ∈ eligSet 13 D)
    (hix : ix ∈ ineligSet 13 D) (hiu : iu ∈ ineligSet 13 D)
    (hxni : x ∉ ineligSet 13 D) (hu : u ∉ ineligSet 13 D) (hv : v ∉ ineligSet 13 D)
    (hg : x ≠ a ∧ u ≠ v ∧ (g13_nbB x).card = 3 ∧ (g13_nbB u).card = 3 ∧
      hc_adjB ix x = true ∧ hc_adjB x u = true ∧ hc_adjB x v = true ∧
      hc_adjB iu u = true ∧ hc_adjB ix qx = true ∧ x ≠ qx ∧ hc_adjB a qx = false ∧
      hc_adjB ix a = false ∧ decide (v.val < 6) = decide (u.val < 6))
    (hxn : 1 ≤ (ru D b x).card) (hsub : ru D b x ⊆ ru D b a)
    (hWx3 : (sem_W 13 D x).card ≤ 3) (hWu2 : (sem_W 13 D u).card ≤ 2) : False := by
  obtain ⟨hxa, huv, hdx, hdu, gix, gxu, gxv, giu, gqx, hxqx, gaqx, gnixa, hsuv⟩ := hg
  have ha_in := pe_co_of_sub h hD b hb hpos hix hx hxn hsub ⟨hdx, gix, gqx, hxa, hxqx, gaqx⟩
  rw [hc_adjB_iff] at gix gxu gxv giu
  have hpx := as_mem hpos hix gix
  obtain ⟨Du, -, hWu, hpu⟩ := ps_side h hD hpos hiu giu hdu hWu2
  obtain ⟨eu, heu, hbu, hfu, hfux⟩ := pa_ed h hD hpos gxu
  obtain ⟨ev, hev, hbv, hfv, -⟩ := pa_ed h hD hpos gxv
  have hbuD : sem_bar eu = Du := by
    rw [hWu, Finset.mem_insert, Finset.mem_singleton] at hbu
    exact hbu.resolve_left (fun hh => hxni (hfux _ hiu hh ▸ hiu))
  have hWx := pa_three hpx heu hev
    (fun e => hu (hfu _ hix e.symm ▸ hix))
    (fun e => hv (hfv _ hix e.symm ▸ hix))
    (fun e => hpu v huv.symm hsuv (by rw [← hbuD, e]; exact hbv)) hWx3
  have hfull := full_g13 h hD hB0 hpos hix gix (fun p hp hne1 hsub' => by
    rcases hWx p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · exact hu (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbu).2.1) ▸ hix)
    · exact hv (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbv).2.1) ▸ hix))
  exact sem_adjB_false.1 gnixa ((hfull a).1 ha_in)

theorem c8_two_pos_kill {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (x c1 c2 ix ic1 ic2 v q1 q2 : Fin 13)
    (hc1 : c1 ∈ eligSet 13 D) (hc2 : c2 ∈ eligSet 13 D)
    (hix : ix ∈ ineligSet 13 D) (hic1 : ic1 ∈ ineligSet 13 D) (hic2 : ic2 ∈ ineligSet 13 D) (hv : v ∉ ineligSet 13 D)
    (hg : c1 ≠ x ∧ c2 ≠ x ∧ ix ≠ ic1 ∧ ix ≠ ic2 ∧ ic1 ≠ ic2 ∧
      (g13_nbB c1).card = 3 ∧ (g13_nbB c2).card = 3 ∧
      hc_adjB ix x = true ∧ hc_adjB x v = true ∧
      hc_adjB ic1 c1 = true ∧ hc_adjB ic1 q1 = true ∧ c1 ≠ q1 ∧ hc_adjB x q1 = false ∧
      hc_adjB ic2 c2 = true ∧ hc_adjB ic2 q2 = true ∧ c2 ≠ q2 ∧ hc_adjB x q2 = false)
    (h1n : 1 ≤ (ru D b c1).card) (h2n : 1 ≤ (ru D b c2).card)
    (hs1 : ru D b c1 ⊆ ru D b x) (hs2 : ru D b c2 ⊆ ru D b x)
    (hWx3 : (sem_W 13 D x).card ≤ 3) : False := by
  obtain ⟨h1x, h2x, nx1, nx2, n12, hd1, hd2, gix, gxv, gc1, gq1, hq1, gxq1, gc2, gq2, hq2, gxq2⟩ := hg
  have m0 := as_mem hpos hix ((hc_adjB_iff _ _).1 gix)
  have m1 := mem_W_of_pos hpos hic1 (pe_co_of_sub h hD b hb hpos hic1 hc1 h1n hs1 ⟨hd1, gc1, gq1, h1x, hq1, gxq1⟩)
  have m2 := mem_W_of_pos hpos hic2 (pe_co_of_sub h hD b hb hpos hic2 hc2 h2n hs2 ⟨hd2, gc2, gq2, h2x, hq2, gxq2⟩)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gxv)
  have h4 := pa_card4 m0 m1 m2 hev
    (fun e => nx1 (hpos.2 _ hix _ hic1 e)) (fun e => nx2 (hpos.2 _ hix _ hic2 e))
    (fun e => hv (hfv _ hix e.symm ▸ hix)) (fun e => n12 (hpos.2 _ hic1 _ hic2 e))
    (fun e => hv (hfv _ hic1 e.symm ▸ hic1)) (fun e => hv (hfv _ hic2 e.symm ▸ hic2))
  omega

theorem c8_three_pos_kill {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (x c1 c2 c3 ix ic1 ic2 ic3 v q1 q2 q3 : Fin 13)
    (hc1 : c1 ∈ eligSet 13 D) (hc2 : c2 ∈ eligSet 13 D) (hc3 : c3 ∈ eligSet 13 D)
    (hix : ix ∈ ineligSet 13 D) (hic1 : ic1 ∈ ineligSet 13 D) (hic2 : ic2 ∈ ineligSet 13 D) (hic3 : ic3 ∈ ineligSet 13 D)
    (hv : v ∉ ineligSet 13 D)
    (hg : c1 ≠ x ∧ c2 ≠ x ∧ c3 ≠ x ∧ ix ≠ ic1 ∧ ix ≠ ic2 ∧ ix ≠ ic3 ∧ ic1 ≠ ic2 ∧ ic1 ≠ ic3 ∧ ic2 ≠ ic3 ∧
      (g13_nbB c1).card = 3 ∧ (g13_nbB c2).card = 3 ∧ (g13_nbB c3).card = 3 ∧
      hc_adjB ix x = true ∧ hc_adjB x v = true ∧
      hc_adjB ic1 c1 = true ∧ hc_adjB ic1 q1 = true ∧ c1 ≠ q1 ∧ hc_adjB x q1 = false ∧
      hc_adjB ic2 c2 = true ∧ hc_adjB ic2 q2 = true ∧ c2 ≠ q2 ∧ hc_adjB x q2 = false ∧
      hc_adjB ic3 c3 = true ∧ hc_adjB ic3 q3 = true ∧ c3 ≠ q3 ∧ hc_adjB x q3 = false)
    (h1n : 1 ≤ (ru D b c1).card) (h2n : 1 ≤ (ru D b c2).card) (h3n : 1 ≤ (ru D b c3).card)
    (hs1 : ru D b c1 ⊆ ru D b x) (hs2 : ru D b c2 ⊆ ru D b x) (hs3 : ru D b c3 ⊆ ru D b x)
    (hWx4 : (sem_W 13 D x).card ≤ 4) : False := by
  obtain ⟨h1x, h2x, h3x, nx1, nx2, nx3, n12, n13, n23, hd1, hd2, hd3, gix, gxv,
    gc1, gq1, hq1, gxq1, gc2, gq2, hq2, gxq2, gc3, gq3, hq3, gxq3⟩ := hg
  have m0 := as_mem hpos hix ((hc_adjB_iff _ _).1 gix)
  have m1 := mem_W_of_pos hpos hic1 (pe_co_of_sub h hD b hb hpos hic1 hc1 h1n hs1 ⟨hd1, gc1, gq1, h1x, hq1, gxq1⟩)
  have m2 := mem_W_of_pos hpos hic2 (pe_co_of_sub h hD b hb hpos hic2 hc2 h2n hs2 ⟨hd2, gc2, gq2, h2x, hq2, gxq2⟩)
  have m3 := mem_W_of_pos hpos hic3 (pe_co_of_sub h hD b hb hpos hic3 hc3 h3n hs3 ⟨hd3, gc3, gq3, h3x, hq3, gxq3⟩)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gxv)
  have h5 := pa_card5 m0 m1 m2 m3 hev
    (fun e => nx1 (hpos.2 _ hix _ hic1 e)) (fun e => nx2 (hpos.2 _ hix _ hic2 e))
    (fun e => nx3 (hpos.2 _ hix _ hic3 e)) (fun e => hv (hfv _ hix e.symm ▸ hix))
    (fun e => n12 (hpos.2 _ hic1 _ hic2 e)) (fun e => n13 (hpos.2 _ hic1 _ hic3 e))
    (fun e => hv (hfv _ hic1 e.symm ▸ hic1)) (fun e => n23 (hpos.2 _ hic2 _ hic3 e))
    (fun e => hv (hfv _ hic2 e.symm ▸ hic2)) (fun e => hv (hfv _ hic3 e.symm ▸ hic3))
  omega

theorem c8_r3_kill {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hB0 : Bzero 13 D = 0)
    (b : Fin 13 → ℕ) (hb : PureBranch 13 D b) {pos : Fin 13 → ℕ × Bool} (hpos : k4_Pos 13 G13 D pos)
    (hR2 : (residualUnits 13 D b).card = 2)
    (a n1 n2 p1 p2 ia i1 i2 ip qa_p1 qp1_a qa_n1 qn1_a qn2_a : Fin 13)
    (ha : a ∈ eligSet 13 D) (hn1 : n1 ∈ eligSet 13 D) (hn2 : n2 ∈ eligSet 13 D) (hp1 : p1 ∈ eligSet 13 D)
    (hia : ia ∈ ineligSet 13 D) (hi1 : i1 ∈ ineligSet 13 D) (hi2 : i2 ∈ ineligSet 13 D) (hip : ip ∈ ineligSet 13 D)
    (hani : a ∉ ineligSet 13 D) (hn1ni : n1 ∉ ineligSet 13 D) (hn2ni : n2 ∉ ineligSet 13 D) (hp1ni : p1 ∉ ineligSet 13 D) (hp2ni : p2 ∉ ineligSet 13 D)
    (hg : a ≠ n1 ∧ a ≠ n2 ∧ a ≠ p1 ∧ n1 ≠ n2 ∧ p1 ≠ n1 ∧ n1 ≠ p2 ∧
      ia ≠ i1 ∧ ia ≠ i2 ∧ ia ≠ ip ∧ i1 ≠ i2 ∧ i1 ≠ ip ∧ i2 ≠ ip ∧
      (g13_nbB a).card = 3 ∧ (g13_nbB n1).card = 3 ∧ (g13_nbB n2).card = 3 ∧ (g13_nbB p1).card = 3 ∧
      hc_adjB ia a = true ∧ hc_adjB i1 n1 = true ∧ hc_adjB i2 n2 = true ∧ hc_adjB ip p1 = true ∧
      hc_adjB a n1 = true ∧ hc_adjB a n2 = true ∧ hc_adjB n1 p1 = true ∧ hc_adjB p1 p2 = true ∧
      decide (n2.val < 6) = decide (n1.val < 6) ∧ decide (p1.val < 6) = decide (a.val < 6) ∧
      decide (p2.val < 6) = decide (n1.val < 6) ∧
      hc_adjB ia qa_p1 = true ∧ a ≠ qa_p1 ∧ hc_adjB p1 qa_p1 = false ∧ hc_adjB ia p1 = false ∧
      hc_adjB ip qp1_a = true ∧ p1 ≠ qp1_a ∧ hc_adjB a qp1_a = false ∧ hc_adjB ip a = false ∧
      hc_adjB ia qa_n1 = true ∧ a ≠ qa_n1 ∧ hc_adjB n1 qa_n1 = false ∧ hc_adjB ia n1 = false ∧
      hc_adjB i1 qn1_a = true ∧ n1 ≠ qn1_a ∧ hc_adjB a qn1_a = false ∧ hc_adjB i1 a = false ∧
      hc_adjB i2 qn2_a = true ∧ n2 ≠ qn2_a ∧ hc_adjB a qn2_a = false)
    (haR : ru D b a = residualUnits 13 D b)
    (hn2_ge3 : (sem_W 13 D n1).card ≥ 3 → (sem_W 13 D n2).card ≥ 3) : False := by
  obtain ⟨han1, han2, hap1, hn12, hp1n1, hn1p2, nia1, nia2, niap, n12, n1p, n2p,
    hda, hdn1, hdn2, hdp1, gia, gi1, gi2, gip, gan1, gan2, gn1p1, gp1p2,
    hsn12, hspa, hsp2n1,
    gqa_p1, haqp1, gp1qp1, gniap1, gqp1_a, hp1qa, gaqp1, gnipa,
    gqa_n1, haqn1, gn1qn1, gnian1, gqn1_a, hn1qa, gaqn1, gni1a,
    gqn2_a, hn2qa, gaqn2⟩ := hg
  have hWa4 : (sem_W 13 D a).card ≤ 4 := by have := cc_le h hD b hb a; rw [haR, hR2] at this; omega
  have hsubR : ∀ t, ru D b t ⊆ ru D b a := fun t => by rw [haR]; exact Finset.filter_subset _ _
  have h3n1 : 3 ≤ (sem_W 13 D n1).card := by
    by_contra hlt
    have hn1_2 : (sem_W 13 D n1).card ≤ 2 := by omega
    have h3p1 : 3 ≤ (sem_W 13 D p1).card := by
      by_contra hp1_lt
      exact pa_m1 h hD hpos n1 p1 a i1 ip hi1 hip hn1ni hp1ni hani
        ⟨gi1, gip, gn1p1, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gan1)), hap1, hdp1, hspa.symm⟩
        hn1_2 (by omega)
    have hp1n : 1 ≤ (ru D b p1).card := by have := cc_le h hD b hb p1; omega
    have hpp1_in := mem_W_of_pos hpos hip (pe_co_of_sub h hD b hb hpos hip hp1 hp1n (hsubR p1)
      ⟨hdp1, gip, gqp1_a, hap1.symm, hp1qa, gaqp1⟩)
    obtain ⟨Dn1, -, hWn1, hpn1⟩ := ps_side h hD hpos hi1 ((hc_adjB_iff _ _).1 gi1) hdn1 hn1_2
    obtain ⟨e1, he1, hb1, hf1, hf1x⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gan1)
    obtain ⟨e2, he2, hb2, hf2, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gan2)
    have hb1D : sem_bar e1 = Dn1 := by
      rw [hWn1, Finset.mem_insert, Finset.mem_singleton] at hb1
      exact hb1.resolve_left (fun hh => hani (hf1x _ hi1 hh ▸ hi1))
    have hWa := pa_four (as_mem hpos hia ((hc_adjB_iff _ _).1 gia)) hpp1_in he1 he2
      (fun e => niap (hpos.2 _ hia _ hip e)) (fun e => hn1ni (hf1 _ hia e.symm ▸ hia))
      (fun e => hn2ni (hf2 _ hia e.symm ▸ hia)) (fun e => hn1ni (hf1 _ hip e.symm ▸ hip))
      (fun e => hn2ni (hf2 _ hip e.symm ▸ hip))
      (fun e => hpn1 n2 hn12.symm hsn12 (by rw [← hb1D, e]; exact hb2)) hWa4
    have hfull_a := full_g13 h hD hB0 hpos hia ((hc_adjB_iff _ _).1 gia) (fun p hp hne1 hsub' => by
      rcases hWa p hp with rfl | rfl | rfl | rfl
      · exact hne1 rfl
      · have hm : ip ∈ supp 13 D (src D (sem_bar (pos ip))) := by
          rw [show src D (sem_bar (pos ip)) = src D ((pos ip).1, !(pos ip).2) from rfl, (hpos.1 ip hip).2.2.2]
          exact Finset.mem_singleton_self ip
        exact niap.symm (Finset.mem_singleton.1 (hsub' hm))
      · exact hn1ni (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hb1).2.1) ▸ hia)
      · exact hn2ni (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hb2).2.1) ▸ hia))
    have hp1_lt2 : (ru D b p1).card < 2 := by
      by_contra hge2
      have hp1R : ru D b p1 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hp1_in := pe_co_of_sub h hD b hb hpos hia ha (by rw [haR, hR2]; omega) (by rw [haR, hp1R])
        ⟨hda, gia, gqa_p1, hap1, haqp1, gp1qp1⟩
      exact sem_adjB_false.1 gniap1 ((hfull_a p1).1 hp1_in)
    have hWp1_3 : (sem_W 13 D p1).card ≤ 3 := by have := cc_le h hD b hb p1; omega
    exact c8_le2_full_kill h hD hB0 b hb hpos p1 a ip n1 p2 i1 qp1_a
      hp1 hip hi1 hp1ni hn1ni hp2ni
      ⟨hap1.symm, hn1p2, hdp1, hdn1, gip, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gn1p1)), gp1p2,
        gi1, gqp1_a, hp1qa, gaqp1, gnipa, hsp2n1⟩
      hp1n (hsubR p1) hWp1_3 hn1_2
  have h3n2 : 3 ≤ (sem_W 13 D n2).card := hn2_ge3 h3n1
  have hn1n : 1 ≤ (ru D b n1).card := by have := cc_le h hD b hb n1; omega
  have hn2n : 1 ≤ (ru D b n2).card := by have := cc_le h hD b hb n2; omega
  have hp1_2 : (sem_W 13 D p1).card ≤ 2 := by
    by_contra hp1_lt
    have hp1n : 1 ≤ (ru D b p1).card := by have := cc_le h hD b hb p1; omega
    exact c8_three_pos_kill h hD b hb hpos a n1 n2 p1 ia i1 i2 ip n1 qn1_a qn2_a qp1_a
      hn1 hn2 hp1 hia hi1 hi2 hip hn1ni
      ⟨han1.symm, han2.symm, hap1.symm, nia1, nia2, niap, n12, n1p, n2p, hdn1, hdn2, hdp1,
        gia, gan1, gi1, gqn1_a, hn1qa, gaqn1, gi2, gqn2_a, hn2qa, gaqn2, gip, gqp1_a, hp1qa, gaqp1⟩
      hn1n hn2n hp1n (hsubR n1) (hsubR n2) (hsubR p1) hWa4
  have hpi1_in := mem_W_of_pos hpos hi1 (pe_co_of_sub h hD b hb hpos hi1 hn1 hn1n (hsubR n1) ⟨hdn1, gi1, gqn1_a, han1.symm, hn1qa, gaqn1⟩)
  have hpi2_in := mem_W_of_pos hpos hi2 (pe_co_of_sub h hD b hb hpos hi2 hn2 hn2n (hsubR n2) ⟨hdn2, gi2, gqn2_a, han2.symm, hn2qa, gaqn2⟩)
  obtain ⟨e1, he1, hb1, hf1, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gan1)
  have hWa := pa_four (as_mem hpos hia ((hc_adjB_iff _ _).1 gia)) hpi1_in hpi2_in he1
    (fun e => nia1 (hpos.2 _ hia _ hi1 e)) (fun e => nia2 (hpos.2 _ hia _ hi2 e))
    (fun e => hn1ni (hf1 _ hia e.symm ▸ hia)) (fun e => n12 (hpos.2 _ hi1 _ hi2 e))
    (fun e => hn1ni (hf1 _ hi1 e.symm ▸ hi1)) (fun e => hn1ni (hf1 _ hi2 e.symm ▸ hi2)) hWa4
  have hfull_a := full_g13 h hD hB0 hpos hia ((hc_adjB_iff _ _).1 gia) (fun p hp hne1 hsub' => by
    rcases hWa p hp with rfl | rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : i1 ∈ supp 13 D (src D (sem_bar (pos i1))) := by
        rw [show src D (sem_bar (pos i1)) = src D ((pos i1).1, !(pos i1).2) from rfl, (hpos.1 i1 hi1).2.2.2]
        exact Finset.mem_singleton_self i1
      exact nia1.symm (Finset.mem_singleton.1 (hsub' hm))
    · have hm : i2 ∈ supp 13 D (src D (sem_bar (pos i2))) := by
        rw [show src D (sem_bar (pos i2)) = src D ((pos i2).1, !(pos i2).2) from rfl, (hpos.1 i2 hi2).2.2.2]
        exact Finset.mem_singleton_self i2
      exact nia2.symm (Finset.mem_singleton.1 (hsub' hm))
    · exact hn1ni (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hb1).2.1) ▸ hia))
  have hn1_lt2 : (ru D b n1).card < 2 := by
    by_contra hge2
    have hn1R : ru D b n1 = residualUnits 13 D b := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hn1_in := pe_co_of_sub h hD b hb hpos hia ha (by rw [haR, hR2]; omega) (by rw [haR, hn1R])
      ⟨hda, gia, gqa_n1, han1, haqn1, gn1qn1⟩
    exact sem_adjB_false.1 gnian1 ((hfull_a n1).1 hn1_in)
  have hWn1_3 : (sem_W 13 D n1).card ≤ 3 := by have := cc_le h hD b hb n1; omega
  exact c8_le2_full_kill h hD hB0 b hb hpos n1 a i1 p1 a ip qn1_a
    hn1 hi1 hip hn1ni hp1ni hani
    ⟨han1.symm, hap1.symm, hdn1, hdp1, gi1, gn1p1, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gan1)),
      gip, gqn1_a, hn1qa, gaqn1, gni1a, hspa.symm⟩
    hn1n (hsubR n1) hWn1_3 hp1_2

theorem elim_24 {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (h11 : totalSurplus 13 D ≤ 11) (hI : ineligSet 13 D = hc_rep ⟨24, by decide⟩) : False := by
  have hIeq : ineligSet 13 D = {3, 4, 6, 7} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 13, x ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → x ∈ eligSet 13 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt : (eligSet 13 D).card + 1 ≤ Bplus 13 D := by
    by_contra hle; exact tight_le_all h hD (by omega) ⟨24, by decide⟩ hI
  have hel := inelig_card_add 13 D
  have hts := totalSurplus_split 13 D
  have hc4 : (ineligSet 13 D).card = 4 := by rw [hIeq]; decide
  obtain ⟨br, hbr⟩ := sem_exists_minBranch sem_g13_gr h.1 (sem_g13_comp hD)
  have hbp := sem_minBranch_pure hbr
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g13_gr h (sem_g13_comp hD)
  have hpa : ∀ z k w iz ik : Fin 13,
      iz ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → ik ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
      z ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → k ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → w ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
      (hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧ hc_adjB z w = true ∧
        w ≠ k ∧ (g13_nbB k).card = 3 ∧ decide (w.val < 6) = decide (k.val < 6)) →
      (sem_W 13 D z).card ≤ 2 → 3 ≤ (sem_W 13 D k).card := fun z k w iz ik hiz hik hz hk hw hg hcz => by
    by_contra hlt
    exact pa_m1 h hD hpos z k w iz ik (hIeq ▸ hiz) (hIeq ▸ hik) (hIeq ▸ hz) (hIeq ▸ hk) (hIeq ▸ hw) hg hcz (by omega)
  by_cases hB1 : Bplus 13 D = (eligSet 13 D).card + 1
  · have hR1 : (residualUnits 13 D br).card = 1 := by have := card_residual h.1 br hbp; omega
    obtain ⟨pos', P, Q, hctx⟩ := pa_setup_one h hD hB1
    have hru_eq : ∀ x, 3 ≤ (sem_W 13 D x).card → ru D br x = residualUnits 13 D br := fun x hx => by
      have := cc_le h hD br hbp x
      exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hW3 : ∀ x, (sem_W 13 D x).card ≤ 3 := fun x => by
      have := cc_le h hD br hbp x
      have : (ru D br x).card ≤ 1 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hR1
      omega
    have hkill_le2 : ∀ (x c ix ic u v iu qc : Fin 13),
        c ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → ix ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → ic ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        iu ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → x ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        u ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → v ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        (x ≠ c ∧ ix ≠ ic ∧ u ≠ v ∧ (g13_nbB c).card = 3 ∧ (g13_nbB u).card = 3 ∧
          hc_adjB ix x = true ∧ hc_adjB ic c = true ∧ hc_adjB x u = true ∧ hc_adjB x v = true ∧
          hc_adjB iu u = true ∧ hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB x qc = false ∧
          decide (v.val < 6) = decide (u.val < 6)) →
        3 ≤ (sem_W 13 D x).card → 3 ≤ (sem_W 13 D c).card → (sem_W 13 D u).card ≤ 2 → False :=
      fun x c ix ic u v iu qc hc hix hic hiu hx hu hv hg hx3 hc3 hu2 =>
        c8_le2_pos_kill h hD br hbp hpos x c ix ic u v iu qc (hE c hc)
          (hIeq ▸ hix) (hIeq ▸ hic) (hIeq ▸ hiu) (hIeq ▸ hx) (hIeq ▸ hu) (hIeq ▸ hv) hg
          (by rw [hru_eq c hc3, hR1]) (by rw [hru_eq c hc3, hru_eq x hx3]) (hW3 x) hu2
    by_cases h8 : 3 ≤ (sem_W 13 D 8).card
    · by_cases h0 : 3 ≤ (sem_W 13 D 0).card
      · by_cases h12 : 3 ≤ (sem_W 13 D 12).card
        · exact c8_two_pos_kill h hD br hbp hpos 0 8 12 6 4 3 8 9 9
            (hE 8 (by decide)) (hE 12 (by decide))
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (by decide) (by rw [hru_eq 8 h8, hR1]) (by rw [hru_eq 12 h12, hR1])
            (by rw [hru_eq 8 h8, hru_eq 0 h0]) (by rw [hru_eq 12 h12, hru_eq 0 h0]) (hW3 0)
        · exact hkill_le2 0 8 6 4 12 8 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) h0 h8 (by omega)
      · have h12 := hpa 0 12 8 6 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
        exact hkill_le2 8 12 4 3 0 5 6 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) h8 h12 (by omega)
    · have h0 := hpa 8 0 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
      have h5 := hpa 8 5 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
      have h12 : (sem_W 13 D 12).card ≤ 2 := by
        by_contra h12; exact hkill_le2 0 12 6 3 8 12 4 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) h0 (by omega) (by omega)
      have h10 : (sem_W 13 D 10).card ≤ 2 := by
        by_contra h10; exact hkill_le2 5 10 7 3 8 10 4 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) h5 (by omega) (by omega)
      have h2 := hpa 10 2 5 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h10
      have h11' : (sem_W 13 D 11).card ≤ 2 := by
        by_contra h11'; exact hkill_le2 2 11 6 4 10 11 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) h2 (by omega) h10
      exact same_side_cap_I h hD hctx.1 hctx.2.2.1 0 2 6 8 12 10 11 4 3 3 4
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
        (hctx.2.1 0) (hctx.2.1 2) (hctx.2.2.2 0 h0).1 (hctx.2.2.2 0 h0).2 (hctx.2.2.2 2 h2).1 (hctx.2.2.2 2 h2).2
        (by omega) h12 h10 h11'
  · have hB0 : Bzero 13 D = 0 := by omega
    have hR2 : (residualUnits 13 D br).card = 2 := by have := card_residual h.1 br hbp; omega
    have hr3_sym : ∀ (a n1 n2 p1 p2 r1 r2 ia i1 i2 ip qa_p1 qp1_a qa_r1 qr1_a qa_n1 qn1_a qa_n2 qn2_a : Fin 13),
        a ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → n1 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → n2 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        p1 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → p2 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        r1 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → r2 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        ia ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → i1 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        i2 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → ip ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        (a ≠ n1 ∧ a ≠ n2 ∧ a ≠ p1 ∧ n1 ≠ n2 ∧ p1 ≠ n1 ∧ n1 ≠ p2 ∧
          ia ≠ i1 ∧ ia ≠ i2 ∧ ia ≠ ip ∧ i1 ≠ i2 ∧ i1 ≠ ip ∧ i2 ≠ ip) →
        ((g13_nbB a).card = 3 ∧ (g13_nbB n1).card = 3 ∧ (g13_nbB n2).card = 3 ∧ (g13_nbB p1).card = 3 ∧
          hc_adjB ia a = true ∧ hc_adjB i1 n1 = true ∧ hc_adjB i2 n2 = true ∧ hc_adjB ip p1 = true ∧
          hc_adjB a n1 = true ∧ hc_adjB a n2 = true ∧ hc_adjB n1 p1 = true ∧ hc_adjB p1 p2 = true) →
        (decide (n2.val < 6) = decide (n1.val < 6) ∧ decide (p1.val < 6) = decide (a.val < 6) ∧
          decide (p2.val < 6) = decide (n1.val < 6) ∧
          hc_adjB ia qa_p1 = true ∧ a ≠ qa_p1 ∧ hc_adjB p1 qa_p1 = false ∧ hc_adjB ia p1 = false ∧
          hc_adjB ip qp1_a = true ∧ p1 ≠ qp1_a ∧ hc_adjB a qp1_a = false ∧ hc_adjB ip a = false) →
        (hc_adjB ia qa_n1 = true ∧ a ≠ qa_n1 ∧ hc_adjB n1 qa_n1 = false ∧ hc_adjB ia n1 = false ∧
          hc_adjB i1 qn1_a = true ∧ n1 ≠ qn1_a ∧ hc_adjB a qn1_a = false ∧ hc_adjB i1 a = false ∧
          hc_adjB i2 qn2_a = true ∧ n2 ≠ qn2_a ∧ hc_adjB a qn2_a = false) →
        (a ≠ r1 ∧ r1 ≠ n2 ∧ n2 ≠ r2 ∧ (g13_nbB r1).card = 3 ∧
          hc_adjB ip r1 = true ∧ hc_adjB n2 r1 = true ∧ hc_adjB r1 r2 = true ∧
          decide (r1.val < 6) = decide (a.val < 6) ∧ decide (r2.val < 6) = decide (n1.val < 6) ∧
          hc_adjB ia qa_r1 = true ∧ a ≠ qa_r1 ∧ hc_adjB r1 qa_r1 = false ∧ hc_adjB ia r1 = false) →
        (hc_adjB ip qr1_a = true ∧ r1 ≠ qr1_a ∧ hc_adjB a qr1_a = false ∧ hc_adjB ip a = false ∧
          hc_adjB ia qa_n2 = true ∧ a ≠ qa_n2 ∧ hc_adjB n2 qa_n2 = false ∧ hc_adjB ia n2 = false ∧
          hc_adjB i2 a = false) →
        (ru D br a).card ≤ 1 := by
      intro a n1 n2 p1 p2 r1 r2 ia i1 i2 ip qa_p1 qp1_a qa_r1 qr1_a qa_n1 qn1_a qa_n2 qn2_a
        ha hn1 hn2 hp1 hp2 hr1 hr2 hia hi1 hi2 hip hg1a hg1b hg1c hg1d hg2a hg2b
      by_contra hgt
      have haR : ru D br a = residualUnits 13 D br := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      obtain ⟨han1, han2, hap1, hn12, hp1n1, hn1p2, nia1, nia2, niap, n12, n1p, n2p⟩ := hg1a
      obtain ⟨hda, hdn1, hdn2, hdp1, gia, gi1, gi2, gip, gan1, gan2, gn1p1, gp1p2⟩ := hg1b
      obtain ⟨hsn12, hspa, hsp2n1, gqa_p1, haqp1, gp1qp1, gniap1, gqp1_a, hp1qa, gaqp1, gnipa⟩ := hg1c
      obtain ⟨gqa_n1, haqn1, gn1qn1, gnian1, gqn1_a, hn1qa, gaqn1, gni1a, gqn2_a, hn2qa, gaqn2⟩ := hg1d
      obtain ⟨har1, hr1n2, hn2r2, hdr1, gipr1, gn2r1, gr1r2, hsr1a, hsr2n1, gqar1, haqar1, gr1qar1, gniar1⟩ := hg2a
      obtain ⟨gqr1a, hr1qra, gaqr1a, gnipa', gqan2, haqan2, gn2qan2, gnian2, gni2a⟩ := hg2b
      have hn2_ge : 3 ≤ (sem_W 13 D n2).card := by
        by_contra hn2lt
        exact c8_r3_kill h hD hB0 br hbp hpos hR2 a n2 n1 r1 r2 ia i2 i1 ip qa_r1 qr1_a qa_n2 qn2_a qn1_a
          (hE a ha) (hE n2 hn2) (hE n1 hn1) (hE r1 hr1)
          (hIeq ▸ hia) (hIeq ▸ hi2) (hIeq ▸ hi1) (hIeq ▸ hip)
          (hIeq ▸ ha) (hIeq ▸ hn2) (hIeq ▸ hn1) (hIeq ▸ hr1) (hIeq ▸ hr2)
          ⟨han2, han1, har1, hn12.symm, hr1n2, hn2r2,
            nia2, nia1, niap, n12.symm, n2p, n1p,
            hda, hdn2, hdn1, hdr1, gia, gi2, gi1, gipr1, gan2, gan1, gn2r1, gr1r2,
            hsn12.symm, hsr1a, hsr2n1.trans hsn12.symm,
            gqar1, haqar1, gr1qar1, gniar1, gqr1a, hr1qra, gaqr1a, gnipa',
            gqan2, haqan2, gn2qan2, gnian2, gqn2_a, hn2qa, gaqn2, gni2a,
            gqn1_a, hn1qa, gaqn1⟩
          haR (fun h => absurd h hn2lt)
      exact c8_r3_kill h hD hB0 br hbp hpos hR2 a n1 n2 p1 p2 ia i1 i2 ip qa_p1 qp1_a qa_n1 qn1_a qn2_a
        (hE a ha) (hE n1 hn1) (hE n2 hn2) (hE p1 hp1)
        (hIeq ▸ hia) (hIeq ▸ hi1) (hIeq ▸ hi2) (hIeq ▸ hip)
        (hIeq ▸ ha) (hIeq ▸ hn1) (hIeq ▸ hn2) (hIeq ▸ hp1) (hIeq ▸ hp2)
        ⟨han1, han2, hap1, hn12, hp1n1, hn1p2, nia1, nia2, niap, n12, n1p, n2p,
          hda, hdn1, hdn2, hdp1, gia, gi1, gi2, gip, gan1, gan2, gn1p1, gp1p2,
          hsn12, hspa, hsp2n1, gqa_p1, haqp1, gp1qp1, gniap1, gqp1_a, hp1qa, gaqp1, gnipa,
          gqa_n1, haqn1, gn1qn1, gnian1, gqn1_a, hn1qa, gaqn1, gni1a, gqn2_a, hn2qa, gaqn2⟩
        haR (fun _ => hn2_ge)
    have hle1_0 : (ru D br 0).card ≤ 1 := hr3_sym 0 8 12 5 10 1 11 6 4 3 7 2 1 2 5 2 9 2 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_1 : (ru D br 1).card ≤ 1 := hr3_sym 1 12 11 0 8 2 10 7 3 4 6 5 2 5 0 5 9 5 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_2 : (ru D br 2).card ≤ 1 := hr3_sym 2 11 10 1 12 5 8 6 4 3 7 0 5 0 1 0 9 0 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_5 : (ru D br 5).card ≤ 1 := hr3_sym 5 10 8 2 11 0 12 7 3 4 6 1 0 1 2 1 9 1 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_8 : (ru D br 8).card ≤ 1 := hr3_sym 8 0 5 12 1 10 2 4 6 7 3 9 9 9 9 9 2 9 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_10 : (ru D br 10).card ≤ 1 := hr3_sym 10 5 2 8 0 11 1 3 7 6 4 9 9 9 9 9 1 9 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_11 : (ru D br 11).card ≤ 1 := hr3_sym 11 2 1 10 5 12 0 4 6 7 3 9 9 9 9 9 0 9 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hle1_12 : (ru D br 12).card ≤ 1 := hr3_sym 12 1 0 11 2 8 5 3 7 6 4 9 9 9 9 9 5 9 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨u0, u1, hu01, hRpair⟩ := Finset.card_eq_two.1 hR2
    have hru_class : ∀ x : Fin 13, (ru D br x).card ≤ 1 → 3 ≤ (sem_W 13 D x).card →
        (sem_W 13 D x).card = 3 ∧ merges 13 D (carrierT 13 D {x}) = ∅ ∧
        (ru D br x = {u0} ∨ ru D br x = {u1}) := by
      intro x hle1 h3
      have hcc := cc_le h hD br hbp x
      have hc1 : (ru D br x).card = 1 := by omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc1
      have huR : u ∈ residualUnits 13 D br := (Finset.filter_subset _ _) (hu ▸ Finset.mem_singleton_self u)
      rw [hRpair, Finset.mem_insert, Finset.mem_singleton] at huR
      refine ⟨by omega, Finset.card_eq_zero.1 (by omega), ?_⟩
      rcases huR with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr hu
    have hkill_same : ∀ (a c ia ic qa qc va : Fin 13),
        a ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → c ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        ia ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → ic ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → va ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        (a ≠ c ∧ ia ≠ ic ∧ (g13_nbB a).card = 3 ∧ (g13_nbB c).card = 3 ∧
          hc_adjB ia a = true ∧ hc_adjB ic c = true ∧ hc_adjB a va = true ∧
          hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB c qa = false ∧
          hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB a qc = false ∧ hc_adjB ia c = false) →
        (ru D br a).card ≤ 1 → 3 ≤ (sem_W 13 D a).card → 3 ≤ (sem_W 13 D c).card →
        ru D br a = ru D br c → False := fun a c ia ic qa qc va ha hc hia hic hva hg hla h3a h3c heq => by
      have ha_c := cc_le h hD br hbp a
      have hc_c := cc_le h hD br hbp c
      exact two_diff_I_kill h hD hB0 br hbp hpos (hE a ha) (hE c hc) (hIeq ▸ hia) (hIeq ▸ hic) (hIeq ▸ hva) hg
        (by omega) (by omega) heq.subset heq.symm.subset (by omega)
    have hcap_pair : ∀ (u : Σ _ : ℕ, ℕ) (a1 a2 i0 u1 u2 v1 v2 iu1 iu2 iv1 iv2 : Fin 13),
        u ∈ residualUnits 13 D br →
        (ru D br a1).card ≤ 1 → (ru D br a2).card ≤ 1 →
        3 ≤ (sem_W 13 D a1).card → 3 ≤ (sem_W 13 D a2).card →
        ru D br a1 = {u} → ru D br a2 = {u} →
        i0 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → iu1 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        iu2 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → iv1 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → iv2 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        a1 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → a2 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        (hc_adjB i0 a1 = true ∧ hc_adjB i0 a2 = true ∧
          hc_adjB a1 u1 = true ∧ hc_adjB a1 u2 = true ∧
          hc_adjB a2 v1 = true ∧ hc_adjB a2 v2 = true ∧
          hc_adjB iu1 u1 = true ∧ hc_adjB iu2 u2 = true ∧
          hc_adjB iv1 v1 = true ∧ hc_adjB iv2 v2 = true ∧
          (g13_nbB u1).card = 3 ∧ (g13_nbB u2).card = 3 ∧ (g13_nbB v1).card = 3 ∧ (g13_nbB v2).card = 3 ∧
          u1 ≠ u2 ∧ v1 ≠ v2 ∧ u1 ≠ v1 ∧ u1 ≠ v2 ∧ u2 ≠ v1 ∧ u2 ≠ v2 ∧
          decide (u2.val < 6) = decide (u1.val < 6) ∧ decide (v1.val < 6) = decide (u1.val < 6) ∧
          decide (v2.val < 6) = decide (u1.val < 6)) →
        (sem_W 13 D u1).card ≤ 2 → (sem_W 13 D u2).card ≤ 2 →
        (sem_W 13 D v1).card ≤ 2 → (sem_W 13 D v2).card ≤ 2 → False := by
      intro u a1 a2 i0 u1 u2 v1 v2 iu1 iu2 iv1 iv2 huR hle1 hle2 h31 h32 hru1 hru2
        hi0 hiu1 hiu2 hiv1 hiv2 ha1 ha2 hg hcu1 hcu2 hcv1 hcv2
      have hcc1 := cc_le h hD br hbp a1
      have hcc2 := cc_le h hD br hbp a2
      have hm1 : merges 13 D (carrierT 13 D {a1}) = ∅ := Finset.card_eq_zero.1 (by omega)
      have hm2 : merges 13 D (carrierT 13 D {a2}) = ∅ := Finset.card_eq_zero.1 (by omega)
      have h1in : a1 ∈ supp 13 D u.1 := (Finset.mem_filter.1 (by rw [hru1]; exact Finset.mem_singleton_self u : u ∈ ru D br a1)).2
      have h2in : a2 ∈ supp 13 D u.1 := (Finset.mem_filter.1 (by rw [hru2]; exact Finset.mem_singleton_self u : u ∈ ru D br a2)).2
      obtain ⟨P, Q, hPQ, hall⟩ := gct_gen sem_g13_gr h (sem_g13_comp hD) br hbr huR {a1, a2} (by simp) (fun x hx => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨hm1, h1in, fun u' hu' hx' => Finset.mem_singleton.1 (hru1 ▸ Finset.mem_filter.2 ⟨hu', hx'⟩)⟩
        · exact ⟨hm2, h2in, fun u' hu' hx' => Finset.mem_singleton.1 (hru2 ▸ Finset.mem_filter.2 ⟨hu', hx'⟩)⟩)
      exact same_side_cap_I h hD hpos (fun hpq => hPQ (congrArg Prod.fst hpq)) a1 a2 i0 u1 u2 v1 v2 iu1 iu2 iv1 iv2
        (hIeq ▸ hi0) (hIeq ▸ hiu1) (hIeq ▸ hiu2) (hIeq ▸ hiv1) (hIeq ▸ hiv2) (hIeq ▸ ha1) (hIeq ▸ ha2) hg
        (by omega) (by omega) (hall a1 (by simp)).1 (hall a1 (by simp)).2 (hall a2 (by simp)).1 (hall a2 (by simp)).2
        hcu1 hcu2 hcv1 hcv2
    have hno_cross : ∀ (a c n1 n2 ia ic i1 i2 qc qa1 q1a qa2 q2a q12 q21 : Fin 13),
        a ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → c ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        n1 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) → n2 ∉ ({3, 4, 6, 7} : Finset (Fin 13)) →
        ia ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → ic ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        i1 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) → i2 ∈ ({3, 4, 6, 7} : Finset (Fin 13)) →
        (a ≠ c ∧ n1 ≠ n2 ∧ ia ≠ ic ∧ ia ≠ i1 ∧ ia ≠ i2 ∧ i1 ≠ i2 ∧
          (g13_nbB a).card = 3 ∧ (g13_nbB c).card = 3 ∧ (g13_nbB n1).card = 3 ∧ (g13_nbB n2).card = 3 ∧
          hc_adjB ia a = true ∧ hc_adjB ic c = true ∧ hc_adjB i1 n1 = true ∧ hc_adjB i2 n2 = true ∧
          hc_adjB a n1 = true ∧ hc_adjB a n2 = true ∧
          hc_adjB ic qc = true ∧ c ≠ qc ∧ hc_adjB a qc = false ∧
          decide (n2.val < 6) = decide (n1.val < 6) ∧
          hc_adjB ia qa1 = true ∧ a ≠ qa1 ∧ hc_adjB n1 qa1 = false ∧ hc_adjB ia n1 = false ∧
          hc_adjB i1 q1a = true ∧ n1 ≠ q1a ∧ hc_adjB a q1a = false ∧
          hc_adjB ia qa2 = true ∧ a ≠ qa2 ∧ hc_adjB n2 qa2 = false ∧ hc_adjB ia n2 = false ∧
          hc_adjB i2 q2a = true ∧ n2 ≠ q2a ∧ hc_adjB a q2a = false ∧
          hc_adjB i1 q12 = true ∧ n1 ≠ q12 ∧ hc_adjB n2 q12 = false ∧ hc_adjB i1 n2 = false ∧
          hc_adjB i2 q21 = true ∧ n2 ≠ q21 ∧ hc_adjB n1 q21 = false) →
        (ru D br a).card ≤ 1 → (ru D br n1).card ≤ 1 → (ru D br n2).card ≤ 1 →
        3 ≤ (sem_W 13 D a).card → 3 ≤ (sem_W 13 D c).card →
        ru D br a = ru D br c → False := by
      intro a c n1 n2 ia ic i1 i2 qc qa1 q1a qa2 q2a q12 q21 ha hc hn1 hn2 hia hic hi1 hi2 hg hla hln1 hln2 h3a h3c heq
      obtain ⟨hac, hn12, hiac, hia1, hia2, hi12, hda, hdc, hdn1, hdn2, gia, gic, gi1, gi2, gan1, gan2,
        gqc, hcqc, gaqc, hsn12,
        gqa1, haqa1, gn1qa1, gnian1, gq1a, hn1q1a, gaq1a,
        gqa2, haqa2, gn2qa2, gnian2, gq2a, hn2q2a, gaq2a,
        gq12, hn1q12, gn2q12, gni1n2, gq21, hn2q21, gn1q21⟩ := hg
      have hWa3 : (sem_W 13 D a).card ≤ 3 := by have := cc_le h hD br hbp a; omega
      have hcn : 1 ≤ (ru D br c).card := by have := cc_le h hD br hbp c; omega
      have h3n1 : 3 ≤ (sem_W 13 D n1).card := by
        by_contra hlt
        exact c8_le2_pos_kill h hD br hbp hpos a c ia ic n1 n2 i1 qc (hE c hc)
          (hIeq ▸ hia) (hIeq ▸ hic) (hIeq ▸ hi1) (hIeq ▸ ha) (hIeq ▸ hn1) (hIeq ▸ hn2)
          ⟨hac, hiac, hn12, hdc, hdn1, gia, gic, gan1, gan2, gi1, gqc, hcqc, gaqc, hsn12⟩
          hcn heq.symm.subset hWa3 (by omega)
      have h3n2 : 3 ≤ (sem_W 13 D n2).card := by
        by_contra hlt
        exact c8_le2_pos_kill h hD br hbp hpos a c ia ic n2 n1 i2 qc (hE c hc)
          (hIeq ▸ hia) (hIeq ▸ hic) (hIeq ▸ hi2) (hIeq ▸ ha) (hIeq ▸ hn2) (hIeq ▸ hn1)
          ⟨hac, hiac, hn12.symm, hdc, hdn2, gia, gic, gan2, gan1, gi2, gqc, hcqc, gaqc, hsn12.symm⟩
          hcn heq.symm.subset hWa3 (by omega)
      have han1 : a ≠ n1 := fun hh => by rw [hh] at gan1; exact adj_irrefl n1 ((hc_adjB_iff _ _).1 gan1)
      have han2 : a ≠ n2 := fun hh => by rw [hh] at gan2; exact adj_irrefl n2 ((hc_adjB_iff _ _).1 gan2)
      obtain ⟨-, -, ha_u⟩ := hru_class a hla h3a
      obtain ⟨-, -, hn1_u⟩ := hru_class n1 hln1 h3n1
      obtain ⟨-, -, hn2_u⟩ := hru_class n2 hln2 h3n2
      have hne1 : ru D br a ≠ ru D br n1 := fun hh =>
        hkill_same a n1 ia i1 qa1 q1a n1 ha hn1 hia hi1 hn1
          ⟨han1, hia1, hda, hdn1, gia, gi1, gan1, gqa1, haqa1, gn1qa1, gq1a, hn1q1a, gaq1a, gnian1⟩ hla h3a h3n1 hh
      have hne2 : ru D br a ≠ ru D br n2 := fun hh =>
        hkill_same a n2 ia i2 qa2 q2a n2 ha hn2 hia hi2 hn2
          ⟨han2, hia2, hda, hdn2, gia, gi2, gan2, gqa2, haqa2, gn2qa2, gq2a, hn2q2a, gaq2a, gnian2⟩ hla h3a h3n2 hh
      have h12eq : ru D br n1 = ru D br n2 := by
        rcases ha_u with ha0 | ha1 <;> rcases hn1_u with h10 | h11 <;> rcases hn2_u with h20 | h21
        · exact absurd (ha0.trans h10.symm) hne1
        · exact absurd (ha0.trans h10.symm) hne1
        · exact absurd (ha0.trans h20.symm) hne2
        · exact h11.trans h21.symm
        · exact h10.trans h20.symm
        · exact absurd (ha1.trans h21.symm) hne2
        · exact absurd (ha1.trans h11.symm) hne1
        · exact absurd (ha1.trans h11.symm) hne1
      exact hkill_same n1 n2 i1 i2 q12 q21 a hn1 hn2 hi1 hi2 ha
        ⟨hn12, hi12, hdn1, hdn2, gi1, gi2, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gan1)),
          gq12, hn1q12, gn2q12, gq21, hn2q21, gn1q21, gni1n2⟩ hln1 h3n1 h3n2 h12eq
    by_cases h8 : 3 ≤ (sem_W 13 D 8).card
    · obtain ⟨-, -, h8u⟩ := hru_class 8 hle1_8 h8
      have h12_ne8 : 3 ≤ (sem_W 13 D 12).card → ru D br 12 ≠ ru D br 8 := fun h12 heq =>
        hkill_same 12 8 3 4 9 9 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_12 h12 h8 heq
      have h10_ne8 : 3 ≤ (sem_W 13 D 10).card → ru D br 10 ≠ ru D br 8 := fun h10 heq =>
        hkill_same 10 8 3 4 9 9 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_10 h10 h8 heq
      have h0_ne8 : 3 ≤ (sem_W 13 D 0).card → ru D br 0 ≠ ru D br 8 := fun h0 heq =>
        hkill_same 0 8 6 4 2 9 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_0 h0 h8 heq
      have h5_ne8 : 3 ≤ (sem_W 13 D 5).card → ru D br 5 ≠ ru D br 8 := fun h5 heq =>
        hkill_same 5 8 7 4 1 9 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_5 h5 h8 heq
      have h1_ne8 : 3 ≤ (sem_W 13 D 1).card → ru D br 1 ≠ ru D br 8 := fun h1 heq =>
        hno_cross 1 8 11 12 7 4 4 3 9 5 9 5 9 9 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hle1_1 hle1_11 hle1_12 h1 h8 heq
      have h2_ne8 : 3 ≤ (sem_W 13 D 2).card → ru D br 2 ≠ ru D br 8 := fun h2 heq =>
        hno_cross 2 8 10 11 6 4 3 4 9 0 9 0 9 9 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hle1_2 hle1_10 hle1_11 h2 h8 heq
      have hsame_other : ∀ x y, (ru D br x).card ≤ 1 → (ru D br y).card ≤ 1 →
          3 ≤ (sem_W 13 D x).card → 3 ≤ (sem_W 13 D y).card →
          ru D br x ≠ ru D br 8 → ru D br y ≠ ru D br 8 → ru D br x = ru D br y := by
        intro x y hlx hly hx hy hnx hny
        obtain ⟨-, -, hxu⟩ := hru_class x hlx hx
        obtain ⟨-, -, hyu⟩ := hru_class y hly hy
        rcases h8u with h80 | h81 <;> rcases hxu with hx0 | hx1 <;> rcases hyu with hy0 | hy1
        · exact absurd (hx0.trans h80.symm) hnx
        · exact absurd (hx0.trans h80.symm) hnx
        · exact absurd (hy0.trans h80.symm) hny
        · exact hx1.trans hy1.symm
        · exact hx0.trans hy0.symm
        · exact absurd (hy1.trans h81.symm) hny
        · exact absurd (hx1.trans h81.symm) hnx
        · exact absurd (hx1.trans h81.symm) hnx
      by_cases h0 : 3 ≤ (sem_W 13 D 0).card
      ·
        have h12 : (sem_W 13 D 12).card ≤ 2 := by
          by_contra hc
          exact hkill_same 0 12 6 3 2 9 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            hle1_0 h0 (by omega) (hsame_other 0 12 hle1_0 hle1_12 h0 (by omega) (h0_ne8 h0) (h12_ne8 (by omega)))
        have h1 : (sem_W 13 D 1).card ≤ 2 := by
          by_contra hc
          exact hkill_same 0 1 6 7 2 5 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            hle1_0 h0 (by omega) (hsame_other 0 1 hle1_0 hle1_1 h0 (by omega) (h0_ne8 h0) (h1_ne8 (by omega)))
        exact pa_m1 h hD hpos 1 12 11 7 3 (by rw [hIeq]; decide) (by rw [hIeq]; decide)
          (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1 h12
      ·
        have h12 := hpa 0 12 8 6 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
        have h1 : (sem_W 13 D 1).card ≤ 2 := by
          by_contra hc
          exact hkill_same 1 12 7 3 5 9 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            hle1_1 (by omega) h12 (hsame_other 1 12 hle1_1 hle1_12 (by omega) h12 (h1_ne8 (by omega)) (h12_ne8 h12))
        have h5 : (sem_W 13 D 5).card ≤ 2 := by
          by_contra hc
          exact hno_cross 5 12 8 10 7 3 4 3 9 1 9 1 9 9 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) hle1_5 hle1_8 hle1_10 (by omega) h12
            (hsame_other 5 12 hle1_5 hle1_12 (by omega) h12 (h5_ne8 (by omega)) (h12_ne8 h12))
        have h2 : (sem_W 13 D 2).card ≤ 2 := by
          by_contra hc
          exact hno_cross 2 12 10 11 6 3 3 4 9 0 9 0 9 9 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) hle1_2 hle1_10 hle1_11 (by omega) h12
            (hsame_other 2 12 hle1_2 hle1_12 (by omega) h12 (h2_ne8 (by omega)) (h12_ne8 h12))
        have h11' := hpa 1 11 12 7 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1
        have h11_eq8 : ru D br 11 = ru D br 8 := by
          obtain ⟨-, -, h11u⟩ := hru_class 11 hle1_11 h11'
          have h11_ne12 : ru D br 11 ≠ ru D br 12 := fun heq =>
            hkill_same 11 12 4 3 9 9 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_11 h11' h12 heq
          obtain ⟨-, -, h12u⟩ := hru_class 12 hle1_12 h12
          rcases h8u with h80 | h81 <;> rcases h12u with h120 | h121 <;> rcases h11u with h110 | h111
          · exact absurd (h120.trans h80.symm) (h12_ne8 h12)
          · exact absurd (h120.trans h80.symm) (h12_ne8 h12)
          · exact h110.trans h80.symm
          · exact absurd (h111.trans h121.symm) h11_ne12
          · exact absurd (h110.trans h120.symm) h11_ne12
          · exact h111.trans h81.symm
          · exact absurd (h121.trans h81.symm) (h12_ne8 h12)
          · exact absurd (h121.trans h81.symm) (h12_ne8 h12)
        rcases h8u with h80 | h81
        · exact hcap_pair u0 8 11 4 0 5 1 2 6 7 7 6 (hRpair ▸ by simp) hle1_8 hle1_11 h8 h11' h80 (h11_eq8.trans h80)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by omega) h5 h1 h2
        · exact hcap_pair u1 8 11 4 0 5 1 2 6 7 7 6 (hRpair ▸ by simp) hle1_8 hle1_11 h8 h11' h81 (h11_eq8.trans h81)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by omega) h5 h1 h2
    ·
      have h0 := hpa 8 0 5 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
      have h5 := hpa 8 5 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
      have h05_ne : ru D br 0 ≠ ru D br 5 := fun heq =>
        hkill_same 0 5 6 7 2 1 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_0 h0 h5 heq
      have h12 : (sem_W 13 D 12).card ≤ 2 := by
        by_contra h12
        obtain ⟨-, -, h0u⟩ := hru_class 0 hle1_0 h0
        obtain ⟨-, -, h5u⟩ := hru_class 5 hle1_5 h5
        obtain ⟨-, -, h12u⟩ := hru_class 12 hle1_12 (by omega)
        have h12_eq : ru D br 12 = ru D br 0 ∨ ru D br 12 = ru D br 5 := by
          rcases h0u with h00 | h01 <;> rcases h5u with h50 | h51 <;> rcases h12u with h120 | h121
          · exact absurd (h00.trans h50.symm) h05_ne
          · exact absurd (h00.trans h50.symm) h05_ne
          · exact Or.inl (h120.trans h00.symm)
          · exact Or.inr (h121.trans h51.symm)
          · exact Or.inr (h120.trans h50.symm)
          · exact Or.inl (h121.trans h01.symm)
          · exact absurd (h01.trans h51.symm) h05_ne
          · exact absurd (h01.trans h51.symm) h05_ne
        rcases h12_eq with h120 | h125
        · exact hkill_same 0 12 6 3 2 9 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_0 h0 (by omega) h120.symm
        · exact c8_le2_pos_kill h hD br hbp hpos 5 12 7 3 8 10 4 9 (hE 12 (by decide))
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
            (by have := cc_le h hD br hbp 12; omega) h125.subset (by have := cc_le h hD br hbp 5; omega) (by omega)
      have h10 : (sem_W 13 D 10).card ≤ 2 := by
        by_contra h10
        obtain ⟨-, -, h0u⟩ := hru_class 0 hle1_0 h0
        obtain ⟨-, -, h5u⟩ := hru_class 5 hle1_5 h5
        obtain ⟨-, -, h10u⟩ := hru_class 10 hle1_10 (by omega)
        have h10_eq : ru D br 10 = ru D br 0 ∨ ru D br 10 = ru D br 5 := by
          rcases h0u with h00 | h01 <;> rcases h5u with h50 | h51 <;> rcases h10u with h100 | h101
          · exact absurd (h00.trans h50.symm) h05_ne
          · exact absurd (h00.trans h50.symm) h05_ne
          · exact Or.inl (h100.trans h00.symm)
          · exact Or.inr (h101.trans h51.symm)
          · exact Or.inr (h100.trans h50.symm)
          · exact Or.inl (h101.trans h01.symm)
          · exact absurd (h01.trans h51.symm) h05_ne
          · exact absurd (h01.trans h51.symm) h05_ne
        rcases h10_eq with h100 | h105
        · exact c8_le2_pos_kill h hD br hbp hpos 0 10 6 3 8 12 4 9 (hE 10 (by decide))
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
            (by have := cc_le h hD br hbp 10; omega) h100.subset (by have := cc_le h hD br hbp 0; omega) (by omega)
        · exact hkill_same 5 10 7 3 1 9 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_5 h5 (by omega) h105.symm
      have h2 := hpa 10 2 5 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h10
      have h11' : (sem_W 13 D 11).card ≤ 2 := by
        by_contra h11'
        obtain ⟨-, -, h0u⟩ := hru_class 0 hle1_0 h0
        obtain ⟨-, -, h5u⟩ := hru_class 5 hle1_5 h5
        obtain ⟨-, -, h11u⟩ := hru_class 11 hle1_11 (by omega)
        have h11_eq : ru D br 11 = ru D br 0 ∨ ru D br 11 = ru D br 5 := by
          rcases h0u with h00 | h01 <;> rcases h5u with h50 | h51 <;> rcases h11u with h110 | h111
          · exact absurd (h00.trans h50.symm) h05_ne
          · exact absurd (h00.trans h50.symm) h05_ne
          · exact Or.inl (h110.trans h00.symm)
          · exact Or.inr (h111.trans h51.symm)
          · exact Or.inr (h110.trans h50.symm)
          · exact Or.inl (h111.trans h01.symm)
          · exact absurd (h01.trans h51.symm) h05_ne
          · exact absurd (h01.trans h51.symm) h05_ne
        rcases h11_eq with h110 | h115
        · exact c8_le2_pos_kill h hD br hbp hpos 0 11 6 4 8 12 4 9 (hE 11 (by decide))
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
            (by have := cc_le h hD br hbp 11; omega) h110.subset (by have := cc_le h hD br hbp 0; omega) (by omega)
        · exact c8_le2_pos_kill h hD br hbp hpos 5 11 7 4 8 10 4 9 (hE 11 (by decide))
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
            (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
            (by have := cc_le h hD br hbp 11; omega) h115.subset (by have := cc_le h hD br hbp 5; omega) (by omega)
      have h2_eq0 : ru D br 2 = ru D br 0 := by
        obtain ⟨-, -, h0u⟩ := hru_class 0 hle1_0 h0
        obtain ⟨-, -, h5u⟩ := hru_class 5 hle1_5 h5
        obtain ⟨-, -, h2u⟩ := hru_class 2 hle1_2 h2
        have h25_ne : ru D br 2 ≠ ru D br 5 := fun heq =>
          hkill_same 2 5 6 7 0 1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hle1_2 h2 h5 heq
        rcases h0u with h00 | h01 <;> rcases h5u with h50 | h51 <;> rcases h2u with h20 | h21
        · exact absurd (h00.trans h50.symm) h05_ne
        · exact absurd (h00.trans h50.symm) h05_ne
        · exact h20.trans h00.symm
        · exact absurd (h21.trans h51.symm) h25_ne
        · exact absurd (h20.trans h50.symm) h25_ne
        · exact h21.trans h01.symm
        · exact absurd (h01.trans h51.symm) h05_ne
        · exact absurd (h01.trans h51.symm) h05_ne
      obtain ⟨-, -, h0u⟩ := hru_class 0 hle1_0 h0
      rcases h0u with h00 | h01
      · exact hcap_pair u0 0 2 6 8 12 10 11 4 3 3 4 (hRpair ▸ by simp) hle1_0 hle1_2 h0 h2 h00 (h2_eq0.trans h00)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by omega) h12 h10 h11'
      · exact hcap_pair u1 0 2 6 8 12 10 11 4 3 3 4 (hRpair ▸ by simp) hle1_0 hle1_2 h0 h2 h01 (h2_eq0.trans h01)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by omega) h12 h10 h11'

theorem g13_orbit_partition : ∀ idx : Fin 44,
    (∃ k : Fin 11, sideR_dead_idx k = idx) ∨
    (∃ k : Fin 12, sideL_dead_idx k = idx) ∨
    idx.val = 7 ∨ idx.val = 8 ∨ idx.val = 10 ∨ idx.val = 11 ∨ idx.val = 12 ∨
    idx.val = 13 ∨ idx.val = 14 ∨ idx.val = 15 ∨ idx.val = 16 ∨ idx.val = 17 ∨ idx.val = 19 ∨
    idx.val = 23 ∨ idx.val = 24 ∨ idx.val = 25 ∨ idx.val = 26 ∨ idx.val = 27 ∨
    idx.val = 28 ∨ idx.val = 29 ∨ idx.val = 35 ∨ idx.val = 36 ∨ idx.val = 40 := by
  decide +kernel

theorem aut_preserves_sideL : ∀ (σ : Equiv.Perm (Fin 13)), IsAut σ → sideL.image σ = sideL := by
  intro σ hσ
  have hdeg : ∀ v : Fin 13, (g13_nbB (σ v)).card = (g13_nbB v).card := by
    intro v
    have heq : g13_nbB (σ v) = (g13_nbB v).image σ := by
      ext u
      simp only [g13_nbB, Finset.mem_filter, Finset.mem_univ, true_and, hc_adjB_iff, Finset.mem_image]
      constructor
      · intro h; exact ⟨σ⁻¹ u, (hσ v (σ⁻¹ u)).1 (by simpa using h), by simp⟩
      · rintro ⟨w, hw, rfl⟩; exact (hσ v w).2 hw
    rw [heq, Finset.card_image_of_injective _ σ.injective]
  have hside : ∀ v : Fin 13, σ v ∈ sideL ↔ v ∈ sideL := by
    have h6 : ∃ u : Fin 13, u ∈ sideR ∧ (g13_nbB u).card = 2 := ⟨6, by decide, by decide⟩
    have hdeg2_R : ∀ u : Fin 13, (g13_nbB u).card = 2 → u ∈ sideR := by decide +kernel
    have hdeg2_nbr : ∀ v : Fin 13, v ∈ sideL ↔ ∃ u : Fin 13, (g13_nbB u).card = 2 ∧ Adj u v := by decide +kernel
    intro v
    rw [hdeg2_nbr (σ v), hdeg2_nbr v]
    constructor
    · rintro ⟨u, hu2, huv⟩
      exact ⟨σ⁻¹ u, by rw [← hdeg (σ⁻¹ u)]; simpa using hu2, (hσ (σ⁻¹ u) v).1 (by simpa using huv)⟩
    · rintro ⟨u, hu2, huv⟩
      exact ⟨σ u, by rw [hdeg u]; exact hu2, (hσ u v).2 huv⟩
  ext u
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (hside v).2 hv
  · intro hu; exact ⟨σ⁻¹ u, (hside (σ⁻¹ u)).1 (by simpa using hu), by simp⟩

theorem g13_classify {D : Dag} (h : StrictLive 13 D) (hD : Correct D) (hlen : D.length ≤ 23) :
    D.length = 23 ∧ Bplus 13 D = 11 ∧ Bzero 13 D = 0 ∧ ineligSet 13 D = sideL ∧
      ∀ k : Fin 6, sup_Occ 13 D sideR (sem_g13_nb (os_ptL k)) := by
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hcov := elig_isCover h hD
  have hge2 := g13_inelig_ge2 h hlen b hb
  obtain ⟨σ, hσ, hmem⟩ := exists_aut_canon ((g13_cover_iff_indep D).1 hcov) hge2
  obtain ⟨h1, h2, h3, h4, -, -, -, h8⟩ := g13_relabel σ hσ h hD
  have h11 : totalSurplus 13 (relabel σ D) ≤ 11 := (g13_budget h1 (h3 ▸ hlen)).2
  obtain ⟨idx, hidx⟩ := hc_rep_of_mem hmem
  have hI' : ineligSet 13 (relabel σ D) = hc_rep idx := h8.trans hidx.symm
  rcases g13_orbit_partition idx with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | h7 | h8' | h10 | h11' | h12 | h13 | h14 | h15 | h16 | h17 | h19 |
    h23 | h24 | h25 | h26 | h27 | h28 | h29 | h35 | h36 | h40
  · exact absurd (elim_sideR_dead h1 h2 h11 k hI') id
  · exact absurd (elim_sideL_dead h1 h2 h11 k hI') id
  · exact absurd (elim_7 h1 h2 h11 ((Fin.ext h7 : idx = ⟨7, by decide⟩) ▸ hI')) id
  · exact absurd (elim_8 h1 h2 h11 ((Fin.ext h8' : idx = ⟨8, by decide⟩) ▸ hI')) id
  · exact absurd (elim_10 h1 h2 h11 ((Fin.ext h10 : idx = ⟨10, by decide⟩) ▸ hI')) id
  · exact absurd (elim_11 h1 h2 h11 ((Fin.ext h11' : idx = ⟨11, by decide⟩) ▸ hI')) id
  · exact absurd (elim_12 h1 h2 h11 ((Fin.ext h12 : idx = ⟨12, by decide⟩) ▸ hI')) id
  · exact absurd (elim_13 h1 h2 h11 ((Fin.ext h13 : idx = ⟨13, by decide⟩) ▸ hI')) id
  · exact absurd (elim_14 h1 h2 h11 ((Fin.ext h14 : idx = ⟨14, by decide⟩) ▸ hI')) id
  · exact absurd (elim_15 h1 h2 h11 ((Fin.ext h15 : idx = ⟨15, by decide⟩) ▸ hI')) id
  · exact absurd (elim_16 h1 h2 h11 ((Fin.ext h16 : idx = ⟨16, by decide⟩) ▸ hI')) id
  · exact absurd (elim_17 h1 h2 h11 ((Fin.ext h17 : idx = ⟨17, by decide⟩) ▸ hI')) id
  · exact absurd (elim_19 h1 h2 h11 ((Fin.ext h19 : idx = ⟨19, by decide⟩) ▸ hI')) id
  · exact absurd (elim_23 h1 h2 h11 ((Fin.ext h23 : idx = ⟨23, by decide⟩) ▸ hI')) id
  · exact absurd (elim_24 h1 h2 h11 ((Fin.ext h24 : idx = ⟨24, by decide⟩) ▸ hI')) id
  · exact absurd (elim_25 h1 h2 h11 ((Fin.ext h25 : idx = ⟨25, by decide⟩) ▸ hI')) id
  · exact absurd (elim_26 h1 h2 h11 ((Fin.ext h26 : idx = ⟨26, by decide⟩) ▸ hI')) id
  · exact absurd (elim_27 h1 h2 h11 ((Fin.ext h27 : idx = ⟨27, by decide⟩) ▸ hI')) id
  · exact absurd (elim_28 h1 h2 h11 ((Fin.ext h28 : idx = ⟨28, by decide⟩) ▸ hI')) id
  · exact absurd (elim_29 h1 h2 h11 ((Fin.ext h29 : idx = ⟨29, by decide⟩) ▸ hI')) id
  · exact absurd (elim_35 h1 h2 h11 ((Fin.ext h35 : idx = ⟨35, by decide⟩) ▸ hI')) id
  · exact absurd (elim_36 h1 h2 h11 ((Fin.ext h36 : idx = ⟨36, by decide⟩) ▸ hI')) id
  · have hrep40 : hc_rep idx = sideL := by
      have : idx = ⟨40, by decide⟩ := Fin.ext h40
      rw [this]; decide +kernel
    have him : (ineligSet 13 D).image σ = sideL := h8.symm.trans (hI'.trans hrep40)
    have hIL : ineligSet 13 D = sideL := by
      rw [← aut_preserves_sideL σ hσ] at him
      exact Finset.image_injective σ.injective him
    obtain ⟨h23, hB11, hB0, hocc⟩ := g13_Lprime_forced h hD hlen hIL
    exact ⟨h23, hB11, hB0, hIL, hocc⟩

def wstep1 (w0 : ℕ) (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [if w.length = w0 then true else gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl1 (w0 : ℕ) (D : Dag) (w : List Bool) : List Bool :=
  D.foldl (wstep1 w0) w

def val1 (D : Dag) {n : ℕ} (w0 : ℕ) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (wl1 w0 D (List.ofFn (fun i : Fin n => if i.val = w0 then true else x i))).getD u false

theorem wstep1_length (w0 : ℕ) (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep1 w0 w g).length = w.length + 1 := by simp [wstep1]

theorem wl1_length (w0 : ℕ) (D : Dag) : ∀ w : List Bool, (wl1 w0 D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; rfl
  | cons g D ih => intro w; rw [wl1, List.foldl_cons, ← wl1, ih, wstep1_length, List.length_cons]; omega

theorem wl1_getD_lt (w0 : ℕ) (D : Dag) : ∀ (w : List Bool) (u : ℕ), u < w.length →
    (wl1 w0 D w).getD u false = w.getD u false := by
  induction D with
  | nil => intro w u _; rfl
  | cons g D ih =>
    intro w u hu
    rw [wl1, List.foldl_cons, ← wl1, ih _ _ (by rw [wstep1_length]; omega)]
    exact List.getD_append _ _ _ _ hu

theorem val1_input (D : Dag) {n : ℕ} (w0 : ℕ) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val1 D w0 x u = if u = w0 then true else x ⟨u, hu⟩ := by
  unfold val1
  rw [wl1_getD_lt w0 D _ u (by simp [hu])]
  simp [List.getD_eq_getElem?_getD, hu]

theorem val1_ge (D : Dag) {n : ℕ} (w0 : ℕ) (x : Fin n → Bool) (u : ℕ) (hu : n + D.length ≤ u) :
    val1 D w0 x u = false := by
  unfold val1
  exact List.getD_eq_default _ _ (by rw [wl1_length, List.length_ofFn]; omega)

theorem val1_gate {n : ℕ} {D : Dag} (hS : Strict n D) (w0 : ℕ) (x : Fin n → Bool) (j : ℕ) (hj : j < D.length) :
    val1 D w0 x (n + j) = if n + j = w0 then true else gop (tag D j) (val1 D w0 x (opA D j)) (val1 D w0 x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  let init := List.ofFn (fun i : Fin n => if i.val = w0 then true else x i)
  have hinit : init.length = n := by simp [init]
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by
    have := List.take_append_drop j D
    rw [← List.cons_getElem_drop_succ (h := hj)] at this
    exact this.symm
  let pref := wl1 w0 (D.take j) init
  have hplen : pref.length = n + j := by
    change (wl1 w0 (D.take j) init).length = n + j
    rw [wl1_length, hinit, List.length_take, Nat.min_eq_left (by omega)]
  have hfull : wl1 w0 D init = wl1 w0 (D.drop (j + 1)) (wstep1 w0 pref D[j]) := by
    conv_lhs => rw [hsplit]
    simp only [wl1, List.foldl_append, List.foldl_cons, pref]
  have hget : ∀ u, u < n + j → (wl1 w0 D init).getD u false = pref.getD u false := by
    intro u hu
    rw [hfull, wl1_getD_lt _ _ _ u (by rw [wstep1_length, hplen]; omega)]
    unfold wstep1
    exact List.getD_append _ _ _ _ (by omega)
  change (wl1 w0 D init).getD (n + j) false = _
  rw [hfull, wl1_getD_lt _ _ _ (n + j) (by rw [wstep1_length, hplen]; omega)]
  have hlast : (wstep1 w0 pref D[j]).getD (n + j) false =
      if n + j = w0 then true else gop D[j].1 (pref.getD D[j].2.1 false) (pref.getD D[j].2.2 false) := by
    rw [← hplen]
    simp [wstep1, List.getD_eq_getElem?_getD]
  rw [hlast, ← tag_eq D j hj, ← opA_eq D j hj, ← opB_eq D j hj]
  change (if n + j = w0 then true else gop (tag D j) (pref.getD (opA D j) false) (pref.getD (opB D j) false)) = _
  rw [← hget (opA D j) ha, ← hget (opB D j) hb]
  rfl

theorem val1_self {n : ℕ} {D : Dag} (hS : Strict n D) (w0 : ℕ) (hw : w0 < n + D.length) (x : Fin n → Bool) :
    val1 D w0 x w0 = true := by
  by_cases hn : w0 < n
  · rw [val1_input D w0 x w0 hn]; simp
  · have hj : w0 - n < D.length := by omega
    have heq : n + (w0 - n) = w0 := by omega
    have hg := val1_gate hS w0 x (w0 - n) hj
    rw [heq] at hg
    simpa using hg

theorem val1_ge_val {n : ℕ} {D : Dag} (hS : Strict n D) (w0 : ℕ) (x : Fin n → Bool) :
    ∀ u, val D x u = true → val1 D w0 x u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hn : u < n
    · rw [val_input D x u hn] at hu
      rw [val1_input D w0 x u hn]
      split_ifs <;> [rfl; exact hu]
    · by_cases hlt : u < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj] at hu
        rw [val1_gate hS w0 x j hj]
        split_ifs
        · rfl
        · cases ht : tag D j
          · rw [ht] at hu
            rw [gop_false, Bool.or_eq_true] at hu ⊢
            rcases hu with h1 | h1
            · exact Or.inl (ih _ ha h1)
            · exact Or.inr (ih _ hb h1)
          · rw [ht] at hu
            rw [gop_true, Bool.and_eq_true] at hu ⊢
            exact ⟨ih _ ha hu.1, ih _ hb hu.2⟩
      · rw [val_ge D x u (by omega)] at hu; exact Bool.noConfusion hu

theorem val1_mono {n : ℕ} {D : Dag} (hS : Strict n D) (w0 : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : ∀ u, val1 D w0 x u = true → val1 D w0 y u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hn : u < n
    · rw [val1_input D w0 x u hn] at hu
      rw [val1_input D w0 y u hn]
      split_ifs at hu ⊢
      · rfl
      · exact hxy _ hu
    · by_cases hlt : u < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val1_gate hS w0 x j hj] at hu
        rw [val1_gate hS w0 y j hj]
        split_ifs at hu ⊢
        · rfl
        · cases ht : tag D j
          · rw [ht] at hu
            rw [gop_false, Bool.or_eq_true] at hu ⊢
            rcases hu with h1 | h1
            · exact Or.inl (ih _ ha h1)
            · exact Or.inr (ih _ hb h1)
          · rw [ht] at hu
            rw [gop_true, Bool.and_eq_true] at hu ⊢
            exact ⟨ih _ ha hu.1, ih _ hb hu.2⟩
      · rw [val1_ge D w0 x u (by omega)] at hu; exact Bool.noConfusion hu

theorem val1_changed_path {n : ℕ} {D : Dag} (hS : Strict n D) (w0 : ℕ) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (u : ℕ) (hu : val1 D w0 x u ≠ val1 D w0 y u) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val1 D w0 x b ≠ val1 D w0 y b) v.val u := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hn : u < n
    · rw [val1_input D w0 x u hn, val1_input D w0 y u hn] at hu
      by_cases hw : u = w0
      · simp [hw] at hu
      · simp only [hw, ↓reduceIte] at hu
        have huv : (⟨u, hn⟩ : Fin n) = v := by by_contra hc; exact hu (hxy _ hc)
        rw [← huv]
    · by_cases hlt : u < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hu
        rw [val1_gate hS w0 x j hj, val1_gate hS w0 y j hj] at hg
        by_cases hw : n + j = w0
        · simp [hw] at hg
        · simp only [hw, ↓reduceIte] at hg
          by_cases h1 : val1 D w0 x (opA D j) = val1 D w0 y (opA D j)
          · have h2 : val1 D w0 x (opB D j) ≠ val1 D w0 y (opB D j) := by
              intro h2; apply hg; rw [h1, h2]
            exact Relation.ReflTransGen.tail (ih _ hb h2)
              ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hu⟩
          · exact Relation.ReflTransGen.tail (ih _ ha h1)
              ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hu⟩
      · exfalso; apply hu; rw [val1_ge D w0 x u (by omega), val1_ge D w0 y u (by omega)]

theorem val1_dom_eq {n : ℕ} {D : Dag} (hS : Strict n D) (w0 : ℕ) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val1 D w0 x b = val1 D w0 y b) : val1 D w0 x (outW n D) = val1 D w0 y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val1_input D w0 x _ v.isLt, val1_input D w0 y _ v.isLt] at hb
    by_cases hw : v.val = w0
    · exact hne (by
        have hpath := val1_changed_path hS w0 x y v hxy (outW n D) hne
        rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨c, hs, -⟩
        · rw [← heq, val1_input D w0 x _ v.isLt, val1_input D w0 y _ v.isLt]; simp [hw]
        · exfalso
          have h0 : val1 D w0 x v.val = val1 D w0 y v.val := by
            rw [val1_input D w0 x _ v.isLt, val1_input D w0 y _ v.isLt]; simp [hw]
          have hno : ∀ u, val1 D w0 x u = val1 D w0 y u := by
            intro u
            induction u using Nat.strong_induction_on with
            | _ u ih =>
              by_cases hn : u < n
              · rw [val1_input D w0 x u hn, val1_input D w0 y u hn]
                by_cases huw : u = w0
                · simp [huw]
                · simp only [huw, ↓reduceIte]
                  exact hxy _ (fun h => huw (by rw [← hw, ← h]))
              · by_cases hlt : u < n + D.length
                · obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
                  have hj : j < D.length := by omega
                  obtain ⟨ha, hb', -⟩ := hS j hj
                  rw [val1_gate hS w0 x j hj, val1_gate hS w0 y j hj, ih _ ha, ih _ hb']
                · rw [val1_ge D w0 x u (by omega), val1_ge D w0 y u (by omega)]
          exact hne (hno _))
    · simp only [hw, ↓reduceIte] at hb
      have hxy2 : x = y := by
        funext k
        by_cases hk : k = v
        · rw [hk]; exact hb
        · exact hxy k hk
      exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (val1_changed_path hS w0 x y v hxy _ hne))

theorem kill_Lprime_with_w {D : Dag} (h : StrictLive 13 D) (hD : Correct D)
    (hlen : D.length = 23) (hI : ineligSet 13 D = sideL) (hB0 : Bzero 13 D = 0)
    (hocc : ∀ k : Fin 6, sup_Occ 13 D sideR (sem_g13_nb (os_ptL k)))
    (w0 : ℕ) (hwlt : w0 < 13 + 22)
    (hsub : supp 13 D w0 ⊆ ({3, 4} : Finset (Fin 13)))
    (h1 : ∀ y : Fin 13 → Bool, val1 D w0 y (outW 13 D) = true ↔ y 9 = true ∨ G13Edge y) : False := by
  classical
  have hS := h.1
  have hG := sem_g13_gr
  have hC := sem_g13_comp hD
  by_cases hne : (supp 13 D w0).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hi34 : i = 3 ∨ i = 4 := by
      have := hsub hi; simp only [Finset.mem_insert, Finset.mem_singleton] at this; exact this
    have hiI : i ∈ ineligSet 13 D := by rw [hI]; rcases hi34 with rfl | rfl <;> decide
    have hdom : sem_Dom 13 D w0 i.val := sem_chain_dom hS (sem_inelig_chain hS hiI hi)
    obtain ⟨v, hv9, hiv⟩ : ∃ v : Fin 13, v ≠ 9 ∧ Adj i v := by
      rcases hi34 with rfl | rfl
      · exact ⟨10, by decide, by decide⟩
      · exact ⟨8, by decide, by decide⟩
    have hagree : ∀ k : Fin 13, k ≠ i → single v k = sem_two i v k := by
      intro k hk; simp [single, sem_two, hk]
    have hw_eq : val1 D w0 (single v) w0 = val1 D w0 (sem_two i v) w0 := by
      rw [val1_self hS w0 (by omega), val1_self hS w0 (by omega)]
    have hout_eq := val1_dom_eq hS w0 (single v) (sem_two i v) i hagree w0 hdom hw_eq
    have htrue : val1 D w0 (sem_two i v) (outW 13 D) = true :=
      val1_ge_val hS w0 (sem_two i v) (outW 13 D) ((hD _).2 (g13_pair hiv))
    rw [← hout_eq] at htrue
    rcases (h1 (single v)).1 htrue with hv9' | hedge
    · simp [single, hv9.symm] at hv9'
    · exact g13_not_single v hedge
  · have hw0_emp : supp 13 D w0 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
    let Sbig := sup_big 13 D sideR
    have hbig12 : 12 ≤ Sbig.card := by
      let L3 := (Finset.univ : Finset (Fin 6)).image (fun k => sem_g13_nb (os_ptL k))
      have hL3c : L3.card = 6 := by
        rw [Finset.card_image_of_injective _ (fun a b hab => os_ptL_inj (g13_nb_inj hab))]; decide
      have hch := sup_charge hS (P := sideR) (by decide) L3
        (fun T hT => by
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hT
          have h3 : (sem_g13_nb (os_ptL k)).card = 3 := by revert k; decide +kernel
          exact ⟨h3, hocc k⟩)
        (fun T hT T' hT' hne' => by
          obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hT
          obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hT'
          have := sup_g13_inter (os_ptL a) (os_ptL b) (fun hab => hne' (hab ▸ rfl)) Finset.univ
          simpa [sem_g13_nb] using this)
        ∅ (fun _ h => absurd h (Finset.notMem_empty _))
      rw [hL3c, Finset.card_empty] at hch
      exact by omega
    have hbig_sub : Sbig ⊆ Finset.range 23 := fun j hj => by
      have hm := (Finset.mem_filter.1 hj).1
      rw [merges, Finset.mem_filter, Finset.mem_range, hlen] at hm
      exact Finset.mem_range.2 hm.1
    let Z := (Finset.range 23).filter (fun j => supp 13 D (13 + j) = ∅)
    let Spos := sideL.image (fun i => (pos i).1)
    have hSpos_sub : Spos ⊆ Z := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      have hiI : i ∈ ineligSet 13 D := hI ▸ hi
      obtain ⟨hlt, hemp, -, -⟩ := hpos.1 i hiI
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hemp⟩
    have hSpos_card : Spos.card = 6 := by
      have hinj : Set.InjOn (fun i => (pos i).1) sideL := by
        intro i hi i' hi' heq
        by_contra hne'
        have hiI : i ∈ ineligSet 13 D := hI ▸ hi
        have hi'I : i' ∈ ineligSet 13 D := hI ▸ hi'
        rcases sem_same_gate heq with hp | hp
        · exact hne' (hpos.2 i hiI i' hi'I hp.symm)
        · have hs1 := (hpos.1 i' hi'I).2.2.1
          have hs2 := (hpos.1 i hiI).2.2.2
          have hsub1 : sem_g13_nb i' ⊆ supp 13 D (src D (pos i')) := fun a ha => hs1 a (g13_mem_nb.1 ha)
          rw [hp] at hsub1
          have hbar : src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) := rfl
          rw [hbar, hs2] at hsub1
          have hc1 := Finset.card_le_card hsub1
          rw [Finset.card_singleton] at hc1
          have hdeg := degree_two_or_three i'
          rw [g13_nb_eq] at hc1; omega
      rw [Finset.card_image_of_injOn hinj]; decide
    have hdisj_bZ : Disjoint Sbig Z := by
      rw [Finset.disjoint_left]
      intro j hjb hjZ
      have h2 := (Finset.mem_filter.1 hjb).2
      have hemp := (Finset.mem_filter.1 hjZ).2
      rw [hemp, Finset.empty_inter, Finset.card_empty] at h2
      omega
    let Kout := Finset.range 23 \ (Sbig ∪ Z)
    have hpart : Sbig.card + Z.card + Kout.card = 23 := by
      have hsubU : Sbig ∪ Z ⊆ Finset.range 23 := Finset.union_subset hbig_sub (Finset.filter_subset _ _)
      have h1 := Finset.card_sdiff_add_card_eq_card hsubU
      rw [Finset.card_union_of_disjoint hdisj_bZ, Finset.card_range] at h1
      change Kout.card + (Sbig.card + Z.card) = 23 at h1
      omega
    have h22Z : 22 ∈ Z := by
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
      have hout : outW 13 D = 13 + 22 := by unfold outW; omega
      rw [← hout]; exact g13_supp_out hD
    let AZ := (arcs D).filter (fun e => ∃ j ∈ Z, src D e = 13 + j)
    have hAZ_eq : AZ.card = Z.card - 1 := by
      have hbij : ∀ j ∈ Z.erase 22, (AZ.filter (fun e => src D e = 13 + j)).card = 1 := by
        intro j hj
        have hjZ := (Finset.mem_erase.1 hj).2
        have hj22 := (Finset.mem_erase.1 hj).1
        have hjlt : j < 23 := Finset.mem_range.1 (Finset.mem_filter.1 hjZ).1
        have hlive : 1 ≤ fanout D (13 + j) := h.2.1 (13 + j) (by omega)
        have hfo1 : fanout D (13 + j) = 1 := by
          by_contra hne1
          have h2 : 2 ≤ fanout D (13 + j) := by omega
          have hbz := bz_card hS {13 + j} (fun b hb => by
            rw [Finset.mem_singleton.1 hb]; exact ⟨h2, (Finset.mem_filter.1 hjZ).2⟩)
          rw [Finset.card_singleton, hB0] at hbz; omega
        obtain ⟨r, hr⟩ := Finset.card_eq_one.1 (show (readers D (13 + j)).card = 1 from hfo1)
        have hrm : r ∈ readers D (13 + j) := hr ▸ Finset.mem_singleton_self r
        simp only [readers, Finset.mem_filter, Finset.mem_range] at hrm
        obtain ⟨hrlt, hrop⟩ := hrm
        obtain ⟨s, hs⟩ : ∃ s : Bool, src D (r, s) = 13 + j := by
          rcases hrop with hA | hB
          · exact ⟨false, by simpa [src] using hA⟩
          · exact ⟨true, by simpa [src] using hB⟩
        have hset : AZ.filter (fun e => src D e = 13 + j) = {(r, s)} := by
          ext ⟨k, t⟩
          simp only [AZ, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, Finset.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨hk, -⟩, hsrc⟩
            have hkr : k ∈ readers D (13 + j) := by
              rw [readers, Finset.mem_filter, Finset.mem_range]
              refine ⟨hk, ?_⟩
              cases t
              · left; simpa [src] using hsrc
              · right; simpa [src] using hsrc
            rw [hr, Finset.mem_singleton] at hkr
            subst hkr
            refine ⟨rfl, ?_⟩
            by_contra hts
            have hne_s := sem_src_ne hS hrlt s
            have ht' : t = !s := by cases s <;> cases t <;> simp_all
            rw [ht'] at hsrc
            exact hne_s (hs.trans hsrc.symm)
          · rintro ⟨rfl, rfl⟩
            exact ⟨⟨hrlt, j, hjZ, hs⟩, hs⟩
        rw [hset, Finset.card_singleton]
      have hAZ_union : AZ = (Z.erase 22).biUnion (fun j => AZ.filter (fun e => src D e = 13 + j)) := by
        ext e
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase]
        constructor
        · intro he
          obtain ⟨-, j, hjZ, hsrc⟩ := Finset.mem_filter.1 he
          have hj22 : j ≠ 22 := by
            intro heq; subst heq
            rcases e with ⟨ek, es⟩
            have hklt : ek < D.length := Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_filter.1 he).1).1
            have hlt' := sem_src_lt hS hklt es
            rw [hlen] at hklt
            omega
          exact ⟨j, ⟨hj22, hjZ⟩, he, hsrc⟩
        · rintro ⟨_, -, he, -⟩; exact he
      rw [hAZ_union, Finset.card_biUnion (fun i _ j _ hij => Finset.disjoint_left.2 (fun e he1 he2 => by
        have h1' := (Finset.mem_filter.1 he1).2
        have h2' := (Finset.mem_filter.1 he2).2
        omega))]
      rw [Finset.sum_congr rfl hbij, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem h22Z]
    have hAZ_k_sub : ∀ e ∈ AZ, e.1 ∈ (Z \ Spos) ∪ Kout := by
      intro e he
      obtain ⟨heA, j, hjZ, hsrc⟩ := Finset.mem_filter.1 he
      have hklt : e.1 < 23 := by have := (Finset.mem_range.1 (Finset.mem_product.1 heA).1); omega
      have hsrc_emp : supp 13 D (src D e) = ∅ := hsrc ▸ (Finset.mem_filter.1 hjZ).2
      have hnotbig : e.1 ∉ Sbig := by
        intro hkb
        have hm := (Finset.mem_filter.1 hkb).1
        rw [merges, Finset.mem_filter, Finset.mem_range] at hm
        obtain ⟨-, -, hA, hB⟩ := hm
        have hc : src D e ∈ carrierT 13 D sideR := by
          cases hs : e.2
          · simpa [src, hs] using hA
          · simpa [src, hs] using hB
        obtain ⟨a, ha⟩ := sup_mem_carrier.1 hc
        rw [hsrc_emp, Finset.empty_inter] at ha
        exact Finset.notMem_empty _ ha
      have hnotpos : e.1 ∉ Spos := by
        intro hkp
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.1 hkp
        have hiI : i ∈ ineligSet 13 D := hI ▸ hi
        rcases sem_same_gate heq with hp | hp
        · have hne' : (sem_g13_nb i).Nonempty := Finset.card_pos.1 (by have := degree_two_or_three i; dsimp [sem_g13_nb]; omega)
          obtain ⟨a, ha⟩ := hne'
          have := (hpos.1 i hiI).2.2.1 a (g13_mem_nb.1 ha)
          rw [← hp, hsrc_emp] at this; exact Finset.notMem_empty _ this
        · have := (hpos.1 i hiI).2.2.2
          have hbar : src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) := rfl
          rw [← hbar, ← hp, hsrc_emp] at this
          exact Finset.singleton_ne_empty i this.symm
      by_cases hkZ : e.1 ∈ Z
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hkZ, hnotpos⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hklt,
          fun hu => (Finset.mem_union.1 hu).elim hnotbig hkZ⟩)
    have hAZ_by_k : AZ.card = ∑ k ∈ (Z \ Spos) ∪ Kout, (AZ.filter (fun e => e.1 = k)).card := by
      have hU : AZ = ((Z \ Spos) ∪ Kout).biUnion (fun k => AZ.filter (fun e => e.1 = k)) := by
        ext e; simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun he => ⟨e.1, hAZ_k_sub e he, he, rfl⟩, fun ⟨_, _, he, _⟩ => he⟩
      conv_lhs => rw [hU]
      rw [Finset.card_biUnion (fun a _ b _ hab => Finset.disjoint_left.2 (fun e h1' h2' =>
        hab ((Finset.mem_filter.1 h1').2.symm.trans (Finset.mem_filter.1 h2').2)))]
    have hdisj_ZK : Disjoint (Z \ Spos) Kout := Finset.disjoint_left.2 (fun k hk1 hk2 =>
      (Finset.mem_sdiff.1 hk2).2 (Finset.mem_union_right _ (Finset.mem_sdiff.1 hk1).1))
    have hle2 : ∀ k ∈ Z \ Spos, (AZ.filter (fun e => e.1 = k)).card ≤ 2 := fun k _ => by
      have hsub' : AZ.filter (fun e => e.1 = k) ⊆ {(k, false), (k, true)} := fun ⟨j, s⟩ h => by
        have hj : j = k := (Finset.mem_filter.1 h).2
        subst hj; cases s <;> simp
      exact (Finset.card_le_card hsub').trans (by rw [Finset.card_pair (by simp)])
    have hle1 : ∀ k ∈ Kout, (AZ.filter (fun e => e.1 = k)).card ≤ 1 := fun k hk => by
      by_contra hgt
      have h0 : (k, false) ∈ AZ ∧ (k, true) ∈ AZ := by
        have hsub' : AZ.filter (fun e => e.1 = k) ⊆ {(k, false), (k, true)} := fun ⟨j, s⟩ h => by
          have hj : j = k := (Finset.mem_filter.1 h).2; subst hj; cases s <;> simp
        have hcard : (AZ.filter (fun e => e.1 = k)).card = 2 :=
          le_antisymm ((Finset.card_le_card hsub').trans (by rw [Finset.card_pair (by simp)])) (by omega)
        have heq := Finset.eq_of_subset_of_card_le hsub' (by rw [hcard, Finset.card_pair (by simp)])
        have hf : (k, false) ∈ AZ.filter (fun e => e.1 = k) := by rw [heq]; simp
        have ht : (k, true) ∈ AZ.filter (fun e => e.1 = k) := by rw [heq]; simp
        exact ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 ht).1⟩
      have hklt : k < 23 := Finset.mem_range.1 (Finset.mem_sdiff.1 hk).1
      obtain ⟨-, j1, hj1, hsrc1⟩ := Finset.mem_filter.1 h0.1
      obtain ⟨-, j2, hj2, hsrc2⟩ := Finset.mem_filter.1 h0.2
      have hAemp : supp 13 D (opA D k) = ∅ := by
        change supp 13 D (src D (k, false)) = ∅
        rw [hsrc1]; exact (Finset.mem_filter.1 hj1).2
      have hBemp : supp 13 D (opB D k) = ∅ := by
        change supp 13 D (src D (k, true)) = ∅
        rw [hsrc2]; exact (Finset.mem_filter.1 hj2).2
      have hkemp : supp 13 D (13 + k) = ∅ := by
        rw [supp_gate hS k (by omega), hAemp, hBemp]; split_ifs <;> simp
      exact (Finset.mem_sdiff.1 hk).2 (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hklt, hkemp⟩))
    rw [Finset.sum_union hdisj_ZK] at hAZ_by_k
    have hsum1 : ∑ k ∈ Z \ Spos, (AZ.filter (fun e => e.1 = k)).card ≤ 2 * (Z \ Spos).card :=
      (Finset.sum_le_sum hle2).trans (by simp [mul_comm])
    have hsum2 : ∑ k ∈ Kout, (AZ.filter (fun e => e.1 = k)).card ≤ Kout.card :=
      (Finset.sum_le_sum hle1).trans (by simp)
    have hZsdiff : (Z \ Spos).card + Spos.card = Z.card := Finset.card_sdiff_add_card_eq_card hSpos_sub
    have hsum1_eq : ∑ k ∈ Z \ Spos, (AZ.filter (fun e => e.1 = k)).card = 2 * (Z \ Spos).card := by omega
    have hstar : ∀ k ∈ Z \ Spos, supp 13 D (opA D k) = ∅ ∧ supp 13 D (opB D k) = ∅ := by
      intro k hk
      have hkc : (AZ.filter (fun e => e.1 = k)).card = 2 := by
        by_contra hne2
        have hlt2 : (AZ.filter (fun e => e.1 = k)).card < 2 := by have := hle2 k hk; omega
        have hlt_sum : ∑ x ∈ Z \ Spos, (AZ.filter (fun e => e.1 = x)).card < ∑ _x ∈ Z \ Spos, 2 :=
          Finset.sum_lt_sum hle2 ⟨k, hk, hlt2⟩
        simp only [Finset.sum_const, smul_eq_mul] at hlt_sum
        omega
      have hsub' : AZ.filter (fun e => e.1 = k) ⊆ {(k, false), (k, true)} := fun ⟨j, s⟩ h => by
        have hj : j = k := (Finset.mem_filter.1 h).2; subst hj; cases s <;> simp
      have heq := Finset.eq_of_subset_of_card_le hsub' (by rw [hkc, Finset.card_pair (by simp)])
      have hf : (k, false) ∈ AZ.filter (fun e => e.1 = k) := by rw [heq]; simp
      have ht : (k, true) ∈ AZ.filter (fun e => e.1 = k) := by rw [heq]; simp
      obtain ⟨-, j1, hj1, hsrc1⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 hf).1
      obtain ⟨-, j2, hj2, hsrc2⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 ht).1
      refine ⟨?_, ?_⟩
      · change supp 13 D (src D (k, false)) = ∅; rw [hsrc1]; exact (Finset.mem_filter.1 hj1).2
      · change supp 13 D (src D (k, true)) = ∅; rw [hsrc2]; exact (Finset.mem_filter.1 hj2).2
    have hmain : ∀ u, u < 13 + 23 → supp 13 D u ∩ sideR = ∅ →
        val1 D w0 (fun _ : Fin 13 => false) u = false → val1 D w0 (single (9 : Fin 13)) u = false := by
      intro u
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        intro hult hnoR hemp0
        have huw0 : u ≠ w0 := fun heq => by
          rw [heq, val1_self hS w0 (by omega)] at hemp0; exact Bool.noConfusion hemp0
        by_cases hn : u < 13
        · rw [val1_input D w0 (single (9 : Fin 13)) u hn]
          simp only [huw0, ↓reduceIte, single, decide_eq_false_iff_not]
          intro h9
          have hm : (9 : Fin 13) ∈ supp 13 D u ∩ sideR := Finset.mem_inter.2 ⟨by
            rw [supp_input D ⟨u, hn⟩, Finset.mem_singleton]; exact h9.symm, by decide⟩
          rw [hnoR] at hm; exact Finset.notMem_empty _ hm
        · obtain ⟨k, rfl⟩ : ∃ k, u = 13 + k := ⟨u - 13, by omega⟩
          have hklt : k < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS k hklt
          rw [val1_gate hS w0 (fun _ : Fin 13 => false) k hklt] at hemp0
          simp only [huw0, ↓reduceIte] at hemp0
          rw [val1_gate hS w0 (single (9 : Fin 13)) k hklt]
          simp only [huw0, ↓reduceIte]
          by_cases hkZ : k ∈ Z
          · by_cases hkSpos : k ∈ Spos
            · obtain ⟨i, hi, hkpos⟩ := Finset.mem_image.1 hkSpos
              have hiI : i ∈ ineligSet 13 D := hI ▸ hi
              have hte : tag D k = true := by
                have hmemW := as_W h hD hpos hiI
                have hm : sem_bar (pos i) ∈ sem_W 13 D i := by rw [hmemW]; exact Finset.mem_singleton_self _
                have ht := sem_W_and hS hm
                simpa [sem_bar, hkpos] using ht
              let a := src D ((pos i).1, !(pos i).2)
              have hasupp : supp 13 D a = {i} := (hpos.1 i hiI).2.2.2
              have halt : a < 13 + k := by
                have hplt : (pos i).1 < D.length := by rw [hkpos]; exact hklt
                have := sem_src_lt hS hplt (!(pos i).2)
                simpa [a, hkpos] using this
              have ha_noR : supp 13 D a ∩ sideR = ∅ := by
                rw [hasupp]; apply Finset.eq_empty_iff_forall_notMem.2
                intro x hx; rw [Finset.mem_inter, Finset.mem_singleton] at hx
                obtain ⟨rfl, hxR⟩ := hx
                have hdisj : ∀ z : Fin 13, z ∈ sideL → z ∉ sideR := by decide +kernel
                exact hdisj x hi hxR
              have ha_emp0 : val1 D w0 (fun _ : Fin 13 => false) a = false := by
                cases h0 : val1 D w0 (fun _ : Fin 13 => false) a
                · rfl
                · exfalso
                  have hdom : sem_Dom 13 D a i.val := sem_chain_dom hS (sem_inelig_chain hS hiI (by rw [hasupp]; exact Finset.mem_singleton_self i))
                  obtain ⟨v, hv9, hiv⟩ : ∃ v : Fin 13, v ≠ 9 ∧ Adj i v := by
                    have hsub3 : ∀ x ∈ sideL, ∃ v : Fin 13, v ≠ 9 ∧ hc_adjB x v = true := by decide +kernel
                    obtain ⟨v, hv9, hvadj⟩ := hsub3 i hi
                    exact ⟨v, hv9, (hc_adjB_iff i v).1 hvadj⟩
                  have hval_a1 : val1 D w0 (single v) a = true := val1_mono hS w0 _ _ (fun _ h => Bool.noConfusion h) a h0
                  have hval_a2 : val1 D w0 (sem_two i v) a = true := val1_mono hS w0 _ _ (fun _ h => Bool.noConfusion h) a h0
                  have hout_eq := val1_dom_eq hS w0 (single v) (sem_two i v) i (fun m hm => by simp [single, sem_two, hm]) a hdom (hval_a1.trans hval_a2.symm)
                  have htrue := val1_ge_val hS w0 (sem_two i v) (outW 13 D) ((hD _).2 (g13_pair hiv))
                  rw [← hout_eq] at htrue
                  rcases (h1 (single v)).1 htrue with hv9' | hedge
                  · simp [single, hv9.symm] at hv9'
                  · exact g13_not_single v hedge
              have ha9 := ih a halt (by omega) ha_noR ha_emp0
              rw [hte, gop_true]
              cases hs : (pos i).2
              · have : opB D k = a := by simp [a, src, hs, hkpos]
                rw [this, ha9, Bool.and_false]
              · have : opA D k = a := by simp [a, src, hs, hkpos]
                rw [this, ha9, Bool.false_and]
            · obtain ⟨hAe, hBe⟩ := hstar k (Finset.mem_sdiff.2 ⟨hkZ, hkSpos⟩)
              cases ht : tag D k
              · rw [ht, gop_false, Bool.or_eq_false_iff] at hemp0
                rw [gop_false, ih _ ha (by omega) (by rw [hAe]; simp) hemp0.1,
                    ih _ hb (by omega) (by rw [hBe]; simp) hemp0.2]; rfl
              · rw [ht, gop_true, Bool.and_eq_false_iff] at hemp0
                rw [gop_true]
                rcases hemp0 with hA0 | hB0
                · rw [ih _ ha (by omega) (by rw [hAe]; simp) hA0, Bool.false_and]
                · rw [ih _ hb (by omega) (by rw [hBe]; simp) hB0, Bool.and_false]
          · have hsup_ne : (supp 13 D (13 + k)).Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              intro he; exact hkZ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), he⟩)
            obtain ⟨i, hi⟩ := hsup_ne
            have hiI : i ∈ ineligSet 13 D := by
              rw [hI]
              have hnotR : i ∉ sideR := fun hR => by
                have hm : i ∈ supp 13 D (13 + k) ∩ sideR := Finset.mem_inter.2 ⟨hi, hR⟩
                rw [hnoR] at hm; exact Finset.notMem_empty _ hm
              have hLR : ∀ z : Fin 13, z ∉ sideR → z ∈ sideL := by decide +kernel
              exact hLR i hnotR
            have htk := sem_inelig_or hG h hC hiI hklt hi
            have hpure := sem_inelig_pure hG hS hC hiI hi
            rw [sem_supp_or hS hklt htk] at hpure
            have hAsub : supp 13 D (opA D k) ⊆ {i} := by rw [← hpure]; exact Finset.subset_union_left
            have hBsub : supp 13 D (opB D k) ⊆ {i} := by rw [← hpure]; exact Finset.subset_union_right
            have hi_notR : i ∉ sideR := by
              have hdisj : ∀ z : Fin 13, z ∈ sideL → z ∉ sideR := by decide +kernel
              exact hdisj i (hI ▸ hiI)
            have hAnoR : supp 13 D (opA D k) ∩ sideR = ∅ := Finset.eq_empty_iff_forall_notMem.2 (fun x hx => by
              have hx1 := hAsub (Finset.mem_inter.1 hx).1
              rw [Finset.mem_singleton] at hx1; exact hi_notR (hx1 ▸ (Finset.mem_inter.1 hx).2))
            have hBnoR : supp 13 D (opB D k) ∩ sideR = ∅ := Finset.eq_empty_iff_forall_notMem.2 (fun x hx => by
              have hx1 := hBsub (Finset.mem_inter.1 hx).1
              rw [Finset.mem_singleton] at hx1; exact hi_notR (hx1 ▸ (Finset.mem_inter.1 hx).2))
            rw [htk, gop_false, Bool.or_eq_false_iff] at hemp0
            rw [htk, gop_false, ih _ ha (by omega) hAnoR hemp0.1, ih _ hb (by omega) hBnoR hemp0.2]; rfl
    have hout_emp : val1 D w0 (fun _ : Fin 13 => false) (outW 13 D) = false := by
      cases h0 : val1 D w0 (fun _ : Fin 13 => false) (outW 13 D)
      · rfl
      · rcases (h1 (fun _ : Fin 13 => false)).1 h0 with h9 | hedge
        · exact Bool.noConfusion h9
        · exact False.elim (g13_not_empty hedge)
    have hout_9 := hmain (outW 13 D) (by unfold outW; omega) (by rw [g13_supp_out hD]; simp) hout_emp
    have hout_9t : val1 D w0 (single (9 : Fin 13)) (outW 13 D) = true := (h1 (single (9 : Fin 13))).2 (Or.inl (by simp [single]))
    rw [hout_9] at hout_9t
    exact Bool.noConfusion hout_9t

def edgeList14 : List (ℕ × ℕ) :=
  [(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
   (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def G14Edge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList14 ∧ x u = true ∧ x v = true

def ext0 (y : Fin 13 → Bool) (i : Fin 14) : Bool :=
  if h : i.val = 0 then false else y ⟨i.val - 1, by omega⟩

def ext1 (y : Fin 13 → Bool) (i : Fin 14) : Bool :=
  if h : i.val = 0 then true else y ⟨i.val - 1, by omega⟩

theorem g14_ext0_iff (y : Fin 13 → Bool) : G14Edge (ext0 y) ↔ G13Edge y := by
  have hedge : ∀ u v : Fin 14, (u.val, v.val) ∈ edgeList14 → u.val ≠ 0 →
      v.val ≠ 0 ∧ (u.val - 1, v.val - 1) ∈ edgeList := by decide +kernel
  have hedge_back : ∀ u v : Fin 13, (u.val, v.val) ∈ edgeList →
      (u.val + 1, v.val + 1) ∈ edgeList14 := by decide +kernel
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu0 : u.val ≠ 0 := by intro h0; simp [ext0, h0] at hu
    obtain ⟨hv0, h13⟩ := hedge u v huv hu0
    refine ⟨⟨u.val - 1, by omega⟩, ⟨v.val - 1, by omega⟩, h13, ?_, ?_⟩
    · simpa [ext0, hu0] using hu
    · simpa [ext0, hv0] using hv
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨⟨u.val + 1, by omega⟩, ⟨v.val + 1, by omega⟩, hedge_back u v huv, ?_, ?_⟩
    · simp [ext0, hu]
    · simp [ext0, hv]

theorem g14_ext1_iff (y : Fin 13 → Bool) : G14Edge (ext1 y) ↔ y 9 = true ∨ G13Edge y := by
  have hedge : ∀ u v : Fin 14, (u.val, v.val) ∈ edgeList14 →
      (u.val = 0 ∧ v.val = 10) ∨ (u.val ≠ 0 ∧ v.val ≠ 0 ∧ (u.val - 1, v.val - 1) ∈ edgeList) := by decide +kernel
  have hedge_back : ∀ u v : Fin 13, (u.val, v.val) ∈ edgeList →
      (u.val + 1, v.val + 1) ∈ edgeList14 := by decide +kernel
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases hedge u v huv with ⟨hu0, hv10⟩ | ⟨hu0, hv0, h13⟩
    · left; have : v = ⟨10, by decide⟩ := Fin.ext hv10; subst this; simpa [ext1] using hv
    · right; refine ⟨⟨u.val - 1, by omega⟩, ⟨v.val - 1, by omega⟩, h13, ?_, ?_⟩
      · simpa [ext1, hu0] using hu
      · simpa [ext1, hv0] using hv
  · rintro (h9 | ⟨u, v, huv, hu, hv⟩)
    · exact ⟨0, 10, by decide, by simp [ext1], by simpa [ext1] using h9⟩
    · refine ⟨⟨u.val + 1, by omega⟩, ⟨v.val + 1, by omega⟩, hedge_back u v huv, ?_, ?_⟩
      · simp [ext1, hu]
      · simp [ext1, hv]

def g14_mate (v : Fin 14) : Fin 14 :=
  match v.val with
  | 0 => 10 | 1 => 7 | 2 => 8 | 3 => 12 | 4 => 13 | 5 => 9 | 6 => 11
  | 7 => 1 | 8 => 2 | 9 => 5 | 10 => 0 | 11 => 6 | 12 => 3 | _ => 4

theorem g14_mate_edge : ∀ v : Fin 14, (v.val, (g14_mate v).val) ∈ edgeList14 ∨ ((g14_mate v).val, v.val) ∈ edgeList14 := by
  decide +kernel

theorem g14_not_empty : ¬ G14Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h

theorem g14_not_single (v : Fin 14) : ¬ G14Edge (fun i => decide (i = v)) := by
  have hirr : ∀ u : Fin 14, (u.val, u.val) ∉ edgeList14 := by decide +kernel
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab; exact hirr v hab

theorem g14_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧
      ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ G14Edge x := by
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 14) C hmono
    (by
      intro b; cases b
      · exact ⟨fun i => decide (i = 0) || decide (i = 10), by
          rw [Ne, Bool.not_eq_false]; exact (hC _).2 ⟨0, 10, by decide, by simp, by simp⟩⟩
      · exact ⟨fun _ => false, fun h => g14_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g14_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      refine ⟨fun j => decide (j = i) || decide (j = g14_mate i), fun j => decide (j = g14_mate i),
        fun j hj => by simp [hj], fun h => g14_not_single (g14_mate i) ((hC _).1 ?_)⟩
      rw [← h]; apply (hC _).2
      rcases g14_mate_edge i with he | he
      · exact ⟨i, g14_mate i, he, by simp, by simp⟩
      · exact ⟨g14_mate i, i, he, by simp, by simp⟩)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

def pin0Step (acc : List (Option ℕ) × List Gate × ℕ) (g : Bool × ℕ × ℕ) :
    List (Option ℕ) × List Gate × ℕ :=
  let (st, gs, skip) := acc
  let sa := st.getD g.2.1 none
  let sb := st.getD g.2.2 none
  match g.1, sa, sb with
  | true, none, _ => (st ++ [none], gs, skip + 1)
  | true, _, none => (st ++ [none], gs, skip + 1)
  | true, some a, some b =>
    if a = b then (st ++ [some a], gs, skip + 1)
    else (st ++ [some (13 + gs.length)], gs ++ [⟨.and, [a, b]⟩], skip)
  | false, none, sb => (st ++ [sb], gs, skip + 1)
  | false, sa, none => (st ++ [sa], gs, skip + 1)
  | false, some a, some b =>
    if a = b then (st ++ [some a], gs, skip + 1)
    else (st ++ [some (13 + gs.length)], gs ++ [⟨.or, [a, b]⟩], skip)

def pin0Init : List (Option ℕ) :=
  none :: (List.finRange 13).map (fun i => some i.val)

def pin0Run (D : Dag) : List (Option ℕ) × List Gate × ℕ :=
  D.foldl pin0Step (pin0Init, [], 0)

def optEval (w : List Bool) : Option ℕ → Bool
  | none => false
  | some idx => w.getD idx false

def Pin0Inv (y : Fin 13 → Bool) (wD : List Bool) (acc : List (Option ℕ) × List Gate × ℕ) : Prop :=
  let (st, gs, skip) := acc
  st.length = wD.length ∧
  gs.length + skip + 14 = wD.length ∧
  (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
  (∀ u, u < st.length →
    (∀ idx, st.getD u none = some idx → idx < 13 + gs.length) ∧
    optEval (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) (List.ofFn y)) (st.getD u none) = wD.getD u false)

theorem foldl_gstep_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]; omega

theorem foldl_gstep_getD_lt (gs : List Gate) : ∀ (w : List Bool) (u : ℕ), u < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w).getD u false = w.getD u false := by
  induction gs with
  | nil => intro w u _; rfl
  | cons g gs ih =>
    intro w u hu
    rw [List.foldl_cons, ih _ u (by simp; omega), List.getD_append _ _ _ _ hu]

theorem pin0_step_inv (y : Fin 13 → Bool) (wD : List Bool) (acc : List (Option ℕ) × List Gate × ℕ)
    (g : Bool × ℕ × ℕ) (hg : g.2.1 < wD.length ∧ g.2.2 < wD.length) (hinv : Pin0Inv y wD acc) :
    Pin0Inv y (wstep wD g) (pin0Step acc g) := by
  rcases acc with ⟨st, gs, skip⟩
  obtain ⟨hlen, hsum, hmono, hval⟩ := hinv
  let evalW := fun gs' : List Gate => gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) (List.ofFn y)
  have hlenW : (evalW gs).length = 13 + gs.length := by rw [foldl_gstep_len, List.length_ofFn]
  have ha := hval g.2.1 (by omega)
  have hb := hval g.2.2 (by omega)
  have hstep_same : ∀ (o : Option ℕ) (ho_lt : ∀ idx, o = some idx → idx < 13 + gs.length)
      (ho_val : optEval (evalW gs) o = gop g.1 (wD.getD g.2.1 false) (wD.getD g.2.2 false)),
      Pin0Inv y (wstep wD g) (st ++ [o], gs, skip + 1) := by
    intro o ho_lt ho_val
    refine ⟨by simp [wstep, hlen], by simp [wstep]; omega, hmono, fun u hu => ?_⟩
    rw [List.length_append, List.length_singleton] at hu
    by_cases hult : u < st.length
    · unfold wstep
      rw [List.getD_append _ _ _ _ hult, List.getD_append _ _ _ _ (by omega)]
      exact hval u hult
    · have hueq : u = st.length := by omega
      subst hueq
      rw [show (st ++ [o]).getD st.length none = o by simp [List.getD_eq_getElem?_getD]]
      rw [show (wstep wD g).getD st.length false = gop g.1 (wD.getD g.2.1 false) (wD.getD g.2.2 false) by
        rw [hlen]; simp [wstep, List.getD_eq_getElem?_getD]]
      exact ⟨ho_lt, ho_val⟩
  have hstep_emit : ∀ (op : GateOp) (hop : op = .and ∨ op = .or) (a b : ℕ)
      (ha_lt : a < 13 + gs.length) (hb_lt : b < 13 + gs.length)
      (heval_eq : op.eval [(evalW gs).getD a false, (evalW gs).getD b false] = gop g.1 (wD.getD g.2.1 false) (wD.getD g.2.2 false)),
      Pin0Inv y (wstep wD g) (st ++ [some (13 + gs.length)], gs ++ [⟨op, [a, b]⟩], skip) := by
    intro op hop a b ha_lt hb_lt heval_eq
    have hew : evalW (gs ++ [⟨op, [a, b]⟩]) = evalW gs ++ [op.eval [(evalW gs).getD a false, (evalW gs).getD b false]] := by
      simp [evalW, List.foldl_append]
    refine ⟨by simp [wstep, hlen], by simp [wstep]; omega, ?_, fun u hu => ?_⟩
    · intro g' hg'
      rcases List.mem_append.1 hg' with hm | hm
      · exact hmono g' hm
      · rw [List.mem_singleton.1 hm]; exact ⟨hop, by simp⟩
    · rw [List.length_append, List.length_singleton] at hu
      by_cases hult : u < st.length
      · unfold wstep
        rw [List.getD_append _ _ _ _ hult, List.getD_append _ _ _ _ (by omega)]
        obtain ⟨h1, h2⟩ := hval u hult
        refine ⟨fun idx hidx => by have := h1 idx hidx; simp; omega, ?_⟩
        cases hst : st.getD u none with
        | none =>
          rw [hst] at h2
          exact h2
        | some idx =>
          have hlt' : idx < (evalW gs).length := by rw [hlenW]; exact h1 idx hst
          change (evalW (gs ++ [⟨op, [a, b]⟩])).getD idx false = _
          rw [hew, List.getD_append _ _ _ _ hlt']
          rw [hst] at h2
          exact h2
      · have hueq : u = st.length := by omega
        subst hueq
        rw [show (st ++ [some (13 + gs.length)]).getD st.length none = some (13 + gs.length) by simp [List.getD_eq_getElem?_getD]]
        rw [show (wstep wD g).getD st.length false = gop g.1 (wD.getD g.2.1 false) (wD.getD g.2.2 false) by
          rw [hlen]; simp [wstep, List.getD_eq_getElem?_getD]]
        refine ⟨fun idx hidx => by cases hidx; simp, ?_⟩
        change (evalW (gs ++ [⟨op, [a, b]⟩])).getD (13 + gs.length) false = _
        rw [hew, ← hlenW, show (evalW gs ++ [op.eval [(evalW gs).getD a false, (evalW gs).getD b false]]).getD (evalW gs).length false =
          op.eval [(evalW gs).getD a false, (evalW gs).getD b false] by simp [List.getD_eq_getElem?_getD]]
        exact heval_eq
  unfold pin0Step
  dsimp only
  cases htag : g.1
  · cases hsa : st.getD g.2.1 none with
    | none =>
      have hwa : wD.getD g.2.1 false = false := by rw [← ha.2, hsa]; rfl
      exact hstep_same (st.getD g.2.2 none) hb.1 (by rw [htag, hb.2, hwa, gop_false, Bool.false_or])
    | some a =>
      cases hsb : st.getD g.2.2 none with
      | none =>
        have hwb : wD.getD g.2.2 false = false := by rw [← hb.2, hsb]; rfl
        exact hstep_same (some a) (fun idx h => ha.1 idx (hsa.trans h)) (by rw [htag, ← hsa, ha.2, hwb, gop_false, Bool.or_false])
      | some b =>
        dsimp only
        split_ifs with hab
        · subst hab
          exact hstep_same (some a) (fun idx h => ha.1 idx (hsa.trans h)) (by
            have hwa : wD.getD g.2.1 false = (evalW gs).getD a false := by rw [← ha.2, hsa]; rfl
            have hwb : wD.getD g.2.2 false = (evalW gs).getD a false := by rw [← hb.2, hsb]; rfl
            rw [htag, hwa, hwb, gop_false, Bool.or_self]; rfl)
        · exact hstep_emit .or (Or.inr rfl) a b (ha.1 a hsa) (hb.1 b hsb) (by
            have hwa : wD.getD g.2.1 false = (evalW gs).getD a false := by rw [← ha.2, hsa]; rfl
            have hwb : wD.getD g.2.2 false = (evalW gs).getD b false := by rw [← hb.2, hsb]; rfl
            rw [htag, hwa, hwb, gop_false]; simp [GateOp.eval])
  · cases hsa : st.getD g.2.1 none with
    | none =>
      have hwa : wD.getD g.2.1 false = false := by rw [← ha.2, hsa]; rfl
      exact hstep_same none (fun _ h => by cases h) (by rw [htag, hwa, gop_true, Bool.false_and]; rfl)
    | some a =>
      cases hsb : st.getD g.2.2 none with
      | none =>
        have hwb : wD.getD g.2.2 false = false := by rw [← hb.2, hsb]; rfl
        exact hstep_same none (fun _ h => by cases h) (by rw [htag, hwb, gop_true, Bool.and_false]; rfl)
      | some b =>
        dsimp only
        split_ifs with hab
        · subst hab
          exact hstep_same (some a) (fun idx h => ha.1 idx (hsa.trans h)) (by
            have hwa : wD.getD g.2.1 false = (evalW gs).getD a false := by rw [← ha.2, hsa]; rfl
            have hwb : wD.getD g.2.2 false = (evalW gs).getD a false := by rw [← hb.2, hsb]; rfl
            rw [htag, hwa, hwb, gop_true, Bool.and_self]; rfl)
        · exact hstep_emit .and (Or.inl rfl) a b (ha.1 a hsa) (hb.1 b hsb) (by
            have hwa : wD.getD g.2.1 false = (evalW gs).getD a false := by rw [← ha.2, hsa]; rfl
            have hwb : wD.getD g.2.2 false = (evalW gs).getD b false := by rw [← hb.2, hsb]; rfl
            rw [htag, hwa, hwb, gop_true]; simp [GateOp.eval])

theorem pin0_fold_inv (y : Fin 13 → Bool) (D : Dag) : ∀ (wD : List Bool) (acc : List (Option ℕ) × List Gate × ℕ),
    (∀ j (hj : j < D.length), (D[j]'hj).2.1 < wD.length + j ∧ (D[j]'hj).2.2 < wD.length + j) →
    Pin0Inv y wD acc → Pin0Inv y (wl D wD) (D.foldl pin0Step acc) := by
  induction D with
  | nil => intro wD acc _ hinv; exact hinv
  | cons g D ih =>
    intro wD acc hlt hinv
    have h0 := hlt 0 (by simp)
    rw [wl, List.foldl_cons, ← wl, List.foldl_cons]
    refine ih (wstep wD g) (pin0Step acc g) (fun j hj => ?_) (pin0_step_inv y wD acc g (by simpa using h0) hinv)
    have hj' := hlt (j + 1) (by simp; omega)
    rw [wstep_length]
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj'

theorem pin0_init_inv (y : Fin 13 → Bool) : Pin0Inv y (List.ofFn (ext0 y)) (pin0Init, [], 0) := by
  refine ⟨by simp [pin0Init], by simp, fun _ h => by simp at h, fun u hu => ?_⟩
  have h14 : u < 14 := by simpa [pin0Init] using hu
  by_cases hu0 : u = 0
  · subst hu0
    refine ⟨fun _ h => by simp [pin0Init] at h, ?_⟩
    simp [pin0Init, optEval, ext0, List.getD_eq_getElem?_getD]
  · have hst : pin0Init.getD u none = some (u - 1) := by
      have : ∀ k : Fin 14, k.val ≠ 0 → pin0Init.getD k.val none = some (k.val - 1) := by decide +kernel
      exact this ⟨u, h14⟩ hu0
    rw [hst]
    refine ⟨fun idx h => by cases h; simp; omega, ?_⟩
    change (List.ofFn y).getD (u - 1) false = (List.ofFn (ext0 y)).getD u false
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn]
    simp [h14, show u - 1 < 13 by omega, ext0, hu0]

theorem pin0Step_skip_ge (acc : List (Option ℕ) × List Gate × ℕ) (g : Bool × ℕ × ℕ) :
    acc.2.2 ≤ (pin0Step acc g).2.2 := by
  rcases acc with ⟨st, gs, skip⟩
  unfold pin0Step; dsimp only
  cases g.1 <;> cases st.getD g.2.1 none <;> cases st.getD g.2.2 none <;> dsimp only <;> (try split_ifs) <;> (try dsimp only) <;> omega

theorem pin0_fold_skip_mono (D : Dag) : ∀ acc, acc.2.2 ≤ (D.foldl pin0Step acc).2.2 := by
  induction D with
  | nil => intro acc; exact le_refl _
  | cons g D ih => intro acc; rw [List.foldl_cons]; exact (pin0Step_skip_ge acc g).trans (ih _)

theorem pin0Step_st_prefix (acc : List (Option ℕ) × List Gate × ℕ) (g : Bool × ℕ × ℕ) :
    ∃ o, (pin0Step acc g).1 = acc.1 ++ [o] := by
  rcases acc with ⟨st, gs, skip⟩
  unfold pin0Step; dsimp only
  cases g.1 <;> cases st.getD g.2.1 none <;> cases st.getD g.2.2 none <;> dsimp only <;> (try split_ifs) <;> exact ⟨_, rfl⟩

theorem pin0_fold_st_getD (D : Dag) : ∀ acc u, u < acc.1.length →
    (D.foldl pin0Step acc).1.getD u none = acc.1.getD u none := by
  induction D with
  | nil => intro acc u _; rfl
  | cons g D ih =>
    intro acc u hu
    obtain ⟨o, ho⟩ := pin0Step_st_prefix acc g
    rw [List.foldl_cons, ih _ u (by rw [ho, List.length_append, List.length_singleton]; omega), ho, List.getD_append _ _ _ _ hu]

theorem pin0_circuit {D : Dag} (h : StrictLive 14 D)
    (hD : ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ G14Edge x) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + (pin0Run D).2.2 = D.length ∧
      ∀ y : Fin 13 → Bool, C'.eval (List.ofFn y) = true ↔ G13Edge y := by
  have hlt : ∀ j (hj : j < D.length), (D[j]'hj).2.1 < (List.ofFn (ext0 (fun _ => false))).length + j ∧
      (D[j]'hj).2.2 < (List.ofFn (ext0 (fun _ => false))).length + j := by
    intro j hj
    have hs := h.1 j hj
    rw [List.length_ofFn, ← opA_eq D j hj, ← opB_eq D j hj]
    exact ⟨hs.1, hs.2.1⟩
  have hinv : ∀ y : Fin 13 → Bool, Pin0Inv y (wl D (List.ofFn (ext0 y))) (pin0Run D) := fun y =>
    pin0_fold_inv y D (List.ofFn (ext0 y)) (pin0Init, [], 0)
      (by intro j hj; simpa [List.length_ofFn] using hlt j hj) (pin0_init_inv y)
  have hlen : (pin0Run D).1.length = 14 + D.length := by
    have := (hinv (fun _ => false)).1
    rw [wl_length, List.length_ofFn] at this; exact this
  have hsum : (pin0Run D).2.1.length + (pin0Run D).2.2 = D.length := by
    have := (hinv (fun _ => false)).2.1
    rw [wl_length, List.length_ofFn] at this
    change (pin0Run D).2.1.length + (pin0Run D).2.2 + 14 = 14 + D.length at this
    omega
  have hout_lt : outW 14 D < (pin0Run D).1.length := by
    have hne : 0 < D.length := List.length_pos_iff.2 h.2.2
    unfold outW; omega
  cases hout : (pin0Run D).1.getD (outW 14 D) none with
  | none =>
    exfalso
    have hev := ((hinv (sem_two 0 6)).2.2.2 (outW 14 D) hout_lt).2
    change optEval _ ((pin0Run D).1.getD (outW 14 D) none) = val D (ext0 (sem_two 0 6)) (outW 14 D) at hev
    rw [hout] at hev
    have ht : val D (ext0 (sem_two 0 6)) (outW 14 D) = true :=
      (hD _).2 ((g14_ext0_iff _).2 (g13_pair (by decide : Adj 0 6)))
    change false = val D (ext0 (sem_two 0 6)) (outW 14 D) at hev
    rw [ht] at hev; exact Bool.noConfusion hev
  | some outIdx =>
    refine ⟨⟨(pin0Run D).2.1, outIdx⟩, (hinv (fun _ => false)).2.2.1, hsum, fun y => ?_⟩
    have hev := ((hinv y).2.2.2 (outW 14 D) hout_lt).2
    change optEval _ ((pin0Run D).1.getD (outW 14 D) none) = val D (ext0 y) (outW 14 D) at hev
    rw [hout] at hev
    have hce : (⟨(pin0Run D).2.1, outIdx⟩ : Circuit).eval (List.ofFn y) =
        optEval ((pin0Run D).2.1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) (List.ofFn y)) (some outIdx) := rfl
    unfold pin0Run at hce ⊢
    rw [hce, hev]
    exact (hD (ext0 y)).trans (g14_ext0_iff y)

theorem pin0_skip_at {D : Dag} (j : ℕ) (hj : j < D.length)
    (hnone : ((D.take j).foldl pin0Step (pin0Init, [], 0)).1.getD (opA D j) none = none ∨
             ((D.take j).foldl pin0Step (pin0Init, [], 0)).1.getD (opB D j) none = none) :
    ((D.take j).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤
      ((D.take (j + 1)).foldl pin0Step (pin0Init, [], 0)).2.2 := by
  have htk : D.take (j + 1) = D.take j ++ [D[j]] := List.take_succ_eq_append_getElem hj
  rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize ((D.take j).foldl pin0Step (pin0Init, [], 0)) = acc at hnone ⊢
  rcases acc with ⟨st, gs, skip⟩
  rw [opA_eq D j hj, opB_eq D j hj] at hnone
  unfold pin0Step; dsimp only
  rcases hnone with hA | hB
  · rw [hA]; cases (D[j]).1 <;> cases st.getD (D[j]).2.2 none <;> dsimp only <;> omega
  · rw [hB]; cases (D[j]).1 <;> cases st.getD (D[j]).2.1 none <;> dsimp only <;> omega

theorem pin0_two_skips {D : Dag} {j1 j2 : ℕ} (h12 : j1 < j2) (hj2 : j2 < D.length)
    (h1 : ((D.take j1).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤ ((D.take (j1 + 1)).foldl pin0Step (pin0Init, [], 0)).2.2)
    (h2 : ((D.take j2).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤ ((D.take (j2 + 1)).foldl pin0Step (pin0Init, [], 0)).2.2) :
    2 ≤ (pin0Run D).2.2 := by
  have hm : ∀ a b, a ≤ b → b ≤ D.length →
      ((D.take a).foldl pin0Step (pin0Init, [], 0)).2.2 ≤ ((D.take b).foldl pin0Step (pin0Init, [], 0)).2.2 := by
    intro a b hab hbl
    have hta : (D.take b).take a = D.take a := by rw [List.take_take, Nat.min_eq_left hab]
    have hsp : D.take b = D.take a ++ (D.take b).drop a := by
      rw [← hta]; exact (List.take_append_drop a (D.take b)).symm
    conv_rhs => rw [hsp, List.foldl_append]
    exact pin0_fold_skip_mono _ _
  have s1 := hm (j1 + 1) j2 (by omega) (by omega)
  have s2 := hm (j2 + 1) D.length (by omega) (le_refl _)
  rw [List.take_length] at s2
  change _ ≤ (pin0Run D).2.2 at s2
  omega

theorem pin0_st_len (D : Dag) (k : ℕ) (hk : k ≤ D.length) :
    ((D.take k).foldl pin0Step (pin0Init, [], 0)).1.length = 14 + k := by
  induction k with
  | zero => simp [pin0Init]
  | succ k ih =>
    have htk : D.take (k + 1) = D.take k ++ [D[k]] := List.take_succ_eq_append_getElem (by omega)
    rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨o, ho⟩ := pin0Step_st_prefix _ _
    rw [ho, List.length_append, List.length_singleton, ih (by omega)]
    omega

def mapW (j0 w : ℕ) (u : ℕ) : ℕ :=
  if u = 14 + j0 then w - 1
  else if u < 14 + j0 then u - 1
  else u - 2

def delGate (D : Dag) (j0 w : ℕ) : Dag :=
  (D.take j0 ++ D.drop (j0 + 1)).map (fun g => (g.1, mapW j0 w g.2.1, mapW j0 w g.2.2))

theorem g14_no_circuit (C : Circuit) (hmono : Monotone2 C) (hsize : C.size ≤ 24)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) : False := by
  classical
  obtain ⟨D, h, hlenD, hD⟩ := g14_normalize C hmono hC
  have hD24 : D.length ≤ 24 := le_trans hlenD hsize
  have hS := h.1
  have hkill22 : 2 ≤ (pin0Run D).2.2 → False := by
    intro hsk
    obtain ⟨C', hm', hsz', hC'⟩ := pin0_circuit h hD
    obtain ⟨D', h', hlen', hD'⟩ := g13_normalize C' hm' hC'
    have h23 := (g13_classify h' hD' (by omega)).1
    omega
  have h0_none : ∀ k, k ≤ D.length → ((D.take k).foldl pin0Step (pin0Init, [], 0)).1.getD 0 none = none := fun k _ => by
    rw [pin0_fold_st_getD _ _ 0 (by decide)]; rfl
  have hfo0_pos : 1 ≤ fanout D 0 := h.2.1 0 (by have := List.length_pos_iff.2 h.2.2; omega)
  by_cases hfo0_2 : 2 ≤ fanout D 0
  · obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.1 (show 1 < (readers D 0).card from hfo0_2)
    have hstep : ∀ j ∈ readers D 0, j < D.length ∧
        ((D.take j).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤
          ((D.take (j + 1)).foldl pin0Step (pin0Init, [], 0)).2.2 := by
      intro j hj
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      refine ⟨hj.1, pin0_skip_at j hj.1 ?_⟩
      rcases hj.2 with hA | hB
      · left; rw [hA]; exact h0_none j (by omega)
      · right; rw [hB]; exact h0_none j (by omega)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hkill22 (pin0_two_skips hlt (hstep j2 hj2).1 (hstep j1 hj1).2 (hstep j2 hj2).2)
    · exact hkill22 (pin0_two_skips hlt (hstep j1 hj1).1 (hstep j2 hj2).2 (hstep j1 hj1).2)
  · have hfo0_1 : fanout D 0 = 1 := by omega
    obtain ⟨j0, hj0⟩ := Finset.card_eq_one.1 (show (readers D 0).card = 1 from hfo0_1)
    have hj0m : j0 ∈ readers D 0 := hj0 ▸ Finset.mem_singleton_self j0
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj0m
    obtain ⟨hj0lt, hj0op⟩ := hj0m
    have hnot_out : 14 + j0 ≠ outW 14 D := by
      intro heq
      cases ht : tag D j0
      · have htrue : val D (single (0 : Fin 14)) (outW 14 D) = true := by
          rw [← heq, val_gate hS _ j0 hj0lt, ht, gop_false, Bool.or_eq_true]
          rcases hj0op with hA | hB
          · left; rw [hA, val_input D _ 0 (by decide)]; simp [single]
          · right; rw [hB, val_input D _ 0 (by decide)]; simp [single]
        exact g14_not_single 0 ((hD _).1 htrue)
      · have hfalse : val D (ext0 (sem_two 0 6)) (outW 14 D) = false := by
          rw [← heq, val_gate hS _ j0 hj0lt, ht, gop_true, Bool.and_eq_false_iff]
          rcases hj0op with hA | hB
          · left; rw [hA, val_input D _ 0 (by decide)]; simp [ext0]
          · right; rw [hB, val_input D _ 0 (by decide)]; simp [ext0]
        have htrue : val D (ext0 (sem_two 0 6)) (outW 14 D) = true :=
          (hD _).2 ((g14_ext0_iff _).2 (g13_pair (by decide : Adj 0 6)))
        rw [hfalse] at htrue; exact Bool.noConfusion htrue
    have hfo_j0 : 1 ≤ fanout D (14 + j0) := h.2.1 (14 + j0) (by unfold outW at hnot_out; omega)
    obtain ⟨j1, hj1m⟩ := Finset.card_pos.1 hfo_j0
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj1m
    obtain ⟨hj1lt, hj1op⟩ := hj1m
    have hj01 : j0 < j1 := by
      have hs := hS j1 hj1lt
      rcases hj1op with hA | hB <;> omega
    by_cases htag0 : tag D j0 = true
    · have hs0 : ((D.take j0).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤
          ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).2.2 := by
        refine pin0_skip_at j0 hj0lt ?_
        rcases hj0op with hA | hB
        · left; rw [hA]; exact h0_none j0 (by omega)
        · right; rw [hB]; exact h0_none j0 (by omega)
      have hj0_none_next : ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).1.getD (14 + j0) none = none := by
        have htk : D.take (j0 + 1) = D.take j0 ++ [D[j0]] := List.take_succ_eq_append_getElem hj0lt
        rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlenj := pin0_st_len D j0 (by omega)
        have h0n := h0_none j0 (by omega)
        have h1 : (D[j0]).1 = true := by rw [← tag_eq D j0 hj0lt]; exact htag0
        have h2 : (D[j0]).2.1 = 0 ∨ (D[j0]).2.2 = 0 := by rw [← opA_eq D j0 hj0lt, ← opB_eq D j0 hj0lt]; exact hj0op
        generalize ((D.take j0).foldl pin0Step (pin0Init, [], 0)) = acc at hlenj h0n ⊢
        rcases acc with ⟨st, gs, skip⟩
        unfold pin0Step; dsimp only
        rw [h1]
        rcases h2 with hA | hB
        · rw [hA, h0n]; dsimp only; rw [← hlenj]; simp [List.getD_eq_getElem?_getD]
        · rw [hB, h0n]; cases st.getD (D[j0]).2.1 none <;> (dsimp only; rw [← hlenj]; simp [List.getD_eq_getElem?_getD])
      have hj0_none_j1 : ((D.take j1).foldl pin0Step (pin0Init, [], 0)).1.getD (14 + j0) none = none := by
        have hsp : D.take j1 = D.take (j0 + 1) ++ (D.take j1).drop (j0 + 1) := by
          have := (List.take_append_drop (j0 + 1) (D.take j1)).symm
          rwa [List.take_take, Nat.min_eq_left (by omega)] at this
        rw [hsp, List.foldl_append, pin0_fold_st_getD _ _ (14 + j0) (by rw [pin0_st_len D (j0 + 1) (by omega)]; omega)]
        exact hj0_none_next
      have hs1 : ((D.take j1).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤
          ((D.take (j1 + 1)).foldl pin0Step (pin0Init, [], 0)).2.2 := by
        refine pin0_skip_at j1 hj1lt ?_
        rcases hj1op with hA | hB
        · left; rw [hA]; exact hj0_none_j1
        · right; rw [hB]; exact hj0_none_j1
      exact hkill22 (pin0_two_skips hj01 hj1lt hs0 hs1)
    · have htag0f : tag D j0 = false := Bool.eq_false_iff.2 htag0
      obtain ⟨w, hw_lt, hw_ne0, hw_other⟩ : ∃ w, w < 14 + j0 ∧ w ≠ 0 ∧
          ((opA D j0 = 0 ∧ opB D j0 = w) ∨ (opA D j0 = w ∧ opB D j0 = 0)) := by
        obtain ⟨ha, hb, hne⟩ := hS j0 hj0lt
        rcases hj0op with hA | hB
        · exact ⟨opB D j0, hb, fun h => hne (hA.trans h.symm), Or.inl ⟨hA, rfl⟩⟩
        · exact ⟨opA D j0, ha, fun h => hne (h.trans hB.symm), Or.inr ⟨rfl, hB⟩⟩
      let Draw := delGate D j0 w
      have hDraw_len : Draw.length = D.length - 1 := by
        simp [Draw, delGate, List.length_take, List.length_drop]; omega
      have hDraw_gt : ∀ j, j < D.length → j ≠ j0 → opA D j ≠ 0 ∧ opB D j ≠ 0 := by
        intro j hj hne
        have hnr : j ∉ readers D 0 := by rw [hj0, Finset.mem_singleton]; exact hne
        simp only [readers, Finset.mem_filter, Finset.mem_range, not_and, not_or] at hnr
        exact hnr hj
      have hmap_lt : ∀ u, u ≠ 0 → u < 14 + j0 → mapW j0 w u = u - 1 := fun u _ hlt => by
        unfold mapW; split_ifs <;> omega
      have hmap_gt : ∀ u, 14 + j0 < u → mapW j0 w u = u - 2 := fun u hgt => by
        unfold mapW; split_ifs <;> omega
      have hmap_j0 : mapW j0 w (14 + j0) = w - 1 := by unfold mapW; simp
      have hDraw_gate_lt : ∀ j (hj : j < j0), Draw[j]'(by rw [hDraw_len]; omega) = (tag D j, mapW j0 w (opA D j), mapW j0 w (opB D j)) := by
        intro j hj
        simp only [Draw, delGate, List.getElem_map, List.getElem_append_left (by simp; omega : j < (D.take j0).length),
          List.getElem_take, tag_eq D j (by omega), opA_eq D j (by omega), opB_eq D j (by omega)]
      have hDraw_gate_gt : ∀ j (hj : j0 < j) (hjlt : j < D.length),
          Draw[j - 1]'(by rw [hDraw_len]; omega) = (tag D j, mapW j0 w (opA D j), mapW j0 w (opB D j)) := by
        intro j hj hjlt
        have hlen_tk : (D.take j0).length = j0 := by simp; omega
        simp only [Draw, delGate, List.getElem_map, List.getElem_append_right (by omega : (D.take j0).length ≤ j - 1),
          hlen_tk, List.getElem_drop, show j0 + 1 + (j - 1 - j0) = j by omega,
          tag_eq D j hjlt, opA_eq D j hjlt, opB_eq D j hjlt]
      by_cases hcoll : ∃ j, j < D.length ∧ j ≠ j0 ∧ mapW j0 w (opA D j) = mapW j0 w (opB D j)
      · obtain ⟨jc, hjclt, hjcne, hceq⟩ := hcoll
        obtain ⟨hca, hcb, hcne⟩ := hS jc hjclt
        obtain ⟨hca0, hcb0⟩ := hDraw_gt jc hjclt hjcne
        have hpair : (opA D jc = 14 + j0 ∧ opB D jc = w) ∨ (opA D jc = w ∧ opB D jc = 14 + j0) := by
          unfold mapW at hceq
          split_ifs at hceq <;> omega
        have hj0c : j0 < jc := by rcases hpair with ⟨hA, _⟩ | ⟨_, hB⟩ <;> omega
        have hs0 : ((D.take j0).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤
            ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).2.2 := by
          refine pin0_skip_at j0 hj0lt ?_
          rcases hj0op with hA | hB
          · left; rw [hA]; exact h0_none j0 (by omega)
          · right; rw [hB]; exact h0_none j0 (by omega)
        have hst_eq_next : ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).1.getD (14 + j0) none =
            ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).1.getD w none := by
          have htk : D.take (j0 + 1) = D.take j0 ++ [D[j0]] := List.take_succ_eq_append_getElem hj0lt
          rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlenj := pin0_st_len D j0 (by omega)
          have h0n := h0_none j0 (by omega)
          have h1 : (D[j0]).1 = false := by rw [← tag_eq D j0 hj0lt]; exact htag0f
          have h2 : ((D[j0]).2.1 = 0 ∧ (D[j0]).2.2 = w) ∨ ((D[j0]).2.1 = w ∧ (D[j0]).2.2 = 0) := by
            rw [← opA_eq D j0 hj0lt, ← opB_eq D j0 hj0lt]; exact hw_other
          generalize ((D.take j0).foldl pin0Step (pin0Init, [], 0)) = acc at hlenj h0n ⊢
          rcases acc with ⟨st, gs, skip⟩
          dsimp only at hlenj h0n
          unfold pin0Step; dsimp only
          rw [h1]
          rcases h2 with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · rw [hA, hB, h0n]; dsimp only
            rw [show (st ++ [st.getD w none]).getD (14 + j0) none = st.getD w none by rw [← hlenj]; simp [List.getD_eq_getElem?_getD]]
            rw [List.getD_append _ _ _ _ (by omega)]
          · rw [hA, hB, h0n]
            cases hsw : st.getD w none with
            | none =>
              dsimp only
              rw [show (st ++ [(none : Option ℕ)]).getD (14 + j0) none = none by rw [← hlenj]; simp [List.getD_eq_getElem?_getD]]
              rw [List.getD_append _ _ _ _ (by omega), hsw]
            | some a =>
              dsimp only
              rw [show (st ++ [some a]).getD (14 + j0) none = some a by rw [← hlenj]; simp [List.getD_eq_getElem?_getD]]
              rw [List.getD_append _ _ _ _ (by omega), hsw]
        have hst_eq_jc : ((D.take jc).foldl pin0Step (pin0Init, [], 0)).1.getD (opA D jc) none =
            ((D.take jc).foldl pin0Step (pin0Init, [], 0)).1.getD (opB D jc) none := by
          have hsp : D.take jc = D.take (j0 + 1) ++ (D.take jc).drop (j0 + 1) := by
            have := (List.take_append_drop (j0 + 1) (D.take jc)).symm
            rwa [List.take_take, Nat.min_eq_left (by omega)] at this
          have hlen1 := pin0_st_len D (j0 + 1) (by omega)
          have h1' : ((D.take jc).foldl pin0Step (pin0Init, [], 0)).1.getD (14 + j0) none =
              ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).1.getD (14 + j0) none := by
            rw [hsp, List.foldl_append]; exact pin0_fold_st_getD _ _ (14 + j0) (by omega)
          have h2' : ((D.take jc).foldl pin0Step (pin0Init, [], 0)).1.getD w none =
              ((D.take (j0 + 1)).foldl pin0Step (pin0Init, [], 0)).1.getD w none := by
            rw [hsp, List.foldl_append]; exact pin0_fold_st_getD _ _ w (by omega)
          rcases hpair with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · rw [hA, hB, h1', h2', hst_eq_next]
          · rw [hA, hB, h1', h2', hst_eq_next]
        have hsc : ((D.take jc).foldl pin0Step (pin0Init, [], 0)).2.2 + 1 ≤
            ((D.take (jc + 1)).foldl pin0Step (pin0Init, [], 0)).2.2 := by
          have htk : D.take (jc + 1) = D.take jc ++ [D[jc]] := List.take_succ_eq_append_getElem hjclt
          rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [opA_eq D jc hjclt, opB_eq D jc hjclt] at hst_eq_jc
          generalize ((D.take jc).foldl pin0Step (pin0Init, [], 0)) = acc at hst_eq_jc ⊢
          rcases acc with ⟨st, gs, skip⟩
          unfold pin0Step; dsimp only
          rw [hst_eq_jc]
          cases (D[jc]).1 <;> cases st.getD (D[jc]).2.2 none <;> dsimp only <;> simp
        exact hkill22 (pin0_two_skips hj0c hjclt hs0 hsc)
      · push Not at hcoll
        have hStrictDraw : Strict 13 Draw := by
          intro k hk
          by_cases hkj0 : k < j0
          · have hge := hDraw_gate_lt k hkj0
            rw [opA_eq Draw k hk, opB_eq Draw k hk, hge]; dsimp only
            obtain ⟨ha, hb, -⟩ := hS k (by omega)
            obtain ⟨ha0, hb0⟩ := hDraw_gt k (by omega) (by omega)
            rw [hmap_lt _ ha0 (by omega), hmap_lt _ hb0 (by omega)]
            exact ⟨by omega, by omega, by rw [← hmap_lt _ ha0 (by omega), ← hmap_lt _ hb0 (by omega)]; exact hcoll k (by omega) (by omega)⟩
          · have hge := hDraw_gate_gt (k + 1) (by omega) (by omega)
            have hge' : Draw[k]'hk = (tag D (k + 1), mapW j0 w (opA D (k + 1)), mapW j0 w (opB D (k + 1))) := by simpa using hge
            rw [opA_eq Draw k hk, opB_eq Draw k hk, hge']; dsimp only
            obtain ⟨ha, hb, -⟩ := hS (k + 1) (by omega)
            obtain ⟨ha0, hb0⟩ := hDraw_gt (k + 1) (by omega) (by omega)
            have hlt_m : ∀ u, u ≠ 0 → u < 14 + (k + 1) → mapW j0 w u < 13 + k := by
              intro u hu0 hult
              unfold mapW; split_ifs <;> omega
            exact ⟨hlt_m _ ha0 ha, hlt_m _ hb0 hb, hcoll (k + 1) (by omega) (by omega)⟩
        have hLiveDraw : Live 13 Draw := by
          intro u hu
          have hult : u < 13 + D.length - 2 := by omega
          by_cases hu_w : u = w - 1
          · refine Finset.card_pos.2 ⟨j1 - 1, ?_⟩
            rw [readers, Finset.mem_filter, Finset.mem_range]
            have hge := hDraw_gate_gt j1 hj01 hj1lt
            refine ⟨by omega, ?_⟩
            rw [opA_eq Draw (j1 - 1) (by omega), opB_eq Draw (j1 - 1) (by omega), hge]; dsimp only
            rcases hj1op with hA | hB
            · left; rw [hA, hmap_j0, hu_w]
            · right; rw [hB, hmap_j0, hu_w]
          · let u0 := if u + 1 < 14 + j0 then u + 1 else u + 2
            have hu0_map : mapW j0 w u0 = u := by unfold u0 mapW; split_ifs <;> omega
            have hu0_lt : u0 + 1 < 14 + D.length := by unfold u0; split_ifs <;> omega
            have hu0_ne0 : u0 ≠ 0 := by unfold u0; split_ifs <;> omega
            have hu0_nej0 : u0 ≠ 14 + j0 := by unfold u0; split_ifs <;> omega
            have hu0_new : u0 ≠ w := by intro heq; apply hu_w; rw [← hu0_map, heq, hmap_lt w hw_ne0 hw_lt]
            obtain ⟨r, hrm⟩ := Finset.card_pos.1 (h.2.1 u0 hu0_lt)
            simp only [readers, Finset.mem_filter, Finset.mem_range] at hrm
            obtain ⟨hrlt, hrop⟩ := hrm
            have hr_nej0 : r ≠ j0 := by
              intro heq; subst heq
              rcases hw_other with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> rcases hrop with h1' | h1'
              · exact hu0_ne0 (h1'.symm.trans hA)
              · exact hu0_new (h1'.symm.trans hB)
              · exact hu0_new (h1'.symm.trans hA)
              · exact hu0_ne0 (h1'.symm.trans hB)
            refine Finset.card_pos.2 ⟨if r < j0 then r else r - 1, ?_⟩
            rw [readers, Finset.mem_filter, Finset.mem_range]
            split_ifs with hrj0
            · refine ⟨by omega, ?_⟩
              rw [opA_eq Draw r (by omega), opB_eq Draw r (by omega), hDraw_gate_lt r hrj0]; dsimp only
              rcases hrop with hA | hB
              · left; rw [hA, hu0_map]
              · right; rw [hB, hu0_map]
            · refine ⟨by omega, ?_⟩
              rw [opA_eq Draw (r - 1) (by omega), opB_eq Draw (r - 1) (by omega), hDraw_gate_gt r (by omega) hrlt]; dsimp only
              rcases hrop with hA | hB
              · left; rw [hA, hu0_map]
              · right; rw [hB, hu0_map]
        have hDraw_ne : Draw ≠ [] := by
          intro hemp
          have hlen0 : Draw.length = 0 := by rw [hemp]; rfl
          have hD1 : D.length ≤ 1 := by omega
          apply hnot_out; unfold outW; omega
        have hSLDraw : StrictLive 13 Draw := ⟨hStrictDraw, hLiveDraw, hDraw_ne⟩
        have hval0 : ∀ y : Fin 13 → Bool, ∀ u, u ≠ 0 → u < 14 + D.length →
            val Draw y (mapW j0 w u) = val D (ext0 y) u := by
          intro y u
          induction u using Nat.strong_induction_on with
          | _ u ih =>
            intro hu0 hult
            by_cases hn : u < 14
            · rw [hmap_lt u hu0 (by omega), val_input Draw y (u - 1) (by omega), val_input D (ext0 y) u hn]
              simp [ext0, hu0]
            · obtain ⟨j, rfl⟩ : ∃ j, u = 14 + j := ⟨u - 14, by omega⟩
              have hjlt : j < D.length := by omega
              by_cases hjj0 : j = j0
              · subst j
                rw [hmap_j0, val_gate hS (ext0 y) j0 hj0lt, htag0f, gop_false]
                have h0f : val D (ext0 y) 0 = false := by rw [val_input D (ext0 y) 0 (by decide)]; simp [ext0]
                have hw_eq : val Draw y (w - 1) = val D (ext0 y) w := by
                  rw [← hmap_lt w hw_ne0 hw_lt]; exact ih w hw_lt hw_ne0 (by omega)
                rcases hw_other with ⟨hA, hB⟩ | ⟨hA, hB⟩
                · rw [hA, hB, h0f, Bool.false_or, hw_eq]
                · rw [hA, hB, h0f, Bool.or_false, hw_eq]
              · obtain ⟨ha, hb, -⟩ := hS j hjlt
                obtain ⟨ha0, hb0⟩ := hDraw_gt j hjlt hjj0
                by_cases hlt0 : j < j0
                · rw [hmap_lt (14 + j) (by omega) (by omega), show 14 + j - 1 = 13 + j by omega]
                  rw [val_gate hStrictDraw y j (by omega), val_gate hS (ext0 y) j hjlt]
                  have hge := hDraw_gate_lt j hlt0
                  rw [tag_eq Draw j (by omega), opA_eq Draw j (by omega), opB_eq Draw j (by omega), hge]; dsimp only
                  rw [ih _ ha ha0 (by omega), ih _ hb hb0 (by omega)]
                · rw [hmap_gt (14 + j) (by omega), show 14 + j - 2 = 13 + (j - 1) by omega]
                  rw [val_gate hStrictDraw y (j - 1) (by omega), val_gate hS (ext0 y) j hjlt]
                  have hge := hDraw_gate_gt j (by omega) hjlt
                  rw [tag_eq Draw (j - 1) (by omega), opA_eq Draw (j - 1) (by omega), opB_eq Draw (j - 1) (by omega), hge]; dsimp only
                  rw [ih _ ha ha0 (by omega), ih _ hb hb0 (by omega)]
        have hCorrectDraw : Correct Draw := fun y => by
          have hout_map : mapW j0 w (outW 14 D) = outW 13 Draw := by
            unfold outW mapW; split_ifs <;> omega
          rw [← hout_map, hval0 y (outW 14 D) (by unfold outW; omega) (by unfold outW; have := List.length_pos_iff.2 h.2.2; omega)]
          exact (hD (ext0 y)).trans (g14_ext0_iff y)
        obtain ⟨hDraw23, -, hDrawB0, hDrawI, hDrawOcc⟩ := g13_classify hSLDraw hCorrectDraw (by omega)
        have hw'_sub : supp 13 Draw (w - 1) ⊆ ({3, 4} : Finset (Fin 13)) := by
          intro v hv
          have hv1 : val Draw (sem_two v 9) (w - 1) = true :=
            sem_val_of_supp hStrictDraw hv (by simp [sem_two])
          have hDw : val D (ext0 (sem_two v 9)) w = true := by
            rw [← hval0 (sem_two v 9) w hw_ne0 (by omega), hmap_lt w hw_ne0 hw_lt]; exact hv1
          have hj0_eq : val D (ext0 (sem_two v 9)) (14 + j0) = val D (ext1 (sem_two v 9)) (14 + j0) := by
            rw [val_gate hS (ext0 _) j0 hj0lt, val_gate hS (ext1 _) j0 hj0lt, htag0f, gop_false, gop_false]
            have h0_1 : val D (ext1 (sem_two v 9)) 0 = true := by rw [val_input D _ 0 (by decide)]; simp [ext1]
            rcases hw_other with ⟨hA, hB⟩ | ⟨hA, hB⟩
            · rw [hA, hB, hDw, h0_1]; simp
            · rw [hA, hB, hDw, h0_1]; simp
          have hdom0 : sem_Dom 14 D (14 + j0) (0 : Fin 14).val := by
            apply sem_chain_dom hS
            refine Relation.ReflTransGen.single ⟨⟨by omega, by omega, ?_⟩, hfo0_1⟩
            rw [Nat.add_sub_cancel_left]; exact hj0op
          have hout_eq := sem_dom_eq hS (ext0 (sem_two v 9)) (ext1 (sem_two v 9)) (0 : Fin 14)
            (fun k hk => by simp [ext0, ext1, hk]) (14 + j0) hdom0 hj0_eq
          have h1true : val D (ext1 (sem_two v 9)) (outW 14 D) = true :=
            (hD _).2 ((g14_ext1_iff _).2 (Or.inl (by simp [sem_two])))
          rw [← hout_eq] at h1true
          have hedge13 : G13Edge (sem_two v 9) := (g14_ext0_iff _).1 ((hD _).1 h1true)
          rw [g13Edge_iff_adj] at hedge13
          obtain ⟨a, b', hab, ha, hb⟩ := hedge13
          simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hb
          have hv9 : Adj v 9 := by
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd hab (adj_irrefl _)
            · exact hab
            · exact adj_symm hab
            · exact absurd hab (adj_irrefl _)
          have h9nbrs : ∀ x : Fin 13, hc_adjB x 9 = true → x = 3 ∨ x = 4 := by decide +kernel
          rcases h9nbrs v ((hc_adjB_iff v 9).2 hv9) with rfl | rfl <;> simp
        have hfo_w' : fanout Draw (w - 1) ≤ 1 := by
          by_cases hne : (supp 13 Draw (w - 1)).Nonempty
          · obtain ⟨v, hv⟩ := hne
            have hvI : v ∈ ineligSet 13 Draw := by
              rw [hDrawI]
              have hv34 := hw'_sub hv
              simp only [Finset.mem_insert, Finset.mem_singleton] at hv34
              rcases hv34 with rfl | rfl <;> decide
            exact mem_ineligSet.1 hvI (w - 1) hv
          · have hemp : supp 13 Draw (w - 1) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
            by_contra hgt
            have hbz := bz_card hStrictDraw {w - 1} (fun b hb => by rw [Finset.mem_singleton.1 hb]; exact ⟨by omega, hemp⟩)
            rw [Finset.card_singleton, hDrawB0] at hbz; omega
        have hw_no_other : ∀ j, j < D.length → j ≠ j0 → opA D j ≠ w ∧ opB D j ≠ w := by
          intro j hj hne
          have hnot : ¬ (opA D j = w ∨ opB D j = w) := by
            intro hread
            have hj_nej1 : j ≠ j1 := by
              intro heq; subst j
              apply hcoll j1 hj1lt (by omega)
              rcases hj1op with hA1 | hB1 <;> rcases hread with hA2 | hB2
              · exact absurd (hA1.symm.trans hA2) (by omega)
              · rw [hA1, hB2, hmap_j0, hmap_lt w hw_ne0 hw_lt]
              · rw [hA2, hB1, hmap_j0, hmap_lt w hw_ne0 hw_lt]
              · exact absurd (hB1.symm.trans hB2) (by omega)
            let r1 := j1 - 1
            let r2 := if j < j0 then j else j - 1
            have hr12 : r1 ≠ r2 := by dsimp only [r1, r2]; split_ifs <;> omega
            have hm1 : r1 ∈ readers Draw (w - 1) := by
              rw [readers, Finset.mem_filter, Finset.mem_range]
              refine ⟨by omega, ?_⟩
              rw [opA_eq Draw r1 (by omega), opB_eq Draw r1 (by omega), hDraw_gate_gt j1 hj01 hj1lt]; dsimp only
              rcases hj1op with hA | hB
              · left; rw [hA, hmap_j0]
              · right; rw [hB, hmap_j0]
            have hm2 : r2 ∈ readers Draw (w - 1) := by
              rw [readers, Finset.mem_filter, Finset.mem_range]
              dsimp only [r2]
              split_ifs with hlt
              · refine ⟨by omega, ?_⟩
                rw [opA_eq Draw j (by omega), opB_eq Draw j (by omega), hDraw_gate_lt j hlt]; dsimp only
                rcases hread with hA | hB
                · left; rw [hA, hmap_lt w hw_ne0 hw_lt]
                · right; rw [hB, hmap_lt w hw_ne0 hw_lt]
              · refine ⟨by omega, ?_⟩
                rw [opA_eq Draw (j - 1) (by omega), opB_eq Draw (j - 1) (by omega), hDraw_gate_gt j (by omega) hj]; dsimp only
                rcases hread with hA | hB
                · left; rw [hA, hmap_lt w hw_ne0 hw_lt]
                · right; rw [hB, hmap_lt w hw_ne0 hw_lt]
            have h2 : 2 ≤ fanout Draw (w - 1) := by
              have hsub2 : ({r1, r2} : Finset ℕ) ⊆ readers Draw (w - 1) := by
                intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
              have := Finset.card_le_card hsub2
              rw [Finset.card_pair hr12] at this; exact this
            omega
          rw [not_or] at hnot; exact hnot
        have hval1 : ∀ y : Fin 13 → Bool, ∀ u, u ≠ 0 → u ≠ w → u < 14 + D.length →
            val1 Draw (w - 1) y (mapW j0 w u) = val D (ext1 y) u := by
          intro y u
          induction u using Nat.strong_induction_on with
          | _ u ih =>
            intro hu0 huw hult
            have hmap_ne : u ≠ 14 + j0 → mapW j0 w u ≠ w - 1 := fun huj => by
              unfold mapW; split_ifs <;> omega
            by_cases hn : u < 14
            · rw [hmap_lt u hu0 (by omega), val1_input Draw (w - 1) y (u - 1) (by omega), val_input D (ext1 y) u hn]
              have hne' : u - 1 ≠ w - 1 := by omega
              simp [hne', ext1, hu0]
            · obtain ⟨j, rfl⟩ : ∃ j, u = 14 + j := ⟨u - 14, by omega⟩
              have hjlt : j < D.length := by omega
              by_cases hjj0 : j = j0
              · subst j
                rw [hmap_j0, val1_self hStrictDraw (w - 1) (by omega), val_gate hS (ext1 y) j0 hj0lt, htag0f, gop_false]
                have h0_1 : val D (ext1 y) 0 = true := by rw [val_input D _ 0 (by decide)]; simp [ext1]
                rcases hw_other with ⟨hA, hB⟩ | ⟨hA, hB⟩
                · rw [hA, h0_1]; simp
                · rw [hB, h0_1]; simp
              · obtain ⟨ha, hb, -⟩ := hS j hjlt
                obtain ⟨ha0, hb0⟩ := hDraw_gt j hjlt hjj0
                obtain ⟨haw, hbw⟩ := hw_no_other j hjlt hjj0
                by_cases hlt0 : j < j0
                · have hne' : 13 + j ≠ w - 1 := by have := hmap_ne (by omega); rw [hmap_lt _ (by omega) (by omega)] at this; omega
                  rw [hmap_lt (14 + j) (by omega) (by omega), show 14 + j - 1 = 13 + j by omega]
                  rw [val1_gate hStrictDraw (w - 1) y j (by omega), val_gate hS (ext1 y) j hjlt]
                  simp only [hne', ↓reduceIte]
                  have hge := hDraw_gate_lt j hlt0
                  rw [tag_eq Draw j (by omega), opA_eq Draw j (by omega), opB_eq Draw j (by omega), hge]; dsimp only
                  rw [ih _ ha ha0 haw (by omega), ih _ hb hb0 hbw (by omega)]
                · have hne' : 13 + (j - 1) ≠ w - 1 := by have := hmap_ne (by omega); rw [hmap_gt _ (by omega)] at this; omega
                  rw [hmap_gt (14 + j) (by omega), show 14 + j - 2 = 13 + (j - 1) by omega]
                  rw [val1_gate hStrictDraw (w - 1) y (j - 1) (by omega), val_gate hS (ext1 y) j hjlt]
                  simp only [hne', ↓reduceIte]
                  have hge := hDraw_gate_gt j (by omega) hjlt
                  rw [tag_eq Draw (j - 1) (by omega), opA_eq Draw (j - 1) (by omega), opB_eq Draw (j - 1) (by omega), hge]; dsimp only
                  rw [ih _ ha ha0 haw (by omega), ih _ hb hb0 hbw (by omega)]
        have h1_iff : ∀ y : Fin 13 → Bool, val1 Draw (w - 1) y (outW 13 Draw) = true ↔ y 9 = true ∨ G13Edge y := by
          intro y
          have hout_map : mapW j0 w (outW 14 D) = outW 13 Draw := by unfold outW mapW; split_ifs <;> omega
          rw [← hout_map, hval1 y (outW 14 D) (by unfold outW; omega) (by unfold outW; omega) (by unfold outW; omega)]
          exact (hD (ext1 y)).trans (g14_ext1_iff y)
        exact kill_Lprime_with_w hSLDraw hCorrectDraw hDraw23 hDrawI hDrawB0 hDrawOcc (w - 1) (by omega) hw'_sub h1_iff

end PEqualNP.Outside.L_meta_9772_aux

theorem PEqualNP.Outside.L_meta_9772 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsize, hC⟩
  exact PEqualNP.Outside.L_meta_9772_aux.g14_no_circuit C hmono hsize hC
