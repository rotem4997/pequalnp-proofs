import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7107

namespace FullTapeCore

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

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

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

def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def G10Edge (x : Fin 10 → Bool) : Prop :=
  ∃ u v : Fin 10, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 10) : Prop :=
  (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def adjBits (u : Fin 10) : ℕ :=
  match u.val with
  | 0 => 50 | 1 => 69 | 2 => 138 | 3 => 276 | 4 => 521 | 5 => 385 | 6 => 770 | 7 => 548 | 8 => 104 | _ => 208

def hc_adjB (u v : Fin 10) : Bool := (adjBits u).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 10, hc_adjB u v = true ↔ Adj u v := by
  decide +kernel

theorem sem_adjB_false {u v : Fin 10} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff]; cases hc_adjB u v <;> decide

theorem adj_symm {u v : Fin 10} (h : Adj u v) : Adj v u := h.symm

theorem adj_irrefl (u : Fin 10) : ¬ Adj u u := by
  revert u; decide +kernel

theorem g10Edge_iff_adj (x : Fin 10 → Bool) :
    G10Edge x ↔ ∃ u v : Fin 10, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩; exact ⟨u, v, Or.inl huv, hx, hy⟩
  · rintro ⟨u, v, huv | hvu, hx, hy⟩
    · exact ⟨u, v, huv, hx, hy⟩
    · exact ⟨v, u, hvu, hy, hx⟩

def g10_nbB (v : Fin 10) : Finset (Fin 10) :=
  Finset.univ.filter (fun u => hc_adjB v u = true)

theorem nbr_diff_exists : ∀ u v : Fin 10, u ≠ v → ∃ z : Fin 10, Adj u z ∧ ¬ Adj v z := by
  have h : ∀ u v : Fin 10, u ≠ v → ∃ z : Fin 10, hc_adjB u z = true ∧ hc_adjB v z = false := by
    decide +kernel
  intro u v huv
  obtain ⟨z, h1, h2⟩ := h u v huv
  exact ⟨z, (hc_adjB_iff u z).1 h1, sem_adjB_false.1 h2⟩

def hc_mate (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 2 | 8 => 3 | _ => 4

theorem hc_mate_adj : ∀ v : Fin 10, hc_adjB v (hc_mate v) = true := by
  decide +kernel

def IsAut (σ : Equiv.Perm (Fin 10)) : Prop :=
  ∀ u v : Fin 10, Adj (σ u) (σ v) ↔ Adj u v

theorem g10Edge_aut (σ : Equiv.Perm (Fin 10)) (hσ : IsAut σ) (x : Fin 10 → Bool) :
    G10Edge (x ∘ σ) ↔ G10Edge x := by
  rw [g10Edge_iff_adj, g10Edge_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩
    exact ⟨σ u, σ v, (hσ u v).mpr huv, hx, hy⟩
  · rintro ⟨u, v, huv, hx, hy⟩
    refine ⟨σ.symm u, σ.symm v, (hσ (σ.symm u) (σ.symm v)).mp ?_, ?_, ?_⟩
    · simpa using huv
    · simpa [Function.comp] using hx
    · simpa [Function.comp] using hy

def IsCover (S : Finset (Fin 10)) : Prop :=
  ∀ u v : Fin 10, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 10)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

def autFwd (k : Fin 30) (v : Fin 10) : Fin 10 :=
  match k.val with
  | 0 => match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | _ => 9
  | 1 => match v.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 9 | 8 => 8 | _ => 7
  | 2 => match v.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 5 | _ => 6
  | 3 => match v.val with | 0 => 3 | 1 => 2 | 2 => 7 | 3 => 9 | 4 => 4 | 5 => 8 | 6 => 1 | 7 => 5 | 8 => 6 | _ => 0
  | 4 => match v.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 9 | 7 => 5 | 8 => 6 | _ => 7
  | 5 => match v.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 9 | 4 => 7 | 5 => 1 | 6 => 8 | 7 => 0 | 8 => 6 | _ => 5
  | 6 => match v.val with | 0 => 3 | 1 => 4 | 2 => 9 | 3 => 6 | 4 => 8 | 5 => 2 | 6 => 0 | 7 => 7 | 8 => 1 | _ => 5
  | 7 => match v.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 7 | 4 => 9 | 5 => 0 | 6 => 8 | 7 => 1 | 8 => 5 | _ => 6
  | 8 => match v.val with | 0 => 4 | 1 => 3 | 2 => 8 | 3 => 5 | 4 => 0 | 5 => 9 | 6 => 2 | 7 => 6 | 8 => 7 | _ => 1
  | 9 => match v.val with | 0 => 2 | 1 => 7 | 2 => 9 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 5 | 7 => 6 | 8 => 0 | _ => 8
  | 10 => match v.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 6 | 8 => 5 | _ => 9
  | 11 => match v.val with | 0 => 0 | 1 => 5 | 2 => 8 | 3 => 6 | 4 => 1 | 5 => 4 | 6 => 7 | 7 => 3 | 8 => 9 | _ => 2
  | 12 => match v.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 6 | 4 => 8 | 5 => 4 | 6 => 7 | 7 => 0 | 8 => 9 | _ => 5
  | 13 => match v.val with | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 7 | 4 => 9 | 5 => 3 | 6 => 1 | 7 => 8 | 8 => 2 | _ => 6
  | 14 => match v.val with | 0 => 4 | 1 => 9 | 2 => 6 | 3 => 1 | 4 => 0 | 5 => 3 | 6 => 7 | 7 => 8 | 8 => 2 | _ => 5
  | 15 => match v.val with | 0 => 4 | 1 => 9 | 2 => 6 | 3 => 8 | 4 => 3 | 5 => 0 | 6 => 7 | 7 => 1 | 8 => 5 | _ => 2
  | 16 => match v.val with | 0 => 6 | 1 => 8 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 9 | 6 => 5 | 7 => 4 | 8 => 7 | _ => 0
  | 17 => match v.val with | 0 => 8 | 1 => 6 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 3 | 6 => 9 | 7 => 2 | 8 => 4 | _ => 7
  | 18 => match v.val with | 0 => 9 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 3 | 7 => 5 | 8 => 2 | _ => 8
  | 19 => match v.val with | 0 => 9 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 7 | 5 => 6 | 6 => 0 | 7 => 8 | 8 => 1 | _ => 5
  | 20 => match v.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 8 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 9 | 8 => 3 | _ => 7
  | 21 => match v.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 9 | 4 => 6 | 5 => 2 | 6 => 5 | 7 => 3 | 8 => 7 | _ => 8
  | 22 => match v.val with | 0 => 1 | 1 => 6 | 2 => 8 | 3 => 3 | 4 => 2 | 5 => 0 | 6 => 9 | 7 => 5 | 8 => 4 | _ => 7
  | 23 => match v.val with | 0 => 3 | 1 => 8 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 2 | 6 => 6 | 7 => 7 | 8 => 1 | _ => 9
  | 24 => match v.val with | 0 => 3 | 1 => 8 | 2 => 5 | 3 => 7 | 4 => 2 | 5 => 4 | 6 => 6 | 7 => 0 | 8 => 9 | _ => 1
  | 25 => match v.val with | 0 => 6 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 9 | 5 => 8 | 6 => 2 | 7 => 5 | 8 => 3 | _ => 7
  | 26 => match v.val with | 0 => 6 | 1 => 8 | 2 => 3 | 3 => 4 | 4 => 9 | 5 => 1 | 6 => 5 | 7 => 2 | 8 => 0 | _ => 7
  | 27 => match v.val with | 0 => 8 | 1 => 3 | 2 => 2 | 3 => 7 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 1 | 8 => 9 | _ => 0
  | 28 => match v.val with | 0 => 8 | 1 => 3 | 2 => 4 | 3 => 9 | 4 => 6 | 5 => 5 | 6 => 2 | 7 => 0 | 8 => 7 | _ => 1
  | _ => match v.val with | 0 => 8 | 1 => 6 | 2 => 9 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 1 | 7 => 7 | 8 => 0 | _ => 2

def autInv (k : Fin 30) (v : Fin 10) : Fin 10 :=
  match k.val with
  | 0 => match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | _ => 9
  | 1 => match v.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 9 | 8 => 8 | _ => 7
  | 2 => match v.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 9 | 7 => 5 | 8 => 6 | _ => 7
  | 3 => match v.val with | 0 => 9 | 1 => 6 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 2 | 8 => 5 | _ => 3
  | 4 => match v.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 5 | _ => 6
  | 5 => match v.val with | 0 => 7 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 9 | 6 => 8 | 7 => 4 | 8 => 6 | _ => 3
  | 6 => match v.val with | 0 => 6 | 1 => 8 | 2 => 5 | 3 => 0 | 4 => 1 | 5 => 9 | 6 => 3 | 7 => 7 | 8 => 4 | _ => 2
  | 7 => match v.val with | 0 => 5 | 1 => 7 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 9 | 7 => 3 | 8 => 6 | _ => 4
  | 8 => match v.val with | 0 => 4 | 1 => 9 | 2 => 6 | 3 => 1 | 4 => 0 | 5 => 3 | 6 => 7 | 7 => 8 | 8 => 2 | _ => 5
  | 9 => match v.val with | 0 => 8 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 1 | 8 => 9 | _ => 2
  | 10 => match v.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 6 | 8 => 5 | _ => 9
  | 11 => match v.val with | 0 => 0 | 1 => 4 | 2 => 9 | 3 => 7 | 4 => 5 | 5 => 1 | 6 => 3 | 7 => 6 | 8 => 2 | _ => 8
  | 12 => match v.val with | 0 => 7 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 9 | 6 => 3 | 7 => 6 | 8 => 4 | _ => 8
  | 13 => match v.val with | 0 => 1 | 1 => 6 | 2 => 8 | 3 => 5 | 4 => 0 | 5 => 2 | 6 => 9 | 7 => 3 | 8 => 7 | _ => 4
  | 14 => match v.val with | 0 => 4 | 1 => 3 | 2 => 8 | 3 => 5 | 4 => 0 | 5 => 9 | 6 => 2 | 7 => 6 | 8 => 7 | _ => 1
  | 15 => match v.val with | 0 => 5 | 1 => 7 | 2 => 9 | 3 => 4 | 4 => 0 | 5 => 8 | 6 => 2 | 7 => 6 | 8 => 3 | _ => 1
  | 16 => match v.val with | 0 => 9 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 7 | 5 => 6 | 6 => 0 | 7 => 8 | 8 => 1 | _ => 5
  | 17 => match v.val with | 0 => 3 | 1 => 2 | 2 => 7 | 3 => 5 | 4 => 8 | 5 => 4 | 6 => 1 | 7 => 9 | 8 => 0 | _ => 6
  | 18 => match v.val with | 0 => 2 | 1 => 3 | 2 => 8 | 3 => 6 | 4 => 1 | 5 => 7 | 6 => 4 | 7 => 5 | 8 => 9 | _ => 0
  | 19 => match v.val with | 0 => 6 | 1 => 8 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 9 | 6 => 5 | 7 => 4 | 8 => 7 | _ => 0
  | 20 => match v.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 8 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 9 | 8 => 3 | _ => 7
  | 21 => match v.val with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 7 | 4 => 2 | 5 => 6 | 6 => 4 | 7 => 8 | 8 => 9 | _ => 3
  | 22 => match v.val with | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 8 | 5 => 7 | 6 => 1 | 7 => 9 | 8 => 2 | _ => 6
  | 23 => match v.val with | 0 => 3 | 1 => 8 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 2 | 6 => 6 | 7 => 7 | 8 => 1 | _ => 9
  | 24 => match v.val with | 0 => 7 | 1 => 9 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 2 | 6 => 6 | 7 => 3 | 8 => 1 | _ => 8
  | 25 => match v.val with | 0 => 2 | 1 => 1 | 2 => 6 | 3 => 8 | 4 => 3 | 5 => 7 | 6 => 0 | 7 => 9 | 8 => 5 | _ => 4
  | 26 => match v.val with | 0 => 8 | 1 => 5 | 2 => 7 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 0 | 7 => 9 | 8 => 1 | _ => 4
  | 27 => match v.val with | 0 => 9 | 1 => 7 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 3 | 8 => 0 | _ => 8
  | 28 => match v.val with | 0 => 7 | 1 => 9 | 2 => 6 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 4 | 7 => 8 | 8 => 0 | _ => 3
  | _ => match v.val with | 0 => 8 | 1 => 6 | 2 => 9 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 1 | 7 => 7 | 8 => 0 | _ => 2

theorem autLeftInv : ∀ (k : Fin 30) (v : Fin 10), autInv k (autFwd k v) = v := by
  decide +kernel

theorem autRightInv : ∀ (k : Fin 30) (v : Fin 10), autFwd k (autInv k v) = v := by
  decide +kernel

def autOf (k : Fin 30) : Equiv.Perm (Fin 10) where
  toFun := autFwd k
  invFun := autInv k
  left_inv := autLeftInv k
  right_inv := autRightInv k

theorem autOf_isAut : ∀ k : Fin 30, IsAut (autOf k) := by
  intro k u v
  rw [← hc_adjB_iff, ← hc_adjB_iff]
  revert k u v; decide +kernel

def hc_rep (idx : Fin 5) : Finset (Fin 10) :=
  match idx.val with
  | 0 => {0}
  | 1 => {0, 2}
  | 2 => {0, 2, 6}
  | 3 => {0, 2, 8}
  | _ => {0, 2, 8, 9}

def canonI : Finset (Finset (Fin 10)) := Finset.univ.image hc_rep

def repMask (idx : Fin 5) : ℕ :=
  match idx.val with
  | 0 => 1
  | 1 => 5
  | 2 => 69
  | 3 => 261
  | _ => 773

def setMask (S : Finset (Fin 10)) : ℕ :=
  (if (0 : Fin 10) ∈ S then 2 ^ 0 else 0) |||
  (if (1 : Fin 10) ∈ S then 2 ^ 1 else 0) |||
  (if (2 : Fin 10) ∈ S then 2 ^ 2 else 0) |||
  (if (3 : Fin 10) ∈ S then 2 ^ 3 else 0) |||
  (if (4 : Fin 10) ∈ S then 2 ^ 4 else 0) |||
  (if (5 : Fin 10) ∈ S then 2 ^ 5 else 0) |||
  (if (6 : Fin 10) ∈ S then 2 ^ 6 else 0) |||
  (if (7 : Fin 10) ∈ S then 2 ^ 7 else 0) |||
  (if (8 : Fin 10) ∈ S then 2 ^ 8 else 0) |||
  (if (9 : Fin 10) ∈ S then 2 ^ 9 else 0)

theorem ite_two_pow_testBit (p : Prop) [Decidable p] (k b : ℕ) :
    (if p then 2 ^ k else 0).testBit b = (decide (k = b) && decide p) := by
  split_ifs with hp <;> simp [Nat.testBit_two_pow, hp]

theorem setMask_testBit (S : Finset (Fin 10)) (i : Fin 10) :
    (setMask S).testBit i.val = decide (i ∈ S) := by
  fin_cases i <;>
    (simp only [setMask, Nat.testBit_or, ite_two_pow_testBit]; simp)

theorem ite_two_pow_lt (p : Prop) [Decidable p] (k : ℕ) (hk : k < 10) :
    (if p then 2 ^ k else 0) < 2 ^ 10 := by
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) hk
  · omega

theorem setMask_lt (S : Finset (Fin 10)) : setMask S < 1024 := by
  change setMask S < 2 ^ 10
  unfold setMask
  repeat (apply Nat.or_lt_two_pow)
  all_goals exact ite_two_pow_lt _ _ (by omega)

theorem setMask_inj {S T : Finset (Fin 10)} (h : setMask S = setMask T) : S = T := by
  ext i
  have h1 := congrArg (fun m => m.testBit i.val) h
  rw [setMask_testBit, setMask_testBit] at h1
  simpa using h1

theorem repMask_eq : ∀ idx : Fin 5, setMask (hc_rep idx) = repMask idx := by
  decide +kernel

def isIndepMask (m : ℕ) : Bool :=
  edgeList.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def popMask (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0)

def autMask (k : Fin 30) (m : ℕ) : ℕ :=
  (if m.testBit 0 then 2 ^ (autOf k 0).val else 0) |||
  (if m.testBit 1 then 2 ^ (autOf k 1).val else 0) |||
  (if m.testBit 2 then 2 ^ (autOf k 2).val else 0) |||
  (if m.testBit 3 then 2 ^ (autOf k 3).val else 0) |||
  (if m.testBit 4 then 2 ^ (autOf k 4).val else 0) |||
  (if m.testBit 5 then 2 ^ (autOf k 5).val else 0) |||
  (if m.testBit 6 then 2 ^ (autOf k 6).val else 0) |||
  (if m.testBit 7 then 2 ^ (autOf k 7).val else 0) |||
  (if m.testBit 8 then 2 ^ (autOf k 8).val else 0) |||
  (if m.testBit 9 then 2 ^ (autOf k 9).val else 0)

def findCanonIdx (m : ℕ) : Option (Fin 5) :=
  (List.finRange 5).find? (fun idx => repMask idx == m)

theorem isIndepMask_of_isIndep {I : Finset (Fin 10)} (hI : IsIndep I) :
    isIndepMask (setMask I) = true := by
  have hedge : ∀ u v : Fin 10, Adj u v →
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
  exact ⟨hedge 0 1 (by decide), hedge 1 2 (by decide), hedge 2 3 (by decide), hedge 3 4 (by decide),
    hedge 4 0 (by decide), hedge 0 5 (by decide), hedge 1 6 (by decide), hedge 2 7 (by decide),
    hedge 3 8 (by decide), hedge 4 9 (by decide), hedge 5 7 (by decide), hedge 7 9 (by decide),
    hedge 9 6 (by decide), hedge 6 8 (by decide), hedge 8 5 (by decide)⟩

theorem popMask_eq_card (I : Finset (Fin 10)) : popMask (setMask I) = I.card := by
  have h1 : I.card = ∑ x ∈ (Finset.univ : Finset (Fin 10)), if x ∈ I then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have huniv : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  rw [h1, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  dsimp only [popMask]
  rw [show (setMask I).testBit 0 = decide ((0 : Fin 10) ∈ I) from setMask_testBit I 0,
      show (setMask I).testBit 1 = decide ((1 : Fin 10) ∈ I) from setMask_testBit I 1,
      show (setMask I).testBit 2 = decide ((2 : Fin 10) ∈ I) from setMask_testBit I 2,
      show (setMask I).testBit 3 = decide ((3 : Fin 10) ∈ I) from setMask_testBit I 3,
      show (setMask I).testBit 4 = decide ((4 : Fin 10) ∈ I) from setMask_testBit I 4,
      show (setMask I).testBit 5 = decide ((5 : Fin 10) ∈ I) from setMask_testBit I 5,
      show (setMask I).testBit 6 = decide ((6 : Fin 10) ∈ I) from setMask_testBit I 6,
      show (setMask I).testBit 7 = decide ((7 : Fin 10) ∈ I) from setMask_testBit I 7,
      show (setMask I).testBit 8 = decide ((8 : Fin 10) ∈ I) from setMask_testBit I 8,
      show (setMask I).testBit 9 = decide ((9 : Fin 10) ∈ I) from setMask_testBit I 9]
  simp only [decide_eq_true_eq]
  omega

theorem autMask_testBit (k : Fin 30) (m : ℕ) (i : Fin 10) :
    (autMask k m).testBit i.val = m.testBit ((autOf k)⁻¹ i).val := by
  have hc : ∀ (j : Fin 10), ((autOf k j).val = i.val) ↔ j = (autOf k)⁻¹ i := by
    intro j
    constructor
    · intro h; exact ((Equiv.eq_symm_apply (autOf k)).2 (Fin.ext h))
    · intro h; exact congrArg Fin.val ((Equiv.eq_symm_apply (autOf k)).1 h)
  have hterm : ∀ (j : Fin 10),
      (if m.testBit j.val = true then 2 ^ (autOf k j).val else 0).testBit i.val =
      (decide (j = (autOf k)⁻¹ i) && m.testBit j.val) := by
    intro j; rw [ite_two_pow_testBit, decide_eq_decide.2 (hc j)]; cases m.testBit j.val <;> rfl
  have hexp : (autMask k m).testBit i.val =
      ((decide ((0 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 0) ||
      (decide ((1 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 1) ||
      (decide ((2 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 2) ||
      (decide ((3 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 3) ||
      (decide ((4 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 4) ||
      (decide ((5 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 5) ||
      (decide ((6 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 6) ||
      (decide ((7 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 7) ||
      (decide ((8 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 8) ||
      (decide ((9 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 9)) := by
    change ((if m.testBit (0 : Fin 10).val = true then 2 ^ (autOf k 0).val else 0) |||
      (if m.testBit (1 : Fin 10).val = true then 2 ^ (autOf k 1).val else 0) |||
      (if m.testBit (2 : Fin 10).val = true then 2 ^ (autOf k 2).val else 0) |||
      (if m.testBit (3 : Fin 10).val = true then 2 ^ (autOf k 3).val else 0) |||
      (if m.testBit (4 : Fin 10).val = true then 2 ^ (autOf k 4).val else 0) |||
      (if m.testBit (5 : Fin 10).val = true then 2 ^ (autOf k 5).val else 0) |||
      (if m.testBit (6 : Fin 10).val = true then 2 ^ (autOf k 6).val else 0) |||
      (if m.testBit (7 : Fin 10).val = true then 2 ^ (autOf k 7).val else 0) |||
      (if m.testBit (8 : Fin 10).val = true then 2 ^ (autOf k 8).val else 0) |||
      (if m.testBit (9 : Fin 10).val = true then 2 ^ (autOf k 9).val else 0)).testBit i.val = _
    simp only [Nat.testBit_or, hterm]
    rfl
  rw [hexp]
  generalize (autOf k)⁻¹ i = t
  fin_cases t <;> simp

theorem setMask_image_aut (k : Fin 30) (S : Finset (Fin 10)) :
    setMask (S.image (autOf k)) = autMask k (setMask S) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 10
  · have hL : (setMask (S.image (autOf k))).testBit b =
        decide ((⟨b, hb⟩ : Fin 10) ∈ S.image (autOf k)) :=
      setMask_testBit (S.image (autOf k)) ⟨b, hb⟩
    rw [hL]
    have him : (⟨b, hb⟩ : Fin 10) ∈ S.image (autOf k) ↔ (autOf k)⁻¹ ⟨b, hb⟩ ∈ S := by
      constructor
      · intro hmem
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.1 hmem
        have : x = (autOf k)⁻¹ ⟨b, hb⟩ := by rw [← hxi]; simp
        exact this ▸ hx
      · intro hx; exact Finset.mem_image.2 ⟨(autOf k)⁻¹ ⟨b, hb⟩, hx, by simp⟩
    have hR : (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 10).val =
        decide ((autOf k)⁻¹ ⟨b, hb⟩ ∈ S) := by
      rw [autMask_testBit, setMask_testBit]
    change _ = (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 10).val
    rw [hR, decide_eq_decide]
    exact him
  · have hL : (setMask (S.image (autOf k))).testBit b = false :=
      Nat.testBit_lt_two_pow ((setMask_lt _).trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 10 ≤ b)))
    have hltR : autMask k (setMask S) < 2 ^ 10 := by
      unfold autMask
      repeat (apply Nat.or_lt_two_pow)
      all_goals exact ite_two_pow_lt _ _ (Fin.isLt _)
    have hR : (autMask k (setMask S)).testBit b = false :=
      Nat.testBit_lt_two_pow (hltR.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 10 ≤ b)))
    rw [hL, hR]

theorem findCanonIdx_some (m : ℕ) (idx : Fin 5) (h : findCanonIdx m = some idx) :
    repMask idx = m := by
  unfold findCanonIdx at h
  have := List.find?_some h
  simpa using this

theorem g10_indep_le_four : ∀ m : Fin 1024, isIndepMask m.val = true → popMask m.val ≤ 4 := by
  decide +kernel

theorem cover_card_ge_six {S : Finset (Fin 10)} (hcov : IsCover S) : 6 ≤ S.card := by
  have hind : IsIndep (Finset.univ \ S) := by
    intro u hu v hv huv
    have h1 := (Finset.mem_sdiff.mp hu).2
    have h2 := (Finset.mem_sdiff.mp hv).2
    exact (hcov u v huv).elim h1 h2
  have hle : (Finset.univ \ S).card ≤ 4 := by
    rw [← popMask_eq_card]
    exact g10_indep_le_four ⟨setMask (Finset.univ \ S), setMask_lt _⟩ (isIndepMask_of_isIndep hind)
  have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hadd
  omega

theorem g10_canon_all : ∀ m : Fin 1024,
    isIndepMask m.val = true → 1 ≤ popMask m.val →
    ∃ k : Fin 30, (findCanonIdx (autMask k m.val)).isSome = true := by
  decide +kernel

theorem exists_aut_canon {I : Finset (Fin 10)} (h : IsIndep I) (hge : 1 ≤ I.card) :
    ∃ σ : Equiv.Perm (Fin 10), IsAut σ ∧ I.image σ ∈ canonI := by
  have hm_lt := setMask_lt I
  have hind := isIndepMask_of_isIndep h
  have hpop : 1 ≤ popMask (setMask I) := by rw [popMask_eq_card]; exact hge
  obtain ⟨k, hk⟩ := g10_canon_all ⟨setMask I, hm_lt⟩ hind hpop
  obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.1 hk
  refine ⟨autOf k, autOf_isAut k, Finset.mem_image.2 ⟨idx, Finset.mem_univ _, ?_⟩⟩
  apply setMask_inj
  rw [repMask_eq, setMask_image_aut]
  exact findCanonIdx_some _ _ hidx

theorem hc_rep_of_mem {I : Finset (Fin 10)} (h : I ∈ canonI) : ∃ idx : Fin 5, hc_rep idx = I := by
  obtain ⟨idx, -, hidx⟩ := Finset.mem_image.1 h
  exact ⟨idx, hidx⟩

theorem g10_not_empty : ¬ G10Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h

theorem g10_not_single (v : Fin 10) : ¬ G10Edge (fun i => decide (i = v)) := by
  rw [g10Edge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab
  exact adj_irrefl v hab

theorem g10_pair {u v : Fin 10} (h : Adj u v) :
    G10Edge (fun i => decide (i = u) || decide (i = v)) := by
  rw [g10Edge_iff_adj]; exact ⟨u, v, h, by simp, by simp⟩

theorem g10_essential (i : Fin 10) : ∃ x y : Fin 10 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ G10Edge x ∧ ¬ G10Edge y :=
  ⟨fun j => decide (j = i) || decide (j = hc_mate i), fun j => decide (j = hc_mate i),
   fun j hj => by simp [hj], g10_pair ((hc_adjB_iff i (hc_mate i)).1 (hc_mate_adj i)),
   g10_not_single (hc_mate i)⟩

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 10 → Bool, val D x (outW 10 D) = true ↔ G10Edge x

theorem g10_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ G10Edge x) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h01 : Adj (0 : Fin 10) 1 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 10) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (g10_pair h01)⟩
      · exact ⟨fun _ => false, fun h => g10_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g10_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := g10_essential i
      refine ⟨x, y, hxy, fun h => hy ((hC y).1 ?_)⟩
      rw [← h]; exact (hC x).2 hx)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem g10_relabel (σ : Equiv.Perm (Fin 10)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) :
    StrictLive 10 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 10 (relabel σ D) = totalSurplus 10 D ∧
      Bplus 10 (relabel σ D) = Bplus 10 D ∧ Bzero 10 (relabel σ D) = Bzero 10 D ∧
      eligSet 10 (relabel σ D) = (eligSet 10 D).image σ ∧
      ineligSet 10 (relabel σ D) = (ineligSet 10 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact g10Edge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  simpa [ineligSet] using h

theorem g10_cover_iff_indep (D : Dag) :
    IsCover (eligSet 10 D) ↔ IsIndep (ineligSet 10 D) := by
  constructor
  · intro hcov u hu v hv huv
    have h1 := Finset.mem_sdiff.mp hu
    have h2 := Finset.mem_sdiff.mp hv
    exact (hcov u v huv).elim h1.2 h2.2
  · intro hind u v huv
    by_contra hc; push Not at hc
    exact hind u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.1⟩)
      v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.2⟩) huv

theorem g10_wlog {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hind : IsIndep (ineligSet 10 D)) (hge : 1 ≤ (ineligSet 10 D).card) :
    ∃ D' : Dag, StrictLive 10 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 10 D' = totalSurplus 10 D ∧
      Bplus 10 D' = Bplus 10 D ∧ Bzero 10 D' = Bzero 10 D ∧
      (ineligSet 10 D').card = (ineligSet 10 D).card ∧
      ineligSet 10 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := exists_aut_canon hind hge
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := g10_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, h8 ▸ hmem⟩
  rw [h8, Finset.card_image_of_injective _ σ.injective]

theorem g10_budget {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 18) :
    totalSurplus 10 D = D.length - 9 ∧ totalSurplus 10 D ≤ 9 := by
  have := surplus_identity h
  exact ⟨by omega, by omega⟩

theorem g10_p_bounds {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 18)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (hcov : IsCover (eligSet 10 D)) :
    6 ≤ (eligSet 10 D).card ∧ (eligSet 10 D).card ≤ Bplus 10 D ∧
      Bplus 10 D ≤ 9 ∧ totalSurplus 10 D ≤ 9 := by
  have h1 := cover_card_ge_six hcov
  have h2 := elig_le_Bplus h.1 b hb
  have h3 := Bplus_le_total 10 D
  have h4 := (g10_budget h hlen).2
  exact ⟨h1, h2, by omega, h4⟩

theorem g10_inelig_bounds {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 18)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (hcov : IsCover (eligSet 10 D)) :
    (ineligSet 10 D).Nonempty ∧ 1 ≤ (ineligSet 10 D).card ∧ (ineligSet 10 D).card ≤ 4 := by
  obtain ⟨h6, hp, hB, h9⟩ := g10_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 10 D
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

end SemCore

theorem sem_g10_second : ∀ u v : Fin 10, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_g10_gr : sem_Gr (fun u v : Fin 10 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, nbr_diff_exists, fun u v => by
    obtain ⟨a, h1, h2⟩ := sem_g10_second u v
    exact ⟨a, (hc_adjB_iff u a).mp h1, h2⟩⟩

theorem sem_g10_comp {D : Dag} (hD : Correct D) : sem_Comp 10 (fun u v : Fin 10 => Adj u v) D :=
  fun x => (hD x).trans (g10Edge_iff_adj x)

theorem exists_pureBranch {D : Dag} (h : StrictLive 10 D) (hD : Correct D) :
    ∃ b : Fin 10 → ℕ, PureBranch 10 D b :=
  sem_exists_pureBranch sem_g10_gr h.1 (sem_g10_comp hD)

theorem elig_isCover {D : Dag} (h : StrictLive 10 D) (hD : Correct D) :
    IsCover (eligSet 10 D) :=
  fun _ _ huv => sem_elig_cover sem_g10_gr h (sem_g10_comp hD) huv

theorem g10_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ G10Edge x)
    (hsize : C.size ≤ 18) :
    ∃ D : Dag, StrictLive 10 D ∧ Correct D ∧ D.length ≤ 18 ∧
      totalSurplus 10 D ≤ 9 ∧ 1 ≤ (ineligSet 10 D).card ∧ ineligSet 10 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := g10_normalize C hmono hC
  have hlen : D0.length ≤ 18 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h0 hD0
  have hcov := elig_isCover h0 hD0
  obtain ⟨-, hge1, -⟩ := g10_inelig_bounds h0 hlen b hb hcov
  obtain ⟨D, h1, h2, h3, -, -, -, -, h8⟩ :=
    g10_wlog h0 hD0 ((g10_cover_iff_indep D0).mp hcov) hge1
  have hlen' : D.length ≤ 18 := by omega
  obtain ⟨b', hb'⟩ := exists_pureBranch h1 h2
  obtain ⟨-, hge2', -⟩ := g10_inelig_bounds h1 hlen' b' hb' (elig_isCover h1 h2)
  exact ⟨D, h1, h2, hlen', (g10_budget h1 hlen').2, hge2', h8⟩

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

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

end SemArms

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

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

abbrev G10 : Fin 10 → Fin 10 → Prop := fun u v => Adj u v

def ru (D : Dag) (b : Fin 10 → ℕ) (x : Fin 10) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)

theorem mem_ru {D : Dag} {b : Fin 10 → ℕ} {x : Fin 10} {u : Σ _ : ℕ, ℕ} :
    u ∈ ru D b x ↔ u ∈ residualUnits 10 D b ∧ x ∈ supp 10 D u.1 := by
  simp [ru]

theorem cc_le {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) (x : Fin 10) :
    (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_g10_gr h (sem_g10_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 10)) ∩ eligSet 10 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  unfold ru
  omega

theorem as_mem {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i a : Fin 10} (hi : i ∈ ineligSet 10 D) (hia : Adj i a) : pos i ∈ sem_W 10 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

theorem as_priv {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i x : Fin 10} (hi : i ∈ ineligSet 10 D) (h : sem_bar (pos i) ∈ sem_W 10 D x) : x = i := by
  have h1 := (sem_mem_W.1 h).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at h1
  exact Finset.mem_singleton.1 h1

theorem pos_bar_mem {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D) : i ∈ supp 10 D (src D (sem_bar (pos i))) := by
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2]
  exact Finset.mem_singleton_self i

theorem as_W {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i : Fin 10} (hi : i ∈ ineligSet 10 D) :
    sem_W 10 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, -, -, -, h6, -⟩ :=
    sem_inelig_consumer sem_g10_gr h (sem_g10_comp hD) hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 10 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 10 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem full_g10 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos) {i v : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ (pos i).1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_g10_gr h (sem_g10_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
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
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair hde] at this

theorem pa_two {α : Type} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hs : s.card ≤ 2) : ∀ e ∈ s, e = a ∨ e = b := by
  intro e he
  by_contra hne
  rw [not_or] at hne
  have := pa_card3 he ha hb hne.1 hne.2 hab
  omega

theorem pa_three {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : s.card ≤ 3) :
    ∀ e ∈ s, e = a ∨ e = b ∨ e = c := by
  intro e he
  by_contra hne
  rw [not_or, not_or] at hne
  have := pa_card4 he ha hb hc hne.1 hne.2.1 hne.2.2 hab hac hbc
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

theorem pa_ed {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {x y : Fin 10} (hxy : Adj x y) :
    ∃ e ∈ sem_W 10 D x, sem_bar e ∈ sem_W 10 D y ∧
      (∀ i ∈ ineligSet 10 D, e = pos i → y = i) ∧
      ∀ i ∈ ineligSet 10 D, sem_bar e = pos i → x = i := by
  obtain ⟨e, he, hb, -⟩ := sem_edge_slots sem_g10_gr h.1 (sem_g10_comp hD) hxy
  exact ⟨e, he, hb, fun i hi hei => as_priv hpos hi (hei ▸ hb),
    fun i hi hei => as_priv hpos hi (by rw [← hei, sem_bar_bar]; exact he)⟩

theorem g10_deg3_third : ∀ x a b : Fin 10, (g10_nbB x).card = 3 →
    x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem g10_deg3_cover_free {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {x a b : Fin 10}
    (hd : (g10_nbB x).card = 3) (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 10 D x ∧ a ∉ supp 10 D (src D e) ∧ b ∉ supp 10 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := g10_deg3_third x a b hd hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_g10_gr h.1 (sem_g10_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

theorem ps_nonadj {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i x r : Fin 10} (hi : i ∈ ineligSet 10 D)
    (hix : Adj i x) (hir : Adj i r) (hrx : r ≠ x) (hdx : (g10_nbB x).card = 3)
    (hc : (sem_W 10 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 10 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → ¬ Adj r t → Z ∉ sem_W 10 D t := by
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain sem_g10_gr h.1 (sem_g10_comp hD) (x := x) (a := r) (Ne.symm hrx)
  have hY : pos i ∈ sem_W 10 D x := as_mem hpos hi hix
  have hZY : Z ≠ pos i := fun heq => hZr (heq ▸ (hpos.1 i hi).2.2.1 r hir)
  have hW : sem_W 10 D x = {pos i, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  refine ⟨Z, hZY, hW, fun t htx hrt hZt => ?_⟩
  obtain ⟨f, hf, h1, h2⟩ := g10_deg3_cover_free h hD hdx (Ne.symm hrx) (Ne.symm htx) hrt
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · exact h1 ((hpos.1 i hi).2.2.1 r hir)
  · exact h2 (sem_mem_W.1 hZt).2.1

theorem two_in_deg3 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i1 i2 u v : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) : 3 ≤ (sem_W 10 D u).card := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  by_cases hv : v ∈ ineligSet 10 D
  · exact pa_card3 p1 p2 (as_mem hpos hv (adj_symm h3)) p12
      (fun e => hv1.symm (hpos.2 i1 hi1 v hv e)) (fun e => hv2.symm (hpos.2 i2 hi2 v hv e))
  · obtain ⟨e, he, -, hf, -⟩ := pa_ed h hD hpos h3
    exact pa_card3 p1 p2 he p12 (fun hh => hv (hf i1 hi1 hh.symm ▸ hi1))
      (fun hh => hv (hf i2 hi2 hh.symm ▸ hi2))

theorem pa_m1_gen {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) (z k v iz ik r : Fin 10)
    (hiz : iz ∈ ineligSet 10 D) (hik : ik ∈ ineligSet 10 D)
    (hz : z ∉ ineligSet 10 D) (hk : k ∉ ineligSet 10 D) (hv : v ∉ ineligSet 10 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k ∧ (g10_nbB k).card = 3 ∧
      hc_adjB ik r = true ∧ r ≠ k ∧ hc_adjB r v = false)
    (hcz : (sem_W 10 D z).card ≤ 2) (hck : (sem_W 10 D k).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g7
  obtain ⟨Dk, -, hWk, hpk⟩ := ps_nonadj h hD hpos hik g2 g7 g8 g6 hck
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos g3
  obtain ⟨e', he', hbe', hg', -⟩ := pa_ed h hD hpos g4
  rw [hWk, Finset.mem_insert, Finset.mem_singleton] at hbe
  have hb : sem_bar e = Dk := hbe.resolve_left (fun hh => hz (hf' ik hik hh ▸ hik))
  rcases pa_two (as_mem hpos hiz g1) he (fun hh => hk (hf iz hiz hh.symm ▸ hiz)) hcz e' he'
    with h1 | h1
  · exact hv (hg' iz hiz h1 ▸ hiz)
  · exact hpk v g5 (sem_adjB_false.1 g9) (by rw [← hb, ← h1]; exact hbe')

theorem ru_one_two_supp {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {x : Fin 10} {u0 : Σ _ : ℕ, ℕ}
    (hM : merges 10 D (carrierT 10 D {x}) = ∅) (hru : ru D b x = {u0}) :
    ∃ e1 e2 : ℕ × Bool, e1 ∈ sem_W 10 D x ∧ e2 ∈ sem_W 10 D x ∧ e1 ≠ e2 ∧
      supp 10 D u0.1 ⊆ supp 10 D (src D e1) ∧ supp 10 D u0.1 ⊆ supp 10 D (src D e2) := by
  have hS := h.1
  have hu0m : u0 ∈ ru D b x := by rw [hru]; exact Finset.mem_singleton_self u0
  obtain ⟨hu0r, hxu0⟩ := mem_ru.1 hu0m
  have hu0u : u0 ∈ units 10 D := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0r).1).1
  have hfr : 2 ≤ fanout D u0.1 := by have := (mem_units.mp hu0u).2; omega
  have hxe : x ∈ eligSet 10 D := mem_eligSet.2 ⟨u0.1, hfr, hxu0⟩
  have hlow : ∀ w, 2 ≤ fanout D w → x ∈ supp 10 D w → w ≤ u0.1 := by
    intro w hrw hxw
    by_contra hlt
    have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
        by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
    by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D b
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
      have hbv : b v = w := congrArg Sigma.fst hveq
      have hsv := (hb v hv).2.1
      rw [hbv] at hsv
      rw [hsv, Finset.mem_singleton] at hxw
      have hmin := (hb x hxe).2.2.2 u0.1 hfr hxu0
      rw [hxw, hbv] at hmin; omega
    · have h1 : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ ru D b x := mem_ru.2 ⟨Finset.mem_sdiff.2 ⟨hwu, hwr⟩, hxw⟩
      rw [hru, Finset.mem_singleton] at h1
      have : w = u0.1 := congrArg Sigma.fst h1
      omega
  have harm_sub : ∀ {a c : ℕ}, Relation.ReflTransGen (sem_Arm 10 D {x}) a c →
      supp 10 D a ⊆ supp 10 D c := by
    intro a c hp
    induction hp with
    | refl => exact Finset.Subset.refl _
    | @tail u v _ huv ih =>
      obtain ⟨hj, hge, hop⟩ := huv.1
      have hv : 10 + (v - 10) = v := by omega
      have hxv : x ∈ supp 10 D (10 + (v - 10)) := by
        rw [hv]; exact (huv.2.2 x (Finset.mem_singleton_self x)).2
      have htag : tag D (v - 10) = false := (sem_zm_gate hS hM (by omega) hxv).1
      exact ih.trans (by
        rw [← hv, sem_supp_or hS (by omega) htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right)
  have hread : ∀ j ∈ readers D u0.1,
      j < D.length ∧ u0.1 < 10 + j ∧ (opA D j = u0.1 ∨ opB D j = u0.1) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D u0.1, ∃ e : ℕ × Bool, e ∈ sem_W 10 D x ∧
      supp 10 D u0.1 ⊆ supp 10 D (src D e) ∧
      ((e.1 = j ∧ src D e = u0.1) ∨ Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hlt, hop⟩ := hread j hj
    by_cases hxj : x ∈ supp 10 D (10 + j)
    · have htag : tag D j = false := (sem_zm_gate hS hM hjl hxj).1
      have hsub1 : supp 10 D u0.1 ⊆ supp 10 D (10 + j) := by
        rw [sem_supp_or hS hjl htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right
      obtain ⟨e, he1, he2⟩ := sem_descent sem_g10_gr h (sem_g10_comp hD) {x}
        ⟨x, Finset.mem_singleton_self x⟩
        (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hM)
        (10 + j) (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hxj)
        (fun y hy w hrw hyw => by
          rw [Finset.mem_singleton.1 hy] at hyw
          by_contra hf; have := hlow w (by omega) hyw; omega)
      exact ⟨e, he1 x (Finset.mem_singleton_self x), hsub1.trans (harm_sub he2), Or.inr he2⟩
    · rcases hop with he | he
      · refine ⟨(j, false), sem_mem_W.2 ⟨hjl, by rw [sb_src_false, he]; exact hxu0, hxj⟩,
          by rw [sb_src_false, he], Or.inl ⟨rfl, by rw [sb_src_false, he]⟩⟩
      · refine ⟨(j, true), sem_mem_W.2 ⟨hjl, by rw [sb_src_true, he]; exact hxu0, hxj⟩,
          by rw [sb_src_true, he], Or.inl ⟨rfl, by rw [sb_src_true, he]⟩⟩
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.1 (by exact hfr : 1 < (readers D u0.1).card)
  have hRstep : ∀ a c, sem_Arm 10 D {x} a c → sem_step 10 D a c := fun _ _ hr => hr.1
  have hfun : ∀ a a' c, sem_Arm 10 D {x} a c → sem_Arm 10 D {x} a' c → a = a' := by
    intro a a' c h1 h2
    by_contra hne2
    obtain ⟨hjl, hge1, hop1⟩ := h1.1
    obtain ⟨-, -, hop2⟩ := h2.1
    have hcv : 10 + (c - 10) = c := by omega
    have ha := (h1.2.2 x (Finset.mem_singleton_self x)).1
    have ha' := (h2.2.2 x (Finset.mem_singleton_self x)).1
    have hc := (h1.2.2 x (Finset.mem_singleton_self x)).2
    have hxc : x ∈ supp 10 D (10 + (c - 10)) := by rw [hcv]; exact hc
    apply (sem_zm_gate hS hM (by omega) hxc).2
    rcases hop1 with e1 | e1 <;> rcases hop2 with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D u0.1, ∀ jb ∈ readers D u0.1, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + ja) (10 + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨-, hlta, -⟩ := hread ja hja
    obtain ⟨hjlb, -, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hu_ne : u ≠ u0.1 := by
        have := sem_rtg_le hS hRstep hu1; omega
      have hux := (hu2.2.2 x (Finset.mem_singleton_self x)).1
      apply (sem_zm_gate hS hM hjlb (hu2.2.2 x (Finset.mem_singleton_self x)).2).2
      have hstep : opA D jb = u ∨ opB D jb = u := by
        have := hu2.1.2.2; simpa using this
      rcases hopb with e1 | e1 <;> rcases hstep with e2 | e2
      · exact absurd (e2.symm.trans e1) hu_ne
      · rw [e1, e2]; exact ⟨hxu0, hux⟩
      · rw [e1, e2]; exact ⟨hux, hxu0⟩
      · exact absurd (e2.symm.trans e1) hu_ne
  obtain ⟨e1, he1W, he1s, he1p⟩ := hterm j1 hj1
  obtain ⟨e2, he2W, he2s, he2p⟩ := hterm j2 hj2
  refine ⟨e1, e2, he1W, he2W, fun heq => ?_, he1s, he2s⟩
  subst heq
  rcases he1p with ⟨hj1e, hs1⟩ | hp1 <;> rcases he2p with ⟨hj2e, hs2⟩ | hp2
  · exact hne (hj1e.symm.trans hj2e)
  · have hle := sem_rtg_le hS hRstep hp2
    have := (hread j2 hj2).2.1
    rw [hs1] at hle; omega
  · have hle := sem_rtg_le hS hRstep hp1
    have := (hread j1 hj1).2.1
    rw [hs2] at hle; omega
  · rcases sem_rtg_comparable hfun hp1 hp2 with h12 | h21
    · exact hcross j1 hj1 j2 hj2 hne h12
    · exact hcross j2 hj2 j1 hj1 hne.symm h21

theorem full_of_two_in_deg3 {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hB0 : Bzero 10 D = 0) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i1 i2 u v : Fin 10} (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) (hcu : (sem_W 10 D u).card ≤ 3) :
    (∀ t, t ∈ supp 10 D (src D (pos i1)) → Adj i1 t) ∧
    (∀ t, t ∈ supp 10 D (src D (pos i2)) → Adj i2 t) := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have hfull : ∀ (ia ib : Fin 10), ia ∈ ineligSet 10 D → ib ∈ ineligSet 10 D → ia ≠ ib →
      Adj ia u → Adj ib u → v ≠ ia → v ≠ ib →
      ∀ t, t ∈ supp 10 D (src D (pos ia)) → Adj ia t := by
    intro ia ib hia hib hab hiau hibu hvia hvib t ht
    have pa := as_mem hpos hia hiau
    have pb := as_mem hpos hib hibu
    have pab : pos ia ≠ pos ib := fun e => hab (hpos.2 ia hia ib hib e)
    have hspec : ∀ t, t ∈ supp 10 D (src D (pos ia)) ↔ Adj ia t := by
      refine full_g10 h hD hB0 hpos hia hiau (fun p hp hne1 hsub => ?_)
      by_cases hv : v ∈ ineligSet 10 D
      · have pv := as_mem hpos hv (adj_symm h3)
        have pav : pos ia ≠ pos v := fun e => hvia.symm (hpos.2 ia hia v hv e)
        have pbv : pos ib ≠ pos v := fun e => hvib.symm (hpos.2 ib hib v hv e)
        rcases pa_three pa pb pv pab pav pbv hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hab.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hib)))
        · exact hvia (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hv)))
      · obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos h3
        have pae : pos ia ≠ e := fun hh => hv (hf ia hia hh.symm ▸ hia)
        have pbe : pos ib ≠ e := fun hh => hv (hf ib hib hh.symm ▸ hib)
        rcases pa_three pa pb he pab pae pbe hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hab.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hib)))
        · exact hv (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hia)
    exact (hspec t).1 ht
  exact ⟨hfull i1 i2 hi1 hi2 hne h1 h2 hv1 hv2, hfull i2 i1 hi2 hi1 hne.symm h2 h1 hv2 hv1⟩

theorem w3_ru_one_bound {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {x i1 i2 v : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : (g10_nbB x).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧
      hc_adjB x v = true ∧ v ≠ i1 ∧ v ≠ i2)
    {u0 : Σ _ : ℕ, ℕ} (hru : ru D b x = {u0}) :
    ∀ t : Fin 10, t ∈ supp 10 D u0.1 → t ≠ x →
      (hc_adjB i1 t = true ∧ ∀ q : Fin 10, hc_adjB i2 q = true → q ≠ x → hc_adjB t q = true) ∨
      (hc_adjB i2 t = true ∧ ∀ q : Fin 10, hc_adjB i1 q = true → q ≠ x → hc_adjB t q = true) := by
  obtain ⟨hdx, h12, hx1, hx2, hxv, hv1, hv2⟩ := hg
  have hbp := sem_minBranch_pure hb
  have hx3 := two_in_deg3 h hD hpos hi1 hi2 ⟨h12, hx1, hx2, hxv, hv1, hv2⟩
  have hcc := cc_le h hD b hbp x
  rw [hru, Finset.card_singleton] at hcc
  have hM : merges 10 D (carrierT 10 D {x}) = ∅ := Finset.card_eq_zero.1 (by omega)
  have hW3 : (sem_W 10 D x).card ≤ 3 := by omega
  obtain ⟨e1, e2, he1W, he2W, he12, hs1, hs2⟩ := ru_one_two_supp h hD b hb hM hru
  obtain ⟨hfull1, hfull2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 ⟨h12, hx1, hx2, hxv, hv1, hv2⟩ hW3
  have p1 := as_mem hpos hi1 ((hc_adjB_iff _ _).1 hx1)
  have p2 := as_mem hpos hi2 ((hc_adjB_iff _ _).1 hx2)
  have hp12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 i1 hi1 i2 hi2 e)
  intro t ht htx
  have ht1 : t ∈ supp 10 D (src D e1) := hs1 ht
  have ht2 : t ∈ supp 10 D (src D e2) := hs2 ht
  by_cases h1 : e1 = pos i1 ∨ e2 = pos i1
  · have hti1 : Adj i1 t := by
      rcases h1 with rfl | rfl
      · exact hfull1 t ht1
      · exact hfull1 t ht2
    by_cases h2 : e1 = pos i2 ∨ e2 = pos i2
    · exfalso
      have hti2 : Adj i2 t := by
        rcases h2 with rfl | rfl
        · exact hfull2 t ht1
        · exact hfull2 t ht2
      have hc : (g10_nbB i1 ∩ g10_nbB i2).card ≤ 1 := by
        have : ∀ a b : Fin 10, a ≠ b → (g10_nbB a ∩ g10_nbB b).card ≤ 1 := by decide +kernel
        exact this i1 i2 h12
      have hxt : ({x, t} : Finset (Fin 10)) ⊆ g10_nbB i1 ∩ g10_nbB i2 := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [Finset.mem_inter, g10_nbB, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with rfl | rfl
        · exact ⟨hx1, hx2⟩
        · exact ⟨(hc_adjB_iff _ _).2 hti1, (hc_adjB_iff _ _).2 hti2⟩
      have hcard := Finset.card_le_card hxt
      rw [Finset.card_pair (Ne.symm htx)] at hcard; omega
    · rw [not_or] at h2
      obtain ⟨ev, hevW, hte⟩ : ∃ ev, ev ∈ sem_W 10 D x ∧ ev ≠ pos i1 ∧ ev ≠ pos i2 ∧ t ∈ supp 10 D (src D ev) := by
        rcases h1 with rfl | rfl
        · exact ⟨e2, he2W, he12.symm, h2.2, ht2⟩
        · exact ⟨e1, he1W, he12, h2.1, ht1⟩
      have hW := pa_three p1 p2 hevW hp12 hte.1.symm hte.2.1.symm hW3
      left
      refine ⟨(hc_adjB_iff _ _).2 hti1, fun q hq2 hqx => ?_⟩
      by_contra hntq
      have hntq' : hc_adjB t q = false := Bool.eq_false_iff.2 hntq
      obtain ⟨f, hfW, hfq, hft⟩ := g10_deg3_cover_free h hD hdx (Ne.symm hqx) (Ne.symm htx)
        (fun hqt => sem_adjB_false.1 hntq' (adj_symm hqt))
      rcases hW f hfW with rfl | rfl | rfl
      · exact hft (by rcases h1 with rfl | rfl; exact ht1; exact ht2)
      · exact hfq ((hpos.1 i2 hi2).2.2.1 q ((hc_adjB_iff _ _).1 hq2))
      · exact hft hte.2.2
  · rw [not_or] at h1
    by_cases h2 : e1 = pos i2 ∨ e2 = pos i2
    · have hti2 : Adj i2 t := by
        rcases h2 with rfl | rfl
        · exact hfull2 t ht1
        · exact hfull2 t ht2
      obtain ⟨ev, hevW, hte⟩ : ∃ ev, ev ∈ sem_W 10 D x ∧ ev ≠ pos i1 ∧ ev ≠ pos i2 ∧ t ∈ supp 10 D (src D ev) := by
        rcases h2 with rfl | rfl
        · exact ⟨e2, he2W, h1.2, he12.symm, ht2⟩
        · exact ⟨e1, he1W, h1.1, he12, ht1⟩
      have hW := pa_three p1 p2 hevW hp12 hte.1.symm hte.2.1.symm hW3
      right
      refine ⟨(hc_adjB_iff _ _).2 hti2, fun q hq1 hqx => ?_⟩
      by_contra hntq
      have hntq' : hc_adjB t q = false := Bool.eq_false_iff.2 hntq
      obtain ⟨f, hfW, hfq, hft⟩ := g10_deg3_cover_free h hD hdx (Ne.symm hqx) (Ne.symm htx)
        (fun hqt => sem_adjB_false.1 hntq' (adj_symm hqt))
      rcases hW f hfW with rfl | rfl | rfl
      · exact hfq ((hpos.1 i1 hi1).2.2.1 q ((hc_adjB_iff _ _).1 hq1))
      · exact hft (by rcases h2 with rfl | rfl; exact ht1; exact ht2)
      · exact hft hte.2.2
    · rw [not_or] at h2
      have h4 := pa_card4 p1 p2 he1W he2W hp12 (Ne.symm h1.1) (Ne.symm h1.2) (Ne.symm h2.1) (Ne.symm h2.2) he12
      omega

def w3_bad (x i1 i2 t : Fin 10) : Bool :=
  (t == x) ||
  (hc_adjB i1 t && (List.finRange 10).all (fun q => !(hc_adjB i2 q && !(q == x)) || hc_adjB t q)) ||
  (hc_adjB i2 t && (List.finRange 10).all (fun q => !(hc_adjB i1 q && !(q == x)) || hc_adjB t q))

theorem w3_ru_one_not_mem {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {x i1 i2 v : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : (g10_nbB x).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧
      hc_adjB x v = true ∧ v ≠ i1 ∧ v ≠ i2)
    {u0 : Σ _ : ℕ, ℕ} (hru : ru D b x = {u0})
    {t : Fin 10} (hnb : w3_bad x i1 i2 t = false) : t ∉ supp 10 D u0.1 := by
  intro ht
  have hnb1 : t ≠ x := by
    intro heq; subst heq; simp [w3_bad] at hnb
  have hbd := w3_ru_one_bound h hD hB0 b hb hpos hi1 hi2 hg hru t ht hnb1
  have htrue : w3_bad x i1 i2 t = true := by
    unfold w3_bad
    rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_imp_iff]
      left; right
      refine ⟨h1, fun q => ?_⟩
      by_cases hq2 : hc_adjB i2 q = true
      · by_cases hqx : q = x
        · simp [hqx]
        · simp [hq2, hqx, h2 q hq2 hqx]
      · simp [Bool.eq_false_iff.2 hq2]
    · simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_imp_iff]
      right
      refine ⟨h1, fun q => ?_⟩
      by_cases hq1 : hc_adjB i1 q = true
      · by_cases hqx : q = x
        · simp [hqx]
        · simp [hq1, hqx, h2 q hq1 hqx]
      · simp [Bool.eq_false_iff.2 hq1]
  rw [hnb] at htrue; exact Bool.false_ne_true htrue

theorem pos_chain_or {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos) {i v : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ (pos i).1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    sem_Chain 10 D (10 + (pos i).1) (outW 10 D) ∧
    (∀ j, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) (10 + j) →
      j ≠ (pos i).1 → tag D j = false) ∧
    (∀ x : Fin 10 → Bool, val D x (10 + (pos i).1) = true → G10Edge x) := by
  have hS := h.1
  have hG := sem_g10_gr
  have hC := sem_g10_comp hD
  have heW := as_W h hD hpos hi
  have he1 : (pos i).1 < D.length := (hpos.1 i hi).1
  have hreach_e : Relation.ReflTransGen (sem_step 10 D) i.val (10 + (pos i).1) :=
    (sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi (pos_bar_mem hpos hi))).tail
      (sem_step_src he1 (sem_bar (pos i)).2)
  have hch_out : sem_Chain 10 D (10 + (pos i).1) (outW 10 D) := by
    have hch_all := sem_noempty_chain_out hG h hC hB0 hi
    have hch_e := sem_noempty_unique hG h hC hB0 hi hreach_e
    have hdet : ∀ a c1 c2, (sem_step 10 D a c1 ∧ fanout D a = 1) →
        (sem_step 10 D a c2 ∧ fanout D a = 1) → c1 = c2 :=
      fun _ _ _ h1 h2 => sem_step_unique h1.1 h2.1 h1.2
    have hsplit : ∀ {a}, sem_Chain 10 D a (10 + (pos i).1) → sem_Chain 10 D a (outW 10 D) →
        sem_Chain 10 D (10 + (pos i).1) (outW 10 D) := by
      intro a h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => intro h2; exact h2
      | head hac hc1 ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with heq | ⟨d, had, hdo⟩
        · exfalso
          have hlt := sem_step_lt hS hac.1
          have hle2 := sem_rtg_le hS (fun _ _ s => s.1) hc1
          rw [heq] at hlt; unfold outW at hlt; omega
        · exact ih (hdet _ _ d hac had ▸ hdo)
    exact hsplit hch_e hch_all
  have hor : ∀ j, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) (10 + j) →
      j ≠ (pos i).1 → tag D j = false := by
    intro j hreach hj
    by_contra ht
    rw [Bool.not_eq_false] at ht
    rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
    · exact hj (by omega)
    · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
      have hjj : j' = j := by omega
      subst hjj
      have hreach2 : Relation.ReflTransGen (sem_step 10 D) i.val w := hreach_e.trans hw1
      have hch := sem_noempty_unique hG h hC hB0 hi hreach2
      have hf : fanout D w = 1 := by
        have h1 := sem_step_fanout hw2
        by_contra hne
        have h2 := sem_branch_empty hG hS hC hi hch (by omega)
        have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
        rw [h2] at h4
        exact Finset.not_nonempty_empty h4
      have hsub : supp 10 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
      have hvi : v ≠ i := fun hvi => adj_irrefl i (hvi ▸ hiv)
      have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
      have hmem : v ∈ supp 10 D (src D (j', !s)) :=
        sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
          (by unfold outW; omega) hiv
      have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 10 D v :=
        sem_mem_W.2 ⟨hj', hmem, fun hc => by
          have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
          exact hvi (Finset.mem_singleton.1 this)⟩
      exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)
  refine ⟨hch_out, hor, fun x hx => ?_⟩
  have hval_out : val D x (outW 10 D) = true := by
    have hstep_val : ∀ {w}, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) w →
        val D x w = true := by
      intro w hp
      induction hp with
      | refl => exact hx
      | @tail u v' hp1 hstep ih =>
        have ⟨hlt, hge, hop⟩ := hstep
        have hv_eq : 10 + (v' - 10) = v' := by omega
        have hjlt : v' - 10 < D.length := by omega
        have hne : v' - 10 ≠ (pos i).1 := by
          have h1 := sem_rtg_le hS (fun _ _ s => s) hp1
          have h2 := sem_step_lt hS hstep
          omega
        have htag : tag D (v' - 10) = false := hor (v' - 10) (hv_eq.symm ▸ hp1.tail hstep) hne
        rw [← hv_eq, val_gate hS x (v' - 10) hjlt, htag, gop_false, Bool.or_eq_true]
        rcases hop with ha | hb'
        · left; rw [ha]; exact ih
        · right; rw [hb']; exact ih
    exact hstep_val (sem_rtg_mono (fun _ _ s => s.1) hch_out)
  exact (hD x).1 hval_out

theorem pa_ed_avoid_min {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    {u v a b : Fin 10} (huv : Adj u v) (hnab : ¬ Adj a b)
    (hun : u ≠ a) (hun' : u ≠ b) (hvb : v = b ∨ v = a) :
    ∃ e : ℕ × Bool, e ∈ sem_W 10 D u ∧
      val D (sem_two u v) (10 + e.1) = true ∧
      val D (sem_two a b) (10 + e.1) = false ∧
      val D (sem_two a b) (src D (sem_bar e)) = true := by
  classical
  have hS := h.1
  have hC := sem_g10_comp hD
  have h1 : val D (sem_two u v) (outW 10 D) = true := (hC _).2 (sem_two_edge huv)
  have h0 : val D (sem_two a b) (outW 10 D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨p, q, hpq, hp, hq⟩ := (hC _).1 hc
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact adj_irrefl _ hpq
    · exact hnab hpq
    · exact hnab (adj_symm hpq)
    · exact adj_irrefl _ hpq
  have hu0 : val D (fun i => decide (i = u)) (outW 10 D) = false := by
    by_contra hc; rw [Bool.not_eq_false] at hc
    exact g10_not_single u ((hD _).1 hc)
  have hex : ∃ w, val D (sem_two u v) w = true ∧ val D (sem_two a b) w = false ∧
      val D (fun i => decide (i = u)) w = false := ⟨outW 10 D, h1, h0, hu0⟩
  obtain ⟨hw1, hw0, hwu⟩ := Nat.find_spec hex
  have hmin : ∀ w', w' < Nat.find hex → val D (sem_two u v) w' = true →
      val D (sem_two a b) w' = true ∨ val D (fun i => decide (i = u)) w' = true := by
    intro w' hlt hv'
    by_contra hc; push Not at hc
    exact Nat.find_min hex hlt ⟨hv', Bool.eq_false_iff.2 hc.1, Bool.eq_false_iff.2 hc.2⟩
  generalize Nat.find hex = w at hw1 hw0 hwu hmin
  have hlt : w < 10 + D.length := by
    by_contra hc; rw [val_ge D _ w (by omega)] at hw1; exact Bool.false_ne_true hw1
  have hge : 10 ≤ w := by
    by_contra hc
    rw [val_input D _ w (by omega)] at hw1 hw0 hwu
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with heq | heq
    · have : (⟨w, by omega⟩ : Fin 10) = u := heq
      rw [this] at hwu; simp at hwu
    · have hwe : (⟨w, by omega⟩ : Fin 10) = v := heq
      rw [hwe] at hw0
      rcases hvb with rfl | rfl <;> simp [sem_two] at hw0
  obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
  rw [val_gate hS _ j hj] at hw1 hw0 hwu
  have htag : tag D j = true := by
    by_contra ht; rw [Bool.not_eq_true] at ht
    rw [ht, gop_false] at hw1 hw0 hwu
    rw [Bool.or_eq_false_iff] at hw0 hwu
    rw [Bool.or_eq_true] at hw1
    rcases hw1 with ha1 | hb1
    · rcases hmin _ ha_lt ha1 with h' | h'
      · rw [hw0.1] at h'; exact Bool.false_ne_true h'
      · rw [hwu.1] at h'; exact Bool.false_ne_true h'
    · rcases hmin _ hb_lt hb1 with h' | h'
      · rw [hw0.2] at h'; exact Bool.false_ne_true h'
      · rw [hwu.2] at h'; exact Bool.false_ne_true h'
  rw [htag, gop_true] at hw1 hw0 hwu
  rw [Bool.and_eq_true] at hw1
  rw [Bool.and_eq_false_iff] at hw0 hwu
  have hma := hmin _ ha_lt hw1.1
  have hmb := hmin _ hb_lt hw1.2
  have hu_not : u ∉ supp 10 D (10 + j) := by
    intro hm
    have := mem_supp.1 hm
    rw [val_gate hS _ j hj, htag, gop_true, Bool.and_eq_true] at this
    change val D (fun i => decide (i = u)) (opA D j) = true ∧ val D (fun i => decide (i = u)) (opB D j) = true at this
    rcases hwu with h' | h'
    · rw [h'] at this; exact Bool.false_ne_true this.1
    · rw [h'] at this; exact Bool.false_ne_true this.2
  have h1' : val D (sem_two u v) (10 + j) = true := by
    rw [val_gate hS _ j hj, htag, gop_true, hw1.1, hw1.2]; rfl
  have h0' : val D (sem_two a b) (10 + j) = false := by
    rw [val_gate hS _ j hj, htag, gop_true]
    rcases hw0 with h' | h'
    · rw [h']; rfl
    · rw [h']; simp
  rcases hma with ha0 | hau
  · have hb0 : val D (sem_two a b) (opB D j) = false := by
      rcases hw0 with h' | h'
      · rw [ha0] at h'; exact Bool.noConfusion h'
      · exact h'
    have hbu : val D (fun i => decide (i = u)) (opB D j) = true := by
      rcases hmb with h' | h'
      · rw [hb0] at h'; exact Bool.noConfusion h'
      · exact h'
    exact ⟨(j, true), sem_mem_W.2 ⟨hj, mem_supp.2 (by rw [sb_src_true]; exact hbu), hu_not⟩,
      h1', h0', by rw [show src D (sem_bar (j, true)) = opA D j from rfl]; exact ha0⟩
  · have hbu : val D (fun i => decide (i = u)) (opB D j) = false := by
      rcases hwu with h' | h'
      · rw [hau] at h'; exact Bool.noConfusion h'
      · exact h'
    have hb0 : val D (sem_two a b) (opB D j) = true := by
      rcases hmb with h' | h'
      · exact h'
      · rw [hbu] at h'; exact Bool.noConfusion h'
    exact ⟨(j, false), sem_mem_W.2 ⟨hj, mem_supp.2 (by rw [sb_src_false]; exact hau), hu_not⟩,
      h1', h0', by rw [show src D (sem_bar (j, false)) = opB D j from rfl]; exact hb0⟩

theorem mem_W_of_pos {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {j t : Fin 10} (hj : j ∈ ineligSet 10 D) (ht : t ∈ supp 10 D (src D (pos j))) :
    pos j ∈ sem_W 10 D t := by
  obtain ⟨h1, h2, -, -⟩ := hpos.1 j hj
  exact sem_mem_W.2 ⟨h1, ht, by rw [h2]; exact Finset.notMem_empty t⟩

theorem pe_co_g10 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {v t j q : Fin 10} (hj : j ∈ ineligSet 10 D) (hv : v ∈ eligSet 10 D)
    (hres : ∀ u ∈ residualUnits 10 D b, v ∈ supp 10 D u.1 → t ∈ supp 10 D u.1)
    {w : ℕ} (hw : v ∈ supp 10 D w ∧ t ∈ supp 10 D w)
    (hg : (g10_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 10 D (src D (pos j)) := by
  obtain ⟨hdv, hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_g10_gr h (sem_g10_comp hD) b hb hvt hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := g10_deg3_cover_free h hD hdv hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj).2.2.1 q hjq)))

theorem pe_co_blow5 {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (br : Fin 10 → ℕ) (hbr : PureBranch 10 D br) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos)
    (a b a1 a2 qa1 qa2 b1 b2 vb : Fin 10)
    (ha : a ∈ eligSet 10 D) (ha1 : a1 ∈ ineligSet 10 D) (ha2 : a2 ∈ ineligSet 10 D)
    (hb1 : b1 ∈ ineligSet 10 D) (hb2 : b2 ∈ ineligSet 10 D)
    (hvb : vb ∉ ineligSet 10 D)
    (hg : a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      (g10_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
      hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true)
    (hAn : 1 ≤ (ru D br a).card) (hsub : ru D br a ⊆ ru D br b) (hBle : (ru D br b).card ≤ 2) :
    False := by
  obtain ⟨hab, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, hda, ga1, ga2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩ := hg
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
  have hres : ∀ u' ∈ residualUnits 10 D br, a ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
    fun u' hu' ha' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', ha'⟩))).2
  have hw : a ∈ supp 10 D u.1 ∧ b ∈ supp 10 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
  have hm1 := mem_W_of_pos hpos ha1 (pe_co_g10 h hD br hbr hpos ha1 ha hres hw ⟨hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
  have hm2 := mem_W_of_pos hpos ha2 (pe_co_g10 h hD br hbr hpos ha2 ha hres hw ⟨hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
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

theorem w3_res2_dichotomy {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbm : sem_MinBranch 10 D br) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) (hR2 : (residualUnits 10 D br).card = 2)
    (a b a1 a2 va b1 b2 vb : Fin 10)
    (ha1 : a1 ∈ ineligSet 10 D) (ha2 : a2 ∈ ineligSet 10 D)
    (hb1 : b1 ∈ ineligSet 10 D) (hb2 : b2 ∈ ineligSet 10 D)
    (hga : (g10_nbB a).card = 3 ∧ a1 ≠ a2 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧ hc_adjB a va = true ∧ va ≠ a1 ∧ va ≠ a2)
    (hgb : (g10_nbB b).card = 3 ∧ b1 ≠ b2 ∧ hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true ∧ vb ≠ b1 ∧ vb ≠ b2)
    (hab_ok : w3_bad a a1 a2 b = false) (hba_ok : w3_bad b b1 b2 a = false) :
    (ru D br a = residualUnits 10 D br ∧ ru D br b = residualUnits 10 D br) ∨
    (∀ x : Fin 10, w3_bad a a1 a2 x = false → w3_bad b b1 b2 x = false → (sem_W 10 D x).card ≤ 2) := by
  have hbr := sem_minBranch_pure hbm
  obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
  have ha3 := two_in_deg3 h hD hpos ha1 ha2 hga.2
  have hb3 := two_in_deg3 h hD hpos hb1 hb2 hgb.2
  have hnea : (ru D br a).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr a; omega)
  have hneb : (ru D br b).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr b; omega)
  have hlea : (ru D br a).card ≤ 2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun u => a ∈ supp 10 D u.1) (residualUnits 10 D br)); unfold ru; omega
  have hleb : (ru D br b).card ≤ 2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun u => b ∈ supp 10 D u.1) (residualUnits 10 D br)); unfold ru; omega
  by_cases ha1c : (ru D br a).card = 1
  · right
    obtain ⟨ua, hua⟩ := Finset.card_eq_one.1 ha1c
    have hua_not_b : ua ∉ ru D br b := fun hm =>
      w3_ru_one_not_mem h hD hB0 br hbm hpos ha1 ha2 hga hua hab_ok (mem_ru.1 hm).2
    have hsub_b : ru D br b ⊆ (residualUnits 10 D br).erase ua := fun u hu =>
      Finset.mem_erase.2 ⟨fun heq => hua_not_b (heq ▸ hu), (mem_ru.1 hu).1⟩
    have hua_in_R : ua ∈ residualUnits 10 D br := (mem_ru.1 (hua ▸ Finset.mem_singleton_self ua)).1
    have herb : ((residualUnits 10 D br).erase ua).card = 1 := by
      rw [Finset.card_erase_of_mem hua_in_R, hR2]
    have hb1c : (ru D br b).card = 1 := by
      have := Finset.card_le_card hsub_b; have := Finset.card_pos.2 hneb; omega
    obtain ⟨ub, hub⟩ := Finset.card_eq_one.1 hb1c
    have hub_in_R : ub ∈ residualUnits 10 D br := (mem_ru.1 (hub ▸ Finset.mem_singleton_self ub)).1
    have huab : ua ≠ ub := fun heq => hua_not_b (heq ▸ hub ▸ Finset.mem_singleton_self ub)
    have hReq2 : residualUnits 10 D br = {ua, ub} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [Finset.card_pair huab, hR2])
      rw [Finset.mem_insert, Finset.mem_singleton] at hu; rcases hu with rfl | rfl; exact hua_in_R; exact hub_in_R
    intro x hxa hxb
    have hrux : ru D br x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
      have huR := (mem_ru.1 hu).1
      rw [hReq2, Finset.mem_insert, Finset.mem_singleton] at huR
      rcases huR with rfl | rfl
      · exact w3_ru_one_not_mem h hD hB0 br hbm hpos ha1 ha2 hga hua hxa (mem_ru.1 hu).2
      · exact w3_ru_one_not_mem h hD hB0 br hbm hpos hb1 hb2 hgb hub hxb (mem_ru.1 hu).2
    have := cc_le h hD br hbr x; rw [hrux, Finset.card_empty] at this; omega
  · by_cases hb1c : (ru D br b).card = 1
    · right
      obtain ⟨ub, hub⟩ := Finset.card_eq_one.1 hb1c
      have hub_not_a : ub ∉ ru D br a := fun hm =>
        w3_ru_one_not_mem h hD hB0 br hbm hpos hb1 hb2 hgb hub hba_ok (mem_ru.1 hm).2
      have hub_in_R : ub ∈ residualUnits 10 D br := (mem_ru.1 (hub ▸ Finset.mem_singleton_self ub)).1
      have hsub_a : ru D br a ⊆ (residualUnits 10 D br).erase ub := fun u hu =>
        Finset.mem_erase.2 ⟨fun heq => hub_not_a (heq ▸ hu), (mem_ru.1 hu).1⟩
      have hera : ((residualUnits 10 D br).erase ub).card = 1 := by
        rw [Finset.card_erase_of_mem hub_in_R, hR2]
      have := Finset.card_le_card hsub_a; have := Finset.card_pos.2 hnea; omega
    · left
      have ha2c : (ru D br a).card = 2 := by have := Finset.card_pos.2 hnea; omega
      have hb2c : (ru D br b).card = 2 := by have := Finset.card_pos.2 hneb; omega
      exact ⟨Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR2, ha2c]),
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR2, hb2c])⟩

theorem petersen_deg3 : ∀ v : Fin 10, (g10_nbB v).card = 3 := by decide +kernel

theorem petersen_w3_bad_eq : ∀ x i1 i2 t : Fin 10,
    i1 ≠ i2 → hc_adjB i1 x = true → hc_adjB i2 x = true → t ≠ x →
    w3_bad x i1 i2 t = false := by decide +kernel

theorem pa_card6 {α : Type} [DecidableEq α] {s : Finset α} {a b c d e f : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s) (hf : f ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) : 6 ≤ s.card := by
  have hsub : ({a, b, c, d, e, f} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae, haf]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe, hbf]),
    Finset.card_insert_of_notMem (by simp [hcd, hce, hcf]),
    Finset.card_insert_of_notMem (by simp [hde, hdf]), Finset.card_pair hef] at this

theorem pa_five {α : Type} [DecidableEq α] {s : Finset α} {a b c d e : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hs : s.card ≤ 5) : ∀ x ∈ s, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  intro x hx
  by_contra hne
  rw [not_or, not_or, not_or, not_or] at hne
  have := pa_card6 hx ha hb hc hd he hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2
    hab hac had hae hbc hbd hbe hcd hce hde
  omega

theorem shared_w3_eq {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbr : PureBranch 10 D br) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    (a b i0 ia ib vb qa qb : Fin 10)
    (ha : a ∈ eligSet 10 D) (hb : b ∈ eligSet 10 D)
    (hi0 : i0 ∈ ineligSet 10 D) (hia : ia ∈ ineligSet 10 D) (hib : ib ∈ ineligSet 10 D)
    (hvb : vb ∉ ineligSet 10 D)
    (hg : a ≠ b ∧ i0 ≠ ia ∧ i0 ≠ ib ∧ ia ≠ ib ∧
          (g10_nbB a).card = 3 ∧ (g10_nbB b).card = 3 ∧
          hc_adjB i0 a = true ∧ hc_adjB ia a = true ∧
          hc_adjB i0 b = true ∧ hc_adjB ib b = true ∧ hc_adjB b vb = true ∧
          hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB b qa = false ∧
          hc_adjB ib qb = true ∧ b ≠ qb ∧ hc_adjB a qb = false ∧ hc_adjB ib a = false)
    (hAne : (ru D br a).Nonempty) (hruEq : ru D br a = ru D br b) (hBle : (ru D br b).card ≤ 2) : False := by
  obtain ⟨hab, h0a, h0b, habi, hda, hdb, g0a, gaa, g0b, gbb, gvb, gqa, haqa, gbqa, gqb, hbqb, gaqb, gnba⟩ := hg
  obtain ⟨u, hu⟩ := hAne
  have hres1 : ∀ u' ∈ residualUnits 10 D br, a ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
    fun u' hu' ha' => (mem_ru.1 (hruEq ▸ mem_ru.2 ⟨hu', ha'⟩)).2
  have hres2 : ∀ u' ∈ residualUnits 10 D br, b ∈ supp 10 D u'.1 → a ∈ supp 10 D u'.1 :=
    fun u' hu' hb' => (mem_ru.1 (hruEq.symm ▸ mem_ru.2 ⟨hu', hb'⟩)).2
  have hw : a ∈ supp 10 D u.1 ∧ b ∈ supp 10 D u.1 :=
    ⟨(mem_ru.1 hu).2, (mem_ru.1 (hruEq ▸ hu)).2⟩
  have hpa_in_b := mem_W_of_pos hpos hia (pe_co_g10 h hD br hbr hpos hia ha hres1 hw ⟨hda, gaa, gqa, hab, haqa, gbqa⟩)
  have ha_in_pb := pe_co_g10 h hD br hbr hpos hib hb hres2 ⟨hw.2, hw.1⟩ ⟨hdb, gbb, gqb, hab.symm, hbqb, gaqb⟩
  have hp0_in_b := as_mem hpos hi0 ((hc_adjB_iff _ _).1 g0b)
  have hpb_in_b := as_mem hpos hib ((hc_adjB_iff _ _).1 gbb)
  obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
  have hWb_le4 : (sem_W 10 D b).card ≤ 4 := by have := cc_le h hD br hbr b; omega
  have hWb := pa_four hpb_in_b hp0_in_b hpa_in_b hev
    (fun e => h0b.symm (hpos.2 _ hib _ hi0 e))
    (fun e => habi.symm (hpos.2 _ hib _ hia e))
    (fun e => hvb (hfv _ hib e.symm ▸ hib))
    (fun e => h0a (hpos.2 _ hi0 _ hia e))
    (fun e => hvb (hfv _ hi0 e.symm ▸ hi0))
    (fun e => hvb (hfv _ hia e.symm ▸ hia))
    hWb_le4
  have hfull := full_g10 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gbb) (fun p hp hne1 hsub' => by
    rcases hWb p hp with rfl | rfl | rfl | rfl
    · exact hne1 rfl
    · exact h0b (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hi0)))
    · exact habi (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hia)))
    · exact hvb (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbev).2.1) ▸ hib))
  exact sem_adjB_false.1 gnba ((hfull a).1 ha_in_pb)

theorem val_gate_of_supp_pair {D : Dag} (hS : Strict 10 D) {e : ℕ × Bool} {a b : Fin 10}
    (hlt : e.1 < D.length) (hand : tag D e.1 = true)
    (ha : a ∈ supp 10 D (src D e)) (hb : b ∈ supp 10 D (src D (sem_bar e))) :
    val D (sem_two a b) (10 + e.1) = true := by
  have h1 := val_mono hS (fun i => decide (i = a)) (sem_two a b)
    (fun i hi => by simp only [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
    (src D e) (mem_supp.1 ha)
  have h2 := val_mono hS (fun i => decide (i = b)) (sem_two a b)
    (fun i hi => by simp only [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
    (src D (sem_bar e)) (mem_supp.1 hb)
  rw [val_gate hS _ e.1 hlt, hand, gop_true]
  rcases he : e with ⟨j, s⟩; rw [he] at h1 h2
  cases s
  · rw [sb_src_false] at h1; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h2; simp [h1, h2]
  · rw [sb_src_true] at h1; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h2; simp [h1, h2]

theorem val_gate_of_supp_and_val {D : Dag} (hS : Strict 10 D) {e : ℕ × Bool} {a b : Fin 10}
    (hlt : e.1 < D.length) (hand : tag D e.1 = true)
    (ha : a ∈ supp 10 D (src D e)) (hb : val D (sem_two a b) (src D (sem_bar e)) = true) :
    val D (sem_two a b) (10 + e.1) = true := by
  have h1 := val_mono hS (fun i => decide (i = a)) (sem_two a b)
    (fun i hi => by simp only [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
    (src D e) (mem_supp.1 ha)
  rw [val_gate hS _ e.1 hlt, hand, gop_true]
  rcases he : e with ⟨j, s⟩; rw [he] at h1 hb
  cases s
  · rw [sb_src_false] at h1; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at hb; simp [h1, hb]
  · rw [sb_src_true] at h1; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at hb; simp [h1, hb]

theorem not_edge_sem_two {a b : Fin 10} (hnab : ¬ Adj a b) : ¬ G10Edge (sem_two a b) := by
  rw [g10Edge_iff_adj]
  rintro ⟨p, q, hpq, hp, hq⟩
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact adj_irrefl _ hpq
  · exact hnab hpq
  · exact hnab (adj_symm hpq)
  · exact adj_irrefl _ hpq

theorem full_of_le2 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos) {i x v : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hix : Adj i x) (hxv : Adj x v) (hv : v ∉ ineligSet 10 D)
    (hle : (sem_W 10 D x).card ≤ 2) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ Adj i t := by
  have hp := as_mem hpos hi hix
  obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos hxv
  have hne : pos i ≠ ev := fun hh => hv (hfv i hi hh.symm ▸ hi)
  have hWx := pa_two hp hev hne hle
  exact full_g10 h hD hB0 hpos hi hix (fun p hp' hne1 hsub => by
    rcases hWx p hp' with rfl | rfl
    · exact hne1 rfl
    · exact hv (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1) ▸ hi))

theorem meeting_le {D : Dag} (hS : Strict 10 D) {x y : Fin 10} {w : ℕ}
    (hv : val D (sem_two x y) w = true) (hx : x ∉ supp 10 D w) (hy : y ∉ supp 10 D w) :
    ∃ j s, j < D.length ∧ 10 + j ≤ w ∧ (j, s) ∈ sem_W 10 D x ∧ (j, !s) ∈ sem_W 10 D y := by
  classical
  have hex : ∃ u, u ≤ w ∧ val D (sem_two x y) u = true ∧ x ∉ supp 10 D u ∧ y ∉ supp 10 D u :=
    ⟨w, le_refl w, hv, hx, hy⟩
  obtain ⟨hle, huv, hux, huy⟩ := Nat.find_spec hex
  have hmin : ∀ u', u' < Nat.find hex → val D (sem_two x y) u' = true →
      x ∈ supp 10 D u' ∨ y ∈ supp 10 D u' := by
    intro u' hlt hv'
    by_contra hc; push Not at hc
    exact Nat.find_min hex hlt ⟨le_trans (le_of_lt hlt) hle, hv', hc.1, hc.2⟩
  generalize Nat.find hex = u at hle huv hux huy hmin
  have hlt : u < 10 + D.length := by
    by_contra hc; rw [val_ge D _ u (by omega)] at huv; exact Bool.false_ne_true huv
  have hge : 10 ≤ u := by
    by_contra hc
    rw [val_input D _ u (by omega)] at huv
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at huv
    rcases huv with heq | heq
    · exact hux (by rw [mem_supp, val_input D _ u (by omega)]; exact decide_eq_true heq)
    · exact huy (by rw [mem_supp, val_input D _ u (by omega)]; exact decide_eq_true heq)
  obtain ⟨j, rfl⟩ : ∃ j, u = 10 + j := ⟨u - 10, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
  rw [val_gate hS _ j hj] at huv
  have htag : tag D j = true := by
    by_contra ht; rw [Bool.not_eq_true] at ht
    rw [ht, gop_false, Bool.or_eq_true] at huv
    rcases huv with ha1 | hb1
    · rcases hmin _ ha_lt ha1 with h' | h'
      · exact hux (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl h')
      · exact huy (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl h')
    · rcases hmin _ hb_lt hb1 with h' | h'
      · exact hux (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr h')
      · exact huy (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr h')
  rw [htag, gop_true, Bool.and_eq_true] at huv
  have hxa := hmin _ ha_lt huv.1
  have hxb := hmin _ hb_lt huv.2
  have hxab : ¬(x ∈ supp 10 D (opA D j) ∧ x ∈ supp 10 D (opB D j)) :=
    fun h' => hux (by rw [sem_supp_and hS hj htag, Finset.mem_inter]; exact h')
  have hyab : ¬(y ∈ supp 10 D (opA D j) ∧ y ∈ supp 10 D (opB D j)) :=
    fun h' => huy (by rw [sem_supp_and hS hj htag, Finset.mem_inter]; exact h')
  rcases hxa with h1 | h1 <;> rcases hxb with h2 | h2
  · exact absurd ⟨h1, h2⟩ hxab
  · exact ⟨j, false, hj, hle, sem_mem_W.2 ⟨hj, by rw [sb_src_false]; exact h1, hux⟩,
      sem_mem_W.2 ⟨hj, by rw [show src D (j, !false) = opB D j from rfl]; exact h2, huy⟩⟩
  · exact ⟨j, true, hj, hle, sem_mem_W.2 ⟨hj, by rw [sb_src_true]; exact h2, hux⟩,
      sem_mem_W.2 ⟨hj, by rw [show src D (j, !true) = opA D j from rfl]; exact h1, huy⟩⟩
  · exact absurd ⟨h1, h2⟩ hyab

theorem o1_common_zero : ∀ r1 r2 t : Fin 10,
    hc_adjB 0 r1 = true → hc_adjB 0 r2 = true → r1 ≠ r2 → t ≠ 0 →
    hc_adjB r1 t = false ∨ hc_adjB r2 t = false := by decide +kernel

theorem o1_priv_nb {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) (h0 : (0 : Fin 10) ∈ ineligSet 10 D)
    {u r1 r2 : Fin 10} (hg : hc_adjB 0 u = true ∧ hc_adjB 0 r1 = true ∧ hc_adjB 0 r2 = true ∧
      r1 ≠ u ∧ r2 ≠ u ∧ r1 ≠ r2 ∧ u ≠ 0)
    (hWu : (sem_W 10 D u).card ≤ 2) :
    ∃ Z, Z ≠ pos 0 ∧ sem_W 10 D u = {pos 0, Z} ∧ ∀ t : Fin 10, t ≠ u → Z ∉ sem_W 10 D t := by
  obtain ⟨g0u, g01, g02, h1u, h2u, h12, hu0⟩ := hg
  obtain ⟨Z, hZn, hW, hZp1⟩ := ps_nonadj h hD hpos h0 ((hc_adjB_iff _ _).1 g0u)
    ((hc_adjB_iff _ _).1 g01) h1u (petersen_deg3 u) hWu
  obtain ⟨Z', hZ'n, hW', hZp2⟩ := ps_nonadj h hD hpos h0 ((hc_adjB_iff _ _).1 g0u)
    ((hc_adjB_iff _ _).1 g02) h2u (petersen_deg3 u) hWu
  have hZeq : Z' = Z := by
    have hm : Z' ∈ sem_W 10 D u := by rw [hW']; simp
    rw [hW, Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.resolve_left hZ'n
  rw [hZeq] at hZp2
  refine ⟨Z, hZn, hW, fun t htu hZt => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    rw [as_W h hD hpos h0, Finset.mem_singleton] at hZt
    have hu_in : sem_bar (pos 0) ∈ sem_W 10 D u := hZt ▸ (by rw [hW]; simp)
    exact hu0 (as_priv hpos h0 hu_in)
  · rcases o1_common_zero r1 r2 t g01 g02 h12 ht0 with h1 | h2
    · exact hZp1 t htu (sem_adjB_false.1 h1) hZt
    · exact hZp2 t htu (sem_adjB_false.1 h2) hZt

theorem o1_order {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbm : sem_MinBranch 10 D br) (hR0 : residualUnits 10 D br = ∅)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    (hI : ineligSet 10 D = {0})
    (hp0_val : ∀ x, val D x (10 + (pos 0).1) = true → G10Edge x)
    (hM_all : ∀ v : Fin 10, merges 10 D (carrierT 10 D {v}) = ∅)
    {u u' u'' a b c d : Fin 10} {Zu Zu' Zu'' R : ℕ × Bool}
    (hg : hc_adjB a b = false ∧ hc_adjB c a = true ∧ hc_adjB d a = true ∧
      c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
      u ≠ 0 ∧ u' ≠ 0 ∧ u'' ≠ 0 ∧ u ≠ u' ∧ u' ≠ u'' ∧ u ≠ u'' ∧
      u' ≠ a ∧ u' ≠ b ∧ u'' ≠ a ∧ u'' ≠ b)
    (hWu : sem_W 10 D u = {pos 0, Zu})
    (hWu' : sem_W 10 D u' = {pos 0, Zu'})
    (hWu'' : sem_W 10 D u'' = {pos 0, Zu''})
    (hZu'_p : ∀ t, t ≠ u' → Zu' ∉ sem_W 10 D t)
    (hZu''_p : ∀ t, t ≠ u'' → Zu'' ∉ sem_W 10 D t)
    (hWa : sem_W 10 D a = {sem_bar Zu, R})
    (hWb : sem_W 10 D b = {sem_bar Zu, sem_bar R})
    (hWc : sem_W 10 D c = {sem_bar Zu', sem_bar R})
    (hWd : sem_W 10 D d = {sem_bar Zu'', sem_bar R})
    (hW_other : ∀ v : Fin 10, v ≠ 0 → v ≠ u → v ≠ u' → v ≠ u'' → v ≠ a → v ≠ b →
      ∀ e ∈ sem_W 10 D v, e = sem_bar Zu' ∨ e = sem_bar Zu'' ∨ e = R ∨ e = sem_bar R)
    (hR_supp : supp 10 D (10 + R.1) = ∅) :
    Zu.1 < Zu'.1 := by
  classical
  have hS := h.1
  obtain ⟨hnab', hca', hda', hca_ne, hcb', hda_ne, hdb', hu0, hu'0, hu''0, huu', hu'u'', huu'', hu'a, hu'b, hu''a, hu''b⟩ := hg
  have hnab : ¬ Adj a b := sem_adjB_false.1 hnab'
  have hca : Adj c a := (hc_adjB_iff _ _).1 hca'
  have hda : Adj d a := (hc_adjB_iff _ _).1 hda'
  have hR_a : R ∈ sem_W 10 D a := by rw [hWa]; simp
  have hbR_b : sem_bar R ∈ sem_W 10 D b := by rw [hWb]; simp
  have hZu'_u' : Zu' ∈ sem_W 10 D u' := by rw [hWu']; simp
  have hZu''_u'' : Zu'' ∈ sem_W 10 D u'' := by rw [hWu'']; simp
  have hval_R : val D (sem_two a b) (10 + R.1) = true :=
    val_gate_of_supp_pair hS (sem_mem_W.1 hR_a).1 (sem_W_and hS hR_a)
      (sem_mem_W.1 hR_a).2.1 (sem_mem_W.1 hbR_b).2.1
  have hval_p0 : val D (sem_two a b) (10 + (pos 0).1) = false := by
    by_contra hc; rw [Bool.not_eq_false] at hc
    exact not_edge_sem_two hnab (hp0_val _ hc)
  have ⟨hZu'_f, hZu'_src⟩ : val D (sem_two a b) (10 + Zu'.1) = false ∧ val D (sem_two a b) (src D Zu') = true := by
    obtain ⟨e, hec, -, hf, hbf⟩ := pa_ed_avoid_min h hD hca hnab hca_ne hcb' (Or.inr rfl)
    rw [hWc, Finset.mem_insert, Finset.mem_singleton] at hec
    rcases hec with rfl | rfl
    · exact ⟨hf, by simpa [sem_bar_bar] using hbf⟩
    · rw [show (sem_bar R).1 = R.1 from rfl, hval_R] at hf; exact Bool.noConfusion hf
  have ⟨hZu''_f, hZu''_src⟩ : val D (sem_two a b) (10 + Zu''.1) = false ∧ val D (sem_two a b) (src D Zu'') = true := by
    obtain ⟨e, hed, -, hf, hbf⟩ := pa_ed_avoid_min h hD hda hnab hda_ne hdb' (Or.inr rfl)
    rw [hWd, Finset.mem_insert, Finset.mem_singleton] at hed
    rcases hed with rfl | rfl
    · exact ⟨hf, by simpa [sem_bar_bar] using hbf⟩
    · rw [show (sem_bar R).1 = R.1 from rfl, hval_R] at hf; exact Bool.noConfusion hf
  let inU : ℕ → Prop := fun w => w < 10 + D.length ∧ val D (sem_two a b) w = true ∧
    a ∉ supp 10 D w ∧ b ∉ supp 10 D w
  let stepU : ℕ → ℕ → Prop := fun w1 w2 => sem_step 10 D w1 w2 ∧ inU w1 ∧ inU w2
  have hnot_supp_src : ∀ {v : Fin 10} {Z : ℕ × Bool}, (∀ t, t ≠ v → Z ∉ sem_W 10 D t) →
      Z ∈ sem_W 10 D v → ∀ t, t ≠ v → t ∉ supp 10 D (src D Z) := by
    intro v Z hZp hZv t htv ht
    exact hZp t htv (zm_mem hS (hM_all t) (sem_mem_W.1 hZv).1 (sem_W_and hS hZv) ht)
  have hZu'_inU : inU (src D Zu') := by
    have hj := (sem_mem_W.1 hZu'_u').1
    exact ⟨lt_trans (sem_src_lt hS hj Zu'.2) (by omega), hZu'_src,
      hnot_supp_src hZu'_p hZu'_u' a hu'a.symm, hnot_supp_src hZu'_p hZu'_u' b hu'b.symm⟩
  have hZu''_inU : inU (src D Zu'') := by
    have hj := (sem_mem_W.1 hZu''_u'').1
    exact ⟨lt_trans (sem_src_lt hS hj Zu''.2) (by omega), hZu''_src,
      hnot_supp_src hZu''_p hZu''_u'' a hu''a.symm, hnot_supp_src hZu''_p hZu''_u'' b hu''b.symm⟩
  have hZ_uniq : ∀ j s, (j, s) ∈ sem_W 10 D a → (j, !s) ∈ sem_W 10 D b → j = R.1 := by
    intro j s ha1 hb1
    rw [hWa, Finset.mem_insert, Finset.mem_singleton] at ha1
    rw [hWb, Finset.mem_insert, Finset.mem_singleton] at hb1
    rcases ha1 with h1 | h1
    · rcases hb1 with h2 | h2
      · have : (j, s) = (j, !s) := h1.trans h2.symm
        have hsb := congrArg Prod.snd this; cases s <;> exact Bool.noConfusion hsb
      · exact congrArg Prod.fst h2
    · exact congrArg Prod.fst h1
  have hU_entry : ∀ w, inU w → w = 10 + R.1 ∨ ∃ w1, stepU w1 w := by
    intro w hw
    obtain ⟨hwlt, hwv, han, hbn⟩ := hw
    have hwge : 10 ≤ w := by
      by_contra hc; rw [val_input D _ w (by omega)] at hwv
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hwv
      rcases hwv with h' | h'
      · exact han (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
      · exact hbn (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
    obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
    have hj : j < D.length := by omega
    obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
    rw [val_gate hS _ j hj] at hwv
    by_cases ht : tag D j = true
    · rw [ht, gop_true, Bool.and_eq_true] at hwv
      by_cases haU : a ∉ supp 10 D (opA D j) ∧ b ∉ supp 10 D (opA D j)
      · right; exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, hwv.1, haU.1, haU.2⟩,
          ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, han, hbn⟩⟩⟩
      · by_cases hbU : a ∉ supp 10 D (opB D j) ∧ b ∉ supp 10 D (opB D j)
        · right; exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hwv.2, hbU.1, hbU.2⟩,
            ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, han, hbn⟩⟩⟩
        · left
          rw [not_and_or, Classical.not_not, Classical.not_not] at haU hbU
          have haab : ¬(a ∈ supp 10 D (opA D j) ∧ a ∈ supp 10 D (opB D j)) :=
            fun h' => han (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          have hbab : ¬(b ∈ supp 10 D (opA D j) ∧ b ∈ supp 10 D (opB D j)) :=
            fun h' => hbn (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          rcases haU with ha1 | hb1 <;> rcases hbU with ha2 | hb2
          · exact absurd ⟨ha1, ha2⟩ haab
          · have := hZ_uniq j false (sem_mem_W.2 ⟨hj, by rw [sb_src_false]; exact ha1, han⟩)
              (sem_mem_W.2 ⟨hj, by rw [show src D (j, !false) = opB D j from rfl]; exact hb2, hbn⟩); omega
          · have := hZ_uniq j true (sem_mem_W.2 ⟨hj, by rw [sb_src_true]; exact ha2, han⟩)
              (sem_mem_W.2 ⟨hj, by rw [show src D (j, !true) = opA D j from rfl]; exact hb1, hbn⟩); omega
          · exact absurd ⟨hb1, hb2⟩ hbab
    · rw [Bool.not_eq_true] at ht; rw [ht, gop_false, Bool.or_eq_true] at hwv
      have haa : a ∉ supp 10 D (opA D j) := fun hm => han (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have hab : a ∉ supp 10 D (opB D j) := fun hm => han (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      have hba : b ∉ supp 10 D (opA D j) := fun hm => hbn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have hbb : b ∉ supp 10 D (opB D j) := fun hm => hbn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      right
      rcases hwv with ha1 | hb1
      · exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, ha1, haa, hba⟩,
          ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, ha1]; rfl, han, hbn⟩⟩⟩
      · exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hb1, hab, hbb⟩,
          ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, hb1]; simp, han, hbn⟩⟩⟩
  have hU_reach : ∀ w, inU w → Relation.ReflTransGen stepU (10 + R.1) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases hU_entry w hw with rfl | ⟨w1, hw1⟩
      · exact Relation.ReflTransGen.refl
      · exact (ih w1 (sem_step_lt hS hw1.1) hw1.2.1).tail hw1
  have hfan_eq_b : ∀ w, 2 ≤ fanout D w → ∃ x ∈ eligSet 10 D, br x = w := by
    intro w hfw
    have hne_s : (supp 10 D w).Nonempty := sem_bzero_branch hS hB0 (by omega)
    have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
        by show 0 + 1 < fanout D w; omega⟩, hne_s⟩
    have hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
      by_contra hnr
      have : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
      rw [hR0] at this; exact Finset.notMem_empty _ this
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hwr
    exact ⟨x, hx, congrArg Sigma.fst hxe⟩
  have hsrc_ne : src D Zu' ≠ src D Zu'' := fun heq =>
    hnot_supp_src hZu''_p hZu''_u'' u' hu'u'' (heq ▸ (sem_mem_W.1 hZu'_u').2.1)
  have hstep_Zu' : sem_step 10 D (src D Zu') (10 + Zu'.1) :=
    sem_step_src (sem_mem_W.1 hZu'_u').1 Zu'.2
  have hstep_Zu'' : sem_step 10 D (src D Zu'') (10 + Zu''.1) :=
    sem_step_src (sem_mem_W.1 hZu''_u'').1 Zu''.2
  have hfan1_det : ∀ {w1 c1 c2}, fanout D w1 = 1 → sem_step 10 D w1 c1 → sem_step 10 D w1 c2 → c1 = c2 :=
    fun hf h1 h2 => sem_step_unique h1 h2 hf
  have hex_split : ∃ w, inU w ∧ 2 ≤ fanout D w := by
    by_contra hno; push Not at hno
    have hdet : ∀ w1 c1 c2, stepU w1 c1 → stepU w1 c2 → c1 = c2 := fun w1 c1 c2 s1 s2 => by
      have hf1 := sem_step_fanout s1.1; have hf2 := hno w1 s1.2.1
      exact hfan1_det (by omega) s1.1 s2.1
    have htot : ∀ {w0 x y}, Relation.ReflTransGen stepU w0 x → Relation.ReflTransGen stepU w0 y →
        Relation.ReflTransGen stepU x y ∨ Relation.ReflTransGen stepU y x := by
      intro w0 x y hx
      induction hx using Relation.ReflTransGen.head_induction_on with
      | refl => intro hy; exact Or.inl hy
      | head hab hbx ih =>
        intro hy
        rcases Relation.ReflTransGen.cases_head hy with rfl | ⟨w2, hac, hcy⟩
        · exact Or.inr (Relation.ReflTransGen.head hab hbx)
        · exact ih (hdet _ _ w2 hab hac ▸ hcy)
    rcases htot (hU_reach _ hZu'_inU) (hU_reach _ hZu''_inU) with h12 | h21
    · rcases Relation.ReflTransGen.cases_head h12 with heq | ⟨w2, hw2, -⟩
      · exact hsrc_ne heq
      · have hf1 := sem_step_fanout hstep_Zu'; have hf2 := hno _ hZu'_inU
        have hceq := hfan1_det (by omega) hw2.1 hstep_Zu'
        have hv := hw2.2.2.2.1; rw [hceq, hZu'_f] at hv; exact Bool.false_ne_true hv
    · rcases Relation.ReflTransGen.cases_head h21 with heq | ⟨w2, hw2, -⟩
      · exact hsrc_ne heq.symm
      · have hf1 := sem_step_fanout hstep_Zu''; have hf2 := hno _ hZu''_inU
        have hceq := hfan1_det (by omega) hw2.1 hstep_Zu''
        have hv := hw2.2.2.2.1; rw [hceq, hZu''_f] at hv; exact Bool.false_ne_true hv
  let wb := Nat.find hex_split
  have hwb_spec : inU wb ∧ 2 ≤ fanout D wb := Nat.find_spec hex_split
  have hwb_min : ∀ w, w < wb → inU w → fanout D w ≤ 1 := fun w hlt hw => by
    by_contra hc; exact Nat.find_min hex_split hlt ⟨hw, by omega⟩
  obtain ⟨x, hxE, hbx⟩ := hfan_eq_b wb hwb_spec.2
  have hwb_gt_R : 10 + R.1 < wb := by
    have hle := sem_rtg_le hS (fun _ _ s => s.1) (hU_reach wb hwb_spec.1)
    have hne : 10 + R.1 ≠ wb := fun heq => by
      have hx_in : x ∈ supp 10 D (10 + R.1) := by rw [heq, ← hbx, (hbm x hxE).2.1]; exact Finset.mem_singleton_self x
      rw [hR_supp] at hx_in; exact Finset.notMem_empty _ hx_in
    omega
  have hreach_from_wb : ∀ w, inU w → (w < wb → ∀ c2, stepU w c2 → False) → Relation.ReflTransGen stepU wb w := by
    intro w hw hdead
    have hdet_lt : ∀ w1 c1 c2, w1 < wb → stepU w1 c1 → stepU w1 c2 → c1 = c2 := fun w1 c1 c2 hlt s1 s2 => by
      have hf1 := sem_step_fanout s1.1; have hf2 := hwb_min w1 hlt s1.2.1
      exact hfan1_det (by omega) s1.1 s2.1
    have hsplit : ∀ {w0}, Relation.ReflTransGen stepU w0 wb → Relation.ReflTransGen stepU w0 w →
        Relation.ReflTransGen stepU wb w ∨ Relation.ReflTransGen stepU w wb := by
      intro w0 h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => intro h2; exact Or.inl h2
      | head hac hcwb ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨w2, had, hdw⟩
        · exact Or.inr (Relation.ReflTransGen.head hac hcwb)
        · have halt := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcwb)
          exact ih (hdet_lt _ _ w2 halt hac had ▸ hdw)
    rcases hsplit (hU_reach wb hwb_spec.1) (hU_reach w hw) with h1 | h2
    · exact h1
    · rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨w2, hw2, h2wb⟩
      · exact Relation.ReflTransGen.refl
      · have hwlt : w < wb := (sem_step_lt hS hw2.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) h2wb)
        exact absurd hw2 (hdead hwlt w2)
  have hwb_to_Zu' : Relation.ReflTransGen stepU wb (src D Zu') :=
    hreach_from_wb _ hZu'_inU (fun hlt c2 hc2 => by
      have hf1 := sem_step_fanout hstep_Zu'; have hf2 := hwb_min _ hlt hZu'_inU
      have hceq := hfan1_det (by omega) hc2.1 hstep_Zu'
      have hv := hc2.2.2.2.1; rw [hceq, hZu'_f] at hv; exact Bool.false_ne_true hv)
  have hwb_to_Zu'' : Relation.ReflTransGen stepU wb (src D Zu'') :=
    hreach_from_wb _ hZu''_inU (fun hlt c2 hc2 => by
      have hf1 := sem_step_fanout hstep_Zu''; have hf2 := hwb_min _ hlt hZu''_inU
      have hceq := hfan1_det (by omega) hc2.1 hstep_Zu''
      have hv := hc2.2.2.2.1; rw [hceq, hZu''_f] at hv; exact Bool.false_ne_true hv)
  have hexit_U : ∀ (y : Fin 10), y ∈ eligSet 10 D → br y = wb → ∀ t, Relation.ReflTransGen stepU wb t →
      y ∉ supp 10 D t → ∃ e ∈ sem_W 10 D y, inU (10 + e.1) ∧ wb < 10 + e.1 ∧
        Relation.ReflTransGen stepU (10 + e.1) t := by
    intro y hyE hby t hp
    have hyw : y ∈ supp 10 D wb := by rw [← hby, (hbm y hyE).2.1]; exact Finset.mem_singleton_self y
    induction hp with
    | refl => intro hyt; exact absurd hyw hyt
    | @tail u1 v1 hp1 hstep ih =>
      intro hyt
      by_cases hyu : y ∈ supp 10 D u1
      · obtain ⟨hjlt, hjge, hop⟩ := hstep.1
        have hveq : 10 + (v1 - 10) = v1 := by omega
        have heW : ∃ s : Bool, (v1 - 10, s) ∈ sem_W 10 D y := by
          rcases hop with ha1 | hb1
          · exact ⟨false, sem_mem_W.2 ⟨by omega, by simpa [src, ha1] using hyu, by rwa [hveq]⟩⟩
          · exact ⟨true, sem_mem_W.2 ⟨by omega, by simpa [src, hb1] using hyu, by rwa [hveq]⟩⟩
        obtain ⟨s, hs⟩ := heW
        have hltv : wb < v1 := lt_of_le_of_lt (sem_rtg_le hS (fun _ _ st => st.1) hp1) (sem_step_lt hS hstep.1)
        exact ⟨(v1 - 10, s), hs, by simpa [hveq] using hstep.2.2, by omega, by rw [hveq]⟩
      · obtain ⟨e, heW, heU, hltv, hrt⟩ := ih hyu
        exact ⟨e, heW, heU, hltv, hrt.tail hstep⟩
  have hx_ne0 : x ≠ 0 := fun heq => (Finset.mem_sdiff.1 (hI ▸ Finset.mem_singleton_self (0 : Fin 10))).2 (heq ▸ hxE)
  have hx_nea : x ≠ a := fun heq => hwb_spec.1.2.2.1 (heq ▸ (hbx ▸ (hbm x hxE).2.1 ▸ Finset.mem_singleton_self x))
  have hx_neb : x ≠ b := fun heq => hwb_spec.1.2.2.2 (heq ▸ (hbx ▸ (hbm x hxE).2.1 ▸ Finset.mem_singleton_self x))
  have hx_neu' : x ≠ u' := fun heq => by
    subst heq
    obtain ⟨e, heW, heU, -, -⟩ := hexit_U x hxE hbx _ hwb_to_Zu'' (hnot_supp_src hZu''_p hZu''_u'' x hu'u'')
    rw [hWu', Finset.mem_insert, Finset.mem_singleton] at heW
    rcases heW with rfl | rfl
    · have hv := heU.2.1; rw [hval_p0] at hv; exact False.elim (Bool.false_ne_true hv)
    · have hv := heU.2.1; rw [hZu'_f] at hv; exact Bool.false_ne_true hv
  have hx_neu'' : x ≠ u'' := fun heq => by
    subst heq
    obtain ⟨e, heW, heU, -, -⟩ := hexit_U x hxE hbx _ hwb_to_Zu' (hnot_supp_src hZu'_p hZu'_u' x hu'u''.symm)
    rw [hWu'', Finset.mem_insert, Finset.mem_singleton] at heW
    rcases heW with rfl | rfl
    · have hv := heU.2.1; rw [hval_p0] at hv; exact False.elim (Bool.false_ne_true hv)
    · have hv := heU.2.1; rw [hZu''_f] at hv; exact Bool.false_ne_true hv
  have hx_eq_u : x = u := by
    by_contra hxu
    obtain ⟨e, heW, heU, hlt_wb, -⟩ := hexit_U x hxE hbx _ hwb_to_Zu' (hnot_supp_src hZu'_p hZu'_u' x hx_neu')
    rcases hW_other x hx_ne0 hxu hx_neu' hx_neu'' hx_nea hx_neb e heW with rfl | rfl | rfl | rfl
    · have hv := heU.2.1; rw [show (sem_bar Zu').1 = Zu'.1 from rfl, hZu'_f] at hv; exact Bool.false_ne_true hv
    · have hv := heU.2.1; rw [show (sem_bar Zu'').1 = Zu''.1 from rfl, hZu''_f] at hv; exact Bool.false_ne_true hv
    · omega
    · rw [show (sem_bar R).1 = R.1 from rfl] at hlt_wb; omega
  subst hx_eq_u
  obtain ⟨e, heW, heU, -, hrt⟩ := hexit_U x hxE hbx _ hwb_to_Zu' (hnot_supp_src hZu'_p hZu'_u' x huu')
  rw [hWu, Finset.mem_insert, Finset.mem_singleton] at heW
  rcases heW with rfl | rfl
  · have hv := heU.2.1; rw [hval_p0] at hv; exact False.elim (Bool.false_ne_true hv)
  · have hle := sem_rtg_le hS (fun _ _ st => st.1) hrt
    have hlt := sem_src_lt hS (sem_mem_W.1 hZu'_u').1 Zu'.2
    change src D Zu' < 10 + Zu'.1 at hlt
    omega

theorem elim_O1 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h9 : totalSurplus 10 D ≤ 9)
    (hI : ineligSet 10 D = {0}) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hel := inelig_card_add 10 D
  have hts := totalSurplus_split 10 D
  have hI1 : (ineligSet 10 D).card = 1 := by rw [hI]; decide
  have hE9 : (eligSet 10 D).card = 9 := by omega
  have hBp_ge := elig_le_Bplus hS br hbp
  have hB0 : Bzero 10 D = 0 := by omega
  have hR0 : residualUnits 10 D br = ∅ := Finset.card_eq_zero.1 (by have := card_residual hS br hbp; omega)
  have hcc0 : ∀ x : Fin 10, (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card ≤ 2 := fun x => by
    have h1 := cc_le h hD br hbp x
    unfold ru at h1; rw [hR0, Finset.filter_empty, Finset.card_empty] at h1; omega
  have hW2 : ∀ x : Fin 10, (sem_W 10 D x).card ≤ 2 := fun x => by have := hcc0 x; omega
  have h0 : (0 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have hni : ∀ v : Fin 10, v ≠ 0 → v ∉ ineligSet 10 D := fun v hv hm => by
    rw [hI, Finset.mem_singleton] at hm; exact hv hm
  obtain ⟨Z1, hZ1n, hW1, hZ1p⟩ := o1_priv_nb h hD hpos h0 (u := 1) (r1 := 4) (r2 := 5) (by decide) (hW2 1)
  obtain ⟨Z4, hZ4n, hW4, hZ4p⟩ := o1_priv_nb h hD hpos h0 (u := 4) (r1 := 1) (r2 := 5) (by decide) (hW2 4)
  obtain ⟨Z5, hZ5n, hW5, hZ5p⟩ := o1_priv_nb h hD hpos h0 (u := 5) (r1 := 1) (r2 := 4) (by decide) (hW2 5)
  have hZ1_2 : sem_bar Z1 ∈ sem_W 10 D 2 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 1 2)
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z1 := he.resolve_left (fun hh => hni 2 (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ1_6 : sem_bar Z1 ∈ sem_W 10 D 6 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 1 6)
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z1 := he.resolve_left (fun hh => hni 6 (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ4_3 : sem_bar Z4 ∈ sem_W 10 D 3 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 4 3)
    rw [hW4, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z4 := he.resolve_left (fun hh => hni 3 (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ4_9 : sem_bar Z4 ∈ sem_W 10 D 9 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 4 9)
    rw [hW4, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z4 := he.resolve_left (fun hh => hni 9 (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ5_7 : sem_bar Z5 ∈ sem_W 10 D 7 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 5 7)
    rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z5 := he.resolve_left (fun hh => hni 7 (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ5_8 : sem_bar Z5 ∈ sem_W 10 D 8 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 5 8)
    rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z5 := he.resolve_left (fun hh => hni 8 (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  obtain ⟨r2, hr2_2, hbr2_3, -, -⟩ := pa_ed h hD hpos (by decide : Adj 2 3)
  have hne_2 : sem_bar Z1 ≠ r2 := fun hh => hZ1p 3 (by decide) (by rw [← sem_bar_bar Z1, hh]; exact hbr2_3)
  have hW2_eq : sem_W 10 D 2 = {sem_bar Z1, r2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hne_2]; exact hW2 2)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ1_2; exact hr2_2
  have hbr2_7 : sem_bar r2 ∈ sem_W 10 D 7 := by
    obtain ⟨e, he, hbe, -, -⟩ := pa_ed h hD hpos (by decide : Adj 2 7)
    rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = r2 := he.resolve_left (fun hh => hZ1p 7 (by decide) (by rw [← sem_bar_bar Z1, ← hh]; exact hbe))
    rwa [← this]
  have hne_3 : sem_bar Z4 ≠ sem_bar r2 := fun hh => by
    have hz : Z4 = r2 := by simpa [sem_bar_bar] using congrArg sem_bar hh
    exact hZ4p 2 (by decide) (hz ▸ hr2_2)
  have hW3_eq : sem_W 10 D 3 = {sem_bar Z4, sem_bar r2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hne_3]; exact hW2 3)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ4_3; exact hbr2_3
  have hr2_8 : r2 ∈ sem_W 10 D 8 := by
    obtain ⟨e, he, hbe, -, -⟩ := pa_ed h hD hpos (by decide : Adj 3 8)
    rw [hW3_eq, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = sem_bar r2 := he.resolve_left (fun hh => hZ4p 8 (by decide) (by rw [← sem_bar_bar Z4, ← hh]; exact hbe))
    simpa [this, sem_bar_bar] using hbe
  have hne_8 : sem_bar Z5 ≠ r2 := fun hh => hZ5p 3 (by decide) (by rw [← sem_bar_bar Z5, hh]; exact hbr2_3)
  have hW8_eq : sem_W 10 D 8 = {sem_bar Z5, r2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hne_8]; exact hW2 8)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ5_8; exact hr2_8
  have hbr2_6 : sem_bar r2 ∈ sem_W 10 D 6 := by
    obtain ⟨e, he, hbe, -, -⟩ := pa_ed h hD hpos (by decide : Adj 8 6)
    rw [hW8_eq, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = r2 := he.resolve_left (fun hh => hZ5p 6 (by decide) (by rw [← sem_bar_bar Z5, ← hh]; exact hbe))
    rwa [← this]
  have hne_6 : sem_bar Z1 ≠ sem_bar r2 := fun hh => by
    have hz : Z1 = r2 := by simpa [sem_bar_bar] using congrArg sem_bar hh
    exact hZ1p 2 (by decide) (hz ▸ hr2_2)
  have hW6_eq : sem_W 10 D 6 = {sem_bar Z1, sem_bar r2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hne_6]; exact hW2 6)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ1_6; exact hbr2_6
  have hr2_9 : r2 ∈ sem_W 10 D 9 := by
    obtain ⟨e, he, hbe, -, -⟩ := pa_ed h hD hpos (by decide : Adj 6 9)
    rw [hW6_eq, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = sem_bar r2 := he.resolve_left (fun hh => hZ1p 9 (by decide) (by rw [← sem_bar_bar Z1, ← hh]; exact hbe))
    simpa [this, sem_bar_bar] using hbe
  have hne_9 : sem_bar Z4 ≠ r2 := fun hh => hZ4p 3 (by decide) (by rw [← sem_bar_bar Z4, hh]; exact hbr2_3)
  have hW9_eq : sem_W 10 D 9 = {sem_bar Z4, r2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hne_9]; exact hW2 9)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ4_9; exact hr2_9
  have hne_7 : sem_bar Z5 ≠ sem_bar r2 := fun hh => by
    have hz : Z5 = r2 := by simpa [sem_bar_bar] using congrArg sem_bar hh
    exact hZ5p 2 (by decide) (hz ▸ hr2_2)
  have hW7_eq : sem_W 10 D 7 = {sem_bar Z5, sem_bar r2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hne_7]; exact hW2 7)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ5_7; exact hbr2_7
  have hM_all : ∀ v : Fin 10, merges 10 D (carrierT 10 D {v}) = ∅ := by
    intro v
    have hM2 : ∀ x : Fin 10, (sem_W 10 D x).card = 2 → merges 10 D (carrierT 10 D {x}) = ∅ := fun x hx =>
      Finset.card_eq_zero.1 (by have := hcc0 x; omega)
    fin_cases v
    · obtain ⟨_, _, _, _, _, _, _, hM0⟩ := sem_inelig_consumer sem_g10_gr h hC h0; exact hM0
    · exact hM2 1 (by rw [hW1, Finset.card_pair hZ1n.symm])
    · exact hM2 2 (by rw [hW2_eq, Finset.card_pair hne_2])
    · exact hM2 3 (by rw [hW3_eq, Finset.card_pair hne_3])
    · exact hM2 4 (by rw [hW4, Finset.card_pair hZ4n.symm])
    · exact hM2 5 (by rw [hW5, Finset.card_pair hZ5n.symm])
    · exact hM2 6 (by rw [hW6_eq, Finset.card_pair hne_6])
    · exact hM2 7 (by rw [hW7_eq, Finset.card_pair hne_7])
    · exact hM2 8 (by rw [hW8_eq, Finset.card_pair hne_8])
    · exact hM2 9 (by rw [hW9_eq, Finset.card_pair hne_9])
  have hR_supp : supp 10 D (10 + r2.1) = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun v hv => by
    have ht := sem_W_and hS hr2_2
    have hzm := (sem_zm_gate hS (hM_all v) (sem_mem_W.1 hr2_2).1 hv).1
    rw [ht] at hzm; exact Bool.noConfusion hzm
  have hp0_val := (pos_chain_or h hD hB0 hpos h0 (by decide : Adj 0 1) (fun p hp hne1 hsub => by
    rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hne1 rfl
    · exact hni 2 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hZ1_2).2.1) ▸ h0))).2.2
  have h14 : Z1.1 < Z4.1 := o1_order h hD hB0 br hbm hR0 hpos hI hp0_val hM_all
    (u := 1) (u' := 4) (u'' := 5) (a := 2) (b := 6) (c := 3) (d := 7) (Zu := Z1) (Zu' := Z4) (Zu'' := Z5) (R := r2)
    (by decide) hW1 hW4 hW5 hZ4p hZ5p hW2_eq hW6_eq hW3_eq hW7_eq
    (fun v hv0 hv1 hv4 hv5 hv2 hv6 e he => by
      fin_cases v <;> dsimp only at *
      · exact absurd rfl hv0
      · exact absurd rfl hv1
      · exact absurd rfl hv2
      · change e ∈ sem_W 10 D 3 at he; rw [hW3_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp
      · exact absurd rfl hv4
      · exact absurd rfl hv5
      · exact absurd rfl hv6
      · change e ∈ sem_W 10 D 7 at he; rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp
      · change e ∈ sem_W 10 D 8 at he; rw [hW8_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp
      · change e ∈ sem_W 10 D 9 at he; rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp)
    hR_supp
  have h41 : Z4.1 < Z1.1 := o1_order h hD hB0 br hbm hR0 hpos hI hp0_val hM_all
    (u := 4) (u' := 1) (u'' := 5) (a := 3) (b := 9) (c := 2) (d := 8) (Zu := Z4) (Zu' := Z1) (Zu'' := Z5) (R := sem_bar r2)
    (by decide) hW4 hW1 hW5 hZ1p hZ5p hW3_eq (by simpa [sem_bar_bar] using hW9_eq)
    (by simpa [sem_bar_bar] using hW2_eq) (by simpa [sem_bar_bar] using hW8_eq)
    (fun v hv0 hv4 hv1 hv5 hv3 hv9 e he => by
      fin_cases v <;> dsimp only at *
      · exact absurd rfl hv0
      · exact absurd rfl hv1
      · change e ∈ sem_W 10 D 2 at he; rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp [sem_bar_bar]
      · exact absurd rfl hv3
      · exact absurd rfl hv4
      · exact absurd rfl hv5
      · change e ∈ sem_W 10 D 6 at he; rw [hW6_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp [sem_bar_bar]
      · change e ∈ sem_W 10 D 7 at he; rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp [sem_bar_bar]
      · change e ∈ sem_W 10 D 8 at he; rw [hW8_eq, Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl <;> simp [sem_bar_bar]
      · exact absurd rfl hv9)
    hR_supp
  omega

theorem elim_O2 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h9 : totalSurplus 10 D ≤ 9)
    (hI : ineligSet 10 D = {0, 2}) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hel := inelig_card_add 10 D
  have hts := totalSurplus_split 10 D
  have hI2 : (ineligSet 10 D).card = 2 := by rw [hI]; decide
  have hE8 : (eligSet 10 D).card = 8 := by omega
  have hBp_ge := elig_le_Bplus hS br hbp
  have hm : ∀ v : Fin 10, v ∈ ({0, 2} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 2} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  by_cases hR0 : Bplus 10 D ≤ 8
  · have hres : residualUnits 10 D br = ∅ := Finset.card_eq_zero.1 (by have := card_residual hS br hbp; omega)
    have hW2 : ∀ x : Fin 10, (sem_W 10 D x).card ≤ 2 := fun x => by
      have h1 := cc_le h hD br hbp x; unfold ru at h1; rw [hres, Finset.filter_empty, Finset.card_empty] at h1; omega
    exact pa_m1_gen h hD hpos 3 4 8 2 0 1 (hm 2 (by decide)) (hm 0 (by decide))
      (hn 3 (by decide)) (hn 4 (by decide)) (hn 8 (by decide)) (by decide) (hW2 3) (hW2 4)
  · have hB0 : Bzero 10 D = 0 := by omega
    have hR1 : (residualUnits 10 D br).card = 1 := by have := card_residual hS br hbp; omega
    obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
    have h1_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 2 (by decide)) (u := 1) (v := 6) (by decide)
    have hru1 : ru D br 1 = {u0} := by
      have hcc := cc_le h hD br hbp 1
      have hsub1 : ru D br 1 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
      exact Finset.eq_of_subset_of_card_le hsub1 (by rw [Finset.card_singleton]; omega)
    have hle2 : ∀ x : Fin 10, x ≠ 1 → (sem_W 10 D x).card ≤ 2 := fun x hx1 => by
      have hnot := w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 2 (by decide))
        (x := 1) (v := 6) (by decide) hru1 (petersen_w3_bad_eq 1 0 2 x (by decide) (by decide) (by decide) hx1)
      have hrux : ru D br x = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun u hu =>
        hnot ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
      have := cc_le h hD br hbp x; rw [hrux, Finset.card_empty] at this; omega
    exact pa_m1_gen h hD hpos 3 4 8 2 0 1 (hm 2 (by decide)) (hm 0 (by decide))
      (hn 3 (by decide)) (hn 4 (by decide)) (hn 8 (by decide)) (by decide) (hle2 3 (by decide)) (hle2 4 (by decide))

theorem elim_O3b {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h9 : totalSurplus 10 D ≤ 9)
    (hI : ineligSet 10 D = {0, 2, 8}) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hel := inelig_card_add 10 D
  have hts := totalSurplus_split 10 D
  have hI3 : (ineligSet 10 D).card = 3 := by rw [hI]; decide
  have hE7 : (eligSet 10 D).card = 7 := by omega
  have hBp_ge := elig_le_Bplus hS br hbp
  have hm : ∀ v : Fin 10, v ∈ ({0, 2, 8} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 2, 8} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 2, 8} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hI ▸ sem_mem_inelig.2 hc)
  have h1_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 2 (by decide)) (u := 1) (v := 6) (by decide)
  have h3_3 := two_in_deg3 h hD hpos (hm 2 (by decide)) (hm 8 (by decide)) (u := 3) (v := 4) (by decide)
  have h5_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 8 (by decide)) (u := 5) (v := 7) (by decide)
  by_cases hB7 : Bplus 10 D ≤ 7
  · have hres : residualUnits 10 D br = ∅ := Finset.card_eq_zero.1 (by have := card_residual hS br hbp; omega)
    have h1 := cc_le h hD br hbp 1; unfold ru at h1; rw [hres, Finset.filter_empty, Finset.card_empty] at h1; omega
  · by_cases hB8 : Bplus 10 D = 8
    · have hR1 : (residualUnits 10 D br).card = 1 := by have := card_residual hS br hbp; omega
      obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
      have hru1 : ru D br 1 = {u0} := Finset.eq_of_subset_of_card_le
        (by rw [← hRu0]; exact Finset.filter_subset _ _) (by have := cc_le h hD br hbp 1; rw [Finset.card_singleton]; omega)
      have hru3 : ru D br 3 = {u0} := Finset.eq_of_subset_of_card_le
        (by rw [← hRu0]; exact Finset.filter_subset _ _) (by have := cc_le h hD br hbp 3; rw [Finset.card_singleton]; omega)
      have hres13 : ∀ u' ∈ residualUnits 10 D br, (1 : Fin 10) ∈ supp 10 D u'.1 → (3 : Fin 10) ∈ supp 10 D u'.1 :=
        fun u' hu' _ => (mem_ru.1 (hru3 ▸ (hRu0 ▸ hu'))).2
      have hw13 : (1 : Fin 10) ∈ supp 10 D u0.1 ∧ (3 : Fin 10) ∈ supp 10 D u0.1 :=
        ⟨(mem_ru.1 (hru1 ▸ Finset.mem_singleton_self u0)).2, (mem_ru.1 (hru3 ▸ Finset.mem_singleton_self u0)).2⟩
      have hp0_3 := mem_W_of_pos hpos (hm 0 (by decide))
        (pe_co_g10 h hD br hbp hpos (hm 0 (by decide)) (helig 1 (by decide)) hres13 hw13 (q := 5) (by decide))
      have hp2_3 := as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 3)
      have hp8_3 := as_mem hpos (hm 8 (by decide)) (by decide : Adj 8 3)
      obtain ⟨e4, he4, -, hf4, -⟩ := pa_ed h hD hpos (by decide : Adj 3 4)
      have h4 := pa_card4 hp0_3 hp2_3 hp8_3 he4
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 2 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 8 (by decide)) e) (by decide))
        (fun e => hn 4 (by decide) (hf4 _ (hm 0 (by decide)) e.symm ▸ hm 0 (by decide)))
        (fun e => absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 8 (by decide)) e) (by decide))
        (fun e => hn 4 (by decide) (hf4 _ (hm 2 (by decide)) e.symm ▸ hm 2 (by decide)))
        (fun e => hn 4 (by decide) (hf4 _ (hm 8 (by decide)) e.symm ▸ hm 8 (by decide)))
      have hc := cc_le h hD br hbp 3; rw [hru3, Finset.card_singleton] at hc; omega
    · have hB0 : Bzero 10 D = 0 := by omega
      have hR2 : (residualUnits 10 D br).card = 2 := by have := card_residual hS br hbp; omega
      rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 1 3 0 2 6 2 8 4
          (hm 0 (by decide)) (hm 2 (by decide)) (hm 2 (by decide)) (hm 8 (by decide))
          (by decide) (by decide) (by decide) (by decide) with ⟨hru1, hru3⟩ | hle2
      · exact shared_w3_eq h hD hB0 br hbp hpos 1 3 2 0 8 4 5 5
          (helig 1 (by decide)) (helig 3 (by decide)) (hm 2 (by decide)) (hm 0 (by decide)) (hm 8 (by decide))
          (hn 4 (by decide)) (by decide) (by rw [hru1]; exact Finset.card_pos.1 (by omega))
          (by rw [hru1, hru3]) (by rw [hru3, hR2])
      · have := hle2 5 (by decide) (by decide); omega

def o4I : Finset (Fin 10) := {0, 2, 8, 9}
def o4A : Finset (Fin 10) := {1, 3, 4, 5, 6, 7}

theorem o4_vert_info : ∀ v ∈ o4A,
    ∃ i1 ∈ o4I, ∃ i2 ∈ o4I, ∃ ve ∈ o4A,
      i1 ≠ i2 ∧ hc_adjB i1 v = true ∧ hc_adjB i2 v = true ∧ hc_adjB v ve = true ∧ ve ≠ i1 ∧ ve ≠ i2 := by
  decide +kernel

theorem o4_diff_i : ∀ a ∈ o4A, ∀ b ∈ o4A, a ≠ b →
    ∃ i ∈ o4I, ∃ q : Fin 10,
      hc_adjB i a = true ∧ hc_adjB i b = false ∧ hc_adjB i q = true ∧ a ≠ q ∧ hc_adjB b q = false := by
  decide +kernel

def o4_i1 (v : Fin 10) : Fin 10 :=
  match v.val with | 1 => 0 | 3 => 2 | 4 => 0 | 5 => 0 | 6 => 8 | _ => 2

def o4_i2 (v : Fin 10) : Fin 10 :=
  match v.val with | 1 => 2 | 3 => 8 | 4 => 9 | 5 => 8 | 6 => 9 | _ => 9

def o4_ve (v : Fin 10) : Fin 10 :=
  match v.val with | 1 => 6 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 1 | _ => 5

def o4_findQ (i a b : Fin 10) : Fin 10 :=
  ((List.finRange 10).find? (fun q => hc_adjB i q && (a != q) && !hc_adjB b q)).getD 0

def o4_disj (a b : Fin 10) : Bool :=
  o4_i1 a != o4_i1 b && o4_i1 a != o4_i2 b && o4_i2 a != o4_i1 b && o4_i2 a != o4_i2 b

def o4_sh_i0 (a b : Fin 10) : Fin 10 :=
  if o4_i1 a == o4_i1 b || o4_i1 a == o4_i2 b then o4_i1 a else o4_i2 a

def o4_sh_ia (a b : Fin 10) : Fin 10 :=
  if o4_i1 a == o4_i1 b || o4_i1 a == o4_i2 b then o4_i2 a else o4_i1 a

def o4_sh_ib (a b : Fin 10) : Fin 10 :=
  if o4_i1 b == o4_sh_i0 a b then o4_i2 b else o4_i1 b

theorem o4_disj_ok : ∀ a ∈ o4A, ∀ b ∈ o4A, a ≠ b → o4_disj a b = true →
    let a1 := o4_i1 a; let a2 := o4_i2 a; let b1 := o4_i1 b; let b2 := o4_i2 b
    let qa1 := o4_findQ a1 a b; let qa2 := o4_findQ a2 a b; let vb := o4_ve b
    a1 ∈ o4I ∧ a2 ∈ o4I ∧ b1 ∈ o4I ∧ b2 ∈ o4I ∧ vb ∈ o4A ∧
    a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
    hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
    hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
    hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
    hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true := by
  decide +kernel

theorem o4_share_ok : ∀ a ∈ o4A, ∀ b ∈ o4A, a ≠ b → o4_disj a b = false →
    let i0 := o4_sh_i0 a b; let ia := o4_sh_ia a b; let ib := o4_sh_ib a b
    let vb := o4_ve b; let qa := o4_findQ ia a b; let qb := o4_findQ ib b a
    i0 ∈ o4I ∧ ia ∈ o4I ∧ ib ∈ o4I ∧ vb ∈ o4A ∧
    a ≠ b ∧ i0 ≠ ia ∧ i0 ≠ ib ∧ ia ≠ ib ∧
    hc_adjB i0 a = true ∧ hc_adjB ia a = true ∧
    hc_adjB i0 b = true ∧ hc_adjB ib b = true ∧ hc_adjB b vb = true ∧
    hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB b qa = false ∧
    hc_adjB ib qb = true ∧ b ≠ qb ∧ hc_adjB a qb = false ∧ hc_adjB ib a = false := by
  decide +kernel

theorem o4_opp_ok : ∀ a ∈ o4A,
    let c := o4_ve a
    let a1 := o4_i1 c; let a2 := o4_i2 c; let b1 := o4_i1 a; let b2 := o4_i2 a
    let qa1 := o4_findQ a1 c a; let qa2 := o4_findQ a2 c a; let va := o4_ve a
    c ∈ o4A ∧ a1 ∈ o4I ∧ a2 ∈ o4I ∧ b1 ∈ o4I ∧ b2 ∈ o4I ∧ va ∈ o4A ∧
    c ≠ a ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
    hc_adjB a1 c = true ∧ hc_adjB a2 c = true ∧
    hc_adjB a1 qa1 = true ∧ c ≠ qa1 ∧ hc_adjB a qa1 = false ∧
    hc_adjB a2 qa2 = true ∧ c ≠ qa2 ∧ hc_adjB a qa2 = false ∧
    hc_adjB b1 a = true ∧ hc_adjB b2 a = true ∧ hc_adjB a va = true := by
  decide +kernel

theorem o4_not_mem_I : ∀ v ∈ o4A, v ∉ o4I := by decide +kernel

theorem elim_O4 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h9 : totalSurplus 10 D ≤ 9)
    (hI : ineligSet 10 D = {0, 2, 8, 9}) : False := by
  classical
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hel := inelig_card_add 10 D
  have hts := totalSurplus_split 10 D
  have hI4 : (ineligSet 10 D).card = 4 := by rw [hI]; decide
  have hE6 : (eligSet 10 D).card = 6 := by omega
  have hBp_ge := elig_le_Bplus hS br hbp
  have hm : ∀ v : Fin 10, v ∈ o4I → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∈ o4A → v ∉ ineligSet 10 D := fun v hv => hI ▸ o4_not_mem_I v hv
  have helig : ∀ v : Fin 10, v ∈ o4A → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hn v hv (sem_mem_inelig.2 hc)
  have hW3 : ∀ v ∈ o4A, 3 ≤ (sem_W 10 D v).card := fun v hv => by
    obtain ⟨i1, hi1, i2, hi2, ve, -, h12, g1, g2, gv, hve1, hve2⟩ := o4_vert_info v hv
    exact two_in_deg3 h hD hpos (hm i1 hi1) (hm i2 hi2) ⟨h12, g1, g2, gv, hve1, hve2⟩
  have hru_ne : ∀ v ∈ o4A, (ru D br v).Nonempty := fun v hv =>
    Finset.card_pos.1 (by have := cc_le h hD br hbp v; have := hW3 v hv; omega)
  have hru1_ne : ∀ a ∈ o4A, ∀ b ∈ o4A, a ≠ b → ru D br a ⊆ ru D br b → (ru D br b).card ≤ 1 → False := by
    intro a ha b hb hab hsub hble
    obtain ⟨u, hu⟩ := hru_ne a ha
    have hres : ∀ u' ∈ residualUnits 10 D br, a ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
      fun u' hu' ha' => (mem_ru.1 (hsub (mem_ru.2 ⟨hu', ha'⟩))).2
    have hw : a ∈ supp 10 D u.1 ∧ b ∈ supp 10 D u.1 := ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub hu)).2⟩
    obtain ⟨i, hi, q, gia, gib, giq, haq, hbq⟩ := o4_diff_i a ha b hb hab
    have hpi := mem_W_of_pos hpos (hm i hi)
      (pe_co_g10 h hD br hbp hpos (hm i hi) (helig a ha) hres hw ⟨petersen_deg3 a, gia, giq, hab, haq, hbq⟩)
    obtain ⟨b1, hb1, b2, hb2, vb, hvbA, hb12, gb1, gb2, gvb, -, -⟩ := o4_vert_info b hb
    have hpb1 := as_mem hpos (hm b1 hb1) ((hc_adjB_iff _ _).1 gb1)
    have hpb2 := as_mem hpos (hm b2 hb2) ((hc_adjB_iff _ _).1 gb2)
    obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
    have hib1 : i ≠ b1 := fun hh => by rw [hh, gb1] at gib; exact Bool.noConfusion gib
    have hib2 : i ≠ b2 := fun hh => by rw [hh, gb2] at gib; exact Bool.noConfusion gib
    have h4 := pa_card4 hpi hpb1 hpb2 hev
      (fun e => hib1 (hpos.2 _ (hm i hi) _ (hm b1 hb1) e))
      (fun e => hib2 (hpos.2 _ (hm i hi) _ (hm b2 hb2) e))
      (fun e => hn vb hvbA (hfv _ (hm i hi) e.symm ▸ hm i hi))
      (fun e => hb12 (hpos.2 _ (hm b1 hb1) _ (hm b2 hb2) e))
      (fun e => hn vb hvbA (hfv _ (hm b1 hb1) e.symm ▸ hm b1 hb1))
      (fun e => hn vb hvbA (hfv _ (hm b2 hb2) e.symm ▸ hm b2 hb2))
    have := cc_le h hD br hbp b; omega
  have hru2_ne : Bzero 10 D = 0 → ∀ a ∈ o4A, ∀ b ∈ o4A, a ≠ b → ru D br a = ru D br b → (ru D br b).card ≤ 2 → False := by
    intro hB0 a ha b hb hab heq hble
    cases hd : o4_disj a b
    · obtain ⟨hi0, hia, hib, hvbA, hab', h0a, h0b, habi, g0a, gaa, g0b, gbb, gvb, gqa, haqa, gbqa, gqb, hbqb, gaqb, gnba⟩ :=
        o4_share_ok a ha b hb hab hd
      exact shared_w3_eq h hD hB0 br hbp hpos a b (o4_sh_i0 a b) (o4_sh_ia a b) (o4_sh_ib a b) (o4_ve b)
        (o4_findQ (o4_sh_ia a b) a b) (o4_findQ (o4_sh_ib a b) b a)
        (helig a ha) (helig b hb) (hm _ hi0) (hm _ hia) (hm _ hib) (hn _ hvbA)
        ⟨hab', h0a, h0b, habi, petersen_deg3 a, petersen_deg3 b, g0a, gaa, g0b, gbb, gvb, gqa, haqa, gbqa, gqb, hbqb, gaqb, gnba⟩
        (hru_ne a ha) heq hble
    · obtain ⟨ha1, ha2, hb1, hb2, hvbA, hab', ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12,
        ga1, ga2, gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩ := o4_disj_ok a ha b hb hab hd
      exact pe_co_blow5 h hD br hbp hpos a b (o4_i1 a) (o4_i2 a) (o4_findQ (o4_i1 a) a b) (o4_findQ (o4_i2 a) a b)
        (o4_i1 b) (o4_i2 b) (o4_ve b)
        (helig a ha) (hm _ ha1) (hm _ ha2) (hm _ hb1) (hm _ hb2) (hn _ hvbA)
        ⟨hab', ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, petersen_deg3 a, ga1, ga2, gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩
        (Finset.card_pos.2 (hru_ne a ha)) (by rw [heq]) hble
  by_cases hB6 : Bplus 10 D ≤ 6
  · have hres : residualUnits 10 D br = ∅ := Finset.card_eq_zero.1 (by have := card_residual hS br hbp; omega)
    obtain ⟨u, hu⟩ := hru_ne 1 (by decide); exact Finset.notMem_empty u (hres ▸ (mem_ru.1 hu).1)
  · by_cases hB7 : Bplus 10 D = 7
    · have hR1 : (residualUnits 10 D br).card = 1 := by have := card_residual hS br hbp; omega
      have hru_eq : ∀ v ∈ o4A, ru D br v = residualUnits 10 D br := fun v hv =>
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
          (by rw [hR1]; exact Finset.card_pos.2 (hru_ne v hv))
      exact hru1_ne 1 (by decide) 3 (by decide) (by decide)
        (by rw [hru_eq 1 (by decide), hru_eq 3 (by decide)]) (by rw [hru_eq 3 (by decide), hR1])
    · by_cases hB8 : Bplus 10 D = 8
      · have hR2 : (residualUnits 10 D br).card = 2 := by have := card_residual hS br hbp; omega
        obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
        have hS1_le : ∀ u0 : Σ _ : ℕ, ℕ, (o4A.filter (fun v => ru D br v = {u0})).card ≤ 1 := fun u0 => by
          by_contra hc
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (o4A.filter (fun v => ru D br v = {u0})).card)
          rw [Finset.mem_filter] at ha hb
          exact hru1_ne a ha.1 b hb.1 hab (by rw [ha.2, hb.2]) (by rw [hb.2, Finset.card_singleton])
        have hpart : o4A ⊆ o4A.filter (fun v => ru D br v = {u1}) ∪ o4A.filter (fun v => ru D br v = {u2}) ∪
            o4A.filter (fun v => ru D br v = residualUnits 10 D br) := by
          intro v hv
          have hsub : ru D br v ⊆ {u1, u2} := hReq ▸ Finset.filter_subset _ _
          have hne := hru_ne v hv
          by_cases h1 : u1 ∈ ru D br v <;> by_cases h2 : u2 ∈ ru D br v
          · have : ru D br v = residualUnits 10 D br := by
              rw [hReq]; exact Finset.Subset.antisymm hsub (fun x hx => by
                rw [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl; exact h1; exact h2)
            simp [hv, this]
          · have : ru D br v = {u1} := Finset.Subset.antisymm (fun x hx => by
              have := hsub hx; rw [Finset.mem_insert, Finset.mem_singleton] at this
              exact Finset.mem_singleton.2 (this.resolve_right (fun hx2 => h2 (hx2 ▸ hx))))
              (Finset.singleton_subset_iff.2 h1)
            simp [hv, this]
          · have : ru D br v = {u2} := Finset.Subset.antisymm (fun x hx => by
              have := hsub hx; rw [Finset.mem_insert, Finset.mem_singleton] at this
              exact Finset.mem_singleton.2 (this.resolve_left (fun hx1 => h1 (hx1 ▸ hx))))
              (Finset.singleton_subset_iff.2 h2)
            simp [hv, this]
          · obtain ⟨u, hu⟩ := hne
            have := hsub hu; rw [Finset.mem_insert, Finset.mem_singleton] at this
            exact (this.elim (fun e => h1 (e ▸ hu)) (fun e => h2 (e ▸ hu))).elim
        have hcA : o4A.card = 6 := by decide
        have hc3 : 4 ≤ (o4A.filter (fun v => ru D br v = residualUnits 10 D br)).card := by
          have h1 := Finset.card_le_card hpart
          have h2 := Finset.card_union_le (o4A.filter (fun v => ru D br v = {u1}) ∪ o4A.filter (fun v => ru D br v = {u2}))
            (o4A.filter (fun v => ru D br v = residualUnits 10 D br))
          have h3 := Finset.card_union_le (o4A.filter (fun v => ru D br v = {u1})) (o4A.filter (fun v => ru D br v = {u2}))
          have := hS1_le u1; have := hS1_le u2; omega
        set S := o4A.filter (fun v => ru D br v = residualUnits 10 D br)
        have hpair : ((1 : Fin 10) ∈ S ∧ (6 : Fin 10) ∈ S) ∨ ((3 : Fin 10) ∈ S ∧ (4 : Fin 10) ∈ S) ∨
            ((5 : Fin 10) ∈ S ∧ (7 : Fin 10) ∈ S) := by
          by_contra hc; push Not at hc
          have hle1 : (S ∩ {1, 6}).card ≤ 1 := by
            by_contra hgt; obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < (S ∩ {1, 6}).card)
            rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
            · exact hxy rfl
            · exact hc.1 hx.1 hy.1
            · exact hc.1 hy.1 hx.1
            · exact hxy rfl
          have hle2 : (S ∩ {3, 4}).card ≤ 1 := by
            by_contra hgt; obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < (S ∩ {3, 4}).card)
            rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
            · exact hxy rfl
            · exact hc.2.1 hx.1 hy.1
            · exact hc.2.1 hy.1 hx.1
            · exact hxy rfl
          have hle3 : (S ∩ {5, 7}).card ≤ 1 := by
            by_contra hgt; obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < (S ∩ {5, 7}).card)
            rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
            · exact hxy rfl
            · exact hc.2.2 hx.1 hy.1
            · exact hc.2.2 hy.1 hx.1
            · exact hxy rfl
          have hcov : S ⊆ (S ∩ {1, 6}) ∪ (S ∩ {3, 4}) ∪ (S ∩ {5, 7}) := fun v hv => by
            have hvA : v ∈ o4A := (Finset.mem_filter.1 hv).1
            simp only [o4A, Finset.mem_insert, Finset.mem_singleton] at hvA
            rcases hvA with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, by decide⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, by decide⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, by decide⟩))
            · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, by decide⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, by decide⟩))
            · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, by decide⟩)
          have h1 := Finset.card_le_card hcov
          have h2 := Finset.card_union_le ((S ∩ {1, 6}) ∪ (S ∩ {3, 4})) (S ∩ {5, 7})
          have h3 := Finset.card_union_le (S ∩ {1, 6}) (S ∩ {3, 4})
          omega
        rcases hpair with ⟨h1, h6⟩ | ⟨h3, h4⟩ | ⟨h5, h7⟩
        · rw [Finset.mem_filter] at h1 h6
          exact pe_co_blow5 h hD br hbp hpos 1 6 0 2 4 3 8 9 1
            (helig 1 (by decide)) (hm 0 (by decide)) (hm 2 (by decide)) (hm 8 (by decide)) (hm 9 (by decide))
            (hn 1 (by decide)) (by decide) (by rw [h1.2, hR2]; omega) (by rw [h1.2, h6.2]) (by rw [h6.2, hR2])
        · rw [Finset.mem_filter] at h3 h4
          exact pe_co_blow5 h hD br hbp hpos 3 4 2 8 1 5 0 9 3
            (helig 3 (by decide)) (hm 2 (by decide)) (hm 8 (by decide)) (hm 0 (by decide)) (hm 9 (by decide))
            (hn 3 (by decide)) (by decide) (by rw [h3.2, hR2]; omega) (by rw [h3.2, h4.2]) (by rw [h4.2, hR2])
        · rw [Finset.mem_filter] at h5 h7
          exact pe_co_blow5 h hD br hbp hpos 5 7 0 8 1 3 2 9 5
            (helig 5 (by decide)) (hm 0 (by decide)) (hm 8 (by decide)) (hm 2 (by decide)) (hm 9 (by decide))
            (hn 5 (by decide)) (by decide) (by rw [h5.2, hR2]; omega) (by rw [h5.2, h7.2]) (by rw [h7.2, hR2])
      · have hB0 : Bzero 10 D = 0 := by omega
        have hR3 : (residualUnits 10 D br).card = 3 := by have := card_residual hS br hbp; omega
        have hno1 : ∀ v ∈ o4A, (ru D br v).card ≠ 1 := by
          intro v hv hvc
          obtain ⟨u0, hu0⟩ := Finset.card_eq_one.1 hvc
          obtain ⟨i1, hi1, i2, hi2, ve, -, h12, g1, g2, gv, hve1, hve2⟩ := o4_vert_info v hv
          have hu0_in : u0 ∈ residualUnits 10 D br := (mem_ru.1 (hu0 ▸ Finset.mem_singleton_self u0)).1
          let T := ((residualUnits 10 D br).erase u0).powerset.filter Finset.Nonempty
          have hmap : ∀ w ∈ o4A.erase v, ru D br w ∈ T := fun w hw => by
            rw [Finset.mem_erase] at hw
            have hnot := w3_ru_one_not_mem h hD hB0 br hbm hpos (hm i1 hi1) (hm i2 hi2)
              ⟨petersen_deg3 v, h12, g1, g2, gv, hve1, hve2⟩ hu0
              (petersen_w3_bad_eq v i1 i2 w h12 g1 g2 hw.1)
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨fun u hu => Finset.mem_erase.2 ⟨fun heq => hnot (heq ▸ (mem_ru.1 hu).2), (mem_ru.1 hu).1⟩, hru_ne w hw.2⟩
          have hpigeon : ∀ (s : Finset (Fin 10)) (t : Finset (Finset (Σ _ : ℕ, ℕ)))
              (f : Fin 10 → Finset (Σ _ : ℕ, ℕ)),
              t.card < s.card → (∀ x ∈ s, f x ∈ t) → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
            intro s t f hlt hm'
            by_contra hc; push Not at hc
            have hinj : Set.InjOn f s := fun x hx y hy hxy => Classical.byContradiction fun hne => hc x hx y hy hne hxy
            have hle := Finset.card_le_card (Finset.image_subset_iff.2 hm')
            rw [Finset.card_image_of_injOn hinj] at hle; omega
          have hTcard : T.card ≤ 3 := by
            have h1 : ((residualUnits 10 D br).erase u0).card = 2 := by rw [Finset.card_erase_of_mem hu0_in, hR3]
            have h2 : (((residualUnits 10 D br).erase u0).powerset).card = 4 := by rw [Finset.card_powerset, h1]; rfl
            have hemp : ∅ ∈ ((residualUnits 10 D br).erase u0).powerset := Finset.empty_mem_powerset _
            have hsub : T ⊆ (((residualUnits 10 D br).erase u0).powerset).erase ∅ := fun s hs => by
              rw [Finset.mem_filter] at hs; exact Finset.mem_erase.2 ⟨Finset.nonempty_iff_ne_empty.1 hs.2, hs.1⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hemp, h2] at this; omega
          have hAcard : (o4A.erase v).card = 5 := by rw [Finset.card_erase_of_mem hv]; decide
          obtain ⟨a, ha, b, hb, hab, heq⟩ := hpigeon (o4A.erase v) T (ru D br) (by omega) hmap
          have hble : (ru D br b).card ≤ 2 := by
            have hmem := hmap b hb; rw [Finset.mem_filter, Finset.mem_powerset] at hmem
            have := Finset.card_le_card hmem.1; rw [Finset.card_erase_of_mem hu0_in, hR3] at this; omega
          exact hru2_ne hB0 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab heq hble
        let S2 := o4A.filter (fun v => (ru D br v).card = 2)
        let T2 := (residualUnits 10 D br).powersetCard 2
        have hT2card : T2.card = 3 := by rw [Finset.card_powersetCard, hR3]; decide
        have hS2le : S2.card ≤ 3 := by
          by_contra hc
          have hmap : ∀ v ∈ S2, ru D br v ∈ T2 := fun v hv => by
            rw [Finset.mem_filter] at hv; exact Finset.mem_powersetCard.2 ⟨Finset.filter_subset _ _, hv.2⟩
          have hpigeon2 : ∀ (s : Finset (Fin 10)) (t : Finset (Finset (Σ _ : ℕ, ℕ)))
              (f : Fin 10 → Finset (Σ _ : ℕ, ℕ)),
              t.card < s.card → (∀ x ∈ s, f x ∈ t) → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
            intro s t f hlt hm'
            by_contra hc'; push Not at hc'
            have hinj : Set.InjOn f s := fun x hx y hy hxy => Classical.byContradiction fun hne => hc' x hx y hy hne hxy
            have hle := Finset.card_le_card (Finset.image_subset_iff.2 hm')
            rw [Finset.card_image_of_injOn hinj] at hle; omega
          obtain ⟨a, ha, b, hb, hab, heq⟩ := hpigeon2 S2 T2 (ru D br) (by omega) hmap
          rw [Finset.mem_filter] at ha hb
          exact hru2_ne hB0 a ha.1 b hb.1 hab heq (by omega)
        let S3 := o4A.filter (fun v => ru D br v = residualUnits 10 D br)
        have hS3ge : 2 ≤ S3.card := by
          have hpart : o4A ⊆ S2 ∪ S3 := fun v hv => by
            have hpos1 := Finset.card_pos.2 (hru_ne v hv)
            have hne1 := hno1 v hv
            have hle3 : (ru D br v).card ≤ 3 := by rw [← hR3]; exact Finset.card_le_card (Finset.filter_subset _ _)
            by_cases hc2 : (ru D br v).card = 2
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hv, hc2⟩)
            · have hc3 : (ru D br v).card = 3 := by omega
              exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hv,
                Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR3, hc3])⟩)
          have h1 := Finset.card_le_card hpart
          have h2 := Finset.card_union_le S2 S3
          have hcA : o4A.card = 6 := by decide
          omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S3.card)
        rw [Finset.mem_filter] at ha hb
        let c := o4_ve a
        let a1 := o4_i1 c; let a2 := o4_i2 c; let b1 := o4_i1 a; let b2 := o4_i2 a
        let qa1 := o4_findQ a1 c a; let qa2 := o4_findQ a2 c a; let va := o4_ve a
        obtain ⟨hcA, ha1, ha2, hb1, hb2, hvaA,
          hca, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, gca1, gca2, gqa1, hcqa1, haqa1, gqa2, hcqa2, haqa2,
          gb1a, gb2a, gvaa⟩ := o4_opp_ok a ha.1
        obtain ⟨uc, huc⟩ := hru_ne c hcA
        have hresc : ∀ u' ∈ residualUnits 10 D br, c ∈ supp 10 D u'.1 → a ∈ supp 10 D u'.1 :=
          fun u' hu' _ => (mem_ru.1 (ha.2 ▸ hu')).2
        have hwc : c ∈ supp 10 D uc.1 ∧ a ∈ supp 10 D uc.1 :=
          ⟨(mem_ru.1 huc).2, (mem_ru.1 (ha.2 ▸ (mem_ru.1 huc).1)).2⟩
        have hpa1 := mem_W_of_pos hpos (hm a1 ha1)
          (pe_co_g10 h hD br hbp hpos (hm a1 ha1) (helig c hcA) hresc hwc ⟨petersen_deg3 c, gca1, gqa1, hca, hcqa1, haqa1⟩)
        have hpa2 := mem_W_of_pos hpos (hm a2 ha2)
          (pe_co_g10 h hD br hbp hpos (hm a2 ha2) (helig c hcA) hresc hwc ⟨petersen_deg3 c, gca2, gqa2, hca, hcqa2, haqa2⟩)
        have hpb1 := as_mem hpos (hm b1 hb1) ((hc_adjB_iff _ _).1 gb1a)
        have hpb2 := as_mem hpos (hm b2 hb2) ((hc_adjB_iff _ _).1 gb2a)
        obtain ⟨eva, heva, hbeva, hfva, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvaa)
        have hWa_le5 : (sem_W 10 D a).card ≤ 5 := by have := cc_le h hD br hbp a; rw [ha.2, hR3] at this; omega
        have hWa := pa_five hpb1 hpb2 hpa1 hpa2 heva
          (fun e => hb12 (hpos.2 _ (hm b1 hb1) _ (hm b2 hb2) e))
          (fun e => ha1b1.symm (hpos.2 _ (hm b1 hb1) _ (hm a1 ha1) e))
          (fun e => ha2b1.symm (hpos.2 _ (hm b1 hb1) _ (hm a2 ha2) e))
          (fun e => hn va hvaA (by rw [show va = b1 from hfva _ (hm b1 hb1) e.symm]; exact hm b1 hb1))
          (fun e => ha1b2.symm (hpos.2 _ (hm b2 hb2) _ (hm a1 ha1) e))
          (fun e => ha2b2.symm (hpos.2 _ (hm b2 hb2) _ (hm a2 ha2) e))
          (fun e => hn va hvaA (by rw [show va = b2 from hfva _ (hm b2 hb2) e.symm]; exact hm b2 hb2))
          (fun e => ha12 (hpos.2 _ (hm a1 ha1) _ (hm a2 ha2) e))
          (fun e => hn va hvaA (by rw [show va = a1 from hfva _ (hm a1 ha1) e.symm]; exact hm a1 ha1))
          (fun e => hn va hvaA (by rw [show va = a2 from hfva _ (hm a2 ha2) e.symm]; exact hm a2 ha2))
          hWa_le5
        have hfull_b1 := full_g10 h hD hB0 hpos (hm b1 hb1) ((hc_adjB_iff _ _).1 gb1a) (fun p hp hne1 hsub' => by
          rcases hWa p hp with rfl | rfl | rfl | rfl | rfl
          · exact hne1 rfl
          · exact hb12.symm (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm b2 hb2))))
          · exact ha1b1 (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm a1 ha1))))
          · exact ha2b1 (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm a2 ha2))))
          · exact hn va hvaA (by rw [show va = b1 from Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbeva).2.1)]; exact hm b1 hb1))
        have hfull_b2 := full_g10 h hD hB0 hpos (hm b2 hb2) ((hc_adjB_iff _ _).1 gb2a) (fun p hp hne1 hsub' => by
          rcases hWa p hp with rfl | rfl | rfl | rfl | rfl
          · exact hb12 (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm b1 hb1))))
          · exact hne1 rfl
          · exact ha1b2 (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm a1 ha1))))
          · exact ha2b2 (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm a2 ha2))))
          · exact hn va hvaA (by rw [show va = b2 from Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbeva).2.1)]; exact hm b2 hb2))
        obtain ⟨i, hi, q, gia, gib, giq, haq, hbq⟩ := o4_diff_i a ha.1 b hb.1 hab
        obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (residualUnits 10 D br).card)
        have hresab : ∀ u' ∈ residualUnits 10 D br, a ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
          fun u' hu' _ => (mem_ru.1 (hb.2 ▸ hu')).2
        have hwab : a ∈ supp 10 D u.1 ∧ b ∈ supp 10 D u.1 :=
          ⟨(mem_ru.1 (ha.2 ▸ hu)).2, (mem_ru.1 (hb.2 ▸ hu)).2⟩
        have hb_in_pi := pe_co_g10 h hD br hbp hpos (hm i hi) (helig a ha.1) hresab hwab ⟨petersen_deg3 a, gia, giq, hab, haq, hbq⟩
        have hi_eq : i = b1 ∨ i = b2 := by
          have hmem : i ∈ o4I := hi
          have h4 : o4I = {a1, a2, b1, b2} := by
            symm; refine Finset.eq_of_subset_of_card_le (fun z hz => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl | rfl <;> assumption) ?_
            have hnm1 : a1 ∉ ({a2, b1, b2} : Finset (Fin 10)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ha12, ha1b1, ha1b2⟩
            have hnm2 : a2 ∉ ({b1, b2} : Finset (Fin 10)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ha2b1, ha2b2⟩
            rw [Finset.card_insert_of_notMem hnm1, Finset.card_insert_of_notMem hnm2, Finset.card_pair hb12]
            have ho4c : o4I.card = 4 := by change ({0, 2, 8, 9} : Finset (Fin 10)).card = 4; rw [← hI]; exact hI4
            omega
          rw [h4, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl | rfl
          · exfalso
            have h3 : (g10_nbB a).card = 3 := petersen_deg3 a
            have hsub : ({b1, b2, va} : Finset (Fin 10)) ⊆ g10_nbB a := fun z hz => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 gb1a)⟩
              · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 gb2a)⟩
              · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, gvaa⟩
            have hva1 : va ≠ b1 := fun hh => o4_not_mem_I va hvaA (hh ▸ hb1)
            have hva2 : va ≠ b2 := fun hh => o4_not_mem_I va hvaA (hh ▸ hb2)
            have hnm_b1 : b1 ∉ ({b2, va} : Finset (Fin 10)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hb12, hva1.symm⟩
            have heq_nb := Finset.eq_of_subset_of_card_le hsub (by
              rw [Finset.card_insert_of_notMem hnm_b1, Finset.card_pair hva2.symm, h3])
            have hm1 : a1 ∈ g10_nbB a := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 gia)⟩
            rw [← heq_nb, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hm1
            rcases hm1 with h' | h' | h'
            · exact ha1b1 h'
            · exact ha1b2 h'
            · exact o4_not_mem_I va hvaA (h' ▸ ha1)
          · exfalso
            have h3 : (g10_nbB a).card = 3 := petersen_deg3 a
            have hsub : ({b1, b2, va} : Finset (Fin 10)) ⊆ g10_nbB a := fun z hz => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 gb1a)⟩
              · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 gb2a)⟩
              · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, gvaa⟩
            have hva1 : va ≠ b1 := fun hh => o4_not_mem_I va hvaA (hh ▸ hb1)
            have hva2 : va ≠ b2 := fun hh => o4_not_mem_I va hvaA (hh ▸ hb2)
            have hnm_b1 : b1 ∉ ({b2, va} : Finset (Fin 10)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hb12, hva1.symm⟩
            have heq_nb := Finset.eq_of_subset_of_card_le hsub (by
              rw [Finset.card_insert_of_notMem hnm_b1, Finset.card_pair hva2.symm, h3])
            have hm1 : a2 ∈ g10_nbB a := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 gia)⟩
            rw [← heq_nb, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hm1
            rcases hm1 with h' | h' | h'
            · exact ha2b1 h'
            · exact ha2b2 h'
            · exact o4_not_mem_I va hvaA (h' ▸ ha2)
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hi_eq with rfl | rfl
        · exact sem_adjB_false.1 gib ((hfull_b1 b).1 hb_in_pi)
        · exact sem_adjB_false.1 gib ((hfull_b2 b).1 hb_in_pi)

theorem exp3_kill {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {x a b : Fin 10}
    (h1a : ¬ Adj 1 a) (h1b : ¬ Adj 1 b) (hab : ¬ Adj a b)
    (hnb : Adj x 1 ∨ Adj x a ∨ Adj x b)
    (hhit : ∀ e ∈ sem_W 10 D x, (1 : Fin 10) ∈ supp 10 D (src D e) ∨
      a ∈ supp 10 D (src D e) ∨ b ∈ supp 10 D (src D e)) : False := by
  have hA : ∀ u ∈ ({1, a, b} : Finset (Fin 10)), ∀ v ∈ ({1, a, b} : Finset (Fin 10)), ¬ Adj u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact adj_irrefl _
    · exact h1a
    · exact h1b
    · exact fun h' => h1a (adj_symm h')
    · exact adj_irrefl _
    · exact hab
    · exact fun h' => h1b (adj_symm h')
    · exact fun h' => hab (adj_symm h')
    · exact adj_irrefl _
  have hnb' : ∃ y ∈ ({1, a, b} : Finset (Fin 10)), Adj x y := by
    rcases hnb with h1 | h2 | h3
    · exact ⟨1, by simp, h1⟩
    · exact ⟨a, by simp, h2⟩
    · exact ⟨b, by simp, h3⟩
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure sem_g10_gr h.1 (sem_g10_comp hD) {1, a, b} hA x hnb'
  have heW : (j, s) ∈ sem_W 10 D x := sem_mem_W.2 ⟨hj, h1, h2⟩
  rcases hhit (j, s) heW with hm | hm | hm
  · exact Finset.disjoint_left.1 hd hm (by simp)
  · exact Finset.disjoint_left.1 hd hm (by simp)
  · exact Finset.disjoint_left.1 hd hm (by simp)

theorem o3a_one_at_most_one {D : Dag} (hS : Strict 10 D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i0 i2 i6 : Fin 10}
    (hi0 : i0 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D) (hi6 : i6 ∈ ineligSet 10 D)
    (hi02 : i0 ≠ i2) (hi06 : i0 ≠ i6) (hi26 : i2 ≠ i6)
    (hp0 : pos i0 ∈ sem_W 10 D 1) (hp2 : pos i2 ∈ sem_W 10 D 1) (hp6 : pos i6 ∈ sem_W 10 D 1)
    (hcc : (sem_W 10 D 1).card + (merges 10 D (carrierT 10 D {1})).card ≤ 4)
    {e1 e2 : ℕ × Bool}
    (he1_lt : e1.1 < D.length) (he1_and : tag D e1.1 = true) (he1_1 : (1 : Fin 10) ∈ supp 10 D (src D e1))
    (he1_n0 : e1.1 ≠ (pos i0).1) (he1_n2 : e1.1 ≠ (pos i2).1) (he1_n6 : e1.1 ≠ (pos i6).1)
    (he2_lt : e2.1 < D.length) (he2_and : tag D e2.1 = true) (he2_1 : (1 : Fin 10) ∈ supp 10 D (src D e2))
    (he2_n0 : e2.1 ≠ (pos i0).1) (he2_n2 : e2.1 ≠ (pos i2).1) (he2_n6 : e2.1 ≠ (pos i6).1) :
    e1.1 = e2.1 := by
  by_contra hne
  have h02 : pos i0 ≠ pos i2 := fun e => hi02 (hpos.2 _ hi0 _ hi2 e)
  have h06 : pos i0 ≠ pos i6 := fun e => hi06 (hpos.2 _ hi0 _ hi6 e)
  have h26 : pos i2 ≠ pos i6 := fun e => hi26 (hpos.2 _ hi2 _ hi6 e)
  have h1n0 : e1 ≠ pos i0 := fun e => he1_n0 (congrArg Prod.fst e)
  have h1n2 : e1 ≠ pos i2 := fun e => he1_n2 (congrArg Prod.fst e)
  have h1n6 : e1 ≠ pos i6 := fun e => he1_n6 (congrArg Prod.fst e)
  have h2n0 : e2 ≠ pos i0 := fun e => he2_n0 (congrArg Prod.fst e)
  have h2n2 : e2 ≠ pos i2 := fun e => he2_n2 (congrArg Prod.fst e)
  have h2n6 : e2 ≠ pos i6 := fun e => he2_n6 (congrArg Prod.fst e)
  have h12 : e1 ≠ e2 := fun e => hne (congrArg Prod.fst e)
  have hmemM : ∀ e : ℕ × Bool, e.1 < D.length → tag D e.1 = true →
      (1 : Fin 10) ∈ supp 10 D (10 + e.1) → e.1 ∈ merges 10 D (carrierT 10 D {1}) := fun e hlt ht hm => by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    have hAB := Finset.mem_inter.1 (sem_supp_and hS hlt ht ▸ hm)
    exact ⟨hlt, sem_mem_carrier1.2 hm, sem_mem_carrier1.2 hAB.1, sem_mem_carrier1.2 hAB.2⟩
  by_cases h1in : (1 : Fin 10) ∈ supp 10 D (10 + e1.1) <;> by_cases h2in : (1 : Fin 10) ∈ supp 10 D (10 + e2.1)
  · have hw3 := pa_card3 hp0 hp2 hp6 h02 h06 h26
    have hm2 : 2 ≤ (merges 10 D (carrierT 10 D {1})).card := by
      have hsub : ({e1.1, e2.1} : Finset ℕ) ⊆ merges 10 D (carrierT 10 D {1}) := fun j hj => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hmemM e1 he1_lt he1_and h1in
        · exact hmemM e2 he2_lt he2_and h2in
      have := Finset.card_le_card hsub; rwa [Finset.card_pair hne] at this
    omega
  · have hw4 := pa_card4 hp0 hp2 hp6 (sem_mem_W.2 ⟨he2_lt, he2_1, h2in⟩) h02 h06 h2n0.symm h26 h2n2.symm h2n6.symm
    have hm1 : 1 ≤ (merges 10 D (carrierT 10 D {1})).card := Finset.card_pos.2 ⟨_, hmemM e1 he1_lt he1_and h1in⟩
    omega
  · have hw4 := pa_card4 hp0 hp2 hp6 (sem_mem_W.2 ⟨he1_lt, he1_1, h1in⟩) h02 h06 h1n0.symm h26 h1n2.symm h1n6.symm
    have hm1 : 1 ≤ (merges 10 D (carrierT 10 D {1})).card := Finset.card_pos.2 ⟨_, hmemM e2 he2_lt he2_and h2in⟩
    omega
  · have hw5 := pa_card5 hp0 hp2 hp6 (sem_mem_W.2 ⟨he1_lt, he1_1, h1in⟩) (sem_mem_W.2 ⟨he2_lt, he2_1, h2in⟩)
      h02 h06 h1n0.symm h2n0.symm h26 h1n2.symm h2n2.symm h1n6.symm h2n6.symm h12
    omega

theorem o3a_core_kill {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbm : sem_MinBranch 10 D br) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    (hI : ineligSet 10 D = {0, 2, 6})
    {ua ub : Σ _ : ℕ, ℕ} (huab : ua ≠ ub) (hReq : residualUnits 10 D br = {ua, ub})
    (hru1 : ru D br 1 = {ua, ub})
    (i0 i2 i6 x3 x4 x9 x7 x5 x8 : Fin 10)
    (hg : i0 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ i2 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ i6 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧
      i0 ≠ i2 ∧ i0 ≠ i6 ∧ i2 ≠ i6 ∧
      x3 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x4 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x9 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧
      x7 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x5 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x8 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧
      hc_adjB i0 1 = true ∧ hc_adjB i2 1 = true ∧ hc_adjB i6 1 = true ∧
      hc_adjB i0 x4 = true ∧ hc_adjB i0 x5 = true ∧ hc_adjB i2 x3 = true ∧ hc_adjB i2 x7 = true ∧
      hc_adjB i6 x8 = true ∧ hc_adjB i6 x9 = true ∧
      hc_adjB x3 x4 = true ∧ hc_adjB x4 x9 = true ∧ hc_adjB x9 x7 = true ∧
      hc_adjB x7 x5 = true ∧ hc_adjB x5 x8 = true ∧ hc_adjB x8 x3 = true ∧
      hc_adjB i0 x3 = false ∧ hc_adjB i0 x7 = false ∧ hc_adjB i0 x8 = false ∧ hc_adjB i0 x9 = false ∧
      hc_adjB i2 x4 = false ∧ hc_adjB i2 x5 = false ∧ hc_adjB i2 x8 = false ∧ hc_adjB i2 x9 = false ∧
      hc_adjB i6 x3 = false ∧ hc_adjB i6 x4 = false ∧ hc_adjB i6 x5 = false ∧ hc_adjB i6 x7 = false ∧
      hc_adjB x5 x3 = false ∧ hc_adjB x5 x9 = false ∧ hc_adjB x8 x4 = false ∧ hc_adjB x8 x7 = false ∧
      hc_adjB x3 x9 = false ∧ hc_adjB x4 x7 = false ∧ hc_adjB x3 x5 = false ∧ hc_adjB x7 x8 = false ∧
      hc_adjB 1 x3 = false ∧ hc_adjB 1 x4 = false ∧ hc_adjB 1 x5 = false ∧ hc_adjB 1 x7 = false ∧ hc_adjB 1 x8 = false ∧ hc_adjB 1 x9 = false ∧
      hc_adjB x4 x5 = false ∧ hc_adjB x8 x9 = false ∧ hc_adjB x3 x7 = false ∧
      x3 ≠ 1 ∧ x4 ≠ 1 ∧ x5 ≠ 1 ∧ x7 ≠ 1 ∧ x8 ≠ 1 ∧ x9 ≠ 1 ∧
      x4 ≠ x5 ∧ x8 ≠ x9 ∧ x3 ≠ x4 ∧ x4 ≠ x9 ∧ x9 ≠ x7 ∧ x7 ≠ x5 ∧ x5 ≠ x8 ∧ x8 ≠ x3 ∧ x3 ≠ x7 ∧ x4 ≠ x8 ∧ x9 ≠ x5 ∧ x3 ≠ x9 ∧ x4 ≠ x7 ∧ x3 ≠ x5 ∧ x7 ≠ x8)
    (hru4 : ru D br x4 = {ua}) (hru5 : ru D br x5 = {ua})
    (hru8 : ru D br x8 = {ub}) (hru9 : ru D br x9 = {ub})
    (hru3 : ru D br x3 = ∅ ∨ ru D br x3 = {ua, ub})
    (hru7 : ru D br x7 = ∅ ∨ ru D br x7 = {ua, ub}) : False := by
  classical
  have hS := h.1
  have hC := sem_g10_comp hD
  have hbp := sem_minBranch_pure hbm
  obtain ⟨hi0', hi2', hi6', hi02, hi06, hi26, hx3n, hx4n, hx9n, hx7n, hx5n, hx8n,
    g01, g21, g61, g04, g05, g23, g27, g68, g69,
    g34, g49, g97, g75, g58, g83,
    n03, n07, n08, n09, n24, n25, n28, n29, n63, n64, n65, n67,
    n53, n59, n84, n87, n39, n47, n35, n78, n13, n14, n15, n17, n18, n19, n45, n89, n37,
    h31, h41, h51, h71, h81, h91, h45, h89, h34, h49, h97, h75, h58, h83, h37, h48, h95, h39, h47, h35, h78⟩ := hg
  have hm : ∀ v : Fin 10, v ∈ ({0, 2, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 2, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 2, 6} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hI ▸ sem_mem_inelig.2 hc)
  have hi0 := hm i0 hi0'; have hi2 := hm i2 hi2'; have hi6 := hm i6 hi6'
  have h1E : (1 : Fin 10) ∈ eligSet 10 D := helig 1 (by decide)
  have h1_ua : (1 : Fin 10) ∈ supp 10 D ua.1 := (mem_ru.1 (hru1 ▸ Finset.mem_insert_self ua {ub})).2
  have h1_ub : (1 : Fin 10) ∈ supp 10 D ub.1 := (mem_ru.1 (hru1 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self ub))).2
  have h5_ua : x5 ∈ supp 10 D ua.1 := (mem_ru.1 (hru5 ▸ Finset.mem_singleton_self ua)).2
  have h4_ua : x4 ∈ supp 10 D ua.1 := (mem_ru.1 (hru4 ▸ Finset.mem_singleton_self ua)).2
  have h8_ub : x8 ∈ supp 10 D ub.1 := (mem_ru.1 (hru8 ▸ Finset.mem_singleton_self ub)).2
  have h9_ub : x9 ∈ supp 10 D ub.1 := (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self ub)).2
  have hpe1 : ∀ b : Fin 10, b ≠ 1 → ru D br b = {ua, ub} →
      ∀ j ∈ ({i0, i2, i6} : Finset (Fin 10)), ∀ q : Fin 10,
      hc_adjB j 1 = true → hc_adjB j q = true → (1 : Fin 10) ≠ q → hc_adjB b q = false →
      b ∈ supp 10 D (src D (pos j)) := by
    intro b hb1 hrub j hj q gj1 gjq h1q hbq
    have hjI : j ∈ ineligSet 10 D := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl; exact hi0; exact hi2; exact hi6
    have hres : ∀ u' ∈ residualUnits 10 D br, (1 : Fin 10) ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
      fun u' hu' _ => (mem_ru.1 (hrub ▸ (hReq ▸ hu'))).2
    have hw : (1 : Fin 10) ∈ supp 10 D ua.1 ∧ b ∈ supp 10 D ua.1 :=
      ⟨h1_ua, (mem_ru.1 (hrub ▸ Finset.mem_insert_self ua {ub})).2⟩
    exact pe_co_g10 h hD br hbp hpos hjI h1E hres hw ⟨petersen_deg3 1, gj1, gjq, hb1.symm, h1q, hbq⟩

  have hW4_eq3 : (sem_W 10 D x4).card = 3 ∧ merges 10 D (carrierT 10 D {x4}) = ∅ := by
    have hge3 : 3 ≤ (sem_W 10 D x4).card := by
      by_contra hle2
      have hfull0 := full_of_le2 h hD hB0 hpos hi0 ((hc_adjB_iff _ _).1 g04) ((hc_adjB_iff _ _).1 g49) (hn x9 hx9n) (by omega)
      have h3ge : 3 ≤ (sem_W 10 D x3).card := by
        by_contra h3le
        exact pa_m1_gen h hD hpos x3 x4 x8 i2 i0 1 hi2 hi0 (hn x3 hx3n) (hn x4 hx4n) (hn x8 hx8n)
          ⟨g23, g04, g34, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 g83), h48.symm,
            petersen_deg3 x4, g01, h41.symm, n18⟩ (by omega) (by omega)
      have hru3_full : ru D br x3 = {ua, ub} := hru3.resolve_left (fun he => by
        have := cc_le h hD br hbp x3; rw [he, Finset.card_empty] at this; omega)
      have h3in0 := hpe1 x3 h31 hru3_full i0 (by simp) x5 g01 g05 h51.symm n35
      exact sem_adjB_false.1 n03 ((hfull0 x3).1 h3in0)
    have hcc := cc_le h hD br hbp x4; rw [hru4, Finset.card_singleton] at hcc
    exact ⟨by omega, Finset.card_eq_zero.1 (by omega)⟩
  have hW9_eq3 : (sem_W 10 D x9).card = 3 ∧ merges 10 D (carrierT 10 D {x9}) = ∅ := by
    have hge3 : 3 ≤ (sem_W 10 D x9).card := by
      by_contra hle2
      have hfull6 := full_of_le2 h hD hB0 hpos hi6 ((hc_adjB_iff _ _).1 g69) ((hc_adjB_iff _ _).1 g97) (hn x7 hx7n) (by omega)
      have h7ge : 3 ≤ (sem_W 10 D x7).card := by
        by_contra h7le
        exact pa_m1_gen h hD hpos x7 x9 x5 i2 i6 1 hi2 hi6 (hn x7 hx7n) (hn x9 hx9n) (hn x5 hx5n)
          ⟨g27, g69, by rw [hc_adjB_iff]; exact adj_symm ((hc_adjB_iff _ _).1 g97), g75, h95.symm,
            petersen_deg3 x9, g61, h91.symm, n15⟩ (by omega) (by omega)
      have hru7_full : ru D br x7 = {ua, ub} := hru7.resolve_left (fun he => by
        have := cc_le h hD br hbp x7; rw [he, Finset.card_empty] at this; omega)
      have h7in6 := hpe1 x7 h71 hru7_full i6 (by simp) x8 g61 g68 h81.symm n78
      exact sem_adjB_false.1 n67 ((hfull6 x7).1 h7in6)
    have hcc := cc_le h hD br hbp x9; rw [hru9, Finset.card_singleton] at hcc
    exact ⟨by omega, Finset.card_eq_zero.1 (by omega)⟩

  have h3_struct : merges 10 D (carrierT 10 D {x3}) = ∅ ∧
      ∃ g3 ∈ sem_W 10 D x3,
        (∀ e ∈ sem_W 10 D x3, e = pos i0 ∨ e = pos i2 ∨ e = pos i6 ∨ e = g3) ∧
        sem_bar g3 ∈ sem_W 10 D x4 ∧ sem_bar g3 ∈ sem_W 10 D x8 := by
    obtain ⟨g3, hg3, hbg3_4, hfg3, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 g34)
    obtain ⟨g3', hg3', hbg3'_8, hfg3', -⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 g83))
    have hg3_n0 : g3 ≠ pos i0 := fun e => hn x4 hx4n (hfg3 i0 hi0 e ▸ hi0)
    have hg3_n2 : g3 ≠ pos i2 := fun e => hn x4 hx4n (hfg3 i2 hi2 e ▸ hi2)
    have hg3_n6 : g3 ≠ pos i6 := fun e => hn x4 hx4n (hfg3 i6 hi6 e ▸ hi6)
    have hg3'_n0 : g3' ≠ pos i0 := fun e => hn x8 hx8n (hfg3' i0 hi0 e ▸ hi0)
    have hg3'_n2 : g3' ≠ pos i2 := fun e => hn x8 hx8n (hfg3' i2 hi2 e ▸ hi2)
    have hg3'_n6 : g3' ≠ pos i6 := fun e => hn x8 hx8n (hfg3' i6 hi6 e ▸ hi6)
    have hp2 := as_mem hpos hi2 ((hc_adjB_iff _ _).1 g23)
    rcases hru3 with h3e | h3f
    · have hcc := cc_le h hD br hbp x3; rw [h3e, Finset.card_empty] at hcc
      have h2 := pa_two hp2 hg3 hg3_n2.symm (by omega)
      have hcard : 2 ≤ (sem_W 10 D x3).card := by
        have hsub : ({pos i2, g3} : Finset (ℕ × Bool)) ⊆ sem_W 10 D x3 := fun e he => by
          rw [Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl; exact hp2; exact hg3
        have := Finset.card_le_card hsub; rwa [Finset.card_pair hg3_n2.symm] at this
      have hge : g3' = g3 := (h2 g3' hg3').resolve_left hg3'_n2
      exact ⟨Finset.card_eq_zero.1 (by omega), g3, hg3, fun e he => by
        rcases h2 e he with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inr rfl)),
        hbg3_4, hge ▸ hbg3'_8⟩
    · have hcc := cc_le h hD br hbp x3; rw [h3f, Finset.card_pair huab] at hcc
      have hp0 := mem_W_of_pos hpos hi0 (hpe1 x3 h31 h3f i0 (by simp) x5 g01 g05 h51.symm n35)
      have hp6 := mem_W_of_pos hpos hi6 (hpe1 x3 h31 h3f i6 (by simp) x9 g61 g69 h91.symm n39)
      have h02 : pos i0 ≠ pos i2 := fun e => hi02 (hpos.2 _ hi0 _ hi2 e)
      have h06 : pos i0 ≠ pos i6 := fun e => hi06 (hpos.2 _ hi0 _ hi6 e)
      have h26 : pos i2 ≠ pos i6 := fun e => hi26 (hpos.2 _ hi2 _ hi6 e)
      have h4 := pa_four hp0 hp2 hp6 hg3 h02 h06 hg3_n0.symm h26 hg3_n2.symm hg3_n6.symm (by omega)
      have hcard := pa_card4 hp0 hp2 hp6 hg3 h02 h06 hg3_n0.symm h26 hg3_n2.symm hg3_n6.symm
      have hge : g3' = g3 := by
        rcases h4 g3' hg3' with h' | h' | h' | h'
        · exact absurd h' hg3'_n0
        · exact absurd h' hg3'_n2
        · exact absurd h' hg3'_n6
        · exact h'
      exact ⟨Finset.card_eq_zero.1 (by omega), g3, hg3, h4, hbg3_4, hge ▸ hbg3'_8⟩
  have h7_struct : merges 10 D (carrierT 10 D {x7}) = ∅ ∧
      ∃ g7 ∈ sem_W 10 D x7,
        (∀ e ∈ sem_W 10 D x7, e = pos i0 ∨ e = pos i2 ∨ e = pos i6 ∨ e = g7) ∧
        sem_bar g7 ∈ sem_W 10 D x9 ∧ sem_bar g7 ∈ sem_W 10 D x5 := by
    obtain ⟨g7, hg7, hbg7_9, hfg7, -⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 g97))
    obtain ⟨g7', hg7', hbg7'_5, hfg7', -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 g75)
    have hg7_n0 : g7 ≠ pos i0 := fun e => hn x9 hx9n (hfg7 i0 hi0 e ▸ hi0)
    have hg7_n2 : g7 ≠ pos i2 := fun e => hn x9 hx9n (hfg7 i2 hi2 e ▸ hi2)
    have hg7_n6 : g7 ≠ pos i6 := fun e => hn x9 hx9n (hfg7 i6 hi6 e ▸ hi6)
    have hg7'_n0 : g7' ≠ pos i0 := fun e => hn x5 hx5n (hfg7' i0 hi0 e ▸ hi0)
    have hg7'_n2 : g7' ≠ pos i2 := fun e => hn x5 hx5n (hfg7' i2 hi2 e ▸ hi2)
    have hg7'_n6 : g7' ≠ pos i6 := fun e => hn x5 hx5n (hfg7' i6 hi6 e ▸ hi6)
    have hp2 := as_mem hpos hi2 ((hc_adjB_iff _ _).1 g27)
    rcases hru7 with h7e | h7f
    · have hcc := cc_le h hD br hbp x7; rw [h7e, Finset.card_empty] at hcc
      have h2 := pa_two hp2 hg7 hg7_n2.symm (by omega)
      have hcard : 2 ≤ (sem_W 10 D x7).card := by
        have hsub : ({pos i2, g7} : Finset (ℕ × Bool)) ⊆ sem_W 10 D x7 := fun e he => by
          rw [Finset.mem_insert, Finset.mem_singleton] at he; rcases he with rfl | rfl; exact hp2; exact hg7
        have := Finset.card_le_card hsub; rwa [Finset.card_pair hg7_n2.symm] at this
      have hge : g7' = g7 := (h2 g7' hg7').resolve_left hg7'_n2
      exact ⟨Finset.card_eq_zero.1 (by omega), g7, hg7, fun e he => by
        rcases h2 e he with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inr rfl)),
        hbg7_9, hge ▸ hbg7'_5⟩
    · have hcc := cc_le h hD br hbp x7; rw [h7f, Finset.card_pair huab] at hcc
      have hp0 := mem_W_of_pos hpos hi0 (hpe1 x7 h71 h7f i0 (by simp) x4 g01 g04 h41.symm
        (sem_adjB_false.2 (fun hh => sem_adjB_false.1 n47 (adj_symm hh))))
      have hp6 := mem_W_of_pos hpos hi6 (hpe1 x7 h71 h7f i6 (by simp) x8 g61 g68 h81.symm n78)
      have h02 : pos i0 ≠ pos i2 := fun e => hi02 (hpos.2 _ hi0 _ hi2 e)
      have h06 : pos i0 ≠ pos i6 := fun e => hi06 (hpos.2 _ hi0 _ hi6 e)
      have h26 : pos i2 ≠ pos i6 := fun e => hi26 (hpos.2 _ hi2 _ hi6 e)
      have h4 := pa_four hp0 hp2 hp6 hg7 h02 h06 hg7_n0.symm h26 hg7_n2.symm hg7_n6.symm (by omega)
      have hcard := pa_card4 hp0 hp2 hp6 hg7 h02 h06 hg7_n0.symm h26 hg7_n2.symm hg7_n6.symm
      have hge : g7' = g7 := by
        rcases h4 g7' hg7' with h' | h' | h' | h'
        · exact absurd h' hg7'_n0
        · exact absurd h' hg7'_n2
        · exact absurd h' hg7'_n6
        · exact h'
      exact ⟨Finset.card_eq_zero.1 (by omega), g7, hg7, h4, hbg7_9, hge ▸ hbg7'_5⟩
  obtain ⟨hM3, g3, hg3, hW3_all, hbg3_4, hbg3_8⟩ := h3_struct
  obtain ⟨hM7, g7, hg7, hW7_all, hbg7_9, hbg7_5⟩ := h7_struct

  obtain ⟨eu1, heu1_4, heu1_n0, heu1_1, heu1_5⟩ :
      ∃ eu1 ∈ sem_W 10 D x4, eu1 ≠ pos i0 ∧ (1 : Fin 10) ∈ supp 10 D (src D eu1) ∧ x5 ∈ supp 10 D (src D eu1) := by
    obtain ⟨e1, e2, he1, he2, h12, hs1, hs2⟩ := ru_one_two_supp h hD br hbm hW4_eq3.2 hru4
    by_cases h1p : e1 = pos i0
    · exact ⟨e2, he2, fun hh => h12 (h1p.trans hh.symm), hs2 h1_ua, hs2 h5_ua⟩
    · exact ⟨e1, he1, h1p, hs1 h1_ua, hs1 h5_ua⟩
  obtain ⟨eu2, heu2_9, heu2_n6, heu2_1, heu2_8⟩ :
      ∃ eu2 ∈ sem_W 10 D x9, eu2 ≠ pos i6 ∧ (1 : Fin 10) ∈ supp 10 D (src D eu2) ∧ x8 ∈ supp 10 D (src D eu2) := by
    obtain ⟨e1, e2, he1, he2, h12, hs1, hs2⟩ := ru_one_two_supp h hD br hbm hW9_eq3.2 hru9
    by_cases h1p : e1 = pos i6
    · exact ⟨e2, he2, fun hh => h12 (h1p.trans hh.symm), hs2 h1_ub, hs2 h8_ub⟩
    · exact ⟨e1, he1, h1p, hs1 h1_ub, hs1 h8_ub⟩

  have ⟨e0, he0_4, he0_n5, he0_v43, he0_v49⟩ :
      ∃ e0 ∈ sem_W 10 D x4, x5 ∉ supp 10 D (src D e0) ∧
        val D (sem_two x4 x3) (10 + e0.1) = true ∧ val D (sem_two x4 x9) (10 + e0.1) = true := by
    have hres45 : ∀ u' ∈ residualUnits 10 D br, x4 ∈ supp 10 D u'.1 → x5 ∈ supp 10 D u'.1 := fun u' hu' h4' =>
      (mem_ru.1 (hru5 ▸ (hru4 ▸ mem_ru.2 ⟨hu', h4'⟩))).2
    obtain ⟨e0, hri⟩ := ri_gen sem_g10_gr h hC br hbp h45 (helig x4 hx4n) hres45 ⟨h4_ua, h5_ua⟩
    obtain ⟨e3, he3_4, hv43, hv53f, hbv53⟩ := pa_ed_avoid_min h hD (adj_symm ((hc_adjB_iff _ _).1 g34))
      (sem_adjB_false.1 n53) h45 h34.symm (Or.inl rfl)
    obtain ⟨e9, he9_4, hv49, hv59f, hbv59⟩ := pa_ed_avoid_min h hD ((hc_adjB_iff _ _).1 g49)
      (sem_adjB_false.1 n59) h45 h49 (Or.inl rfl)
    have h3n5 : x5 ∉ supp 10 D (src D e3) := fun hm5 => by
      have := val_gate_of_supp_and_val hS (sem_mem_W.1 he3_4).1 (sem_W_and hS he3_4) hm5 hbv53
      rw [this] at hv53f; exact Bool.noConfusion hv53f
    have h9n5 : x5 ∉ supp 10 D (src D e9) := fun hm5 => by
      have := val_gate_of_supp_and_val hS (sem_mem_W.1 he9_4).1 (sem_W_and hS he9_4) hm5 hbv59
      rw [this] at hv59f; exact Bool.noConfusion hv59f
    have h3eq : e3 = e0 := by by_contra hne; exact h3n5 (hri e3 he3_4 hne)
    have h9eq : e9 = e0 := by by_contra hne; exact h9n5 (hri e9 he9_4 hne)
    exact ⟨e0, h3eq ▸ he3_4, h3eq ▸ h3n5, h3eq ▸ hv43, h9eq ▸ hv49⟩
  have ⟨e0_9, he09_9, he09_n8, he09_v97, he09_v94⟩ :
      ∃ e0_9 ∈ sem_W 10 D x9, x8 ∉ supp 10 D (src D e0_9) ∧
        val D (sem_two x9 x7) (10 + e0_9.1) = true ∧ val D (sem_two x9 x4) (10 + e0_9.1) = true := by
    have hres98 : ∀ u' ∈ residualUnits 10 D br, x9 ∈ supp 10 D u'.1 → x8 ∈ supp 10 D u'.1 := fun u' hu' h9' =>
      (mem_ru.1 (hru8 ▸ (hru9 ▸ mem_ru.2 ⟨hu', h9'⟩))).2
    obtain ⟨e0_9, hri⟩ := ri_gen sem_g10_gr h hC br hbp h89.symm (helig x9 hx9n) hres98 ⟨h9_ub, h8_ub⟩
    obtain ⟨e7, he7_9, hv97, hv87f, hbv87⟩ := pa_ed_avoid_min h hD ((hc_adjB_iff _ _).1 g97)
      (sem_adjB_false.1 n87) h89.symm h97 (Or.inl rfl)
    obtain ⟨e4, he4_9, hv94, hv84f, hbv84⟩ := pa_ed_avoid_min h hD (adj_symm ((hc_adjB_iff _ _).1 g49))
      (sem_adjB_false.1 n84) h89.symm h49.symm (Or.inl rfl)
    have h7n8 : x8 ∉ supp 10 D (src D e7) := fun hm8 => by
      have := val_gate_of_supp_and_val hS (sem_mem_W.1 he7_9).1 (sem_W_and hS he7_9) hm8 hbv87
      rw [this] at hv87f; exact Bool.noConfusion hv87f
    have h4n8 : x8 ∉ supp 10 D (src D e4) := fun hm8 => by
      have := val_gate_of_supp_and_val hS (sem_mem_W.1 he4_9).1 (sem_W_and hS he4_9) hm8 hbv84
      rw [this] at hv84f; exact Bool.noConfusion hv84f
    have h7eq : e7 = e0_9 := by by_contra hne; exact h7n8 (hri e7 he7_9 hne)
    have h4eq : e4 = e0_9 := by by_contra hne; exact h4n8 (hri e4 he4_9 hne)
    exact ⟨e0_9, h7eq ▸ he7_9, h7eq ▸ h7n8, h7eq ▸ hv97, h4eq ▸ hv94⟩
  have hp0_4 := as_mem hpos hi0 ((hc_adjB_iff _ _).1 g04)
  have hp6_9 := as_mem hpos hi6 ((hc_adjB_iff _ _).1 g69)
  have he0_n0 : e0 ≠ pos i0 := fun hh => he0_n5 (hh ▸ (hpos.1 i0 hi0).2.2.1 x5 ((hc_adjB_iff _ _).1 g05))
  have he0_neu1 : e0 ≠ eu1 := fun hh => he0_n5 (hh ▸ heu1_5)
  have hW4_all := pa_three hp0_4 heu1_4 he0_4 heu1_n0.symm he0_n0.symm he0_neu1.symm (by omega)
  have he09_n6 : e0_9 ≠ pos i6 := fun hh => he09_n8 (hh ▸ (hpos.1 i6 hi6).2.2.1 x8 ((hc_adjB_iff _ _).1 g68))
  have he09_neu2 : e0_9 ≠ eu2 := fun hh => he09_n8 (hh ▸ heu2_8)
  have hW9_all := pa_three hp6_9 heu2_9 he09_9 heu2_n6.symm he09_n6.symm he09_neu2.symm (by omega)
  have hpos_1 : (1 : Fin 10) ∈ supp 10 D (src D (pos i0)) ∧ (1 : Fin 10) ∈ supp 10 D (src D (pos i2)) ∧
      (1 : Fin 10) ∈ supp 10 D (src D (pos i6)) :=
    ⟨(hpos.1 i0 hi0).2.2.1 1 ((hc_adjB_iff _ _).1 g01),
     (hpos.1 i2 hi2).2.2.1 1 ((hc_adjB_iff _ _).1 g21),
     (hpos.1 i6 hi6).2.2.1 1 ((hc_adjB_iff _ _).1 g61)⟩
  have hnot_g3_1 : (1 : Fin 10) ∉ supp 10 D (src D g3) := fun h1g3 => by
    obtain ⟨e, he3, hne1⟩ := sem_antichain sem_g10_gr hS hC h31
    rcases hW3_all e he3 with rfl | rfl | rfl | rfl
    · exact hne1 hpos_1.1
    · exact hne1 hpos_1.2.1
    · exact hne1 hpos_1.2.2
    · exact hne1 h1g3
  have hbar_val : ∀ {e : ℕ × Bool} {a b : Fin 10}, e ∈ sem_W 10 D a →
      val D (sem_two a b) (10 + e.1) = true → val D (sem_two a b) (src D (sem_bar e)) = true := by
    intro e a b he hv
    have hj := (sem_mem_W.1 he).1; have ht := sem_W_and hS he
    rw [val_gate hS _ e.1 hj, ht, gop_true, Bool.and_eq_true] at hv
    rcases heq : e with ⟨j, s⟩; rw [heq] at hv
    cases s
    · exact hv.2
    · exact hv.1
  have hbar_notsupp : ∀ {e : ℕ × Bool} {a : Fin 10}, e ∈ sem_W 10 D a → a ∉ supp 10 D (src D (sem_bar e)) := by
    intro e a he ha
    have hj := (sem_mem_W.1 he).1; have ht := sem_W_and hS he
    have ha1 := (sem_mem_W.1 he).2.1
    apply (sem_mem_W.1 he).2.2
    rw [sem_supp_and hS hj ht, Finset.mem_inter]
    rcases heq : e with ⟨j, s⟩; rw [heq] at ha ha1
    cases s
    · exact ⟨by simpa [src] using ha1, by simpa [src, sem_bar] using ha⟩
    · exact ⟨by simpa [src, sem_bar] using ha, by simpa [src] using ha1⟩
  have hneq_pos_fst : ∀ {e : ℕ × Bool} {v : Fin 10}, v ∉ ({0, 2, 6} : Finset (Fin 10)) →
      v ∈ supp 10 D (src D (sem_bar e)) → (1 : Fin 10) ∈ supp 10 D (src D e) →
      e.1 ≠ (pos i0).1 ∧ e.1 ≠ (pos i2).1 ∧ e.1 ≠ (pos i6).1 := by
    intro e v hvn hv h1e
    have one : ∀ j ∈ ({0, 2, 6} : Finset (Fin 10)), e.1 ≠ (pos j).1 := fun j hj heq => by
      have hjI := hm j hj
      rcases sem_same_gate heq.symm with rfl | hbar
      · have := (hpos.1 j hjI).2.2.2
        rw [show src D (sem_bar (pos j)) = src D ((pos j).1, !(pos j).2) from rfl, this, Finset.mem_singleton] at hv
        exact hvn (hv ▸ hj)
      · rw [hbar, show src D (sem_bar (pos j)) = src D ((pos j).1, !(pos j).2) from rfl,
          (hpos.1 j hjI).2.2.2, Finset.mem_singleton] at h1e
        exact (by decide : (1 : Fin 10) ∉ ({0, 2, 6} : Finset (Fin 10))) (h1e ▸ hj)
    exact ⟨one i0 hi0', one i2 hi2', one i6 hi6'⟩

  by_cases h3in : x3 ∈ supp 10 D (src D (sem_bar e0))
  · have hand_e0 : tag D e0.1 = true := sem_W_and hS he0_4
    have hb3 : sem_bar e0 ∈ sem_W 10 D x3 :=
      zm_mem hS hM3 (e := sem_bar e0) (sem_mem_W.1 he0_4).1 hand_e0 h3in
    have hbe0_eq : sem_bar e0 = g3 := by
      rcases hW3_all (sem_bar e0) hb3 with h' | h' | h' | h'
      · exact absurd (as_priv hpos hi0 (x := x4) (by rw [← h', sem_bar_bar]; exact he0_4)) (fun heq => hx4n (heq ▸ hi0'))
      · exact absurd (as_priv hpos hi2 (x := x4) (by rw [← h', sem_bar_bar]; exact he0_4)) (fun heq => hx4n (heq ▸ hi2'))
      · exact absurd (as_priv hpos hi6 (x := x4) (by rw [← h', sem_bar_bar]; exact he0_4)) (fun heq => hx4n (heq ▸ hi6'))
      · exact h'
    have he0_8 : x8 ∈ supp 10 D (src D e0) := by
      have : e0 = sem_bar g3 := by rw [← hbe0_eq, sem_bar_bar]
      rw [this]; exact (sem_mem_W.1 hbg3_8).2.1
    exact exp3_kill h hD (sem_adjB_false.1 n18) (sem_adjB_false.1 n19) (sem_adjB_false.1 n89)
      (Or.inr (Or.inr ((hc_adjB_iff _ _).1 g49))) (fun e he => by
        rcases hW4_all e he with rfl | rfl | rfl
        · exact Or.inl hpos_1.1
        · exact Or.inl heu1_1
        · exact Or.inr (Or.inl he0_8))
  · obtain ⟨j, s, hj, hle, h4js, h3js⟩ :=
      meeting_le hS (hbar_val he0_4 he0_v43) (hbar_notsupp he0_4) h3in
    have hlt_e0 : j < e0.1 := by
      have hsrc := sem_src_lt hS (sem_mem_W.1 he0_4).1 (sem_bar e0).2
      change src D (sem_bar e0) < 10 + e0.1 at hsrc; omega
    have hjs_eq : (j, s) = eu1 := by
      rcases hW4_all (j, s) h4js with h' | h' | h'
      · have hbar3 : sem_bar (pos i0) ∈ sem_W 10 D x3 := by rw [← h']; exact h3js
        exact absurd (as_priv hpos hi0 hbar3) (fun heq => hx3n (heq ▸ hi0'))
      · exact h'
      · have := congrArg Prod.fst h'; omega
    have hb_eu1_3 : sem_bar eu1 ∈ sem_W 10 D x3 := by rw [← hjs_eq]; exact h3js
    have hbeu1_eq_g3 : sem_bar eu1 = g3 := by
      rcases hW3_all (sem_bar eu1) hb_eu1_3 with h' | h' | h' | h'
      · exact absurd (as_priv hpos hi0 (x := x4) (by rw [← h', sem_bar_bar]; exact heu1_4)) (fun heq => hx4n (heq ▸ hi0'))
      · exact absurd (as_priv hpos hi2 (x := x4) (by rw [← h', sem_bar_bar]; exact heu1_4)) (fun heq => hx4n (heq ▸ hi2'))
      · exact absurd (as_priv hpos hi6 (x := x4) (by rw [← h', sem_bar_bar]; exact heu1_4)) (fun heq => hx4n (heq ▸ hi6'))
      · exact h'
    have heu1_lt_e0 : eu1.1 < e0.1 := by rw [← hjs_eq]; exact hlt_e0
    have heu1_n026 := hneq_pos_fst hx3n (sem_mem_W.1 hb_eu1_3).2.1 heu1_1
    by_cases h9in : x9 ∈ supp 10 D (src D (sem_bar e0))
    · have hand_e0 : tag D e0.1 = true := sem_W_and hS he0_4
      have hb9 : sem_bar e0 ∈ sem_W 10 D x9 :=
        zm_mem hS hW9_eq3.2 (e := sem_bar e0) (sem_mem_W.1 he0_4).1 hand_e0 h9in
      rcases hW9_all (sem_bar e0) hb9 with h' | h' | h'
      · exact absurd (as_priv hpos hi6 (x := x4) (by rw [← h', sem_bar_bar]; exact he0_4)) (fun heq => hx4n (heq ▸ hi6'))
      · have heu2_n026 := hneq_pos_fst hx4n (by rw [← h', sem_bar_bar]; exact (sem_mem_W.1 he0_4).2.1) heu2_1
        have hcc1 : (sem_W 10 D 1).card + (merges 10 D (carrierT 10 D {1})).card ≤ 4 := by
          have := cc_le h hD br hbp 1; rw [hru1, Finset.card_pair huab] at this; omega
        have heq12 := o3a_one_at_most_one hS hpos hi0 hi2 hi6 hi02 hi06 hi26
          (as_mem hpos hi0 ((hc_adjB_iff _ _).1 g01)) (as_mem hpos hi2 ((hc_adjB_iff _ _).1 g21))
          (as_mem hpos hi6 ((hc_adjB_iff _ _).1 g61)) hcc1
          (sem_mem_W.1 heu1_4).1 (sem_W_and hS heu1_4) heu1_1 heu1_n026.1 heu1_n026.2.1 heu1_n026.2.2
          (sem_mem_W.1 heu2_9).1 (sem_W_and hS heu2_9) heu2_1 heu2_n026.1 heu2_n026.2.1 heu2_n026.2.2
        have h'1 : e0.1 = eu2.1 := by simpa [sem_bar] using congrArg Prod.fst h'
        omega
      · by_cases h7in : x7 ∈ supp 10 D (src D (sem_bar e0_9))
        · have hand_e09 : tag D e0_9.1 = true := sem_W_and hS he09_9
          have hb7 : sem_bar e0_9 ∈ sem_W 10 D x7 :=
            zm_mem hS hM7 (e := sem_bar e0_9) (sem_mem_W.1 he09_9).1 hand_e09 h7in
          have hbe09_eq : sem_bar e0_9 = g7 := by
            rcases hW7_all (sem_bar e0_9) hb7 with h1' | h1' | h1' | h1'
            · exact absurd (as_priv hpos hi0 (x := x9) (by rw [← h1', sem_bar_bar]; exact he09_9)) (fun heq => hx9n (heq ▸ hi0'))
            · exact absurd (as_priv hpos hi2 (x := x9) (by rw [← h1', sem_bar_bar]; exact he09_9)) (fun heq => hx9n (heq ▸ hi2'))
            · exact absurd (as_priv hpos hi6 (x := x9) (by rw [← h1', sem_bar_bar]; exact he09_9)) (fun heq => hx9n (heq ▸ hi6'))
            · exact h1'
          have he09_5 : x5 ∈ supp 10 D (src D e0_9) := by
            have : e0_9 = sem_bar g7 := by rw [← hbe09_eq, sem_bar_bar]
            rw [this]; exact (sem_mem_W.1 hbg7_5).2.1
          exact exp3_kill h hD (sem_adjB_false.1 n14) (sem_adjB_false.1 n15) (sem_adjB_false.1 n45)
            (Or.inr (Or.inl (adj_symm ((hc_adjB_iff _ _).1 g49)))) (fun e he => by
              rcases hW9_all e he with rfl | rfl | rfl
              · exact Or.inl hpos_1.2.2
              · exact Or.inl heu2_1
              · exact Or.inr (Or.inr he09_5))
        · obtain ⟨j2, s2, hj2, hle2, h9js, h7js⟩ :=
            meeting_le hS (hbar_val he09_9 he09_v97) (hbar_notsupp he09_9) h7in
          have hlt_e09 : j2 < e0_9.1 := by
            have hsrc := sem_src_lt hS (sem_mem_W.1 he09_9).1 (sem_bar e0_9).2
            change src D (sem_bar e0_9) < 10 + e0_9.1 at hsrc; omega
          have hjs2_eq : (j2, s2) = eu2 := by
            rcases hW9_all (j2, s2) h9js with h1' | h1' | h1'
            · have hbar7 : sem_bar (pos i6) ∈ sem_W 10 D x7 := by rw [← h1']; exact h7js
              exact absurd (as_priv hpos hi6 hbar7) (fun heq => hx7n (heq ▸ hi6'))
            · exact h1'
            · have := congrArg Prod.fst h1'; omega
          have hb_eu2_7 : sem_bar eu2 ∈ sem_W 10 D x7 := by rw [← hjs2_eq]; exact h7js
          have heu2_n026 := hneq_pos_fst hx7n (sem_mem_W.1 hb_eu2_7).2.1 heu2_1
          have hcc1 : (sem_W 10 D 1).card + (merges 10 D (carrierT 10 D {1})).card ≤ 4 := by
            have := cc_le h hD br hbp 1; rw [hru1, Finset.card_pair huab] at this; omega
          have heq12 := o3a_one_at_most_one hS hpos hi0 hi2 hi6 hi02 hi06 hi26
            (as_mem hpos hi0 ((hc_adjB_iff _ _).1 g01)) (as_mem hpos hi2 ((hc_adjB_iff _ _).1 g21))
            (as_mem hpos hi6 ((hc_adjB_iff _ _).1 g61)) hcc1
            (sem_mem_W.1 heu1_4).1 (sem_W_and hS heu1_4) heu1_1 heu1_n026.1 heu1_n026.2.1 heu1_n026.2.2
            (sem_mem_W.1 heu2_9).1 (sem_W_and hS heu2_9) heu2_1 heu2_n026.1 heu2_n026.2.1 heu2_n026.2.2
          rcases sem_same_gate heq12 with heq | hbar
          · have hg3_7 : x7 ∈ supp 10 D (src D g3) := by
              rw [← hbeu1_eq_g3, ← heq]; exact (sem_mem_W.1 hb_eu2_7).2.1
            exact exp3_kill h hD (sem_adjB_false.1 n14) (sem_adjB_false.1 n17) (sem_adjB_false.1 n47)
              (Or.inr (Or.inl ((hc_adjB_iff _ _).1 g34))) (fun e he => by
                rcases hW3_all e he with rfl | rfl | rfl | rfl
                · exact Or.inl hpos_1.1
                · exact Or.inl hpos_1.2.1
                · exact Or.inl hpos_1.2.2
                · exact Or.inr (Or.inr hg3_7))
          · exact hnot_g3_1 (by rw [← hbeu1_eq_g3, ← hbar]; exact heu2_1)
    · obtain ⟨j2, s2, hj2, hle2, h4js, h9js⟩ :=
        meeting_le hS (hbar_val he0_4 he0_v49) (hbar_notsupp he0_4) h9in
      have hlt_e0' : j2 < e0.1 := by
        have hsrc := sem_src_lt hS (sem_mem_W.1 he0_4).1 (sem_bar e0).2
        change src D (sem_bar e0) < 10 + e0.1 at hsrc; omega
      have hjs2_eq : (j2, s2) = eu1 := by
        rcases hW4_all (j2, s2) h4js with h' | h' | h'
        · have hbar9 : sem_bar (pos i0) ∈ sem_W 10 D x9 := by rw [← h']; exact h9js
          exact absurd (as_priv hpos hi0 hbar9) (fun heq => hx9n (heq ▸ hi0'))
        · exact h'
        · have := congrArg Prod.fst h'; omega
      have hg3_in_9 : g3 ∈ sem_W 10 D x9 := by rw [← hbeu1_eq_g3, ← hjs2_eq]; exact h9js
      have hg3_eq_e09 : g3 = e0_9 := by
        rcases hW9_all g3 hg3_in_9 with h' | h' | h'
        · exact absurd (as_priv hpos hi6 (x := x4) (by rw [← h', ← hbeu1_eq_g3, sem_bar_bar]; exact heu1_4)) (fun heq => hx4n (heq ▸ hi6'))
        · exact absurd (h' ▸ heu2_1) hnot_g3_1
        · exact h'
      exact exp3_kill h hD (sem_adjB_false.1 n13) (sem_adjB_false.1 n17) (sem_adjB_false.1 n37)
        (Or.inr (Or.inr ((hc_adjB_iff _ _).1 g97))) (fun e he => by
          rcases hW9_all e he with rfl | rfl | rfl
          · exact Or.inl hpos_1.2.2
          · exact Or.inl heu2_1
          · exact Or.inr (Or.inl (hg3_eq_e09 ▸ (sem_mem_W.1 hg3).2.1)))

theorem c6_code_z0 (code : Fin 6 → Nat) (hlt : ∀ k : Fin 6, code k < 4)
    (he_ok : ∀ k : Fin 6, code k ≠ 0 ∨ code ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩ ≠ 0)
    (hnp : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 → code j ≠ 0 → code j ≠ code k)
    (hz3 : ∀ j k : Fin 6, code j = 0 → j.val % 3 ≠ k.val % 3 → code k ≠ 3)
    (hs0 : code 0 = 0 ∨ code 3 = 0) :
    (code 0 = 0 ∨ code 0 = 3) ∧ (code 3 = 0 ∨ code 3 = 3) ∧
      ((code 1 = 1 ∧ code 4 = 1 ∧ code 2 = 2 ∧ code 5 = 2) ∨
       (code 1 = 2 ∧ code 4 = 2 ∧ code 2 = 1 ∧ code 5 = 1)) := by
  have hl0 := hlt 0; have hl1 := hlt 1; have hl2 := hlt 2; have hl3 := hlt 3; have hl4 := hlt 4; have hl5 := hlt 5
  have e0 : code 0 ≠ 0 ∨ code 1 ≠ 0 := he_ok 0
  have e2 : code 2 ≠ 0 ∨ code 3 ≠ 0 := he_ok 2
  have e3 : code 3 ≠ 0 ∨ code 4 ≠ 0 := he_ok 3
  have e5 : code 5 ≠ 0 ∨ code 0 ≠ 0 := he_ok 5
  have hc1 : code 1 ≠ 3 := hs0.elim (fun h0 => hz3 0 1 h0 (by decide)) (fun h3 => hz3 3 1 h3 (by decide))
  have hc2 : code 2 ≠ 3 := hs0.elim (fun h0 => hz3 0 2 h0 (by decide)) (fun h3 => hz3 3 2 h3 (by decide))
  have hc4 : code 4 ≠ 3 := hs0.elim (fun h0 => hz3 0 4 h0 (by decide)) (fun h3 => hz3 3 4 h3 (by decide))
  have hc5 : code 5 ≠ 3 := hs0.elim (fun h0 => hz3 0 5 h0 (by decide)) (fun h3 => hz3 3 5 h3 (by decide))
  have h14_n0 : code 1 ≠ 0 ∧ code 4 ≠ 0 := by
    rcases hs0 with h0 | h3
    · have h1 : code 1 ≠ 0 := e0.resolve_left (not_not.2 h0)
      have h5 : code 5 ≠ 0 := e5.resolve_right (not_not.2 h0)
      have h15 : code 1 ≠ code 5 := hnp 1 5 (by decide) h1
      have h4n0 : code 4 ≠ 0 := fun h4 => by
        have h3n0 : code 3 ≠ 0 := e3.resolve_right (not_not.2 h4)
        have h3n3 : code 3 ≠ 3 := hz3 4 3 h4 (by decide)
        have h31 := hnp 3 1 (by decide) h3n0; have h35 := hnp 3 5 (by decide) h3n0; omega
      exact ⟨h1, h4n0⟩
    · have h4 : code 4 ≠ 0 := e3.resolve_left (not_not.2 h3)
      have h2 : code 2 ≠ 0 := e2.resolve_right (not_not.2 h3)
      have h42 : code 4 ≠ code 2 := hnp 4 2 (by decide) h4
      have h1n0 : code 1 ≠ 0 := fun h1 => by
        have h0n0 : code 0 ≠ 0 := e0.resolve_right (not_not.2 h1)
        have h0n3 : code 0 ≠ 3 := hz3 1 0 h1 (by decide)
        have h04 := hnp 0 4 (by decide) h0n0; have h02 := hnp 0 2 (by decide) h0n0; omega
      exact ⟨h1n0, h4⟩
  have h25_n0 : code 2 ≠ 0 ∧ code 5 ≠ 0 := by
    rcases hs0 with h0 | h3
    · have h1 : code 1 ≠ 0 := h14_n0.1
      have h5 : code 5 ≠ 0 := e5.resolve_right (not_not.2 h0)
      have h15 : code 1 ≠ code 5 := hnp 1 5 (by decide) h1
      have h2n0 : code 2 ≠ 0 := fun h2 => by
        have h3n0 : code 3 ≠ 0 := e2.resolve_left (not_not.2 h2)
        have h3n3 : code 3 ≠ 3 := hz3 2 3 h2 (by decide)
        have h31 := hnp 3 1 (by decide) h3n0; have h35 := hnp 3 5 (by decide) h3n0; omega
      exact ⟨h2n0, h5⟩
    · have h4 : code 4 ≠ 0 := h14_n0.2
      have h2 : code 2 ≠ 0 := e2.resolve_right (not_not.2 h3)
      have h42 : code 4 ≠ code 2 := hnp 4 2 (by decide) h4
      have h5n0 : code 5 ≠ 0 := fun h5 => by
        have h0n0 : code 0 ≠ 0 := e5.resolve_left (not_not.2 h5)
        have h0n3 : code 0 ≠ 3 := hz3 5 0 h5 (by decide)
        have h04 := hnp 0 4 (by decide) h0n0; have h02 := hnp 0 2 (by decide) h0n0; omega
      exact ⟨h2, h5n0⟩
  have h12 := hnp 1 2 (by decide) h14_n0.1; have h15 := hnp 1 5 (by decide) h14_n0.1
  have h42 := hnp 4 2 (by decide) h14_n0.2; have h45 := hnp 4 5 (by decide) h14_n0.2
  have h01 := hnp 1 0 (by decide) h14_n0.1; have h02 := hnp 2 0 (by decide) h25_n0.1
  have h31 := hnp 1 3 (by decide) h14_n0.1; have h32 := hnp 2 3 (by decide) h25_n0.1
  refine ⟨?_, ?_, ?_⟩
  · by_cases h00 : code 0 = 0
    · exact Or.inl h00
    · exact Or.inr (by omega)
  · by_cases h30 : code 3 = 0
    · exact Or.inl h30
    · exact Or.inr (by omega)
  · by_cases h11 : code 1 = 1
    · exact Or.inl ⟨h11, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

theorem c6_code_z1 (code : Fin 6 → Nat) (hlt : ∀ k : Fin 6, code k < 4)
    (he_ok : ∀ k : Fin 6, code k ≠ 0 ∨ code ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩ ≠ 0)
    (hnp : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 → code j ≠ 0 → code j ≠ code k)
    (hz3 : ∀ j k : Fin 6, code j = 0 → j.val % 3 ≠ k.val % 3 → code k ≠ 3)
    (hs1 : code 1 = 0 ∨ code 4 = 0) :
    (code 1 = 0 ∨ code 1 = 3) ∧ (code 4 = 0 ∨ code 4 = 3) ∧
      ((code 2 = 1 ∧ code 5 = 1 ∧ code 3 = 2 ∧ code 0 = 2) ∨
       (code 2 = 2 ∧ code 5 = 2 ∧ code 3 = 1 ∧ code 0 = 1)) := by
  let r (k : Fin 6) : Fin 6 := k + 1
  let next (k : Fin 6) : Fin 6 := ⟨(k.val+1)%6,by omega⟩
  have hnext : ∀ k, next (r k) = r (next k) := by decide +kernel
  have hmod : ∀ j k, j.val % 3 ≠ k.val % 3 → (r j).val % 3 ≠ (r k).val % 3 := by decide +kernel
  apply c6_code_z0 (fun k => code (r k)) (fun k => hlt (r k)) ?_ ?_ ?_ hs1
  · intro k
    change code (r k) ≠ 0 ∨ code (r (next k)) ≠ 0
    rw [← hnext]
    exact he_ok (r k)
  · exact fun j k h => hnp (r j) (r k) (hmod j k h)
  · exact fun j k hj h => hz3 (r j) (r k) hj (hmod j k h)

theorem c6_code_z2 (code : Fin 6 → Nat) (hlt : ∀ k : Fin 6, code k < 4)
    (he_ok : ∀ k : Fin 6, code k ≠ 0 ∨ code ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩ ≠ 0)
    (hnp : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 → code j ≠ 0 → code j ≠ code k)
    (hz3 : ∀ j k : Fin 6, code j = 0 → j.val % 3 ≠ k.val % 3 → code k ≠ 3)
    (hs2 : code 2 = 0 ∨ code 5 = 0) :
    (code 2 = 0 ∨ code 2 = 3) ∧ (code 5 = 0 ∨ code 5 = 3) ∧
      ((code 3 = 1 ∧ code 0 = 1 ∧ code 4 = 2 ∧ code 1 = 2) ∨
       (code 3 = 2 ∧ code 0 = 2 ∧ code 4 = 1 ∧ code 1 = 1)) := by
  let r (k : Fin 6) : Fin 6 := k + 2
  let next (k : Fin 6) : Fin 6 := ⟨(k.val+1)%6,by omega⟩
  have hnext : ∀ k, next (r k) = r (next k) := by decide +kernel
  have hmod : ∀ j k, j.val % 3 ≠ k.val % 3 → (r j).val % 3 ≠ (r k).val % 3 := by decide +kernel
  apply c6_code_z0 (fun k => code (r k)) (fun k => hlt (r k)) ?_ ?_ ?_ hs2
  · intro k
    change code (r k) ≠ 0 ∨ code (r (next k)) ≠ 0
    rw [← hnext]
    exact he_ok (r k)
  · exact fun j k h => hnp (r j) (r k) (hmod j k h)
  · exact fun j k hj h => hz3 (r j) (r k) hj (hmod j k h)

theorem c6_code_pattern (code : Fin 6 → Nat) (hlt : ∀ k : Fin 6, code k < 4)
    (he_ok : ∀ k : Fin 6, code k ≠ 0 ∨ code ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩ ≠ 0)
    (hnp : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 → code j ≠ 0 → code j ≠ code k)
    (hz3 : ∀ j k : Fin 6, code j = 0 → j.val % 3 ≠ k.val % 3 → code k ≠ 3) :
    ((code 0 = 0 ∨ code 0 = 3) ∧ (code 3 = 0 ∨ code 3 = 3) ∧
      ((code 1 = 1 ∧ code 4 = 1 ∧ code 2 = 2 ∧ code 5 = 2) ∨
       (code 1 = 2 ∧ code 4 = 2 ∧ code 2 = 1 ∧ code 5 = 1))) ∨
    ((code 1 = 0 ∨ code 1 = 3) ∧ (code 4 = 0 ∨ code 4 = 3) ∧
      ((code 2 = 1 ∧ code 5 = 1 ∧ code 3 = 2 ∧ code 0 = 2) ∨
       (code 2 = 2 ∧ code 5 = 2 ∧ code 3 = 1 ∧ code 0 = 1))) ∨
    ((code 2 = 0 ∨ code 2 = 3) ∧ (code 5 = 0 ∨ code 5 = 3) ∧
      ((code 3 = 1 ∧ code 0 = 1 ∧ code 4 = 2 ∧ code 1 = 2) ∨
       (code 3 = 2 ∧ code 0 = 2 ∧ code 4 = 1 ∧ code 1 = 1))) := by
  by_cases hs0 : code 0 = 0 ∨ code 3 = 0
  · exact Or.inl (c6_code_z0 code hlt he_ok hnp hz3 hs0)
  · by_cases hs1 : code 1 = 0 ∨ code 4 = 0
    · exact Or.inr (Or.inl (c6_code_z1 code hlt he_ok hnp hz3 hs1))
    · by_cases hs2 : code 2 = 0 ∨ code 5 = 0
      · exact Or.inr (Or.inr (c6_code_z2 code hlt he_ok hnp hz3 hs2))
      · push Not at hs0 hs1 hs2
        have hl0 := hlt 0; have hl1 := hlt 1; have hl2 := hlt 2; have hl3 := hlt 3; have hl4 := hlt 4; have hl5 := hlt 5
        have n01 := hnp 0 1 (by decide) hs0.1; have n02 := hnp 0 2 (by decide) hs0.1
        have n12 := hnp 1 2 (by decide) hs1.1
        have n31 := hnp 3 1 (by decide) hs0.2; have n32 := hnp 3 2 (by decide) hs0.2
        have n40 := hnp 4 0 (by decide) hs1.2; have n42 := hnp 4 2 (by decide) hs1.2
        have n50 := hnp 5 0 (by decide) hs2.2; have n51 := hnp 5 1 (by decide) hs2.2
        by_cases c0 : code 0 = 3
        · left
          refine ⟨Or.inr c0, Or.inr (by omega), ?_⟩
          by_cases h11 : code 1 = 1
          · exact Or.inl ⟨h11, by omega, by omega, by omega⟩
          · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
        · by_cases c1 : code 1 = 3
          · right; left
            refine ⟨Or.inr c1, Or.inr (by omega), ?_⟩
            by_cases h21 : code 2 = 1
            · exact Or.inl ⟨h21, by omega, by omega, by omega⟩
            · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
          · right; right
            have c2 : code 2 = 3 := by omega
            refine ⟨Or.inr c2, Or.inr (by omega), ?_⟩
            by_cases h31 : code 3 = 1
            · exact Or.inl ⟨h31, by omega, by omega, by omega⟩
            · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

def c6V (k : Fin 6) : Fin 10 :=
  match k.val with | 0 => 3 | 1 => 4 | 2 => 9 | 3 => 7 | 4 => 5 | _ => 8

def c6I (k : Fin 6) : Fin 10 :=
  match k.val % 3 with | 0 => 2 | 1 => 0 | _ => 6

theorem c6_geom_adj : ∀ k : Fin 6,
    c6I k ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ c6V k ∉ ({0, 2, 6} : Finset (Fin 10)) ∧
    hc_adjB (c6I k) (c6V k) = true ∧ hc_adjB (c6I k) 1 = true := by decide +kernel

theorem c6_geom_edge : ∀ k : Fin 6,
    let k1 : Fin 6 := ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩
    let k5 : Fin 6 := ⟨(k.val + 5) % 6, Nat.mod_lt _ (by omega)⟩
    hc_adjB (c6V k) (c6V k1) = true ∧ hc_adjB (c6V k) (c6V k5) = true ∧
    c6V k5 ≠ c6V k1 ∧ c6V k1 ≠ 1 ∧ hc_adjB 1 (c6V k5) = false := by decide +kernel

theorem c6_geom_diff : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 →
    c6V j ≠ c6V k ∧ c6I j ≠ c6I k ∧ hc_adjB (c6I j) (c6V k) = false ∧ hc_adjB (c6I k) (c6V j) = false ∧
    (∃ q : Fin 10, hc_adjB (c6I j) q = true ∧ c6V j ≠ q ∧ hc_adjB (c6V k) q = false) ∧
    (∃ q : Fin 10, hc_adjB (c6I k) q = true ∧ c6V k ≠ q ∧ hc_adjB (c6V j) q = false) ∧
    (∃ q : Fin 10, hc_adjB (c6I j) q = true ∧ (1 : Fin 10) ≠ q ∧ hc_adjB (c6V k) q = false) := by
  decide +kernel

theorem c6_geom_1_to_k : ∀ k : Fin 6,
    c6V k ≠ 1 ∧
    (∃ q : Fin 10, hc_adjB 0 q = true ∧ (1 : Fin 10) ≠ q ∧ hc_adjB (c6V k) q = false) ∧
    (∃ q : Fin 10, hc_adjB 2 q = true ∧ (1 : Fin 10) ≠ q ∧ hc_adjB (c6V k) q = false) ∧
    (∃ q : Fin 10, hc_adjB 6 q = true ∧ (1 : Fin 10) ≠ q ∧ hc_adjB (c6V k) q = false) := by
  decide +kernel

theorem c6_geom_nb_e : ∀ k : Fin 6,
    ∃ v : Fin 10, v ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ hc_adjB (c6V k) v = true := by
  decide +kernel

def o3aCoreGeom (i0 i2 i6 x3 x4 x9 x7 x5 x8 : Fin 10) : Prop :=
  i0 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ i2 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ i6 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧
  i0 ≠ i2 ∧ i0 ≠ i6 ∧ i2 ≠ i6 ∧
  x3 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x4 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x9 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧
  x7 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x5 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x8 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧
  hc_adjB i0 1 = true ∧ hc_adjB i2 1 = true ∧ hc_adjB i6 1 = true ∧
  hc_adjB i0 x4 = true ∧ hc_adjB i0 x5 = true ∧ hc_adjB i2 x3 = true ∧ hc_adjB i2 x7 = true ∧
  hc_adjB i6 x8 = true ∧ hc_adjB i6 x9 = true ∧
  hc_adjB x3 x4 = true ∧ hc_adjB x4 x9 = true ∧ hc_adjB x9 x7 = true ∧
  hc_adjB x7 x5 = true ∧ hc_adjB x5 x8 = true ∧ hc_adjB x8 x3 = true ∧
  hc_adjB i0 x3 = false ∧ hc_adjB i0 x7 = false ∧ hc_adjB i0 x8 = false ∧ hc_adjB i0 x9 = false ∧
  hc_adjB i2 x4 = false ∧ hc_adjB i2 x5 = false ∧ hc_adjB i2 x8 = false ∧ hc_adjB i2 x9 = false ∧
  hc_adjB i6 x3 = false ∧ hc_adjB i6 x4 = false ∧ hc_adjB i6 x5 = false ∧ hc_adjB i6 x7 = false ∧
  hc_adjB x5 x3 = false ∧ hc_adjB x5 x9 = false ∧ hc_adjB x8 x4 = false ∧ hc_adjB x8 x7 = false ∧
  hc_adjB x3 x9 = false ∧ hc_adjB x4 x7 = false ∧ hc_adjB x3 x5 = false ∧ hc_adjB x7 x8 = false ∧
  hc_adjB 1 x3 = false ∧ hc_adjB 1 x4 = false ∧ hc_adjB 1 x5 = false ∧ hc_adjB 1 x7 = false ∧ hc_adjB 1 x8 = false ∧ hc_adjB 1 x9 = false ∧
  hc_adjB x4 x5 = false ∧ hc_adjB x8 x9 = false ∧ hc_adjB x3 x7 = false ∧
  x3 ≠ 1 ∧ x4 ≠ 1 ∧ x5 ≠ 1 ∧ x7 ≠ 1 ∧ x8 ≠ 1 ∧ x9 ≠ 1 ∧
  x4 ≠ x5 ∧ x8 ≠ x9 ∧ x3 ≠ x4 ∧ x4 ≠ x9 ∧ x9 ≠ x7 ∧ x7 ≠ x5 ∧ x5 ≠ x8 ∧ x8 ≠ x3 ∧ x3 ≠ x7 ∧ x4 ≠ x8 ∧ x9 ≠ x5 ∧ x3 ≠ x9 ∧ x4 ≠ x7 ∧ x3 ≠ x5 ∧ x7 ≠ x8

theorem o3a_geom_mk (i0 i2 i6 x3 x4 x9 x7 x5 x8 : Fin 10)
    (h1 : i0 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ i2 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧ i6 ∈ ({0, 2, 6} : Finset (Fin 10)) ∧
      i0 ≠ i2 ∧ i0 ≠ i6 ∧ i2 ≠ i6 ∧
      x3 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x4 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x9 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧
      x7 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x5 ∉ ({0, 2, 6} : Finset (Fin 10)) ∧ x8 ∉ ({0, 2, 6} : Finset (Fin 10)))
    (h2 : hc_adjB i0 1 = true ∧ hc_adjB i2 1 = true ∧ hc_adjB i6 1 = true ∧
      hc_adjB i0 x4 = true ∧ hc_adjB i0 x5 = true ∧ hc_adjB i2 x3 = true ∧ hc_adjB i2 x7 = true ∧
      hc_adjB i6 x8 = true ∧ hc_adjB i6 x9 = true ∧
      hc_adjB x3 x4 = true ∧ hc_adjB x4 x9 = true ∧ hc_adjB x9 x7 = true ∧
      hc_adjB x7 x5 = true ∧ hc_adjB x5 x8 = true ∧ hc_adjB x8 x3 = true)
    (h3 : hc_adjB i0 x3 = false ∧ hc_adjB i0 x7 = false ∧ hc_adjB i0 x8 = false ∧ hc_adjB i0 x9 = false ∧
      hc_adjB i2 x4 = false ∧ hc_adjB i2 x5 = false ∧ hc_adjB i2 x8 = false ∧ hc_adjB i2 x9 = false ∧
      hc_adjB i6 x3 = false ∧ hc_adjB i6 x4 = false ∧ hc_adjB i6 x5 = false ∧ hc_adjB i6 x7 = false ∧
      hc_adjB x5 x3 = false ∧ hc_adjB x5 x9 = false ∧ hc_adjB x8 x4 = false ∧ hc_adjB x8 x7 = false)
    (h4 : hc_adjB x3 x9 = false ∧ hc_adjB x4 x7 = false ∧ hc_adjB x3 x5 = false ∧ hc_adjB x7 x8 = false ∧
      hc_adjB 1 x3 = false ∧ hc_adjB 1 x4 = false ∧ hc_adjB 1 x5 = false ∧ hc_adjB 1 x7 = false ∧ hc_adjB 1 x8 = false ∧ hc_adjB 1 x9 = false ∧
      hc_adjB x4 x5 = false ∧ hc_adjB x8 x9 = false ∧ hc_adjB x3 x7 = false)
    (h5 : x3 ≠ 1 ∧ x4 ≠ 1 ∧ x5 ≠ 1 ∧ x7 ≠ 1 ∧ x8 ≠ 1 ∧ x9 ≠ 1 ∧
      x4 ≠ x5 ∧ x8 ≠ x9 ∧ x3 ≠ x4 ∧ x4 ≠ x9)
    (h6 : x9 ≠ x7 ∧ x7 ≠ x5 ∧ x5 ≠ x8 ∧ x8 ≠ x3 ∧ x3 ≠ x7 ∧ x4 ≠ x8 ∧ x9 ≠ x5 ∧ x3 ≠ x9 ∧ x4 ≠ x7 ∧ x3 ≠ x5 ∧ x7 ≠ x8) :
    o3aCoreGeom i0 i2 i6 x3 x4 x9 x7 x5 x8 := by
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  rcases h3 with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩
  rcases h4 with ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩
  rcases h5 with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩
  rcases h6 with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16,
    d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩

theorem o3a_geom_0 : o3aCoreGeom 0 2 6 3 4 9 7 5 8 :=
  o3a_geom_mk 0 2 6 3 4 9 7 5 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem o3a_geom_1 : o3aCoreGeom 6 0 2 4 9 7 5 8 3 :=
  o3a_geom_mk 6 0 2 4 9 7 5 8 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem o3a_geom_2 : o3aCoreGeom 2 6 0 9 7 5 8 3 4 :=
  o3a_geom_mk 2 6 0 9 7 5 8 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem elim_O3a {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h9 : totalSurplus 10 D ≤ 9)
    (hI : ineligSet 10 D = {0, 2, 6}) : False := by
  classical
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hel := inelig_card_add 10 D
  have hts := totalSurplus_split 10 D
  have hI3 : (ineligSet 10 D).card = 3 := by rw [hI]; decide
  have hE7 : (eligSet 10 D).card = 7 := by omega
  have hBp_ge := elig_le_Bplus hS br hbp
  have hm : ∀ v : Fin 10, v ∈ ({0, 2, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 2, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 2, 6} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hI ▸ sem_mem_inelig.2 hc)
  have h1_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 2 (by decide)) (u := 1) (v := 6) (by decide)
  have hru1_ne : (ru D br 1).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbp 1; omega)
  have hpe1_ge4 : ∀ k : Fin 6, ru D br 1 ⊆ ru D br (c6V k) → 4 ≤ (sem_W 10 D (c6V k)).card := by
    intro k hsub
    obtain ⟨u, hu⟩ := hru1_ne
    have hres : ∀ u' ∈ residualUnits 10 D br, (1 : Fin 10) ∈ supp 10 D u'.1 → c6V k ∈ supp 10 D u'.1 :=
      fun u' hu' h1' => (mem_ru.1 (hsub (mem_ru.2 ⟨hu', h1'⟩))).2
    have hw : (1 : Fin 10) ∈ supp 10 D u.1 ∧ c6V k ∈ supp 10 D u.1 := ⟨(mem_ru.1 hu).2, (mem_ru.1 (hsub hu)).2⟩
    obtain ⟨hk1, ⟨q0, gq0, h1q0, hkq0⟩, ⟨q2, gq2, h1q2, hkq2⟩, ⟨q6, gq6, h1q6, hkq6⟩⟩ := c6_geom_1_to_k k
    have hp0 := mem_W_of_pos hpos (hm 0 (by decide))
      (pe_co_g10 h hD br hbp hpos (hm 0 (by decide)) (helig 1 (by decide)) hres hw ⟨petersen_deg3 1, by decide, gq0, hk1.symm, h1q0, hkq0⟩)
    have hp2 := mem_W_of_pos hpos (hm 2 (by decide))
      (pe_co_g10 h hD br hbp hpos (hm 2 (by decide)) (helig 1 (by decide)) hres hw ⟨petersen_deg3 1, by decide, gq2, hk1.symm, h1q2, hkq2⟩)
    have hp6 := mem_W_of_pos hpos (hm 6 (by decide))
      (pe_co_g10 h hD br hbp hpos (hm 6 (by decide)) (helig 1 (by decide)) hres hw ⟨petersen_deg3 1, by decide, gq6, hk1.symm, h1q6, hkq6⟩)
    obtain ⟨v, hvn, gkv⟩ := c6_geom_nb_e k
    obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gkv)
    exact pa_card4 hp0 hp2 hp6 hev
      (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 2 (by decide)) e) (by decide))
      (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 6 (by decide)) e) (by decide))
      (fun e => hn v hvn (hfv _ (hm 0 (by decide)) e.symm ▸ hm 0 (by decide)))
      (fun e => absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 6 (by decide)) e) (by decide))
      (fun e => hn v hvn (hfv _ (hm 2 (by decide)) e.symm ▸ hm 2 (by decide)))
      (fun e => hn v hvn (hfv _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide)))
  have hc6_edge_ne : ∀ k : Fin 6,
      ru D br (c6V k) ≠ ∅ ∨ ru D br (c6V ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩) ≠ ∅ := by
    intro k
    let k1 : Fin 6 := ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩
    let k5 : Fin 6 := ⟨(k.val + 5) % 6, Nat.mod_lt _ (by omega)⟩
    by_contra hc; push Not at hc
    have hwk : (sem_W 10 D (c6V k)).card ≤ 2 := by have := cc_le h hD br hbp (c6V k); rw [hc.1, Finset.card_empty] at this; omega
    have hwk1 : (sem_W 10 D (c6V k1)).card ≤ 2 := by have := cc_le h hD br hbp (c6V k1); rw [hc.2, Finset.card_empty] at this; omega
    obtain ⟨hi_k, hv_k, gik, -⟩ := c6_geom_adj k
    obtain ⟨hi_k1, hv_k1, gik1, g1k1⟩ := c6_geom_adj k1
    obtain ⟨-, hv_k5, -, -⟩ := c6_geom_adj k5
    obtain ⟨ge1, ge5, h51, hk1_1, n15⟩ := c6_geom_edge k
    exact pa_m1_gen h hD hpos (c6V k) (c6V k1) (c6V k5) (c6I k) (c6I k1) 1
      (hm _ hi_k) (hm _ hi_k1) (hn _ hv_k) (hn _ hv_k1) (hn _ hv_k5)
      ⟨gik, gik1, ge1, ge5, h51, petersen_deg3 _, g1k1, hk1_1.symm, n15⟩ hwk hwk1
  by_cases hB7 : Bplus 10 D ≤ 7
  · have hres : residualUnits 10 D br = ∅ := Finset.card_eq_zero.1 (by have := card_residual hS br hbp; omega)
    obtain ⟨u, hu⟩ := hru1_ne; exact Finset.notMem_empty u (hres ▸ (mem_ru.1 hu).1)
  · by_cases hB8 : Bplus 10 D = 8
    · have hR1 : (residualUnits 10 D br).card = 1 := by have := card_residual hS br hbp; omega
      have hru1_eq : ru D br 1 = residualUnits 10 D br :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR1]; exact Finset.card_pos.2 hru1_ne)
      rcases hc6_edge_ne ⟨0, by decide⟩ with hne | hne
      · have hsub : ru D br 1 ⊆ ru D br (c6V ⟨0, by decide⟩) := by
          rw [hru1_eq]; exact (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
            (by rw [hR1]; exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne))).symm.subset
        have h4 := hpe1_ge4 ⟨0, by decide⟩ hsub
        have hcc := cc_le h hD br hbp (c6V ⟨0, by decide⟩)
        have hle1 : (ru D br (c6V ⟨0, by decide⟩)).card ≤ (residualUnits 10 D br).card := Finset.card_le_card (Finset.filter_subset _ _)
        omega
      · have hsub : ru D br 1 ⊆ ru D br (c6V ⟨1, by decide⟩) := by
          rw [hru1_eq]; exact (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
            (by rw [hR1]; exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne))).symm.subset
        have h4 := hpe1_ge4 ⟨1, by decide⟩ hsub
        have hcc := cc_le h hD br hbp (c6V ⟨1, by decide⟩)
        have hle1 : (ru D br (c6V ⟨1, by decide⟩)).card ≤ (residualUnits 10 D br).card := Finset.card_le_card (Finset.filter_subset _ _)
        omega
    · have hB0 : Bzero 10 D = 0 := by omega
      have hR2 : (residualUnits 10 D br).card = 2 := by have := card_residual hS br hbp; omega
      obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
      have hc6_pair_ru1 : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 →
          ∀ u0 : Σ _ : ℕ, ℕ, ru D br (c6V j) = {u0} → ru D br (c6V k) = {u0} → False := by
        intro j k hmod u0 hrj hrk
        obtain ⟨hjk, hijk, nij, nji, ⟨qj, gqj, hvjq, hvkq⟩, ⟨qk, gqk, hvkqk, hvjqk⟩, -⟩ := c6_geom_diff j k hmod
        obtain ⟨hij, hvjn, gij, -⟩ := c6_geom_adj j
        obtain ⟨hik, hvkn, gik, -⟩ := c6_geom_adj k
        have hres_jk : ∀ u' ∈ residualUnits 10 D br, c6V j ∈ supp 10 D u'.1 → c6V k ∈ supp 10 D u'.1 :=
          fun u' hu' hj' => (mem_ru.1 (hrk ▸ (hrj ▸ mem_ru.2 ⟨hu', hj'⟩))).2
        have hres_kj : ∀ u' ∈ residualUnits 10 D br, c6V k ∈ supp 10 D u'.1 → c6V j ∈ supp 10 D u'.1 :=
          fun u' hu' hk' => (mem_ru.1 (hrj ▸ (hrk ▸ mem_ru.2 ⟨hu', hk'⟩))).2
        have hw : c6V j ∈ supp 10 D u0.1 ∧ c6V k ∈ supp 10 D u0.1 :=
          ⟨(mem_ru.1 (hrj ▸ Finset.mem_singleton_self u0)).2, (mem_ru.1 (hrk ▸ Finset.mem_singleton_self u0)).2⟩
        have hpj_k := mem_W_of_pos hpos (hm _ hij)
          (pe_co_g10 h hD br hbp hpos (hm _ hij) (helig _ hvjn) hres_jk hw ⟨petersen_deg3 _, gij, gqj, hjk, hvjq, hvkq⟩)
        have hj_in_pk := pe_co_g10 h hD br hbp hpos (hm _ hik) (helig _ hvkn) hres_kj ⟨hw.2, hw.1⟩ ⟨petersen_deg3 _, gik, gqk, hjk.symm, hvkqk, hvjqk⟩
        have hpk_k := as_mem hpos (hm _ hik) ((hc_adjB_iff _ _).1 gik)
        obtain ⟨vk, hvkn', gkvk⟩ := c6_geom_nb_e k
        obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gkvk)
        have hWk_le3 : (sem_W 10 D (c6V k)).card ≤ 3 := by have := cc_le h hD br hbp (c6V k); rw [hrk, Finset.card_singleton] at this; omega
        have hWk := pa_three hpk_k hpj_k hev
          (fun e => hijk.symm (hpos.2 _ (hm _ hik) _ (hm _ hij) e))
          (fun e => hn vk hvkn' (hfv _ (hm _ hik) e.symm ▸ hm _ hik))
          (fun e => hn vk hvkn' (hfv _ (hm _ hij) e.symm ▸ hm _ hij)) hWk_le3
        have hfull := full_g10 h hD hB0 hpos (hm _ hik) ((hc_adjB_iff _ _).1 gik) (fun p hp hne1 hsub' => by
          rcases hWk p hp with rfl | rfl | rfl
          · exact hne1 rfl
          · exact hijk (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm _ hij))))
          · exact hn vk hvkn' (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbev).2.1) ▸ hm _ hik))
        exact sem_adjB_false.1 nji ((hfull (c6V j)).1 hj_in_pk)
      by_cases h1c : (ru D br 1).card = 1
      · obtain ⟨ua, hua⟩ := Finset.card_eq_one.1 h1c
        have hua_in : ua ∈ residualUnits 10 D br := (mem_ru.1 (hua ▸ Finset.mem_singleton_self ua)).1
        have hother_card : ((residualUnits 10 D br).erase ua).card = 1 := by rw [Finset.card_erase_of_mem hua_in, hR2]
        obtain ⟨ub, hub⟩ := Finset.card_eq_one.1 hother_card
        have hall_ub : ∀ k : Fin 6, ru D br (c6V k) ≠ ∅ → ru D br (c6V k) = {ub} := by
          intro k hne
          have hnot := w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 2 (by decide))
            (x := 1) (v := 6) (by decide) hua (petersen_w3_bad_eq 1 0 2 (c6V k) (by decide) (by decide) (by decide) (c6_geom_1_to_k k).1)
          have hsub : ru D br (c6V k) ⊆ {ub} := fun u hu => by
            rw [← hub]; exact Finset.mem_erase.2 ⟨fun heq => hnot (heq ▸ (mem_ru.1 hu).2), (mem_ru.1 hu).1⟩
          exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne))
        rcases hc6_edge_ne ⟨0, by decide⟩ with h0 | h1 <;>
        rcases hc6_edge_ne ⟨2, by decide⟩ with h2 | h3 <;>
        rcases hc6_edge_ne ⟨4, by decide⟩ with h4 | h5
        · exact hc6_pair_ru1 ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) ub (hall_ub _ h0) (hall_ub _ h2)
        · exact hc6_pair_ru1 ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) ub (hall_ub _ h0) (hall_ub _ h2)
        · exact hc6_pair_ru1 ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide) ub (hall_ub _ h0) (hall_ub _ h4)
        · exact hc6_pair_ru1 ⟨0, by decide⟩ ⟨5, by decide⟩ (by decide) ub (hall_ub _ h0) (hall_ub _ h5)
        · exact hc6_pair_ru1 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) ub (hall_ub _ h1) (hall_ub _ h2)
        · exact hc6_pair_ru1 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) ub (hall_ub _ h1) (hall_ub _ h2)
        · exact hc6_pair_ru1 ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide) ub (hall_ub _ h1) (hall_ub _ h3)
        · exact hc6_pair_ru1 ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide) ub (hall_ub _ h1) (hall_ub _ h3)
      · have hru1_full : ru D br 1 = {u1, u2} := by
          have hle2 : (ru D br 1).card ≤ 2 := by rw [← hR2]; exact Finset.card_le_card (Finset.filter_subset _ _)
          have hpos1 := Finset.card_pos.2 hru1_ne
          rw [← hReq]; exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
        have hc6_pair_R : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 →
            ru D br (c6V j) = {u1, u2} → ru D br (c6V k) = {u1, u2} → False := by
          intro j k hmod hrj hrk
          obtain ⟨hjk, hijk, nij, -, ⟨qj, gqj, hvjq, hvkq⟩, -, -⟩ := c6_geom_diff j k hmod
          obtain ⟨hij, hvjn, gij, -⟩ := c6_geom_adj j
          have hres1j : ∀ u' ∈ residualUnits 10 D br, (1 : Fin 10) ∈ supp 10 D u'.1 → c6V j ∈ supp 10 D u'.1 :=
            fun u' hu' _ => (mem_ru.1 (hrj ▸ (hReq ▸ hu'))).2
          have hw1j : (1 : Fin 10) ∈ supp 10 D u1.1 ∧ c6V j ∈ supp 10 D u1.1 :=
            ⟨(mem_ru.1 (hru1_full ▸ Finset.mem_insert_self u1 {u2})).2, (mem_ru.1 (hrj ▸ Finset.mem_insert_self u1 {u2})).2⟩
          obtain ⟨hj1, ⟨q0, gq0, h1q0, hjq0⟩, ⟨q2, gq2, h1q2, hjq2⟩, ⟨q6, gq6, h1q6, hjq6⟩⟩ := c6_geom_1_to_k j
          have hp0 := mem_W_of_pos hpos (hm 0 (by decide))
            (pe_co_g10 h hD br hbp hpos (hm 0 (by decide)) (helig 1 (by decide)) hres1j hw1j ⟨petersen_deg3 1, by decide, gq0, hj1.symm, h1q0, hjq0⟩)
          have hp2 := mem_W_of_pos hpos (hm 2 (by decide))
            (pe_co_g10 h hD br hbp hpos (hm 2 (by decide)) (helig 1 (by decide)) hres1j hw1j ⟨petersen_deg3 1, by decide, gq2, hj1.symm, h1q2, hjq2⟩)
          have hp6 := mem_W_of_pos hpos (hm 6 (by decide))
            (pe_co_g10 h hD br hbp hpos (hm 6 (by decide)) (helig 1 (by decide)) hres1j hw1j ⟨petersen_deg3 1, by decide, gq6, hj1.symm, h1q6, hjq6⟩)
          obtain ⟨vj, hvjn', gjvj⟩ := c6_geom_nb_e j
          obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gjvj)
          have hWj_le4 : (sem_W 10 D (c6V j)).card ≤ 4 := by have := cc_le h hD br hbp (c6V j); rw [hrj, Finset.card_pair hu12] at this; omega
          have hWj := pa_four hp0 hp2 hp6 hev
            (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 2 (by decide)) e) (by decide))
            (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 6 (by decide)) e) (by decide))
            (fun e => hn vj hvjn' (hfv _ (hm 0 (by decide)) e.symm ▸ hm 0 (by decide)))
            (fun e => absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 6 (by decide)) e) (by decide))
            (fun e => hn vj hvjn' (hfv _ (hm 2 (by decide)) e.symm ▸ hm 2 (by decide)))
            (fun e => hn vj hvjn' (hfv _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide))) hWj_le4
          have hfull := full_g10 h hD hB0 hpos (hm _ hij) ((hc_adjB_iff _ _).1 gij) (fun p hp hne1 hsub' => by
            rcases hWj p hp with rfl | rfl | rfl | rfl
            · exact hne1 (by have : c6I j = 0 := (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm 0 (by decide))))).symm; rw [this])
            · exact hne1 (by have : c6I j = 2 := (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm 2 (by decide))))).symm; rw [this])
            · exact hne1 (by have : c6I j = 6 := (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos (hm 6 (by decide))))).symm; rw [this])
            · exact hn vj hvjn' (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbev).2.1) ▸ hm _ hij))
          have hresjk : ∀ u' ∈ residualUnits 10 D br, c6V j ∈ supp 10 D u'.1 → c6V k ∈ supp 10 D u'.1 :=
            fun u' hu' _ => (mem_ru.1 (hrk ▸ (hReq ▸ hu'))).2
          have hwjk : c6V j ∈ supp 10 D u1.1 ∧ c6V k ∈ supp 10 D u1.1 :=
            ⟨(mem_ru.1 (hrj ▸ Finset.mem_insert_self u1 {u2})).2, (mem_ru.1 (hrk ▸ Finset.mem_insert_self u1 {u2})).2⟩
          have hk_in_pj := pe_co_g10 h hD br hbp hpos (hm _ hij) (helig _ hvjn) hresjk hwjk ⟨petersen_deg3 _, gij, gqj, hjk, hvjq, hvkq⟩
          exact sem_adjB_false.1 nij ((hfull (c6V k)).1 hk_in_pj)
        have hc6_zero_R : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 →
            ru D br (c6V j) = ∅ → ru D br (c6V k) = {u1, u2} → False := by
          intro j k hmod hrj hrk
          obtain ⟨-, -, nij, -, -, -, ⟨q, gq, h1q, hkq⟩⟩ := c6_geom_diff j k hmod
          obtain ⟨hij, hvjn, gij, gi1⟩ := c6_geom_adj j
          obtain ⟨vj, hvjn', gjvj⟩ := c6_geom_nb_e j
          have hWj2 : (sem_W 10 D (c6V j)).card ≤ 2 := by have := cc_le h hD br hbp (c6V j); rw [hrj, Finset.card_empty] at this; omega
          have hfull := full_of_le2 h hD hB0 hpos (hm _ hij) ((hc_adjB_iff _ _).1 gij) ((hc_adjB_iff _ _).1 gjvj) (hn vj hvjn') hWj2
          have hres1k : ∀ u' ∈ residualUnits 10 D br, (1 : Fin 10) ∈ supp 10 D u'.1 → c6V k ∈ supp 10 D u'.1 :=
            fun u' hu' _ => (mem_ru.1 (hrk ▸ (hReq ▸ hu'))).2
          have hw1k : (1 : Fin 10) ∈ supp 10 D u1.1 ∧ c6V k ∈ supp 10 D u1.1 :=
            ⟨(mem_ru.1 (hru1_full ▸ Finset.mem_insert_self u1 {u2})).2, (mem_ru.1 (hrk ▸ Finset.mem_insert_self u1 {u2})).2⟩
          have hk_in := pe_co_g10 h hD br hbp hpos (hm _ hij) (helig 1 (by decide)) hres1k hw1k
            ⟨petersen_deg3 1, gi1, gq, (c6_geom_1_to_k k).1.symm, h1q, hkq⟩
          exact sem_adjB_false.1 nij ((hfull (c6V k)).1 hk_in)
        let code : Fin 6 → Nat := fun k =>
          (if u1 ∈ ru D br (c6V k) then 1 else 0) + (if u2 ∈ ru D br (c6V k) then 2 else 0)
        have hcode_eq : ∀ k : Fin 6,
            (code k = 0 ↔ ru D br (c6V k) = ∅) ∧
            (code k = 1 ↔ ru D br (c6V k) = {u1}) ∧
            (code k = 2 ↔ ru D br (c6V k) = {u2}) ∧
            (code k = 3 ↔ ru D br (c6V k) = {u1, u2}) := by
          intro k
          have hsub : ru D br (c6V k) ⊆ {u1, u2} := hReq ▸ Finset.filter_subset _ _
          by_cases h1 : u1 ∈ ru D br (c6V k) <;> by_cases h2 : u2 ∈ ru D br (c6V k)
          · have h3 : ru D br (c6V k) = {u1, u2} := Finset.Subset.antisymm hsub (fun x hx => by
              rw [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl; exact h1; exact h2)
            have hc3 : code k = 3 := by dsimp only [code]; simp [h1, h2]
            refine ⟨⟨by omega, fun heq => absurd (heq ▸ h1) (Finset.notMem_empty _)⟩,
              ⟨by omega, fun heq => False.elim (hu12.symm (Finset.mem_singleton.1 (heq ▸ h2)))⟩,
              ⟨by omega, fun heq => False.elim (hu12 (Finset.mem_singleton.1 (heq ▸ h1)))⟩,
              ⟨fun _ => h3, fun _ => hc3⟩⟩
          · have h3 : ru D br (c6V k) = {u1} := Finset.Subset.antisymm (fun x hx => by
              have := hsub hx; rw [Finset.mem_insert, Finset.mem_singleton] at this
              exact Finset.mem_singleton.2 (this.resolve_right (fun hx2 => h2 (hx2 ▸ hx)))) (Finset.singleton_subset_iff.2 h1)
            have hc1 : code k = 1 := by dsimp only [code]; simp [h1, h2]
            refine ⟨⟨by omega, fun heq => absurd (heq ▸ h1) (Finset.notMem_empty _)⟩,
              ⟨fun _ => h3, fun _ => hc1⟩,
              ⟨by omega, fun heq => False.elim (hu12 (Finset.mem_singleton.1 (heq ▸ h1)))⟩,
              ⟨by omega, fun heq => False.elim (h2 (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2)))⟩⟩
          · have h3 : ru D br (c6V k) = {u2} := Finset.Subset.antisymm (fun x hx => by
              have := hsub hx; rw [Finset.mem_insert, Finset.mem_singleton] at this
              exact Finset.mem_singleton.2 (this.resolve_left (fun hx1 => h1 (hx1 ▸ hx)))) (Finset.singleton_subset_iff.2 h2)
            have hc2 : code k = 2 := by dsimp only [code]; simp [h1, h2]
            refine ⟨⟨by omega, fun heq => absurd (heq ▸ h2) (Finset.notMem_empty _)⟩,
              ⟨by omega, fun heq => False.elim (hu12.symm (Finset.mem_singleton.1 (heq ▸ h2)))⟩,
              ⟨fun _ => h3, fun _ => hc2⟩,
              ⟨by omega, fun heq => False.elim (h1 (heq ▸ Finset.mem_insert_self u1 {u2}))⟩⟩
          · have h3 : ru D br (c6V k) = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun x hx => by
              have := hsub hx; rw [Finset.mem_insert, Finset.mem_singleton] at this
              exact this.elim (fun e => h1 (e ▸ hx)) (fun e => h2 (e ▸ hx))
            have hc0 : code k = 0 := by dsimp only [code]; simp [h1, h2]
            refine ⟨⟨fun _ => h3, fun _ => hc0⟩,
              ⟨by omega, fun heq => False.elim (h1 (heq ▸ Finset.mem_singleton_self u1))⟩,
              ⟨by omega, fun heq => False.elim (h2 (heq ▸ Finset.mem_singleton_self u2))⟩,
              ⟨by omega, fun heq => False.elim (h1 (heq ▸ Finset.mem_insert_self u1 {u2}))⟩⟩
        have hcode_lt : ∀ k : Fin 6, code k < 4 := fun k => by dsimp [code]; split_ifs <;> omega
        have he_ok : ∀ k : Fin 6, code k ≠ 0 ∨ code ⟨(k.val + 1) % 6, Nat.mod_lt _ (by omega)⟩ ≠ 0 := fun k => by
          rcases hc6_edge_ne k with h1 | h1
          · left; intro hc; exact h1 ((hcode_eq k).1.1 hc)
          · right; intro hc; exact h1 ((hcode_eq _).1.1 hc)
        have hno_pair : ∀ j k : Fin 6, j.val % 3 ≠ k.val % 3 → code j ≠ 0 → code j ≠ code k := by
          intro j k hmod hj0 heq
          have hj4 := hcode_lt j
          have h123 : code j = 1 ∨ code j = 2 ∨ code j = 3 := by omega
          rcases h123 with h1 | h2 | h3
          · exact hc6_pair_ru1 j k hmod u1 ((hcode_eq j).2.1.1 h1) ((hcode_eq k).2.1.1 (heq ▸ h1))
          · exact hc6_pair_ru1 j k hmod u2 ((hcode_eq j).2.2.1.1 h2) ((hcode_eq k).2.2.1.1 (heq ▸ h2))
          · exact hc6_pair_R j k hmod ((hcode_eq j).2.2.2.1 h3) ((hcode_eq k).2.2.2.1 (heq ▸ h3))
        have hzero3 : ∀ j k : Fin 6, code j = 0 → j.val % 3 ≠ k.val % 3 → code k ≠ 3 := by
          intro j k hj0 hmod hk3
          exact hc6_zero_R j k hmod ((hcode_eq j).1.1 hj0) ((hcode_eq k).2.2.2.1 hk3)
        rcases c6_code_pattern code hcode_lt he_ok hno_pair hzero3 with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
        · rcases hc with ⟨c1, c4, c2, c5⟩ | ⟨c1, c4, c2, c5⟩
          · exact o3a_core_kill h hD hB0 br hbm hpos hI hu12 hReq hru1_full 0 2 6 3 4 9 7 5 8 o3a_geom_0
              ((hcode_eq 1).2.1.1 c1) ((hcode_eq 4).2.1.1 c4) ((hcode_eq 5).2.2.1.1 c5) ((hcode_eq 2).2.2.1.1 c2)
              (ha.elim (fun x => Or.inl ((hcode_eq 0).1.1 x)) (fun x => Or.inr ((hcode_eq 0).2.2.2.1 x)))
              (hb.elim (fun x => Or.inl ((hcode_eq 3).1.1 x)) (fun x => Or.inr ((hcode_eq 3).2.2.2.1 x)))
          · exact o3a_core_kill h hD hB0 br hbm hpos hI hu12.symm (by rw [hReq, Finset.pair_comm])
              (by rw [hru1_full, Finset.pair_comm]) 0 2 6 3 4 9 7 5 8 o3a_geom_0
              ((hcode_eq 1).2.2.1.1 c1) ((hcode_eq 4).2.2.1.1 c4) ((hcode_eq 5).2.1.1 c5) ((hcode_eq 2).2.1.1 c2)
              (ha.elim (fun x => Or.inl ((hcode_eq 0).1.1 x)) (fun x => Or.inr (by rw [Finset.pair_comm]; exact (hcode_eq 0).2.2.2.1 x)))
              (hb.elim (fun x => Or.inl ((hcode_eq 3).1.1 x)) (fun x => Or.inr (by rw [Finset.pair_comm]; exact (hcode_eq 3).2.2.2.1 x)))
        · rcases hc with ⟨c1, c4, c2, c5⟩ | ⟨c1, c4, c2, c5⟩
          · exact o3a_core_kill h hD hB0 br hbm hpos hI hu12 hReq hru1_full 6 0 2 4 9 7 5 8 3 o3a_geom_1
              ((hcode_eq 2).2.1.1 c1) ((hcode_eq 5).2.1.1 c4) ((hcode_eq 0).2.2.1.1 c5) ((hcode_eq 3).2.2.1.1 c2)
              (ha.elim (fun x => Or.inl ((hcode_eq 1).1.1 x)) (fun x => Or.inr ((hcode_eq 1).2.2.2.1 x)))
              (hb.elim (fun x => Or.inl ((hcode_eq 4).1.1 x)) (fun x => Or.inr ((hcode_eq 4).2.2.2.1 x)))
          · exact o3a_core_kill h hD hB0 br hbm hpos hI hu12.symm (by rw [hReq, Finset.pair_comm])
              (by rw [hru1_full, Finset.pair_comm]) 6 0 2 4 9 7 5 8 3 o3a_geom_1
              ((hcode_eq 2).2.2.1.1 c1) ((hcode_eq 5).2.2.1.1 c4) ((hcode_eq 0).2.1.1 c5) ((hcode_eq 3).2.1.1 c2)
              (ha.elim (fun x => Or.inl ((hcode_eq 1).1.1 x)) (fun x => Or.inr (by rw [Finset.pair_comm]; exact (hcode_eq 1).2.2.2.1 x)))
              (hb.elim (fun x => Or.inl ((hcode_eq 4).1.1 x)) (fun x => Or.inr (by rw [Finset.pair_comm]; exact (hcode_eq 4).2.2.2.1 x)))
        · rcases hc with ⟨c1, c4, c2, c5⟩ | ⟨c1, c4, c2, c5⟩
          · exact o3a_core_kill h hD hB0 br hbm hpos hI hu12 hReq hru1_full 2 6 0 9 7 5 8 3 4 o3a_geom_2
              ((hcode_eq 3).2.1.1 c1) ((hcode_eq 0).2.1.1 c4) ((hcode_eq 1).2.2.1.1 c5) ((hcode_eq 4).2.2.1.1 c2)
              (ha.elim (fun x => Or.inl ((hcode_eq 2).1.1 x)) (fun x => Or.inr ((hcode_eq 2).2.2.2.1 x)))
              (hb.elim (fun x => Or.inl ((hcode_eq 5).1.1 x)) (fun x => Or.inr ((hcode_eq 5).2.2.2.1 x)))
          · exact o3a_core_kill h hD hB0 br hbm hpos hI hu12.symm (by rw [hReq, Finset.pair_comm])
              (by rw [hru1_full, Finset.pair_comm]) 2 6 0 9 7 5 8 3 4 o3a_geom_2
              ((hcode_eq 3).2.2.1.1 c1) ((hcode_eq 0).2.2.1.1 c4) ((hcode_eq 1).2.1.1 c5) ((hcode_eq 4).2.1.1 c2)
              (ha.elim (fun x => Or.inl ((hcode_eq 2).1.1 x)) (fun x => Or.inr (by rw [Finset.pair_comm]; exact (hcode_eq 2).2.2.2.1 x)))
              (hb.elim (fun x => Or.inl ((hcode_eq 5).1.1 x)) (fun x => Or.inr (by rw [Finset.pair_comm]; exact (hcode_eq 5).2.2.2.1 x)))

theorem petersen_lb_19 (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ G10Edge x) (hsize : C.size ≤ 18) :
    False := by
  obtain ⟨D, h, hD, -, h9, -, hmem⟩ := g10_wlog_canon C hmono hC hsize
  obtain ⟨idx, hI⟩ := hc_rep_of_mem hmem
  have hI' : ineligSet 10 D = hc_rep idx := hI.symm
  fin_cases idx
  · exact elim_O1 h hD h9 (by rw [hI']; decide)
  · exact elim_O2 h hD h9 (by rw [hI']; decide)
  · exact elim_O3a h hD h9 (by rw [hI']; decide)
  · exact elim_O3b h hD h9 (by rw [hI']; decide)
  · exact elim_O4 h hD h9 (by rw [hI']; decide)

def petBool (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

theorem petBool_iff (x : Fin 10 → Bool) : petBool x = true ↔ G10Edge x := by
  revert x
  unfold G10Edge petBool edgeList
  decide +kernel

end FullTapeCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open FullTapeCore

namespace FullTape

abbrev Op := Bool × Fin 30 × Fin 30

def seed : List (BitVec 30) :=
  [579928113, 419987523, 608501894, 169476364, 23364120, 201770016,
    3616832, 28839040, 834691328, 1040194048, 0, 1073741823]

def wordStep (w : List (BitVec 30)) (g : Op) : List (BitVec 30) :=
  let a := w.getD g.2.1.val 0
  let b := w.getD g.2.2.val 0
  w ++ [if g.1 then a &&& b else a ||| b]

def rawGate (g : Op) : Gate :=
  ⟨if g.1 then .and else .or,[g.2.1.val,g.2.2.val]⟩

def gateOf (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then .and else .or,[g.2.1,g.2.2]⟩

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def project (r : Fin 30) (words : List (BitVec 30)) : List Bool :=
  words.map fun w => w.getLsbD r.val

def row (r : Fin 30) (i : Fin 10) : Bool :=
  (seed.getD i.val 0).getLsbD r.val

theorem getD_project (r : Fin 30) (w : List (BitVec 30)) (i : ℕ) :
    (project r w).getD i false = (w.getD i 0).getLsbD r.val := by
  by_cases h : i < w.length
  · have h' : i < (project r w).length := by simpa [project] using h
    rw [List.getD_eq_getElem _ _ h',List.getD_eq_getElem _ _ h]
    simp [project]
  · have h' : (project r w).length ≤ i := by simpa [project] using Nat.le_of_not_gt h
    rw [List.getD_eq_default _ _ h',List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    simp

theorem project_step (r : Fin 30) (w : List (BitVec 30)) (g : Op) :
    project r (wordStep w g) = gateStep (project r w) (rawGate g) := by
  have append (x y : List (BitVec 30)) : project r (x ++ y) = project r x ++ project r y := by
    simp [project]
  have singleton (x : BitVec 30) : project r [x] = [x.getLsbD r.val] := rfl
  unfold wordStep gateStep rawGate
  rw [append,singleton]
  cases h : g.1 <;>
    simp only [h,Bool.false_eq_true,↓reduceIte,
      List.map_cons,List.map_nil,BitVec.getLsbD_and,BitVec.getLsbD_or,
      GateOp.eval,List.any_cons,List.any_nil,List.all_cons,List.all_nil,id_eq,Bool.or_false,Bool.and_true,
      getD_project]

theorem project_run (r : Fin 30) (program : List Op) (w : List (BitVec 30)) :
    project r (program.foldl wordStep w) = (program.map rawGate).foldl gateStep (project r w) := by
  induction program generalizing w with
  | nil => rfl
  | cons a p ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [ih,project_step]

theorem project_seed : ∀ r : Fin 30,
    project r seed = List.ofFn (row r) ++ [false,true] := by
  decide +kernel

def initial : List Ref × Dag :=
  ((List.range 10).map Sum.inr ++ [Sum.inl false, Sum.inl true],[])

theorem initial_ok : na_Good 10 initial := by
  refine ⟨fun j hj => absurd hj (by simp [initial]),fun r hr => ?_⟩
  simp only [initial,List.mem_append,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with ⟨k,hk,rfl⟩ | rfl | rfl
  · simpa [na_ok,initial] using hk
  · trivial
  · trivial

theorem initial_eval (x : Fin 10 → Bool) :
    initial.1.map (refVal (wl initial.2 (List.ofFn x))) = List.ofFn x ++ [false,true] := by
  change (((List.range 10).map Sum.inr) ++ [Sum.inl false,Sum.inl true]).map
    (refVal (wl ([] : Dag) (List.ofFn x))) = _
  rw [List.map_append,na_init]
  rfl

theorem program_basis (p : List Op) :
    ∀ g ∈ p.map rawGate, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hg
  cases h : u.1 <;> simp [rawGate,h]

theorem dag_basis (D : Dag) (o : ℕ) : Monotone2 ⟨D.map gateOf,o⟩ := by
  intro g hg
  change g ∈ D.map gateOf at hg
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hg
  cases h : u.1 <;> simp [gateOf,h]

theorem dag_eval (D : Dag) (o : ℕ) (x : Fin 10 → Bool) :
    (Circuit.mk (D.map gateOf) o).eval (List.ofFn x) = val D x o := by
  change ((D.map gateOf).foldl gateStep (List.ofFn x)).getD o false = _
  have same (s : List Bool) : (D.map gateOf).foldl gateStep s = wl D s := by
    induction D generalizing s with
    | nil => rfl
    | cons g d ih =>
      simp only [List.map_cons,List.foldl_cons,wl_cons]
      rw [ih]
      congr 1
      cases h : g.1 <;> simp [gateStep,wstep,gateOf,gop,h,GateOp.eval]
  rw [same]
  rfl

private theorem goal_bits : ∀ r : Fin 30, (32767 : BitVec 30).getLsbD r.val = decide (r.val < 15) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem bounds : ∀ x : Fin 10 → Bool,
    (petBool x = true → ∃ r : Fin 30, r.val < 15 ∧ ∀ i, row r i = true → x i = true) ∧
    (petBool x = false → ∃ r : Fin 30, 15 ≤ r.val ∧ ∀ i, x i = true → row r i = true) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem no_model (program : List Op) (small : program.length ≤ 18) :
    (32767 : BitVec 30) ∉ program.foldl wordStep seed := by
  intro hit
  obtain ⟨i,hi,atIndex⟩ := List.getElem_of_mem hit
  have exactWord : (program.foldl wordStep seed).getD i 0 = 32767 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact atIndex
  let state := (program.map rawGate).foldl (na_step 10) initial
  obtain ⟨good,count,semantic⟩ := na_fold_spec 10 (program.map rawGate) (program_basis program) initial initial_ok
  change na_Good 10 state at good
  change state.2.length ≤ initial.2.length + (program.map rawGate).length at count
  have len : state.2.length ≤ 18 := by simpa [initial] using count.trans (by simpa [initial] using small)
  have onRows (r : Fin 30) :
      refVal (wl state.2 (List.ofFn (row r))) (na_look state.1 i) = decide (r.val < 15) := by
    rw [na_look_val]
    have decode := semantic (row r) _ (initial_eval (row r))
    change (state.1.map (refVal (wl state.2 (List.ofFn (row r))))) =
      (program.map rawGate).foldl gateStep (List.ofFn (row r) ++ [false,true]) at decode
    rw [decode, ← project_seed r, ← project_run r program seed, getD_project, exactWord, goal_bits]
  rcases read : na_look state.1 i with c | output
  · have yes := onRows 0
    have no := onRows 15
    simp [read,refVal] at yes no
    exact Bool.noConfusion (no.symm.trans yes)
  · have evalRow (r : Fin 30) : val state.2 (row r) output = decide (r.val < 15) := by
      simpa [read,refVal,val] using onRows r
    refine petersen_lb_19 ⟨state.2.map gateOf,output⟩ (dag_basis state.2 output) ?_ ?_
    · intro x
      rw [dag_eval]
      constructor
      · intro yes
        apply (petBool_iff x).1
        by_contra wrong
        have no : petBool x = false := Bool.eq_false_of_not_eq_true wrong
        obtain ⟨r,hr,below⟩ := (bounds x).2 no
        have up := val_mono good.1 x (row r) below output yes
        rw [evalRow,decide_eq_false (by omega)] at up
        contradiction
      · intro yes
        obtain ⟨r,hr,below⟩ := (bounds x).1 ((petBool_iff x).2 yes)
        apply val_mono good.1 (row r) x below output
        rw [evalRow, decide_eq_true hr]
    · simpa [Circuit.size] using len

end FullTape

set_option maxHeartbeats 0 in
theorem fullTape : ∀ (x1 : List (Bool × Fin (30 : ℕ) × Fin (30 : ℕ))),   x1.length ≤ (18 : ℕ) →     (32767 : BitVec (30 : ℕ)) ∉       List.foldl         (fun (x3 : List (BitVec (30 : ℕ))) (x4 : Bool × Fin (30 : ℕ) × Fin (30 : ℕ)) =>           have x5 : BitVec (30 : ℕ) := x3.getD ↑x4.2.1 (0 : BitVec (30 : ℕ));           have x6 : BitVec (30 : ℕ) := x3.getD ↑x4.2.2 (0 : BitVec (30 : ℕ));           x3 ++ [if x4.1 = Bool.true then x5 &&& x6 else x5 ||| x6])         [(579928113 : BitVec (30 : ℕ)), (419987523 : BitVec (30 : ℕ)), (608501894 : BitVec (30 : ℕ)), (169476364 : BitVec (30 : ℕ)), (23364120 : BitVec (30 : ℕ)), (201770016 : BitVec (30 : ℕ)), (3616832 : BitVec (30 : ℕ)), (28839040 : BitVec (30 : ℕ)), (834691328 : BitVec (30 : ℕ)), (1040194048 : BitVec (30 : ℕ)), (0 : BitVec (30 : ℕ)), (1073741823 : BitVec (30 : ℕ))] x1 := by
  exact FullTape.no_model

namespace PetersenPartial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
export FullTapeCore (Bplus Bzero Dag Live PureBranch Ref Strict StrictLive arcs branchW card_reserved card_residual card_unitsPlus carrierDiff carrierT carrier_flow carrier_flow_diff carrier_flow_union eligSet elig_le_Bplus exists_strictLive_of_strict exists_strict_of_monotone2 exitArcs fanout fanout_eq_zero_of_ge getD_ge gop gop_false gop_true ineligSet inelig_card_add inner k4_Pos live_reaches_out lt_of_fanout_pos mem_eligSet mem_ineligSet mem_ru mem_supp mem_units merges na_Good na_comb na_comb_inl na_comb_inr na_comb_ok na_del na_del_length na_del_ops na_del_strict na_del_val na_eval0 na_eval1 na_eval2 na_fold_spec na_getD_append_lt na_getD_snoc na_init na_isAnd na_live_aux na_look na_look_ok na_look_val na_no_reader na_ok na_ok_mono na_refVal_wstep na_sh na_step na_step_spec na_strict_snoc na_strict_take na_up normalize_strictLive opA opA_eq opB opB_eq outW readers refVal reservedUnits reserved_subset residualUnits ru sb_card_arcs sb_card_arcs_filter sb_card_units_filter sb_carrierT_sub sb_fanout_arcs sb_mem_inner sb_reserved_inj sb_singleton_inter_nonempty sb_sources_carrierT sb_src_false sb_src_lt sb_src_true sb_sum_fanout_eq sb_surplus_add_card sem_Arm sem_Chain sem_Dom sem_Edge sem_Gr sem_MinBranch sem_W sem_W_and sem_bar sem_bzero_branch sem_bzero_mem sem_carrier_chain sem_chain_dom sem_chain_dom_at sem_chain_fork sem_changed_path sem_dom_eq sem_dom_eq_at sem_first_joint sem_ind sem_ind_no_edge sem_inelig_chain sem_inelig_surplus sem_ins sem_ins_agree sem_ins_ge sem_ins_self sem_mem_W sem_mem_carrier1 sem_mem_diff sem_mem_exit1 sem_mem_exit_diff sem_mem_inelig sem_minBranch_pure sem_path_chain sem_rtg_comparable sem_rtg_le sem_rtg_mono sem_sibling_indep sem_single_le sem_single_no_edge sem_src_lt sem_src_ne sem_step sem_step_fanout sem_step_iff sem_step_lt sem_step_reader sem_step_src sem_step_unique sem_supp_and sem_supp_and_sub sem_supp_lt sem_supp_or sem_surplus_diff sem_two sem_two_edge sem_val_gate_src sem_val_of_supp sem_zm_gate single sources src supp supp_gate supp_ge supp_input surplusOn surplus_carrierT_eq surplus_identity tag tag_eq totalSurplus totalSurplus_split units unitsPlus val val_gate val_ge val_input val_mono val_take val_unique wl wl_append wl_cons wl_getD_gate wl_getD_lt wl_length wl_take_getD wstep wstep_getD_last wstep_getD_lt wstep_length)

structure sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop where
  positive (x : Fin n → Bool) : sem_Edge G x → val D x (outW n D) = true
  soundPair (u v : Fin n) : let x := fun i => decide (i = u) || decide (i = v);
                             val D x (outW n D) = true → sem_Edge G x
  soundSingle (v : Fin n) : val D (single v) (outW n D) = true → sem_Edge G (single v)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v (hC.soundSingle v (mem_supp.1 hv)))

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
  have h3 := hC.positive _ h2
  rw [← hout] at h3
  exact h1 (hC.soundPair u z h3)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, hC.positive _ (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
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

theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : val D (sem_ind A) (outW n D) = false) (x : Fin n)
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
  have h3 := hC.positive _ h2
  rw [← hout] at h3
  exact Bool.noConfusion (hA.symm.trans h3)

end SemCore

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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

end SemArms

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

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
  obtain ⟨u, v, huv, hu, hv⟩ := hC.soundPair i t hout
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at huv
  · exact hG.2.1 _ huv
  · exact hnt huv
  · exact hnt (hG.1 _ _ huv)
  · exact hG.2.1 _ huv

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

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
  have hneg : val D (sem_ind {c,z}) (outW n D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have heq : sem_ind ({c,z} : Finset (Fin n)) = sem_two c z := by
      funext k
      simp [sem_ind,sem_two]
    apply sem_ind_no_edge hA
    rw [heq] at hc ⊢
    exact hC.soundPair c z hc
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hneg x ⟨z, by simp, hxz⟩
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
    exact sem_single_no_edge hG a (hC.soundSingle a hc)
  have hy1 : val D (sem_ins i (single a)) (outW n D) = true :=
    hC.positive _ ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
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

theorem ru_one_two_supp {G : Fin 10 → Fin 10 → Prop} (hG : sem_Gr G) {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 G D)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {x : Fin 10} {u0 : Σ _ : ℕ, ℕ}
    (hM : merges 10 D (carrierT 10 D {x}) = ∅) (hru : ru D b x = {u0}) :
    ∃ e1 e2 : ℕ × Bool, e1 ∈ sem_W 10 D x ∧ e2 ∈ sem_W 10 D x ∧ e1 ≠ e2 ∧
      supp 10 D u0.1 ⊆ supp 10 D (src D e1) ∧ supp 10 D u0.1 ⊆ supp 10 D (src D e2) := by
  have hS := h.1
  have hu0m : u0 ∈ ru D b x := by rw [hru]; exact Finset.mem_singleton_self u0
  obtain ⟨hu0r, hxu0⟩ := mem_ru.1 hu0m
  have hu0u : u0 ∈ units 10 D := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0r).1).1
  have hfr : 2 ≤ fanout D u0.1 := by have := (mem_units.mp hu0u).2; omega
  have hxe : x ∈ eligSet 10 D := mem_eligSet.2 ⟨u0.1, hfr, hxu0⟩
  have hlow : ∀ w, 2 ≤ fanout D w → x ∈ supp 10 D w → w ≤ u0.1 := by
    intro w hrw hxw
    by_contra hlt
    have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
        by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
    by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D b
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
      have hbv : b v = w := congrArg Sigma.fst hveq
      have hsv := (hb v hv).2.1
      rw [hbv] at hsv
      rw [hsv, Finset.mem_singleton] at hxw
      have hmin := (hb x hxe).2.2.2 u0.1 hfr hxu0
      rw [hxw, hbv] at hmin; omega
    · have h1 : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ ru D b x := mem_ru.2 ⟨Finset.mem_sdiff.2 ⟨hwu, hwr⟩, hxw⟩
      rw [hru, Finset.mem_singleton] at h1
      have : w = u0.1 := congrArg Sigma.fst h1
      omega
  have harm_sub : ∀ {a c : ℕ}, Relation.ReflTransGen (sem_Arm 10 D {x}) a c →
      supp 10 D a ⊆ supp 10 D c := by
    intro a c hp
    induction hp with
    | refl => exact Finset.Subset.refl _
    | @tail u v _ huv ih =>
      obtain ⟨hj, hge, hop⟩ := huv.1
      have hv : 10 + (v - 10) = v := by omega
      have hxv : x ∈ supp 10 D (10 + (v - 10)) := by
        rw [hv]; exact (huv.2.2 x (Finset.mem_singleton_self x)).2
      have htag : tag D (v - 10) = false := (sem_zm_gate hS hM (by omega) hxv).1
      exact ih.trans (by
        rw [← hv, sem_supp_or hS (by omega) htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right)
  have hread : ∀ j ∈ readers D u0.1,
      j < D.length ∧ u0.1 < 10 + j ∧ (opA D j = u0.1 ∨ opB D j = u0.1) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D u0.1, ∃ e : ℕ × Bool, e ∈ sem_W 10 D x ∧
      supp 10 D u0.1 ⊆ supp 10 D (src D e) ∧
      ((e.1 = j ∧ src D e = u0.1) ∨ Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hlt, hop⟩ := hread j hj
    by_cases hxj : x ∈ supp 10 D (10 + j)
    · have htag : tag D j = false := (sem_zm_gate hS hM hjl hxj).1
      have hsub1 : supp 10 D u0.1 ⊆ supp 10 D (10 + j) := by
        rw [sem_supp_or hS hjl htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hD {x}
        ⟨x, Finset.mem_singleton_self x⟩
        (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hM)
        (10 + j) (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hxj)
        (fun y hy w hrw hyw => by
          rw [Finset.mem_singleton.1 hy] at hyw
          by_contra hf; have := hlow w (by omega) hyw; omega)
      exact ⟨e, he1 x (Finset.mem_singleton_self x), hsub1.trans (harm_sub he2), Or.inr he2⟩
    · rcases hop with he | he
      · refine ⟨(j, false), sem_mem_W.2 ⟨hjl, by rw [sb_src_false, he]; exact hxu0, hxj⟩,
          by rw [sb_src_false, he], Or.inl ⟨rfl, by rw [sb_src_false, he]⟩⟩
      · refine ⟨(j, true), sem_mem_W.2 ⟨hjl, by rw [sb_src_true, he]; exact hxu0, hxj⟩,
          by rw [sb_src_true, he], Or.inl ⟨rfl, by rw [sb_src_true, he]⟩⟩
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.1 (by exact hfr : 1 < (readers D u0.1).card)
  have hRstep : ∀ a c, sem_Arm 10 D {x} a c → sem_step 10 D a c := fun _ _ hr => hr.1
  have hfun : ∀ a a' c, sem_Arm 10 D {x} a c → sem_Arm 10 D {x} a' c → a = a' := by
    intro a a' c h1 h2
    by_contra hne2
    obtain ⟨hjl, hge1, hop1⟩ := h1.1
    obtain ⟨-, -, hop2⟩ := h2.1
    have hcv : 10 + (c - 10) = c := by omega
    have ha := (h1.2.2 x (Finset.mem_singleton_self x)).1
    have ha' := (h2.2.2 x (Finset.mem_singleton_self x)).1
    have hc := (h1.2.2 x (Finset.mem_singleton_self x)).2
    have hxc : x ∈ supp 10 D (10 + (c - 10)) := by rw [hcv]; exact hc
    apply (sem_zm_gate hS hM (by omega) hxc).2
    rcases hop1 with e1 | e1 <;> rcases hop2 with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D u0.1, ∀ jb ∈ readers D u0.1, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + ja) (10 + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨-, hlta, -⟩ := hread ja hja
    obtain ⟨hjlb, -, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hu_ne : u ≠ u0.1 := by
        have := sem_rtg_le hS hRstep hu1; omega
      have hux := (hu2.2.2 x (Finset.mem_singleton_self x)).1
      apply (sem_zm_gate hS hM hjlb (hu2.2.2 x (Finset.mem_singleton_self x)).2).2
      have hstep : opA D jb = u ∨ opB D jb = u := by
        have := hu2.1.2.2; simpa using this
      rcases hopb with e1 | e1 <;> rcases hstep with e2 | e2
      · exact absurd (e2.symm.trans e1) hu_ne
      · rw [e1, e2]; exact ⟨hxu0, hux⟩
      · rw [e1, e2]; exact ⟨hux, hxu0⟩
      · exact absurd (e2.symm.trans e1) hu_ne
  obtain ⟨e1, he1W, he1s, he1p⟩ := hterm j1 hj1
  obtain ⟨e2, he2W, he2s, he2p⟩ := hterm j2 hj2
  refine ⟨e1, e2, he1W, he2W, fun heq => ?_, he1s, he2s⟩
  subst heq
  rcases he1p with ⟨hj1e, hs1⟩ | hp1 <;> rcases he2p with ⟨hj2e, hs2⟩ | hp2
  · exact hne (hj1e.symm.trans hj2e)
  · have hle := sem_rtg_le hS hRstep hp2
    have := (hread j2 hj2).2.1
    rw [hs1] at hle; omega
  · have hle := sem_rtg_le hS hRstep hp1
    have := (hread j1 hj1).2.1
    rw [hs2] at hle; omega
  · rcases sem_rtg_comparable hfun hp1 hp2 with h12 | h21
    · exact hcross j1 hj1 j2 hj2 hne h12
    · exact hcross j2 hj2 j1 hj1 hne.symm h21

section CertificateBridge
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag} {pos : Fin n → ℕ × Bool}

theorem anchor_exit (hp : k4_Pos n G D pos) {i t : Fin n} (hi : i ∈ ineligSet n D)
    (ht : t ∈ supp n D (src D (pos i))) : pos i ∈ sem_W n D t :=
  sem_mem_W.mpr ⟨(hp.1 i hi).1,ht,by rw [(hp.1 i hi).2.1]; simp⟩

theorem push_anchor (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (br : Fin n → ℕ) (hb : PureBranch n D br) (hp : k4_Pos n G D pos)
    {i x t q y : Fin n} (hi : i ∈ ineligSet n D) (hx : x ∈ eligSet n D)
    (hxt : x ≠ t) (hix : G i x) (hiq : G i q) (hxy : G x y)
    (hneg : val D (sem_ind {t,q,y}) (outW n D) = false)
    (hru : ∀ u ∈ residualUnits n D br, x ∈ supp n D u.1 → t ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ t ∈ supp n D w) :
    t ∈ supp n D (src D (pos i)) := by
  obtain ⟨e0,hexcept⟩ := ri_gen hG h hC br hb hxt hx hru hw
  have hxpos := anchor_exit hp hi ((hp.1 i hi).2.2.1 x hix)
  by_contra hnot
  have hsame : pos i = e0 := by
    by_contra hne
    exact hnot (hexcept (pos i) hxpos hne)
  obtain ⟨j,s,hj,_,h1,h2,hd⟩ := sem_exposure hG h.1 hC {t,q,y} hneg x ⟨y,by simp,hxy⟩
  have he : (j,s) ∈ sem_W n D x := sem_mem_W.mpr ⟨hj,h1,h2⟩
  have ht0 (ht : t ∈ supp n D (src D (j,s))) := Finset.disjoint_left.mp hd ht
  have hq0 (hq : q ∈ supp n D (src D (j,s))) := Finset.disjoint_left.mp hd hq
  have hne : (j,s) ≠ e0 := by
    rintro heq
    have h := (hp.1 i hi).2.2.1 q hiq
    rw [hsame,←heq] at h
    exact hq0 h (by simp)
  exact ht0 (hexcept _ he hne) (by simp)

theorem anchor_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hp : k4_Pos n G D pos) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_W n D i = {sem_bar (pos i)} := by
  obtain ⟨e,_,_,_,_,_,he,_⟩ := sem_inelig_consumer hG h hC hi
  change sem_W n D i = {e} at he
  have hx : sem_bar (pos i) ∈ sem_W n D i := sem_mem_W.mpr
      ⟨(hp.1 i hi).1,by rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) by rfl,(hp.1 i hi).2.2.2]; simp,
        by rw [show (sem_bar (pos i)).1 = (pos i).1 by rfl,(hp.1 i hi).2.1]; simp⟩
  rw [he,Finset.mem_singleton] at hx
  simpa [hx] using he

theorem card_anchor_image (hp : k4_Pos n G D pos) (A : Finset (Fin n))
    (hA : A ⊆ ineligSet n D) : (A.image pos).card = A.card := by
  exact Finset.card_image_of_injOn fun i hi j hj hij => hp.2 i (hA hi) j (hA hj) hij

theorem fresh_slot (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hp : k4_Pos n G D pos) {x y : Fin n} (hxy : G x y) (hy : y ∉ ineligSet n D)
    (A : Finset (Fin n)) (hA : A ⊆ ineligSet n D) :
    ∃ e ∈ sem_W n D x, e ∉ A.image pos ∧ y ∈ supp n D (src D (sem_bar e)) := by
  classical
  obtain ⟨e,he,hey,_⟩ := sem_edge_slots hG h.1 hC hxy
  have hs := (sem_mem_W.mp hey).2.1
  refine ⟨e,he,?_,hs⟩
  intro him
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp him
  change y ∈ supp n D (src D ((pos i).1,!(pos i).2)) at hs
  rw [(hp.1 i (hA hi)).2.2.2,Finset.mem_singleton] at hs
  exact hy (hs ▸ hA hi)

theorem anchor_full_at_capacity (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) (hp : k4_Pos n G D pos) {i x : Fin n}
    (hi : i ∈ ineligSet n D) (hix : G i x) (K : Finset (ℕ × Bool))
    (hK : K ⊆ sem_W n D x) (htight : (sem_W n D x).card ≤ K.card)
    (hopp : ∀ p ∈ K, p.1 ≠ (pos i).1 → ∃ t, t ≠ i ∧ t ∈ supp n D (src D (sem_bar p))) :
    ∀ t, t ∈ supp n D (src D (pos i)) ↔ G i t := by
  have hKeq := Finset.eq_of_subset_of_card_le hK htight
  have hr := full_gen hG h hC hB0 hi (anchor_unique hG h hC hp hi) hix (by
    intro p he hne hsub
    obtain ⟨t,ht,hin⟩ := hopp p (hKeq ▸ he) hne
    exact ht (Finset.mem_singleton.mp (hsub hin)))
  simpa [sem_bar] using hr
end CertificateBridge
section SlotBridge
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag} {pos : Fin n → ℕ × Bool}

theorem slots_realize (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hp : k4_Pos n G D pos) (x : Fin n) (A Y : Finset (Fin n))
    (hA : A ⊆ ineligSet n D) (hc : ∀ i ∈ A, x ∈ supp n D (src D (pos i)))
    (hy : ∀ y ∈ Y, G x y ∧ y ∉ ineligSet n D) :
    ∃ K : Finset (ℕ × Bool), K.card = A.card + (if Y.Nonempty then 1 else 0) ∧
      K ⊆ sem_W n D x ∧ ∀ i ∈ ineligSet n D, ∀ p ∈ K, p.1 ≠ (pos i).1 →
          ∃ t, t ≠ i ∧ t ∈ supp n D (src D (sem_bar p)) := by
  classical
  have hs : A.image pos ⊆ sem_W n D x := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    exact anchor_exit hp (hA hi) (hc _ hi)
  have ho : ∀ i ∈ ineligSet n D, ∀ p ∈ A.image pos, p.1 ≠ (pos i).1 →
          ∃ t, t ≠ i ∧ t ∈ supp n D (src D (sem_bar p)) := by
    intro i hi p he hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    refine ⟨a, fun heq => hn (heq ▸ rfl), ?_⟩
    change a ∈ supp n D (src D ((pos a).1, !(pos a).2))
    rw [(hp.1 a (hA ha)).2.2.2]; simp
  by_cases hn : Y.Nonempty
  · obtain ⟨y,hy'⟩ := hn
    have hn : Y.Nonempty := ⟨y,hy'⟩
    obtain ⟨e,he,hen,hey⟩ := fresh_slot hG h hC hp (hy _ hy').1 (hy _ hy').2 A hA
    refine ⟨insert e (A.image pos),by simp [hn, hen, card_anchor_image hp A hA],?_,?_⟩
    · simpa only [Finset.insert_subset_iff] using And.intro he hs
    · intro i hi p hp' hd
      rcases Finset.mem_insert.mp hp' with rfl|ha
      · exact ⟨y,fun hyi => (hy _ hy').2 (hyi ▸ hi),hey⟩
      · exact ho _ hi _ ha hd
  · exact ⟨A.image pos,by simp [hn,card_anchor_image hp A hA],hs,ho⟩

theorem partial_exit_bound {G : Fin 10 → Fin 10 → Prop} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (br : Fin 10 → ℕ) (hb : PureBranch 10 D br) (x : Fin 10) :
    (sem_W 10 D x).card ≤ 2 + (ru D br x).card := by
  have hcount := sem_code_count hG h hC br hb x
  have hcard := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 10)) ∩ eligSet 10 D ⊆ {x})
  rw [Finset.card_singleton] at hcard
  change (sem_W 10 D x).card ≤ 2 + ((residualUnits 10 D br).filter (fun u => x ∈ supp 10 D u.1)).card
  omega

theorem two_residual_forces_no_zero (h : StrictLive 10 D) (hlen : D.length ≤ 17)
    (hI : (ineligSet 10 D).card = 4) (br : Fin 10 → ℕ) (hb : PureBranch 10 D br)
    (hres : 2 ≤ (residualUnits 10 D br).card) : Bzero 10 D = 0 := by
  have htotal := surplus_identity h
  have hsplit := totalSurplus_split 10 D
  have hcard := inelig_card_add 10 D
  have hrem := card_residual h.1 br hb
  omega
end SlotBridge
section ResidualPacking

theorem residual_coding {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 17)
    (hI : (ineligSet 10 D).card = 4) (br : Fin 10 → ℕ) (hb : PureBranch 10 D br) :
    ∃ R : Fin 10 → Finset (Fin 2),
      (∀ x, (R x).card = (ru D br x).card) ∧
      (∀ x t, (R x).Nonempty → R x ⊆ R t →
        (∀ u ∈ residualUnits 10 D br, x ∈ supp 10 D u.1 → t ∈ supp 10 D u.1) ∧
        ∃ w, x ∈ supp 10 D w ∧ t ∈ supp 10 D w) ∧
      ((∀ j : Fin 2, ∃ x, j ∈ R x) → Bzero 10 D = 0) := by
  classical
  let U := residualUnits 10 D br
  have hcard : U.card ≤ 2 := by
    have ht := surplus_identity h
    have hs := totalSurplus_split 10 D
    have hc := inelig_card_add 10 D
    have hr := card_residual h.1 br hb
    change (residualUnits 10 D br).card ≤ 2
    omega
  let code (u : Σ _ : ℕ, ℕ) : Fin 2 :=
    if hu : u ∈ U then ((Fintype.equivFin ↥U) ⟨u,hu⟩).castLE (by simpa using hcard) else 0
  have hinj : Set.InjOn code (U : Set (Σ _ : ℕ, ℕ)) := by
    intro a ha b hb' he
    change a ∈ U at ha
    change b ∈ U at hb'
    have hv := congrArg Fin.val he
    simp only [code,dif_pos ha,dif_pos hb',Fin.val_castLE] at hv
    exact congrArg Subtype.val ((Fintype.equivFin ↥U).injective (Fin.ext hv))
  let R (x : Fin 10) := (ru D br x).image code
  have hsub (x : Fin 10) : ru D br x ⊆ U := Finset.filter_subset _ _
  refine ⟨R,fun x => Finset.card_image_of_injOn fun a ha b hb' he => hinj (hsub x ha) (hsub x hb') he,?_,?_⟩
  · intro x t hn hxt
    have hcopy (u : Σ _ : ℕ, ℕ) (hu : u ∈ ru D br x) : u ∈ ru D br t := by
      have hu' : code u ∈ R x := Finset.mem_image_of_mem _ hu
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp (hxt hu')
      exact hinj (hsub t hv) (hsub x hu) he ▸ hv
    refine ⟨fun u hu hx => (mem_ru.mp (hcopy u (mem_ru.mpr ⟨hu,hx⟩))).2,?_⟩
    obtain ⟨j,hj⟩ := hn
    obtain ⟨u,hu,_⟩ := Finset.mem_image.mp hj
    exact ⟨u.1,(mem_ru.mp hu).2,(mem_ru.mp (hcopy _ hu)).2⟩
  · intro used
    have cover : (Finset.univ : Finset (Fin 2)) ⊆ U.image code := by
      intro j _
      obtain ⟨x,hx⟩ := used j
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image_of_mem code (hsub _ hu)
    apply two_residual_forces_no_zero h hlen hI br hb
    have hlow := (Finset.card_le_card cover).trans (Finset.card_image_le : (U.image code).card ≤ U.card)
    simpa [U] using hlow
end ResidualPacking
section FourInterface
abbrev Vert := Fin 10
def propagated (G : Vert → Vert → Prop) (safe : Finset Vert → Prop)
    (I : Finset Vert) (R : Vert → Finset (Fin 2)) (i t : Vert) : Prop :=
  G i t ∨ (t ∉ I ∧ ∃ v ∉ I, G i v ∧ v ≠ t ∧ (R v).Nonempty ∧ R v ⊆ R t ∧
    ∃ q, G i q ∧ q ≠ v ∧ ∃ y, G v y ∧ safe {t,q,y})

noncomputable def neighborsOutside (G : Vert → Vert → Prop) (I : Finset Vert) (x : Vert) : Finset Vert := by
  classical
  exact Finset.univ.filter (fun y => G x y ∧ y ∉ I)

noncomputable def usedAnchors (W : Vert → Vert → Prop) (I : Finset Vert) (x : Vert) : Finset Vert := by
  classical
  exact I.filter (fun i => W i x)

noncomputable def bill (G W : Vert → Vert → Prop) (I : Finset Vert) (x : Vert) : ℕ := by
  classical
  exact (usedAnchors W I x).card + (if (neighborsOutside G I x).Nonempty then 1 else 0)

def balanced (G W : Vert → Vert → Prop) (I : Finset Vert) (R : Vert → Finset (Fin 2)) : Prop :=
  (∀ x ∉ I, bill G W I x ≤ 2+(R x).card) ∧
  ((∀ j : Fin 2, ∃ t ∉ I, j ∈ R t) → ∀ x ∉ I, bill G W I x = 2+(R x).card →
    ∀ i ∈ I, G i x → ∀ t, W i t → G i t)

theorem four_interface {G : Vert → Vert → Prop} {D : Dag} (hG : sem_Gr G)
    (h : StrictLive 10 D) (hC : sem_Comp 10 G D) (hlen : D.length ≤ 17)
    (I : Finset Vert) (hI : I = ineligSet 10 D) (hcI : I.card = 4)
    (safe : Finset Vert → Prop) (hsafe : ∀ A, safe A → val D (sem_ind A) (outW 10 D) = false) :
    ∃ R : Vert → Finset (Fin 2), balanced G G I R ∧ balanced G (propagated G safe I R) I R := by
  classical
  subst I
  obtain ⟨br,hbr⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hbr
  obtain ⟨R,hcard,hcopy,hzero⟩ := residual_coding h hlen hcI br hbp
  obtain ⟨pos,hp⟩ := k4_assigned hG h hC
  have base (i : Vert) (hi : i ∈ ineligSet 10 D) (x : Vert) (hx : G i x) :
      x ∈ supp 10 D (src D (pos i)) := (hp.1 i hi).2.2.1 x hx
  have lift (i : Vert) (hi : i ∈ ineligSet 10 D) (t : Vert)
      (ht : propagated G safe (ineligSet 10 D) R i t) : t ∈ supp 10 D (src D (pos i)) := by
    rcases ht with hbase | ⟨htout,v,hv,hiv,hvt,hne,hsub,q,hiq,hq,y,hvy,hf⟩
    · exact base i hi t hbase
    · obtain ⟨hc,w,hw⟩ := hcopy v t hne hsub
      have hve : v ∈ eligSet 10 D := by simpa [ineligSet] using hv
      exact push_anchor hG h hC br hbp hp hi hve hvt hiv hiq hvy (hsafe _ hf) hc hw
  have certify (W : Vert → Vert → Prop)
      (hs : ∀ i ∈ ineligSet 10 D, ∀ x, W i x → x ∈ supp 10 D (src D (pos i))) :
      balanced G W (ineligSet 10 D) R := by
    let I := ineligSet 10 D
    have real (x : Vert) :
        ∃ K : Finset (ℕ × Bool), K.card = bill G W I x ∧ K ⊆ sem_W 10 D x ∧
          ∀ i ∈ I, ∀ p ∈ K, p.1 ≠ (pos i).1 → ∃ t, t ≠ i ∧ t ∈ supp 10 D (src D (sem_bar p)) := by
      exact slots_realize hG h hC hp x (usedAnchors W I x) (neighborsOutside G I x)
         (fun _ hh => (Finset.mem_filter.mp hh).1)
         (fun i hh => hs i (Finset.mem_filter.mp hh).1 x (Finset.mem_filter.mp hh).2)
         (fun _ hh => (Finset.mem_filter.mp hh).2)
    constructor
    · intro x _
      obtain ⟨K,hk,hK,_⟩ := real x
      rw [hcard, ←hk]
      exact (Finset.card_le_card hK).trans (partial_exit_bound hG h hC br hbp x)
    · intro hall x _ heq i hi hix t ht
      have hB0 := hzero fun j => by obtain ⟨v,_,hv⟩ := hall j; exact ⟨v,hv⟩
      obtain ⟨K,hk,hK,hop⟩ := real x
      have hcap := partial_exit_bound hG h hC br hbp x
      have he : (sem_W 10 D x).card ≤ K.card := by rw [hk,heq,hcard]; exact hcap
      exact (anchor_full_at_capacity hG h hC hB0 hp hi hix K hK he (hop _ hi) t).1 (hs i hi t ht)
  exact ⟨R,certify G base,certify _ lift⟩
end FourInterface

end PetersenPartial

namespace PetersenFourExitCertificate

def requiredNeighbors : List ℕ := [48, 68, 138, 276, 521, 385, 770, 548, 104, 208]

def fullNeighbors : List ℕ := [50, 69, 138, 276, 521, 385, 770, 548, 104, 208]

def exposureTable : List (List ℕ) :=
  [[0, 954, 884, 618, 502, 638, 252, 466, 406, 558],
   [973, 0, 885, 233, 500, 636, 253, 217, 789, 805],
   [969, 954, 0, 747, 498, 634, 249, 475, 915, 811],
   [965, 946, 885, 0, 502, 630, 245, 467, 919, 807],
   [973, 938, 869, 747, 0, 622, 237, 459, 903, 815],
   [973, 922, 853, 715, 470, 0, 221, 475, 919, 783],
   [909, 954, 821, 683, 438, 574, 0, 411, 919, 815],
   [845, 826, 885, 619, 374, 638, 125, 0, 791, 815],
   [717, 698, 629, 747, 246, 638, 253, 219, 0, 559],
   [461, 442, 373, 235, 502, 126, 253, 475, 407, 0]]

def exposure (v t q : ℕ) : Bool :=
  !(fullNeighbors.getD t 0).testBit q &&
    (List.range 10).any fun y => (requiredNeighbors.getD v 0).testBit y &&
      !(fullNeighbors.getD y 0).testBit t && !(fullNeighbors.getD y 0).testBit q

theorem exposureTableProof : ∀ v t q : Fin 10,
    ((exposureTable.getD v.val []).getD t.val 0).testBit q.val = exposure v.val t.val q.val := by
  decide +kernel

def counter (r : ℕ) : ℕ :=
  2 + (if r.testBit 0 then 1 else 0) + (if r.testBit 1 then 1 else 0)

def slots (eligible : ℕ) (supports : List ℕ) (x : ℕ) : ℕ :=
  (supports.countP fun mask => mask.testBit x) +
     (if requiredNeighbors.getD x 0 &&& eligible = 0 then 0 else 1)

def carryStep (vtx : List (ℕ × ℕ)) (mask : ℕ) : ℕ :=
  vtx.foldl (fun out t =>
    if mask.testBit t.1 || !(vtx.any fun v =>
        mask.testBit v.1 && v.1 != t.1 && v.2 != 0 &&
        v.2 &&& t.2 == v.2 &&
        mask &&& (((exposureTable.getD v.1 []).getD t.1 0) &&& (1023 ^^^ (1 <<< v.1))) != 0)
    then out
    else out ||| (1 <<< t.1)) mask

def rejectOne (ineligible eligible : List ℕ) (assignment : ℕ) : Bool :=
  let active := (eligible.zipIdx).map fun (x,i) => (x, (assignment >>> (2*i)) &&& 3)
  let activeSet := eligible.foldl (fun m v => m ||| (1 <<< v)) 0
  let seeds := ineligible.map fun v => requiredNeighbors.getD v 0
  let exceeds := fun W : List ℕ => active.any fun x => decide (slots activeSet W x.1 > counter x.2)
  if exceeds seeds then true else
    let W := seeds.map (carryStep active)
    exceeds W ||
      ((active.foldl (fun cum x => cum ||| x.2) 0 == 3) &&
        active.any fun x =>
          (slots activeSet W x.1 == counter x.2) &&
          ((ineligible.zip (seeds.zip W)).any fun (i,w) =>
            (requiredNeighbors.getD x.1 0).testBit i && (w.1 != w.2)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem ex0 : ∀ k : Fin 4096, rejectOne [0,1,3,7] [2,4,5,6,8,9] k.val = true := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem ex1 : ∀ k : Fin 4096, rejectOne [0,2,8,9] [1,3,4,5,6,7] k.val = true := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem ex2 : ∀ k : Fin 4096, rejectOne [2,4,5,6] [0,1,3,7,8,9] k.val = true := by
  decide +kernel

end PetersenFourExitCertificate

namespace PetersenMissingEdgeOrbits

def required (u v : Fin 10) : Bool :=
  ([48, 68, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD u.val 0 |>.testBit v.val

def full (u v : Fin 10) : Bool :=
  ([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD u.val 0 |>.testBit v.val

def table : List (List (Fin 10)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
   [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
   [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
   [0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
   [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
   [1, 0, 4, 9, 6, 2, 5, 3, 7, 8],
   [1, 0, 5, 7, 2, 6, 4, 8, 9, 3],
   [1, 0, 5, 8, 6, 2, 4, 7, 3, 9]]

def perm (j : Fin 8) (v : Fin 10) : Fin 10 :=
  (table.getD j.val []).getD v.val 0

theorem injectivePerm (j : Fin 8) : Function.Injective (perm j) := by
  revert j
  unfold Function.Injective
  decide +kernel

theorem surjectivePerm (j : Fin 8) : Function.Surjective (perm j) := by
  revert j
  unfold Function.Surjective
  decide +kernel

noncomputable def equiv (j : Fin 8) : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective (perm j) ⟨injectivePerm j, surjectivePerm j⟩

theorem permRequired : ∀ j u v, required (perm j u) (perm j v) = required u v := by
  decide +kernel

theorem permFull : ∀ j u v, full (perm j u) (perm j v) = full u v := by
  decide +kernel

def independent (S : Finset (Fin 10)) : Prop :=
  ∀ u v : Fin 10, u ∈ S → v ∈ S → required u v = false

def repsTwo : List (Finset (Fin 10)) := [{0,1}, {0,2}, {0,3}, {2,4}, {2,6}, {2,8}, {3,7}]
def repsThree : List (Finset (Fin 10)) := [{0,1,3}, {0,2,6}, {0,2,8}, {0,3,7}, {0,3,9}, {2,4,5}, {2,4,8}, {2,8,9}]
def repsFour : List (Finset (Fin 10)) := [{0,1,3,7}, {0,2,8,9}, {2,4,5,6}]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem independenceCard :
    ∀ S : Finset (Fin 10), independent S → S.card ≤ 4 := by
  unfold independent
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem twoOrbits :
    ∀ S : Finset (Fin 10), independent S → S.card = 2 →
       ∃ j : Fin 8, S.image (perm j) ∈ repsTwo := by
  unfold independent
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem threeOrbits :
    ∀ S : Finset (Fin 10), independent S → S.card = 3 →
       ∃ j : Fin 8, S.image (perm j) ∈ repsThree := by
  unfold independent
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem fourOrbits :
    ∀ S : Finset (Fin 10), independent S → S.card = 4 →
       ∃ j : Fin 8, S.image (perm j) ∈ repsFour := by
  unfold independent
  decide +kernel

end PetersenMissingEdgeOrbits

namespace PetersenFourPacking

def label (S : Finset (Fin 2)) : Fin 4 :=
  ⟨(if 0 ∈ S then 1 else 0)+(if 1 ∈ S then 2 else 0),by split <;> split <;> decide⟩

theorem labelBits : ∀ (S : Finset (Fin 2)) (j : Fin 2),
    (label S).val.testBit j.val = decide (j ∈ S) := by decide +kernel

theorem labelCard : ∀ S : Finset (Fin 2),
    (if (label S).val.testBit 0 then 1 else 0) +
    (if (label S).val.testBit 1 then 1 else 0) = S.card := by decide +kernel

theorem labelOrder : ∀ S T : Finset (Fin 2),
    ((label S).val &&& (label T).val = (label S).val) ↔ S ⊆ T := by decide +kernel

theorem labelPos : ∀ S : Finset (Fin 2), (label S).val ≠ 0 ↔ S.Nonempty := by decide +kernel

def six (a b c d e f : Fin 4) : Fin 4096 :=
  ⟨a.val+4*b.val+16*c.val+64*d.val+256*e.val+1024*f.val,by omega⟩

theorem unpackSix : ∀ a b c d e f : Fin 4,
    (List.range 6).map (fun i => ((six a b c d e f).val >>> (2*i)) &&& 3) =
    [a.val,b.val,c.val,d.val,e.val,f.val] := by decide +kernel
end PetersenFourPacking

namespace PetersenFourNumericLink
open PetersenPartial PetersenFourExitCertificate PetersenFourPacking

abbrev G (u v : Vert) : Prop := PetersenMissingEdgeOrbits.required u v = true
def Safe (A : Finset Vert) : Prop :=
  ∀ u v : Vert, u ∈ A → v ∈ A → PetersenMissingEdgeOrbits.full u v = false

theorem fromExposure : ∀ v t q : Vert, exposure v.val t.val q.val = true →
       ∃ y, G v y ∧ Safe {t,q,y} := by
  unfold Safe G
  decide +kernel

theorem bitAt (v j : ℕ) : (1 <<< v : ℕ).testBit j = decide (v=j) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem foldUnion {α : Type} (f : α → ℕ) (V : List α) (z j : ℕ) :
    (V.foldl (fun m v => m ||| f v) z).testBit j = true ↔
       z.testBit j = true ∨ ∃ v ∈ V, (f v).testBit j = true := by
  induction V generalizing z with
  | nil => simp
  | cons v vs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true]
    simp only [List.mem_cons,exists_eq_or_imp]
    tauto

def copyable (V : List (ℕ × ℕ)) (m : ℕ) (t : ℕ × ℕ) : Bool :=
  V.any fun v => m.testBit v.1 && v.1 != t.1 && v.2 != 0 && v.2 &&& t.2 == v.2 &&
    m &&& (((exposureTable.getD v.1 []).getD t.1 0) &&& (1023 ^^^ (1 <<< v.1))) != 0

theorem carried_bit (V : List (ℕ × ℕ)) (m j : ℕ) :
    (carryStep V m).testBit j = true ↔ m.testBit j = true ∨
      ∃ t ∈ V, t.1 = j ∧ copyable V m t = true := by
  let f (t : ℕ × ℕ) : ℕ := if m.testBit t.1 || !(copyable V m t) then 0 else 1 <<< t.1
  have eq : carryStep V m = V.foldl (fun a t => a ||| f t) m := by
    unfold carryStep
    congr 1
    funext acc t
    change (if m.testBit t.1 || !(copyable V m t) then acc else acc ||| (1 <<< t.1)) = _
    unfold f
    split <;> simp
  rw [eq,foldUnion]
  constructor
  · rintro (h|⟨t,ht,hv⟩)
    · exact Or.inl h
    · unfold f at hv
      split at hv
      · simp at hv
      · rename_i he
        simp only [bitAt,decide_eq_true_eq] at hv
        refine Or.inr ⟨t,ht,hv,?_⟩
        cases H : copyable V m t <;> simp_all
  · rintro (h|⟨t,ht,hj,hc⟩)
    · exact Or.inl h
    · by_cases prior : m.testBit j = true
      · exact Or.inl prior
      · refine Or.inr ⟨t,ht,?_⟩
        simp [f,hj,hc,prior,bitAt]

theorem seedBit : ∀ u v : Vert, (requiredNeighbors.getD u.val 0).testBit v.val = decide (G u v) := by
  unfold G
  decide +kernel

theorem seedSize : ∀ i : Vert, requiredNeighbors.getD i.val 0 < 1024 := by decide +kernel

theorem codeOfCopy {R : Vert → Finset (Fin 2)} {V : List (ℕ × ℕ)}
    (good : ∀ z ∈ V, ∃ v : Vert, v.val=z.1 ∧ z.2=(label (R v)).val)
    {i t : Vert} {d : ℕ} (hc : copyable V (requiredNeighbors.getD i.val 0) (t.val,d) = true)
    (hd : d = (label (R t)).val) :
    ∃ v : Vert, (v.val,(label (R v)).val) ∈ V ∧ G i v ∧ v ≠ t ∧
      (R v).Nonempty ∧ R v ⊆ R t ∧ ∃ q, G i q ∧ q ≠ v ∧ ∃ y, G v y ∧ Safe {t,q,y} := by
  unfold copyable at hc
  obtain ⟨z,hz,hc⟩ := List.any_eq_true.mp hc
  obtain ⟨v,hh,hcode⟩ := good z hz
  cases z with
  | mk a b =>
    change v.val = a at hh
    subst a
    change b = _ at hcode
    subst b
    subst d
    simp only [Bool.and_eq_true,beq_iff_eq, bne_iff_ne,seedBit,decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨⟨hg,hvt⟩,hn⟩,hs⟩,hex⟩
    obtain ⟨q,hq⟩ := Nat.exists_testBit_of_ne_zero hex
    simp only [Nat.testBit_and,Nat.testBit_xor, Bool.and_eq_true] at hq
    have qlt : q < 10 := by
      by_contra h
      have lim := seedSize i
      have z := Nat.testBit_eq_false_of_lt (n := requiredNeighbors.getD i.val 0) (i := q)
      have grow : 2^10 ≤ 2^q := Nat.pow_le_pow_right (by decide) (by omega)
      have hzero := z (by omega)
      exact Bool.noConfusion (hzero.symm.trans hq.1)
    let p : Vert := ⟨q,qlt⟩
    have hinc : G i p := by
      have hbit := hq.1
      change (requiredNeighbors.getD i.val 0).testBit p.val = true at hbit
      exact of_decide_eq_true ((seedBit i p).symm.trans hbit)
    have hpv : p ≠ v := by
      intro he
      have : q = v.val := congrArg Fin.val he
      have hbad := hq.2.2
      have hmask : (1023 : ℕ).testBit q = true := by
        change (2^10-1 : ℕ).testBit q = true
        exact (Nat.testBit_two_pow_sub_one 10 q).trans (decide_eq_true qlt)
      rw [hmask,bitAt,←this] at hbad
      simp at hbad
    have he : exposure v.val t.val p.val = true := by
      rw [←exposureTableProof]
      exact hq.2.1
    exact ⟨v,hz,hg,(fun h => hvt (congrArg Fin.val h)),(labelPos _).mp hn,(labelOrder _ _).mp hs,p,hinc,hpv,fromExposure _ _ _ he⟩

end PetersenFourNumericLink
namespace PetersenFourNumericLink
open PetersenPartial PetersenFourExitCertificate PetersenFourPacking

abbrev tableFor (V : List Vert) (R : Vert → Finset (Fin 2)) :=
  V.map fun x => (x.val,(label (R x)).val)

theorem carrySound (V : List Vert) (I : Finset Vert) (R : Vert → Finset (Fin 2))
    (hv : ∀ v ∈ V, v ∉ I) (i : Vert) (j : ℕ)
    (hbit : (carryStep (tableFor V R) (requiredNeighbors.getD i.val 0)).testBit j = true) :
    ∃ x : Vert, x.val=j ∧ propagated G Safe I R i x := by
  rcases (carried_bit _ _ _).mp hbit with h|⟨z,hz,hj,hc⟩
  · have hlt : j < 10 := by
      by_contra hn
      have hpow : 2^10 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
      have lim := seedSize i
      have he := Nat.testBit_eq_false_of_lt (n:=requiredNeighbors.getD i.val 0) (i:=j) (by omega)
      exact Bool.noConfusion (he.symm.trans h)
    let x : Vert := ⟨j,hlt⟩
    exact ⟨x,rfl,Or.inl (of_decide_eq_true ((seedBit i x).symm.trans h))⟩
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    have good : ∀ z ∈ tableFor V R, ∃ v : Vert, v.val=z.1 ∧ z.2=(label (R v)).val := by
      intro z hz; obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz; exact ⟨v,rfl,rfl⟩
    obtain ⟨v,hv',hiv,hvt,hpos,hsub,hq⟩ := codeOfCopy good hc rfl
    obtain ⟨v',hvm,hsame⟩ := List.mem_map.mp hv'
    have eqv : v' = v := Fin.ext (congrArg Prod.fst hsame)
    exact ⟨t,hj,Or.inr ⟨hv _ ht,v,eqv ▸ hv _ hvm,hiv,hvt,hpos,hsub,hq⟩⟩

theorem finiteCount (A : List Vert) (hn : A.Nodup) (mask : Vert → ℕ) (x : Vert) :
    ((A.map mask).countP fun w => w.testBit x.val) =
      (A.toFinset.filter fun i => (mask i).testBit x.val = true).card := by
  rw [List.countP_map,List.countP_eq_length_filter,← List.toFinset_filter]
  exact (List.toFinset_card_of_nodup (hn.filter _)).symm

theorem activeBit (V : List Vert) (j : ℕ) :
    ((V.map Fin.val).foldl (fun m v => m ||| (1 <<< v)) 0).testBit j = true ↔
      ∃ x ∈ V, x.val = j := by
  simpa only [Nat.zero_testBit,Bool.false_eq_true,false_or,bitAt,decide_eq_true_eq,
    List.mem_map,exists_exists_and_eq_and] using
    (foldUnion (fun v : ℕ => 1 <<< v) (V.map Fin.val) 0 j)

theorem slots_sound (I V : List Vert) (hn : I.Nodup) (hV : ∀ x ∈ V, x ∉ I.toFinset)
    (P : Vert → Vert → Prop) (mask : Vert → ℕ)
    (hc : ∀ i ∈ I, ∀ x : Vert, (mask i).testBit x.val = true → P i x) (x : Vert) :
    slots ((V.map Fin.val).foldl (fun m v => m ||| (1 <<< v)) 0) (I.map mask) x.val ≤
      bill G P I.toFinset x := by
  classical
  let em := (V.map Fin.val).foldl (fun m v => m ||| (1 <<< v)) 0
  have hcount : ((I.map mask).countP fun w => w.testBit x.val) ≤
       (usedAnchors P I.toFinset x).card := by
    rw [finiteCount I hn mask x]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hm,hbit⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hm,hc _ (List.mem_toFinset.mp hm) _ hbit⟩
  have hbonus : (if requiredNeighbors.getD x.val 0 &&& em = 0 then 0 else 1) ≤
        (if (neighborsOutside G I.toFinset x).Nonempty then 1 else 0) := by
    split
    · omega
    · rename_i ne
      obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero ne
      rw [Nat.testBit_and,Bool.and_eq_true] at hj
      obtain ⟨y,hy,hyj⟩ := (activeBit V j).mp hj.2
      have hg : G x y := of_decide_eq_true ((seedBit x y).symm.trans (hyj.symm ▸ hj.1))
      have hy' : (neighborsOutside G I.toFinset x).Nonempty :=
        ⟨y,by simp only [neighborsOutside,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hg,hV _ hy⟩⟩
      simp [hy']
  exact Nat.add_le_add hcount hbonus
end PetersenFourNumericLink
namespace PetersenFourNumericLink
open PetersenPartial PetersenFourExitCertificate PetersenFourPacking

theorem tripleZip {α β γ δ : Type} (l : List α) (f : α → β) (g : α → γ) (h : α → δ) :
    (l.map f).zip ((l.map g).zip (l.map h)) = l.map (fun a => (f a,g a,h a)) := by
  induction l with | nil => rfl | cons a l ih => simpa using ih

theorem unchanged_when_full (V : List Vert) (R : Vert → Finset (Fin 2)) (I : Finset Vert)
    (hv : ∀ v ∈ V, v ∉ I) (i : Vert)
    (hall : ∀ t, propagated G Safe I R i t → G i t) :
    carryStep (tableFor V R) (requiredNeighbors.getD i.val 0) = requiredNeighbors.getD i.val 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hb; obtain ⟨t,ht,hp⟩ := carrySound V I R hv i j hb
    rw [←ht,seedBit,decide_eq_true_eq]
    exact hall _ hp
  · intro hb; exact (carried_bit _ _ _).mpr (Or.inl hb)

theorem reject_false (I V : List Vert) (hn : I.Nodup) (hv : ∀ v ∈ V, v ∉ I.toFinset)
    (R : Vert → Finset (Fin 2)) (k : ℕ)
    (enc : ((V.map Fin.val).zipIdx).map (fun (x,i) => (x,(k >>> (2*i)) &&& 3)) = tableFor V R)
    (hb : balanced G G I.toFinset R)
    (hc : balanced G (propagated G Safe I.toFinset R) I.toFinset R) :
    rejectOne (I.map Fin.val) (V.map Fin.val) k = false := by
  let active := tableFor V R
  let em := (V.map Fin.val).foldl (fun m v => m ||| (1 <<< v)) 0
  let init (i : Vert) := requiredNeighbors.getD i.val 0
  let final (i : Vert) := carryStep active (init i)
  let bounds (mask : Vert → ℕ) := active.any fun x => decide (slots em (I.map mask) x.1 > counter x.2)
  have cardR (x : Vert) : counter (label (R x)).val = 2 + (R x).card := by
    unfold counter
    rw [←labelCard (R x)]
    omega
  have hs (x : Vert) : slots em (I.map init) x.val ≤ bill G G I.toFinset x :=
    slots_sound I V hn hv G init (fun i _ t ht => of_decide_eq_true ((seedBit i t).symm.trans ht)) x
  have hf (x : Vert) : slots em (I.map final) x.val ≤ bill G (propagated G Safe I.toFinset R) I.toFinset x := by
    apply slots_sound I V hn hv
    intro i _ t ht
    obtain ⟨t',he,hp⟩ := carrySound V I.toFinset R hv i t.val ht
    exact Fin.ext he ▸ hp
  have low (mask : Vert → ℕ) (hxs : ∀ x ∈ V, slots em (I.map mask) x.val ≤ 2+(R x).card) :
      bounds mask = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨z,hz,he⟩ := List.any_eq_true.mp h
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    change decide (slots em (I.map mask) x.val > counter (label (R x)).val) = true at he
    exact (not_lt_of_ge (hxs _ hx)) (cardR x ▸ of_decide_eq_true he)
  have iseed := low init (fun x hx => (hs x).trans (hb.1 x (hv x hx)))
  have ifinal := low final (fun x hx => (hf x).trans (hc.1 x (hv x hx)))
  have nosat : ((active.foldl (fun cum x => cum ||| x.2) 0 == 3) &&
      active.any (fun x =>
        (slots em (I.map final) x.1 == counter x.2) &&
        ((I.map (fun i => (i.val,init i,final i))).any (fun (i,w) =>
           (requiredNeighbors.getD x.1 0).testBit i && (w.1 != w.2))))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨hall,hbad⟩ := (show _ ∧ _ by simpa only [Bool.and_eq_true] using h)
    have allbits : ∀ j : Fin 2, ∃ t ∉ I.toFinset, j ∈ R t := by
      intro j
      have bit : (3 : ℕ).testBit j.val = true := by fin_cases j <;> decide
      rw [←beq_iff_eq.mp hall] at bit
      rcases (foldUnion Prod.snd active 0 j.val).mp bit with hzero|⟨z,hz,hbit⟩
      · simp at hzero
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
        exact ⟨t,hv _ ht,of_decide_eq_true ((labelBits (R t) j).symm.trans hbit)⟩
    obtain ⟨z,hz,hm⟩ := List.any_eq_true.mp hbad
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    obtain ⟨he,hex⟩ := (show _ ∧ _ by simpa only [Bool.and_eq_true] using hm)
    have heq : slots em (I.map final) x.val = 2+(R x).card := (beq_iff_eq.mp he).trans (cardR x)
    have htight := le_antisymm (hc.1 x (hv x hx)) (heq ▸ hf x)
    obtain ⟨w,hw,hwbad⟩ := List.any_eq_true.mp hex
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    obtain ⟨hxi,hdiff⟩ := (show _ ∧ _ by simpa only [Bool.and_eq_true] using hwbad)
    have hxi' := of_decide_eq_true ((seedBit x i).symm.trans hxi)
    have hh := unchanged_when_full V R I.toFinset hv i (hc.2 allbits x (hv x hx) htight i
      (List.mem_toFinset.mpr hi) (by exact (show ∀ x y : Vert, G x y → G y x by unfold G; decide +kernel) _ _ hxi'))
    exact (bne_iff_ne.mp hdiff) hh.symm
  unfold rejectOne
  rw [enc]
  change (if (active.any fun x => decide (slots em ((I.map Fin.val).map fun v => requiredNeighbors.getD v 0) x.1 > counter x.2)) then _ else _) = false
  simp only [List.map_map,Function.comp_def] at *
  change (if bounds init then true else bounds final || _) = false
  rw [iseed,if_neg (by decide : ¬false = true),ifinal,Bool.false_or]
  rw [tripleZip]
  exact nosat
end PetersenFourNumericLink
namespace PetersenFourNumericLink
open PetersenPartial PetersenFourExitCertificate PetersenFourPacking PetersenMissingEdgeOrbits

theorem activeSix (a b c d e f : Vert) (R : Vert → Finset (Fin 2)) :
    ∃ k : Fin 4096, let V := [a,b,c,d,e,f]
                    ((V.map Fin.val).zipIdx).map (fun (x,i) => (x,(k.val >>> (2*i)) &&& 3)) =
                      tableFor V R := by
  let k := six (label (R a)) (label (R b)) (label (R c)) (label (R d)) (label (R e)) (label (R f))
  refine ⟨k,?_⟩
  exact congrArg (List.zip [a.val,b.val,c.val,d.val,e.val,f.val])
    (unpackSix (label (R a)) (label (R b)) (label (R c)) (label (R d)) (label (R e)) (label (R f)))

theorem four_representatives_impossible (J : Finset Vert) (hj : J ∈ repsFour)
    (R : Vert → Finset (Fin 2)) (hb : balanced G G J R)
    (hc : balanced G (propagated G Safe J R) J R) : False := by
  simp only [repsFour, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl|rfl|rfl
  · obtain ⟨k,hk⟩ := activeSix 2 4 5 6 8 9 R
    have he := reject_false ([0,1,3,7] : List Vert) [2,4,5,6,8,9] (by decide) (by decide) R k.val hk hb hc
    exact Bool.noConfusion ((ex0 k).symm.trans he)
  · obtain ⟨k,hk⟩ := activeSix 1 3 4 5 6 7 R
    have he := reject_false ([0,2,8,9] : List Vert) [1,3,4,5,6,7] (by decide) (by decide) R k.val hk hb hc
    exact Bool.noConfusion ((ex1 k).symm.trans he)
  · obtain ⟨k,hk⟩ := activeSix 0 1 3 7 8 9 R
    have he := reject_false ([2,4,5,6] : List Vert) [0,1,3,7,8,9] (by decide) (by decide) R k.val hk hb hc
    exact Bool.noConfusion ((ex2 k).symm.trans he)
end PetersenFourNumericLink

namespace PetersenPartial

section FourTransport

private theorem memImageEquiv (σ : Vert ≃ Vert) (I : Finset Vert) (x : Vert) :
    σ x ∈ I.image σ ↔ x ∈ I := by
  constructor
  · intro hx
    obtain ⟨y, hy, h⟩ := Finset.mem_image.mp hx
    exact σ.injective h ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem billTransport (σ : Vert ≃ Vert)
    {G G' W W' : Vert → Vert → Prop} (I : Finset Vert)
    (hG : ∀ u v, G' (σ u) (σ v) ↔ G u v)
    (hW : ∀ u v, W' (σ u) (σ v) ↔ W u v) (x : Vert) :
    bill G' W' (I.image σ) (σ x) = bill G W I x := by
  classical
  have hA : usedAnchors W' (I.image σ) (σ x) = (usedAnchors W I x).image σ := by
    ext y
    obtain ⟨z, rfl⟩ := σ.surjective y
    rw [memImageEquiv]
    simp only [usedAnchors, Finset.mem_filter, memImageEquiv, hW]
  have hN : neighborsOutside G' (I.image σ) (σ x) = (neighborsOutside G I x).image σ := by
    ext y
    obtain ⟨z, rfl⟩ := σ.surjective y
    rw [memImageEquiv]
    simp only [neighborsOutside, Finset.mem_filter, Finset.mem_univ, true_and, memImageEquiv, hG]
  simp only [bill, hA, hN, Finset.card_image_of_injective _ σ.injective, Finset.image_nonempty]

private theorem imgTriple (σ : Vert ≃ Vert) (a b c : Vert) :
    ({a,b,c} : Finset Vert).image σ = {σ a, σ b, σ c} := by
  classical
  simp

theorem propagatedTransport (σ : Vert ≃ Vert)
    {G G' : Vert → Vert → Prop} {safe safe' : Finset Vert → Prop}
    (I : Finset Vert) (R : Vert → Finset (Fin 2))
    (hG : ∀ u v, G' (σ u) (σ v) ↔ G u v)
    (hSafe : ∀ A : Finset Vert, safe' (A.image σ) ↔ safe A) (i t : Vert) :
    propagated G' safe' (I.image σ) (fun x => R (σ.symm x)) (σ i) (σ t) ↔
      propagated G safe I R i t := by
  classical
  constructor
  · intro h
    rcases h with h | ⟨ht,v,hv,hiv,hvt,hne,hsub,q,hiq,hq,y,hvy,hs⟩
    · exact Or.inl ((hG i t).mp h)
    · obtain ⟨v',rfl⟩ := σ.surjective v
      obtain ⟨q',rfl⟩ := σ.surjective q
      obtain ⟨y',rfl⟩ := σ.surjective y
      have hsafe : safe {t,q',y'} := (hSafe _).mp (by rwa [imgTriple])
      exact Or.inr ⟨fun h => ht ((memImageEquiv σ I t).mpr h), v',
        fun h => hv ((memImageEquiv σ I v').mpr h), (hG i v').mp hiv,
        fun h => hvt (congrArg σ h), by simpa using hne, by simpa using hsub,
        q', (hG i q').mp hiq, fun h => hq (congrArg σ h), y',
        (hG v' y').mp hvy, hsafe⟩
  · intro h
    rcases h with h | ⟨ht,v,hv,hiv,hvt,hne,hsub,q,hiq,hq,y,hvy,hs⟩
    · exact Or.inl ((hG i t).mpr h)
    · have hs' := (hSafe _).mpr hs
      rw [imgTriple] at hs'
      exact Or.inr ⟨fun h => ht ((memImageEquiv σ I t).mp h), σ v,
        fun h => hv ((memImageEquiv σ I v).mp h), (hG i v).mpr hiv,
        fun h => hvt (σ.injective h), by simpa using hne, by simpa using hsub,
        σ q, (hG i q).mpr hiq, fun h => hq (σ.injective h), σ y,
        (hG v y).mpr hvy, hs'⟩

theorem balancedTransport (σ : Vert ≃ Vert)
    {G G' W W' : Vert → Vert → Prop} (I : Finset Vert) (R : Vert → Finset (Fin 2))
    (hG : ∀ u v, G' (σ u) (σ v) ↔ G u v)
    (hW : ∀ u v, W' (σ u) (σ v) ↔ W u v)
    (bal : balanced G W I R) :
    balanced G' W' (I.image σ) (fun x => R (σ.symm x)) := by
  classical
  constructor
  · intro v hv
    obtain ⟨x,rfl⟩ := σ.surjective v
    dsimp only
    rw [σ.symm_apply_apply, billTransport σ I hG hW]
    exact bal.1 x (fun hx => hv ((memImageEquiv σ I x).mpr hx))
  · intro Hall v hv ht a ha hadj w hw
    have hall : ∀ j : Fin 2, ∃ t ∉ I, j ∈ R t := by
      intro j
      obtain ⟨z,hz,hj⟩ := Hall j
      exact ⟨σ.symm z, (fun h => hz (Finset.mem_image.mpr ⟨σ.symm z, h, σ.apply_symm_apply z⟩)), hj⟩
    obtain ⟨x,rfl⟩ := σ.surjective v
    obtain ⟨i,rfl⟩ := σ.surjective a
    obtain ⟨t,rfl⟩ := σ.surjective w
    dsimp only at ht
    rw [σ.symm_apply_apply, billTransport σ I hG hW] at ht
    exact (hG i t).mpr (bal.2 hall x (fun h => hv ((memImageEquiv σ I x).mpr h))
      ht i ((memImageEquiv σ I i).mp ha) ((hG i x).mp hadj) t ((hW i t).mp hw))

theorem configurationTransport (σ : Vert ≃ Vert)
    {G G' : Vert → Vert → Prop} {safe safe' : Finset Vert → Prop}
    (I : Finset Vert) (R : Vert → Finset (Fin 2))
    (hG : ∀ u v, G' (σ u) (σ v) ↔ G u v)
    (hSafe : ∀ A : Finset Vert, safe' (A.image σ) ↔ safe A)
    (bal : balanced G G I R ∧ balanced G (propagated G safe I R) I R) :
    balanced G' G' (I.image σ) (fun x => R (σ.symm x)) ∧
      balanced G' (propagated G' safe' (I.image σ) (fun x => R (σ.symm x)))
        (I.image σ) (fun x => R (σ.symm x)) :=
  ⟨balancedTransport σ I R hG hG bal.1, balancedTransport σ I R hG
    (propagatedTransport σ I R hG hSafe) bal.2⟩

end FourTransport

end PetersenPartial

namespace PetersenPartial

section PetersenFourTransport

open PetersenMissingEdgeOrbits

def requiredAdj (x y : Vert) : Prop := required x y = true

def safeRows (X : Finset Vert) : Prop :=
  ∀ x y : Vert, x ∈ X → y ∈ X → full x y = false

theorem requiredAcross (j : Fin 8) (u v : Vert) :
    requiredAdj (equiv j u) (equiv j v) ↔ requiredAdj u v := by
  change (required (perm j u) (perm j v) = true) ↔ (required u v = true)
  rw [permRequired]

theorem safeAcross (j : Fin 8) (X : Finset Vert) :
    safeRows (X.image (equiv j)) ↔ safeRows X := by
  constructor
  · intro h x y hx hy
    have hit := h (equiv j x) (equiv j y)
      (Finset.mem_image.mpr ⟨x,hx,rfl⟩) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    change full (perm j x) (perm j y) = false at hit
    rw [permFull] at hit
    exact hit
  · intro h u v hu hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    change full (perm j x) (perm j y) = false
    rw [permFull]
    exact h x y hx hy

theorem fourToRepresentative {I : Finset Vert} {R : Vert → Finset (Fin 2)}
    (hI : independent I) (hIcard : I.card = 4)
    (b : balanced requiredAdj requiredAdj I R ∧
      balanced requiredAdj (propagated requiredAdj safeRows I R) I R) :
    ∃ J ∈ repsFour, ∃ S : Vert → Finset (Fin 2),
      balanced requiredAdj requiredAdj J S ∧
      balanced requiredAdj (propagated requiredAdj safeRows J S) J S := by
  obtain ⟨j,hj⟩ := fourOrbits I hI hIcard
  let σ := equiv j
  have mem : I.image σ ∈ repsFour := hj
  exact ⟨I.image σ, mem, fun v => R (σ.symm v),
    configurationTransport σ I R (requiredAcross j) (safeAcross j) b⟩

end PetersenFourTransport

end PetersenPartial

namespace PetersenPartial

theorem no_four_ineligible {D : Dag}
    (hG : sem_Gr PetersenFourNumericLink.G)
    (h : StrictLive 10 D) (hC : sem_Comp 10 PetersenFourNumericLink.G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 4)
    (hsafe : ∀ A, PetersenFourNumericLink.Safe A → val D (sem_ind A) (outW 10 D) = false) : False := by
  let I := ineligSet 10 D
  obtain ⟨R,hbase,hprop⟩ := four_interface hG h hC hlen I rfl hI PetersenFourNumericLink.Safe hsafe
  have hi : PetersenMissingEdgeOrbits.independent I := by
    intro u v hu hv
    apply Bool.eq_false_iff.mpr
    intro hpos
    have hw := sem_elig_cover hG h hC (show PetersenFourNumericLink.G u v from hpos)
    exact hw.elim (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2
  obtain ⟨J,hJ,S,b,c⟩ := fourToRepresentative hi hI ⟨hbase,hprop⟩
  exact PetersenFourNumericLink.four_representatives_impossible J hJ S b c
end PetersenPartial

namespace PetersenPartial
namespace TwoExit
open PetersenMissingEdgeOrbits
abbrev G (u v : Vert) : Prop := required u v = true
abbrev Safe (A : Finset Vert) : Prop := ∀ u v : Vert, u ∈ A → v ∈ A → full u v = false

theorem barBar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by cases e; simp [sem_bar]
theorem exitTarget {n : ℕ} {D : Dag} {v : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D v) :
    v ∈ supp n D (src D e) := (sem_mem_W.mp he).2.1

theorem pairOfTwo {α : Type} [DecidableEq α] {S : Finset α} {a e : α}
    (ha : a ∈ S) (he : e ∈ S) (hne : e ≠ a) (h : S.card ≤ 2) : S = {a,e} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr he)
  · simpa [Finset.card_pair hne.symm] using h

theorem zeroResidualExits {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2) :
    ∀ v, (sem_W 10 D v).card ≤ 2 := by
  obtain ⟨br,hm⟩ := sem_exists_minBranch hG h.1 hC
  have hb := sem_minBranch_pure hm
  have he := inelig_card_add 10 D
  have hr := card_residual h.1 br hb
  have ht := surplus_identity h
  have hs := totalSurplus_split 10 D
  have none : residualUnits 10 D br = ∅ := Finset.card_eq_zero.mp (by omega)
  intro v
  have hv := partial_exit_bound hG h hC br hb v
  simpa [ru,none] using hv

theorem reservedOpp {n : ℕ} {D : Dag} {F : Fin n → Fin n → Prop}
    {pos : Fin n → ℕ × Bool} (hp : k4_Pos n F D pos) {i v : Fin n} (hi : i ∈ ineligSet n D)
    {e : ℕ × Bool} (hv : sem_bar e ∈ sem_W n D v) (he : e = pos i) : v = i := by
  subst e
  have := exitTarget hv
  change v ∈ supp n D (src D ((pos i).1,!(pos i).2)) at this
  simpa only [(hp.1 i hi).2.2.2, Finset.mem_singleton] using this

theorem pathConflict {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    {pos : Vert → ℕ × Bool} (hp : k4_Pos 10 G D pos) {z k v iz ik r y : Vert}
    (hiZ : iz ∈ ineligSet 10 D) (hiK : ik ∈ ineligSet 10 D)
    (hz : z ∉ ineligSet 10 D) (hk : k ∉ ineligSet 10 D) (hv : v ∉ ineligSet 10 D)
    (hzi : G iz z) (hki : G ik k) (hir : G ik r)
    (hzk : G z k) (hzv : G z v) (hky : G k y)
    (hneg : val D (sem_ind {r,v,y}) (outW 10 D) = false)
    (hcz : (sem_W 10 D z).card ≤ 2) (hck : (sem_W 10 D k).card ≤ 2) : False := by
  obtain ⟨e,hez,hek,_⟩ := sem_edge_slots hG h.1 hC hzk
  obtain ⟨f,hfz,hfv,_⟩ := sem_edge_slots hG h.1 hC hzv
  have haz := anchor_exit hp hiZ ((hp.1 iz hiZ).2.2.1 z hzi)
  have hak := anchor_exit hp hiK ((hp.1 ik hiK).2.2.1 k hki)
  have enz : e ≠ pos iz := fun eq => hk (reservedOpp hp hiZ hek eq ▸ hiZ)
  have fnz : f ≠ pos iz := fun eq => hv (reservedOpp hp hiZ hfv eq ▸ hiZ)
  have hh : f = e := by
    rw [pairOfTwo haz hez enz hcz,Finset.mem_insert,Finset.mem_singleton] at hfz
    exact hfz.resolve_left fnz
  subst f
  have hne : sem_bar e ≠ pos ik := by
    intro eq
    have ez : sem_bar (sem_bar e) ∈ sem_W 10 D z := by simpa only [barBar] using hez
    exact hz (reservedOpp hp hiK ez eq ▸ hiK)
  obtain ⟨j,s,hj,_,hs0,hs1,hd⟩ := sem_exposure hG h.1 hC {r,v,y} hneg k ⟨y,by simp,hky⟩
  have hslot : (j,s) ∈ sem_W 10 D k := sem_mem_W.mpr ⟨hj,hs0,hs1⟩
  rw [pairOfTwo hak hek hne hck,Finset.mem_insert,Finset.mem_singleton] at hslot
  rcases hslot with ha|ha
  · rw [ha] at hd
    exact Finset.disjoint_left.mp hd ((hp.1 ik hiK).2.2.1 r hir) (by simp)
  · rw [ha] at hd
    exact Finset.disjoint_left.mp hd (exitTarget hfv) (by simp)
end TwoExit
end PetersenPartial

namespace PetersenPartial.TwoExit
open PetersenMissingEdgeOrbits
structure Double where
  x : Vert
  i : Vert
  j : Vert
  y : Vert
  deriving DecidableEq
structure Path where
  z : Vert
  k : Vert
  v : Vert
  iz : Vert
  ik : Vert
  r : Vert
  y : Vert
  deriving DecidableEq
def doubles : List Double := [⟨2,1,3,7⟩, ⟨2,1,7,3⟩, ⟨2,3,7,1⟩, ⟨3,2,4,8⟩, ⟨3,2,8,4⟩, ⟨3,4,8,2⟩, ⟨4,0,3,9⟩, ⟨4,0,9,3⟩, ⟨4,3,9,0⟩, ⟨5,0,7,8⟩, ⟨5,0,8,7⟩, ⟨5,7,8,0⟩, ⟨6,1,8,9⟩, ⟨6,1,9,8⟩, ⟨6,8,9,1⟩, ⟨7,2,5,9⟩, ⟨7,2,9,5⟩, ⟨7,5,9,2⟩, ⟨8,3,5,6⟩, ⟨8,3,6,5⟩, ⟨8,5,6,3⟩, ⟨9,4,6,7⟩, ⟨9,4,7,6⟩, ⟨9,6,7,4⟩]
def paths : List Path := [⟨2,3,7,1,4,0,8⟩, ⟨2,7,3,1,5,0,9⟩, ⟨3,8,2,4,5,0,6⟩, ⟨3,8,4,2,6,1,5⟩, ⟨4,3,9,0,2,1,8⟩, ⟨4,9,3,0,6,1,7⟩]
def Double.fits (d : Double) (I : Finset Vert) : Prop :=
  d.i ∈ I ∧ d.j ∈ I ∧ d.i ≠ d.j ∧ d.y ∉ I ∧ G d.i d.x ∧ G d.j d.x ∧ G d.x d.y
def Path.fits (p : Path) (I : Finset Vert) : Prop :=
  p.iz ∈ I ∧ p.ik ∈ I ∧ p.z ∉ I ∧ p.k ∉ I ∧ p.v ∉ I ∧
  G p.iz p.z ∧ G p.ik p.k ∧ G p.ik p.r ∧ G p.z p.k ∧ G p.z p.v ∧ G p.k p.y ∧ Safe {p.r,p.v,p.y}

instance (I : Finset Vert) (d : Double) : Decidable (d.fits I) := by unfold Double.fits G; infer_instance
instance (I : Finset Vert) (p : Path) : Decidable (p.fits I) := by unfold Path.fits Safe G; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem geometricCases : ∀ I : Finset Vert, I.card = 2 → independent I →
    I = {0,1} ∨ (∃ j : Fin doubles.length, (doubles[j]).fits I) ∨ ∃ j : Fin paths.length, (paths[j]).fits I := by
  unfold independent
  decide +kernel

theorem two_reduces_to_endpoints {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false) :
    ineligSet 10 D = {0,1} := by
  let I := ineligSet 10 D
  obtain ⟨pos,hp⟩ := k4_assigned hG h hC
  have caps := zeroResidualExits hG h hC hlen hI
  have hi : independent I := by
    intro u v hu hv
    apply Bool.eq_false_iff.mpr
    intro hpos
    exact (sem_elig_cover hG h hC (show G u v from hpos)).elim (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2
  rcases geometricCases I hI hi with he|⟨idx,hd⟩|⟨idx,hp'⟩
  · exact he
  · let d := doubles[idx]
    change d.fits I at hd
    obtain ⟨hi,hj,hne,hy,hiX,hjX,hXY⟩ := hd
    have h1 := anchor_exit hp hi ((hp.1 d.i hi).2.2.1 d.x hiX)
    have h2 := anchor_exit hp hj ((hp.1 d.j hj).2.2.1 d.x hjX)
    have hpos : pos d.j ≠ pos d.i := fun h0 => hne (hp.2 _ hi _ hj h0.symm)
    obtain ⟨e,he,heY,_⟩ := sem_edge_slots hG h.1 hC hXY
    rw [pairOfTwo h1 h2 hpos (caps d.x),Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with le|ri
    · exact False.elim (hy (reservedOpp hp hi heY le ▸ hi))
    · exact False.elim (hy (reservedOpp hp hj heY ri ▸ hj))
  · let p := paths[idx]
    change p.fits I at hp'
    obtain ⟨hiz,hik,hz,hk,hv,hzi,hki,hir,hzk,hzv,hky,hs⟩ := hp'
    exact False.elim (pathConflict hG h hC hp hiz hik hz hk hv hzi hki hir hzk hzv hky (hsafe _ hs) (caps _) (caps _))
end PetersenPartial.TwoExit
namespace PetersenPartial.TwoExit
open PetersenMissingEdgeOrbits

theorem peripheralSlot {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    {pos : Vert → ℕ × Bool} (hp : k4_Pos 10 G D pos) {i p c : Vert}
    (hi : i ∈ ineligSet 10 D) (hip : G i p) (hpc : G p c) (hc : c ≠ i)
    (hcap : (sem_W 10 D p).card ≤ 2) :
    ∃ e ∈ sem_W 10 D p, e ≠ pos i ∧ sem_W 10 D p = {pos i,e} ∧
      (∀ t, G p t → t ≠ i → sem_bar e ∈ sem_W 10 D t) ∧
      (∀ r t y, G i r → G p y → val D (sem_ind {r,t,y}) (outW 10 D) = false →
        t ∉ supp 10 D (src D e)) := by
  obtain ⟨e,he,hec,_⟩ := sem_edge_slots hG h.1 hC hpc
  have hne : e ≠ pos i := fun eq => hc (reservedOpp hp hi hec eq)
  have ha := anchor_exit hp hi ((hp.1 i hi).2.2.1 p hip)
  have hw := pairOfTwo ha he hne hcap
  refine ⟨e,he,hne,hw,?_,?_⟩
  · intro t ht hti
    obtain ⟨f,hf,hft,_⟩ := sem_edge_slots hG h.1 hC ht
    rw [hw, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with h0|h1
    · exact False.elim (hti (reservedOpp hp hi hft h0))
    · simpa only [h1] using hft
  · intro r t y hir hpy hneg
    obtain ⟨j,s,hj,_,h0,h1,hd⟩ := sem_exposure hG h.1 hC {r,t,y} hneg p ⟨y,by simp,hpy⟩
    have hs : (j,s) ∈ sem_W 10 D p := sem_mem_W.mpr ⟨hj,h0,h1⟩
    rw [hw, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with eq|eq
    · rw [eq] at hd
      exact False.elim (Finset.disjoint_left.mp hd ((hp.1 i hi).2.2.1 r hir) (by simp))
    · rw [eq] at hd
      exact fun ht => Finset.disjoint_left.mp hd ht (by simp)
end PetersenPartial.TwoExit
namespace PetersenPartial.TwoExit
theorem diagonalMeeting {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    {v w : Fin 10} (hvw : G v w)
    {a b c d : ℕ × Bool} (hav : sem_bar a ∈ sem_W 10 D v) (hbv : sem_bar b ∈ sem_W 10 D v)
    (hcw : sem_bar c ∈ sem_W 10 D w) (hdw : sem_bar d ∈ sem_W 10 D w)
    (hab : a ≠ b) (hcd : c ≠ d) (had : a ≠ sem_bar d) (hbc : b ≠ sem_bar c)
    (hv : (sem_W 10 D v).card ≤ 2) (hw : (sem_W 10 D w).card ≤ 2) :
    a = sem_bar c ∨ b = sem_bar d := by
  have inj : Function.Injective sem_bar := fun x y hxy => by simpa only [barBar] using congrArg sem_bar hxy
  obtain ⟨e,he,hef,_⟩ := sem_edge_slots hG h.1 hC hvw
  rw [pairOfTwo hav hbv (fun eq => hab (inj eq.symm)) hv, Finset.mem_insert,Finset.mem_singleton] at he
  rw [pairOfTwo hcw hdw (fun eq => hcd (inj eq.symm)) hw, Finset.mem_insert,Finset.mem_singleton] at hef
  rcases he with he|he <;> rw [he,barBar] at hef
  · exact Or.inl (hef.resolve_right had)
  · exact Or.inr (hef.resolve_left hbc)
end PetersenPartial.TwoExit

namespace PetersenPartial.TwoExit
theorem gridHasSharedGate {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false) :
    ∃ (i p q : Fin 10) (e : ℕ × Bool), i ∈ ineligSet 10 D ∧
      ((i = 0 ∧ p = 4 ∧ q = 5) ∨ (i = 1 ∧ p = 2 ∧ q = 6)) ∧
      e ∈ sem_W 10 D p ∧ sem_bar e ∈ sem_W 10 D q ∧
      (∀ t, G p t → t ≠ i → sem_bar e ∈ sem_W 10 D t) ∧
      (∀ t, G q t → t ≠ i → e ∈ sem_W 10 D t) := by
  have hi := two_reduces_to_endpoints hG h hC hlen hI hsafe
  obtain ⟨pos,hp⟩ := k4_assigned hG h hC
  have caps := zeroResidualExits hG h hC hlen hI
  have hi0 : (0 : Fin 10) ∈ ineligSet 10 D := by rw [hi]; decide
  have hi1 : (1 : Fin 10) ∈ ineligSet 10 D := by rw [hi]; decide
  obtain ⟨e4,w4,_,_,n4,x4⟩ := peripheralSlot hG h hC hp hi0 (show G 0 4 by decide) (show G 4 3 by decide) (by decide) (caps _)
  obtain ⟨e2,w2,_,_,n2,x2⟩ := peripheralSlot hG h hC hp hi1 (show G 1 2 by decide) (show G 2 3 by decide) (by decide) (caps _)
  obtain ⟨e5,w5,_,_,n5,x5⟩ := peripheralSlot hG h hC hp hi0 (show G 0 5 by decide) (show G 5 8 by decide) (by decide) (caps _)
  obtain ⟨e6,w6,_,_,n6,x6⟩ := peripheralSlot hG h hC hp hi1 (show G 1 6 by decide) (show G 6 8 by decide) (by decide) (caps _)
  have diff42 : e4 ≠ e2 := by
    intro eq
    have hn := x4 5 2 9 (by decide) (by decide) (hsafe _ (by decide))
    rw [eq] at hn
    exact hn (exitTarget w2)
  have diff56 : e5 ≠ e6 := by
    intro eq
    have hn := x5 4 6 7 (by decide) (by decide) (hsafe _ (by decide))
    rw [eq] at hn
    exact hn (exitTarget w6)
  have diff46 : e4 ≠ sem_bar e6 := by
    intro eq
    have hn := x4 5 9 3 (by decide) (by decide) (hsafe _ (by decide))
    rw [eq] at hn
    exact hn (exitTarget (n6 9 (by decide) (by decide)))
  have diff25 : e2 ≠ sem_bar e5 := by
    intro eq
    have hn := x2 6 7 3 (by decide) (by decide) (hsafe _ (by decide))
    rw [eq] at hn
    exact hn (exitTarget (n5 7 (by decide) (by decide)))

  rcases diagonalMeeting hG h hC (show G 3 8 by decide)
    (n4 3 (by decide) (by decide)) (n2 3 (by decide) (by decide))
    (n5 8 (by decide) (by decide)) (n6 8 (by decide) (by decide))
    diff42 diff56 diff46 diff25 (caps _) (caps _) with he|he
  · refine ⟨0,4,5,e4,hi0,Or.inl ⟨rfl,rfl,rfl⟩,w4,?_,n4,?_⟩
    · simpa only [he,barBar] using w5
    · simpa only [he] using n5
  · refine ⟨1,2,6,e2,hi1,Or.inr ⟨rfl,rfl,rfl⟩,w2,?_,n2,?_⟩
    · simpa only [he,barBar] using w6
    · simpa only [he] using n6
end PetersenPartial.TwoExit

namespace PetersenPartial.TwoExit
def adv {n : ℕ} (D : Dag) (u v : Fin n) (w : ℕ) : Prop :=
  val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w
def advStep {n : ℕ} (D : Dag) (u v : Fin n) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ adv D u v b
theorem causalMeeting {n : ℕ} {D : Dag} (hS : Strict n D) {u v : Fin n} (w : ℕ)
    (hw : adv D u v w) : ∃ e : ℕ × Bool, e ∈ sem_W n D u ∧ sem_bar e ∈ sem_W n D v ∧
      adv D u v (n+e.1) ∧ Relation.ReflTransGen (advStep D u v) (n+e.1) w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hp : ∃ a, sem_step n D a w ∧ adv D u v a
    · obtain ⟨a,has,haa⟩ := hp
      obtain ⟨e,he,he',had,hr⟩ := ih a (sem_step_lt hS has) haa
      exact ⟨e,he,he',had,hr.tail ⟨has,hw⟩⟩
    obtain ⟨hw1,hw2,hw3⟩ := hw
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
    have hmin (a : ℕ) (has : a = opA D j ∨ a = opB D j) (hva : val D (sem_two u v) a = true) :
        u ∈ supp n D a ∨ v ∈ supp n D a := by
      by_contra hn'
      rw [not_or] at hn'
      have has' : sem_step n D a (n+j) := by
        rcases has with h|h
        · subst a; exact sem_step_src (n:=n) (D:=D) hj false
        · subst a; exact sem_step_src (n:=n) (D:=D) hj true
      exact hp ⟨a,has',hva,hn'.1,hn'.2⟩
    have hval := hw1
    rw [val_gate hS _ j hj] at hw1
    rw [supp_gate hS j hj] at hw2 hw3
    cases ht : tag D j
    · exfalso
      rw [ht] at hw1 hw2 hw3
      simp only [gop_false, Bool.or_eq_true] at hw1
      simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
      rcases hw1 with h | h
      · rcases hmin _ (Or.inl rfl) h with h' | h'
        · exact hw2.1 h'
        · exact hw3.1 h'
      · rcases hmin _ (Or.inr rfl) h with h' | h'
        · exact hw2.2 h'
        · exact hw3.2 h'
    · rw [ht] at hw1 hw2 hw3
      simp only [gop_true, Bool.and_eq_true] at hw1
      simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
      have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
        rw [sem_supp_and hS hj ht]
        simp only [Finset.mem_inter, not_and]
        exact ⟨hw2, hw3⟩
      have finish (s : Bool) (hu : u ∈ supp n D (src D (j,s))) (hv : v ∈ supp n D (src D (j,!s))) :
          ∃ e : ℕ × Bool, e ∈ sem_W n D u ∧ sem_bar e ∈ sem_W n D v ∧
            adv D u v (n+e.1) ∧ Relation.ReflTransGen (advStep D u v) (n+e.1) (n+j) :=
        ⟨(j,s),sem_mem_W.mpr ⟨hj,hu,hsupp.1⟩,sem_mem_W.mpr ⟨hj,hv,hsupp.2⟩,⟨hval,hsupp⟩,.refl⟩
      rcases hmin _ (Or.inl rfl) hw1.1 with hA|hA
      · exact finish false hA ((hmin _ (Or.inr rfl) hw1.2).resolve_left (hw2 hA))
      · exact finish true ((hmin _ (Or.inr rfl) hw1.2).resolve_right (hw3 hA)) hA

end PetersenPartial.TwoExit

namespace PetersenPartial.TwoExit

theorem twoBranch {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2) {w : ℕ} (hf : 2 ≤ fanout D w) :
    ∃ j ∈ eligSet 10 D, supp 10 D w = {j} ∧ sem_Dom 10 D w j.val := by
  obtain ⟨br,hm⟩ := sem_exists_minBranch hG h.1 hC
  have hb := sem_minBranch_pure hm
  have he := inelig_card_add 10 D
  have hr := card_residual h.1 br hb
  have ht := surplus_identity h
  have hs := totalSurplus_split 10 D
  have none : residualUnits 10 D br = ∅ := Finset.card_eq_zero.mp (by omega)
  have hn := sem_bzero_branch h.1 (show Bzero 10 D = 0 by omega) hf
  have hu : (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos h.1 (w:=w) (by omega)),by show 0+1 < fanout D w; omega⟩,hn⟩
  have hx : (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
    by_contra hz
    have bad : (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.mpr ⟨hu,hz⟩
    simpa only [none,Finset.notMem_empty] using bad
  obtain ⟨j,hj,hb'⟩ := Finset.mem_image.mp hx
  have hbj : br j = w := congrArg Sigma.fst hb'
  rw [← hbj]
  exact ⟨j,hj,(hm j hj).2.1,sem_chain_dom h.1 (hm j hj).2.2.1⟩

theorem dominatedFalse {D : Dag} (hS : Strict 10 D) (hC : sem_Comp 10 G D)
    {v p q z : Fin 10} {w : ℕ} (hdom : sem_Dom 10 D w v.val) (hvz : G v z)
    (hneg : val D (sem_ind {p,q,z}) (outW 10 D) = false) :
    val D (sem_two p q) w = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  let x := sem_ind ({p,q,z} : Finset (Fin 10))
  have hx : val D x w = true := val_mono hS _ _ (by
    intro i hi
    simp only [sem_two,Bool.or_eq_true,decide_eq_true_eq] at hi
    rcases hi with rfl|rfl <;> simp [x,sem_ind]) w h
  have hy := val_mono hS x (sem_ins v x) (sem_ins_ge v x) w hx
  have hout := sem_dom_eq hS x (sem_ins v x) v (sem_ins_agree v x) w hdom (by rw [hx,hy])
  have hpos := hC.positive (sem_ins v x) ⟨v,z,hvz,sem_ins_self v _,by simp [sem_ins,x,sem_ind]⟩
  rw [← hout,hneg] at hpos
  contradiction

end PetersenPartial.TwoExit
namespace PetersenPartial.TwoExit
theorem twinShield : ∀ p q : Fin 10, ((p = 4 ∧ q = 5) ∨ (p = 2 ∧ q = 6)) →
    ∀ j : Fin 10, j ≠ p → j ≠ q → ∃ z : Fin 10, G j z ∧ Safe {p,q,z} := by
  unfold Safe G
  decide +kernel

theorem truePairNoBranch {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false)
    {p q : Fin 10} (hspecific : (p = 4 ∧ q = 5) ∨ (p = 2 ∧ q = 6))
    {w : ℕ} (ha : adv D p q w) : fanout D w ≤ 1 := by
  by_contra hn
  obtain ⟨j,_,hj,hd⟩ := twoBranch hG h hC hlen hI (show 2 ≤ fanout D w by omega)
  have hjm : j ∈ supp 10 D w := hj ▸ Finset.mem_singleton_self j
  obtain ⟨z,hz,hs⟩ := twinShield p q hspecific j (fun he => ha.2.1 (he ▸ hjm)) (fun he => ha.2.2 (he ▸ hjm))
  have hf := dominatedFalse h.1 hC hd hz (hsafe _ hs)
  exact Bool.false_ne_true (hf.symm.trans ha.1)
end PetersenPartial.TwoExit

namespace PetersenPartial.TwoExit
theorem siblingUnreachable {n : ℕ} {D : Dag} (hS : Strict n D) {start j : ℕ} (hj : j < D.length)
    (s : Bool) (hch : sem_Chain n D start (src D (j,!s))) (hf : fanout D (src D (j,!s)) = 1) :
    ¬ Relation.ReflTransGen (sem_step n D) start (src D (j,s)) := by
  intro hp
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

end PetersenPartial.TwoExit
namespace PetersenPartial.TwoExit
theorem commonGuard {D : Dag} (hS : Strict 10 D) {H : ℕ} {p q : Fin 10}
    {P Q : Fin 4 → Fin 10} (hp : ∃ a, P a = p) (hq : ∃ a, P a = q)
    (hpq : ∀ a, P a = p ∨ P a = q)
    (huniq : ∀ a e, e ∈ sem_W 10 D (P a) → sem_bar e ∈ sem_W 10 D (Q a) → 10+e.1 = H)
    (hfan : ∀ w, adv D p q w → fanout D w ≤ 1)
    (hout : val D (sem_two p q) (outW 10 D) = false)
    (hs : val D (sem_two p q) H = true) (ha : ∀ a, adv D (P a) (Q a) H)
    (hr : ∀ a, Relation.ReflTransGen (advStep D (P a) (Q a)) H (outW 10 D)) :
    ∃ f : ℕ × Bool, H < 10+f.1 ∧ ∀ a, f ∈ sem_W 10 D (Q a) := by
  suffices claim : ∀ w, sem_Chain 10 D H w → val D (sem_two p q) w = true →
      (∀ a, adv D (P a) (Q a) w) →
      (∀ a, Relation.ReflTransGen (advStep D (P a) (Q a)) w (outW 10 D)) →
      ∃ f : ℕ × Bool, H < 10+f.1 ∧ ∀ a, f ∈ sem_W 10 D (Q a) from claim H .refl hs ha hr
  intro w
  generalize hk : 10 + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | ind k ih =>
    intro hc hv hada hrw
    have hne : w ≠ outW 10 D := fun eq => Bool.false_ne_true (hout.symm.trans (eq ▸ hv))
    obtain ⟨a,ha'⟩ := hp
    obtain ⟨b,hb'⟩ := hq
    have hww : adv D p q w := ⟨hv,ha' ▸ (hada a).2.1,hb' ▸ (hada b).2.1⟩
    rcases Relation.ReflTransGen.cases_head (hrw 0) with eq|⟨z,hsz,_⟩
    · exact False.elim (hne eq)
    have hf : fanout D w = 1 := le_antisymm (hfan w hww) (sem_step_fanout hsz.1)
    have hall (i : Fin 4) : adv D (P i) (Q i) z ∧ Relation.ReflTransGen (advStep D (P i) (Q i)) z (outW 10 D) := by
      rcases Relation.ReflTransGen.cases_head (hrw i) with eq|⟨z',hh,ht⟩
      · exact False.elim (hne eq)
      have hz' := sem_step_unique hsz.1 hh.1 hf
      subst z'
      exact ⟨hh.2,ht⟩
    have hlt := sem_step_lt hS hsz.1
    have hbd := hsz.1.1
    cases hz : val D (sem_two p q) z
    case true =>
      exact ih (10+D.length-z) (by omega) z rfl (hc.tail ⟨hsz.1,hf⟩) hz (fun i => (hall i).1) (fun i => (hall i).2)
    case false =>
      obtain ⟨j,t,hj,rfl,hw⟩ := sem_step_iff.mp hsz.1
      let s := !t
      have hs' : src D (j,!s) = w := by simpa [s] using hw
      have hg := sem_val_gate_src hS (sem_two p q) hj s
      rw [hs',hv,hz] at hg
      have hand : tag D j = true := by cases ht : tag D j <;> simp [ht,gop] at hg ⊢
      have hside : val D (sem_two p q) (src D (j,s)) = false := by simpa [hand,gop] using hg.symm
      have hup := sem_rtg_le hS (fun _ _ h => h.1) hc
      refine ⟨(j,s),by omega,?_⟩
      intro i
      have hpIn : P i ∉ supp 10 D (src D (j,s)) := by
        intro hi
        have := sem_val_of_supp hS hi (x := sem_two p q) (by rcases hpq i with he|he <;> simp [he,sem_two])
        exact Bool.false_ne_true (hside.symm.trans this)
      have hgate := (hall i).1
      have hside' := hgate.1
      rw [sem_val_gate_src hS _ hj s,hand,gop_true,Bool.and_eq_true] at hside'
      apply sem_mem_W.mpr
      refine ⟨hj,?_,hgate.2.2⟩
      by_contra hm
      obtain ⟨e,he,he',_,hr'⟩ := causalMeeting hS _ (show adv D (P i) (Q i) (src D (j,s)) from ⟨hside'.1,hpIn,hm⟩)
      have hh := huniq i e he he'
      rw [hh] at hr'
      exact siblingUnreachable hS hj s (hs' ▸ hc) (hs' ▸ hf) (sem_rtg_mono (fun _ _ x => x.1) hr')
end PetersenPartial.TwoExit

namespace PetersenPartial.TwoExit
theorem twinGuard {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false)
    {i p q : Fin 10} {e : ℕ × Bool} (hi : i ∈ ineligSet 10 D)
    (hdata : (i = 0 ∧ p = 4 ∧ q = 5) ∨ (i = 1 ∧ p = 2 ∧ q = 6))
    (he : e ∈ sem_W 10 D p) (hbe : sem_bar e ∈ sem_W 10 D q) :
    ∃ f : ℕ × Bool, e.1 < f.1 ∧ f ∈ sem_W 10 D 3 ∧ f ∈ sem_W 10 D 8 := by
  have hgeom : (G i p ∧ G i q ∧ G p 3 ∧ G q 8 ∧ i ≠ p ∧ i ≠ q ∧ (3 : Fin 10) ≠ i ∧ (8 : Fin 10) ≠ i ∧ Safe {p,q}) := by
    rcases hdata with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> decide
  obtain ⟨hip,hiq,hp3,hq8,hip',hiq',h3i,h8i,hs⟩ := hgeom
  obtain ⟨pos,hpos⟩ := k4_assigned hG h hC
  have caps := zeroResidualExits hG h hC hlen hI
  have ep : e ≠ pos i := fun eq => hiq' (reservedOpp hpos hi hbe eq).symm
  have eq' : sem_bar e ≠ pos i := by
    intro eq'
    have hep : sem_bar (sem_bar e) ∈ sem_W 10 D p := by simpa only [barBar] using he
    exact hip' (reservedOpp hpos hi hep eq').symm
  have hwp := pairOfTwo (anchor_exit hpos hi ((hpos.1 i hi).2.2.1 p hip)) he ep (caps _)
  have hwq := pairOfTwo (anchor_exit hpos hi ((hpos.1 i hi).2.2.1 q hiq)) hbe eq' (caps _)
  let P : Fin 4 → Fin 10 := fun k => if k=0 then p else q
  let Q : Fin 4 → Fin 10 := fun k => if k=0 then 3 else 8
  have hu (k : Fin 4) (f : ℕ × Bool) (hf : f ∈ sem_W 10 D (P k))
      (hfb : sem_bar f ∈ sem_W 10 D (Q k)) : 10+f.1 = 10+e.1 := by
    by_cases hk : k = 0
    · simp only [P,Q,hk,if_pos] at hf hfb
      rw [hwp,Finset.mem_insert,Finset.mem_singleton] at hf
      rcases hf with h1|rfl
      · exact False.elim (h3i (reservedOpp hpos hi hfb h1))
      · rfl
    · simp [P,Q,hk] at hf hfb
      rw [hwq,Finset.mem_insert,Finset.mem_singleton] at hf
      rcases hf with h1|rfl
      · exact False.elim (h8i (reservedOpp hpos hi hfb h1))
      · rfl
  have starts (k : Fin 4) : adv D (P k) (Q k) (10+e.1) ∧
      Relation.ReflTransGen (advStep D (P k) (Q k)) (10+e.1) (outW 10 D) := by
    have hg : G (P k) (Q k) := by
      by_cases hk : k=0
      · simpa only [P,Q,if_pos hk] using hp3
      · simpa only [P,Q,if_neg hk] using hq8
    have had : adv D (P k) (Q k) (outW 10 D) :=
      ⟨hC.positive _ (sem_two_edge hg),by rw [sem_supp_out hG hC]; simp, by rw [sem_supp_out hG hC]; simp⟩
    obtain ⟨f,hf,hfb,hadv,hr⟩ := causalMeeting h.1 _ had
    rw [hu k f hf hfb] at hadv hr
    exact ⟨hadv,hr⟩
  have hpair : val D (sem_two p q) (10+e.1) = true := by
    rw [sem_val_gate_src h.1 _ (sem_mem_W.mp he).1 e.2,sem_W_and h.1 he,gop_true,Bool.and_eq_true]
    exact ⟨sem_val_of_supp h.1 (exitTarget he) (by simp [sem_two]),sem_val_of_supp h.1 (exitTarget hbe) (by simp [sem_two])⟩
  have hind : sem_two p q = sem_ind {p,q} := by funext x; simp [sem_two,sem_ind]
  have hspec : (p=4 ∧ q=5) ∨ (p=2 ∧ q=6) := hdata.imp And.right And.right
  obtain ⟨f,hlt,hfr⟩ := commonGuard h.1 (p:=p) (q:=q) (P:=P) (Q:=Q) ⟨0,rfl⟩ ⟨1,rfl⟩
    (fun k => by by_cases hk : k=0 <;> simp [P,hk]) hu
    (fun _ => truePairNoBranch hG h hC hlen hI hsafe hspec)
    (by rw [hind]; exact hsafe _ hs) hpair (fun k => (starts k).1) (fun k => (starts k).2)
  exact ⟨f,by omega,hfr 0,hfr 1⟩
end PetersenPartial.TwoExit

namespace PetersenPartial.TwoExit
theorem no_two_ineligible {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 2)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false) : False := by
  obtain ⟨i,p,q,e,hi,hdata,he,hbe,hp,hq⟩ := gridHasSharedGate hG h hC hlen hI hsafe
  obtain ⟨f,hlt,hf3,hf8⟩ := twinGuard hG h hC hlen hI hsafe hi hdata he hbe
  obtain ⟨pos,hpos⟩ := k4_assigned hG h hC
  have caps := zeroResidualExits hG h hC hlen hI
  have hset := two_reduces_to_endpoints hG h hC hlen hI hsafe
  rcases hdata with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · have hK : (1 : Fin 10) ∈ ineligSet 10 D := by rw [hset]; decide
    obtain ⟨a,ha,_,_,na,xa⟩ := peripheralSlot hG h hC hpos hK (show G 1 2 by decide) (show G 2 3 by decide) (by decide) (caps _)
    obtain ⟨b,hb,_,_,nb,xb⟩ := peripheralSlot hG h hC hpos hK (show G 1 6 by decide) (show G 6 8 by decide) (by decide) (caps _)
    have hne : a ≠ b := by
      intro eq
      have hn := xa 6 6 3 (by decide) (by decide) (hsafe _ (by decide))
      rw [eq] at hn
      exact hn (exitTarget hb)
    have b3 := hp 3 (by decide) (by decide)
    have b8 := hq 8 (by decide) (by decide)
    have a3 := na 3 (by decide) (by decide)
    have b8' := nb 8 (by decide) (by decide)
    have h3 : f ≠ sem_bar e := by intro eq; have := congrArg Prod.fst eq; change f.1 = e.1 at this; omega
    have h8 : f ≠ e := by intro eq; have := congrArg Prod.fst eq; omega
    have force {x z : ℕ × Bool} {S : Finset (ℕ × Bool)} (hx : x ∈ S) (hz : z ∈ S) (hf : f ∈ S)
        (hnd : f ≠ x) (hzx : z ≠ x) (hcap : S.card ≤ 2) : f = z := by
      rw [pairOfTwo hx hz hzx hcap,Finset.mem_insert,Finset.mem_singleton] at hf
      exact hf.resolve_left hnd
    have hax : sem_bar a ≠ sem_bar e := by
      intro eq
      have heq : a = e := by simpa only [barBar] using congrArg sem_bar eq
      have hx := xa 6 4 7 (by decide) (by decide) (hsafe _ (by decide))
      rw [heq] at hx
      exact hx (exitTarget he)
    have hbx : sem_bar b ≠ e := by
      intro eq
      have heq : b = sem_bar e := by simpa only [barBar] using congrArg sem_bar eq
      have hx := xb 2 5 9 (by decide) (by decide) (hsafe _ (by decide))
      rw [heq] at hx
      exact hx (exitTarget hbe)
    have hfa := force b3 a3 hf3 h3 hax (caps 3)
    have hfb := force b8 b8' hf8 h8 hbx (caps 8)
    exact hne (by simpa only [barBar] using congrArg sem_bar (hfa.symm.trans hfb))
  · have hK : (0 : Fin 10) ∈ ineligSet 10 D := by rw [hset]; decide
    obtain ⟨a,ha,_,_,na,xa⟩ := peripheralSlot hG h hC hpos hK (show G 0 4 by decide) (show G 4 3 by decide) (by decide) (caps _)
    obtain ⟨b,hb,_,_,nb,xb⟩ := peripheralSlot hG h hC hpos hK (show G 0 5 by decide) (show G 5 8 by decide) (by decide) (caps _)
    have hne : a ≠ b := by
      intro eq
      have hn := xa 5 5 3 (by decide) (by decide) (hsafe _ (by decide))
      rw [eq] at hn
      exact hn (exitTarget hb)
    have b3 := hp 3 (by decide) (by decide)
    have b8 := hq 8 (by decide) (by decide)
    have a3 := na 3 (by decide) (by decide)
    have b8' := nb 8 (by decide) (by decide)
    have h3 : f ≠ sem_bar e := by intro eq; have := congrArg Prod.fst eq; change f.1 = e.1 at this; omega
    have h8 : f ≠ e := by intro eq; have := congrArg Prod.fst eq; omega
    have force {x z : ℕ × Bool} {S : Finset (ℕ × Bool)} (hx : x ∈ S) (hz : z ∈ S) (hf : f ∈ S)
        (hnd : f ≠ x) (hzx : z ≠ x) (hcap : S.card ≤ 2) : f = z := by
      rw [pairOfTwo hx hz hzx hcap,Finset.mem_insert,Finset.mem_singleton] at hf
      exact hf.resolve_left hnd
    have hax : sem_bar a ≠ sem_bar e := by
      intro eq
      have heq : a = e := by simpa only [barBar] using congrArg sem_bar eq
      have hx := xa 5 2 9 (by decide) (by decide) (hsafe _ (by decide))
      rw [heq] at hx
      exact hx (exitTarget he)
    have hbx : sem_bar b ≠ e := by
      intro eq
      have heq : b = sem_bar e := by simpa only [barBar] using congrArg sem_bar eq
      have hx := xb 4 6 7 (by decide) (by decide) (hsafe _ (by decide))
      rw [heq] at hx
      exact hx (exitTarget hbe)
    have hfa := force b3 a3 hf3 h3 hax (caps 3)
    have hfb := force b8 b8' hf8 h8 hbx (caps 8)
    exact hne (by simpa only [barBar] using congrArg sem_bar (hfa.symm.trans hfb))
end PetersenPartial.TwoExit

namespace PetersenPartial.ThreeExit
abbrev G (u v : Fin 10) := PetersenMissingEdgeOrbits.required u v = true
abbrev Heavy (D : Dag) (v : Fin 10) := 3 ≤ (sem_W 10 D v).card

theorem heavyCommon {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 3) (x : Fin 10) (hx : Heavy D x) :
    (sem_W 10 D x).card = 3 ∧ ∃ e f : ℕ × Bool, e ≠ f ∧
      ∀ v, Heavy D v → e ∈ sem_W 10 D v ∧ f ∈ sem_W 10 D v := by
  obtain ⟨br,hm⟩ := sem_exists_minBranch hG h.1 hC
  have hb := sem_minBranch_pure hm
  have he := inelig_card_add 10 D
  have hr := card_residual h.1 br hb
  have ht := surplus_identity h
  have hs := totalSurplus_split 10 D
  have hle : (residualUnits 10 D br).card ≤ 1 := by omega
  have hsub (v : Fin 10) : ru D br v ⊆ residualUnits 10 D br := Finset.filter_subset _ _
  have hcnt (v : Fin 10) := Finset.card_le_card (hsub v)
  have hcx := hcnt x
  have hp := partial_exit_bound hG h hC br hb x
  change 3 ≤ (sem_W 10 D x).card at hx
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp (show (residualUnits 10 D br).card = 1 by omega)
  have hall (v : Fin 10) (hv : Heavy D v) :
      ru D br v = {u} ∧ merges 10 D (carrierT 10 D {v}) = ∅ ∧ v ∈ supp 10 D u.1 := by
    have hc := partial_exit_bound hG h hC br hb v
    have hz := hcnt v
    change 3 ≤ (sem_W 10 D v).card at hv
    have hru : ru D br v = {u} := by
      rw [← hu]
      exact Finset.eq_of_subset_of_card_le (hsub v) (by omega)
    have hcode := sem_code_count hG h hC br hb v
    change (sem_W 10 D v).card + _ = 1 + _ + (ru D br v).card at hcode
    have hi := Finset.card_le_card (Finset.inter_subset_left : ({v} : Finset (Fin 10)) ∩ eligSet 10 D ⊆ {v})
    rw [Finset.card_singleton] at hi
    refine ⟨hru,Finset.card_eq_zero.mp (by omega),?_⟩
    exact (mem_ru.mp (hru ▸ Finset.mem_singleton_self u)).2
  obtain ⟨e,f,he,hf,hne,hs1,hs2⟩ := ru_one_two_supp hG h hC br hm (hall x hx).2.1 (hall x hx).1
  refine ⟨by omega,e,f,hne,?_⟩
  intro v hv
  have ha (a : ℕ × Bool) (hex : a ∈ sem_W 10 D x) (hs' : supp 10 D u.1 ⊆ supp 10 D (src D a)) :
      a ∈ sem_W 10 D v := by
    have hj := (sem_mem_W.mp hex).1
    refine sem_mem_W.mpr ⟨hj,hs' (hall v hv).2.2,?_⟩
    intro him
    exact Bool.noConfusion ((sem_W_and h.1 hex).symm.trans (sem_zm_gate h.1 (hall v hv).2.1 hj him).1)
  exact ⟨ha e he hs1,ha f hf hs2⟩
end PetersenPartial.ThreeExit

namespace PetersenPartial.ThreeExit
abbrev Safe (A : Finset (Fin 10)) := ∀ u v : Fin 10, u ∈ A → v ∈ A → PetersenMissingEdgeOrbits.full u v = false

theorem threeCover {α : Type} [DecidableEq α] {S : Finset α} {a b c : α} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : S.card ≤ 3) :
    S = {a,b,c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset ha (Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hc))
  · simpa [Finset.card_insert_of_notMem,hab,hac,hbc] using hs

theorem privateExclude {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false)
    {x t z y : Fin 10} {a b f : ℕ × Bool} (hcard : (sem_W 10 D x).card ≤ 3)
    (ha : a ∈ sem_W 10 D x) (hb : b ∈ sem_W 10 D x) (hf : f ∈ sem_W 10 D x)
    (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)

    (hta' : a ∈ sem_W 10 D t) (htb : b ∈ sem_W 10 D t)
    (hxy : G x y) (hs : Safe {z,t,y}) : z ∉ supp 10 D (src D f) := by
  obtain ⟨j,s,hj,_,h0,h1,hd⟩ := sem_exposure hG h.1 hC {z,t,y} (hsafe _ hs) x ⟨y,by simp,hxy⟩
  have hs' : (j,s) ∈ sem_W 10 D x := sem_mem_W.mpr ⟨hj,h0,h1⟩
  rw [threeCover ha hb hf hab haf hbf hcard,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hs'
  rcases hs' with eq|eq|eq
  · rw [eq] at hd
    exact False.elim (Finset.disjoint_left.mp hd (sem_mem_W.mp hta').2.1 (by simp))
  · rw [eq] at hd
    exact False.elim (Finset.disjoint_left.mp hd (sem_mem_W.mp htb).2.1 (by simp))
  · rw [eq] at hd
    exact fun hh => Finset.disjoint_left.mp hd hh (by simp)
end PetersenPartial.ThreeExit
namespace PetersenPartial.ThreeExit
abbrev V := Fin 10
def Force (I H : Finset V) (i : V) : Prop :=
  i ∈ I ∧ ∃ x ∈ H, G i x ∧ ∃ s, G i s ∧ ∃ t ∈ H, ∃ y, G x y ∧ Safe {s,t,y}
instance (I H : Finset V) (i : V) : Decidable (Force I H i) := by unfold Force G Safe; infer_instance

def Aset (I H : Finset V) (x : V) := I.filter (fun i => G i x ∨ (Force I H i ∧ x ∈ H))
def Yset (I : Finset V) (x : V) := Finset.univ.filter (fun y => G x y ∧ y ∉ I)
def slots (I H : Finset V) (x : V) := (Aset I H x).card + (if (Yset I x).Nonempty then 1 else 0)
def capacity (H : Finset V) (x : V) := 2 + if x ∈ H then 1 else 0

theorem heavyLedger {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 3)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false)
    (H : Finset V) (hh : ∀ v, v ∈ H ↔ Heavy D v) :
    (Finset.univ.filter (Force (ineligSet 10 D) H)).card ≤ 2 ∧
    (∀ x, slots (ineligSet 10 D) H x ≤ capacity H x) ∧
    (∀ x i t, H.Nonempty → slots (ineligSet 10 D) H x = capacity H x →
      Force (ineligSet 10 D) H i → G i x → t ∈ H → G i t) := by
  classical
  let I := ineligSet 10 D
  obtain ⟨pos,hp⟩ := k4_assigned hG h hC
  have hc (x : V) : (sem_W 10 D x).card ≤ capacity H x := by
    by_cases hx : x ∈ H
    · rw [capacity,if_pos hx,(heavyCommon hG h hC hlen hI x ((hh x).1 hx)).1]
    · have hh' := mt (hh x).2 hx
      change ¬ 3 ≤ (sem_W 10 D x).card at hh'
      rw [capacity,if_neg hx]; omega
  have labs : ∃ a b : ℕ × Bool, ∀ i, Force I H i → pos i = a ∨ pos i = b := by
    by_cases hn : H.Nonempty
    · obtain ⟨x,hx⟩ := hn
      obtain ⟨_,a,b,hab,hm⟩ := heavyCommon hG h hC hlen hI x ((hh x).1 hx)
      refine ⟨a,b,?_⟩
      rintro i ⟨hi,x,hx,hix,s,his,t,ht,y,hxy,hs⟩
      by_contra hnot
      have hnx := (hh x).1 hx
      have ha := (hm x hnx).1
      have hb := (hm x hnx).2
      have hc' := (heavyCommon hG h hC hlen hI x hnx).1
      have hf := anchor_exit hp hi ((hp.1 i hi).2.2.1 x hix)
      have hab' := not_or.mp hnot
      have hns := privateExclude hG h hC hsafe (le_of_eq hc') ha hb hf hab (Ne.symm hab'.1) (Ne.symm hab'.2)
        (hm t ((hh t).1 ht)).1 (hm t ((hh t).1 ht)).2 hxy hs
      exact hns ((hp.1 i hi).2.2.1 s his)
    · exact ⟨(0,false),(0,false),fun _ hf => False.elim (hn ⟨_,hf.2.choose_spec.1⟩)⟩
  obtain ⟨a,b,hl⟩ := labs
  have hm (i : V) (hi : Force I H i) (x : V) (hx : x ∈ H) : x ∈ supp 10 D (src D (pos i)) := by
    obtain ⟨_,xh,hxh,hix,s,his,t,ht,y,hxy,hs⟩ := hi
    obtain ⟨hc',e,f,hef,hco⟩ := heavyCommon hG h hC hlen hI xh ((hh xh).1 hxh)
    have hif : pos i = e ∨ pos i = f := by
      by_contra hn
      have hi' : i ∈ I := by assumption
      have hf := anchor_exit hp hi' ((hp.1 i hi').2.2.1 xh hix)
      have hnf := not_or.mp hn
      exact privateExclude hG h hC hsafe (le_of_eq hc') (hco xh ((hh _).1 hxh)).1
        (hco xh ((hh _).1 hxh)).2 hf hef (Ne.symm hnf.1) (Ne.symm hnf.2)
        (hco t ((hh t).1 ht)).1 (hco t ((hh t).1 ht)).2 hxy hs ((hp.1 i hi').2.2.1 s his)
    rcases hif with he|he <;> rw [he]
    · exact (sem_mem_W.mp (hco x ((hh x).1 hx)).1).2.1
    · exact (sem_mem_W.mp (hco x ((hh x).1 hx)).2).2.1
  have hk (x : V) := slots_realize hG h hC hp x (Aset I H x) (Yset I x)
    (Finset.filter_subset _ _) (fun i hi => by
      obtain ⟨hi',hi''⟩ := Finset.mem_filter.mp hi
      rcases hi'' with he|⟨hf,hx⟩
      · exact (hp.1 i hi').2.2.1 x he
      · exact hm i hf x hx)
    (fun _ h' => (Finset.mem_filter.mp h').2)
  refine ⟨?_,?_,?_⟩
  · let F := Finset.univ.filter (Force I H)
    have hin : F ⊆ I := fun _ hi => ((Finset.mem_filter.mp hi).2).1
    have hf : F.image pos ⊆ {a,b} := by
      rintro _ hv; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa using hl i ((Finset.mem_filter.mp hi).2)
    have hle := Finset.card_le_card hf
    rw [card_anchor_image hp F hin] at hle
    exact hle.trans (Finset.card_insert_le .. |>.trans (by simp))
  · intro x
    obtain ⟨K,hk',hks,_⟩ := hk x
    change (Aset I H x).card + _ ≤ _
    rw [← hk']
    exact (Finset.card_le_card hks).trans (hc x)
  · intro x i t hhn heq hfi hix ht
    obtain ⟨K,hkc,hks,hko⟩ := hk x
    have htight : (sem_W 10 D x).card ≤ K.card := by rw [hkc]; exact (hc x).trans_eq heq.symm
    obtain ⟨br,hbr⟩ := sem_exists_minBranch hG h.1 hC
    obtain ⟨v,hv⟩ := hhn
    have hr := card_residual h.1 br (sem_minBranch_pure hbr)
    have hi' := inelig_card_add 10 D
    have hs := totalSurplus_split 10 D
    have hsur := surplus_identity h
    have wr := partial_exit_bound hG h hC br (sem_minBranch_pure hbr) v
    have hv' := (hh v).1 hv
    change 3 ≤ (sem_W 10 D v).card at hv'
    have hle := Finset.card_le_card (Finset.filter_subset (fun u => v ∈ supp 10 D u.1) (residualUnits 10 D br))
    change (ru D br v).card ≤ _ at hle
    have hbz : Bzero 10 D = 0 := by omega
    exact (anchor_full_at_capacity hG h hC hbz hp hfi.1 hix K hks htight (hko _ hfi.1) t).1 (hm i hfi t ht)
end PetersenPartial.ThreeExit

namespace PetersenPartial.ThreeExit
structure Valid (I H : Finset V) : Prop where
  forces : (Finset.univ.filter (Force I H)).card ≤ 2
  costs : ∀ x, slots I H x ≤ capacity H x
  tight : ∀ x i t, H.Nonempty → slots I H x = capacity H x →
    Force I H i → G i x → t ∈ H → G i t
  path : ∀ p : TwoExit.Path, p.fits I → p.z ∉ H → p.k ∉ H → False

theorem forcedBy {I H : Finset V} {i x s t y : V} (hi : i ∈ I) (hx : x ∈ H) (ht : t ∈ H)
    (hg : G i x ∧ G i s ∧ G x y ∧ Safe {s,t,y}) : Force I H i :=
  ⟨hi,x,hx,hg.1,s,hg.2.1,t,ht,y,hg.2.2⟩

theorem billLower {I H K : Finset V} {x : V} {n m : ℕ} (hk : K ⊆ Aset I H x)
    (hcard : K.card = n) (hy : (if (Yset I x).Nonempty then 1 else 0) = m) :
    n+m ≤ slots I H x := by
  unfold slots
  rw [← hcard,← hy]
  exact Nat.add_le_add_right (Finset.card_le_card hk) _

theorem capMax (H : Finset V) (x : V) : capacity H x ≤ 3 := by unfold capacity; split <;> decide
theorem capLight {H : Finset V} {x : V} (hx : x ∉ H) : capacity H x ≤ 2 := by simp [capacity,hx]

theorem threeForced {I H K : Finset V} (h : Valid I H) (hK : K.card = 3)
    (hk : ∀ i ∈ K, Force I H i) : False := by
  have hsub : K ⊆ Finset.univ.filter (Force I H) := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk i hi⟩
  have hc := Finset.card_le_card hsub
  have hsum := h.forces
  omega

theorem billOverflow {I H : Finset V} (h : Valid I H) {x : V} {low cap : ℕ}
    (hl : low ≤ slots I H x) (hc : capacity H x ≤ cap) (hle : cap < low) : False := by
  have := h.costs x
  omega

theorem billTight {I H : Finset V} (h : Valid I H) {x i t : V} {bound : ℕ}
    (hl : bound ≤ slots I H x) (hc : capacity H x ≤ bound)
    (hf : Force I H i) (hx : G i x) (ht : t ∈ H) (hnt : ¬ G i t) : False :=
  hnt (h.tight x i t ⟨t,ht⟩ (le_antisymm (h.costs _) (hc.trans hl)) hf hx ht)

end PetersenPartial.ThreeExit

namespace PetersenPartial.ThreeExit
theorem monoForce {I S H : Finset V} (h : S ⊆ H) {i : V} : Force I S i → Force I H i := by
  rintro ⟨hi,x,hx,g,s,gs,t,ht,y,gy,hs⟩
  exact ⟨hi,x,h hx,g,s,gs,t,h ht,y,gy,hs⟩

theorem monoSlots {I S H : Finset V} (h : S ⊆ H) (x : V) : slots I S x ≤ slots I H x := by
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hh⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi,hh.imp_right (fun hh => ⟨monoForce h hh.1,h hh.2⟩)⟩

inductive Tree where
  | s (x : V) (l r : Tree)
  | f
  | o (x : V)
  | t (x i v : V)
  | p (z k v iz ik r y : V)

def ceiling (L : Finset V) (x : V) := if x ∈ L then 2 else 3

def test (I S L : Finset V) : Tree → Bool
  | .s x l r => test I (insert x S) L l && test I S (insert x L) r
  | .f => decide (2 < (Finset.univ.filter (Force I S)).card)
  | .o x => decide (ceiling L x < slots I S x)
  | .t x i v => decide (ceiling L x ≤ slots I S x ∧ Force I S i ∧ G i x ∧ v ∈ S ∧ ¬ G i v)
  | .p z k v iz ik r y => decide ((TwoExit.Path.mk z k v iz ik r y).fits I ∧ z ∈ L ∧ k ∈ L)

theorem treeSound {I H : Finset V} (h : Valid I H) (t : Tree) :
    ∀ S L, S ⊆ H → Disjoint L H → test I S L t = true → False := by
  induction t with
  | s x l r il ir =>
    intro S L hs hl ht
    simp only [test,Bool.and_eq_true] at ht
    obtain ⟨h1,h2⟩ := ht
    by_cases hx : x ∈ H
    · exact il _ _ (Finset.insert_subset hx hs) hl h1
    · exact ir _ _ hs (Finset.disjoint_insert_left.mpr ⟨hx,hl⟩) h2
  | f =>
    intro S L hs _ ht
    have hh : (Finset.univ.filter (Force I S)).card ≤ (Finset.univ.filter (Force I H)).card :=
      Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,monoForce hs (Finset.mem_filter.mp hi).2⟩)
    exact (Nat.not_lt_of_ge (hh.trans h.forces)) (of_decide_eq_true ht)
  | o x =>
    intro S L hs hl ht
    have hc : capacity H x ≤ ceiling L x := by
      unfold ceiling; split
      · exact capLight (Finset.disjoint_left.mp hl (by assumption))
      · exact capMax H x
    exact (Nat.not_lt_of_ge (((monoSlots hs x).trans (h.costs x)).trans hc)) (of_decide_eq_true ht)
  | t x i v =>
    intro S L hs hl ht
    change decide _ = true at ht
    obtain ⟨hb,hf,hx,hv,hn⟩ := of_decide_eq_true ht
    have hc : capacity H x ≤ ceiling L x := by
      unfold ceiling; split
      · exact capLight (Finset.disjoint_left.mp hl (by assumption))
      · exact capMax H x
    exact hn (h.tight x i v ⟨v,hs hv⟩ (le_antisymm (h.costs x) ((hc.trans hb).trans (monoSlots hs x))) (monoForce hs hf) hx (hs hv))
  | p z k v iz ik r y =>
    intro S L hs hl ht
    change decide _ = true at ht
    obtain ⟨hp,hz,hk⟩ := of_decide_eq_true ht
    exact h.path ⟨z,k,v,iz,ik,r,y⟩ hp (Finset.disjoint_left.mp hl hz) (Finset.disjoint_left.mp hl hk)

def triples : List ((V × V × V) × Tree) := [
  (⟨0,1,3⟩,(.s 2 (.s 4 .f (.o 4)) (.o 2))),
  (⟨0,1,7⟩,(.s 2 (.s 5 .f (.o 5)) (.o 2))),
  (⟨0,1,8⟩,(.s 5 (.s 6 .f (.o 6)) (.o 5))),
  (⟨0,1,9⟩,(.s 4 (.s 6 .f (.o 6)) (.o 4))),
  (⟨0,2,6⟩,(.s 3 (.s 7 (.s 8 (.t 3 2 8) (.s 4 (.s 5 (.t 5 0 7) (.p 5 8 7 0 6 1 3)) (.s 5 (.t 5 0 7) (.p 5 8 7 0 6 1 3)))) (.s 9 (.t 3 2 9) (.p 7 9 5 2 6 1 4))) (.s 4 (.s 7 (.s 5 (.t 5 0 7) (.s 8 (.t 7 2 8) (.p 5 8 7 0 6 1 3))) (.s 9 (.t 4 0 9) (.p 7 9 5 2 6 1 4))) (.p 4 3 9 0 2 1 8)))),
  (⟨0,2,8⟩,(.s 3 (.s 5 (.t 3 2 5) (.o 5)) (.o 3))),
  (⟨0,2,9⟩,(.s 4 (.s 7 (.o 4) (.o 7)) (.o 4))),
  (⟨0,3,6⟩,(.s 8 (.s 4 (.o 4) (.o 4)) (.o 8))),
  (⟨0,3,7⟩,(.s 2 (.s 4 .f (.o 4)) (.o 2))),
  (⟨0,3,9⟩,(.s 4 (.s 2 .f (.s 7 (.t 4 3 7) (.p 2 7 1 3 9 4 5))) (.o 4))),
  (⟨0,6,7⟩,(.s 9 (.s 5 (.o 5) (.o 5)) (.o 9))),
  (⟨0,7,8⟩,(.s 5 (.s 2 .f (.s 3 (.t 5 7 3) (.p 2 3 1 7 8 5 4))) (.o 5))),
  (⟨0,8,9⟩,(.s 4 (.s 5 .f (.o 5)) (.o 4))),
  (⟨1,3,5⟩,(.s 8 (.s 2 (.o 2) (.o 2)) (.o 8))),
  (⟨1,3,7⟩,(.s 2 (.s 5 .f (.s 8 (.t 2 7 8) (.p 5 8 0 7 3 2 6))) (.o 2))),
  (⟨1,3,9⟩,(.s 2 (.s 4 .f (.o 4)) (.o 2))),
  (⟨1,4,5⟩,(.s 2 (.s 3 (.t 2 1 3) (.s 0 .f (.s 8 (.t 0 5 2) (.p 3 8 2 4 5 0 6)))) (.s 3 (.s 7 (.t 3 4 7) (.p 2 7 3 1 5 0 9)) (.p 2 3 7 1 4 0 8)))),
  (⟨1,4,7⟩,(.s 9 (.s 2 (.o 2) (.o 2)) (.o 9))),
  (⟨1,4,8⟩,(.s 3 (.s 6 (.t 3 4 6) (.o 6)) (.o 3))),
  (⟨1,5,9⟩,(.s 6 (.s 7 (.o 6) (.o 7)) (.o 6))),
  (⟨1,7,8⟩,(.s 2 (.s 5 .f (.o 5)) (.o 2))),
  (⟨1,8,9⟩,(.s 6 (.s 2 .f (.s 3 (.t 6 9 3) (.p 2 3 7 1 8 6 4))) (.o 6))),
  (⟨2,4,5⟩,(.s 3 (.s 7 .f (.o 7)) (.o 3))),
  (⟨2,4,6⟩,(.s 9 (.s 3 .f (.o 3)) (.o 9))),
  (⟨2,4,8⟩,(.s 3 (.s 5 .f (.s 7 .f (.p 5 7 0 8 2 3 9))) (.o 3))),
  (⟨2,5,6⟩,(.s 8 (.s 7 .f (.o 7)) (.o 8))),
  (⟨2,5,9⟩,(.s 7 (.s 3 .f (.s 4 .f (.p 3 4 8 2 9 7 0))) (.o 7))),
  (⟨2,8,9⟩,(.s 3 (.s 6 .f (.o 6)) (.o 3))),
  (⟨3,5,6⟩,(.s 8 (.s 2 .f (.s 7 .f (.p 2 7 1 3 5 8 9))) (.o 8))),
  (⟨3,5,9⟩,(.s 4 (.s 7 .f (.o 7)) (.o 4))),
  (⟨3,6,7⟩,(.s 8 (.s 2 .f (.o 2)) (.o 8))),
  (⟨4,5,6⟩,(.s 8 (.s 9 .f (.o 9)) (.o 8))),
  (⟨4,6,7⟩,(.s 9 (.s 2 .f (.s 3 .f (.p 2 3 1 7 4 9 8))) (.o 9))),
  (⟨4,7,8⟩,(.s 3 (.s 5 .f (.o 5)) (.o 3)))]
def verts (p : V × V × V) : Finset V := {p.1,p.2.1,p.2.2}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allChecked : triples.all (fun p => test (verts p.1) ∅ ∅ p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCovered : ∀ I : Finset V, I.card = 3 → PetersenMissingEdgeOrbits.independent I →
    (triples.map (fun p => verts p.1)).contains I := by
  unfold PetersenMissingEdgeOrbits.independent
  decide +kernel
theorem noValid (I H : Finset V) (hi : I.card = 3) (hind : PetersenMissingEdgeOrbits.independent I) (hv : Valid I H) : False := by
  obtain ⟨p,hp,he⟩ := List.mem_map.mp (List.contains_iff_mem.mp (allCovered I hi hind))
  have ht := List.all_eq_true.mp allChecked p hp
  rw [he] at ht
  exact treeSound hv p.2 ∅ ∅ (Finset.empty_subset _) (by simp) ht
end PetersenPartial.ThreeExit

namespace PetersenPartial.ThreeExit
theorem no_three_ineligible {D : Dag} (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hlen : D.length ≤ 17) (hI : (ineligSet 10 D).card = 3)
    (hsafe : ∀ A, Safe A → val D (sem_ind A) (outW 10 D) = false) : False := by
  let I := ineligSet 10 D
  let H := Finset.univ.filter (Heavy D)
  have hh (v : V) : v ∈ H ↔ Heavy D v := by simp [H]
  obtain ⟨hforce,hcost,htight⟩ := heavyLedger hG h hC hlen hI hsafe H hh
  have hind : PetersenMissingEdgeOrbits.independent I := by
    intro u v hu hv
    apply Bool.eq_false_iff.mpr
    intro hpos
    exact (sem_elig_cover hG h hC (show G u v from hpos)).elim (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2
  apply noValid I H hI hind
  refine ⟨hforce,hcost,htight,?_⟩
  intro p hp hz hk
  obtain ⟨hiz,hik,hz',hk',hv,hzi,hki,hir,hzk,hzv,hky,hs⟩ := hp
  obtain ⟨pos,hpos⟩ := k4_assigned hG h hC
  have cap (v : V) (hv : v ∉ H) : (sem_W 10 D v).card ≤ 2 := by
    have hn := mt (hh v).2 hv
    change ¬ 3 ≤ (sem_W 10 D v).card at hn
    omega
  exact TwoExit.pathConflict hG h hC hpos hiz hik hz' hk' hv hzi hki hir hzk hzv hky
    (hsafe _ hs) (cap _ hz) (cap _ hk)
end PetersenPartial.ThreeExit

namespace PetersenPartial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open FullTape
section WordCheck

open PetersenMissingEdgeOrbits

private theorem word_bits_missing : ∀ r : Fin 30,
    (32766 : BitVec 30).getLsbD r.val = decide (0 < r.val ∧ r.val < 15) := by
  decide +kernel

private theorem word_rows (program : List Op) (small : program.length ≤ 17)
    (hit : (32766 : BitVec 30) ∈ program.foldl wordStep seed) :
    ∃ D : Dag, ∃ output : ℕ, Strict 10 D ∧ D.length ≤ 17 ∧
       ∀ r : Fin 30, val D (row r) output = decide (0 < r.val ∧ r.val < 15) := by
  obtain ⟨i,hi,atIndex⟩ := List.getElem_of_mem hit
  have exactWord : (program.foldl wordStep seed).getD i 0 = 32766 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact atIndex
  let state := (program.map rawGate).foldl (na_step 10) initial
  obtain ⟨good,count,semantic⟩ :=
    na_fold_spec 10 (program.map rawGate) (program_basis program) initial initial_ok
  change na_Good 10 state at good
  change state.2.length ≤ initial.2.length + (program.map rawGate).length at count
  have len : state.2.length ≤ 17 := count.trans (by simpa [initial] using small)
  have onRows (r : Fin 30) :
      refVal (wl state.2 (List.ofFn (row r))) (na_look state.1 i) =
        decide (0 < r.val ∧ r.val < 15) := by
    rw [na_look_val]
    have decode := semantic (row r) _ (initial_eval (row r))
    change state.1.map (refVal (wl state.2 (List.ofFn (row r)))) =
      (program.map rawGate).foldl gateStep (List.ofFn (row r) ++ [false,true]) at decode
    rw [decode, ← project_seed r, ← project_run r program seed, getD_project, exactWord, word_bits_missing]
  rcases read : na_look state.1 i with c | output
  · have yes := onRows 1
    have no := onRows 15
    simp [read,refVal] at yes no
    exact (Bool.false_ne_true (no.symm.trans yes)).elim
  · exact ⟨state.2, output, good.1, len, fun r => by simpa [read,refVal,val] using onRows r⟩

theorem requiredGeometry : sem_Gr requiredAdj := by
  unfold sem_Gr requiredAdj
  decide +kernel

private theorem requiredPairRow :
    ∀ u v : Vert, requiredAdj u v → ∃ r : Fin 30, (0 < r.val ∧ r.val < 15) ∧
      ∀ i : Vert, row r i = sem_two u v i := by
  unfold requiredAdj
  decide +kernel

private theorem missingPairRow :
    ∀ u v : Vert, ¬requiredAdj u v → ∃ r : Fin 30, ¬(0 < r.val ∧ r.val < 15) ∧
      ∀ i : Vert, sem_two u v i = true → row r i = true := by
  unfold requiredAdj
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem independentRow :
    ∀ A : Finset Vert, safeRows A → ∃ r : Fin 30, 15 ≤ r.val ∧
      ∀ i : Vert, i ∈ A → row r i = true := by
  unfold safeRows
  decide +kernel

theorem partialDAGFromTape (program : List Op) (small : program.length ≤ 17)
    (hit : (32766 : BitVec 30) ∈ program.foldl wordStep seed) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ 17 ∧ sem_Comp 10 requiredAdj D ∧
      ∀ A : Finset Vert, safeRows A → val D (sem_ind A) (outW 10 D) = false := by
  obtain ⟨D0,o,hS,hDlen,hrows⟩ := word_rows program small hit
  let F (x : Vert → Bool) := val D0 x o
  have edgeON (u v : Vert) (h : requiredAdj u v) : F (sem_two u v) = true := by
    obtain ⟨r,hl,hr⟩ := requiredPairRow u v h
    rw [← funext hr]
    simpa only [F, decide_eq_true hl] using hrows r
  have edgeOFF (u v : Vert) (h : ¬requiredAdj u v) : F (sem_two u v) = false := by
    obtain ⟨r,hl,hr⟩ := missingPairRow u v h
    cases hval : F (sem_two u v)
    · rfl
    · have falseAtRow : val D0 (row r) o = false := by simpa only [decide_eq_false hl] using hrows r
      have trueAtRow := val_mono hS (sem_two u v) (row r) hr o hval
      rw [falseAtRow] at trueAtRow
      exact Bool.noConfusion trueAtRow
  have singleOFF (u : Vert) : F (single u) = false := by
    have e : sem_two u u = single u := by
      funext i
      simp [sem_two,single]
    rw [←e]
    exact edgeOFF u u (requiredGeometry.2.1 u)
  have safeOFF (A : Finset Vert) (hA : safeRows A) : F (sem_ind A) = false := by
    obtain ⟨r,hl,hr⟩ := independentRow A hA
    cases hval : F (sem_ind A)
    · rfl
    · have falseAtRow : val D0 (row r) o = false := by
        rw [hrows, decide_eq_false (by omega)]
      have incl : ∀ i : Vert, sem_ind A i = true → row r i = true := by
        intro i hi
        exact hr i (of_decide_eq_true hi)
      have trueAtRow := val_mono hS (sem_ind A) (row r) incl o hval
      rw [falseAtRow] at trueAtRow
      exact Bool.noConfusion trueAtRow
  let C : Circuit := ⟨D0.map gateOf, o⟩
  have agree (x : Vert → Bool) : C.eval (List.ofFn x) = F x := dag_eval D0 o x
  have nonconst (b : Bool) : ∃ x : Vert → Bool, C.eval (List.ofFn x) ≠ b := by
    cases b
    · refine ⟨sem_two 1 2, ?_⟩
      rw [agree, edgeON 1 2 (by unfold requiredAdj; decide +kernel)]
      decide
    · refine ⟨single 0, ?_⟩
      rw [agree,singleOFF]
      decide
  have nonproj (i : Vert) : ∃ x : Vert → Bool, C.eval (List.ofFn x) ≠ x i := by
    refine ⟨single i, ?_⟩
    rw [agree,singleOFF]
    simp [single]
  have essential (i : Vert) : ∃ x y : Vert → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨j,hj,_⟩ := requiredGeometry.2.2.2 i i
    refine ⟨single j, sem_two i j, ?_, ?_⟩
    · intro k hk
      simp [single,sem_two,hk]
    · rw [agree,agree,singleOFF,edgeON i j hj]
      decide
  obtain ⟨D,hLive,hLen,hVal⟩ := normalize_strictLive C (dag_basis D0 o) nonconst nonproj essential
  have value (x : Vert → Bool) : val D x (outW 10 D) = F x := (hVal x).trans (agree x)
  have nd : D.length ≤ 17 := hLen.trans (by simpa [C,Circuit.size] using hDlen)
  refine ⟨D,hLive,nd,⟨?_,?_,?_⟩,?_⟩
  · rintro x ⟨u,v,hu,hxu,hxv⟩
    have sub : ∀ i : Vert, sem_two u v i = true → x i = true := by
      intro i hi
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxv
    apply val_mono hLive.1 (sem_two u v) x sub
    rw [value,edgeON u v hu]
  · intro u v
    dsimp only
    intro h
    by_cases e : requiredAdj u v
    · refine ⟨u,v,e,?_,?_⟩ <;> simp [sem_two]
    · change val D (sem_two u v) (outW 10 D) = true at h
      rw [value,edgeOFF u v e] at h
      exact Bool.noConfusion h
  · intro u h
    rw [value,singleOFF] at h
    exact Bool.noConfusion h
  · intro A hA
    rw [value,safeOFF A hA]

theorem wordCases (w : BitVec 30) (h : w ||| (1 : BitVec 30) = 32767) :
    w = (32766 : BitVec 30) ∨ w = (32767 : BitVec 30) := by
  have hh (i : ℕ) (hi : i < 30) (nz : i ≠ 0) :
      w.getLsbD i = (32767 : BitVec 30).getLsbD i := by
    have atBit := congrArg (fun w : BitVec 30 => w.getLsbD i) h
    have oneOff : (1 : BitVec 30).getLsbD i = false := by
      have small : (⟨i, hi⟩ : Fin 30).val ≠ 0 := nz
      exact (by decide +kernel : ∀ r : Fin 30, r.val ≠ 0 →
        (1 : BitVec 30).getLsbD r.val = false) ⟨i,hi⟩ small
    simpa only [BitVec.getLsbD_or,oneOff,Bool.or_false] using atBit
  have sameAway : ∀ r : Fin 30, r.val ≠ 0 →
      (32766 : BitVec 30).getLsbD r.val = (32767 : BitVec 30).getLsbD r.val := by
    decide +kernel
  cases first : w.getLsbD 0
  · left
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases nz : i = 0
    · subst i
      simpa using first
    · exact (hh i hi nz).trans (sameAway ⟨i,hi⟩ nz).symm
  · right
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases nz : i = 0
    · subst i
      simpa using first
    · exact hh i hi nz

end WordCheck

end PetersenPartial

namespace PetersenPartial

open FullTape PetersenMissingEdgeOrbits

theorem ineligibleIndependent {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 requiredAdj D) : independent (ineligSet 10 D) := by
  intro u v hu hv
  cases e : required u v
  · rfl
  · rcases sem_elig_cover requiredGeometry h hC (show requiredAdj u v from e) with hu' | hv'
    · exact ((sem_mem_inelig.mp hu) hu').elim
    · exact ((sem_mem_inelig.mp hv) hv').elim

theorem possibleIneligibleCards {D : Dag} (h : StrictLive 10 D) (small : D.length ≤ 17)
    (hC : sem_Comp 10 requiredAdj D) :
    (ineligSet 10 D).card = 2 ∨ (ineligSet 10 D).card = 3 ∨ (ineligSet 10 D).card = 4 := by
  obtain ⟨b,hb⟩ := sem_exists_minBranch requiredGeometry h.1 hC
  have e := elig_le_Bplus h.1 b (sem_minBranch_pure hb)
  have surplus := surplus_identity h
  have split := totalSurplus_split 10 D
  have complement := inelig_card_add 10 D
  have upper := independenceCard _ (ineligibleIndependent h hC)
  omega

def ExcludeIneligible (k : ℕ) : Prop :=
  ∀ D : Dag, StrictLive 10 D → D.length ≤ 17 → sem_Comp 10 requiredAdj D →
      (∀ A : Finset Vert, safeRows A → val D (sem_ind A) (outW 10 D) = false) →
      (ineligSet 10 D).card = k → False

def NoFullWord : Prop :=
  ∀ program : List Op, program.length ≤ 17 → (32767 : BitVec 30) ∉ program.foldl wordStep seed

theorem exactTapeFromCases (hFull : NoFullWord)
    (hTwo : ExcludeIneligible 2) (hThree : ExcludeIneligible 3) (hFour : ExcludeIneligible 4) :
    ∀ program : List Op, program.length ≤ 17 →
      ∀ w ∈ program.foldl wordStep seed, w ||| (1 : BitVec 30) ≠ (32767 : BitVec 30) := by
  intro program small w hit equal
  rcases wordCases w equal with rfl | rfl
  · obtain ⟨D, live, budget, correct, safe⟩ := partialDAGFromTape program small hit
    rcases possibleIneligibleCards live budget correct with two | three | four
    · exact hTwo D live budget correct safe two
    · exact hThree D live budget correct safe three
    · exact hFour D live budget correct safe four
  · exact hFull program small hit

end PetersenPartial

theorem oneMissing : ∀ (x1 : List (Bool × Fin (30 : ℕ) × Fin (30 : ℕ))),   x1.length ≤ (17 : ℕ) →     ∀       x3 ∈         List.foldl           (fun (x4 : List (BitVec (30 : ℕ))) (x5 : Bool × Fin (30 : ℕ) × Fin (30 : ℕ)) =>             have x6 : BitVec (30 : ℕ) := x4.getD ↑x5.2.1 (0 : BitVec (30 : ℕ));             have x7 : BitVec (30 : ℕ) := x4.getD ↑x5.2.2 (0 : BitVec (30 : ℕ));             x4 ++ [if x5.1 = Bool.true then x6 &&& x7 else x6 ||| x7])           [(579928113 : BitVec (30 : ℕ)), (419987523 : BitVec (30 : ℕ)), (608501894 : BitVec (30 : ℕ)), (169476364 : BitVec (30 : ℕ)), (23364120 : BitVec (30 : ℕ)), (201770016 : BitVec (30 : ℕ)), (3616832 : BitVec (30 : ℕ)), (28839040 : BitVec (30 : ℕ)), (834691328 : BitVec (30 : ℕ)), (1040194048 : BitVec (30 : ℕ)), (0 : BitVec (30 : ℕ)), (1073741823 : BitVec (30 : ℕ))] x1,       x3 ||| (1 : BitVec (30 : ℕ)) ≠ (32767 : BitVec (30 : ℕ)) := by
  apply PetersenPartial.exactTapeFromCases
  · intro program small found
    exact fullTape program (small.trans (by decide : 17 ≤ 18)) found
  · intro D h small test safe two
    exact PetersenPartial.TwoExit.no_two_ineligible
      PetersenPartial.requiredGeometry h test small two safe
  · intro D h small test safe three
    exact PetersenPartial.ThreeExit.no_three_ineligible
      PetersenPartial.requiredGeometry h test small three safe
  · intro D h small test safe four
    exact PetersenPartial.no_four_ineligible
      PetersenPartial.requiredGeometry h test small four safe

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem reduceToTapes
    (ordinary : ∀ P : List (Bool × Fin 30 × Fin 30), P.length ≤ 18 →
      (32767 : BitVec 30) ∉ P.foldl (fun (w : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) =>
          let a := w.getD c.2.1.val 0
          let b := w.getD c.2.2.val 0
          w ++ [if c.1 then a &&& b else a ||| b])
        ([579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823] : List (BitVec 30)))
    (oneMissing : ∀ P : List (Bool × Fin 30 × Fin 30), P.length ≤ 17 →
      ∀ w ∈ P.foldl (fun (w : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) =>
          let a := w.getD c.2.1.val 0
          let b := w.getD c.2.2.val 0
          w ++ [if c.1 then a &&& b else a ||| b]) ([579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823] : List (BitVec 30)), w ||| 1 ≠ 32767) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],           have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;           x1.eval (x7 ++ [(List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x2).all id]) ≠ x6.2) := by
  intro C items mono size arity
  let samples : List (Nat × Bool) := [(3,true),(6,true),(12,true),(24,true),(17,true),(33,true),(66,true),(132,true),(264,true),(528,true),(160,true),(640,true),(576,true),(320,true),(288,true),(50,false),(69,false),(104,false),(116,false),(138,false),(201,false),(208,false),(276,false),(385,false),(402,false),(521,false),(548,false),(554,false),(770,false),(773,false)]
  let bank (side : Bool) : List (BitVec 30) :=
    [579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823,if side then 536936448 else 1]
  let codes : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,0,1,11,12,13,14,15,16,17,18,19,10,11,2,12,20,21,22,23,24,25,26,27,10,20,3,13,21,28,29,30,31,32,33,34,10,28,4,14,22,29,35,36,37,38,39,40,10,35,5,15,23,30,36,41,42,43,44,45,10,41,6,16,24,31,37,42,46,47,48,49,10,46,7,17,25,32,38,43,47,50,51,52,10,50,8,18,26,33,39,44,48,51,53,54,10,53,9,19,27,34,40,45,49,52,54,55,10,55,10,10,10,10,10,10,10,10,10,10,10,10,0,11,20,28,35,41,46,50,53,55,10,56]
  let layouts : Array (Array Nat) := #[#[0,1,2,3,4,5,6,7,8,9,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,12,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,12,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,1],#[0,4,3,2,1,5,9,8,7,6,12,4,3,2,1,0,5,9,8,7,6,14,13,12,11,10,15,25,26,27,22,29,28,19,23,24,16,17,18,21,20,1],#[0,4,3,2,1,5,9,8,7,6,12,4,3,2,1,0,5,9,8,7,6,14,13,12,11,10,15,25,26,27,22,29,28,19,23,24,16,17,18,21,20,0],#[0,5,8,3,4,1,7,6,2,9,12,5,14,8,3,4,0,10,13,2,9,6,12,11,7,1,15,23,19,24,17,20,21,22,16,18,25,28,27,26,29,0],#[0,1,6,8,5,4,2,9,3,7,12,0,6,13,14,5,4,1,12,8,10,9,11,7,2,3,15,16,22,18,28,29,26,17,25,27,23,21,24,19,20,1],#[0,4,3,8,5,1,9,2,6,7,12,5,10,7,1,0,4,14,11,2,6,9,12,13,8,3,15,23,22,24,26,29,28,19,25,27,16,21,18,17,20,1],#[0,5,8,3,4,1,7,6,2,9,12,5,14,8,3,4,0,10,13,2,9,6,12,11,7,1,15,23,19,24,17,20,21,22,16,18,25,28,27,26,29,1],#[0,4,9,6,1,5,3,7,8,2,12,4,9,12,6,0,5,3,11,13,1,10,7,2,8,14,15,25,17,27,21,20,19,28,23,24,16,26,18,22,29,1],#[0,1,2,3,4,5,6,7,8,9,10,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[4,0,1,2,3,9,5,6,7,8,12,1,2,3,4,0,6,7,8,9,5,13,14,10,11,12,16,19,21,20,22,24,23,25,28,29,15,17,18,26,27,0],#[4,0,1,2,3,9,5,6,7,8,12,1,2,3,4,0,6,7,8,9,5,13,14,10,11,12,16,19,21,20,22,24,23,25,28,29,15,17,18,26,27,1],#[1,0,4,3,2,6,5,9,8,7,12,0,4,3,2,1,6,5,9,8,7,12,11,10,14,13,16,15,17,18,25,27,26,22,28,29,19,21,20,23,24,1],#[1,0,4,9,6,2,5,3,7,8,12,0,5,10,7,1,6,4,14,11,2,13,8,3,9,12,16,15,21,18,23,24,22,26,28,29,19,17,20,25,27,1],#[4,0,5,8,3,9,1,7,6,2,12,6,12,9,4,0,1,13,11,3,5,7,10,14,8,2,16,28,22,29,21,24,23,25,19,20,15,26,18,17,27,0],#[4,0,1,6,9,3,5,2,8,7,12,1,7,10,5,0,6,2,11,14,4,12,9,3,8,13,16,19,17,20,26,27,25,23,28,29,15,21,18,22,24,1],#[5,0,4,3,8,7,1,9,2,6,12,6,13,8,2,1,0,12,14,3,7,5,10,11,9,4,16,28,25,29,17,27,26,22,15,18,19,23,20,21,24,1],#[4,0,5,8,3,9,1,7,6,2,12,6,12,9,4,0,1,13,11,3,5,7,10,14,8,2,16,28,22,29,21,24,23,25,19,20,15,26,18,17,27,1],#[0,1,2,3,4,5,6,7,8,9,2,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[8,5,0,1,6,3,7,4,2,9,12,2,8,14,10,7,1,3,13,5,11,6,12,9,4,0,19,22,15,24,17,18,21,23,16,20,26,28,27,25,29,0],#[3,4,0,1,2,8,9,5,6,7,12,2,3,4,0,1,7,8,9,5,6,11,12,13,14,10,19,22,23,24,25,29,28,15,26,27,16,21,20,17,18,1],#[3,4,0,5,8,2,9,1,7,6,12,7,10,5,0,1,2,11,14,4,6,8,13,12,9,3,19,26,25,27,23,29,28,15,22,24,16,17,20,21,18,1],#[6,1,0,4,9,8,2,5,3,7,12,1,6,13,8,2,7,0,12,14,3,11,9,4,5,10,19,16,23,20,28,29,25,17,26,27,22,21,24,15,18,1],#[3,4,0,5,8,2,9,1,7,6,12,7,10,5,0,1,2,11,14,4,6,8,13,12,9,3,19,26,25,27,23,29,28,15,22,24,16,17,20,21,18,0],#[8,5,0,1,6,3,7,4,2,9,12,2,8,14,10,7,1,3,13,5,11,6,12,9,4,0,19,22,15,24,17,18,21,23,16,20,26,28,27,25,29,1],#[8,5,0,4,3,6,7,1,9,2,12,7,11,9,3,2,1,10,12,4,8,6,13,14,5,0,19,26,15,27,21,18,17,25,16,20,22,28,24,23,29,1],#[0,1,2,3,4,5,6,7,8,9,3,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[2,3,4,0,1,7,8,9,5,6,12,3,4,0,1,2,8,9,5,6,7,14,10,11,12,13,22,25,28,29,15,27,26,16,17,18,19,23,24,21,20,0],#[3,8,5,0,4,2,6,7,1,9,12,8,14,5,4,3,2,13,10,0,9,7,11,12,6,1,22,17,16,18,23,20,21,15,19,24,25,26,29,28,27,1],#[8,3,4,0,5,6,2,9,1,7,12,8,13,6,1,2,3,14,12,0,7,9,11,10,5,4,22,17,15,18,28,27,26,16,25,29,19,21,24,23,20,1],#[8,6,1,0,5,3,9,2,4,7,12,2,7,10,14,8,3,1,11,5,13,9,12,6,0,4,22,19,15,24,26,27,28,23,25,29,17,21,18,16,20,1],#[3,8,5,0,4,2,6,7,1,9,12,8,14,5,4,3,2,13,10,0,9,7,11,12,6,1,22,17,16,18,23,20,21,15,19,24,25,26,29,28,27,0],#[6,8,5,0,1,9,3,7,4,2,12,3,9,12,13,8,2,4,11,6,14,7,10,5,0,1,22,25,16,29,21,20,23,28,19,24,17,26,18,15,27,1],#[0,1,2,3,4,5,6,7,8,9,4,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[1,6,8,5,0,2,9,3,7,4,12,4,5,10,11,9,3,0,14,7,12,8,13,6,1,2,25,15,19,27,23,24,28,26,22,29,21,17,20,16,18,1],#[4,3,8,5,0,9,2,6,7,1,12,9,12,6,0,4,3,11,13,1,5,8,14,10,7,2,25,21,19,20,28,24,23,16,22,29,15,17,27,26,18,1],#[5,8,3,4,0,7,6,2,9,1,12,9,11,7,2,3,4,12,10,1,8,5,14,13,6,0,25,21,16,20,26,18,17,19,15,27,22,23,29,28,24,1],#[4,9,6,1,0,3,7,8,2,5,12,3,8,14,5,4,9,2,13,10,0,12,6,1,7,11,25,22,26,29,17,18,16,23,21,20,15,28,27,19,24,1],#[4,3,8,5,0,9,2,6,7,1,12,9,12,6,0,4,3,11,13,1,5,8,14,10,7,2,25,21,19,20,28,24,23,16,22,29,15,17,27,26,18,0],#[0,1,2,3,4,5,6,7,8,9,5,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[4,3,8,6,9,0,2,5,1,7,12,14,13,6,0,5,10,8,12,1,4,11,9,3,2,7,23,17,19,20,28,27,25,16,26,29,15,21,24,22,18,1],#[4,3,2,7,9,0,8,1,5,6,12,10,7,1,0,5,14,11,2,6,4,8,3,9,12,13,23,26,28,29,19,27,25,16,17,20,15,22,24,21,18,0],#[5,8,3,2,7,0,6,4,1,9,12,14,8,2,7,10,5,13,3,1,11,4,9,12,6,0,23,17,16,20,22,18,21,19,15,24,26,25,29,28,27,0],#[4,9,6,8,3,0,7,1,5,2,12,10,11,9,4,5,14,7,12,3,0,13,6,1,2,8,23,26,22,29,21,18,16,25,17,20,15,28,24,19,27,1],#[0,1,2,3,4,5,6,7,8,9,6,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[9,4,3,8,6,7,0,2,5,1,12,12,11,7,1,6,13,9,10,2,0,14,5,4,3,8,28,21,22,24,26,18,15,19,17,27,16,23,29,25,20,1],#[9,4,3,2,7,6,0,8,1,5,12,13,8,2,1,6,12,14,3,7,0,9,4,5,10,11,28,17,26,27,22,18,15,19,21,24,16,25,29,23,20,0],#[3,4,9,7,2,8,0,6,5,1,12,12,9,4,0,6,13,11,3,5,1,8,2,7,10,14,28,21,23,24,25,20,19,15,17,27,16,22,29,26,18,0],#[0,1,2,3,4,5,6,7,8,9,7,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[6,9,4,3,8,1,7,0,2,5,12,10,14,8,2,7,11,5,13,3,1,12,6,0,4,9,26,23,25,29,17,20,16,22,21,18,19,28,27,15,24,1],#[3,8,5,7,2,4,6,0,9,1,12,11,9,4,5,10,7,12,3,0,14,2,8,13,6,1,26,21,16,18,25,20,17,15,19,27,23,22,29,28,24,0],#[0,1,2,3,4,5,6,7,8,9,8,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[8,6,9,4,3,5,1,7,0,2,12,13,12,9,3,8,14,6,11,4,2,10,7,1,0,5,17,28,15,27,21,24,19,25,23,20,22,26,18,16,29,1],#[0,1,2,3,4,5,6,7,8,9,9,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,11,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0]]
  let layout (p q : Fin 12) := layouts.getD (codes.getD (12*p.val+q.val) 0) #[]
  let side (p q : Fin 12) := decide ((layout p q).getD 41 0 = 1)
  let coord (p q : Fin 12) (i : Nat) := (layout p q).getD i 0
  let row (p q : Fin 12) (r : Fin 30) := samples.getD ((layout p q).getD (11+r.val) 0) (0,false)
  let bitAt (r : Fin 30) (x : BitVec 30) := x.getLsbD r.val
  let src (p : Fin 12) (x : List Bool) := if p.val=11 then true else x.getD p.val false
  have range : ∀ (p q : Fin 12) (i : Fin 11), coord p q i.val < 13 := by decide +kernel
  have data : ∀ (p q : Fin 12) (r : Fin 30),
      let tag := row p q r
      let input := List.ofFn (fun i : Fin 10 => tag.1.testBit i.val)
      let w := bank (side p q)
      tag ∈ samples ∧ tag.2 = bitAt r 32767 ∧
        (∀ i : Fin 10, bitAt r (w.getD (coord p q i.val) 0) = input.getD i.val false) ∧
        bitAt r (w.getD (coord p q 10) 0) = (src p input && src q input) := by decide +kernel
  let conv (k : Nat) : Fin 12 := ⟨min k 10,by omega⟩
  let p := (items.map conv).getD 0 11
  let q := (items.map conv).getD 1 11
  have val (x : List Bool) (hl : x.length=10) (i : Nat) : src (conv i) x = x.getD i false := by
    by_cases h : i < 10
    · simp [src,conv,Nat.min_eq_left (show i ≤ 10 by omega),show i ≠ 11 by omega]
    · simp only [src,conv,Nat.min_eq_right (show 10 ≤ i by omega),List.getD_eq_default x false (show x.length ≤ 10 by omega),
        List.getD_eq_default x false (show x.length ≤ i by omega)]
      decide
  have supplied (x : List Bool) (hl : x.length=10) :
      (items.map (fun i => x.getD i false)).all id = (src p x && src q x) := by
    dsimp only [p,q]
    cases items with
    | nil => simp [src]
    | cons i l =>
      cases l with
      | nil =>
        change (x.getD i false && true) = (src (conv i) x && true)
        rw [val x hl]
      | cons j tail =>
        cases tail with
        | nil => simp [val x hl]
        | cons v l => simp at arity
  let ren (i : Nat) := if i<11 then coord p q i else i+2
  let narrow (i : Nat) : Fin 30 := if h : ren i < 30 then ⟨ren i,h⟩ else 10
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have andEval (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  let cmd (g : Gate) : Bool × Fin 30 × Fin 30 :=
    let isAnd := decide (g.op=GateOp.and)
    let neutral : Fin 30 := if isAnd then 11 else 10
    (isAnd,(g.inputs[0]?).elim neutral narrow,(g.inputs[1]?).elim neutral narrow)
  let step := fun (w : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) =>
          let a := w.getD c.2.1.val 0
          let b := w.getD c.2.2.val 0
          w ++ [if c.1 then a &&& b else a ||| b]
  let physical (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]
  have app {α : Type} (xs : List α) (v d : α) (k : Nat) :
      (xs++[v]).getD k d = if k=xs.length then v else xs.getD k d := by
    by_cases eq : k=xs.length
    · subst k; simp
    by_cases small : k<xs.length
    · rw [if_neg eq]; exact List.getD_append xs [v] d k small
    · rw [if_neg eq,List.getD_eq_default (xs++[v]) d (by simp;omega),List.getD_eq_default xs d (by omega)]
  have simulate (r : Fin 30) (gs : List Gate) (legal : ∀ g ∈ gs,
      (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
      (w : List Bool) (v : List (BitVec 30)) (t : Nat)
      (hw : w.length=11+t) (hv : v.length=13+t) (limit : v.length+gs.length≤31)
      (c0 : v.getD 10 0=0) (c1 : v.getD 11 0=1073741823)
      (agree : ∀ j, bitAt r (v.getD (ren j) 0) = w.getD j false) (j : Nat) :
      bitAt r (((gs.map cmd).foldl step v).getD (ren j) 0) = (gs.foldl physical w).getD j false := by
    induction gs generalizing w v t with
    | nil => exact agree j
    | cons g gs ih =>
      have bound : v.length≤30 := by simp only [List.length_cons] at limit; omega
      have read (a : Nat) : bitAt r (v.getD (narrow a).val 0) = w.getD a false := by
        by_cases h : ren a<30
        · simpa [narrow,h] using agree a
        · have hvv : v.getD (ren a) 0=0 := List.getD_eq_default _ _ (by omega)
          simp only [narrow,h,↓reduceDIte]
          change bitAt r (v.getD 10 0) = w.getD a false
          rw [c0]
          simpa only [hvv] using agree a
      have zeroVal : bitAt r (v.getD 10 0) = false := by rw [c0]; simp [bitAt]
      have oneVal : bitAt r (v.getD 11 0) = true := by
        rw [c1]
        exact (show ∀ k : Fin 30, bitAt k 1073741823 = true by decide +kernel) r
      let c := cmd g
      let z := if c.1 then v.getD c.2.1.val 0 &&& v.getD c.2.2.val 0 else v.getD c.2.1.val 0 ||| v.getD c.2.2.val 0
      let b := g.op.eval (g.inputs.map (fun k => w.getD k false))
      have brz : bitAt r z = b := by
        obtain ⟨op,len⟩ := legal g (by simp)
        have band (u vi : BitVec 30) : bitAt r (u &&& vi) = (bitAt r u && bitAt r vi) := by simp [bitAt]
        have bor (u vi : BitVec 30) : bitAt r (u ||| vi) = (bitAt r u || bitAt r vi) := by simp [bitAt]
        rcases op with op|op <;> cases hin : g.inputs with
        | nil => simp [z,b,c,cmd,op,hin,andEval,orEval,band,bor,zeroVal,oneVal,-List.getD_eq_getElem?_getD] <;> first | exact zeroVal | exact oneVal
        | cons a tail =>
          cases tail with
          | nil => simp [z,b,c,cmd,op,hin,andEval,orEval,band,bor,zeroVal,oneVal,read,-List.getD_eq_getElem?_getD] <;> first | exact (congrArg₂ Bool.and (read a) oneVal).trans (Bool.and_true _) | exact (congrArg₂ Bool.or (read a) zeroVal).trans (Bool.or_false _)
          | cons d tail =>
            cases tail with
            | nil => simp [z,b,c,cmd,op,hin,andEval,orEval,band,bor,read,-List.getD_eq_getElem?_getD] <;> first | exact congrArg₂ Bool.and (read a) (read d) | exact congrArg₂ Bool.or (read a) (read d)
            | cons e rem => simp [hin] at len
      have fresh (k : Nat) : ren k=v.length ↔ k=w.length := by
        by_cases small : k<11
        · have rr := range p q ⟨k,small⟩
          simp only [ren,small,↓reduceIte]; change coord p q k < 13 at rr; omega
        · simp only [ren,small,↓reduceIte]; omega
      have matchNext (k : Nat) : bitAt r ((v++[z]).getD (ren k) 0) = (w++[b]).getD k false := by
        rw [app,app]
        by_cases h : k = w.length
        · rw [if_pos h,if_pos ((fresh k).mpr h)]; exact brz
        · rw [if_neg h,if_neg (fun e => h ((fresh k).mp e))]; exact agree k
      change bitAt r (((gs.map cmd).foldl step (v++[z])).getD (ren j) 0) =
        (gs.foldl physical (w++[b])).getD j false
      apply ih (fun g h => legal g (by simp [h])) (w++[b]) (v++[z]) (t+1)
      · simp [hw,Nat.add_assoc]
      · simp [hv,Nat.add_assoc]
      · simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at limit ⊢; omega
      · rw [List.getD_append _ _ _ _ (by omega)]; exact c0
      · rw [List.getD_append _ _ _ _ (by omega)]; exact c1
      · exact matchNext
  let W := bank (side p q)
  let program := C.gates.map cmd
  let result := program.foldl step W
  have plen : program.length ≤ 18 := by change C.gates.length ≤ 18 at size; simpa [program] using size
  let normal : List (BitVec 30) := [579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823]
  let run (Q : List (Bool × Fin 30 × Fin 30)) := Q.foldl step normal
  let word (v : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) :=
    if c.1 then v.getD c.2.1.val 0 &&& v.getD c.2.2.val 0 else v.getD c.2.1.val 0 ||| v.getD c.2.2.val 0
  let touches (c : Bool × Fin 30 × Fin 30) := decide (c.2.1.val=12 ∨ c.2.2.val=12)
  let seed := normal ++ [0]
  have runSize (P : List (Bool × Fin 30 × Fin 30)) (v : List (BitVec 30)) :
      (P.foldl step v).length = v.length+P.length := by
    induction P generalizing v with
    | nil => simp
    | cons c cs ih =>
      change (cs.foldl step (v++[word v c])).length = _
      rw [ih]; simp; omega
  have previous (P : List (Bool × Fin 30 × Fin 30)) (v : List (BitVec 30)) (j : Nat)
      (hj : j < v.length) : (P.foldl step v).getD j 0 = v.getD j 0 := by
    induction P generalizing v with
    | nil => rfl
    | cons c cs ih =>
      change (cs.foldl step (v++[word v c])).getD j 0 = _
      rw [ih _ (by simp;omega)]
      exact List.getD_append _ _ _ _ hj
  have atMem (v : List (BitVec 30)) (k : Nat) (hz : (0 : BitVec 30) ∈ v) : v.getD k 0 ∈ v := by
    by_cases h : k<v.length
    · rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
    · rwa [List.getD_eq_default _ _ (by omega)]
  have zeroQ (Q : List (Bool × Fin 30 × Fin 30)) : (0 : BitVec 30) ∈ run Q := by
    have e : (run Q).getD 10 0 = 0 := previous Q normal 10 (by decide +kernel)
    have h : 10 < (run Q).length := by change 10<(Q.foldl step normal).length; rw [runSize]; change 10<12+Q.length; omega
    rw [←e,List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
  have zOr (v : BitVec 30) : (0 : BitVec 30) ||| v = v := by exact BitVec.zero_or
  have orZ (v : BitVec 30) : v ||| (0 : BitVec 30) = v := by exact BitVec.or_zero
  have zAnd (v : BitVec 30) : (0 : BitVec 30) &&& v = 0 := by exact BitVec.zero_and
  have andZ (v : BitVec 30) : v &&& (0 : BitVec 30) = 0 := by exact BitVec.and_zero
  have copy (P : List (Bool × Fin 30 × Fin 30)) (v : List (BitVec 30))
      (Q : List (Bool × Fin 30 × Fin 30)) (budget : Q.length+P.length ≤ 18)
      (hv : 13≤v.length) (vz : v.getD 12 0=0) (incl : ∀ w∈v, w∈run Q) :
      ∃ D, D.length ≤ Q.length + P.countP (fun c => !touches c) ∧
        ∀ w∈P.foldl step v, w∈run D := by
    induction P generalizing v Q with
    | nil => exact ⟨Q,by simp,incl⟩
    | cons c cs ih =>
      have lim : Q.length+cs.length+1 ≤18 := by simp only [List.length_cons] at budget; omega
      let z := word v c
      have inext (k : Fin 30) : v.getD k.val 0 ∈ run Q := by
        by_cases h : k.val<v.length
        · rw [List.getD_eq_getElem _ _ h]; exact incl _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (by omega)]; exact zeroQ Q
      have vz' : (v++[z]).getD 12 0 = 0 :=
        (List.getD_append _ _ _ _ (by omega)).trans vz
      have len' : 13 ≤ (v++[z]).length := by simp;omega
      by_cases touched : touches c = true
      · have hw : z ∈ run Q := by
          have choice : c.2.1.val=12 ∨ c.2.2.val=12 := of_decide_eq_true touched
          rcases choice with ha|hb
          · cases op : c.1
            · simpa only [z,word,op,Bool.false_eq_true,↓reduceIte,ha,vz,zOr] using inext c.2.2
            · simpa only [z,word,op,↓reduceIte,ha,vz,zAnd] using zeroQ Q
          · cases op : c.1
            · simpa only [z,word,op,Bool.false_eq_true,↓reduceIte,hb,vz,orZ] using inext c.2.1
            · simpa only [z,word,op,↓reduceIte,hb,vz,andZ] using zeroQ Q
        have inc (w) (h : w ∈ v++[z]) : w ∈ run Q := by
          simp only [List.mem_append,List.mem_singleton] at h
          exact h.elim (incl w) (fun e => e ▸ hw)
        obtain ⟨D,hD,hW⟩ := ih (v++[z]) Q (by omega) len' vz' inc
        exact ⟨D,by simpa [List.countP_cons,touched] using hD,hW⟩
      · have Qlen : (run Q).length < 30 := by
          change (Q.foldl step normal).length < 30
          rw [runSize]; change 12+Q.length<30; omega
        have pick (k : Fin 30) : ∃ i : Fin 30, (run Q).getD i.val 0 = v.getD k.val 0 := by
          obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp (inext k)
          exact ⟨⟨j,by omega⟩,(List.getD_eq_getElem _ _ hj).trans eq⟩
        obtain ⟨a,ha⟩ := pick c.2.1
        obtain ⟨b,hb⟩ := pick c.2.2
        let next := Q++[(c.1,a,b)]
        have eq : run next = run Q ++ [z] := by
          change (Q++[(c.1,a,b)]).foldl step normal = _
          rw [List.foldl_append]
          change run Q ++ [if c.1 then (run Q).getD a.val 0 &&& (run Q).getD b.val 0 else (run Q).getD a.val 0 ||| (run Q).getD b.val 0] = _
          rw [ha,hb]
        have inc (w) (h : w ∈ v++[z]) : w ∈ run next := by
          rw [eq]
          simp only [List.mem_append,List.mem_singleton] at h ⊢
          exact h.imp (incl w) id
        have length : next.length=Q.length+1 := by simp [next]
        obtain ⟨D,hD,hW⟩ := ih (v++[z]) next (by omega) len' vz' inc
        have nt : touches c=false := Bool.eq_false_iff.mpr touched
        refine ⟨D,?_,hW⟩
        simp only [List.countP_cons,nt,Bool.not_false,↓reduceIte]
        omega
  have compare (r : Fin 30) (rel : Bool → Bool → Prop)
      (gate : ∀ a b c d, rel a b → rel c d → rel (a && c) (b && d) ∧ rel (a || c) (b || d))
      (skip : Nat → Prop) (P : List (Bool × Fin 30 × Fin 30))
      (clean : ∀ c∈P, ¬skip c.2.1.val ∧ ¬skip c.2.2.val)
      (v w : List (BitVec 30)) (length : v.length=w.length)
      (agree : ∀ k, ¬skip k → rel (bitAt r (v.getD k 0)) (bitAt r (w.getD k 0))) :
      ∀ k, ¬skip k → rel (bitAt r ((P.foldl step v).getD k 0)) (bitAt r ((P.foldl step w).getD k 0)) := by
    induction P generalizing v w with
    | nil => exact agree
    | cons c cs ih =>
      apply ih (fun g hg => clean g (by simp [hg])) (v++[word v c]) (w++[word w c]) (by simp [length])
      intro k hk
      rw [app,app,length]
      by_cases eq : k=w.length
      · rw [if_pos eq,if_pos eq]
        obtain ⟨nx,ny⟩ := clean c (by simp)
        have zz := gate _ _ _ _ (agree _ nx) (agree _ ny)
        cases op : c.1
        · simpa only [word,op,Bool.false_eq_true,↓reduceIte,bitAt,BitVec.getLsbD_or] using zz.2
        · simpa only [word,op,↓reduceIte,bitAt,BitVec.getLsbD_and] using zz.1
      · rw [if_neg eq,if_neg eq]; exact agree k hk
  have baseBits : ∀ (s : Bool) (r : Fin 30) (i : Fin 13),
      let a := bitAt r (seed.getD i.val 0)
      let b := bitAt r ((bank s).getD i.val 0)
      (a=true → b=true) ∧ (i.val ≠ 12 → a=b) ∧ (r.val≠0 → bitAt r 32767=true → a=b) := by decide +kernel
  have bits (r : Fin 30) (i : Nat) :
      let a := bitAt r (seed.getD i 0)
      let b := bitAt r (W.getD i 0)
      (a=true → b=true) ∧ (i≠12 → a=b) ∧ (r.val≠0 → bitAt r 32767=true → a=b) := by
    by_cases h : i<13
    · exact baseBits (side p q) r ⟨i,h⟩
    · rw [List.getD_eq_default seed _ (by change 13 ≤ i; omega),List.getD_eq_default W _ (by change 13 ≤ i; omega)]
      exact ⟨id,fun _ => rfl,fun _ _ => rfl⟩
  have reject : (32767 : BitVec 30) ∉ result := by
    intro member
    obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp member
    have high : result.getD j 0=32767 := (List.getD_eq_getElem _ _ hj).trans e
    have jValid : j≠12 := by
      rintro rfl
      have kept : result.getD 12 0 = W.getD 12 0 := previous program W 12 (by change 12 < 13; decide)
      have impossible : W.getD 12 0 ≠ 32767 := by cases h : side p q <;> simp [W,h,bank]
      exact impossible (kept.symm.trans high)
    let low := program.foldl step seed
    have ls : seed.length=13 := rfl
    have lw : W.length=13 := rfl
    have sz : low.length=result.length :=
      (runSize program seed).trans ((congrArg (fun n : Nat => n+program.length) (ls.trans lw.symm)).trans (runSize program W).symm)
    have jl : j < low.length := lt_of_lt_of_eq hj sz.symm
    have inlow : low.getD j 0 ∈ low := by rw [List.getD_eq_getElem low 0 jl]; exact List.getElem_mem jl
    have inc (v) (h : v∈seed) : v∈run [] := by
      change v∈normal
      simp only [seed,List.mem_append,List.mem_singleton] at h
      exact h.elim id (fun e => e ▸ (by decide +kernel : (0 : BitVec 30) ∈ normal))
    obtain ⟨D,length,cover⟩ := copy program seed [] (by simpa using plen) (by decide +kernel) (by decide +kernel) inc
    have inD := cover _ inlow
    have eqRule : ∀ a b c d : Bool, a=b → c=d → (a && c)=(b && d) ∧ (a || c)=(b || d) := by decide
    have impRule : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
        ((a&&c)=true → (b&&d)=true) ∧ ((a||c)=true → (b||d)=true) := by decide
    by_cases used : ∃ c∈program, touches c=true
    · have saving (P : List (Bool × Fin 30 × Fin 30)) (h : ∃ c∈P, touches c=true) :
          P.countP (fun c => !touches c) < P.length := by
        induction P with
        | nil => simp at h
        | cons c cs ih =>
          by_cases hit : touches c=true
          · simpa [List.countP_cons,hit] using (Nat.lt_succ_of_le (List.countP_le_length (p:=fun c => !touches c) (l:=cs)))
          · obtain ⟨g,hg,good⟩ := h
            have tail : g∈cs := (List.mem_cons.mp hg).resolve_left (fun eq => hit (eq ▸ good))
            have lt := ih ⟨g,tail,good⟩
            have neg : touches c=false := Bool.eq_false_iff.mpr hit
            simp [List.countP_cons,neg,lt]
      have dsize : D.length≤17 := by have save := saving program used; simp only [List.length_nil,Nat.zero_add] at length;omega
      apply oneMissing D dsize _ inD
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let r : Fin 30 := ⟨i,hi⟩
      change bitAt r ((low.getD j 0) ||| 1) = bitAt r 32767
      have mask : ∀ r : Fin 30, bitAt r 1 = decide (r.val=0) := by decide +kernel
      have bor (a b : BitVec 30) : bitAt r (a ||| b) = (bitAt r a || bitAt r b) := by simp [bitAt]
      rw [bor,mask]
      let f := bitAt r (low.getD j 0)
      change (f || decide (r.val=0)) = bitAt r 32767
      by_cases lead : r.val=0
      · have yes : bitAt r 32767=true := (show ∀ z : Fin 30, z.val=0 → bitAt z 32767=true by decide +kernel) _ lead
        exact (congrArg (fun x => f || x) (decide_eq_true lead)).trans ((Bool.or_true f).trans yes.symm)
      · have lowToHigh := compare r (fun a b => a=true → b=true) impRule (fun _ => False) program
            (fun _ _ => ⟨id,id⟩) seed W (ls.trans lw.symm) (fun k _ => (bits r k).1) j id
        have highToLow (positive : bitAt r 32767 = true) : f=true := by
          have eq := compare r Eq eqRule (fun _ => False) program (fun _ _ => ⟨id,id⟩)
            seed W (ls.trans lw.symm) (fun k _ => (bits r k).2.2 lead positive) j id
          exact eq.trans ((congrArg (bitAt r) high).trans positive)
        have valEq : f=bitAt r 32767 := Bool.eq_iff_iff.mpr
          ⟨fun h => (congrArg (bitAt r) high).symm.trans (lowToHigh h),highToLow⟩
        exact (congrArg (fun x => f || x) (decide_eq_false lead)).trans ((Bool.or_false f).trans valEq)
    · have dsize : D.length≤18 := by
        have sm := List.countP_le_length (p:=fun c => !touches c) (l:=program)
        simp only [List.length_nil,Nat.zero_add] at length
        omega
      have same : low.getD j 0=32767 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        let r : Fin 30 := ⟨i,hi⟩
        have clean (c) (h : c∈program) : c.2.1.val≠12 ∧ c.2.2.val≠12 := by
          have no (w : c.2.1.val=12 ∨ c.2.2.val=12) : False :=
            used ⟨c,h,decide_eq_true w⟩
          exact ⟨fun a => no (Or.inl a),fun b => no (Or.inr b)⟩
        have rr := compare r Eq eqRule (fun k => k=12) program clean seed W (ls.trans lw.symm)
          (fun k ne => (bits r k).2.1 ne) j jValid
        change bitAt r (low.getD j 0)=bitAt r (result.getD j 0) at rr
        exact rr.trans (congrArg (bitAt r) high)
      exact ordinary D dsize ((congrArg (fun x : BitVec 30 => x ∈ run D) same).mp inD)
  by_contra noWitness
  push Not at noWitness
  have out : result.getD (ren C.output) 0 = (32767 : BitVec 30) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i lt
    let r : Fin 30 := ⟨i,lt⟩
    let lab := row p q r
    let x := List.ofFn (fun j : Fin 10 => lab.1.testBit j.val)
    let add := (items.map (fun k => x.getD k false)).all id
    obtain ⟨mem,right,prim,extra⟩ := data p q r
    have hx : x.length=10 := by simp [x]
    have bankLen : W.length=13 := by cases side p q <;> rfl
    have init (j : Nat) : bitAt r (W.getD (ren j) 0) = (x++[add]).getD j false := by
      rw [app,hx]
      by_cases hi : j<10
      · simpa only [ren,show j<11 by omega,↓reduceIte,show j≠10 by omega,ite_false] using prim ⟨j,hi⟩
      by_cases he : j=10
      · subst j
        simpa only [ren,if_pos (by decide : 10<11),ite_true,add,supplied x hx] using extra
      · have large : 11 ≤ j := by omega
        simp only [ren,show ¬j<11 by omega,↓reduceIte,he,ite_false]
        rw [List.getD_eq_default W _ (by omega),List.getD_eq_default x _ (by omega)]
        simp [bitAt]
    have forward := simulate r C.gates (fun g hg => by simpa using mono g hg) (x++[add]) W 0
      (by simp [hx]) (by simp [bankLen]) (by change C.gates.length ≤ 18 at size; omega)
      (by cases side p q <;> rfl) (by cases side p q <;> rfl) init C.output
    change bitAt r (result.getD (ren C.output) 0) = bitAt r 32767
    exact forward.trans ((Classical.not_not.mp (noWitness lab mem)).trans right)
  by_cases h : ren C.output < result.length
  · apply reject
    rw [←out,List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ (by omega)] at out
    exact (by decide : (0 : BitVec 30) ≠ 32767) out

end PEqualNP.Outside.L_meta_7107

namespace PEqualNP.Outside.L_meta_7107
namespace Compilation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 10 → Bool
abbrev F := X → Bool

def pins : List F := (List.ofFn fun i : Fin 10 => fun x : X => x i) ++
  [fun x => x 0 && x 1]
def withConstants (fs : List F) : List F := (fun _ => false) :: (fun _ => true) :: fs
def merge (op : Bool) (a b : F) : F :=
  fun x => if op then a x && b x else a x || b x

private theorem merge_left (op val : Bool) (f : F) :
    merge op (fun _ => val) f = (fun _ => val) ∨ merge op (fun _ => val) f = f := by
  cases op <;> cases val
  · right; funext x; simp [merge]
  · left; funext x; simp [merge]
  · left; funext x; simp [merge]
  · right; funext x; simp [merge]

private theorem merge_comm (op : Bool) (a b : F) :
    merge op a b = merge op b a := by
  funext x
  cases op <;> simp [merge, Bool.and_comm, Bool.or_comm]

private theorem retain {fs : List F} {f a b : F} {op : Bool}
    (ha : a ∈ withConstants fs) (hb : b ∈ withConstants fs)
    (hnew : f ∉ withConstants fs) (h : f = merge op a b) : a ∈ fs := by
  have dropConst (v : Bool) (e : a = fun _ => v) : False := by
    have m := merge_left op v b
    rw [e] at h
    rcases m with m | m
    · exact hnew ((h.trans (m.trans e.symm)).symm ▸ ha)
    · exact hnew ((h.trans m).symm ▸ hb)
  rcases List.mem_cons.mp ha with h0 | ha
  · exact (dropConst false h0).elim
  rcases List.mem_cons.mp ha with h1 | ha
  · exact (dropConst true h1).elim
  exact ha

def values (fs : List F) (x : X) := fs.map (fun f => f x)
def run (gs : List Gate) (x : X) := (Circuit.mk gs 0).wires (values pins x)

private theorem snoc (gs : List Gate) (g : Gate) (x : X) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, Circuit.wires, List.foldl_append]

private theorem valueAt {fs : List F} {f : F} (hf : f ∈ fs) :
    ∃ i : ℕ, ∀ x : X, (values fs x).getD i false = f x := by
  obtain ⟨i,hi,e⟩ := List.getElem_of_mem hf
  refine ⟨i,fun x => ?_⟩
  simp [values, List.getD_eq_getElem?_getD, hi, e]

theorem compile (fs : List F) (step : ∀ i : Fin fs.length,
    let s := withConstants (pins ++ fs.take i.val)
    fs.get i ∉ s ∧ ∃ a ∈ s, ∃ b ∈ s, ∃ op : Bool, fs.get i = merge op a b) :
    ∃ gs : List Gate, gs.length = fs.length ∧ Monotone2 ⟨gs,0⟩ ∧
      ∀ x : X, run gs x = values (pins ++ fs) x := by
  have build (k : ℕ) (hk : k ≤ fs.length) :
      ∃ gs : List Gate, gs.length = k ∧ Monotone2 ⟨gs,0⟩ ∧
        ∀ x : X, run gs x = values (pins ++ fs.take k) x := by
    induction k with
    | zero => exact ⟨[],rfl,fun g hg => by simp at hg,by simp [run, Circuit.wires]⟩
    | succ k ih =>
      have hk' : k < fs.length := hk
      obtain ⟨gs,hl,hmono,hrun⟩ := ih (by omega)
      obtain ⟨hn,a,ha,b,hb,op,he⟩ := step ⟨k,hk'⟩
      obtain ⟨ia,hA⟩ := valueAt (retain ha hb hn he)
      obtain ⟨ib,hB⟩ := valueAt (retain hb ha hn (he.trans (merge_comm op a b)))
      let g : Gate := ⟨if op then .and else .or,[ia,ib]⟩
      refine ⟨gs ++ [g], by simp [hl], ?_, ?_⟩
      · intro j hj
        change j ∈ gs ++ [g] at hj
        rcases List.mem_append.mp hj with h | h
        · exact hmono j h
        · obtain rfl : j = g := List.mem_singleton.mp h
          cases op <;> simp [g]
      · intro x
        rw [snoc, hrun, List.take_succ_eq_append_getElem hk']
        have ev := congrFun he x
        change fs[k] x = merge op a b x at ev
        rw [← List.append_assoc]
        have gateValue : g.op.eval (g.inputs.map fun i => (values (pins ++ fs.take k) x).getD i false)
            = fs[k] x := by
          rw [ev]
          have ha' := hA x
          have hb' := hB x
          rw [List.getD_eq_getElem?_getD] at ha' hb'
          cases op <;> simp [g, GateOp.eval, ha', hb', merge]
        rw [gateValue]
        simp only [values, List.map_append, List.map_cons, List.map_nil]
  simpa using build fs.length (le_refl _)

end Compilation
end PEqualNP.Outside.L_meta_7107

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_7107 PEqualNP.Outside.L_meta_7107.Compilation in
theorem PEqualNP.Outside.L_meta_7107 : (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2, ∀ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 → (¬(x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true → x5 ≠ fun (x11 : Fin (10 : ℕ) → Bool) => x11 x7 && x11 x8) ∧ x5 ≠ fun (x10 : Fin (10 : ℕ) → Bool) => x10 x7 || x10 x8) → (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  intro E fs hlen hw _ hmem
  obtain ⟨gs, hgl, hm, hr⟩ := compile fs (by
    intro i
    obtain ⟨hn,a,ha,b,hb,h⟩ := hw i
    refine ⟨hn,a,ha,b,hb,?_⟩
    rcases h with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩)
  let ef : F := fun x => E.any (fun e => x e.1 && x e.2)
  have hfun : ef ∈ pins ++ fs := List.mem_append_right _ hmem
  obtain ⟨i,hi,h⟩ := List.getElem_of_mem hfun
  let C : Circuit := ⟨gs,i⟩
  have hc (x : X) : C.eval (values pins x) = ef x := by
    change (run gs x).getD i false = _
    rw [hr]
    rw [List.getD_eq_getElem _ _ (by simpa only [values,List.length_map] using hi)]
    simp only [values,List.getElem_map,h]
  have hs : C.size ≤ 18 := by change gs.length ≤ 18; omega
  obtain ⟨r,hrmem,hrwrong⟩ := reduceToTapes fullTape oneMissing C [0,1] hm hs (by decide)
  let x : X := fun t => r.1.testBit t.val
  have hp : values pins x = List.ofFn x ++ [x 0 && x 1] := by
    simp [values, pins, List.map_ofFn, Function.comp_def]
  have fixed : ∀ q ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)], ef (fun t => q.1.testBit t.val) = q.2 := by decide +kernel
  have hinput : (List.map (fun w => (List.ofFn x).getD w false) [0,1]).all id = (x 0 && x 1) := by
    simp [List.getD_eq_getElem?_getD]
  apply hrwrong
  change C.eval (List.ofFn x ++ [(List.map (fun w => (List.ofFn x).getD w false) [0,1]).all id]) = r.2
  rw [hinput, ← hp, hc]
  exact fixed r hrmem
