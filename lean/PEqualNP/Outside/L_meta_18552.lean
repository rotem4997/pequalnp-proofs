import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18552_aux.Normalize

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] =>
    if j = k then (none, Stat.wire j) else (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] =>
    if j = k then (none, Stat.wire j) else (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom] <;>
        split_ifs at * <;> simp_all [Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom] <;>
        split_ifs at * <;> simp_all [Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PEqualNP.TopForm

private def good (m : ℕ) (g : Gate) : Prop :=
    (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) ∧
    g.inputs.length = 2 ∧ g.inputs.Nodup ∧ ∀ i ∈ g.inputs, i < m

private def packed (n : ℕ) (gs : List Gate) : Prop :=
    ∀ j < gs.length, good (n+j) (gs.getD j ⟨.or, []⟩)

private theorem emitted_good (op : GateOp) (hop : op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (m : ℕ) (ins : List Stat) (valid : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, good m g := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd, good, Stat.Valid] <;>
      split_ifs at * <;> simp_all [good, Stat.Valid]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr, good, Stat.Valid] <;>
      split_ifs at * <;> simp_all [good, Stat.Valid]

private theorem packed_extend (n : ℕ) (gs : List Gate) (step : Option Gate)
    (h : packed n gs) (hstep : ∀ g ∈ step, good (n+gs.length) g) :
    packed n (gs ++ step.toList) := by
  cases step with
  | none => simpa using h
  | some g =>
    intro j hj
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj']
      exact h j hj'
    · have he : j = gs.length := by simp at hj; omega
      subst j
      simpa using hstep g (by simp)

private theorem elim_packed (n : ℕ) (gs : List Gate) (y : List Bool) (hy : y.length = n)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (acc : List Stat × List Gate)
    (hs : Inv n y w acc) (hp : packed n acc.2) :
    packed n (elim n gs acc).2 := by
  induction gs generalizing acc w with
  | nil => exact hp
  | cons g gs ih =>
    have hOk (g' : Gate) (mem : g' ∈ g :: gs) : Ok g' := by
      obtain ⟨op,len⟩ := hmono g' mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
      exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), len⟩
    apply ih (fun g' hg => hmono g' (List.mem_cons_of_mem _ hg))
      (wiresFrom [g] w) (elimStep n acc g)
    · exact inv_elim n y hy [g] w acc
        (fun g' hg => hOk g' (List.mem_cons.mpr (Or.inl (by simpa using hg)))) hs
    · unfold elimStep
      refine packed_extend _ _ _ hp (emitted_good g.op (hmono g (by simp)).1 _ _ ?_)
      intro s h
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      exact (hs.2 a).1

private def startStats (n : ℕ) : List Stat :=
    List.ofFn (fun i : Fin n => Stat.wire i)

private theorem inv_start (n : ℕ) (y : List Bool) (hy : y.length = n) :
    Inv n y y (startStats n, []) := by
  refine ⟨by simp [startStats, hy], ?_⟩
  intro i
  change ((startStats n).getD i (.const false)).Valid (n+0) ∧
    ((startStats n).getD i (.const false)).val y = y.getD i false
  by_cases hi : i < n
  · simp [startStats, List.getD_eq_getElem?_getD, hi, Stat.Valid, Stat.val]
  · simp [startStats, List.getD_eq_getElem?_getD, hi, hy, Stat.Valid, Stat.val]

private theorem packed_isAO2 {n : ℕ} {gs : List Gate} (h : packed n gs) (o : ℕ) :
    IsAO2 n (⟨gs,o⟩ : Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have hh := h j hj
    rw [List.getD_eq_getElem?_getD] at hh
    exact (by simpa [hj] using hh.1)
  · intro j hj i hi
    exact (h j hj).2.2.2 i hi
  · intro g mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have hh := h j hj
    rw [List.getD_eq_getElem?_getD] at hh
    exact (by simpa [hj] using hh.2.1)

private theorem packed_nodup {n : ℕ} {gs : List Gate} (h : packed n gs) :
    ∀ g ∈ gs, g.inputs.Nodup := by
  intro g mem
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp mem
  have hh := h j hj
  rw [List.getD_eq_getElem?_getD] at hh
  simpa [hj] using hh.2.2.1

/-- Fold missing inputs, constants, copies, and repeated operands. -/
theorem normalize_nonconstant {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (hne : C.eval x ≠ C.eval y) :
    ∃ D : Circuit, IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      D.size ≤ C.size ∧ D.output < n+D.gates.length ∧
      ∀ z : List Bool, z.length = n → D.eval z = C.eval z := by
  let a := elim n C.gates (startStats n, [])
  have hOk (g : Gate) (mem : g ∈ C.gates) : Ok g := by
    obtain ⟨op,len⟩ := mono g mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), len⟩
  have hInv (z : List Bool) (hz : z.length = n) :
      Inv n z (wiresFrom C.gates z) a :=
    inv_elim n z hz C.gates z _ hOk (inv_start n z hz)
  have hp : packed n a.2 := elim_packed n C.gates x hx mono x _
    (inv_start n x hx) (by simp [packed])
  have hl : a.2.length ≤ C.gates.length := by
    simpa [a] using elim_len n C.gates (startStats n, [])
  cases hs : a.1.getD C.output (.const false) with
  | const b =>
    apply False.elim
    apply hne
    have ex := ((hInv x hx).2 C.output).2
    have ey := ((hInv y hy).2 C.output).2
    rw [hs] at ex ey
    exact ex.symm.trans ey
  | wire o =>
    have hh := ((hInv x hx).2 C.output).1
    rw [hs] at hh
    refine ⟨⟨a.2,o⟩, packed_isAO2 hp o, packed_nodup hp, hl, hh, ?_⟩
    intro z hz
    have e := ((hInv z hz).2 C.output).2
    rw [hs] at e
    exact e

end PEqualNP.Outside.L_meta_18552_aux.Normalize

namespace PEqualNP.Outside.L_meta_18552_aux.Relabel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem getD_snoc_eq {α : Type} (L : List α) (v d : α) :
    (L ++ [v]).getD L.length d = v := by simp

/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private theorem wmap_injective {n m : ℕ} {π : Fin n → Fin m} (inj : Function.Injective π) :
    Function.Injective (wmap n m π) := by
  intro a b eq
  unfold wmap at eq
  split_ifs at eq with ha hb hb
  · exact congrArg Fin.val (inj (Fin.ext eq))
  · have h := (π ⟨a,ha⟩).isLt
    omega
  · have h := (π ⟨b,hb⟩).isLt
    omega
  · omega

private theorem read_back {n m : ℕ} (π : Fin n → Fin m) (D : Circuit) (rb : ReadsBack n D) :
    ReadsBack m (relabel n m π D) := by
  intro j hj i hi
  have idx : j < D.gates.length := by simpa [relabel] using hj
  have get : gateAt (relabel n m π D) j = relGate n m π (gateAt D j) := by
    simp [gateAt, relabel, List.getD_eq_getElem?_getD, idx]
  rw [get] at hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  have above := rb j idx a ha
  unfold wmap
  split
  · have h := (π ⟨a,by assumption⟩).isLt
    omega
  · omega

theorem transport {n m : ℕ} (π : Fin n → Fin m) (inj : Function.Injective π)
    (D : Circuit) (ao : IsAO2 n D) (nd : ∀ g ∈ D.gates, g.inputs.Nodup)
    (out0 : n ≤ D.output) (out1 : D.output < n + D.size) :
    let E := relabel n m π D
    IsAO2 m E ∧ (∀ g ∈ E.gates, g.inputs.Nodup) ∧ m ≤ E.output ∧ E.output < m + E.size ∧
      E.size = D.size ∧ ∀ x : Fin m → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn (x ∘ π)) := by
  have hSize : (relabel n m π D).size = D.size := by simp [relabel, Circuit.size]
  have good (g : Gate) (hg : g ∈ (relabel n m π D).gates) :
      ∃ g' ∈ D.gates, g = relGate n m π g' := by
    obtain ⟨g', h, rfl⟩ := List.mem_map.mp hg
    exact ⟨g', h, rfl⟩
  have output : (relabel n m π D).output = D.output - n + m := by
    simp [relabel, wmap, Nat.not_lt.mpr out0]
  refine ⟨⟨?_, read_back π D ao.2.1, ?_⟩, ?_, ?_, ?_, hSize, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := good g hg
    exact ao.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := good g hg
    simpa [relGate] using ao.2.2 g' hg'
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := good g hg
    exact List.Nodup.map (wmap_injective inj) (nd g' hg')
  · rw [output]; omega
  · rw [output, hSize]; omega
  · intro x
    exact (rel_fold n m π D.gates _ _ (rel_init n m π x)).2.2 D.output

end PEqualNP.Outside.L_meta_18552_aux.Relabel

namespace PEqualNP.Outside.L_meta_18552_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem result (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (inj : Function.Injective π) (mono : Monotone2 C)
    (nonconst : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (nonproj : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i) :
    ∃ E : Circuit, IsAO2 m E ∧ (∀ g ∈ E.gates, g.inputs.Nodup) ∧
      m ≤ E.output ∧ E.output < m + E.size ∧ E.size ≤ C.size ∧
      ∀ x : Fin m → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  let zero : Fin n → Bool := fun _ => false
  obtain ⟨x, hx⟩ := nonconst (C.eval (List.ofFn zero))
  obtain ⟨D, ao, nd, cost, out1, agree⟩ := Normalize.normalize_nonconstant (n := n) mono
    (x := List.ofFn x) (y := List.ofFn zero) (by simp) (by simp) hx
  have out0 : n ≤ D.output := by
    by_contra! raw
    obtain ⟨y, hy⟩ := nonproj ⟨D.output, raw⟩
    apply hy
    rw [← agree _ (by simp)]
    change (Normalize.wiresFrom D.gates (List.ofFn y)).getD D.output false = y ⟨D.output, raw⟩
    obtain ⟨tail, eq, _⟩ := Normalize.wiresFrom_prefix D.gates (List.ofFn y)
    rw [eq, List.getD_append _ _ _ _ (by simpa using raw)]
    simp [List.getD_eq_getElem?_getD, raw]
  obtain ⟨ok, u, lo, hi, sameSize, run⟩ := Relabel.transport π inj D ao nd out0 out1
  exact ⟨_, ok, u, lo, hi, sameSize.trans_le cost,
    fun y => (run y).trans (agree (List.ofFn (y ∘ π)) (by simp))⟩

end PEqualNP.Outside.L_meta_18552_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm in
theorem PEqualNP.Outside.L_meta_18552 :
    ∀ (n m : ℕ) (π : Fin n → Fin m) (C : Circuit), Function.Injective π → Monotone2 C →
      (∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b) →
      (∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i) →
      ∃ E : Circuit, IsAO2 m E ∧ (∀ g ∈ E.gates, g.inputs.Nodup) ∧
        m ≤ E.output ∧ E.output < m + E.size ∧ E.size ≤ C.size ∧
        ∀ x : Fin m → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) :=
  PEqualNP.Outside.L_meta_18552_aux.result
