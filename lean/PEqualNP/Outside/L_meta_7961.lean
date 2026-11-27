import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7961

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit simplifier is adapted from L_meta_7328 and L_meta_1411
-- in open-goat/pequalnp-proofs under the Apache 2.0 license.
abbrev Stat := Bool ⊕ ℕ

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

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma op_cases {g : Gate} (h : Good g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa using h.1

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Good g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Good]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Good]
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Good g) → Inv n y w acc →
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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op (op_cases hgok) w' ins (by simpa [hins] using hgok.2)
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
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

-- Every gate with a constant input can be omitted. An absorbing input
-- additionally marks the gate output as a constant for the next gate.
def absorb : GateOp → Bool
  | .or => true
  | _ => false

lemma simplify_drop (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : ∃ b, Sum.inl b ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨b, hb⟩
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hb hl
  all_goals cases s <;> (try cases t) <;> simp_all [simplify, simpAnd, simpOr]

lemma simplify_absorb (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : Sum.inl (absorb op) ∈ ins) :
    (simplify op m ins).2 = Sum.inl (absorb op) := by
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hc hl
  all_goals cases s <;> (try cases t) <;> simp_all [absorb, simplify, simpAnd, simpOr]
  grind

abbrev State := List Stat × List Gate

def stat (s : State) (i : ℕ) : Stat := s.1.getD i (Sum.inl false)

def plan (n : ℕ) (s : State) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + s.2.length) (g.inputs.map (stat s))

lemma elim_append (n : ℕ) (pre post : List Gate) (s : State) :
    elim n (pre ++ post) s = elim n post (elim n pre s) := by
  simp [elim, List.foldl_append]

lemma elim_extends (n : ℕ) (gs : List Gate) (s : State) :
    ∃ t, (elim n gs s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (elimStep n s g)
    refine ⟨(plan n s g).2 :: t, ?_, by simp [hlen]⟩
    change (elim n gs (elimStep n s g)).1 = _
    rw [ht]
    change (s.1 ++ [(plan n s g).2]) ++ t = _
    simp

lemma elim_stat (n : ℕ) (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    stat (elim n gs s) i = stat s i := by
  obtain ⟨t, ht, _⟩ := elim_extends n gs s
  unfold stat
  rw [ht, List.getD_append _ _ _ _ hi]

lemma elim_good (n : ℕ) (gs : List Gate) (s : State)
    (h : ∀ g ∈ gs, Good g) (hs : ∀ g ∈ s.2, Good g) :
    ∀ g ∈ (elim n gs s).2, Good g := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    change ∀ g' ∈ (elim n gs (elimStep n s g)).2, Good g'
    apply ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    intro a ha
    change a ∈ s.2 ++ (plan n s g).1.toList at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hs a ha
    · exact simplify_ok _ _ _ a (by simpa [plan] using ha)

def fix {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = p then b else x i

def initial {n : ℕ} (p : Fin n) (b : Bool) : State :=
  (List.ofFn fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val, [])

lemma initial_length {n : ℕ} (p : Fin n) (b : Bool) :
    (initial p b).1.length = n := by simp [initial]

lemma initial_stat {n : ℕ} (p : Fin n) (b : Bool) : stat (initial p b) p.val = Sum.inl b := by
  simp [stat, initial]

lemma initial_inv {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (fix p b x)) (initial p b) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (stat (initial p b) j.val).Valid _ ∧ (stat (initial p b) j.val).val _ = _
    by_cases hj : j = p <;>
      simp [stat, initial, fix, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at *
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma drop_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} {b : Bool} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl b) :
    (plan n s g).1 = none := by
  apply simplify_drop _ (op_cases hg) _ _ (by simpa using hg.2)
  exact ⟨b, hb ▸ List.mem_map_of_mem hi⟩

lemma absorb_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl (absorb g.op)) :
    (plan n s g).2 = Sum.inl (absorb g.op) := by
  apply simplify_absorb _ (op_cases hg) _ _ (by simpa using hg.2)
  exact hb ▸ List.mem_map_of_mem hi

lemma restriction (C : Circuit) (hm : Monotone2 C) {n : ℕ} (p : Fin n) (b : Bool)
    (hnc : ∃ x y, circuitFun n C (fix p b x) ≠ circuitFun n C (fix p b y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧
      D.size = (elim n C.gates (initial p b)).2.length := by
  let s := elim n C.gates (initial p b)
  have hval (x : Fin n → Bool) :
      (stat s C.output).val (wiresFrom s.2 (List.ofFn x)) =
        circuitFun n C (fix p b x) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ hm (initial_inv p b x)).2 C.output).2
  cases hz : stat s C.output with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x
    have hy := hval y
    rw [hz] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨s.2, j⟩, elim_good n _ _ hm (by simp [initial]), ?_, rfl⟩
    intro x
    change (wiresFrom s.2 (List.ofFn x)).getD j false = _
    simpa only [hz, Stat.val] using hval x

lemma single_drop {n : ℕ} (p : Fin n) (b : Bool) (pre post : List Gate) (g : Gate)
    (hg : Good g) (hp : p.val ∈ g.inputs) :
    (elim n (pre ++ g :: post) (initial p b)).2.length + 1 ≤
      (pre ++ g :: post).length := by
  let s := elim n pre (initial p b)
  have hs : stat s p.val = Sum.inl b :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p b)
  have hd := drop_at_reader n s g hg hp hs
  have hpre := elim_len n pre (initial p b)
  have hpost := elim_len n post (elimStep n s g)
  rw [elim_append]
  change (elim n post (elimStep n s g)).2.length + 1 ≤ _
  have hstep : (elimStep n s g).2.length = s.2.length := by
    change (s.2 ++ (plan n s g).1.toList).length = _
    simp [hd]
  rw [hstep] at hpost
  change s.2.length ≤ 0 + pre.length at hpre
  simp only [List.length_append, List.length_cons]
  omega

lemma double_drop {n : ℕ} (p : Fin n) (pre mid post : List Gate) (g h : Gate)
    (hg : Good g) (hh : Good h) (hp : p.val ∈ g.inputs) (hr : n + pre.length ∈ h.inputs) :
    (elim n (pre ++ g :: (mid ++ h :: post)) (initial p (absorb g.op))).2.length + 2 ≤
      (pre ++ g :: (mid ++ h :: post)).length := by
  let s := elim n pre (initial p (absorb g.op))
  let t := elimStep n s g
  let u := elim n mid t
  have hs : stat s p.val = Sum.inl (absorb g.op) :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p _)
  have hd := drop_at_reader n s g hg hp hs
  have hc := absorb_at_reader n s g hg hp hs
  obtain ⟨suffix, hext, hlen⟩ := elim_extends n pre (initial p (absorb g.op))
  have hl : s.1.length = n + pre.length := by
    change (elim n pre (initial p (absorb g.op))).1.length = _
    rw [hext, List.length_append, initial_length, hlen]
  have ht : stat t (n + pre.length) = Sum.inl (absorb g.op) := by
    change (s.1 ++ [(plan n s g).2]).getD (n + pre.length) _ = _
    rw [getD_snoc_len _ _ _ _ hl, hc]
  have hlt : n + pre.length < t.1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [hl]
  have hu := (elim_stat n mid t _ hlt).trans ht
  have hd' := drop_at_reader n u h hh hr hu
  have hpre := elim_len n pre (initial p (absorb g.op))
  have hmid := elim_len n mid t
  have hpost := elim_len n post (elimStep n u h)
  have hstep : t.2.length = s.2.length := by
    change (s.2 ++ (plan n s g).1.toList).length = _
    simp [hd]
  have hstep' : (elimStep n u h).2.length = u.2.length := by
    change (u.2 ++ (plan n u h).1.toList).length = _
    simp [hd']
  rw [hstep] at hmid
  rw [hstep'] at hpost
  change s.2.length ≤ 0 + pre.length at hpre
  change u.2.length ≤ _ at hmid
  rw [elim_append]
  change (elim n (mid ++ h :: post) t).2.length + 2 ≤ _
  rw [elim_append]
  change (elim n post (elimStep n u h)).2.length + 2 ≤ _
  simp only [List.length_append, List.length_cons]
  omega

-- A dependency trace either reaches a direct reader or contains two successive gates.
def Direct (n p w : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre post : List Gate) (g : Gate),
    gs = pre ++ g :: post ∧ p ∈ g.inputs ∧ w = n + pre.length

def Chain (n p : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre mid post : List Gate) (g h : Gate),
    gs = pre ++ g :: (mid ++ h :: post) ∧ p ∈ g.inputs ∧ n + pre.length ∈ h.inputs

lemma wire_trace {n p : ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ w, w ≠ p → x.getD w false = y.getD w false)
    (gs : List Gate) (w : ℕ)
    (hne : (wiresFrom gs x).getD w false ≠ (wiresFrom gs y).getD w false) :
    w = p ∨ Direct n p w gs ∨ Chain n p gs := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    exact Or.inl (by by_contra h; exact hne (hxy w h))
  | append_singleton gs g ih =>
    have hxlen : (wiresFrom gs x).length = n + gs.length := by rw [length_wiresFrom, hx]
    have hylen : (wiresFrom gs y).length = n + gs.length := by rw [length_wiresFrom, hy]
    rw [wiresFrom_append, wiresFrom_append] at hne
    change ((wiresFrom gs x) ++ [_]).getD w false ≠
      ((wiresFrom gs y) ++ [_]).getD w false at hne
    by_cases hw : w = n + gs.length
    · rw [getD_snoc_len _ _ _ _ (hxlen.trans hw.symm),
          getD_snoc_len _ _ _ _ (hylen.trans hw.symm)] at hne
      obtain ⟨i, hi, hdiff⟩ : ∃ i ∈ g.inputs,
          (wiresFrom gs x).getD i false ≠ (wiresFrom gs y).getD i false := by
        by_contra! hsame
        apply hne
        apply congrArg (GateOp.eval g.op)
        exact List.map_congr_left hsame
      rcases ih i hdiff with rfl | ⟨pre, post, h, he, hr, rfl⟩ | ⟨pre, mid, post, h, k, he, hr, hs⟩
      · exact Or.inr (Or.inl ⟨gs, [], g, rfl, hi, hw⟩)
      · exact Or.inr (Or.inr ⟨pre, post, [], h, g, by simp [he, List.append_assoc], hr, hi⟩)
      · exact Or.inr (Or.inr ⟨pre, mid, post ++ [g], h, k,
          by simp [he, List.append_assoc], hr, hs⟩)
    · rw [getD_snoc_ne _ _ _ _ (by rwa [hxlen]), getD_snoc_ne _ _ _ _ (by rwa [hylen])] at hne
      rcases ih w hne with hp | ⟨pre, post, h, he, hr, hval⟩ | ⟨pre, mid, post, h, k, he, hr, hs⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨pre, post ++ [g], h, by simp [he, List.append_assoc], hr, hval⟩)
      · exact Or.inr (Or.inr ⟨pre, mid, post ++ [g], h, k,
          by simp [he, List.append_assoc], hr, hs⟩)

lemma fix_agree {n : ℕ} (p : Fin n) (x : Fin n → Bool) (w : ℕ) (hw : w ≠ p.val) :
    (List.ofFn (fix p false x)).getD w false =
      (List.ofFn (fix p true x)).getD w false := by
  by_cases hi : w < n
  · let i : Fin n := ⟨w, hi⟩
    have hn : i ≠ p := fun h => hw (congrArg Fin.val h)
    change (List.ofFn (fix p false x)).getD i.val false =
      (List.ofFn (fix p true x)).getD i.val false
    simp [fix, hn]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

def Nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

def Essential {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) : Prop :=
  ∃ x, f (fix p false x) ≠ f (fix p true x)

lemma trace_of_essential {n : ℕ} (C : Circuit) (p : Fin n)
    (he : Essential (circuitFun n C) p)
    (hnc : Nonconstant (fun x => circuitFun n C (fix p false x))) :
    Direct n p.val C.output C.gates ∨ Chain n p.val C.gates := by
  obtain ⟨x, hx⟩ := he
  rcases wire_trace (n := n) (x := List.ofFn (fix p false x)) (y := List.ofFn (fix p true x))
      (by simp) (by simp) (fix_agree p x) C.gates C.output hx with hp | h
  · exfalso
    obtain ⟨v, w, hne⟩ := hnc
    apply hne
    have heval (z : Fin n → Bool) : circuitFun n C (fix p false z) = false := by
      change (wiresFrom C.gates (List.ofFn (fix p false z))).getD C.output false = false
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn (fix p false z))
      rw [hp, ht, List.getD_append _ _ _ _ (by simp)]
      simp [fix]
    change circuitFun n C (fix p false v) = circuitFun n C (fix p false w)
    rw [heval v, heval w]
  · exact h

lemma direct_const {n : ℕ} (p : Fin n) (pre post : List Gate) (g : Gate)
    (hm : ∀ h ∈ pre ++ g :: post, Good h) (hp : p.val ∈ g.inputs) (x : Fin n → Bool) :
    circuitFun n ⟨pre ++ g :: post, n + pre.length⟩ (fix p (absorb g.op) x) = absorb g.op := by
  let s := elim n pre (initial p (absorb g.op))
  let t := elimStep n s g
  have hg : Good g := hm g (by simp)
  have hs : stat s p.val = Sum.inl (absorb g.op) :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p _)
  have hc := absorb_at_reader n s g hg hp hs
  obtain ⟨suffix, hext, hlen⟩ := elim_extends n pre (initial p (absorb g.op))
  have hl : s.1.length = n + pre.length := by
    change (elim n pre (initial p (absorb g.op))).1.length = _
    rw [hext, List.length_append, initial_length, hlen]
  have ht : stat t (n + pre.length) = Sum.inl (absorb g.op) := by
    change (s.1 ++ [(plan n s g).2]).getD (n + pre.length) _ = _
    rw [getD_snoc_len _ _ _ _ hl, hc]
  have hlt : n + pre.length < t.1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [hl]
  have hstat : stat (elim n (pre ++ g :: post) (initial p (absorb g.op))) (n + pre.length) =
      Sum.inl (absorb g.op) := by
    rw [elim_append]
    exact (elim_stat n post t _ hlt).trans ht
  have hval := ((inv_elim n _ (by simp) _ _ _ hm (initial_inv p (absorb g.op) x)).2
    (n + pre.length)).2
  change (stat (elim n (pre ++ g :: post) (initial p (absorb g.op))) (n + pre.length)).val _ = _ at hval
  rw [hstat] at hval
  exact hval.symm

lemma leaf_step {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p : Fin n)
    (he : Essential (circuitFun n C) p)
    (hnc : ∀ b, Nonconstant (fun x => circuitFun n C (fix p b x))) :
    ∃ (b : Bool) (D : Circuit), Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧ D.size + 2 ≤ C.size := by
  rcases trace_of_essential C p he (hnc false) with hd | ⟨pre, mid, post, g, h, hgs, hp, hr⟩
  · rcases C with ⟨gs, out⟩
    obtain ⟨pre, post, g, rfl, hp, rfl⟩ := hd
    obtain ⟨x, y, hxy⟩ := hnc (absorb g.op)
    exact False.elim (hxy ((direct_const p pre post g hm hp x).trans
      (direct_const p pre post g hm hp y).symm))
  · obtain ⟨D, hD, hval, hsz⟩ := restriction C hm p (absorb g.op) (hnc _)
    refine ⟨absorb g.op, D, hD, hval, ?_⟩
    have hg : Good g := hm g (by simp [hgs])
    have hh : Good h := hm h (by simp [hgs])
    rw [hsz, Circuit.size, hgs]
    exact double_drop p pre mid post g h hg hh hp hr

lemma center_step {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p : Fin n)
    (hnc : Nonconstant (fun x => circuitFun n C (fix p false x))) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p false x)) ∧
      D.size ≤ C.size ∧ (Essential (circuitFun n C) p → D.size + 1 ≤ C.size) := by
  obtain ⟨D, hD, hval, hsz⟩ := restriction C hm p false hnc
  refine ⟨D, hD, hval, ?_, ?_⟩
  · rw [hsz, Circuit.size]
    simpa [initial] using elim_len n C.gates (initial p false)
  · intro he
    rw [hsz, Circuit.size]
    have hr : ∃ pre post g, C.gates = pre ++ g :: post ∧ p.val ∈ g.inputs := by
      rcases trace_of_essential C p he hnc with ⟨pre, post, g, hh, hg, _⟩ |
        ⟨pre, mid, post, g, h, hh, hg, _⟩
      · exact ⟨pre, post, g, hh, hg⟩
      · exact ⟨pre, mid ++ h :: post, g, hh, hg⟩
    obtain ⟨pre, post, g, hh, hg⟩ := hr
    have hg' := hm g (by simp [hh])
    rw [hh]
    exact single_drop p false pre post g hg' hg

abbrev left {a b : ℕ} (e : Fin a × Fin b) : Fin (a + b) := Fin.castAdd b e.1

abbrev right {a b : ℕ} (e : Fin a × Fin b) : Fin (a + b) := Fin.natAdd a e.2

abbrev incident {a b : ℕ} (i : Fin (a + b)) (e : Fin a × Fin b) : Prop :=
  left e = i ∨ right e = i

def edgeFun {a b : ℕ} (E : Finset (Fin a × Fin b)) (x : Fin (a + b) → Bool) : Bool :=
  decide (∃ e ∈ E, x (left e) = true ∧ x (right e) = true)

lemma edge_true {a b : ℕ} {E : Finset (Fin a × Fin b)} {x : Fin (a + b) → Bool} :
    edgeFun E x = true ↔ ∃ e ∈ E, x (left e) = true ∧ x (right e) = true := by
  simp [edgeFun]

lemma endpoints_ne {a b : ℕ} (e : Fin a × Fin b) : left e ≠ right e := by
  intro h
  have hv := congrArg Fin.val h
  change e.1.val = a + e.2.val at hv
  omega

lemma both_endpoints {a b : ℕ} {e : Fin a × Fin b} {p q : Fin (a + b)}
    (hn : p ≠ q) (hp : incident p e) (hq : incident q e) :
    (left e = p ∧ right e = q) ∨ (left e = q ∧ right e = p) := by
  rcases hp with hl | hr <;> rcases hq with hl' | hr'
  · exact (hn (hl.symm.trans hl')).elim
  · exact Or.inl ⟨hl, hr'⟩
  · exact Or.inr ⟨hl', hr⟩
  · exact (hn (hr.symm.trans hr')).elim

lemma single_support_false {a b : ℕ} (E : Finset (Fin a × Fin b))
    (x : Fin (a + b) → Bool) (r : Fin (a + b))
    (h : ∀ i, x i = true → i = r) : edgeFun E x = false := by
  cases he : edgeFun E x with
  | false => rfl
  | true =>
    obtain ⟨e, _, hl, hr⟩ := edge_true.mp he
    exact (endpoints_ne e ((h _ hl).trans (h _ hr).symm)).elim

def one {n : ℕ} (r i : Fin n) : Bool := decide (i = r)

lemma one_false {a b : ℕ} (E : Finset (Fin a × Fin b)) (r : Fin (a + b)) :
    edgeFun E (one r) = false := by
  apply single_support_false E _ r
  simp [one]

lemma pair_true {a b : ℕ} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    {p q : Fin (a + b)} (he : e ∈ E) (hn : p ≠ q)
    (hp : incident p e) (hq : incident q e) :
    edgeFun E (fix p true (one q)) = true := by
  apply edge_true.mpr
  refine ⟨e, he, ?_⟩
  rcases both_endpoints hn hp hq with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr, fix, one, hn.symm]

lemma fix_one_false {n : ℕ} {p q : Fin n} (h : p ≠ q) :
    fix p false (one q) = one q := by
  funext i
  by_cases hi : i = p <;> simp [fix, one, hi, h]

lemma graph_nonconstant {a b : ℕ} {E : Finset (Fin a × Fin b)}
    (h : E.Nonempty) (p : Fin (a + b)) : Nonconstant (edgeFun E) := by
  obtain ⟨e, he⟩ := h
  refine ⟨one p, fun _ => true, ?_⟩
  rw [one_false, edge_true.mpr ⟨e, he, rfl, rfl⟩]
  decide

lemma delete_center {a b : ℕ} (E : Finset (Fin a × Fin b))
    (p q : Fin (a + b)) (hpq : ∀ e ∈ E, incident p e → incident q e)
    (hn : p ≠ q) (bval : Bool) (x : Fin (a + b) → Bool) :
    edgeFun E (fix p bval (fix q false x)) = edgeFun (E.filter fun e => ¬incident q e) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [edge_true, Finset.mem_filter]
  constructor
  · rintro ⟨e, he, hl, hr⟩
    have hq : ¬incident q e := by
      rintro (hq | hq)
      · simp [fix, hq, hn.symm] at hl
      · simp [fix, hq, hn.symm] at hr
    have hp : ¬incident p e := fun h => hq (hpq e he h)
    simp only [incident, not_or] at hq hp
    exact ⟨e, ⟨he, not_or.mpr hq⟩, by simpa [fix, hp.1, hq.1] using hl,
      by simpa [fix, hp.2, hq.2] using hr⟩
  · rintro ⟨e, ⟨he, hq⟩, hl, hr⟩
    have hp : ¬incident p e := fun h => hq (hpq e he h)
    simp only [incident, not_or] at hq hp
    exact ⟨e, he, by simpa [fix, hp.1, hq.1] using hl,
      by simpa [fix, hp.2, hq.2] using hr⟩

lemma center_essential {a b : ℕ} (E : Finset (Fin a × Fin b))
    (p q : Fin (a + b)) (hn : p ≠ q) (e : Fin a × Fin b) (he : e ∈ E)
    (hp : incident p e) (hq : incident q e)
    (huniq : ∀ e' ∈ E, incident p e' → e' = e)
    (hdeg : 2 ≤ (E.filter (incident q)).card) (bval : Bool) :
    Essential (fun x => edgeFun E (fix p bval x)) q := by
  cases bval
  · let S := E.filter (incident q)
    change 2 ≤ S.card at hdeg
    have hmore : ∃ d ∈ S, d ≠ e := by
      by_contra! h
      have hsub : S ⊆ {e} := by
        intro d hd
        simpa using h d hd
      have hlt := Finset.card_le_card hsub
      simp at hlt
      omega
    obtain ⟨d, hd, hde⟩ := hmore
    have hd' := Finset.mem_filter.mp hd
    have hnp : ¬incident p d := fun h => hde (huniq d hd'.1 h)
    obtain ⟨r, hqr, hpr, hor⟩ : ∃ r, q ≠ r ∧ p ≠ r ∧ incident r d := by
      rcases hd'.2 with hl | hr
      · refine ⟨right d, ?_, ?_, Or.inr rfl⟩
        · intro h
          exact endpoints_ne d (hl.trans h)
        · exact fun h => hnp (Or.inr h.symm)
      · refine ⟨left d, ?_, ?_, Or.inl rfl⟩
        · intro h
          exact endpoints_ne d (hr.trans h).symm
        · exact fun h => hnp (Or.inl h.symm)
    refine ⟨one r, ?_⟩
    change edgeFun E (fix p false (fix q false (one r))) ≠
      edgeFun E (fix p false (fix q true (one r)))
    have hyes : edgeFun E (fix p false (fix q true (one r))) = true := by
      apply edge_true.mpr
      refine ⟨d, hd'.1, ?_⟩
      rcases both_endpoints hqr hd'.2 hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [fix, h1, h2, one, hqr.symm, hn.symm, hpr.symm]
      · simp [fix, h1, h2, one, hqr.symm, hn.symm, hpr.symm]
    rw [fix_one_false hqr, fix_one_false hpr, one_false, hyes]
    decide
  · refine ⟨fun _ => false, ?_⟩
    change edgeFun E (fix p true (fix q false (fun _ => false))) ≠
      edgeFun E (fix p true (fix q true (fun _ => false)))
    have hz : fix q false (fun _ => false) = (fun _ => false) := by
      funext i
      simp [fix]
    have hsingle : fix p true (fun _ => false) = one p := by
      funext i
      by_cases h : i = p <;> simp [fix, one, h]
    have hother : fix q true (fun _ => false) = one q := by
      funext i
      by_cases h : i = q <;> simp [fix, one, h]
    rw [hz, hsingle, hother, one_false, pair_true he hn hp hq]
    decide

lemma solve {a b : ℕ} (E : Finset (Fin a × Fin b)) (C : Circuit) (hm : Monotone2 C)
    (hc : circuitFun (a + b) C = edgeFun E) (p q : Fin (a + b)) (hn : p ≠ q)
    (hcard : (E.filter (incident p)).card = 1)
    (hedge : ∃ e ∈ E, incident p e ∧ incident q e)
    (hne : (E.filter fun e => ¬incident q e).Nonempty) :
    ∃ D : Circuit, Monotone2 D ∧
      circuitFun (a + b) D = edgeFun (E.filter fun e => ¬incident q e) ∧
      D.size + min 3 ((E.filter (incident q)).card + 1) ≤ C.size := by
  classical
  obtain ⟨e, he, hp, hq⟩ := hedge
  have huniq (d) (hd : d ∈ E) (hi : incident p d) : d = e := by
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hcard
    have hmem (u) (hu : u ∈ E) (hui : incident p u) : u = s := by
      have hh : u ∈ E.filter (incident p) := Finset.mem_filter.mpr ⟨hu, hui⟩
      simpa [hs] using hh
    exact (hmem d hd hi).trans (hmem e he hp).symm
  have hdel (bval : Bool) (x : Fin (a + b) → Bool) :
      circuitFun (a + b) C (fix p bval (fix q false x)) = edgeFun (E.filter fun e => ¬incident q e) x := by
    rw [hc]
    apply delete_center E p q _ hn
    intro d hd hi
    rwa [huniq d hd hi]
  obtain ⟨x, y, hxy⟩ := graph_nonconstant hne p
  have hnc (bval : Bool) : Nonconstant (fun z => circuitFun (a + b) C (fix p bval z)) := by
    refine ⟨fix q false x, fix q false y, ?_⟩
    simpa only [hdel] using hxy
  have he' : Essential (circuitFun (a + b) C) p := by
    rw [hc]
    exact ⟨one q, by rw [fix_one_false hn, one_false, pair_true he hn hp hq]; decide⟩
  obtain ⟨bval, C', hm', hc', hs'⟩ := leaf_step C hm p he' hnc
  have hn' : Nonconstant (fun z => circuitFun (a + b) C' (fix q false z)) := by
    refine ⟨x, y, ?_⟩
    simpa only [hc', hdel] using hxy
  obtain ⟨D, hmD, hcD, hsD, hsMore⟩ := center_step C' hm' q hn'
  refine ⟨D, hmD, funext fun z => (hcD z).trans ((hc' _).trans (hdel bval z)), ?_⟩
  by_cases hd : 2 ≤ (E.filter (incident q)).card
  · have heq : Essential (circuitFun (a + b) C') q := by
      obtain ⟨z, hz⟩ := center_essential E p q hn e he hp hq huniq hd bval
      exact ⟨z, by simpa only [hc', hc] using hz⟩
    have hh := hsMore heq
    rw [min_eq_left (by omega)]
    omega
  · have hh : min 3 ((E.filter (incident q)).card + 1) ≤ 2 :=
      (min_le_right _ _).trans (by omega)
    omega

end PEqualNP.Outside.L_meta_7961

theorem PEqualNP.Outside.L_meta_7961 :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → (Fin (x1 + x2) → Bool) → Bool := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ x8 ∈ x6, x7 (Fin.castAdd x2 x8.1) = Bool.true ∧ x7 (Fin.natAdd x1 x8.2) = Bool.true);   PEqualNP.MetaComplexity.Monotone2 x4 →     PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = x6 x3 →       ∀ (x9 x10 : Fin (x1 + x2)),         x9 ≠ x10 →           (Finset.filter (x5 x9) x3).card = (1 : ℕ) →             (∃ x13 ∈ x3, x5 x9 x13 ∧ x5 x10 x13) →               have x14 : Finset (Fin x1 × Fin x2) := {x14 ∈ x3 | ¬x5 x10 x14};               x14.Nonempty → ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x16 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 = x6 x14 ∧ x16.size + Min.min (3 : ℕ) ((Finset.filter (x5 x10) x3).card + (1 : ℕ)) ≤ x4.size := by
  intro a b E C
  dsimp only
  intro hm hc p q hn hcard he hne
  exact PEqualNP.Outside.L_meta_7961.solve E C hm hc p q hn hcard he hne
