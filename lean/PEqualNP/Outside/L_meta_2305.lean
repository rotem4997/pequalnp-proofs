import Mathlib
import PEqualNP.Defs

-- Constant propagation adapted from stierms, L-meta-517 (PR #553).
namespace PEqualNP.Outside.L_meta_2305
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

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
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

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
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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


def ConstAt (a : List Stat × List Gate) (k : ℕ) (c : Bool) : Prop :=
  k < a.1.length ∧ a.1.getD k (Sum.inl false) = Sum.inl c

def Good (a : List Stat × List Gate) : Prop := ConstAt a 0 false ∧ ConstAt a 9 true

def reads (g : Gate) : Bool := [0, 9].any fun k => g.inputs.contains k

def count (gs : List Gate) : ℕ := (gs.filter reads).length

theorem const_step (n : ℕ) (a : List Stat × List Gate) (g : Gate) (k : ℕ) (c : Bool)
    (h : ConstAt a k c) : ConstAt (elimStep n a g) k c := by
  have hk := h.1
  refine ⟨by simp [elimStep]; omega, ?_⟩
  change (a.1 ++ [_]).getD k (Sum.inl false) = _
  rw [getD_snoc_ne _ _ _ _ (by omega)]
  exact h.2

theorem good_step (n : ℕ) (a : List Stat × List Gate) (g : Gate) (h : Good a) :
    Good (elimStep n a g) := ⟨const_step n a g 0 false h.1, const_step n a g 9 true h.2⟩

theorem elim_good (n : ℕ) (gs : List Gate) : ∀ a, Good a → Good (elim n gs a) := by
  induction gs with
  | nil => intro a h; exact h
  | cons g gs ih => intro a h; exact ih _ (good_step n a g h)

theorem elim_const (n : ℕ) (gs : List Gate) (k : ℕ) (c : Bool) :
    ∀ a, ConstAt a k c → ConstAt (elim n gs a) k c := by
  induction gs with
  | nil => intro a h; exact h
  | cons g gs ih => intro a h; exact ih _ (const_step n a g k c h)

theorem elim_status_length (n : ℕ) (gs : List Gate) : ∀ a,
    (elim n gs a).1.length = a.1.length + gs.length := by
  induction gs with
  | nil => intro a; simp [elim]
  | cons g gs ih => intro a; change (elim n gs (elimStep n a g)).1.length = _; rw [ih]; simp [elimStep]; omega

theorem none_of_const (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : ConstAt a k c) (hk : k ∈ g.inputs) :
    (simplify g.op (n + a.2.length) (g.inputs.map fun i => a.1.getD i (Sum.inl false))).1 = none := by
  apply simplify_count _ _ _ hg.1.1
  · simpa using hg.1.2
  · intro h; simpa using hg.2 h
  · exact ⟨c, List.mem_map.mpr ⟨k, hk, hc.2⟩⟩

theorem step_len_le (n : ℕ) (a : List Stat × List Gate) (g : Gate) :
    (elimStep n a g).2.length ≤ a.2.length + 1 := by
  simp only [elimStep, List.length_append]
  exact Nat.add_le_add_left (toList_length_le _) _

theorem step_len_const (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : ConstAt a k c) (hk : k ∈ g.inputs) :
    (elimStep n a g).2.length = a.2.length := by
  simp only [elimStep, none_of_const n a g hg k c hc hk]
  simp

theorem step_len_read (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (ha : Good a) (hr : reads g = true) : (elimStep n a g).2.length = a.2.length := by
  have hr' : 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by simpa [reads] using hr
  rcases hr' with h | h
  · exact step_len_const n a g hg 0 false ha.1 h
  · exact step_len_const n a g hg 9 true ha.2 h

theorem elim_count (n : ℕ) (gs : List Gate) : ∀ a, Good a → (∀ g ∈ gs, NOk g) →
    (elim n gs a).2.length + count gs ≤ a.2.length + gs.length := by
  induction gs with
  | nil => intro a _ _; simp [elim, count]
  | cons g gs ih =>
    intro a ha hg
    have h := ih (elimStep n a g) (good_step n a g ha) (fun g' h => hg g' (by simp [h]))
    change (elim n gs (elimStep n a g)).2.length + count (g :: gs) ≤ _
    cases hr : reads g
    · have hstep := step_len_le n a g
      simp [count, hr] at h ⊢
      omega
    · have hstep := step_len_read n a g (hg g (by simp)) ha hr
      simp [count, hr] at h ⊢
      omega

theorem elim_extra (n : ℕ) (gs : List Gate) (k : ℕ) (c : Bool) :
    ∀ a, Good a → ConstAt a k c → (∀ g ∈ gs, NOk g) →
    (∃ g ∈ gs, reads g = false ∧ k ∈ g.inputs) →
    (elim n gs a).2.length + count gs + 1 ≤ a.2.length + gs.length := by
  induction gs with
  | nil => intro a ha hc hg hex; simpa using hex
  | cons g gs ih =>
    intro a ha hc hg hex
    change (elim n gs (elimStep n a g)).2.length + count (g :: gs) + 1 ≤ _
    by_cases he : reads g = false ∧ k ∈ g.inputs
    · have h := elim_count n gs (elimStep n a g) (good_step n a g ha)
        (fun g' h => hg g' (by simp [h]))
      have hstep := step_len_const n a g (hg g (by simp)) k c hc he.2
      simp [count, he.1] at h ⊢
      omega
    · have hex' : ∃ g' ∈ gs, reads g' = false ∧ k ∈ g'.inputs := by
        obtain ⟨g', hmem, hcond⟩ := hex
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact (he hcond).elim
        · exact ⟨g', hmem, hcond⟩
      have h := ih (elimStep n a g) (good_step n a g ha) (const_step n a g k c hc)
        (fun g' h => hg g' (by simp [h])) hex'
      cases hr : reads g
      · have hstep := step_len_le n a g
        simp [count, hr] at h ⊢
        omega
      · have hstep := step_len_read n a g (hg g (by simp)) ha hr
        simp [count, hr] at h ⊢
        omega

theorem force_and (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2) (hc : Sum.inl false ∈ ins) :
    (simplify GateOp.and m ins).2 = Sum.inl false := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify, simpAnd] <;> aesop

theorem force_or (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2) (hc : Sum.inl true ∈ ins) :
    (simplify GateOp.or m ins).2 = Sum.inl true := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify, simpOr]

theorem force_step (n : ℕ) (a : List Stat × List Gate) (g : Gate) (ha : Good a) (hg : NOk g)
    (hf : (g.op = GateOp.and ∧ 0 ∈ g.inputs) ∨ (g.op = GateOp.or ∧ 9 ∈ g.inputs)) :
    ∃ c, ConstAt (elimStep n a g) a.1.length c := by
  rcases hf with ⟨hop, hk⟩ | ⟨hop, hk⟩
  · refine ⟨false, by simp [elimStep], ?_⟩
    change (a.1 ++ [_]).getD a.1.length (Sum.inl false) = _
    rw [getD_snoc_eq, hop]
    exact force_and _ _ (by simpa using hg.1.2) (List.mem_map.mpr ⟨0, hk, ha.1.2⟩)
  · refine ⟨true, by simp [elimStep], ?_⟩
    change (a.1 ++ [_]).getD a.1.length (Sum.inl false) = _
    rw [getD_snoc_eq, hop]
    exact force_or _ _ (by simpa using hg.1.2) (List.mem_map.mpr ⟨9, hk, ha.2.2⟩)

def initial : List Stat × List Gate :=
  ([Sum.inl false] ++ List.ofFn (fun i : Fin 8 => (Sum.inr i.val : Stat)) ++ [Sum.inl true], [])

theorem initial_good : Good initial := by simp [Good, ConstAt, initial, List.ofFn_succ]

theorem init_inv (y : Fin 8 → Bool) :
    Inv 8 (List.ofFn y) (false :: List.ofFn y ++ [true]) initial := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases h : i < 10
  · interval_cases i <;> simp [initial, List.ofFn_succ, wiresFrom, Stat.Valid, Stat.val]
  · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem elimination_bound (gs : List Gate) (hg : ∀ g ∈ gs, NOk g)
    (hc : 3 ≤ count gs ∨ 2 ≤ count gs ∧
      ∃ p g t, gs = p ++ g :: t ∧
        ((g.op = GateOp.and ∧ 0 ∈ g.inputs) ∨ (g.op = GateOp.or ∧ 9 ∈ g.inputs)) ∧
        ∃ h ∈ t, reads h = false ∧ 10 + p.length ∈ h.inputs) :
    (elim 8 gs initial).2.length + 3 ≤ gs.length := by
  rcases hc with hc | ⟨hc, p, g, t, rfl, hf, hex⟩
  · have h := elim_count 8 gs initial initial_good hg
    have hz : initial.2.length = 0 := rfl
    omega
  · let a := elim 8 p initial
    have ha := elim_good 8 p initial initial_good
    have hgp : ∀ h ∈ p, NOk h := fun h hm => hg h (by simp [hm])
    have hgt : ∀ h ∈ t, NOk h := fun h hm => hg h (by simp [hm])
    have hgg := hg g (by simp)
    have hp := elim_count 8 p initial initial_good hgp
    have hl : a.1.length = 10 + p.length := by simp [a, elim_status_length, initial]
    obtain ⟨c, hconst⟩ := force_step 8 a g ha hgg hf
    have ht := elim_extra 8 t (10 + p.length) c (elimStep 8 a g)
      (good_step 8 a g ha) (hl ▸ hconst) hgt hex
    have hr : reads g = true := by
      rcases hf with ⟨_, hm⟩ | ⟨_, hm⟩ <;> simp [reads, hm]
    have hs := step_len_read 8 a g hgg ha hr
    have he : elim 8 (p ++ g :: t) initial = elim 8 t (elimStep 8 a g) := by
      simp [elim, List.foldl_append, a]
    rw [he]
    have hn : count (p ++ g :: t) = count p + count t + 1 := by simp [count, hr]; omega
    have hz : initial.2.length = 0 := rfl
    simp only [List.length_append, List.length_cons] at hc ⊢
    change a.2.length + count p ≤ initial.2.length + p.length at hp
    omega

theorem normalized_eq (g : Gate) (h : Ok g) :
    (Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)) = normGate g := by
  obtain ⟨op, ins⟩ := g
  rcases h.1 with h | h | h <;> simp only at h <;> subst op <;>
    simp [normGate, GateOp.eval]

end PEqualNP.Outside.L_meta_2305

open PEqualNP.Outside.L_meta_2305 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2305 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ) := by
  intro C
  dsimp only
  intro hC hfirst hsize hcount hnc
  have hnorm : List.map (fun g : Gate =>
      (Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)))
      (C.gates.drop 1) = (C.gates.drop 1).map normGate := by
    apply List.map_congr_left
    intro g hg
    exact normalized_eq g (hC g (List.mem_of_mem_drop hg))
  rw [hnorm] at hcount
  have hne : C.gates ≠ [] := by
    intro he
    have h := hfirst (fun _ => false)
    simp [Circuit.wires, he, List.getD_eq_default] at h
  obtain ⟨g, gs, hgs⟩ := List.exists_cons_of_ne_nil hne
  let ns := gs.map normGate
  have hnok : ∀ h ∈ ns, NOk h := by
    intro h hh
    obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
    exact normGate_nok h0 (hC h0 (by rw [hgs]; simp [hh0]))
  have hbound : (elim 8 ns initial).2.length + 3 ≤ gs.length := by
    have h := elimination_bound ns hnok
    have hcount' : 3 ≤ count ns ∨ 2 ≤ count ns ∧
        ∃ p g t, ns = p ++ g :: t ∧
          ((g.op = GateOp.and ∧ 0 ∈ g.inputs) ∨ (g.op = GateOp.or ∧ 9 ∈ g.inputs)) ∧
          ∃ h ∈ t, reads h = false ∧ 10 + p.length ∈ h.inputs := by
      simp only [hgs, List.drop_succ_cons, List.drop_zero] at hcount
      exact hcount
    simpa [ns] using h hcount'
  have hprefix (y : Fin 8 → Bool) :
      g.op.eval (g.inputs.map fun i => (false :: List.ofFn y).getD i false) = true := by
    have h := hfirst (Fin.cons false y)
    have hof : List.ofFn (Fin.cons false y : Fin 9 → Bool) = false :: List.ofFn y := by
      simp [List.ofFn_succ]
    rw [hof, wires_eq, hgs] at h
    change (wiresFrom gs ((false :: List.ofFn y) ++
      [g.op.eval (g.inputs.map fun i => (false :: List.ofFn y).getD i false)])).getD 9 false = _ at h
    rw [getD_wiresFrom gs _ 9 (by simp), getD_snoc_len _ _ _ 9 (by simp)] at h
    simpa using h
  have heval (y : Fin 8 → Bool) :
      (wiresFrom ns (false :: List.ofFn y ++ [true])).getD C.output false =
        circuitFun 9 C (Fin.cons false y) := by
    have hof : List.ofFn (Fin.cons false y : Fin 9 → Bool) = false :: List.ofFn y := by
      simp [List.ofFn_succ]
    unfold circuitFun Circuit.eval
    rw [hof, wires_eq, hgs]
    change (wiresFrom ns (false :: List.ofFn y ++ [true])).getD C.output false =
      (wiresFrom gs ((false :: List.ofFn y) ++
        [g.op.eval (g.inputs.map fun i => (false :: List.ofFn y).getD i false)])).getD C.output false
    rw [hprefix, show ns = gs.map normGate from rfl, wiresFrom_norm]
  let a := elim 8 ns initial
  have hi (y : Fin 8 → Bool) := inv_elim 8 (List.ofFn y) (by simp) ns
    (false :: List.ofFn y ++ [true]) initial (fun g hg => (hnok g hg).1) (init_inv y)
  have hv (y : Fin 8 → Bool) :
      (a.1.getD C.output (Sum.inl false)).val (wiresFrom a.2 (List.ofFn y)) =
        circuitFun 9 C (Fin.cons false y) :=
    ((hi y).2 C.output).2.trans (heval y)
  cases hs : a.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y, z, hyz⟩ := hnc
    apply False.elim
    apply hyz
    rw [← hv y, ← hv z, hs]
    rfl
  | inr j =>
    refine ⟨⟨a.2, j⟩, elim_ok 8 ns initial (by simp [initial]), ?_, ?_⟩
    · change a.2.length ≤ 11
      have hc : C.size = gs.length + 1 := by simp [Circuit.size, hgs]
      change a.2.length + 3 ≤ gs.length at hbound
      omega
    · intro y
      have h := hv y
      rw [hs] at h
      exact h
