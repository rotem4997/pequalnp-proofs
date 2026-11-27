import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10568_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

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

-- Each old wire is either constant or represented by a wire in the smaller circuit.
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
      simp [simpAnd] at hg
    all_goals (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    all_goals (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    all_goals (subst hg; simp [Ok])
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
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
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

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

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

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩


def ncount (gs : List Gate) := opCount isNotGate gs

lemma flag_iff (g : Gate) : isNotGate g.op = true ↔ g.op = .not := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNotGate]

lemma norm_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

lemma norm_count (p : GateOp → Bool) (gs : List Gate) :
    opCount p (gs.map normGate) = opCount p gs := by
  unfold opCount
  rw [List.countP_map]
  exact List.countP_congr fun g _ => by simp [norm_op]

lemma count_le_one (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    ncount gs ≤ 1 := by
  unfold ncount opCount
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j :=
      fun i j hi hj => Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun a => isNotGate a.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha h
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
        have eqn := single (0 : Fin (g::gs).length) i.succ hg (hi ▸ (flag_iff a).mp h)
        exact Fin.succ_ne_zero i eqn.symm
      simp [z, (flag_iff g).mpr hg]
    · have flag : isNotGate g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((flag_iff g).mp h))
      simpa [List.countP_cons,flag] using ih rest

lemma neg_unique {gs : List Gate} (one : ncount gs ≤ 1)
    {g h : Gate} (gm : g ∈ gs) (hm : h ∈ gs) (gn : g.op = .not) (hn : h.op = .not) :
    g = h := by
  let ns := gs.filter fun a => isNotGate a.op
  have len : ns.length ≤ 1 := by simpa [ns,ncount,opCount, List.countP_eq_length_filter] using one
  have x : g ∈ ns := List.mem_filter.mpr ⟨gm,(flag_iff g).mpr gn⟩
  have y : h ∈ ns := List.mem_filter.mpr ⟨hm,(flag_iff h).mpr hn⟩
  cases e : ns with
  | nil => simp [e] at x
  | cons a t =>
    have et : t = [] := List.eq_nil_of_length_eq_zero (by rw [e, List.length_cons] at len; omega)
    simpa [e, et] using (show g = a from by simpa [e,et] using x).trans
      (show h = a from by simpa [e,et] using y).symm

lemma gate_inputs_preserve (v : ℕ) (gs : List Gate)
    (shape : ∀ g ∈ gs, (g.op = .not ∧ g.inputs = [v]) ∨
      ((g.op = .and ∨ g.op = .or) ∧ v ∉ g.inputs)) :
    ∀ (lo hi : List Bool), lo.length = hi.length → v < lo.length →
      hi.getD v false = true →
      (∀ i, i ≠ v → hi.getD i false = true → lo.getD i false = true) →
      ∀ i, i ≠ v → (wiresFrom gs hi).getD i false = true → (wiresFrom gs lo).getD i false = true := by
  induction gs with
  | nil => intro lo hi _ _ _ close; exact close
  | cons g gs ih =>
    intro lo hi hl vh bit close
    let step (w : List Bool) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have low : v < hi.length := by omega
    have next : g.op.eval (g.inputs.map fun i => hi.getD i false) = true →
        g.op.eval (g.inputs.map fun i => lo.getD i false) = true := by
      rcases shape g List.mem_cons_self with ⟨op,pins⟩ | ⟨op,pins⟩
      · intro h
        rw [op, pins] at h
        change (!hi.getD v false) = true at h
        rw [bit] at h
        cases h
      · exact gateOp_mono g.op op g.inputs _ _ fun i hm => close i (fun eq => pins (eq ▸ hm))
    apply ih (fun a ha => shape a (List.mem_cons_of_mem _ ha)) (step lo) (step hi)
      (by simp [step,hl]) (by simp [step]; omega)
      (by simpa only [step, List.getD_append _ _ _ _ low] using bit)
    intro i ne
    by_cases endpos : i = hi.length
    · unfold step
      rw [endpos, getD_snoc_eq, ← hl, getD_snoc_eq]
      exact next
    · simp only [step, getD_snoc_ne _ _ _ _ endpos, getD_snoc_ne _ _ _ _ (show i ≠ lo.length by omega)]
      exact close i ne

lemma elim_count_drop (p : GateOp → Bool) (n v : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ gs, NOk g) →
    v < acc.1.length → (∃ b, acc.1.getD v (Sum.inl false) = Sum.inl b) →
    (∃ g ∈ gs, p g.op = true ∧ v ∈ g.inputs) →
      opCount p (elim n gs acc).2 + 1 ≤ opCount p acc.2 + opCount p gs := by
  induction gs with
  | nil => intro acc _ _ _ r; simp at r
  | cons g gs ih =>
    intro acc ok hv constant read
    change opCount p (elim n gs (elimStep n acc g)).2 + 1 ≤ _
    have ot : ∀ h ∈ gs, NOk h := fun h hm => ok h (List.mem_cons_of_mem _ hm)
    let values := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    have stepCost : opCount p (elimStep n acc g).2 ≤ opCount p acc.2 + (if p g.op then 1 else 0) := by
      simpa only [elimStep, opCount_append, Nat.add_le_add_iff_left] using
        Nat.add_le_add_left (simplify_opCount_le p g.op (n+acc.2.length) values) (opCount p acc.2)
    by_cases chosen : p g.op = true ∧ v ∈ g.inputs
    · obtain ⟨b, hb⟩ := constant
      have empty : (simplify g.op (n+acc.2.length) values).1 = none := by
        have fits := ok g List.mem_cons_self
        apply simplify_count _ _ _ fits.1.1
        · simpa [values] using fits.1.2
        · intro h; simpa [values] using fits.2 h
        · exact ⟨b, List.mem_map.mpr ⟨v, chosen.2, hb⟩⟩
      have same : (elimStep n acc g).2 = acc.2 := by
        change acc.2 ++ (simplify g.op (n+acc.2.length) values).1.toList = _
        simp [empty]
      have h := elim_opCount_le p n gs (elimStep n acc g)
      rw [same] at h
      rw [opCount_cons, chosen.1, if_pos rfl]
      omega
    · have inTail : ∃ h ∈ gs, p h.op = true ∧ v ∈ h.inputs := by
        obtain ⟨h, hm, hp⟩ := read
        rcases List.mem_cons.mp hm with rfl | ht
        · exact (chosen hp).elim
        · exact ⟨_, ht, hp⟩
      have h := ih (elimStep n acc g) ot (by simp [elimStep]; omega) (by
        obtain ⟨b, hb⟩ := constant
        refine ⟨b, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hb) inTail
      rw [opCount_cons]
      omega

def pin {n m : ℕ} (v : Fin n) (rename : Fin n → Fin m) (b : Bool)
    (y : Fin m → Bool) (i : Fin n) := if i = v then b else y (rename i)

lemma ofFnAt {n : ℕ} {α : Type} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem projectBinary {n m : ℕ} (v : Fin n) (rename : Fin n → Fin m) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (one : ncount C.gates ≤ 1)
    (depends : ∃ y : Fin m → Bool, C.eval (List.ofFn (pin v rename false y)) = false ∧
      C.eval (List.ofFn (pin v rename true y)) = true)
    (nonconstant : ∃ y z : Fin m → Bool,
      C.eval (List.ofFn (pin v rename false y)) ≠ C.eval (List.ofFn (pin v rename false z))) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ ncount D.gates ≤ ncount C.gates ∧
      nonNotCount D.gates + 1 ≤ nonNotCount C.gates ∧ ∀ y : Fin m → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn (pin v rename false y)) := by
  let gs := C.gates.map normGate
  have nn : ncount gs = ncount C.gates := norm_count _ _
  have bn : nonNotCount gs = nonNotCount C.gates :=
    norm_count (fun op => !isNotGate op) C.gates
  have ok : ∀ g ∈ gs, NOk g := by
    intro g h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact normGate_nok _ (legal _ ha)
  have eval (x : List Bool) : (wiresFrom gs x).getD C.output false = C.eval x := by
    rw [show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  have output : C.output ≠ v.val := by
    intro eq
    obtain ⟨y,z,different⟩ := nonconstant
    have same (x : Fin m → Bool) : C.eval (List.ofFn (pin v rename false x)) = false := by
      rw [← eval, eq, getD_wiresFrom _ _ _ (by simp), ofFnAt]
      simp [pin]
    exact different ((same y).trans (same z).symm)
  obtain ⟨y, low, high⟩ := depends
  let lo := List.ofFn (pin v rename false y)
  let hi := List.ofFn (pin v rename true y)
  have agree (i : ℕ) (distinct : i ≠ v.val) : hi.getD i false = lo.getD i false := by
    by_cases within : i < n
    · let j : Fin n := ⟨i,within⟩
      have ne : j ≠ v := fun e => distinct (congrArg Fin.val e)
      change (List.ofFn _).getD j.val false = (List.ofFn _).getD j.val false
      rw [ofFnAt,ofFnAt]
      simp [pin,ne]
    · rw [List.getD_eq_default _ _ (by simp [hi]; omega), List.getD_eq_default _ _ (by simp [lo]; omega)]
  have highBit : hi.getD v.val false = true := by rw [ofFnAt]; simp [pin]
  have positiveReader : ∃ g ∈ gs, (!isNotGate g.op) = true ∧ v.val ∈ g.inputs := by
    by_contra none
    have noPos (g : Gate) (hg : g ∈ gs) (read : v.val ∈ g.inputs) : g.op = .not := by
      by_contra wrong
      apply none
      exact ⟨g,hg,by simpa [Bool.not_eq_true'] using (Bool.eq_false_iff.mpr (fun h => wrong ((flag_iff g).mp h))),read⟩
    by_cases exist : ∃ g ∈ gs, v.val ∈ g.inputs
    · obtain ⟨neg, hn, pinRead⟩ := exist
      have negOp := noPos neg hn pinRead
      have singlePin : neg.inputs = [v.val] := by
        have small := (ok neg hn).2 negOp
        generalize he : neg.inputs = ls at pinRead small ⊢
        cases ls with
        | nil => simp at pinRead
        | cons i t =>
          have et : t = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at small; omega)
          simp [et] at pinRead ⊢
          exact pinRead.symm
      have form (g : Gate) (hg : g ∈ gs) :
          (g.op = .not ∧ g.inputs = [v.val]) ∨ ((g.op = .and ∨ g.op = .or) ∧ v.val ∉ g.inputs) := by
        by_cases gn : g.op = .not
        · have e : g = neg := neg_unique (nn ▸ one) hg hn gn negOp
          exact Or.inl ⟨gn, e ▸ singlePin⟩
        · have hop := (ok g hg).1.1
          change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
          exact Or.inr ⟨hop.elim Or.inl (fun h => Or.inr (h.resolve_right gn)), fun r => gn (noPos g hg r)⟩
      have implication := gate_inputs_preserve v.val gs form lo hi (by simp [hi,lo])
        (by simp [lo]) highBit (fun i h pos => (agree i h) ▸ pos) C.output output
      have mismatch := implication ((eval _).trans high)
      rw [eval, low] at mismatch
      cases mismatch
    · have e := agree_except v.val gs hi lo (fun g hg read => exist ⟨g,hg,read⟩)
        (by simp [hi,lo]) agree C.output output
      rw [eval, eval, high, low] at e
      cases e
  let initial : List Stat := List.ofFn fun i : Fin n =>
    if i = v then Sum.inl false else Sum.inr (rename i).val
  have start (x : Fin m → Bool) :
      Inv m (List.ofFn x) (List.ofFn (pin v rename false x)) (initial, []) := by
    refine ⟨by simp [initial], ?_⟩
    intro i
    change (initial.getD i (Sum.inl false)).Valid m ∧
      (initial.getD i (Sum.inl false)).val (List.ofFn x) = (List.ofFn (pin v rename false x)).getD i false
    by_cases within : i < n
    · let j : Fin n := ⟨i, within⟩
      unfold initial
      rw [ofFnAt _ _ j, ofFnAt _ _ j]
      by_cases eq : j = v
      · simp [eq, Stat.Valid, Stat.val, pin]
      · simp only [eq, ↓reduceIte, Stat.Valid, Stat.val, pin]
        exact ⟨(rename j).isLt, ofFnAt _ _ _⟩
    · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  let acc := elim m gs (initial, [])
  have sim (x : Fin m → Bool) : (acc.1.getD C.output (Sum.inl false)).val
      (wiresFrom acc.2 (List.ofFn x)) = C.eval (List.ofFn (pin v rename false x)) := by
    exact ((inv_elim m (List.ofFn x) (by simp) gs _ _ (fun g hg => (ok g hg).1) (start x)).2 C.output).2.trans (eval _)
  have kept : ncount acc.2 ≤ ncount C.gates := by
    rw [← nn]
    simpa [acc,ncount,opCount] using elim_opCount_le isNotGate m gs (initial, [])
  have small : nonNotCount acc.2 + 1 ≤ nonNotCount C.gates := by
    rw [← bn]
    have h := elim_count_drop (fun op => ! isNotGate op) m v.val gs (initial, []) ok
      (by simp [initial]) ⟨false, by change initial.getD v.val _ = _; unfold initial; rw [ofFnAt]; simp⟩ positiveReader
    simpa [acc,nonNotCount,opCount] using h
  cases hz : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x,z,e⟩ := nonconstant
    have a := sim x
    have c := sim z
    rw [hz] at a c
    exact (e (a.symm.trans c)).elim
  | inr o =>
    refine ⟨⟨acc.2,o⟩, elim_ok m gs _ (by simp), kept, small, ?_⟩
    intro x
    have h := sim x
    rw [hz] at h
    exact h

def seven (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) ||
  (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 4 && x 5) ||
  (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def five (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) ||
  (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4)

theorem reduceToFive
    (clique : ∀ D : Circuit, FanInTwo D → ncount D.gates ≤ 1 →
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) → 10 ≤ nonNotCount D.gates)
    (C : Circuit) (fan : FanInTwo C) (single : ncount C.gates ≤ 1)
    (correct : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = seven x) :
    12 ≤ nonNotCount C.gates := by
  let p : Fin 7 → Fin 6 := ![0,0,1,2,3,4,5]
  let q : Fin 6 → Fin 5 := ![0,1,0,2,3,4]
  let six := fun x : Fin 6 → Bool => seven (pin 1 p false x)
  let lastSix := fun i : Fin 6 => decide (i = 5)
  have firstChanges : seven (pin 1 p false lastSix) = false ∧ seven (pin 1 p true lastSix) = true := by decide
  have firstNotConst : seven (pin 1 p false (fun _ => false)) ≠ seven (pin 1 p false (fun _ => true)) := by decide
  obtain ⟨D, dFan, dOne, dSave, dSim⟩ := projectBinary 1 p C fan single
    ⟨lastSix, (correct _).trans firstChanges.1, (correct _).trans firstChanges.2⟩
    ⟨fun _ => false, fun _ => true, by simpa only [correct] using firstNotConst⟩
  have dc (x : Fin 6 → Bool) : D.eval (List.ofFn x) = six x := (dSim x).trans (correct _)
  let lastFive := fun i : Fin 5 => decide (i = 4)
  have secondChanges : six (pin 2 q false lastFive) = false ∧ six (pin 2 q true lastFive) = true := by decide
  have secondNotConst : six (pin 2 q false (fun _ => false)) ≠ six (pin 2 q false (fun _ => true)) := by decide
  obtain ⟨E, eFan, eOne, eSave, eSim⟩ := projectBinary 2 q D dFan (dOne.trans single)
    ⟨lastFive, (dc _).trans secondChanges.1, (dc _).trans secondChanges.2⟩
    ⟨fun _ => false, fun _ => true, by simpa only [dc] using secondNotConst⟩
  have geometry : ∀ x : Fin 5 → Bool, six (pin 2 q false x) = five x := by decide +kernel
  have minimum := clique E eFan (eOne.trans (dOne.trans single))
    (fun x => (eSim x).trans ((dc _).trans (geometry x)))
  omega

end PEqualNP.Outside.L_meta_10568_aux

namespace PEqualNP.Outside.L_meta_10568_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma countTotal (gs : List Gate) : nonNotCount gs + ncount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change opCount (fun op => !isNotGate op) (g::gs) + opCount isNotGate (g::gs) = _
    rw [opCount_cons, opCount_cons]
    change opCount (fun op => !isNotGate op) gs + opCount isNotGate gs = gs.length at ih
    cases bit : isNotGate g.op <;> simp only [Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem indices_unique (gs : List Gate) (one : ncount gs ≤ 1) :
    ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
  induction gs with
  | nil => intro i; exact Fin.elim0 i
  | cons g gs ih =>
    change opCount isNotGate (g::gs) ≤ 1 at one
    rw [opCount_cons] at one
    have tailBound : ncount gs ≤ 1 := by unfold ncount; omega
    have apart (atHead : g.op = .not) (j : Fin gs.length) (atTail : (gs.get j).op = .not) : False := by
      have flag := (flag_iff g).mpr atHead
      rw [flag, if_pos rfl] at one
      have zero : gs.countP (fun a => isNotGate a.op) = 0 := by
        change opCount isNotGate gs = 0
        omega
      exact List.countP_eq_zero.mp zero _ (List.get_mem _ _) ((flag_iff _).mpr atTail)
    intro i j
    refine Fin.cases ?_ (fun u => ?_) i
    · refine Fin.cases (fun _ _ => rfl) (fun t a b => (apart a t b).elim) j
    · refine Fin.cases (fun a b => (apart b u a).elim)
        (fun t a b => congrArg Fin.succ (ih tailBound u t a b)) j

theorem liftClique
    (total : ∀ D : Circuit, FanInTwo D → (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) → 10 ≤ D.size)
    (noNeg : ∀ D : Circuit, FanInTwo D → ncount D.gates ≤ 1 → D.size = 10 →
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) → ncount D.gates = 0)
    (D : Circuit) (legal : FanInTwo D) (one : ncount D.gates ≤ 1)
    (correct : ∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) :
    10 ≤ nonNotCount D.gates := by
  have low := total D legal correct
  have eq := countTotal D.gates
  change 10 ≤ D.gates.length at low
  by_cases t : D.size = 10
  · have := noNeg D legal one t correct
    omega
  · change D.gates.length ≠ 10 at t
    omega

def witness : Circuit := ⟨[⟨.or,[0,6]⟩,⟨.or,[4,5]⟩,⟨.or,[0,1]⟩,⟨.or,[3,8]⟩,⟨.and,[9,10]⟩,⟨.and,[4,5]⟩,⟨.or,[7,8]⟩,⟨.or,[9,10]⟩,⟨.or,[11,12]⟩,⟨.and,[6,14]⟩,⟨.and,[2,13]⟩,⟨.or,[16,17]⟩,⟨.or,[15,18]⟩],19⟩
theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem cost : witness.gates.length = 13 := rfl
set_option maxRecDepth 9000 in
set_option maxHeartbeats 6000000 in
theorem correct : ∀ x : Fin 7 → Bool, witness.eval (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 6000000 in
lemma postedBridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = seven x := by decide +kernel

theorem finishing (clique : ∀ D : Circuit, FanInTwo D → ncount D.gates ≤ 1 → (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) → 10 ≤ nonNotCount D.gates) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal single computes
  by_cases used : ∃ g ∈ gates, g.op = GateOp.not
  · let C : Circuit := ⟨gates,o⟩
    have fan : FanInTwo C := by
      intro g hg
      obtain ⟨op,size⟩ := legal g hg
      exact ⟨op,size⟩
    have correctSeven : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = seven x := by
      intro x
      exact (computes x).trans (postedBridge x)
    have lower := reduceToFive clique C fan (count_le_one gates single) correctSeven
    have total := countTotal gates
    obtain ⟨g,hg,hNeg⟩ := used
    have positive : ncount gates ≠ 0 := by
      intro z
      exact List.countP_eq_zero.mp z g hg ((flag_iff g).mpr hNeg)
    change 12 ≤ nonNotCount gates at lower
    exact ⟨witness.gates, witness.output, mono, by rw [cost]; omega, correct⟩
  · exact ⟨gates,o,fun g hg => ⟨(legal g hg).1.elim Or.inl (fun h =>
      Or.inr (h.resolve_right (fun hn => used ⟨g,hg,hn⟩))), (legal g hg).2⟩, le_rfl, computes⟩

end PEqualNP.Outside.L_meta_10568_aux

namespace PEqualNP.Outside.L_meta_10568.Charge
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]


end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568.Charge
open PEqualNP.CircuitLowerBounds
private lemma bin_lawsFew (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_lawsFew : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_casesFew {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)


def finiteW (w : List Sig) (z : Sig) (limit : Nat) : Prop :=
  (1 ≤ limit ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (limit=0 ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma binFew {w a b} (d : Bool) (limit : Nat) (binary : limit=0) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ finiteW w (bin d a b) limit := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_lawsFew a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_lawsFew b
  rcases operand_casesFew ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_casesFew hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨binary,d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma gateFew (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ finiteW w (gv w g) (g.op.eval [false]).toNat := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ finiteW w (neg a) 1 := by
    rcases operand_casesFew ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_lawsFew.1 ▸ ro)
    · exact Or.inl (neg_lawsFew.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨by decide,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_lawsFew _).1] using Or.inl (b := finiteW w (w.getD i zero) (GateOp.and.eval [false]).toNat) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_lawsFew _).2.1] using Or.inl (b := finiteW w (w.getD i zero) (GateOp.or.eval [false]).toNat) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_lawsFew _).1] using binFew false (GateOp.and.eval [false]).toNat rfl (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_lawsFew _).2.1] using binFew true (GateOp.or.eval [false]).toNat rfl (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)


lemma pullFew {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    {limit : Nat} (hz : represented w z ∨ finiteW w z limit) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k'-t' ≤ (k-t)+(1-limit) ∧ t' ≤ t+limit ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  have htk := (live_size h).1
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨room,a,ha,hp',eq⟩ | ⟨binCap,d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,by omega,by omega,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,by omega,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extractFew (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k-t ≤ gs.countP (fun g => !g.op.eval [false]) ∧ t ≤ gs.countP (fun g => g.op.eval [false]) ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hnot,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hc,hu,hT⟩ := pullFew ht (gateFew w g (legal g (by simp))) hs
    refine ⟨l,u,T,?_,?_,hu,hT⟩ <;>
      cases he : g.op.eval [false] <;> simp [List.countP_cons,he] at hl hc ⊢ <;> omega
def ChargedImpossible (T : Sig) (b h : Nat) (S : Finset Sig) :=
  ∀ k t, k-t ≤ b → t ≤ h → ¬Live T k t S
set_option maxHeartbeats 1600000 in
theorem enumCharged {T : Sig} {cap fuel : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : 0 < fuel → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap+1 →
      ChargedImpossible T cap (fuel-1) (childOne ws a keep).toFinset)
    (twoStep : 0 < cap → ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ChargedImpossible T (cap-1) fuel (childTwo ws a b d ka kb).toFinset) :
    ChargedImpossible T cap fuel ws.toFinset := by
  classical
  intro k t hk nt h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have ntk := (live_size tail).1
    have len : (childOne ws a keep).length ≤ cap+1 := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have ntk := (live_size tail).1
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep (by have := (live_size tail).1; omega) a am b bm d ka kb hab fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)


def fiveInputs := vars 31
def sampleFive (r : Row) (j : Fin 5) := bit r (fiveInputs.getD j.val zero)
def five (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4)
theorem edgeFive : ∀ r : Row, bit r graph = five (sampleFive r) := by decide +kernel
theorem fiveList : List.ofFn (fun j : Fin 5 => fiveInputs.getD j.val zero) = fiveInputs := by decide +kernel
theorem sampleList (r : Row) : List.ofFn (sampleFive r) = fiveInputs.map (bit r) := by
  rw [←fiveList,List.map_ofFn]
  rfl
def nearFive (i : Fin 5) : Row := if i.val=0 then 2 else 1
def upFive (i : Fin 5) : Row := Fin.ofNat 512 (1 <<< i.val ||| (nearFive i).val)
theorem witnessFive : ∀ i : Fin 5, (bit (nearFive i) graph != bit (upFive i) graph) &&
    (fiveInputs.all fun w => w == fiveInputs.getD i.val zero || bit (nearFive i) w == bit (upFive i) w) = true := by decide +kernel
theorem allFive {k t s} (run : Live graph k t s) (sub : ∀ w ∈ s, w ∈ fiveInputs) : s = fiveInputs.toFinset := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨sub a,?_⟩
  intro hm
  rw [←fiveList,List.mem_ofFn] at hm
  obtain ⟨i,rfl⟩ := hm
  have hw := witnessFive i
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hw
  apply raw_required run _ _ sub _ _ hw.1
  exact fun _ ha ne => (hw.2 _ ha).resolve_left ne
theorem transferFive (none : ChargedImpossible graph 9 1 fiveInputs.toFinset)
    (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (oneN : C.gates.countP (fun g => g.op.eval [false]) ≤ 1)
    (correct : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = five x) :
    10 ≤ C.gates.countP (fun g => !g.op.eval [false]) := by
  by_contra! lower
  have val : (execute C.gates fiveInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r ((execute C.gates fiveInputs).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1),←sampleList,edgeFive]
    exact correct _
  have av := get_rep (execute C.gates fiveInputs) C.output
  rw [val] at av
  obtain ⟨k,t,s,hb,hn,live,hs⟩ := extractFew C.gates _ fan graph_proper
    (av.resolve_right (fun f => f graph_proper))
  exact none k t (by omega) (by omega) (allFive live hs ▸ live)

end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568.Charge

abbrev CheckContext := Nat × Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → Nat → Nat → List (List Sig))
def nextBin (op cap : Nat) := if op=2 then cap else cap-1
def nextNeg (op fuel : Nat) := if op = 2 then fuel-1 else fuel

def certClose (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun p => scalarPoolCut p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem certClose_sound {raw T pools links k fuel rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ChargedImpossible T k fuel xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup) (ok : certClose pools links (k+fuel) rest op = true) :
    ChargedImpossible T k fuel (choiceVal op :: rest).toFinset := by
  simp only [certClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨p,hp,hh⟩ | ⟨xs,hx,hh⟩
  · intro n t nb nt live
    have htk := (live_size live).1
    exact scalarPoolCut_sound (pValid _ hp) nd hh n t (by omega) live
  · rw [sameWords_sound hh]; exact lValid _ _ hx

def checkMove (ctx : CheckContext) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,fuel,n,ws,cov,pools,links) := ctx
  let un := op==2
  let nf := nextNeg op fuel
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if (un && fuel==0) || (!un && cap==0) then true else
  if len>nextBin op cap+1 then true else
    let direct := (nf==0)
    let cc := restCov (getCov cov direct) (column direct a.2) (column direct b.2) un ka kb
    if (cc ||| column direct z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := opKeep un ka kb a b ws
      certClose pools (links (nextBin op cap) nf) (nextBin op cap+nf) (rest.map Prod.fst) (movedChoice op a b)

theorem checkMove_sound {raw T r s ws pools links cap fuel a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : op ≠ 2 → 0<cap) (permitted : op=2 → 0<fuel)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ n f tag xs, xs ∈ links n f tag → ChargedImpossible T n f (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : checkMove (cap,fuel,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    ChargedImpossible T (nextBin op cap) (nextNeg op fuel) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk nt h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have ntk := (live_size h).1
  have len : child.length ≤ nextBin op cap+1 := by omega
  unfold checkMove at test
  have hg : (((op==2) && (fuel==0)) || (!(op==2) && (cap==0)))=false := by
    by_cases he : op=2
    · simp [he,show fuel≠0 by have := permitted he; omega]
    · simp [he,show cap≠0 by have := hcap he; omega]
  simp only [hg,Bool.false_eq_true,ite_false] at test
  rw [leq,if_neg (by omega)] at test
  let d := nextNeg op fuel == 0
  have sep := cover_sound h (ws:=child) rfl (pair_sep pairs) d (by
    intro hx
    have ne : nextNeg op fuel=0 := beq_iff_eq.mp hx
    omega)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  change certClose pools (links (nextBin op cap) (nextNeg op fuel)) (nextBin op cap+nextNeg op fuel)
    (rest.map Prod.fst) (movedChoice op a b)=true at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact certClose_sound pv (lv _ _) nd' test k t hk nt h

def testPairF (ctx : CheckContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := checkMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRowF (ctx : CheckContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  checkMove ctx 2 a a z false false && checkMove ctx 2 a a z true true &&
    bs.all (fun b => testPairF ctx a b false && testPairF ctx a b true)
def testAllF (ctx : CheckContext) : List Decor → Bool
  | [] => true
  | a::bs => testRowF ctx a bs && testAllF ctx bs

theorem all_unaryF {ctx ws} (h : testAllF ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    checkMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllF,Bool.and_eq_true,testRowF] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binaryF {ctx ws} (h : testAllF ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPairF ctx a b d=true ∨ testPairF ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllF,Bool.and_eq_true,testRowF,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPairF_at {ctx a b d} (h : testPairF ctx a b d = true) (ka kb : Bool) :
    checkMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPairF,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem nodeFew {raw T r s ws pools links cap fuel}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ n f tag xs, xs ∈ links n f tag → ChargedImpossible T n f (List.toFinset xs))
    (checks : testAllF (cap,fuel,ws.length,ws,preCov ws,pools,links) ws = true) :
    ChargedImpossible T cap fuel (ws.map Prod.fst).toFinset := by
  apply enumCharged nd out
  · intro can v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact checkMove_sound (op:=2) pairs faith nd ha ha (by simp) (fun he => False.elim (he rfl)) (fun _ => can) pv lv pro fresh (all_unaryF checks ha keep)
  · intro canB a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairF (cap,fuel,ws.length,ws,preCov ws,pools,links) a b d = true) :
        ChargedImpossible T (cap-1) fuel (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have p : (if d then 1 else 0 : Nat) ≠ 2 := by cases d <;> decide
      have h := checkMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) (fun _ => canB)
        (fun he => False.elim (p he)) pv lv (eq ▸ pr) (eq ▸ fr) (testPairF_at test ka kb)
      simpa only [nextNeg,nextBin,if_neg p] using h
    rcases all_binaryF checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh



end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem chargeBridge
    (clique : ∀ D : Circuit, FanInTwo D →
      D.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) →
      10 ≤ D.gates.countP (fun g => !g.op.eval [false]))
    (D : Circuit) (fan : FanInTwo D) (h : ncount D.gates ≤ 1)
    (correct : ∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) :
    10 ≤ nonNotCount D.gates := by
  have agree (g : Gate) (hg : g ∈ D.gates) : g.op.eval [false] = isNotGate g.op := by
    have op := (fan g hg).1
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    rcases op with e | e | e <;> rw [e] <;> rfl
  have n : D.gates.countP (fun g => g.op.eval [false]) = ncount D.gates :=
    List.countP_congr (fun g hg => by rw [agree g hg])
  have b : D.gates.countP (fun g => !g.op.eval [false]) = nonNotCount D.gates :=
    List.countP_congr (fun g hg => by rw [agree g hg])
  rw [← b]
  exact clique D fan (n ▸ h) correct

end PEqualNP.Outside.L_meta_10568_aux

namespace PEqualNP.Outside.L_meta_10568_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_10568.Charge

theorem chargeCost (none : ChargedImpossible graph 9 1 fiveInputs.toFinset)
    (D : Circuit) (fan : FanInTwo D) (h : ncount D.gates ≤ 1)
    (correct : ∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = five x) : 10 ≤ nonNotCount D.gates := by
  exact chargeBridge (PEqualNP.Outside.L_meta_10568.Charge.transferFive none) D fan h correct

end PEqualNP.Outside.L_meta_10568_aux

namespace PEqualNP.Outside.L_meta_10568.Charge
def cutColumns : Array ColumnInfo := #[(1,0,30,0,7),(1,2,0,28,2),(1,4,0,26,2),(1,8,0,22,2),(1,16,0,14,2),(2,0,29,0,7),(2,1,0,28,2),(2,4,0,25,2),(2,8,0,21,2),(2,16,0,13,2),(3,0,28,0,4),(3,4,0,24,1),(3,8,0,20,1),(3,16,0,12,1),(4,0,27,0,7),(4,1,0,26,2),(4,2,0,25,2),(4,8,0,19,2),(4,16,0,11,2),(5,0,26,0,4),(5,2,0,24,1),(5,8,0,18,1),(5,16,0,10,1),(6,0,25,0,4),(6,1,0,24,1),(6,8,0,17,1),(6,16,0,9,1),(7,0,24,0,1),(8,0,23,0,7),(8,1,0,22,2),(8,2,0,21,2),(8,4,0,19,2),(8,16,0,7,2),(9,0,22,0,4),(9,2,0,20,1),(9,4,0,18,1),(9,16,0,6,1),(10,0,21,0,4),(10,1,0,20,1),(10,4,0,17,1),(10,16,0,5,1),(11,0,20,0,1),(12,0,19,0,4),(12,1,0,18,1),(12,2,0,17,1),(12,16,0,3,1),(13,0,18,0,1),(14,0,17,0,1),(16,0,15,0,7),(16,1,0,14,2),(16,2,0,13,2),(16,4,0,11,2),(16,8,0,7,2),(17,0,14,0,4),(17,2,0,12,1),(17,4,0,10,1),(17,8,0,6,1),(18,0,13,0,4),(18,1,0,12,1),(18,4,0,9,1),(18,8,0,5,1),(19,0,12,0,1),(20,0,11,0,4),(20,1,0,10,1),(20,2,0,9,1),(20,8,0,3,1),(21,0,10,0,1),(22,0,9,0,1),(24,0,7,0,4),(24,1,0,6,1),(24,2,0,5,1),(24,4,0,3,1),(25,0,6,0,1),(26,0,5,0,1),(28,0,3,0,1)]
def rotations5 : Array (List Nat) := #[[],[67],[50],[50,66],[66,50],[66],[33],[33,67],[33,49],[33,49,65],[33,65,49],[33,65],[49,33],[49,33,66],[49],[49,65],[49,66],[49,66,33],[65,33,50],[65,33],[65,49],[65],[65,50,33],[65,50],[16],[16,67],[16,50],[16,50,66],[16,66,50],[16,66],[16,32],[16,32,67],[16,32,48],[16,32,48,64],[16,32,64,48],[16,32,64],[16,48,32],[16,48,32,66],[16,48],[16,48,64],[16,48,66],[16,48,66,32],[16,64,32,50],[16,64,32],[16,64,48],[16,64],[16,64,50,32],[16,64,50],[32,16],[32,16,67],[32,16,49],[32,16,49,65],[32,16,65,49],[32,16,65],[32],[32,67],[32,48],[32,48,64],[32,64,48],[32,64],[32,49],[32,49,65],[32,49,16],[32,49,16,64],[32,49,64,16],[32,49,64],[32,65,49],[32,65],[32,65,16,48],[32,65,16],[32,65,48],[32,65,48,16],[48,16,33],[48,16,33,66],[48,16],[48,16,65],[48,16,66],[48,16,66,33],[48,32],[48,32,66],[48],[48,64],[48,66],[48,66,32],[48,33,16],[48,33,16,65],[48,33],[48,33,64],[48,33,65],[48,33,65,16],[48,65,32,33],[48,65,32],[48,65,33],[48,65,33,32],[48,65],[48,65,16],[64,16,33,50],[64,16,33],[64,16,49],[64,16],[64,16,50,33],[64,16,50],[64,32,50],[64,32],[64,48],[64],[64,50,32],[64,50],[64,33,16,49],[64,33,16],[64,33,48],[64,33],[64,33,49,16],[64,33,49],[64,49,32],[64,49,32,33],[64,49,33,32],[64,49,33],[64,49,16],[64,49]]
def pointsPos5 : Nat → Bits
  | 0 => 0xfc0fc0fc0fc0fc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff
  | 1 => 0xfff000fff000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f
  | 2 => 0xfff000000ffffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc0
  | 3 => 0xfffffffff00000000003ffffffffff000000ffffffffffff00000000003ffffffffff000000ffffffffffff00000000003ffffffffff000000ffffffffffff00000000003ffffffffff000000ffffffffffff00000000003ffffffffff000000
  | 4 => 0xfffffffffffffffffffc0000000000000000ffffffffffffffffffffffc0000000000000000ffffffffffffffffffffffc0000000000000000ffffffffffffffffffffffc0000000000000000ffffffffffffffffffffffc0000000000000000
  | _ => 0
def pointsNeg5 : Nat → Bits
  | 0 => 0x82082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082
  | 1 => 0x104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104
  | 2 => 0x208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208
  | 3 => 0x410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410
  | 4 => 0x820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820
  | _ => 0
def pointsPos4 : Nat → Bits
  | 0 => 0xe0f83e0ffc1fffc1f07c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff
  | 1 => 0xff003ff07fe0fffe007fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f
  | 2 => 0xffffc0007fff07ffff8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe0
  | 3 => 0xffffffff800007ffffffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff00000
  | _ => 0
def pointsNeg4 : Nat → Bits
  | 0 => 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842
  | 1 => 0x842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084
  | 2 => 0x84210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108
  | 3 => 0x108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
  | _ => 0
def pointsPos3 : Nat → Bits
  | 0 => 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ff
  | 1 => 0xff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f
  | 2 => 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
  | _ => 0
def pointsNeg3 : Nat → Bits
  | 0 => 0x222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222
  | 1 => 0x444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444
  | 2 => 0x888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
  | _ => 0
def pointsPos2 : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | _ => 0
def pointsNeg2 : Nat → Bits
  | 0 => 0x492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492
  | 1 => 0x924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924
  | _ => 0
def pointsPos : Nat → Nat → Bits
  | 5 => pointsPos5
  | 4 => pointsPos4
  | 3 => pointsPos3
  | 2 => pointsPos2
  | _ => fun _ => 0
def pointsNeg : Nat → Nat → Bits
  | 5 => pointsNeg5
  | 4 => pointsNeg4
  | 3 => pointsNeg3
  | 2 => pointsNeg2
  | _ => fun _ => 0
def pathC2645 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC2645 (i : Nat) := (0x1f >>> (5*i)) &&& 0x1f
def spanC2645 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2645 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2645 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC2645 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC2645 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC2645 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC2644 (i : Nat) := (0x322001 >>> (11*i)) &&& 0x7ff
def liveC2644 (i : Nat) := (0xfdf >>> (6*i)) &&& 0x3f
def spanC2644 (i : Nat) := (0x8504 >>> (8*i)) &&& 0xff
def ruleC2644 (i : Nat) := (0x1c385c0070e140 >>> (6*i)) &&& 0x3f
def hashC2644 (i : Nat) := (0x9000060000000005 >>> (4*i)) &&& 0xf
def locC2644 (i : Nat) := (0x4688 >>> (3*i)) &&& 0x7
def cntC2644 (i : Nat) := (0x1f >>> (1*i)) &&& 0x1
def aliasC2644 (i : Nat) := (0x83a1818089 >>> (8*i)) &&& 0xff
def pathC2629 (i : Nat) := (0x288410 >>> (11*i)) &&& 0x7ff
def liveC2629 (i : Nat) := (0xfff >>> (6*i)) &&& 0x3f
def spanC2629 (i : Nat) := (0x2282 >>> (7*i)) &&& 0x7f
def ruleC2629 (i : Nat) := (0x3070e140140 >>> (6*i)) &&& 0x3f
def hashC2629 (i : Nat) := (0x10000800009c3961741696540 >>> (6*i)) &&& 0x3f
def locC2629 (i : Nat) := (0x9ca307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def cntC2629 (i : Nat) := (0xfffff >>> (1*i)) &&& 0x1
def aliasC2629 (i : Nat) := (0xdaaa5aa42a8cc29e1e0c8042863c24bc129206 >>> (8*i)) &&& 0xff
def pathC2628 (i : Nat) := (0x195543caaa1d109120848800510 >>> (21*i)) &&& 0x1fffff
def liveC2628 (i : Nat) := (0x7fbffffbf >>> (7*i)) &&& 0x7f
def spanC2628 (i : Nat) := (0x40668c82884008 >>> (11*i)) &&& 0x7ff
def ruleC2628 (i : Nat) := (0x38304721488800e0c01c0522001388e42a02390e0501660008e4c21c85028c100004e238601c050380a00 >>> (9*i)) &&& 0x1ff
def hashC2628 (i : Nat) := (0xcc2040004c02b0706ba65022 >>> (6*i)) &&& 0x3f
def locC2628 (i : Nat) := (0xdeb38bdab49ca307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def cntC2628 (i : Nat) := (0xfffffff >>> (1*i)) &&& 0x1
def aliasC2628 (i : Nat) := (0x230420180c0f012168a4418812f0004010c20c1e701030a88049024279012191e4f240 >>> (10*i)) &&& 0x3ff
def pathC2613 (i : Nat) := (0x53244292a214951080a90d204428a2094c810864085100428284351410 >>> (21*i)) &&& 0x1fffff
def liveC2613 (i : Nat) := (0x1fffdfffff7fffff2fcf >>> (7*i)) &&& 0x7f
def spanC2613 (i : Nat) := (0x17aa93485808b29221a524840423002 >>> (11*i)) &&& 0x7ff
def ruleC2613 (i : Nat) := (0xb04e23a602a050701d05802c1388e0541600300e23a0b000b8141c8058272611c070282605828000a8500401609c4741601054e23a000018070140e02a000a00 >>> (9*i)) &&& 0x1ff
def hashC2613 (i : Nat) := (0xa09364462a000c3843410180ec084 >>> (7*i)) &&& 0x7f
def locC2613 (i : Nat) := (0x9e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040 >>> (6*i)) &&& 0x3f
def cntC2613 (i : Nat) := (0xffffffffff >>> (1*i)) &&& 0x1
def aliasC2613 (i : Nat) := (0x600c1100a3c90060181295908f80c1aa10062c12d00054eab58e001a0290864402200a2680181790a3e81bb04003820031a4072098c404 >>> (11*i)) &&& 0x7ff
def pathC2612 (i : Nat) := (0x66651532ccca2a65999454cb3328a9966651432ccca286510e5550ea84aaa1d4095534a212aa870425550e984aaa1d10955438212aa8741a5550e034aaa1d3244244a4c8848949910912032432252044244a2681c8919510912990212243204244a200848951810912830432253604244002992200052544000a4a8800145104 >>> (31*i)) &&& 0x7fffffff
def liveC2612 (i : Nat) := (0xffbfdf9f9fcfe7dfefffffdfdfdf9fdfffffbffffff79ffffffcafbfb77f7f5f6f >>> (8*i)) &&& 0xff
def spanC2612 (i : Nat) := (0x18e3bf45d16c915a5a82d21278d325942c81228d00a7843a11c08d46652af995d09c94642094ecc6c530314207d2307104059410e004 >>> (13*i)) &&& 0x1fff
def ruleC2612 (i : Nat) := (0xa83e1131cc382aac03e110852002a0f84461580ac31cc382a0f844014008701c0143e0021c071850f980a3a851128063985a3a85110800c28ea14442021c8c0442148087230110806398583a0511000639856021c8c20e1100a0140087230839850144460000038051118004c0a111804c11c43a308160043b3002a058009cc710e817308008523b3005e0e815304008e2148004d0e02a05cc0002148009421c3905cc2004c00a01680000804c11c43a30800804c10e8c200c730ecc00a200000d71c4c30e21405200002708e2171c0380a0173040021cc30e21405200002c1300a80a4149c239002c09c02905401b00c19c0708e415006718e21500 >>> (10*i)) &&& 0x3ff
def hashC2612 (i : Nat) := (0xc5b309022a003b3db01b4041a51604000a1a04012b3011030200008855007d3b04020a08 >>> (8*i)) &&& 0xff
def locC2612 (i : Nat) := (0x34e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 >>> (7*i)) &&& 0x7f
def cntC2612 (i : Nat) := (0x3ffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2612 (i : Nat) := (0xd00cc04402f01930c20180003cf0408058002095601801c1a46173c4805031000b402813012400200c005c00211000b1e6183501960c013002a65480500004b6f002a380016ab009786c81402a61308eda6188ac0e04a800822879eb47815c31a058321831c0986960cb044582aa0b1cc184c01860c022012d324c04002033c02260204a00358416933cab1540b400e005831011604b10fda4c31c0581002750239745900215c23200642181 >>> (13*i)) &&& 0x1fff
def pathC2597 (i : Nat) := (0x4654c910a6c92a21491454429aa4a8851051532a6c92a214d9254420326a90d3501521aa002a43418154caa304a8853544120aca9022158520442922288246545104aa48a2095490445228264895104d124ac08a2091811240a882488250345134a208a2094c13441299268925464c810a6892021595100cab284218532440108209906549910042132200854341421820928874d9050868b20a1954341443a60828434914504200a2a19562514108c08a865441450ca0828a1954349443 >>> (31*i)) &&& 0x7fffffff
def liveC2597 (i : Nat) := (0x9fbfefdfdfdf9fdfdfdebfafdf9fbfefefefcffbefeffaefe7efe7e3bfefdf9ffcf3fcfcdfdfdf9fc7dfcfddcfddcfcfc3 >>> (8*i)) &&& 0xff
def spanC2597 (i : Nat) := (0x1327980cb0a5052619304716343143871c20e008fc2792bb89c4cda46b1339188ac025e12c95586a064d1a415146862401a000e8c6a53219694a86502270930484a3e21c18b184881a50920214008000 >>> (13*i)) &&& 0x1fff
def ruleC2597 (i : Nat) := (0x381c0002a02805c00b02380a2708e028306728ec17006020583a80c3b052002a2000a2380ac1700016000c01c239058000a8008e4388581500800390d485400858018ec1400a001781505039808720e2150005c13a140e4020e02900070300e421a158002885400350c01c085000383007005c009c23b000288e47085015006c19c6380a80185839806c19c6380a8018e02a00028806000a0c21c83985a0021a020502880670350398e8160005e1c839806703563a05800178720e6003e8720e615806161c83980 >>> (10*i)) &&& 0x3ff
def hashC2597 (i : Nat) := (0x120000011aa488a0600574005e00002a40f9301cde008f802261c00448e01d009340c060202c1e23248cc280b00440080b0d104ce1601800003b060046e4f7d3c404d5 >>> (9*i)) &&& 0x1ff
def locC2597 (i : Nat) := (0xb3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 >>> (8*i)) &&& 0xff
def cntC2597 (i : Nat) := (0xfffffffffffffffffffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2597 (i : Nat) := (0x6083230500e3d8803c083b4680b2d0101932cd765f9980101781800017a40083c7a88c84f01701b9eb402b024707b1be09640b8088f260dc062d466ad380b08e807a484f2800f612083c84a00c507cd518162123c7a5d4004043816078c8d4b480078d0709002f007c03278400c813ed3e556116810235c15f1ec85851c90a142e3c3425c0e4a978094f3c25d74c0a49e4819f312186c00c0653eabc3e13c618134c8280ba1ce08e0164191613025c0380308997a3807691a7a6c1212a00ae25111201798da019124bcb9fcd21d0d180bde0af1850e3f75a3418c007bc64326f1a0950114c58028918003813da58702e0740b625948da164d92497062c88830ec1d98c8b401b472c78a0005e0c0cd055809d8481e44920c2464e01f5a4407d3c8a8bb43c8 >>> (13*i)) &&& 0x1fff
def pathC2596 (i : Nat) := (0xceea326a90e77519354873ba8c9aa439dd464d521ceea306a90e77518354873bacaa12659dd6550c21ceea326a10e77519350873ba8c9a8439dd6351421ceeb1a8a10c259992550e194cca2a655166651532a693326a92432999454caa84cca2a651426651532a813326a925479993549283ccca2a6558266515328c13328a9954099935492a3ccc9aa4941e6651532a653328a99520999454ca884cca2a650426651532a4f3328a99507999454ca83ccca2a6501e6651532a213328a19410999450ca994cca286544266514328213328a1957010e5550eb90872aa875d81095510aa2a04aa9a5414c25550e982812aa694c94295534886884aaa1d574425550ea3a212aa695490295543a84814aa9a4764425550e218212aa874401095543aae084aaa1d47042554d2938212aa875054095534a6e884aaa1d274425550e992052aa874490295543aec884aaa1c764425550e880212aa874dc1095543a8e084aa9a5070865550e938212aa874850695543820934aaa1d1041a5550e8800d2aa8741c16955438ec9922122475499109129ba4c884891d526442448ea932212256001921912a384c884894dc2644244aec902212256240d1391238224814894091348e44a4091a072252148d13912990ca884894846540644a0e32a432247544032912bb042184894c9100424482099065225274401091213a2008489441460ca44820a306522532518329128ba0c194894c9060ca44a469b0212240145832912b926c084891c1160ca44a648b065220014d92544000a48a2a2000535495100028828a990014d92544000a6c92a200055245104002a92088a0014413449000a068a268005324d124 >>> (41*i)) &&& 0x1ffffffffff
def liveC2596 (i : Nat) := (0x9fd7f3f1f9febe3f5fafe7e3fcfa7f6fe6dfd7ecf3f9fd7ebe7f9fcff3f9f5f5fe7f3f9fcfe7e3f9fcfe7f87cfe7d9ec73ce7f9fcfe3f3d7edfdbf5cffcffcafdbef7cfafd7fb7dbcfd7fb95fa7d7eb79fcfe7fbd5f9fd7e7f9f8fefadf779fedff5f3f9fc73f9d8fd7e7ffcf9ff3f9afd7e8e7fb3dbef76fbdd8afddedf6fb7d3eef67bbdcee3 >>> (9*i)) &&& 0x1ff
def spanC2596 (i : Nat) := (0xb686d81b602d61b392c64af16b82ad86b22a91ea02a49e8e2a28a8439f127259b8a6a2990e621970e5a196065239406484908e3c38d8e3418d023408a962a088921e28592103830a0447f11f637c89f017b09e44778dda2750dcc4718dc607089bc36d8db036b09a6368899a4649186661818605e997625a1d623551d4a551894034e8d3624a99224461512341990033e10f043a10e043594d223198b682d04ae32a88a812810984248c8a4210c7e31e887051a8c6051610542138c4a210903e20e0c3040b082820984203068c1430310006 >>> (14*i)) &&& 0x3fff
def ruleC2596 (i : Nat) := (0x220300000c00b80e00a6c00bb0e60a0aa8e60e00a000128390720941c8250738380760500a000ce0393380e70700ec0a014c002a07c0aa5802a07c1114e30e07c110154b061d21640030000c398e30e0541118700007c110000000540f82230e0000a81f04461c0f82230e088000050050000001503e0880000283e0140140003e0000aac283eb000f8c298007c60347685088a0147685089a00051000006002204408820047685089a00224859006380511c0388c0c000e089201180449001124061cc602000061cc604700e230c398c0c29800880c00504441d0160018001c1120018530005c09a058018731860e01460000000c618711860e30a014c00000880290061cc6004cc28053000002201701c014c004400011002980088028c01800142384e08010a0c00510e0140140003063943b02e0021c815003300380280981700183b0290066002b02e00e6002b02e0006043902c00100c3b02d0011dcc00bd054014158008011c08409f304002144e08e0540940bf30e0002a9800a00a0729800a1002141800a660c718740081ccc18033061c02a00330015000983056004c18003e055c1698700060c168002a027c179850011ccc010b0e660c019802161ccc18002a02fcc3800b06002380530051c27047300014600d819c06063942a0031cc154021c41c6001c82150a6008700e138071c2b80 >>> (11*i)) &&& 0x7ff
def hashC2596 (i : Nat) := (0x11e006af0a4943829900070a067c0acbf0b8479e42e0d072034d79d0c99cced0840b000020000d0b81495a460480404c000ac70104540143d0fc0100c000480f0141817000004080402e91002018000280e15806060000024101c008fc000180504c4a00c24058018ec030040700c0001a23000000440900009000077e4007ac47054000059f6681801c120400d00000 >>> (10*i)) &&& 0x3ff
def locC2596 (i : Nat) := (0xabd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff
def cntC2596 (i : Nat) := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2596 (i : Nat) := (0x7400218ae125070ef18c08c1a69e861d181c4041e18622c0034f11081000b010240483a200e0286787542c08e1a7278dc828f2598d72140064c0a5d30f02278a1ae81887a501078ed831215101b6040b84cc170696c00a24c04e00b47098006241cbc262380c802f00cb0a19f6e026869cc25b11e810247b0228000f3280168514a5201d801cf0f219200e0c60c1086cb6b7e808562404521cc066088034c01082180290358639f10341cb63000db0a861c06721d7186a00182e5221a28a078da5a19e80c84af801e0a5994e0335a2153000220088c1005c1e460028004fcd00426b3bca603a60c60c21a0c000896201a841206340b46250020f03010601080b76ae806001a01a20c8bc760705a2e036f09e02b80bc0c1987102206eb80f893e0e3c04542680068579e066a41e9001f0024f0a804020a82cc00780401bbe0ddc178044619817502d2a781e5800725e01ac022a03c25e08322190044c0589aa02a00bc6100c0a063007f015000802386aa601b1c667383c40c92138901d120320861c01e02c860680968163002a2b1884004bf407808a3a02900040d081bc656801e06e83c66c63cb802b822c02f92901129e3200f8cd202080bc6ec80400d21e12f6700c20013d86da00407a4a81440013c3e783dab6009bc1752402996969816f09831404748bc3338180034000e01580a001a22b468500c607504d16820288d8f868211dc0b86053cd368718ca612bf7c0822d4481d868e7af012a7ad047e01b00d922186b400681e1c0bbcc692718be619803af1036727e09e083c80904069ddd5697009619c86680008f3861e204807018ed80f307c06d02 >>> (14*i)) &&& 0x3fff
def pathC2581 (i : Nat) := (0x50719543486a38ca9922150d454d51080ea326a90d474d92544203a8c9aa43580064d521a8e1b24a8854745825412a9a0c1aa43495460d510a8a9b08a885744d8054529baca902211d95241114ac2a9a08924705490344ea80a0992254dc5049114a6e282688a557485044d29b0c08920541c6345134a8e31a04995574850445233a068a2695490345134ae48a206a1c504053244ab2286812654092444d43a4081a489a52144d244d2b0a609a2095c54050d03a0499268925574c9344922ba649a2495c1324d124ae0a1a849947048524452882649a2494c93449010a8e992200853449110042baa20a1887440104c832ace19220085570414310e9ba4c880214914644010a6c9322008526099100429386c8802151c2644010a200824a21d67105050caa3820a286549d16414438eca1a0a21d7150d0510e382429a8435854341443ac2a1a0a21d1050d2510e08286928875c143414438e090a0a10d434410510eb9a48a28215850451432a48a1a6a085434092510ea18028a8875800145432a0e0924a21d6358145086b00c08a86541c6149443a8e3126a085371814504eb3a64a2821591244d410a200828a195670c945042b3860a28434dc1051423aeca1a4a21c7650d2510eb8286928871c12151421ac0a1a4a21c604c9150ca88286928870414349443 >>> (41*i)) &&& 0x1ffffffffff
def liveC2581 (i : Nat) := (0x47e1fc7af47f3d9ea7cbf2f8fc3e9e3f8fc7f5bb567b3d3f7567b1d3e4fc7b3fe3c7e3f1f874f67f1f8fc7e3b1fa7c7e3be7b38ff0be51ef9ecde6e2f96cee47e9f1fc3f1fb3c7c3f1f8fc7ec71e9f8fe3f0f8b9cade3f395ba3d1e9fc7e653e1f47e1f0f87c9e1f4787c3 >>> (9*i)) &&& 0x1ff
def spanC2581 (i : Nat) := (0x5a02c475e2ae0d702b815a1ad0558aac1560a91538a9834c0a50d282903442a014f867833829824b8648b240910c78a3831c08b1c3921830828214009f46f437813995c44dc36d0b589ac0d2269032158c2c225f12e89740b435a02d01604ac252228854029e14c1a585282921461a2090848023e11c94dc46833401908bc65e02b2140c9844822119080748324152090c3881820820308088002 >>> (13*i)) &&& 0x1fff
def ruleC2581 (i : Nat) := (0x5402b8000a1380d41a80a001c178002160a0c00560502781410e050010381c82105447009e800000c00e0390436001081720a470108133000f81284402f4000e50001d0708709c07c2701523081d0700738080b0388288e70103a0e08e139c000519c31d838c0021438070c29803606380519c31c02b0000a31d800c00000600702241c038a0140380042111c2e8051ce0140017014a010e48000a000c28000426382221cb0a0aac0025b01873071803386030e60e300084c7605c000841c98000a0001098ec39838c060ec0a670c0021c1c614c0044054e15c0044054e0015385088e000bb80088e141538002ee002202a70ae01c2b80 >>> (11*i)) &&& 0x7ff
def hashC2581 (i : Nat) := (0x2442dc00018b615c0202e3d258ea034ce1140e06407024001321b00a130020c03802029f2000007284a141b81945f02c0100403041b52381c04c2406c5c6bc06168c802c350080067c0004022019951c00802c0463001070000b00501805000000881000008008035c4090141102c000201c00166044090240254c0200152008014ec00 >>> (10*i)) &&& 0x3ff
def locC2581 (i : Nat) := (0x4ea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff
def cntC2581 (i : Nat) := (0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2581 (i : Nat) := (0x2410841cc3c3500a00706cf1e7e7e781ae821a8aba20897209b849e00a9c74f063f3120e00481268794265008a89000902a20e180e0374d8246a02118848d846bc8d8d210a4e4a3c42c00000484c813d6a20d92051707cc0d5858028808d2e38c404110624c1e0a54780042cd9c8018f601f7642480b810d0034422087a21ba082426034e0140188822a88a026399e3053c3e1219966025606c29e800b0218a2e825a2270110010f2ce08724b4016020a39521c849a05b80ab421885c129a19c21c3d8680c6080220257700402a204a989585e0108c00c07300ca14018ba243029338441b9a781cd903202100868918091494824f01722747a20f8da4109580e12e6a0249c740228a8a418c04f6ae801c2cd062181400780d1c0a026e028e9a1809a01c007881ba478e25855a02330318de862d19b987801da4271a0a43e18c540b19e19b0006800c0252108c448031a63009e0e4867064b1e8eb28018d45b20a00cfc0230a56388999015e02b318035a003a019030e797bc94c200752f02106c8a56996a160512215002e0958086c5c186e095816e702983e001988418b80a0c09e08c601808e92200aa21b289c010b1b7801006c41f8da8098003a12686700c711781933398ccab07e18228a60ca848231b018d25e8278428009c06c4876d81c00a01b0858048801ef12405c40b837006b499ad2d00320e1d03d01d9e42a00806ef2190a880400bd82821a68e7022d79da85a0528339019000f783805210db016f0e9e6e29158 >>> (14*i)) &&& 0x3fff
def pathC2580Block : Nat → Nat
  | 0 => 0xd460d5218873bacaa1843486775193508621ceea326a10d219dd464d421a113ba8c9a84318e7758d4508690ceeb1a8a10d219dd6351421a113bac6a284360445999454cac380b3320a90c450ca6651532a5021ccc92a87604439992550ec38213328a885324d2664d524a5021ccc92a874a0439992550ec00873324aa1d8110e6649543b0e194cca2a6561c10999454428c0a13328a9958714266515218a0984cca2a474c541999254d29ba8f3324a9a41049e6651510aa8a3ccc9aa4350d3799925452402c33328a995181826651532b0e304cca2a651a14099935492302813326a925315066649534a6ea3ccc92a695914799935486a1a6f3324a8a5100426651532a90084cc9aa4961c10999454ca8c20f3328a9951451e664d5218028bccca2a6541c07999454ca880213328a195480426651432a70084cca284760132999450ca402653328a19532442665143290e884cca28654c810999450ca880213328a195680426651432a70084cca28476017210e5550e402e221caaa1c875053095543aa0992852aa69608434425550ec3886884aaa1d8210d0295543b0c082652aa2151d3240a5550ea928290caa9a53150912955348863b2212aa8756076442554caa40ec884aa9a58210c1095543b02218032aa8761c430425550ec3064084aa994434401095543886ab8212aa87485570865550e90a8e10caa9a44349c1095543a42838432aa87219274425550ea0a84894aa9a5104490295543b0c880212aa87485370865550e90a8e10caa9a52141c2195543a42838432aa8761947042554ca88020934aaa1d480850695534a900828d2aa65520764c91091242a6e93221225081d53648644a6ca386c884894d9270d91091242aec90221224855853240a44a9039a04994894e072405219123c20489a47225104091348e44b009926290c894e1211950191291a6232a03225204c46540644a40908ca80c894c131195019129920e32a252251841c654ca44a48a38ca884675a0754c81091242a209906522510041320ca44ad0082641948921527440109129384e880212254809d1004244a7013a2008489215105183291288020a3065225780c14608644b009928c19489201215182191288264a3065224104c9460ca4490a8ba0c1948921d3241832912b8a6483065224804850608644a6480a2c194892150145832912990028b06522570005160ca44a9011a6c084892157045832912b80e08b065225481c93604244a503826c0948961d324583291243a648b065225804c9160ca4490090a6c10c895c13245832912382648b0652200150d454d510002a3a6c92a20004075193548400ac2a9a089200155d2141134002a92068a268005724510350c00ac8a1a04990014092444d4300290a2692268005704c93449000ae0a1a8499001441324d124
  | 1 => 0x1a2147195214c34428e32a429868851d3649510d10a3aca98a43a2167041450cb4428e9b24a0868851c6349410d10a38c692821a21674c945043442ce1928a0868859c10514328433ba8c9aa43522774d925442a44ee9b24a884709dd464d521a913ba6c92a214227751935486844eea326a90d489dd36495108433ba8c1aa434d67751835486994eea306a894219d
  | _ => 0
def pathC2580 (i : Nat) := packedAt pathC2580Block (51*i) 51
def liveC2580 (i : Nat) := (0x21fc3e1f87e1f87e5bd2e4f93f0fce62f93f1ea3e1fc7a0fce787e8fa9d1f59e1f9987f87f274993ecd97bc3b8ee59f3a3a9ea3a9ea5ace3ca761fe5ba5c9f3cc3f27a7a9d87e8fe3bc5d1f0fd1f9ca3e1f87f0fc771ee728fa5fc3f0fc393fc3f328fb1f63d9667f0ee399ee3af363f27e1c9e1f8bee3b9667acfe4d1f59da763de21ff27d8e7359d2759d630fe728fa3e2f87e1fc9f3387e9bb8ef19cff0bc69de579ce7394c6e1fc3e1fb4ff0acedcde2ecbd28feb22fe8fa9e8fa387f33ccfb8ec69dec73ca9e9dcf2a7acfb1ec7b1ec7b1ec5c747d9e63d4f71d6778de3785e358de3 >>> (10*i)) &&& 0x3ff
def spanC2580 (i : Nat) := (0x6e03701b80dc06e03701b80dc06e03701b80dc06e03701b80db0ed836c1b60da0ec0b547a81d4069874c1a22d1068833c5964cb0648b241920c71628b1037e5be0dd12e436a4b50598acc1660b20d712b435a0ac0d50aa81521a905482a414c3a605286887421a105082841401a0050027c33e09f04e0e6852e39704a8a503280940488e3c51c18c1448e187082830c089fc4fc17e03e85f02f427813b85d82ea1750390dc42e206f13781b44d056803309888c025c22e016c2b605a0ad01680b405812b09580aa1521a78d3069804a1250124292049023891828c0450a2811408624112004f847a13c09e00ec27603819b08cc66223101788b4456228194009844a12501280902480240108c7c43831a10b8c544243120090044220110007843821c00a202940c4003 >>> (13*i)) &&& 0x1fff
def ruleC2580 (i : Nat) := (0x30005b0eb059b0017b0530503902503999c03999c03901798003e04448e044c8e04400a30e29c00e01c03004448e044c85c80480c8e485044c8000a00031c33031c02a03e31c00001c03e00002a03e04400001c03903e0000050004b002a58003e58003e98598003e980180044a8e68004468004418e044044c85c80044c85c80044c8000a11c01c18504404403001c044c80044c8004402a880005e1ce30a30e1ce3018504418018501701300a005e30e1ca30017e0000aa00e1ce3001700a000000e05e00e05e0001c730013d00f3000ad0009c08e01308570000ad3000a01c00ec0e30008e01300000ac00c00c0030053002a70053070053070570053070008e013705d00730500017b30b00b30b0030030073002a01773001773002a70073070073001770073070000a09c70000a00002111c03e02504401701302140e41c38060e00e40e41c380 >>> (12*i)) &&& 0xfff
def hashC2580 (i : Nat) := (0xa005c35000a5001b5210831c0470141f014260180b014480fc0f0ecad27b670ac00d701500010104250480b1df4601344bceba0002f00eb90780211c4cade740f4090785202009384030986e012690841615c010fc00010150183e9942e1101504c010042a9800a076579524d03000020010bc0001007914028f8058f4180843104c018b802864030e80002c13008000040105000004060000201009022180041113a1400001020107a03909c0279034060000140d0000200c12000260485100009 >>> (10*i)) &&& 0x3ff
def locC2580 (i : Nat) := (0xe9f4ba3d0e7f3b9bcce5f2b93c8e3f1b8bc4e1f0b83c0dfefb7bbcddeeb73b8dbedb6bb4d9ecb63b0d7ebb5bacd5eab53a8d3e9b4ba4d1e8b43a0cfe7b3b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b0380bfdfafb7cbddeaf378bbddaeb74b9dcae370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff
def cntC2580 (i : Nat) := (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2580 (i : Nat) := (0x233028f05ee958c7f006a087c05098b652fa010c1938101150625b4041228504fc006402a837500ba62af02e0a2240bac1e0020803c0ca2c1a1e4ca83f470c68194240087011a193001d1e60016368dc32ada06142cf2c2fac801878a00284059e0054910226c007813248baa01481a981801060dccc091854094601f493f982d0122f18801b8c0c091c104404b3c7950d40c240833130786321943031902360208e8009000d0044051818a8002300e34a0185800e124a0d84054002e782000d1e1c8c2578bc100d8423c5e0539024c002379850027180f148110133200106a280770156004c1908031000402bc103a00108ac02c968380606c8a7878004699c00123108002a31e783af13541a863619421838027c05c007e0885e021f393c10258c03800323c6c600808e80221134003d80430794518720d09c21a4435484c9e3f0353004e00a403883707838c0a4f0a5d157811220490300360084859c03e1aa3c2f4841913d01a50104a0e001f2067053c02b400d3c5c051a71320011968011811d04ab984a600a306cc35002b06a8000501b806e006e25b4c3fb04e00a2a2d00319e2378ca1004d1da40620a90004c2699960724792584784640074260004684a262b8401c7a4a83b4d4c00450c4da9407412252d1f035fb47879d0184214d610e485de15801c113a01e802ac25f07261288003495080a2c6b801f021c028685a40405a4090118630f3d808b00b2053d83f017b04f87974f53a19636621911843827600ae016003a2777073bc122023c05280603240019020f1008217182d80ac1890c170c3ca05380ee067a01b9e745a3801f41ba210206660155e453c1b78bc64a80130008c6dc601901b986f002e00d4d31845e0c3750490af071704ff8178c37827a130606d4450005f02aec194f120866300e983011a029238720e6b8100008c06a00bd0c7002d783c0e1950c8395804801fe43d031112bc78a002f00027a0000ed19003040e3c24241b980044a02927f8319821067800ec61e800900a4c168199bc920872182b02f019f011e7841e0e832342fc31ac01bb0600c7e812c00954394878804c70909354892c5c402e9908005e04e8c073ca942567a5002f804760950204c00801a300d40e40448019300c2091091807d0308f984336034a62d801b4637dd01780a24b000d892f064a004c403889701300089837037c300e39c8043818240cc006802231 >>> (15*i)) &&& 0x7fff
def pathC2565 (i : Nat) := (0x15193711925442b92e6a300a91d535d1260d504a9039aa299205551371510244ac1a8e282849955349c5349104b04838c891a875854718d024cac222e3128691d8019d1349134b0833a0489a47520534c9014868c0a492226a1d104092444d438b090a2692269601434c54244abc206a1a8499562485314d11490ab8284a1a47545704912350eb80e090a488a5181c1324d124af088286a12655c50150d424ca99268922200854359c4344010a82ab8829906550d464d9100429b24e1b220085464dc4644010b0a9380ca18875c07048535086a40e29920a195681c54341443a5038286928875a11050d2510e88020a1a4a21d680854341443a5008286928874207250d2510ea40e29922a195634c92451410ac2a1a04928875c5434092510ec2264a0a2a1950150d1249443a86b00028a88750d070492510eb1a0e1a28a10d6341c6351421ac6938c6a28215896348d45042a1ace21a4a0854349c4345402aec3b286928876007650d2510ec20ec9922a195765c14349443ae2b8286928875c07048545086b40e0a1a4a21d681c13251432a1038a64a2865460704c9450cabc2c0a1a4a21d765813251432ac2b0264a28655d1644c9150cab00c09922a195081854349443a3030286928875e06050d2510ebc0c0a1a4a21d784414349443ad088286928875c50150d2510eb0a02a1a4a21d100414349443af008286928875e01050d2510eb4020a1a4a21d680413251432 >>> (51*i)) &&& 0x7ffffffffffff
def liveC2565 (i : Nat) := (0x307c8f83b0f4398f4398f23d862788ee1b87e0b06e198fa1d0f43da2e198f61f8364d07a4cd324d0f58b0e87b0e87f1287b0ec3b0783e0f43f07c1e1343c1f07c0f83d0f41c0ec3b0743d0f48b0e83b0ec1b0f83e0fc1e42c3b06c390ec3b0fc1f07c0b0e43b0e83 >>> (10*i)) &&& 0x3ff
def spanC2565 (i : Nat) := (0xa219e29c19c09a19629419219209019008a38818618608418218018008007e17c17827617607227207016c26c06a16a06a06a06a06816616606606416406025c25a15a05625415215205205204e24a24a04624414404023c23823613603223202e22c12822422021e11e01a21a01621411210e20a2081080042040002 >>> (12*i)) &&& 0xfff
def ruleC2565 (i : Nat) := (0x4430e31cb00e0500e61ce00021017025013d8001701701701700e013c05c0ec1c00e18e19c01700a19ce0038004438002a01700e19c58502a485580980e05e0018e19c02ae0002a02a01728e38038538038002a38002a38038502a38038538002a01738002a38002a38028e04404438002a380380385380385380 >>> (12*i)) &&& 0xfff
def hashC2565 (i : Nat) := (0x6213038000b80482a0900206000060705c255f00000e1d00012c580fc2d0000334813160bc1ecb5010122880b23018020000081e78c1603dd40f00b04c00028023b0000c4070d4000058902c0200c005c0045581800d34008000f00300c06008040d92c01c000000204c010051800c060000a >>> (10*i)) &&& 0x3ff
def locC2565 (i : Nat) := (0x2231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff
def cntC2565 (i : Nat) := (0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2565 (i : Nat) := (0x4d182984500f1e8401f0464c52d4961ca903000c891e0db00767a79e6c082401519c0476090901219b040f01f0c9a29e0d2721d02000e80934615dea08264364a22b27e08ec092f10b0570170020251004f02122556801e5600b80381a4048429d844ec078c8af66206100c1e36783807c7a0843768300237a4089479f0776918180c614d48409fac98ba01e8609d1c9e19fc42cc52188e0ce4622003460600104741081b28319c08bcc6897eb84923a11680632040080c01004e01a8000f01c034022004d02736137a0a4680c4400810a3c4ace0824802386a405be37e163a47e123189cc14c87c25640050240a9e019304ed9a0541c238c3179f064d7a7514701fa87c912a1128000ca21c9bc311855ea4856042f0262b7c0de806a1211061323448601146198235686c93d830600802c00680640089e68012465a11d18742250082f25a846110f040413007f002005381e8814191806a098308e79e810a01da01c85a9e3c05c4055c9d2a5610b103e1140032845c69cedd8058c09427431404a085f9e5d01d2684c24af76f083c1228b3036002c6030143c44c1e0c70017962431384131a526200c8216ecce5e4e197de23194029e81d002825d1a9af139e58206005b00898551a50684685929009c8090c0fc04978a0314498d484c9f02 >>> (14*i)) &&& 0x3fff
def pathC2564 (i : Nat) := (0x34cb083b2648a865a65841d93245432d32b40e29928a196995a0714c9450ca99510a38ca81a254428851c6349410a6d4428e31a4a08510a214718d2504288510b3a64a28214ca8859c1051432a65442ce1928a0852910e774592550ec80873ba4c8aa87660109dd464d510820a44ee9b24a885981d2774d925442a48433ba8c1aa434e4219dd460d521b2010ceea306a90d350867751835486bc8433ba8c1aa434e4219dd460d521b2010ceea306a90d9210e775954304ac80873bacaa1843660109dd6544043b2021ceea326a10d98042774590510e21a433ba8c9a843648639dd6351412b2031ceeb1a8a10d9818277581150ca31a433bac6a2843485089dd6351421b22228653328a9959709410999254422ca5021ccc92a871498110e664954388ac38213328a88597608439991550e848a298ccca2a474a44341e6649543a3221a0f3324aa1d8910d079992550e9488693ccc8aa8742461506664d5248d298a833324a9a490591479993548688290084cc9aa496000145e6651532a9201a6f3324a8a51052010999450ca88270084cca284725d804ca6651432b00402653328a1956920132999450ca8c900994cca28654c8874426651432a64880213328a195325a010999450ca882d0084cca2865649380426651423a209c0213328a11d802017110e5550e8c900b90872aa8764887505309554391298a84894aa9a59210c764425550ec88863b2032aa87660101d93295510b2421a20084aaa1d9810d100425550ecb886908432aa87658324401095532b2421aae084aaa1d9210d5700a5550ecb020ab8652aa2110d2155c2195543b3021a4e084aaa1d9210d1700a5550ecb020a38652aa2110d2141c2195543b2ca1a4e21caa8959650d2710e55442a1b0c938872aa21485480850695534a8694086934aa885491e10244d2391234a208122691c89255804852344e44a649026232a03225924c5301951091298a64838ca8948950d4249c6540e11ad242a6488021225305a030484219129ba901ba20084894dd280dd100424492ac0242a30432258020121518219128c9009928c19489255104c9460ca44a2008264a3065225790413251832912a490e9920c19489255714c9060ca44a9240a648b0652253920121418219129910a80a2c194894c970005160ca44ae4a40469b021225325200145832912b92903926c08489255874850608644b0e43a648b0652254921d3245832912c990e90a0c10c89255804853608644b00402429b043225492013245832912bc90090a6c10c89255704c9160ca44ae0382648b065225491c13245832912c48e09922c19488005104092444d43002c028698a8489001545704912350c00af088286a1264005714054350932 >>> (61*i)) &&& 0x1fffffffffffffff
def liveC2564 (i : Nat) := (0x268ec1987a0f81e58e07d2326643e0748e9343cc5903e94d31a71e0694da1b5150ea345cb0d273c0d83b0d273c0e49b8356261ec1c9988eca523a4b09e91d8cb0b43b4661ca0fa334a543d8560ee0e43f81a0f464c3d89992b0c639c348e92c3cbc1392b0db0a8750e8e7418c758696760e07c0f81e89d0718ed84d1f2165388f03939ac332670b13aa2d0d83f4148e91d13b436c348f30c47a8711d98c63686d8591d6168698d91e6168658be05c2d0d31b61 >>> (11*i)) &&& 0x7ff
def spanC2564 (i : Nat) := (0xb02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02a1a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a0680a02809866098260982419024090240902408860180200802008020080200802008020080200785e0705c0685a06818160161505214810140100384e0380e0380e0380c1300c0300c0284a0280a0204802008018460180601042100400 >>> (10*i)) &&& 0x3ff
def ruleC2564 (i : Nat) := (0x260a5808c01a0310188000e002801402100570038007003804c0002e700380005c02600e >>> (13*i)) &&& 0x1fff
def hashC2564 (i : Nat) := (0x3f82f00e9d210000840900a9b27e4105c051841085c4b848031f035010400000600003008620141c0c81a1041b8442e0020b0de060980918001000070200100c04068cc03807006000003c7b44802800179ec0c9e8000020000b05de774805018000483100400049a2008580f00001c006700102c081740e000080204d02d910018f01401010005a80001c060000300000 >>> (10*i)) &&& 0x3ff
def locC2564 (i : Nat) := (0xadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff
def cntC2564 (i : Nat) := (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2564 (i : Nat) := (0x5102a864a430588752054902d83b183d3004909d2001c2a006c18c8307894300c57558002bc263c002146d0e8c2c62e6854cd2cf37150fa0116d07a11642e40d3c51c3c588079694002400070080107c41fb02700e40136ebd8046060c00e42335a1b06fe6c842b2802eb498010822e804d0424f1900001a091020c1b40140861000a78a830f085700cec0002008479b400006463b800d428200c6d2e5a53303401d583a1e69602a612803ea46c10c861a2d2c98020ebd01f411cb07e3048a1a8017901b783ec1a8c2f80420024854c01ada020c9e801001984224280002580102306032f0598121043b67e08480011e2378f8009922700690048a8b603d004b180b509580d805c38066829680a4730014f0a8f3c3c340068c0be313184500be601402bc0720202f0a9080185c084ef19c02dbc2100bc78800180001403af051e072102067401b541b80190006880c53bbc533612000d912807d0c0a2480194005a0c6c798c00d3c3d010000500373151066900686191e4400268419e010c0300ec40b18130205186c0044018bc2db4c3c144001045302ec58e018954430452017de3c034eb4a400fc03829180057004c023805b00880d4848f0023006af03c02a186580a690cc000267b0ab800a0c018209124209bc024800b002f2079806a054e4a40431808bc2f800c855ac290313783ab4c8013003800d6013c412141a42dfc4c2008a17212940c0d80080013cab783cc3ebc1c00d7c00849d802bb4442000614a15800f5793c82c182004e20150d802a1406d4195a030007cbec6c02002c9a410c96005403c80174216051800bd4420c02082862a9e7000a66400116000c10e4849c30b002ebc3c043e42680640c7e2868f01903e00d80038008202a183284f43238381427220aef3700 >>> (15*i)) &&& 0x7fff
def pathC2549 (i : Nat) := (0xae4aa2e68b08a91d901613144934492ca0b09020291a275c5081c5324d124aa0b8a029a264a1562615170994310eba2703a242828435d1181d13245432a42b4042a1a0a21d214202150d0510eb0a20a1a049288750d6141c1249443aecc00eca1a4a21d745a0744c9150cab92d0392868a8875c5081c53251432ae89c0e890a0a10d765c96250d1510eb0a1030a8692887585081854349443ac6bc0c690a8a10d615e06150d2510eb9ae89a242828435896348d1051410a86bc08690a0a10d435e04348505086a1ad021a4282843441680413251432 >>> (61*i)) &&& 0x1fffffffffffffff
def liveC2549 (i : Nat) := (0xe0330660660e81c0720e41d03b03c0701c0790700e41c81c0740e80d03807a0780d8190360680 >>> (11*i)) &&& 0x7ff
def spanC2549 (i : Nat) := (0xb0d82c14190c8241018038582c06030180c0602090080402008402000000000 >>> (9*i)) &&& 0x1ff
def ruleC2549 (i : Nat) := (0x5877038027c0e1c29614d0a38e00b8e7071c39c >>> (13*i)) &&& 0x1fff
def hashC2549 (i : Nat) := (0x9b450708932e0017020008890b1f046a04610001031411025a101e08 >>> (8*i)) &&& 0xff
def locC2549 (i : Nat) := (0xa74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 >>> (7*i)) &&& 0x7f
def cntC2549 (i : Nat) := (0xfffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2549 (i : Nat) := (0x3440a6c898360a894908403c0810b1e798830984786418c806006bc5041b03a820025a9305408d848051cca78800c0d9f5e97daad1b405189b02b0330c186483f080069802d118ab08f05b0b8063c0b0a214e0c483187211c0d000001306aa7c2c5d46023cba76922c06dad023b0140b8175d9805f1780680a75dad8c0 >>> (12*i)) &&& 0xfff
def pathC2548 (i : Nat) := (0x571a65681c53251432a2099510a38ca81a254d910a214718d2504288265442ce1928a0859a10d289dd1641543a5421a313ba0c92a874d57908677518354869ab2010ceea306a90da010d219dd464d421b50082873ba2c828876a4634867758d45086d00c690ceeb1a8a10da8181329dd6045432b342930221ccc92a876845460032999454cad38a0c20433320a90d3a115870426651510b5222b0e194cca2a6560d290d1479991540ac0ad240a653328a19581424814ca6651432a64882d0084cca2865649104e0109994508ec0a1240ae421caaa1da2225305050195534b5221a42ab8432aa8768843441570425550ed3020a1aae21caa885a910d2141c2195543b5021a20938212aa876981050d2710e55442a50d29020291a2722581424814c9460ca44a20bc8209928c194895c910520234d810912c3a9243a648b06522583524834850608644b02bc9029920c194895c9491c9104d810912b8312382648b0652200154171405344c942 >>> (71*i)) &&& 0x7fffffffffffffffff
def liveC2548 (i : Nat) := (0xe01f00f00f00823a21d01d80b80a84981b80a908c1ac0a48a44843c03c81cc0e80cc0c608e0941b40b04960a60b209a0ca0d20e20c21ca0c30d20c30740 >>> (12*i)) &&& 0xfff
def spanC2548 (i : Nat) := (0x20820820820820820820820820820820820820820820820820820820820801 >>> (6*i)) &&& 0x3f
def ruleC2548 (i : Nat) := (0x13 >>> (5*i)) &&& 0x1f
def hashC2548 (i : Nat) := (0x1112120d3e13cf0acdcb0a6c42040000170d125a1e0000b5010b0a97010e00008106020d4100 >>> (8*i)) &&& 0xff
def locC2548 (i : Nat) := (0x38f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 >>> (7*i)) &&& 0x7f
def cntC2548 (i : Nat) := (0x3ffffffffffffffffffffffffffff >>> (1*i)) &&& 0x1
def aliasC2548 (i : Nat) := (0x5901a12431285cba6c05c04e095302a1000ca0143125e2a00e842bad004c02a54c3100078850002005840004445b0089845832c568c880840aef19811de1ae9e40b3d0807ed2d012baf8020c180004eb2238f3661d006da21e0600e000a122e9411e002202e0300100080414006c0c60cb02241ec26013804ee956a2002b03c0471a480c021804879a36298686020202025019e04f0460e9070030f281238024046617b438c5af2100d0890052e87226be5803ad09c4f3081e >>> (13*i)) &&& 0x1fff
def pathC2096 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC2096 (i : Nat) := (0xf >>> (4*i)) &&& 0xf
def spanC2096 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2096 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2096 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC2096 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC2096 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC2096 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC2081 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC2081 (i : Nat) := (0xf >>> (4*i)) &&& 0xf
def spanC2081 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2081 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2081 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC2081 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC2081 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC2081 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC2066 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC2066 (i : Nat) := (0xf >>> (4*i)) &&& 0xf
def spanC2066 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2066 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2066 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC2066 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC2066 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC2066 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC2051 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC2051 (i : Nat) := (0xf >>> (4*i)) &&& 0xf
def spanC2051 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2051 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2051 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC2051 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC2051 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC2051 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC2080 (i : Nat) := (0x18ce88410 >>> (11*i)) &&& 0x7ff
def liveC2080 (i : Nat) := (0x7fff >>> (5*i)) &&& 0x1f
def spanC2080 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2080 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2080 (i : Nat) := (0x5f801c068190400100000 >>> (5*i)) &&& 0x1f
def locC2080 (i : Nat) := (0xfedcba9876543210 >>> (4*i)) &&& 0xf
def cntC2080 (i : Nat) := (0xffff >>> (1*i)) &&& 0x1
def aliasC2080 (i : Nat) := (0xf2100c520913d02902f100860307a008c >>> (9*i)) &&& 0x1ff
def pathC2065 (i : Nat) := (0xc678ce88410 >>> (11*i)) &&& 0x7ff
def liveC2065 (i : Nat) := (0xfdfff >>> (5*i)) &&& 0x1f
def spanC2065 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2065 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2065 (i : Nat) := (0x1078050800607400d0b03 >>> (5*i)) &&& 0x1f
def locC2065 (i : Nat) := (0x9ca307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def cntC2065 (i : Nat) := (0xfffff >>> (1*i)) &&& 0x1
def aliasC2065 (i : Nat) := (0xc04090c9e4000305205e420488c1e293100c03682001e >>> (9*i)) &&& 0x1ff
def pathC2050 (i : Nat) := (0x633 >>> (11*i)) &&& 0x7ff
def liveC2050 (i : Nat) := (0x17 >>> (5*i)) &&& 0x1f
def spanC2050 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2050 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2050 (i : Nat) := (0x1c0c05004000 >>> (3*i)) &&& 0x7
def locC2050 (i : Nat) := (0xe4 >>> (2*i)) &&& 0x3
def cntC2050 (i : Nat) := (0xf >>> (1*i)) &&& 0x1
def aliasC2050 (i : Nat) := (0x2000a0 >>> (6*i)) &&& 0x3f
def pathC2064 (i : Nat) := (0x6448cf2246791132c88195048ce024674911080890d1340e8802144010a0810d340429a02109010 >>> (21*i)) &&& 0x1fffff
def liveC2064 (i : Nat) := (0x1f3efbefbefbf7f7cbf79ef >>> (6*i)) &&& 0x3f
def spanC2064 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2064 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2064 (i : Nat) := (0xb3084cb1b86b00a80a607c0 >>> (6*i)) &&& 0x3f
def locC2064 (i : Nat) := (0x1cdeb38bdab49ca307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def cntC2064 (i : Nat) := (0x1fffffff >>> (1*i)) &&& 0x1
def aliasC2064 (i : Nat) := (0x4007606c31e08064da0041498960009907007908014c51800100984480a614014030e200408e45bc >>> (11*i)) &&& 0x7ff
def pathC2049 (i : Nat) := (0xc4519e448ce880214d010 >>> (21*i)) &&& 0x1fffff
def liveC2049 (i : Nat) := (0xccff27 >>> (6*i)) &&& 0x3f
def spanC2049 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2049 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2049 (i : Nat) := (0xdcba00000980007 >>> (4*i)) &&& 0xf
def locC2049 (i : Nat) := (0x1ac688 >>> (3*i)) &&& 0x7
def cntC2049 (i : Nat) := (0x7f >>> (1*i)) &&& 0x1
def aliasC2049 (i : Nat) := (0x40100000161b019e >>> (9*i)) &&& 0x1ff
def pathC2048 (i : Nat) := (0x80b22065015344869a80890c5444d038a0892054852344e99208195104d010a489a0214c1240c2992281953509010 >>> (31*i)) &&& 0x7fffffff
def liveC2048 (i : Nat) := (0x9d3a3c7b5c71f4c78f0c7 >>> (7*i)) &&& 0x7f
def spanC2048 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2048 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2048 (i : Nat) := (0xa00712218380001f24079d140 >>> (6*i)) &&& 0x3f
def locC2048 (i : Nat) := (0xbdab49ca307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def cntC2048 (i : Nat) := (0xffffff >>> (1*i)) &&& 0x1
def aliasC2048 (i : Nat) := (0x66035101400300e188439a518002c010e900b5090548178801c04028116615e382 >>> (11*i)) &&& 0x7ff
def pathC2033 (i : Nat) := (0x53245032 >>> (31*i)) &&& 0x7fffffff
def liveC2033 (i : Nat) := (0x61 >>> (7*i)) &&& 0x7f
def spanC2033 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2033 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2033 (i : Nat) := (0x3000200 >>> (2*i)) &&& 0x3
def locC2033 (i : Nat) := (0x2 >>> (1*i)) &&& 0x1
def cntC2033 (i : Nat) := (0x3 >>> (1*i)) &&& 0x1
def aliasC2033 (i : Nat) := (0x2a3c >>> (7*i)) &&& 0x7f
def pathC2032 (i : Nat) := (0x5161490348e2324291a27485044d021 >>> (41*i)) &&& 0x1ffffffffff
def liveC2032 (i : Nat) := (0x91a1e0 >>> (8*i)) &&& 0xff
def spanC2032 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC2032 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC2032 (i : Nat) := (0xf00000e0dcba9800 >>> (4*i)) &&& 0xf
def locC2032 (i : Nat) := (0xfac688 >>> (3*i)) &&& 0x7
def cntC2032 (i : Nat) := (0xff >>> (1*i)) &&& 0x1
def aliasC2032 (i : Nat) := (0x430c19d3c462f10124 >>> (9*i)) &&& 0x1ff
def pathC1548 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC1548 (i : Nat) := (0x7 >>> (3*i)) &&& 0x7
def spanC1548 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC1548 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC1548 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC1548 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC1548 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC1548 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC1533 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC1533 (i : Nat) := (0x7 >>> (3*i)) &&& 0x7
def spanC1533 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC1533 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC1533 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC1533 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC1533 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC1533 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC1000 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def liveC1000 (i : Nat) := (0x3 >>> (2*i)) &&& 0x3
def spanC1000 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def ruleC1000 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def hashC1000 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def locC1000 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def cntC1000 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def aliasC1000 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pathC : Nat → Nat → Nat
  | 2645 => pathC2645
  | 2644 => pathC2644
  | 2629 => pathC2629
  | 2628 => pathC2628
  | 2613 => pathC2613
  | 2612 => pathC2612
  | 2597 => pathC2597
  | 2596 => pathC2596
  | 2581 => pathC2581
  | 2580 => pathC2580
  | 2565 => pathC2565
  | 2564 => pathC2564
  | 2549 => pathC2549
  | 2548 => pathC2548
  | 2096 => pathC2096
  | 2081 => pathC2081
  | 2066 => pathC2066
  | 2051 => pathC2051
  | 2080 => pathC2080
  | 2065 => pathC2065
  | 2050 => pathC2050
  | 2064 => pathC2064
  | 2049 => pathC2049
  | 2048 => pathC2048
  | 2033 => pathC2033
  | 2032 => pathC2032
  | 1548 => pathC1548
  | 1533 => pathC1533
  | 1000 => pathC1000
  | _ => fun _ => 0
def liveC : Nat → Nat → Nat
  | 2645 => liveC2645
  | 2644 => liveC2644
  | 2629 => liveC2629
  | 2628 => liveC2628
  | 2613 => liveC2613
  | 2612 => liveC2612
  | 2597 => liveC2597
  | 2596 => liveC2596
  | 2581 => liveC2581
  | 2580 => liveC2580
  | 2565 => liveC2565
  | 2564 => liveC2564
  | 2549 => liveC2549
  | 2548 => liveC2548
  | 2096 => liveC2096
  | 2081 => liveC2081
  | 2066 => liveC2066
  | 2051 => liveC2051
  | 2080 => liveC2080
  | 2065 => liveC2065
  | 2050 => liveC2050
  | 2064 => liveC2064
  | 2049 => liveC2049
  | 2048 => liveC2048
  | 2033 => liveC2033
  | 2032 => liveC2032
  | 1548 => liveC1548
  | 1533 => liveC1533
  | 1000 => liveC1000
  | _ => fun _ => 0
def spanC : Nat → Nat → Nat
  | 2645 => spanC2645
  | 2644 => spanC2644
  | 2629 => spanC2629
  | 2628 => spanC2628
  | 2613 => spanC2613
  | 2612 => spanC2612
  | 2597 => spanC2597
  | 2596 => spanC2596
  | 2581 => spanC2581
  | 2580 => spanC2580
  | 2565 => spanC2565
  | 2564 => spanC2564
  | 2549 => spanC2549
  | 2548 => spanC2548
  | 2096 => spanC2096
  | 2081 => spanC2081
  | 2066 => spanC2066
  | 2051 => spanC2051
  | 2080 => spanC2080
  | 2065 => spanC2065
  | 2050 => spanC2050
  | 2064 => spanC2064
  | 2049 => spanC2049
  | 2048 => spanC2048
  | 2033 => spanC2033
  | 2032 => spanC2032
  | 1548 => spanC1548
  | 1533 => spanC1533
  | 1000 => spanC1000
  | _ => fun _ => 0
def ruleC : Nat → Nat → Nat
  | 2645 => ruleC2645
  | 2644 => ruleC2644
  | 2629 => ruleC2629
  | 2628 => ruleC2628
  | 2613 => ruleC2613
  | 2612 => ruleC2612
  | 2597 => ruleC2597
  | 2596 => ruleC2596
  | 2581 => ruleC2581
  | 2580 => ruleC2580
  | 2565 => ruleC2565
  | 2564 => ruleC2564
  | 2549 => ruleC2549
  | 2548 => ruleC2548
  | 2096 => ruleC2096
  | 2081 => ruleC2081
  | 2066 => ruleC2066
  | 2051 => ruleC2051
  | 2080 => ruleC2080
  | 2065 => ruleC2065
  | 2050 => ruleC2050
  | 2064 => ruleC2064
  | 2049 => ruleC2049
  | 2048 => ruleC2048
  | 2033 => ruleC2033
  | 2032 => ruleC2032
  | 1548 => ruleC1548
  | 1533 => ruleC1533
  | 1000 => ruleC1000
  | _ => fun _ => 0
def hashC : Nat → Nat → Nat
  | 2645 => hashC2645
  | 2644 => hashC2644
  | 2629 => hashC2629
  | 2628 => hashC2628
  | 2613 => hashC2613
  | 2612 => hashC2612
  | 2597 => hashC2597
  | 2596 => hashC2596
  | 2581 => hashC2581
  | 2580 => hashC2580
  | 2565 => hashC2565
  | 2564 => hashC2564
  | 2549 => hashC2549
  | 2548 => hashC2548
  | 2096 => hashC2096
  | 2081 => hashC2081
  | 2066 => hashC2066
  | 2051 => hashC2051
  | 2080 => hashC2080
  | 2065 => hashC2065
  | 2050 => hashC2050
  | 2064 => hashC2064
  | 2049 => hashC2049
  | 2048 => hashC2048
  | 2033 => hashC2033
  | 2032 => hashC2032
  | 1548 => hashC1548
  | 1533 => hashC1533
  | 1000 => hashC1000
  | _ => fun _ => 0
def locC : Nat → Nat → Nat
  | 2645 => locC2645
  | 2644 => locC2644
  | 2629 => locC2629
  | 2628 => locC2628
  | 2613 => locC2613
  | 2612 => locC2612
  | 2597 => locC2597
  | 2596 => locC2596
  | 2581 => locC2581
  | 2580 => locC2580
  | 2565 => locC2565
  | 2564 => locC2564
  | 2549 => locC2549
  | 2548 => locC2548
  | 2096 => locC2096
  | 2081 => locC2081
  | 2066 => locC2066
  | 2051 => locC2051
  | 2080 => locC2080
  | 2065 => locC2065
  | 2050 => locC2050
  | 2064 => locC2064
  | 2049 => locC2049
  | 2048 => locC2048
  | 2033 => locC2033
  | 2032 => locC2032
  | 1548 => locC1548
  | 1533 => locC1533
  | 1000 => locC1000
  | _ => fun _ => 0
def cntC : Nat → Nat → Nat
  | 2645 => cntC2645
  | 2644 => cntC2644
  | 2629 => cntC2629
  | 2628 => cntC2628
  | 2613 => cntC2613
  | 2612 => cntC2612
  | 2597 => cntC2597
  | 2596 => cntC2596
  | 2581 => cntC2581
  | 2580 => cntC2580
  | 2565 => cntC2565
  | 2564 => cntC2564
  | 2549 => cntC2549
  | 2548 => cntC2548
  | 2096 => cntC2096
  | 2081 => cntC2081
  | 2066 => cntC2066
  | 2051 => cntC2051
  | 2080 => cntC2080
  | 2065 => cntC2065
  | 2050 => cntC2050
  | 2064 => cntC2064
  | 2049 => cntC2049
  | 2048 => cntC2048
  | 2033 => cntC2033
  | 2032 => cntC2032
  | 1548 => cntC1548
  | 1533 => cntC1533
  | 1000 => cntC1000
  | _ => fun _ => 0
def aliasC : Nat → Nat → Nat
  | 2645 => aliasC2645
  | 2644 => aliasC2644
  | 2629 => aliasC2629
  | 2628 => aliasC2628
  | 2613 => aliasC2613
  | 2612 => aliasC2612
  | 2597 => aliasC2597
  | 2596 => aliasC2596
  | 2581 => aliasC2581
  | 2580 => aliasC2580
  | 2565 => aliasC2565
  | 2564 => aliasC2564
  | 2549 => aliasC2549
  | 2548 => aliasC2548
  | 2096 => aliasC2096
  | 2081 => aliasC2081
  | 2066 => aliasC2066
  | 2051 => aliasC2051
  | 2080 => aliasC2080
  | 2065 => aliasC2065
  | 2050 => aliasC2050
  | 2064 => aliasC2064
  | 2049 => aliasC2049
  | 2048 => aliasC2048
  | 2033 => aliasC2033
  | 2032 => aliasC2032
  | 1548 => aliasC1548
  | 1533 => aliasC1533
  | 1000 => aliasC1000
  | _ => fun _ => 0
def sizeC : Nat → Nat
  | 2645 => 1
  | 2644 => 2
  | 2629 => 2
  | 2628 => 5
  | 2613 => 11
  | 2612 => 33
  | 2597 => 49
  | 2596 => 120
  | 2581 => 95
  | 2580 => 183
  | 2565 => 83
  | 2564 => 130
  | 2549 => 28
  | 2548 => 41
  | 2096 => 1
  | 2081 => 1
  | 2066 => 1
  | 2051 => 1
  | 2080 => 3
  | 2065 => 4
  | 2050 => 1
  | 2064 => 15
  | 2049 => 4
  | 2048 => 12
  | 2033 => 1
  | 2032 => 3
  | 1548 => 1
  | 1533 => 1
  | 1000 => 1
  | _ => 0
def keyCountC : Nat → Nat
  | 2645 => 0
  | 2644 => 5
  | 2629 => 20
  | 2628 => 28
  | 2613 => 40
  | 2612 => 106
  | 2597 => 180
  | 2596 => 344
  | 2581 => 315
  | 2580 => 468
  | 2565 => 274
  | 2564 => 348
  | 2549 => 84
  | 2548 => 114
  | 2096 => 0
  | 2081 => 0
  | 2066 => 0
  | 2051 => 0
  | 2080 => 16
  | 2065 => 20
  | 2050 => 4
  | 2064 => 29
  | 2049 => 7
  | 2048 => 24
  | 2033 => 2
  | 2032 => 8
  | 1548 => 0
  | 1533 => 0
  | 1000 => 0
  | _ => 0
def nbC : Nat → Nat
  | 2645 => 1
  | 2644 => 17
  | 2629 => 17
  | 2628 => 17
  | 2613 => 17
  | 2612 => 36
  | 2597 => 60
  | 2596 => 115
  | 2581 => 105
  | 2580 => 156
  | 2565 => 92
  | 2564 => 116
  | 2549 => 28
  | 2548 => 38
  | 2096 => 1
  | 2081 => 1
  | 2066 => 1
  | 2051 => 1
  | 2080 => 17
  | 2065 => 17
  | 2050 => 17
  | 2064 => 17
  | 2049 => 17
  | 2048 => 17
  | 2033 => 17
  | 2032 => 17
  | 1548 => 1
  | 1533 => 1
  | 1000 => 1
  | _ => 0
def saltC : Nat → Nat
  | 2645 => 1
  | 2644 => 1
  | 2629 => 15
  | 2628 => 2
  | 2613 => 26
  | 2612 => 3
  | 2597 => 120
  | 2596 => 7
  | 2581 => 3
  | 2580 => 27
  | 2565 => 38
  | 2564 => 1
  | 2549 => 306
  | 2548 => 63
  | 2096 => 1
  | 2081 => 1
  | 2066 => 1
  | 2051 => 1
  | 2080 => 1
  | 2065 => 4
  | 2050 => 4
  | 2064 => 2
  | 2049 => 2
  | 2048 => 10
  | 2033 => 1
  | 2032 => 1
  | 1548 => 1
  | 1533 => 1
  | 1000 => 1
  | _ => 0
end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568.Charge
def sliceNat (x i n : Nat) := (x >>> i) &&& ((1 <<< n)-1)

def evalBank (pw : Nat) : Nat → Nat → List Decor → List Decor
  | 0, _, xs => xs
  | d+1, ops, xs =>
    let a := xs.getD (sliceNat ops 0 pw) defaultDecor
    let b := xs.getD (sliceNat ops pw pw) defaultDecor
    let z := codeDecor (sliceNat ops (2*pw) 2) a b
    evalBank pw d (ops >>> (2*pw+2)) (xs++[z])

def neededOps (pw : Nat) (xs : List Decor) : Nat → Nat → Nat → List Choice
  | 0, _, _ => []
  | d+1, ops, pay =>
    let more := neededOps pw xs d (ops >>> (2*pw+2)) (pay >>> 1)
    if pay &&& 1 = 0 then more else
      (sliceNat ops (2*pw) 2,(xs.getD (sliceNat ops 0 pw) defaultDecor).1,
        (xs.getD (sliceNat ops pw pw) defaultDecor).1) :: more


def group (n b h : Nat) := if b≤9 ∧ h≤3 then 500*n+16*b+h else 0
def maskAt (n : Nat) := (1 <<< n)-1
def startSet (n : Nat) := vars (maskAt n)
def goalAt (n : Nat) := graphGoal (maskAt n)
def encodedRoot (n : Nat) := rawDecor (maskAt n) (pointsPos n) (pointsNeg n)
def depthAt (id i : Nat) := (pathC id i).log2/10
def wiresAt (n id i : Nat) := evalBank 4 (depthAt id i) (pathC id i) (encodedRoot n)
def useAt (n id i : Nat) := selectLive (liveC id i) (wiresAt n id i)
def wordsAt (n id i : Nat) := (useAt n id i).map Prod.fst
def rotationAt (n j : Nat) : List Nat :=
  let s := rotations5[j]?.getD []
  if s.all (fun e => decide (e/16 < n ∧ e % 16 < n)) then s else []
def groupLookup (id tag : Nat) :=
  let count := keyCountC id
  let d := hashC id ((tag*saltC id % 4294967291) % nbC id)
  if d≥count then d-count else (tag+d) % count
def candidateAt (n id c : Nat) :=
  let i := c/128
  if i<sizeC id then some ((wordsAt n id i).map (movedWord ((rotationAt n (c % 128)).map swapRows).reverse)) else none
def candidates (n b h tag : Nat) : List (List Sig) :=
  let id := group n b h
  let g := groupLookup id tag
  if keyCountC id=0 then [] else
    (List.range (cntC id g)).filterMap (fun j => candidateAt n id (aliasC id (locC id g+j)))
def poolsAt (n id i : Nat) (bank : List Decor) : List BoundPool :=
  if n != 5 then [] else
  let s := spanC id i
  (List.range (s &&& 31)).filterMap fun j =>
    let atom := ruleC id ((s >>> 5)+j)
    cutColumns[atom &&& 127]?.bind (fun ci => materialize (startSet n)
      (neededOps 4 bank (depthAt id i) (pathC id i) (atom >>> 7)) (subcube ci.1 ci.2.1) ci.2.2.2.2)
def nextCandidates (n b h bb hh tag : Nat) :=
  if bb+hh < b+h then candidates n bb hh tag else []
def nodeGood (n b h i : Nat) : Bool :=
  let id := group n b h
  let bank := wiresAt n id i
  let ws := selectLive (liveC id i) bank
  let raw := ws.map Prod.fst
  decide raw.Nodup && !(raw.contains (goalAt n)) &&
    testAllF (b,h,ws.length,ws,preCov ws,poolsAt n id i bank,nextCandidates n b h) ws
theorem bankFaith (pw n ops : Nat) (xs : List Decor) {r s}
    (h : ∀ v ∈ xs, faithful r s v) : ∀ v ∈ evalBank pw n ops xs, faithful r s v := by
  induction n generalizing ops xs with
  | zero => exact h
  | succ n ih =>
    apply ih
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get h _)
      · exact faithful_bin _ (faithful_get h _) (faithful_get h _)

theorem rotateCharged {T n f} {ws : List Sig} (hi : ChargedImpossible T n f ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : ChargedImpossible T n f (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  intro k t hk ht h
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run


theorem wordFaith (n id i : Nat) : ∀ v ∈ useAt n id i, faithful (asRow (pointsPos n)) (asRow (pointsNeg n)) v :=
  fun v hv => bankFaith _ _ _ _ (raw_faithful _ _ _) _ ((selectLive_sub _ _).subset hv)

def ValidColumnsAt (n : Nat) := n=5 → ∀ ci ∈ cutColumns.toList,
  Slice (startSet n) (goalAt n) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem poolsAt_good (n id i : Nat) (bank : List Decor) (col : ValidColumnsAt n) :
    ∀ p ∈ poolsAt n id i bank, ValidPool (startSet n) (goalAt n) p := by
  intro x hx
  unfold poolsAt at hx
  split at hx
  · simp at hx
  next hn =>
    have eq : n=5 := by simpa using hn
    obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hx
    obtain ⟨ci,hc,hm⟩ := Option.bind_eq_some_iff.mp hj
    exact materialize_sound (col eq ci (by simpa using Array.mem_of_getElem? hc)) hm

def ValidRotations (n : Nat) := ∀ j < 128, autoOK (goalAt n) ((rotationAt n j).map swapRows) = true
theorem routeAt_good {n b h : Nat}
    (rot : ValidRotations n)
    (earlier : ∀ i < sizeC (group n b h), ChargedImpossible (goalAt n) b h (wordsAt n (group n b h) i).toFinset) :
    ∀ tag xs, xs ∈ candidates n b h tag → ChargedImpossible (goalAt n) b h xs.toFinset := by
  intro tag xs hm
  simp only [candidates] at hm
  split at hm
  · simp at hm
  · obtain ⟨j,_,hx⟩ := List.mem_filterMap.mp hm
    simp only [candidateAt] at hx
    split at hx
    next valid =>
      obtain rfl := Option.some.inj hx
      exact rotateCharged (earlier _ valid) _ (rot _ (Nat.mod_lt _ (by decide)))
    next => simp at hx

def CoveredAt (n : Nat) := properPairs (goalAt n) (asRow (pointsPos n)) (asRow (pointsNeg n))
def CheckedAt (n : Nat) := ∀ b h i, i<sizeC (group n b h) → nodeGood n b h i=true

theorem nodeStep {n b h i : Nat} (cov : CoveredAt n) (col : ValidColumnsAt n)
    (rot : ValidRotations n) (ok : nodeGood n b h i=true)
    (prior : ∀ (bb hh : Nat), bb+hh < b+h → ∀ j < sizeC (group n bb hh),
      ChargedImpossible (goalAt n) bb hh (wordsAt n (group n bb hh) j).toFinset) :
    ChargedImpossible (goalAt n) b h (wordsAt n (group n b h) i).toFinset := by
  simp only [nodeGood,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_true_eq,decide_eq_false_iff_not] at ok
  apply nodeFew (links := nextCandidates n b h) (cap:=b) (fuel:=h) cov (wordFaith _ _ _) ok.1.1 ok.1.2 (poolsAt_good _ _ _ _ col)
  · intro bb hh tag xs hx
    by_cases dec : bb+hh < b+h
    · exact routeAt_good rot (prior _ _ dec) tag xs (by simpa [nextCandidates,dec] using hx)
    · simp [nextCandidates,dec] at hx
  · exact ok.2

theorem checkedBelow (n : Nat) (cov : CoveredAt n) (col : ValidColumnsAt n)
    (rot : ValidRotations n) (checked : CheckedAt n) (lim : Nat) :
    ∀ b h, b+h=lim → ∀ i < sizeC (group n b h),
      ChargedImpossible (goalAt n) b h (wordsAt n (group n b h) i).toFinset := by
  induction lim using Nat.strong_induction_on with
  | ind lim ih =>
    intro b h eq i hi
    apply nodeStep cov col rot (checked _ _ _ hi)
    intro bb hh lt
    exact ih (bb+hh) (by omega) bb hh rfl

end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568.Charge
def span5 (n b h : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | m+1, o => nodeGood n b h o && span5 n b h m (o+1)
theorem range5 {n b h m o i : Nat} (good : span5 n b h m o = true) (lo : o ≤ i) (hi : i < o + m) : nodeGood n b h i = true := by
  induction m generalizing o with
  | zero => omega
  | succ m ih =>
    simp only [span5,Bool.and_eq_true] at good
    by_cases eq : i=o
    · simpa only [eq] using good.1
    · exact ih good.2 (by omega) (by omega)
theorem join5 {n b h a c o} (left : span5 n b h a o=true) (right : span5 n b h c (o+a)=true) :
    span5 n b h (a+c) o=true := by
  induction a generalizing o with
  | zero => simpa using right
  | succ a ih =>
    simp only [span5,Bool.and_eq_true] at left
    rw [Nat.succ_add,span5,Bool.and_eq_true]
    exact ⟨left.1,ih left.2 (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using right)⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf1000q0 : span5 2 0 0 1 0=true := by decide +kernel
theorem block1000 : span5 2 0 0 1 0=true := leaf1000q0
theorem checks2 : CheckedAt 2 := by
  intro b h i hi
  by_cases lim : b≤9 ∧ h≤3
  · obtain ⟨hb,hh⟩ := lim
    interval_cases b <;> interval_cases h
    · exact range5 block1000 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
  · simp [group,lim,sizeC] at hi
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf1533q0 : span5 3 2 1 1 0=true := by decide +kernel
theorem block1533 : span5 3 2 1 1 0=true := leaf1533q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf1548q0 : span5 3 3 0 1 0=true := by decide +kernel
theorem block1548 : span5 3 3 0 1 0=true := leaf1548q0
theorem checks3 : CheckedAt 3 := by
  intro b h i hi
  by_cases lim : b≤9 ∧ h≤3
  · obtain ⟨hb,hh⟩ := lim
    interval_cases b <;> interval_cases h
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block1533 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block1548 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
  · simp [group,lim,sizeC] at hi
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2032q0 : span5 4 2 0 3 0=true := by decide +kernel
theorem block2032 : span5 4 2 0 3 0=true := leaf2032q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2033q0 : span5 4 2 1 1 0=true := by decide +kernel
theorem block2033 : span5 4 2 1 1 0=true := leaf2033q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2048q0 : span5 4 3 0 12 0=true := by decide +kernel
theorem block2048 : span5 4 3 0 12 0=true := leaf2048q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2049q0 : span5 4 3 1 4 0=true := by decide +kernel
theorem block2049 : span5 4 3 1 4 0=true := leaf2049q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2050q0 : span5 4 3 2 1 0=true := by decide +kernel
theorem block2050 : span5 4 3 2 1 0=true := leaf2050q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2051q0 : span5 4 3 3 1 0=true := by decide +kernel
theorem block2051 : span5 4 3 3 1 0=true := leaf2051q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2064q0 : span5 4 4 0 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2064q12 : span5 4 4 0 3 12=true := by decide +kernel
theorem block2064 : span5 4 4 0 15 0=true := (@join5 4 4 0 12 3 0 leaf2064q0 leaf2064q12)
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2065q0 : span5 4 4 1 4 0=true := by decide +kernel
theorem block2065 : span5 4 4 1 4 0=true := leaf2065q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2066q0 : span5 4 4 2 1 0=true := by decide +kernel
theorem block2066 : span5 4 4 2 1 0=true := leaf2066q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2080q0 : span5 4 5 0 3 0=true := by decide +kernel
theorem block2080 : span5 4 5 0 3 0=true := leaf2080q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2081q0 : span5 4 5 1 1 0=true := by decide +kernel
theorem block2081 : span5 4 5 1 1 0=true := leaf2081q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2096q0 : span5 4 6 0 1 0=true := by decide +kernel
theorem block2096 : span5 4 6 0 1 0=true := leaf2096q0
theorem checks4 : CheckedAt 4 := by
  intro b h i hi
  by_cases lim : b≤9 ∧ h≤3
  · obtain ⟨hb,hh⟩ := lim
    interval_cases b <;> interval_cases h
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2032 (Nat.zero_le _) (show i<3 from hi)
    · exact range5 block2033 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2048 (Nat.zero_le _) (show i<12 from hi)
    · exact range5 block2049 (Nat.zero_le _) (show i<4 from hi)
    · exact range5 block2050 (Nat.zero_le _) (show i<1 from hi)
    · exact range5 block2051 (Nat.zero_le _) (show i<1 from hi)
    · exact range5 block2064 (Nat.zero_le _) (show i<15 from hi)
    · exact range5 block2065 (Nat.zero_le _) (show i<4 from hi)
    · exact range5 block2066 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2080 (Nat.zero_le _) (show i<3 from hi)
    · exact range5 block2081 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2096 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
  · simp [group,lim,sizeC] at hi
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2548q0 : span5 5 3 0 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2548q12 : span5 5 3 0 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2548q24 : span5 5 3 0 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2548q36 : span5 5 3 0 5 36=true := by decide +kernel
theorem block2548 : span5 5 3 0 41 0=true := (@join5 5 3 0 24 17 0 (@join5 5 3 0 12 12 0 leaf2548q0 leaf2548q12) (@join5 5 3 0 12 5 24 leaf2548q24 leaf2548q36))
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2549q0 : span5 5 3 1 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2549q12 : span5 5 3 1 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2549q24 : span5 5 3 1 4 24=true := by decide +kernel
theorem block2549 : span5 5 3 1 28 0=true := (@join5 5 3 1 24 4 0 (@join5 5 3 1 12 12 0 leaf2549q0 leaf2549q12) leaf2549q24)
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q0 : span5 5 4 0 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q12 : span5 5 4 0 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q24 : span5 5 4 0 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q36 : span5 5 4 0 12 36=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q48 : span5 5 4 0 12 48=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q60 : span5 5 4 0 12 60=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q72 : span5 5 4 0 12 72=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q84 : span5 5 4 0 12 84=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q96 : span5 5 4 0 12 96=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q108 : span5 5 4 0 12 108=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2564q120 : span5 5 4 0 10 120=true := by decide +kernel
theorem block2564 : span5 5 4 0 130 0=true := (@join5 5 4 0 96 34 0 (@join5 5 4 0 48 48 0 (@join5 5 4 0 24 24 0 (@join5 5 4 0 12 12 0 leaf2564q0 leaf2564q12) (@join5 5 4 0 12 12 24 leaf2564q24 leaf2564q36)) (@join5 5 4 0 24 24 48 (@join5 5 4 0 12 12 48 leaf2564q48 leaf2564q60) (@join5 5 4 0 12 12 72 leaf2564q72 leaf2564q84))) (@join5 5 4 0 24 10 96 (@join5 5 4 0 12 12 96 leaf2564q96 leaf2564q108) leaf2564q120))
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q0 : span5 5 4 1 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q12 : span5 5 4 1 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q24 : span5 5 4 1 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q36 : span5 5 4 1 12 36=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q48 : span5 5 4 1 12 48=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q60 : span5 5 4 1 12 60=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2565q72 : span5 5 4 1 11 72=true := by decide +kernel
theorem block2565 : span5 5 4 1 83 0=true := (@join5 5 4 1 48 35 0 (@join5 5 4 1 24 24 0 (@join5 5 4 1 12 12 0 leaf2565q0 leaf2565q12) (@join5 5 4 1 12 12 24 leaf2565q24 leaf2565q36)) (@join5 5 4 1 24 11 48 (@join5 5 4 1 12 12 48 leaf2565q48 leaf2565q60) leaf2565q72))
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q0 : span5 5 5 0 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q12 : span5 5 5 0 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q24 : span5 5 5 0 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q36 : span5 5 5 0 12 36=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q48 : span5 5 5 0 12 48=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q60 : span5 5 5 0 12 60=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q72 : span5 5 5 0 12 72=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q84 : span5 5 5 0 12 84=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q96 : span5 5 5 0 12 96=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q108 : span5 5 5 0 12 108=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q120 : span5 5 5 0 12 120=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q132 : span5 5 5 0 12 132=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q144 : span5 5 5 0 12 144=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q156 : span5 5 5 0 12 156=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q168 : span5 5 5 0 12 168=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2580q180 : span5 5 5 0 3 180=true := by decide +kernel
theorem block2580 : span5 5 5 0 183 0=true := (@join5 5 5 0 96 87 0 (@join5 5 5 0 48 48 0 (@join5 5 5 0 24 24 0 (@join5 5 5 0 12 12 0 leaf2580q0 leaf2580q12) (@join5 5 5 0 12 12 24 leaf2580q24 leaf2580q36)) (@join5 5 5 0 24 24 48 (@join5 5 5 0 12 12 48 leaf2580q48 leaf2580q60) (@join5 5 5 0 12 12 72 leaf2580q72 leaf2580q84))) (@join5 5 5 0 48 39 96 (@join5 5 5 0 24 24 96 (@join5 5 5 0 12 12 96 leaf2580q96 leaf2580q108) (@join5 5 5 0 12 12 120 leaf2580q120 leaf2580q132)) (@join5 5 5 0 24 15 144 (@join5 5 5 0 12 12 144 leaf2580q144 leaf2580q156) (@join5 5 5 0 12 3 168 leaf2580q168 leaf2580q180))))
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q0 : span5 5 5 1 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q12 : span5 5 5 1 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q24 : span5 5 5 1 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q36 : span5 5 5 1 12 36=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q48 : span5 5 5 1 12 48=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q60 : span5 5 5 1 12 60=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q72 : span5 5 5 1 12 72=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2581q84 : span5 5 5 1 11 84=true := by decide +kernel
theorem block2581 : span5 5 5 1 95 0=true := (@join5 5 5 1 48 47 0 (@join5 5 5 1 24 24 0 (@join5 5 5 1 12 12 0 leaf2581q0 leaf2581q12) (@join5 5 5 1 12 12 24 leaf2581q24 leaf2581q36)) (@join5 5 5 1 24 23 48 (@join5 5 5 1 12 12 48 leaf2581q48 leaf2581q60) (@join5 5 5 1 12 11 72 leaf2581q72 leaf2581q84)))
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q0 : span5 5 6 0 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q12 : span5 5 6 0 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q24 : span5 5 6 0 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q36 : span5 5 6 0 12 36=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q48 : span5 5 6 0 12 48=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q60 : span5 5 6 0 12 60=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q72 : span5 5 6 0 12 72=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q84 : span5 5 6 0 12 84=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q96 : span5 5 6 0 12 96=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2596q108 : span5 5 6 0 12 108=true := by decide +kernel
theorem block2596 : span5 5 6 0 120 0=true := (@join5 5 6 0 96 24 0 (@join5 5 6 0 48 48 0 (@join5 5 6 0 24 24 0 (@join5 5 6 0 12 12 0 leaf2596q0 leaf2596q12) (@join5 5 6 0 12 12 24 leaf2596q24 leaf2596q36)) (@join5 5 6 0 24 24 48 (@join5 5 6 0 12 12 48 leaf2596q48 leaf2596q60) (@join5 5 6 0 12 12 72 leaf2596q72 leaf2596q84))) (@join5 5 6 0 12 12 96 leaf2596q96 leaf2596q108))
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2597q0 : span5 5 6 1 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2597q12 : span5 5 6 1 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2597q24 : span5 5 6 1 12 24=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2597q36 : span5 5 6 1 12 36=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2597q48 : span5 5 6 1 1 48=true := by decide +kernel
theorem block2597 : span5 5 6 1 49 0=true := (@join5 5 6 1 48 1 0 (@join5 5 6 1 24 24 0 (@join5 5 6 1 12 12 0 leaf2597q0 leaf2597q12) (@join5 5 6 1 12 12 24 leaf2597q24 leaf2597q36)) leaf2597q48)
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2612q0 : span5 5 7 0 12 0=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2612q12 : span5 5 7 0 12 12=true := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2612q24 : span5 5 7 0 9 24=true := by decide +kernel
theorem block2612 : span5 5 7 0 33 0=true := (@join5 5 7 0 24 9 0 (@join5 5 7 0 12 12 0 leaf2612q0 leaf2612q12) leaf2612q24)
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2613q0 : span5 5 7 1 11 0=true := by decide +kernel
theorem block2613 : span5 5 7 1 11 0=true := leaf2613q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2628q0 : span5 5 8 0 5 0=true := by decide +kernel
theorem block2628 : span5 5 8 0 5 0=true := leaf2628q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2629q0 : span5 5 8 1 2 0=true := by decide +kernel
theorem block2629 : span5 5 8 1 2 0=true := leaf2629q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2644q0 : span5 5 9 0 2 0=true := by decide +kernel
theorem block2644 : span5 5 9 0 2 0=true := leaf2644q0
set_option maxRecDepth 14000 in
set_option maxHeartbeats 10000000 in
theorem leaf2645q0 : span5 5 9 1 1 0=true := by decide +kernel
theorem block2645 : span5 5 9 1 1 0=true := leaf2645q0
theorem checks5 : CheckedAt 5 := by
  intro b h i hi
  by_cases lim : b≤9 ∧ h≤3
  · obtain ⟨hb,hh⟩ := lim
    interval_cases b <;> interval_cases h
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2548 (Nat.zero_le _) (show i<41 from hi)
    · exact range5 block2549 (Nat.zero_le _) (show i<28 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2564 (Nat.zero_le _) (show i<130 from hi)
    · exact range5 block2565 (Nat.zero_le _) (show i<83 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2580 (Nat.zero_le _) (show i<183 from hi)
    · exact range5 block2581 (Nat.zero_le _) (show i<95 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2596 (Nat.zero_le _) (show i<120 from hi)
    · exact range5 block2597 (Nat.zero_le _) (show i<49 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2612 (Nat.zero_le _) (show i<33 from hi)
    · exact range5 block2613 (Nat.zero_le _) (show i<11 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2628 (Nat.zero_le _) (show i<5 from hi)
    · exact range5 block2629 (Nat.zero_le _) (show i<2 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact range5 block2644 (Nat.zero_le _) (show i<2 from hi)
    · exact range5 block2645 (Nat.zero_le _) (show i<1 from hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
    · exact False.elim ((Nat.not_lt_zero _) hi)
  · simp [group,lim,sizeC] at hi
end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568.Charge
set_option maxRecDepth 12000 in
theorem coverage2 : CoveredAt 2 := by
  change properPairs (chartGoal 3) (asRow (pointsPos 2)) (asRow (pointsNeg 2))
  apply chart_pairs <;> decide +kernel
set_option maxRecDepth 14000 in
theorem rots2 : ValidRotations 2 := by
  have check : ∀ j : Fin 128, autoOK (goalAt 2) ((rotationAt 2 j).map swapRows)=true := by decide +kernel
  intro j hj
  exact check ⟨j,hj⟩
set_option maxRecDepth 12000 in
theorem coverage3 : CoveredAt 3 := by
  change properPairs (chartGoal 7) (asRow (pointsPos 3)) (asRow (pointsNeg 3))
  apply chart_pairs <;> decide +kernel
set_option maxRecDepth 14000 in
theorem rots3 : ValidRotations 3 := by
  have check : ∀ j : Fin 128, autoOK (goalAt 3) ((rotationAt 3 j).map swapRows)=true := by decide +kernel
  intro j hj
  exact check ⟨j,hj⟩
set_option maxRecDepth 12000 in
theorem coverage4 : CoveredAt 4 := by
  change properPairs (chartGoal 15) (asRow (pointsPos 4)) (asRow (pointsNeg 4))
  apply chart_pairs <;> decide +kernel
set_option maxRecDepth 14000 in
theorem rots4 : ValidRotations 4 := by
  have check : ∀ j : Fin 128, autoOK (goalAt 4) ((rotationAt 4 j).map swapRows)=true := by decide +kernel
  intro j hj
  exact check ⟨j,hj⟩
set_option maxRecDepth 12000 in
theorem coverage5 : CoveredAt 5 := by
  change properPairs (chartGoal 31) (asRow (pointsPos 5)) (asRow (pointsNeg 5))
  apply chart_pairs <;> decide +kernel
set_option maxRecDepth 14000 in
theorem rots5 : ValidRotations 5 := by
  have check : ∀ j : Fin 128, autoOK (goalAt 5) ((rotationAt 5 j).map swapRows)=true := by decide +kernel
  intro j hj
  exact check ⟨j,hj⟩
end PEqualNP.Outside.L_meta_10568.Charge

namespace PEqualNP.Outside.L_meta_10568.Charge
theorem impossible2 (checks2 : CheckedAt 2) : Impossible (goalAt 2) 0 (startSet 2).toFinset := by
  intro k h limit run
  have width := (live_size run).2
  have ntk := (live_size run).1
  have card : (startSet 2).toFinset.card = 2 := by decide +kernel
  rw [card] at width
  have ch := checkedBelow 2 coverage2 (by intro no; omega) rots2 checks2
  have negLimit : h≤0 := by omega
  interval_cases h
  · have use := ch 0 0 0 rfl 0 (by decide)
    have eq : wordsAt 2 (group 2 0 0) 0 = startSet 2 := by decide +kernel
    rw [eq] at use
    exact use k 0 (by omega) (by decide) run
theorem lower2 (checks2 : CheckedAt 2) : Lower (vars 3) (graphGoal 3) 1 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (impossible2 checks2)
  intro a ha
  apply essential_ok (xs:=graphPairs 3 1) (by decide +kernel) a
  have eq : (graphPairs 3 1).map Prod.fst = vars 3 := by decide +kernel
  rw [eq]
  exact List.mem_toFinset.mpr ha
def maps2 : List (Nat × List Nat) := [(3,[]),(5,[33]),(9,[49]),(17,[65]),(6,[32]),(10,[48]),(18,[64]),(12,[32,49]),(20,[32,65]),(24,[48,65])]
def known2 := extendKnown [] 1 maps2
set_option maxRecDepth 12000 in
theorem knownOk2 (checks2 : CheckedAt 2) : Known known2 := extendKnown_ok baseKnown (lower2 checks2) (by decide +kernel)
theorem impossible3 (checks3 : CheckedAt 3) : Impossible (goalAt 3) 3 (startSet 3).toFinset := by
  intro k h limit run
  have width := (live_size run).2
  have ntk := (live_size run).1
  have card : (startSet 3).toFinset.card = 3 := by decide +kernel
  rw [card] at width
  have ch := checkedBelow 3 coverage3 (by intro no; omega) rots3 checks3
  have negLimit : h≤1 := by omega
  interval_cases h
  · have use := ch 3 3 0 rfl 0 (by decide)
    have eq : wordsAt 3 (group 3 3 0) 0 = startSet 3 := by decide +kernel
    rw [eq] at use
    exact use k 0 (by omega) (by decide) run
  · have use := ch 3 2 1 rfl 0 (by decide)
    have eq : wordsAt 3 (group 3 2 1) 0 = startSet 3 := by decide +kernel
    rw [eq] at use
    exact use k 1 (by omega) (by decide) run
theorem lower3 (checks3 : CheckedAt 3) : Lower (vars 7) (graphGoal 7) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (impossible3 checks3)
  intro a ha
  apply essential_ok (xs:=graphPairs 7 1) (by decide +kernel) a
  have eq : (graphPairs 7 1).map Prod.fst = vars 7 := by decide +kernel
  rw [eq]
  exact List.mem_toFinset.mpr ha
def maps3 : List (Nat × List Nat) := [(7,[]),(11,[50]),(19,[66]),(13,[49]),(21,[65]),(25,[49,66]),(14,[48]),(22,[64]),(26,[48,66]),(28,[48,65])]
def known3 := extendKnown known2 4 maps3
set_option maxRecDepth 12000 in
theorem knownOk3 (checks2 : CheckedAt 2) (checks3 : CheckedAt 3) : Known known3 := extendKnown_ok (knownOk2 checks2) (lower3 checks3) (by decide +kernel)
theorem impossible4 (checks4 : CheckedAt 4) : Impossible (goalAt 4) 6 (startSet 4).toFinset := by
  intro k h limit run
  have width := (live_size run).2
  have ntk := (live_size run).1
  have card : (startSet 4).toFinset.card = 4 := by decide +kernel
  rw [card] at width
  have ch := checkedBelow 4 coverage4 (by intro no; omega) rots4 checks4
  have negLimit : h≤3 := by omega
  interval_cases h
  · have use := ch 6 6 0 rfl 0 (by decide)
    have eq : wordsAt 4 (group 4 6 0) 0 = startSet 4 := by decide +kernel
    rw [eq] at use
    exact use k 0 (by omega) (by decide) run
  · have use := ch 6 5 1 rfl 0 (by decide)
    have eq : wordsAt 4 (group 4 5 1) 0 = startSet 4 := by decide +kernel
    rw [eq] at use
    exact use k 1 (by omega) (by decide) run
  · have use := ch 6 4 2 rfl 0 (by decide)
    have eq : wordsAt 4 (group 4 4 2) 0 = startSet 4 := by decide +kernel
    rw [eq] at use
    exact use k 2 (by omega) (by decide) run
  · have use := ch 6 3 3 rfl 0 (by decide)
    have eq : wordsAt 4 (group 4 3 3) 0 = startSet 4 := by decide +kernel
    rw [eq] at use
    exact use k 3 (by omega) (by decide) run
theorem lower4 (checks4 : CheckedAt 4) : Lower (vars 15) (graphGoal 15) 7 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (impossible4 checks4)
  intro a ha
  apply essential_ok (xs:=graphPairs 15 1) (by decide +kernel) a
  have eq : (graphPairs 15 1).map Prod.fst = vars 15 := by decide +kernel
  rw [eq]
  exact List.mem_toFinset.mpr ha
def maps4 : List (Nat × List Nat) := [(15,[]),(23,[67]),(27,[66]),(29,[65]),(30,[64])]
def known4 := extendKnown known3 7 maps4
set_option maxRecDepth 12000 in
theorem knownOk4 (checks2 : CheckedAt 2) (checks3 : CheckedAt 3) (checks4 : CheckedAt 4) : Known known4 := extendKnown_ok (knownOk3 checks2 checks3) (lower4 checks4) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem fiveCols (checks2 : CheckedAt 2) (checks3 : CheckedAt 3) (checks4 : CheckedAt 4) : ValidColumnsAt 5 := by
  intro _ ci mem
  have checks : cutColumns.toList.all (fun c => colCheck 31 c (boundsBefore known4)) = true := by decide +kernel
  have sc := col_sound (m:=31) ci (boundsBefore known4) (before_sound known4 (knownOk4 checks2 checks3 checks4)) (List.all_eq_true.mp checks _ mem)
  exact sc
theorem finalChargedOf (checks2 : CheckedAt 2) (checks3 : CheckedAt 3) (checks4 : CheckedAt 4) (checks5 : CheckedAt 5) : ChargedImpossible graph 9 1 fiveInputs.toFinset := by
  have result := checkedBelow 5 coverage5 (fiveCols checks2 checks3 checks4) rots5 checks5 10 9 1 rfl 0 (by decide)
  have rt : wordsAt 5 (group 5 9 1) 0 = fiveInputs := by decide +kernel
  have gt : goalAt 5 = graph := by decide +kernel
  rwa [rt,gt] at result
end PEqualNP.Outside.L_meta_10568.Charge

theorem PEqualNP.Outside.L_meta_10568 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  apply PEqualNP.Outside.L_meta_10568_aux.finishing
  apply PEqualNP.Outside.L_meta_10568_aux.chargeCost
  exact PEqualNP.Outside.L_meta_10568.Charge.finalChargedOf
    PEqualNP.Outside.L_meta_10568.Charge.checks2
    PEqualNP.Outside.L_meta_10568.Charge.checks3
    PEqualNP.Outside.L_meta_10568.Charge.checks4
    PEqualNP.Outside.L_meta_10568.Charge.checks5
