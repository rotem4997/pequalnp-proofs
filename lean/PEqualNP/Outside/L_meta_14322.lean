import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14322

namespace Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
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

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def remap (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

theorem remap_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨remap n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [remap, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end Restriction

namespace Minor.Signed

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 88

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 44 := ((x >>> 44) ^^^ x).setWidth 44
def cuts (ws : List W) : BitVec 44 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 44) ++ (0 : BitVec 44)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 44) (w : W) : Prop :=
  w.getLsbD (44+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 44) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 44+i.val < 88 := by omega
  have hi' : i.val < 88 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 44) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 44)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 88 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 88)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 88) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 88) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 88) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#88)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 7 inputs = false)
    (sample : ∀ k : Fin 88, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 88) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 7 inputs nd (lift low run)))

def rows : List W := [0x110214152113312743f, 0x20442c484a462cc6c48cf, 0x84f0068d0c98cf08f8f0c, 0xe0b00d002a0e0f00f00ff0, 0xf7000f96000ff000fff000, 0xfdfaa000000fffff000000]

def rootBranches : List (W × W × List W) := pairs rows

def leavesReject (t : W × W × List W) : Bool :=
  dispatch 2 (optimized 6) t.1 t.2.1 t.2.2

theorem rootBranches_length : rootBranches.length = 15 := rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_0 : leavesReject (rootBranches.getD 0 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_1 : leavesReject (rootBranches.getD 1 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_2 : leavesReject (rootBranches.getD 2 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_3 : leavesReject (rootBranches.getD 3 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_4 : leavesReject (rootBranches.getD 4 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_5 : leavesReject (rootBranches.getD 5 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_6 : leavesReject (rootBranches.getD 6 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_7 : leavesReject (rootBranches.getD 7 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_8 : leavesReject (rootBranches.getD 8 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_9 : leavesReject (rootBranches.getD 9 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_10 : leavesReject (rootBranches.getD 10 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_11 : leavesReject (rootBranches.getD 11 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_12 : leavesReject (rootBranches.getD 12 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_13 : leavesReject (rootBranches.getD 13 (0,0,[])) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rejected_branch_14 : leavesReject (rootBranches.getD 14 (0,0,[])) = false := by
  decide +kernel

theorem rejected_branches (i : Fin 15) :
    leavesReject (rootBranches.getD i.val (0,0,[])) = false := by
  fin_cases i
  · exact rejected_branch_0
  · exact rejected_branch_1
  · exact rejected_branch_2
  · exact rejected_branch_3
  · exact rejected_branch_4
  · exact rejected_branch_5
  · exact rejected_branch_6
  · exact rejected_branch_7
  · exact rejected_branch_8
  · exact rejected_branch_9
  · exact rejected_branch_10
  · exact rejected_branch_11
  · exact rejected_branch_12
  · exact rejected_branch_13
  · exact rejected_branch_14

set_option maxRecDepth 16000 in
theorem rejected_full_row : optimized 7 2 rows = false := by
  have hAny : rootBranches.any leavesReject = false := by
    apply List.any_eq_false.mpr
    intro t ht
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
    have hlt : i.val < rootBranches.length := i.isLt
    let j : Fin 15 := ⟨i.val,by simpa only [rootBranches_length] using hlt⟩
    have h := rejected_branches j
    change leavesReject (rootBranches.getD i.val (0,0,[])) = false at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] at h
    have h' : leavesReject (rootBranches.get i) = false := h
    rw [← hi,h']
    decide
  change ((rows == [goal] || rows == [~~~goal]) ||
    rootBranches.any leavesReject) = false
  rw [hAny]
  decide +kernel

theorem no_short_root : rows.sublists.all
    (fun ws => (ws == rows) || (cuts ws != -1)) = true := by
  decide +kernel

theorem reject : search 7 rows = false := by
  apply List.any_eq_false.mpr
  intro ws hws
  have hn := List.all_eq_true.mp no_short_root ws hws
  by_cases hw : ws = rows
  · subst ws
    change ¬(decide (6 ≤ 8) && (cuts rows == -1) && optimized 7 2 rows) = true
    simp only [rejected_full_row,Bool.and_false,Bool.false_and,Bool.false_eq_true,not_false_eq_true]
  · have hc : (cuts ws == -1) = false := by
      simpa [hw,beq_iff_eq] using hn
    simp only [hc,Bool.and_false,Bool.false_and,Bool.false_eq_true,not_false_eq_true]

set_option maxRecDepth 8000 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 7 < binaryCost gs :=
  bound_from_search rows rfl (by decide) reject (by decide +kernel) gs o hg he

end Minor.Signed

namespace NotCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14322.Restriction

def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def notCount (gs : List Gate) : ℕ := gs.countP isNot

theorem simplify_not_count (g : Gate) (m : ℕ) (inputs : List Stat) :
    notCount (simplify g.op m inputs).1.toList ≤ notCount [g] := by
  cases g with
  | mk op raw =>
    cases op
    · have h (xs : List Stat) : ∀ x ∈ (simpAnd m xs).1, x.op = .and := by
        intro x hx
        unfold simpAnd at hx
        split at hx <;> simp_all
        rw [← hx]
      cases hs : (simpAnd m inputs).1 with
      | none => simp [simplify,hs,notCount,isNot]
      | some x =>
        have he : x.op = .and := h inputs x (by simp [hs])
        simp [simplify,hs,notCount,isNot,he]
    · have h (xs : List Stat) : ∀ x ∈ (simpOr m xs).1, x.op = .or := by
        intro x hx
        unfold simpOr at hx
        split at hx <;> simp_all
        rw [← hx]
      cases hs : (simpOr m inputs).1 with
      | none => simp [simplify,hs,notCount,isNot]
      | some x =>
        have he : x.op = .or := h inputs x (by simp [hs])
        simp [simplify,hs,notCount,isNot,he]
    · have h₁ : ((simpNot m inputs).1.toList).countP isNot ≤ ((simpNot m inputs).1.toList).length :=
        List.countP_le_length
      have h := h₁.trans (toList_length_le (simpNot m inputs).1)
      simpa [simplify,notCount,isNot] using h
    all_goals simp [simplify,notCount,isNot]

theorem elimStep_not_count (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    notCount (elimStep n acc g).2 ≤ notCount acc.2 + notCount [g] := by
  unfold elimStep
  simp only [notCount,List.countP_append]
  exact Nat.add_le_add_left (simplify_not_count g (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))) _

theorem elim_not_count (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    notCount (elim n gs acc).2 ≤ notCount acc.2 + notCount gs := by
  induction gs generalizing acc with
  | nil => simp [elim,notCount]
  | cons g gs ih =>
    rw [elim_cons]
    have h := ih (elimStep n acc g)
    have hi := elimStep_not_count n acc g
    have hm : notCount (g :: gs) = notCount [g] + notCount gs :=
      List.countP_append (l₁:=[g]) (l₂:=gs)
    omega

end NotCount

namespace BinaryCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14322.Restriction
open PEqualNP.Outside.L_meta_14322.NotCount

def binaryCount (gs : List Gate) : ℕ := gs.countP (fun g => !isNot g)

theorem counts_add (gs : List Gate) : binaryCount gs + notCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [binaryCount,notCount,List.countP_cons,List.length_cons] at ih ⊢
    cases h : isNot g <;> simp [h] <;> omega

theorem count_simp_binary (g : Gate) (m : ℕ) (xs : List Stat) :
    binaryCount (simplify g.op m xs).1.toList ≤ binaryCount [g] := by
  by_cases hn : isNot g = true
  · have ho : g.op = .not := by
      cases g with
      | mk op raw => cases op <;> simp_all [isNot]
    have h (d : Gate) (hd : d ∈ (simpNot m xs).1) : isNot d = true := by
      unfold simpNot at hd
      split at hd <;> simp_all
      rw [← hd]
      rfl
    cases he : (simpNot m xs).1 with
    | none => simp [simplify,ho,he,binaryCount]
    | some d =>
      have hv := h d (by simp [he])
      simp [simplify,ho,he,binaryCount,hv,hn]
  · have h₁ : binaryCount (simplify g.op m xs).1.toList ≤ (simplify g.op m xs).1.toList.length :=
      List.countP_le_length
    exact h₁.trans ((toList_length_le _).trans (by simp [binaryCount,hn]))

theorem step_binary_count (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binaryCount (elimStep n acc g).2 ≤ binaryCount acc.2 + binaryCount [g] := by
  unfold elimStep
  simp only [binaryCount,List.countP_append]
  exact Nat.add_le_add_left (count_simp_binary g (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))) _

theorem step_dropped_binary (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hG : NOk g)
    (k : ℕ) (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    binaryCount (elimStep n acc g).2 = binaryCount acc.2 := by
  have hlen := elimStep_none n acc g hG k hk c hc
  unfold elimStep at hlen ⊢
  generalize h : (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = o at *
  cases o <;> simp_all

theorem elim_binary_count (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    binaryCount (elim n gs acc).2 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs generalizing acc with
  | nil => simp [elim,binaryCount]
  | cons g gs ih =>
    rw [elim_cons]
    have h := ih (elimStep n acc g)
    have hi := step_binary_count n acc g
    have hc : binaryCount (g :: gs) = binaryCount [g] + binaryCount gs :=
      List.countP_append (l₁:=[g]) (l₂:=gs)
    omega

theorem elim_binary_count_lt (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hFit : ∀ g ∈ gs, NOk g) (hBound : k < acc.1.length)
    (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, isNot g = false ∧ k ∈ g.inputs) :
    binaryCount (elim n gs acc).2 + 1 ≤ binaryCount acc.2 + binaryCount gs := by
  obtain ⟨g,hg,hNot,hRead⟩ := hex
  obtain ⟨pre,post,rfl⟩ := List.append_of_mem hg
  let act := elim n pre acc
  have hAct : act.1.getD k (Sum.inl false) = Sum.inl c :=
    (elim_getD n k _ pre _ hBound).trans hc
  have hp := elim_binary_count n pre acc
  have hG := step_dropped_binary n act g (hFit g hg) k hRead c hAct
  have hs := elim_binary_count n post (elimStep n act g)
  rw [hG] at hs
  change binaryCount act.2 ≤ binaryCount acc.2 + binaryCount pre at hp
  have hcat : binaryCount (pre ++ g :: post) =
      binaryCount pre + (binaryCount post + 1) := by
    simp [binaryCount,List.countP_append,List.countP_cons,hNot]
  rw [elim_append, elim_cons,hcat]
  change binaryCount (elim n post (elimStep n act g)).2 + 1 ≤ _
  omega

end BinaryCount

namespace PositivePivot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14322.Restriction
open PEqualNP.Outside.L_meta_14322.NotCount PEqualNP.Outside.L_meta_14322.BinaryCount

theorem except_snoc {R : Bool → Bool → Prop} {w w' : List Bool} {n : ℕ} {a b : Bool}
    (hSize : w.length = w'.length)
    (hR : ∀ j, j ≠ n → R (w.getD j false) (w'.getD j false))
    (hab : R a b) :
    ∀ j, j ≠ n → R ((w ++ [a]).getD j false) ((w' ++ [b]).getD j false) := by
  intro j hj
  by_cases he : j = w.length
  · rw [getD_snoc_len _ _ _ _ he.symm,
      getD_snoc_len _ _ _ _ (hSize.symm.trans he.symm)]
    exact hab
  · rw [getD_snoc_ne _ _ _ _ he,getD_snoc_ne _ _ _ _ (by rwa [← hSize])]
    exact hR j hj

theorem raw_after_snoc (w : List Bool) (a : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [a]).getD i false = w.getD i false :=
  getD_snoc_ne _ _ _ _ (by omega)

theorem gate_mono_at_inputs (g : Gate) (hG : g.op = .and ∨ g.op = .or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false ≤ w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  have order {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by cases a <;> cases b <;> decide
  rw [order]
  rcases hG with hG | hG
  · rw [hG]
    simp only [GateOp.eval,List.all_eq_true,List.mem_map,id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact order.mp (h i hi) (hx _ ⟨i,hi,rfl⟩)
  · rw [hG]
    simp only [GateOp.eval,List.any_eq_true,List.mem_map,id]
    rintro ⟨x, ⟨i,hi,rfl⟩,hx⟩
    exact ⟨_, ⟨i,hi,rfl⟩, order.mp (h i hi) hx⟩

theorem count_cons_zero (g : Gate) (gs : List Gate) (h : isNot g = false) :
    notCount (g::gs) = notCount gs := by simp [notCount,h]

theorem count_cons_one (g : Gate) (gs : List Gate) (h : isNot g = true) :
    notCount (g::gs) = notCount gs + 1 := by simp [notCount,h]

theorem binary_legal (g : Gate) (hFit : Ok g) (h : isNot g = false) :
    g.op = .and ∨ g.op = .or := by
  have ho := hFit.1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho
  rcases ho with ho|ho|ho
  · exact Or.inl ho
  · exact Or.inr ho
  · simp [isNot,ho] at h

theorem not_flag (g : Gate) (h : isNot g = true) : g.op = .not := by
  cases g with
  | mk op inputs => cases op <;> simp_all [isNot]

theorem no_binary_read_zero_not_mono (n : ℕ) (gs : List Gate)
    (hFit : ∀ g ∈ gs, Ok g) (hCount : notCount gs = 0)
    (hNo : ∀ g ∈ gs, isNot g = false → n ∉ g.inputs)
    (w w' : List Bool) (hLen : w.length = w'.length)
    (hOrd : ∀ j, j ≠ n → w.getD j false ≤ w'.getD j false)
    (out : ℕ) (hOut : out ≠ n) :
    (wiresFrom gs w).getD out false ≤ (wiresFrom gs w').getD out false := by
  induction gs generalizing w w' with
  | nil => exact hOrd out hOut
  | cons g gs ih =>
    have hG : isNot g = false := by
      cases h : isNot g
      · rfl
      · rw [count_cons_one _ _ h] at hCount
        omega
    let a := g.op.eval (g.inputs.map fun i => w.getD i false)
    let b := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hAB : a ≤ b :=
      gate_mono_at_inputs g (binary_legal g (hFit g List.mem_cons_self) hG) w w'
        (fun i hi => hOrd i (fun e => hNo g List.mem_cons_self hG (e ▸ hi)))
    change (wiresFrom gs (w ++ [a])).getD out false ≤ (wiresFrom gs (w' ++ [b])).getD out false
    exact ih (fun d hd => hFit d (List.mem_cons_of_mem _ hd))
      ((count_cons_zero _ _ hG).symm.trans hCount)
      (fun d hd => hNo d (List.mem_cons_of_mem _ hd)) (w++[a]) (w'++[b])
      (by simp [hLen]) (except_snoc hLen hOrd hAB)

theorem no_binary_read_one_not_antitone (n : ℕ) (gs : List Gate)
    (hFit : ∀ g ∈ gs, Ok g) (hCount : notCount gs ≤ 1)
    (hNo : ∀ g ∈ gs, isNot g = false → n ∉ g.inputs)
    (w w' : List Bool) (hLen : w.length = w'.length) (hIn : n < w.length)
    (hEq : ∀ j, j ≠ n → w.getD j false = w'.getD j false)
    (hTrue : w.getD n false = true) (hFalse : w'.getD n false = false)
    (out : ℕ) (hOut : out ≠ n) :
    (wiresFrom gs w).getD out false ≤ (wiresFrom gs w').getD out false := by
  induction gs generalizing w w' with
  | nil => exact le_of_eq (hEq out hOut)
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun i => w.getD i false)
    let b := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hL : (w++[a]).length = (w'++[b]).length := by simp [hLen]
    change (wiresFrom gs (w ++ [a])).getD out false ≤ (wiresFrom gs (w' ++ [b])).getD out false
    have hFit' : ∀ d ∈ gs, Ok d := fun d hd => hFit d (List.mem_cons_of_mem _ hd)
    have hNo' : ∀ d ∈ gs, isNot d = false → n ∉ d.inputs :=
      fun d hd => hNo d (List.mem_cons_of_mem _ hd)
    cases hG : isNot g with
    | false =>
      have hAB : a = b := by
        change g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => w'.getD i false)
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hEq i (fun e => hNo g List.mem_cons_self hG (e ▸ hi))
      have hN' := (count_cons_zero _ _ hG) ▸ hCount
      exact ih hFit' hN' hNo' _ _ hL (by simp; omega) (except_snoc hLen hEq hAB)
        ((raw_after_snoc w a n hIn).trans hTrue)
        ((raw_after_snoc w' b n (hLen ▸ hIn)).trans hFalse)
    | true =>
      have ho := not_flag g hG
      have hN' : notCount gs = 0 := by rw [count_cons_one _ _ hG] at hCount; omega
      have hAB : a ≤ b := by
        cases hin : g.inputs with
        | nil => simp [a,b,ho,hin,GateOp.eval]
        | cons i t =>
          by_cases he : i = n
          · simp [a,b,ho,hin,he,GateOp.eval,List.getD_eq_getElem?_getD] at hTrue hFalse ⊢
            simp [hTrue,hFalse]
          · have hh := hEq i he
            simp [a,b,ho,hin,GateOp.eval,List.getD_eq_getElem?_getD] at hh ⊢
            simp [hh]
      exact no_binary_read_zero_not_mono n gs hFit' hN' hNo' _ _ hL
        (except_snoc hLen (fun j hj => le_of_eq (hEq j hj)) hAB) out hOut

theorem positive_pivot_has_binary_reader (n : ℕ) (gs : List Gate) (out : ℕ)
    (hFit : ∀ g ∈ gs, Ok g) (hCount : notCount gs ≤ 1)
    (f : (Fin (n+1) → Bool) → Bool)
    (hE : ∀ x : Fin (n+1) → Bool, (wiresFrom gs (List.ofFn x)).getD out false = f x)
    (hPivot : ∃ x : Fin n → Bool, f (Fin.snoc x false) = false ∧ f (Fin.snoc x true) = true)
    (hNc : ∃ x y : Fin n → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false)) :
    ∃ g ∈ gs, isNot g = false ∧ n ∈ g.inputs := by
  by_contra! hNo
  have hOut : out ≠ n := by
    intro hOut
    have hZ (x : Fin n → Bool) : f (Fin.snoc x false) = false := by
      rw [← hE,hOut,ofFn_snoc,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨x,y,hxy⟩ := hNc
    exact hxy ((hZ x).trans (hZ y).symm)
  obtain ⟨x,hx0,hx1⟩ := hPivot
  let w := List.ofFn x
  have hWt : (w ++ [true]).getD n false = true := getD_snoc_len _ _ _ _ (by simp [w])
  have hWf : (w ++ [false]).getD n false = false := getD_snoc_len _ _ _ _ (by simp [w])
  have hEq : ∀ j, j ≠ n → (w ++ [true]).getD j false = (w ++ [false]).getD j false := by
    intro j hj
    rw [getD_snoc_ne _ _ _ _ (by simpa [w] using hj),getD_snoc_ne _ _ _ _ (by simpa [w] using hj)]
  have hm := no_binary_read_one_not_antitone n gs hFit hCount (fun g hg hz => hNo g hg hz)
    (w++[true]) (w++[false]) (by simp) (by simp [w]) hEq hWt hWf out hOut
  change (wiresFrom gs (List.ofFn x ++ [true])).getD out false ≤
    (wiresFrom gs (List.ofFn x ++ [false])).getD out false at hm
  rw [← ofFn_snoc,← ofFn_snoc,hE,hE,hx0,hx1] at hm
  nomatch hm

theorem normalizing_counts (gs : List Gate) :
    binaryCount (gs.map normGate) = binaryCount gs ∧ notCount (gs.map normGate) = notCount gs := by
  have hN : isNot ∘ normGate = isNot := by
    funext g
    cases g with
    | mk op inputs => cases op <;> rfl
  have hB : (fun g => !isNot (normGate g)) = (fun g => !isNot g) := by
    funext g
    exact congrArg not (congrFun hN g)
  constructor
  · simp only [binaryCount,List.countP_map,Function.comp_def,hB]
  · simp only [notCount,List.countP_map,hN]

theorem one_not_positive_pin_saves_binary (n : ℕ) (C : Circuit) (hFit : FanInTwo C)
    (hCount : notCount C.gates ≤ 1) (f : (Fin (n+1) → Bool) → Bool)
    (hE : ∀ x : Fin (n+1) → Bool, C.eval (List.ofFn x) = f x)
    (hPivot : ∃ x : Fin n → Bool, f (Fin.snoc x false) = false ∧ f (Fin.snoc x true) = true)
    (hNc : ∃ x y : Fin n → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false)) :
    ∃ D : Circuit, FanInTwo D ∧ notCount D.gates ≤ 1 ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f (Fin.snoc x false) := by
  let gs := C.gates.map normGate
  have hNoK (g : Gate) (hg : g ∈ gs) : NOk g := by
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok d (hFit d hd)
  have hFin (g : Gate) (hg : g ∈ gs) : Ok g := (hNoK g hg).1
  have hEv (x : Fin (n+1) → Bool) : (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    rw [show gs = C.gates.map normGate from rfl,wiresFrom_norm]
    exact hE x
  obtain ⟨hb,hn⟩ := normalizing_counts C.gates
  have hCount' : notCount gs ≤ 1 := hn.symm ▸ hCount
  have hRead := positive_pivot_has_binary_reader n gs C.output hFin hCount' f hEv hPivot hNc
  let init := (initStats n false,([] : List Gate))
  let acc := elim n gs init
  have hDing := elim_binary_count_lt n n gs init hNoK (by simp [init,initStats]) false
    (initStats_last n false) hRead
  have hDC : binaryCount acc.2 + 1 ≤ binaryCount C.gates := by
    change binaryCount acc.2 + 1 ≤ 0 + binaryCount gs at hDing
    rw [zero_add,hb] at hDing
    exact hDing
  have hNotD : notCount acc.2 ≤ 1 := by
    have h := elim_not_count n gs init
    change notCount acc.2 ≤ 0 + notCount gs at h
    omega
  have hV (x : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        f (Fin.snoc x false) := by
    have hi := inv_elim n (List.ofFn x) (by simp) gs _ _ hFin (inv_init n false x)
    rw [(hi.2 C.output).2,← ofFn_snoc,hEv]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x,y,h⟩ := hNc
    exfalso
    apply h
    rw [← hV x,← hV y,hst]
    rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs init (by simp [init]),hNotD,hDC,?_⟩
    intro x
    have h := hV x
    rw [hst] at h
    exact h

end PositivePivot

namespace Aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14322.Restriction
open PEqualNP.Outside.L_meta_14322.NotCount PEqualNP.Outside.L_meta_14322.BinaryCount PEqualNP.Outside.L_meta_14322.PositivePivot

def edges : List ℕ := [0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7]

def graph (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def relabel : Fin 8 → Fin 8 := ![5, 3, 7, 4, 1, 6, 2, 0]

def graphEight (x : Fin 8 → Bool) : Bool := graph (x ∘ relabel)
def graphSeven (x : Fin 7 → Bool) : Bool := graphEight (Fin.snoc x false)
def graphSix (x : Fin 6 → Bool) : Bool := graphSeven (Fin.snoc x false)

theorem first_pivot :
    ∃ x : Fin 7 → Bool, graphEight (Fin.snoc x false) = false ∧ graphEight (Fin.snoc x true) = true := by
  refine ⟨fun i => decide (i=6),?_⟩
  decide +kernel

theorem second_pivot :
    ∃ x : Fin 6 → Bool, graphSeven (Fin.snoc x false) = false ∧ graphSeven (Fin.snoc x true) = true := by
  refine ⟨fun i => decide (i=5),?_⟩
  decide +kernel

theorem first_nonconstant : ∃ x y : Fin 7 → Bool, graphSeven x ≠ graphSeven y := by
  refine ⟨fun _ => false,fun _ => true,?_⟩
  decide +kernel

theorem second_nonconstant : ∃ x y : Fin 6 → Bool, graphSix x ≠ graphSix y := by
  refine ⟨fun _ => false,fun _ => true,?_⟩
  decide +kernel

theorem graph_six_is_minor : ∀ x : Fin 6 → Bool, graphSix x = PEqualNP.Outside.L_meta_14322.Minor.Signed.F x := by
  decide +kernel

def witness : List Gate := [
  ⟨.or,[2,0]⟩,
  ⟨.or,[7,5]⟩,
  ⟨.and,[8,9]⟩,
  ⟨.or,[3,1]⟩,
  ⟨.or,[7,6]⟩,
  ⟨.and,[11,12]⟩,
  ⟨.or,[7,1]⟩,
  ⟨.or,[14,0]⟩,
  ⟨.and,[4,15]⟩,
  ⟨.or,[10,13]⟩,
  ⟨.or,[17,16]⟩
]

theorem witness_legal : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem witness_correct : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness,18⟩ (List.ofFn x) = graph x := by
  decide +kernel

theorem unique_not_count (gs : List Gate)
    (unique : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) : notCount gs ≤ 1 := by
  induction gs with
  | nil => simp [notCount]
  | cons g rest ih =>
    by_cases head : isNot g = true
    · have tailZero : rest.countP isNot = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha haNot
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
        have h0 : (⟨0, by simp⟩ : Fin (g :: rest).length) = i.succ :=
          unique _ _ (not_flag g head)
            (show (rest.get i).op = GateOp.not from hi ▸ not_flag a haNot)
        have hval := congrArg Fin.val h0
        simp at hval
      simp [notCount,head,tailZero]
    · unfold notCount
      rw [List.countP_cons_of_neg head]
      apply ih
      intro i j hi hj
      exact Fin.succ_inj.mp (unique i.succ j.succ hi hj)

theorem no_savings (gs : List Gate) (out : ℕ)
    (hFit : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hOne : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (hE : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = graph x) :
    ∃ (gs' : List Gate) (out' : ℕ),
      (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs',out'⟩ (List.ofFn x) = graph x := by
  by_cases hExists : ∃ g ∈ gs, g.op = .not
  · let C : Circuit := ⟨gs,out⟩
    let U : Circuit := remap 8 8 relabel C
    have hUfit : FanInTwo U := by
      intro g hg
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop,harity⟩ := hFit d hd
      exact ⟨by simpa [relGate] using hop, by simpa [relGate] using harity⟩
    have hUBin : binaryCount U.gates = binaryCount gs := by
      change binaryCount (gs.map (relGate 8 8 relabel)) = _
      rw [binaryCount,List.countP_map]
      rfl
    have hUNot : notCount U.gates = notCount gs := by
      change notCount (gs.map (relGate 8 8 relabel)) = _
      rw [notCount,List.countP_map]
      rfl
    have hUcount : notCount U.gates ≤ 1 := hUNot.symm ▸ unique_not_count gs hOne
    have hUEv (x : Fin 8 → Bool) : U.eval (List.ofFn x) = graphEight x :=
      ((rel_fold 8 8 relabel gs _ _ (rel_init 8 8 relabel x)).2.2 out).trans (hE (x ∘ relabel))
    obtain ⟨D,hDfit,hDcount,hDsize,hDEv⟩ :=
      one_not_positive_pin_saves_binary 7 U hUfit hUcount graphEight hUEv first_pivot first_nonconstant
    obtain ⟨E,hEfit,_hEcount,hEsize,hEEv⟩ :=
      one_not_positive_pin_saves_binary 6 D hDfit hDcount graphSeven hDEv second_pivot second_nonconstant
    have hEBin := PEqualNP.Outside.L_meta_14322.Minor.Signed.bound E.gates E.output
      (fun g hg => by simpa only [PEqualNP.Outside.L_meta_14322.Minor.Signed.legal, Set.mem_insert_iff,Set.mem_singleton_iff] using hEfit g hg)
      (fun x => (hEEv x).trans (graph_six_is_minor x))
    have sameCount : PEqualNP.Outside.L_meta_14322.Minor.Signed.binaryCost E.gates = binaryCount E.gates := by
      unfold PEqualNP.Outside.L_meta_14322.Minor.Signed.binaryCost binaryCount
      rw [← List.countP_eq_length_filter]
      congr 1
      funext g
      cases g with
      | mk op inputs => cases op <;> rfl
    rw [sameCount] at hEBin
    rw [hUBin] at hDsize
    have hTot := counts_add gs
    obtain ⟨g,hg,ho⟩ := hExists
    have hNot : 0 < notCount gs := by
      by_contra! hn
      have hzero : notCount gs = 0 := by omega
      exact (List.countP_eq_zero.mp hzero g hg) (by simp [isNot,ho])
    exact ⟨witness,18,witness_legal,by change 11 ≤ gs.length; omega,witness_correct⟩
  · refine ⟨gs,out,?_,le_rfl,hE⟩
    intro g hg
    obtain ⟨ho,hn⟩ := hFit g hg
    refine ⟨?_,hn⟩
    rcases ho with ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr ho
    · exact (hExists ⟨g,hg,ho⟩).elim

end Aux

end PEqualNP.Outside.L_meta_14322

theorem PEqualNP.Outside.L_meta_14322 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  exact PEqualNP.Outside.L_meta_14322.Aux.no_savings
