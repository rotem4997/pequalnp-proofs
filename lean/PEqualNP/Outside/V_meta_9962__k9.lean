import Mathlib
import PEqualNP.Defs

-- The value of L-meta-9962 is 9: an explicit circuit of 9 gates (found by exact search) for the upper half;
-- for the lower half a certified frontier search (k-sandhus merged L-meta-927 Run machinery, as
-- packaged in our lb kit; the HasLitSize glue follows family 2s rep_lb).

namespace PEqualNP.Outside.V_meta_9962__k9_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

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
    rw [elim_cons, List.length_cons]; omega

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

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)


theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## Family 1: a certified frontier search (Run states closed under the moves of `next`) -/

theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr

def L_ : List ℕ := [0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48]
def M_ : ℕ := 4194303
def Y_ : ℕ := 448104
def XS_ : List ℕ := [135466,270924,541808,1083264,2160640,4128768]
def PD_ : List (ℕ × ℕ) := [(1,376156),(2,484338),(3,396453),(4,178958),(5,57563),(6,52529),(7,23492),(8,4286),(9,5379),(10,2013),(11,1714),(12,517),(13,94),(14,115),(15,101),(16,46),(17,11),(18,9)]
def PM_ : List (ℕ × ℕ) := [(8,448104),(13,448104),(19,448104),(20,448104),(21,448104)]

def G_ : List (List ℕ) := [[0,2,1,3,4,6,5,11,13,12,14,7,9,8,10,15,16,18,17,19,21,20]]

/-- the closed set of failing search states (960 states, up to 1 symmetries) -/
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,169898,326220,4146288] BT.lf) [2,541808,1480618,2554444] (BT.nd BT.lf [2,672880,1480618,2423372] BT.lf)) [2,935024,1218474,2423372] (BT.nd (BT.nd BT.lf [2,935024,1218474,2554444] BT.lf) [2,1000560,1218474,2423372] (BT.nd BT.lf [3,34688,135466,326220,4146288] BT.lf))) [3,131072,541808,1480618,2423372] (BT.nd (BT.nd (BT.nd BT.lf [3,131072,803952,1218474,2423372] BT.lf) [3,135466,541808,1345408,2554444] (BT.nd BT.lf [3,135466,541808,1476480,2554444] BT.lf)) [3,135466,672880,1345408,2423372] (BT.nd (BT.nd BT.lf [3,135466,803952,1083264,2554444] BT.lf) [3,135466,935024,1083264,2423372] (BT.nd BT.lf [3,135466,935024,1083264,2554444] BT.lf)))) [3,135466,935024,1218474,2423372] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,135466,935024,1476480,2423372] BT.lf) [3,135466,1000560,1083264,2423372] (BT.nd BT.lf [3,169898,326220,541808,4128768] BT.lf)) [3,393216,541808,1218474,2423372] (BT.nd (BT.nd BT.lf [3,393216,541808,1218474,2554444] BT.lf) [3,393216,935024,1218474,2423372] (BT.nd BT.lf [3,393312,541808,1218474,2423372] BT.lf))) [3,397610,541808,1083264,2554444] (BT.nd (BT.nd (BT.nd BT.lf [3,397610,672880,1083264,2423372] BT.lf) [3,397610,935024,1083264,2423372] (BT.nd BT.lf [3,406382,935024,1218474,2423372] BT.lf)) [3,541808,917504,1218474,2423372] (BT.nd (BT.nd BT.lf [3,541808,935024,1218474,2423372] BT.lf) [3,541808,983040,1218474,2423372] BT.lf)))) [3,935024,1083264,1218474,2423372] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,935024,1218474,2423372] BT.lf) [3,935024,1218474,2423372,4128768] (BT.nd BT.lf [3,948094,1218474,2423372,4146288] BT.lf)) [4,17520,135466,326220,1083264,4128768] (BT.nd (BT.nd BT.lf [4,34688,63488,135466,270924,4146288] BT.lf) [4,34688,135466,326220,541808,4128768] (BT.nd BT.lf [4,65535,135466,326220,1083264,4146288] BT.lf))) [4,131072,135466,541808,1345408,2423372] (BT.nd (BT.nd (BT.nd BT.lf [4,131072,135466,803952,1083264,2423372] BT.lf) [4,131072,262144,541808,1218474,2423372] (BT.nd BT.lf [4,131072,270924,541808,1480618,2160640] BT.lf)) [4,131072,270924,803952,1218474,2160640] (BT.nd (BT.nd BT.lf [4,131072,397610,541808,1083264,2423372] BT.lf) [4,135466,270924,541808,1345408,2291712] BT.lf))) [4,135466,270924,541808,1476480,2553856] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,135466,270924,672880,1345408,2160640] BT.lf) [4,135466,270924,935024,1083264,2160640] (BT.nd BT.lf [4,135466,270924,935024,1083264,2423372] BT.lf)) [4,135466,270924,935024,1083264,2553856] (BT.nd (BT.nd BT.lf [4,135466,270924,1000560,1083264,2160640] BT.lf) [4,135466,270924,1099648,2686064,4146288] (BT.nd BT.lf [4,135466,270924,1099712,2686064,4128768] BT.lf))) [4,135466,270924,1099712,2948732,4128768] (BT.nd (BT.nd (BT.nd BT.lf [4,135466,271948,1624048,2160640,4146288] BT.lf) [4,135466,271980,1624048,2160640,4128768] (BT.nd BT.lf [4,135466,271980,1759226,2160640,4128768] BT.lf)) [4,135466,287308,1083264,2686064,4146288] (BT.nd (BT.nd BT.lf [4,135466,288332,1083264,2160640,4146288] BT.lf) [4,135466,324172,541808,1083264,4128768] BT.lf))))) [4,135466,324172,541808,1218474,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,135466,326220,541808,1083264,4128768] BT.lf) [4,135466,326220,541808,1083264,4146288] (BT.nd BT.lf [4,135466,326220,541808,1218474,4128768] BT.lf)) [4,135466,327679,1083264,2423372,4146288] (BT.nd (BT.nd BT.lf [4,135466,393216,541808,1083264,2423372] BT.lf) [4,135466,393216,541808,1083264,2554444] (BT.nd BT.lf [4,135466,393216,541808,1218474,2423372] BT.lf))) [4,135466,393216,541808,1476480,2423372] (BT.nd (BT.nd (BT.nd BT.lf [4,135466,393216,935024,1083264,2423372] BT.lf) [4,135466,393312,541808,1083264,2423372] (BT.nd BT.lf [4,135466,401996,541808,1345408,2160640] BT.lf)) [4,135466,401996,541808,1476480,2160640] (BT.nd (BT.nd BT.lf [4,135466,401996,803952,1083264,2160640] BT.lf) [4,135466,401996,935024,1083264,2160640] BT.lf))) [4,135466,406382,935024,1083264,2423372] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,135466,541808,917504,1083264,2423372] BT.lf) [4,135466,541808,935024,1083264,2423372] (BT.nd BT.lf [4,135466,541808,983040,1083264,2423372] BT.lf)) [4,135466,541808,1083264,1441792,2423372] (BT.nd (BT.nd BT.lf [4,135466,541808,1083264,1507328,2423372] BT.lf) [4,135466,541808,1083264,2031616,2423372] (BT.nd BT.lf [4,135466,541808,1083264,2032752,2423372] BT.lf))) [4,135466,541808,1083264,2049136,2423372] (BT.nd (BT.nd (BT.nd BT.lf [4,135466,541808,1218474,1441792,2423372] BT.lf) [4,135466,541808,1218474,2031616,2423372] (BT.nd BT.lf [4,135466,541808,1345408,2423372,4128768] BT.lf)) [4,135466,541808,1345408,2423372,4137548] (BT.nd (BT.nd BT.lf [4,135466,541808,1345408,2423372,4146288] BT.lf) [4,135466,541808,1345408,2423372,4192256] BT.lf)))) [4,135466,541808,1345408,2423372,4192844] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,135466,541808,1345416,2423372,4128768] BT.lf) [4,135466,541808,1345472,2423372,4128768] (BT.nd BT.lf [4,135466,541808,1345472,2423372,4146288] BT.lf)) [4,135466,541808,1353676,2423372,4162048] (BT.nd (BT.nd BT.lf [4,135466,541808,1476480,2423372,4128768] BT.lf) [4,135466,541808,1480618,2423372,4128768] (BT.nd BT.lf [4,135466,575088,1353676,2423372,4128768] BT.lf))) [4,135466,803952,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [4,135466,803952,1083264,2423372,4137548] BT.lf) [4,135466,803952,1083264,2423372,4146288] (BT.nd BT.lf [4,135466,803952,1083264,2423372,4192256] BT.lf)) [4,135466,803952,1083264,2423372,4192844] (BT.nd (BT.nd BT.lf [4,135466,803952,1218474,2423372,4128768] BT.lf) [4,135466,803952,1345408,2423372,4128768] BT.lf))) [4,135466,803960,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,135466,804464,1083264,2423372,4128768] BT.lf) [4,135466,812668,1083264,2422848,4146288] (BT.nd BT.lf [4,135466,812668,1083264,2423372,4145216] BT.lf)) [4,135466,812668,1083264,2423372,4146288] (BT.nd (BT.nd BT.lf [4,135466,812668,1099712,2423372,4128768] BT.lf) [4,135466,812668,1218474,2423372,4146288] (BT.nd BT.lf [4,135466,812668,1345472,2160640,4146288] BT.lf))) [4,135466,935024,1083264,2160640,2423372] (BT.nd (BT.nd (BT.nd BT.lf [4,135466,935024,1083264,2423372] BT.lf) [4,135466,935024,1083264,2423372,4128768] (BT.nd BT.lf [4,135466,948094,1083264,2423372,4146288] BT.lf)) [4,151914,812668,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [4,168746,541808,1353676,2423372,4128768] BT.lf) [4,393216,397610,541808,1083264,2423372] BT.lf)))))) [4,393216,406382,541808,1218474,2423372] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,393216,541808,1083264,1218474,2423372] BT.lf) [4,393216,541808,1218474,2423372] (BT.nd BT.lf [4,393216,541808,1218474,2423372,4128768] BT.lf)) [4,397610,401996,541808,1083264,2160640] (BT.nd (BT.nd BT.lf [4,397610,541808,1083264,2423372,4128768] BT.lf) [4,397610,541808,1083264,2423372,4137548] (BT.nd BT.lf [4,397610,541808,1083264,2423372,4146288] BT.lf))) [4,397610,541808,1083264,2423372,4192256] (BT.nd (BT.nd (BT.nd BT.lf [4,397610,541808,1083264,2423372,4192844] BT.lf) [4,397610,541808,1218474,2423372,4128768] (BT.nd BT.lf [4,397610,541808,1345408,2423372,4128768] BT.lf)) [4,397610,541808,1480618,2423372,4128768] (BT.nd (BT.nd BT.lf [4,397610,803952,1083264,2423372,4128768] BT.lf) [4,397674,541808,1083264,2423372,4128768] BT.lf))) [4,397674,541808,1083264,2423372,4146288] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,397674,812668,1083264,2160640,4146288] BT.lf) [4,398122,541808,1083264,2423372,4128768] (BT.nd BT.lf [4,406382,541808,1083264,2423372,4132872] BT.lf)) [4,406382,541808,1087368,2423372,4128768] (BT.nd (BT.nd BT.lf [4,406382,541808,1218474,2423372,4128768] BT.lf) [4,406382,541808,1218474,2423372,4146288] (BT.nd BT.lf [4,406382,542328,1218474,2160640,4128768] BT.lf))) [4,406382,677242,1083264,2423372,4146288] (BT.nd (BT.nd (BT.nd BT.lf [4,541808,948094,1218474,2423372,4128768] BT.lf) [4,541808,983167,1218474,2423372,4128768] (BT.nd BT.lf [4,677242,812668,1218474,2423372,4128768] BT.lf)) [5,520,406382,541808,1218474,2160640,4128768] (BT.nd (BT.nd BT.lf [5,1024,135466,270924,1624048,2160640,4146288] BT.lf) [5,1056,135466,270924,1624048,2160640,4128768] BT.lf)))) [5,1056,135466,270924,1759226,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1056,270924,677242,1218474,2160640,4128768] BT.lf) [5,17408,135466,270924,1083264,2160640,4146288] (BT.nd BT.lf [5,17520,34688,135466,270924,2160640,4128768] BT.lf)) [5,17520,135466,270924,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,17520,135466,270924,1083264,2160640,4146288] BT.lf) [5,17520,135466,270924,1083264,2423372,4128768] (BT.nd BT.lf [5,33280,135466,541808,1353676,2423372,4128768] BT.lf))) [5,34304,135466,270924,541808,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,34304,135466,270924,541808,2423372,4128768] BT.lf) [5,34432,135466,270924,541808,2160640,4128768] (BT.nd BT.lf [5,34688,63488,135466,270924,541808,4128768] BT.lf)) [5,34688,65535,135466,270924,2160640,4146288] (BT.nd (BT.nd BT.lf [5,34688,135466,270924,541808,2160640,4128768] BT.lf) [5,34688,135466,270924,541808,2160640,4146288] BT.lf))) [5,34688,135466,270924,541808,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,34688,169898,270924,541808,2160640,4128768] BT.lf) [5,38826,135466,270924,541808,2160640,4128768] (BT.nd BT.lf [5,56755,135466,270924,1083264,2160640,4146288] BT.lf)) [5,65535,135466,270924,541808,4163456,4192256] (BT.nd (BT.nd BT.lf [5,65535,135466,270924,1083264,2160640,4146288] BT.lf) [5,65535,135466,270924,1083264,2423372,4146288] (BT.nd BT.lf [5,65535,135466,270924,1083264,4146288,4192256] BT.lf))) [5,65535,135466,326220,541808,1083264] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,135466,326220,541808,1083264,4128768] BT.lf) [5,131072,135466,262144,541808,1083264,2423372] (BT.nd BT.lf [5,131072,135466,270924,541808,1345408,2160640] BT.lf)) [5,131072,135466,270924,803952,1083264,2160640] (BT.nd (BT.nd BT.lf [5,131072,270924,397610,541808,1083264,2160640] BT.lf) [5,131072,270924,541808,1218474,2160640,4128768] BT.lf))))) [5,131072,270924,541808,1218474,2160640,4133162] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,131072,270924,541808,1218474,2160640,4146288] BT.lf) [5,131072,270924,541808,1218474,2160640,4163456] (BT.nd BT.lf [5,131072,270924,541808,1218474,2160640,4167594] BT.lf)) [5,131072,270924,541808,1218474,2291712,4128768] (BT.nd (BT.nd BT.lf [5,131072,270924,541808,1218474,2423372,4128768] BT.lf) [5,131072,270924,672880,1218474,2160640,4128768] (BT.nd BT.lf [5,131072,401996,541808,1218474,2160640,4128768] BT.lf))) [5,131080,270924,541808,1218474,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,131104,270924,541808,1218474,2160640,4128768] BT.lf) [5,131104,270924,541808,1218474,2160640,4146288] (BT.nd BT.lf [5,131104,270924,677242,1083264,2160640,4146288] BT.lf)) [5,131328,270924,541808,1218474,2160640,4128768] (BT.nd (BT.nd BT.lf [5,131370,270924,541808,1218474,2160640,4128768] BT.lf) [5,135168,270924,541808,1218474,2160640,4128768] BT.lf))) [5,135210,270924,541808,1083264,2160640,3080192] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135210,270924,541808,1083264,2160640,4128768] BT.lf) [5,135210,270924,541808,1083264,2160640,4146288] (BT.nd BT.lf [5,135210,270924,541808,1083264,2160640,4163456] BT.lf)) [5,135210,270924,541808,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [5,135210,270924,541808,1218474,2160640,4128768] BT.lf) [5,135434,270924,541808,1218474,2160640,4128768] (BT.nd BT.lf [5,135458,270924,541808,1218474,2160640,4128768] BT.lf))) [5,135466,169898,270924,541808,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,196607,270924,1083264,2160640,4146288] BT.lf) [5,135466,270924,393216,541808,1083264,2160640] (BT.nd BT.lf [5,135466,270924,393216,541808,1083264,2423372] BT.lf)) [5,135466,270924,393216,541808,1083264,2553856] (BT.nd (BT.nd BT.lf [5,135466,270924,393216,935024,1083264,2160640] BT.lf) [5,135466,270924,393312,541808,1083264,2160640] BT.lf)))) [5,135466,270924,406382,935024,1083264,2160640] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541744,1083264,2160640,4146288] BT.lf) [5,135466,270924,541808,917504,1083264,2160640] (BT.nd BT.lf [5,135466,270924,541808,935024,1083264,2160640] BT.lf)) [5,135466,270924,541808,983040,1083264,2160640] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083008,2160640,4128768] BT.lf) [5,135466,270924,541808,1083008,2160640,4146288] (BT.nd BT.lf [5,135466,270924,541808,1083008,2160640,4163200] BT.lf))) [5,135466,270924,541808,1083008,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,1441792,2160640] BT.lf) [5,135466,270924,541808,1083264,1507328,2160640] (BT.nd BT.lf [5,135466,270924,541808,1083264,2031616,2160640] BT.lf)) [5,135466,270924,541808,1083264,2031616,2423372] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2032752,2160640] BT.lf) [5,135466,270924,541808,1083264,2049136,2160640] BT.lf))) [5,135466,270924,541808,1083264,2160640,3604480] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4128768] BT.lf) [5,135466,270924,541808,1083264,2160640,4128776] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4128800] BT.lf)) [5,135466,270924,541808,1083264,2160640,4128808] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4128864] BT.lf) [5,135466,270924,541808,1083264,2160640,4129280] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4129288] BT.lf))) [5,135466,270924,541808,1083264,2160640,4129344] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4129792] BT.lf) [5,135466,270924,541808,1083264,2160640,4129824] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4129856] BT.lf)) [5,135466,270924,541808,1083264,2160640,4129904] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4130304] BT.lf) [5,135466,270924,541808,1083264,2160640,4146176] BT.lf))))))) [5,135466,270924,541808,1083264,2160640,4146224] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4146288] BT.lf) [5,135466,270924,541808,1083264,2160640,4146296] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4146800] BT.lf)) [5,135466,270924,541808,1083264,2160640,4161536] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4162048] BT.lf) [5,135466,270924,541808,1083264,2160640,4162560] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4163200] BT.lf))) [5,135466,270924,541808,1083264,2160640,4179056] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160640,4181137] BT.lf) [5,135466,270924,541808,1083264,2160648,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160648,4128776] BT.lf)) [5,135466,270924,541808,1083264,2160648,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160672,4128768] BT.lf) [5,135466,270924,541808,1083264,2160672,4128800] BT.lf))) [5,135466,270924,541808,1083264,2160672,4146288] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160680,4128768] BT.lf) [5,135466,270924,541808,1083264,2160704,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2160704,4128832] BT.lf)) [5,135466,270924,541808,1083264,2160704,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2160712,4128768] BT.lf) [5,135466,270924,541808,1083264,2160736,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2161152,4128768] BT.lf))) [5,135466,270924,541808,1083264,2161152,4129280] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2161152,4146288] BT.lf) [5,135466,270924,541808,1083264,2161160,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2161216,4128768] BT.lf)) [5,135466,270924,541808,1083264,2161228,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2161664,4128768] BT.lf) [5,135466,270924,541808,1083264,2161664,4129792] BT.lf)))) [5,135466,270924,541808,1083264,2161664,4146288] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2161696,4128768] BT.lf) [5,135466,270924,541808,1083264,2161728,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2162176,4128768] BT.lf)) [5,135466,270924,541808,1083264,2291712,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2291712,4133162] BT.lf) [5,135466,270924,541808,1083264,2291712,4146288] (BT.nd BT.lf [5,135466,270924,541808,1083264,2291712,4163456] BT.lf))) [5,135466,270924,541808,1083264,2291720,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2291744,4128768] BT.lf) [5,135466,270924,541808,1083264,2291744,4146288] (BT.nd BT.lf [5,135466,270924,541808,1083264,2422784,4128768] BT.lf)) [5,135466,270924,541808,1083264,2422784,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2422792,4128768] BT.lf) [5,135466,270924,541808,1083264,2422848,4128768] BT.lf))) [5,135466,270924,541808,1083264,2422848,4146288] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2422860,4128768] BT.lf) [5,135466,270924,541808,1083264,2423296,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2423308,4128768] BT.lf)) [5,135466,270924,541808,1083264,2423364,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,2490368] BT.lf) [5,135466,270924,541808,1083264,2423372,3080192] (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,3604480] BT.lf))) [5,135466,270924,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,4128776] BT.lf) [5,135466,270924,541808,1083264,2423372,4128800] (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,4128832] BT.lf)) [5,135466,270924,541808,1083264,2423372,4129280] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,4129792] BT.lf) [5,135466,270924,541808,1083264,2423372,4132864] BT.lf))))) [5,135466,270924,541808,1083264,2423372,4132872] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,4145152] BT.lf) [5,135466,270924,541808,1083264,2423372,4145216] (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,4146288] BT.lf)) [5,135466,270924,541808,1083264,2423372,4161536] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2423372,4162048] BT.lf) [5,135466,270924,541808,1083264,2423404,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083264,2424396,4128768] BT.lf))) [5,135466,270924,541808,1083264,2553856,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083264,2554444,4128768] BT.lf) [5,135466,270924,541808,1083272,2160648,4128768] (BT.nd BT.lf [5,135466,270924,541808,1083272,2423372,4128768] BT.lf)) [5,135466,270924,541808,1083296,2160672,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1083296,2423372,4128768] BT.lf) [5,135466,270924,541808,1083328,2423372,4128768] BT.lf))) [5,135466,270924,541808,1087360,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1087368,2423372,4128768] BT.lf) [5,135466,270924,541808,1099648,2423372,4128768] (BT.nd BT.lf [5,135466,270924,541808,1099648,2686064,4128768] BT.lf)) [5,135466,270924,541808,1099712,2423372,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1214336,2291712,4128768] BT.lf) [5,135466,270924,541808,1214336,2423372,4128768] (BT.nd BT.lf [5,135466,270924,541808,1218474,2291712,4128768] BT.lf))) [5,135466,270924,541808,1218474,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,541808,1218474,2423372,4146288] BT.lf) [5,135466,270924,541816,1083264,2160640,4128768] (BT.nd BT.lf [5,135466,270924,541816,1083264,2160640,4128776] BT.lf)) [5,135466,270924,541816,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,541816,1083264,2160640,4146296] BT.lf) [5,135466,270924,541816,1083264,2160648,4128768] BT.lf)))) [5,135466,270924,541816,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,542064,1083264,2160640,4146288] BT.lf) [5,135466,270924,542320,1083264,2160640,4128768] (BT.nd BT.lf [5,135466,270924,542320,1083264,2160640,4129280] BT.lf)) [5,135466,270924,542320,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,542320,1083264,2160640,4146800] BT.lf) [5,135466,270924,542320,1083264,2161152,4128768] (BT.nd BT.lf [5,135466,270924,542320,1083264,2423372,4128768] BT.lf))) [5,135466,270924,542320,1218474,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,542328,1083264,2160640,4128768] BT.lf) [5,135466,270924,542328,1218474,2160640,4128768] (BT.nd BT.lf [5,135466,270924,574576,1083264,2160640,4128768] BT.lf)) [5,135466,270924,574576,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,574576,1083264,2160640,4161536] BT.lf) [5,135466,270924,574576,1083264,2160640,4179056] BT.lf))) [5,135466,270924,574576,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,575088,1083264,2160640,4128768] BT.lf) [5,135466,270924,575088,1083264,2423372,4128768] (BT.nd BT.lf [5,135466,270924,589823,1083264,2160640,4146288] BT.lf)) [5,135466,270924,672880,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,672880,1083264,2160640,4133162] BT.lf) [5,135466,270924,672880,1083264,2160640,4146288] (BT.nd BT.lf [5,135466,270924,672880,1083264,2160640,4163456] BT.lf))) [5,135466,270924,672880,1083264,2291712,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,672880,1083264,2423372,4128768] BT.lf) [5,135466,270924,672880,1214336,2160640,4128768] (BT.nd BT.lf [5,135466,270924,672880,1218474,2160640,4128768] BT.lf)) [5,135466,270924,672888,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,135466,270924,676976,1083264,2160640,4128768] BT.lf) [5,135466,270924,677242,1083264,2160640,4146288] BT.lf)))))) [5,135466,270924,677242,1083264,2423372,4146288] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270924,677242,1218474,2160640,4146288] BT.lf) [5,135466,270924,935024,1083264,2160640] (BT.nd BT.lf [5,135466,270924,935024,1083264,2160640,4128768] BT.lf)) [5,135466,270924,948094,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [5,135466,270924,1624048,2686064,3211136,4128768] BT.lf) [5,135466,270924,4146288,4163456,4192256] (BT.nd BT.lf [5,135466,270956,541808,1083264,2160640,4128768] BT.lf))) [5,135466,270956,541808,1083264,2160640,4128800] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,270956,541808,1083264,2160640,4146288] BT.lf) [5,135466,270956,541808,1083264,2160672,4128768] (BT.nd BT.lf [5,135466,270956,541808,1083264,2423372,4128768] BT.lf)) [5,135466,270956,541808,1083264,2423404,4128768] (BT.nd (BT.nd BT.lf [5,135466,270956,541808,1083296,2160640,4128768] BT.lf) [5,135466,270956,541808,1218474,2160640,4128768] BT.lf))) [5,135466,271180,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,271948,541808,1083264,2160640,4128768] BT.lf) [5,135466,271948,541808,1083264,2160640,4129792] (BT.nd BT.lf [5,135466,271948,541808,1083264,2160640,4146288] BT.lf)) [5,135466,271948,541808,1083264,2161664,4128768] (BT.nd (BT.nd BT.lf [5,135466,271948,541808,1083264,2423372,4128768] BT.lf) [5,135466,271948,541808,1083264,2424396,4128768] (BT.nd BT.lf [5,135466,271948,541808,1218474,2160640,4128768] BT.lf))) [5,135466,271948,541808,1624048,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,271980,541808,1083264,2160640,4128768] BT.lf) [5,135466,271980,541808,1218474,2160640,4128768] (BT.nd BT.lf [5,135466,275020,541808,1083264,2160640,4128768] BT.lf)) [5,135466,275020,541808,1083264,2160640,4132864] (BT.nd (BT.nd BT.lf [5,135466,275020,541808,1083264,2160640,4146288] BT.lf) [5,135466,275020,541808,1083264,2423372,4128768] BT.lf)))) [5,135466,275020,541808,1087360,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,275020,541808,1218474,2160640,4128768] BT.lf) [5,135466,275020,545904,1083264,2160640,4128768] (BT.nd BT.lf [5,135466,275052,541808,1083264,2160640,4128768] BT.lf)) [5,135466,287308,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,135466,287308,541808,1083264,2160640,4145152] BT.lf) [5,135466,287308,541808,1083264,2160640,4146288] (BT.nd BT.lf [5,135466,287308,541808,1083264,2423372,4128768] BT.lf))) [5,135466,287308,541808,1083264,2686064,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,287308,541808,1099648,2160640,4128768] BT.lf) [5,135466,287308,541808,1218474,2160640,4128768] (BT.nd BT.lf [5,135466,287340,541808,1083264,2160640,4128768] BT.lf)) [5,135466,288332,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,135466,291404,541808,1083264,2160640,4128768] BT.lf) [5,135466,303692,541808,1083264,2160640,4128768] BT.lf))) [5,135466,303692,541808,1083264,2160640,4146288] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,303692,541808,1083264,2160640,4161536] BT.lf) [5,135466,303692,541808,1083264,2423372,4128768] (BT.nd BT.lf [5,135466,303692,541808,1218474,2160640,4128768] BT.lf)) [5,135466,303692,574576,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,135466,304716,541808,1083264,2160640,4128768] BT.lf) [5,135466,307788,541808,1083264,2160640,4128768] (BT.nd BT.lf [5,135466,307788,541808,1218474,2160640,4128768] BT.lf))) [5,135466,320076,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,326220,541808,1083264,2160640,4128768] BT.lf) [5,135466,326220,541808,1083264,4128768] (BT.nd BT.lf [5,135466,327679,541808,1083264,2423372,4128768] BT.lf)) [5,135466,393216,401996,541808,1083264,2160640] (BT.nd (BT.nd BT.lf [5,135466,393216,406382,541808,1083264,2423372] BT.lf) [5,135466,393216,541808,1083264,2160640,2423372] BT.lf))))) [5,135466,393216,541808,1083264,2423372] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,393216,541808,1083264,2423372,4128768] BT.lf) [5,135466,397610,541808,1083264,2423372,4128768] (BT.nd BT.lf [5,135466,401996,541808,1083264,2160640,4128768] BT.lf)) [5,135466,401996,541808,1083264,2160640,4133162] (BT.nd (BT.nd BT.lf [5,135466,401996,541808,1083264,2160640,4146288] BT.lf) [5,135466,401996,541808,1083264,2160640,4163456] (BT.nd BT.lf [5,135466,401996,541808,1083264,2291712,4128768] BT.lf))) [5,135466,401996,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,401996,541808,1083264,2554444,4128768] BT.lf) [5,135466,401996,541808,1214336,2160640,4128768] (BT.nd BT.lf [5,135466,401996,541808,1218474,2160640,4128768] BT.lf)) [5,135466,401996,672880,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [5,135466,402028,541808,1083264,2160640,4128768] BT.lf) [5,135466,402028,541808,1083264,2160640,4146288] BT.lf))) [5,135466,406092,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,406382,541808,1083264,2423372,4128768] BT.lf) [5,135466,406382,541808,1083264,2423372,4146288] (BT.nd BT.lf [5,135466,406382,541808,1218474,2423372,4128768] BT.lf)) [5,135466,406382,812668,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [5,135466,541808,786432,1083264,2423372,4128768] BT.lf) [5,135466,541808,795212,1083264,2423372,4128768] (BT.nd BT.lf [5,135466,541808,803952,1083264,2423372,4128768] BT.lf))) [5,135466,541808,812668,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,541808,812668,1083264,2423372,4146288] BT.lf) [5,135466,541808,812668,1218474,2423372,4128768] (BT.nd BT.lf [5,135466,541808,948094,1083264,2423372,4128768] BT.lf)) [5,135466,541808,983167,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [5,135466,541808,1083264,1310720,2423372,4128768] BT.lf) [5,135466,541808,1083264,1319500,2423372,4128768] BT.lf)))) [5,135466,541808,1083264,1345408,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,541808,1083264,1353676,2423372,4128768] BT.lf) [5,135466,541808,1083264,1353676,2423372,4146288] (BT.nd BT.lf [5,135466,541808,1083264,1488878,2423372,4128768] BT.lf)) [5,135466,541808,1083264,1508239,2423372,4128768] (BT.nd (BT.nd BT.lf [5,135466,541808,1083264,1894396,2423372,4128768] BT.lf) [5,135466,541808,1083264,1902293,2423372,4128768] (BT.nd BT.lf [5,135466,541808,1083264,2031616,2033663,2423372] BT.lf))) [5,135466,541808,1083264,2031616,2160640,2423372] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,541808,1083264,2031616,2423372] BT.lf) [5,135466,541808,1083264,2031616,2423372,4128768] (BT.nd BT.lf [5,135466,541808,1083264,2033663,2423372,4128768] BT.lf)) [5,135466,541808,1083264,2033663,2423372,4146288] (BT.nd (BT.nd BT.lf [5,135466,541808,1083264,2033663,2423372,4192256] BT.lf) [5,135466,541808,1083264,2037759,2423372,4128768] BT.lf))) [5,135466,541808,1083264,2041855,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,541808,1083264,2050047,2423372,4128768] BT.lf) [5,135466,541808,1083264,2066431,2423372,4128768] (BT.nd BT.lf [5,135466,541808,1083264,2097151,2423372,4128768] BT.lf)) [5,135466,541808,1083264,2162687,2423372] (BT.nd (BT.nd BT.lf [5,135466,541808,1218474,1353676,2423372,4128768] BT.lf) [5,135466,541808,1218474,1488878,2423372,4128768] (BT.nd BT.lf [5,135466,541808,1218474,2033663,2423372,4128768] BT.lf))) [5,135466,541808,1345408,2160640,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,135466,541808,1345408,2423372,4128768] BT.lf) [5,135466,541808,1353676,1624048,2423372,4128768] (BT.nd BT.lf [5,135466,541808,1353676,2423372,4128768,4163456] BT.lf)) [5,135466,541808,1353676,2423372,4163456] (BT.nd (BT.nd BT.lf [5,135466,541808,2423372,3180416,4128768] BT.lf) [5,135466,677242,812668,1083264,2423372,4128768] BT.lf)))))))) [5,135466,803952,1083264,2160640,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,135466,803952,1083264,2423372,4128768] BT.lf) [5,135466,812668,1083264,1353676,2160640,4146288] (BT.nd BT.lf [5,135466,812668,1083264,1624048,2423372,4128768] BT.lf)) [5,135466,812668,1083264,2160640,2423372,4146288] (BT.nd (BT.nd BT.lf [5,135466,812668,1083264,2423372,4128768,4146288] BT.lf) [5,135466,812668,1083264,2423372,4146288] (BT.nd BT.lf [5,135466,812668,1353676,1624048,2160640,4128768] BT.lf))) [5,135466,1083264,2423372,2638960,4128768] (BT.nd (BT.nd (BT.nd BT.lf [5,136490,271948,541808,1083264,2160640,4128768] BT.lf) [5,168234,303692,541808,1083264,2160640,4128768] (BT.nd BT.lf [5,397610,541808,1083264,2160640,2423372,4128768] BT.lf)) [5,397610,541808,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [5,406382,541808,677242,1083264,2423372,4128768] BT.lf) [5,406382,541808,1083264,1218474,2423372,4128768] BT.lf))) [5,406382,541808,1083264,2160640,4133162,4137548] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,406382,541808,1083264,2423372,4128768,4133162] BT.lf) [5,406382,541808,1218474,2423372,4128768] (BT.nd BT.lf [5,406382,677242,812668,1083264,2160640,4128768] BT.lf)) [5,541808,1083264,2232618,2423372,4128768] (BT.nd (BT.nd BT.lf [5,541808,1218474,1353676,2423372,4128768] BT.lf) [5,541808,1218474,2423372,3211136,4128768] (BT.nd BT.lf [6,0,135466,270924,541808,1083264,2160640,4128768] BT.lf))) [6,8,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,8,135466,270924,541808,1083264,2160640,4128776] BT.lf) [6,8,135466,270924,541808,1083264,2160640,4146288] (BT.nd BT.lf [6,8,135466,270924,541808,1083264,2160648,4128768] BT.lf)) [6,8,135466,270924,541808,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [6,8,135466,270924,541816,1083264,2160640,4128768] BT.lf) [6,32,135466,270924,541808,1083264,2160640,4128768] BT.lf)))) [6,32,135466,270924,541808,1083264,2160640,4128800] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,32,135466,270924,541808,1083264,2160640,4146288] BT.lf) [6,32,135466,270924,541808,1083264,2160672,4128768] (BT.nd BT.lf [6,32,135466,270924,541808,1083264,2423372,4128768] BT.lf)) [6,32,135466,270924,541808,1083296,2160640,4128768] (BT.nd (BT.nd BT.lf [6,32,135466,270924,541808,1218474,2160640,4128768] BT.lf) [6,32,135466,270956,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,40,135466,270924,541808,1083264,2160640,4128768] BT.lf))) [6,96,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,256,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,256,135466,270924,541808,1083264,2160640,4146288] (BT.nd BT.lf [6,256,135466,270924,541808,1083264,2423372,4128768] BT.lf)) [6,256,135466,270924,541808,1218474,2160640,4128768] (BT.nd (BT.nd BT.lf [6,264,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,288,135466,270924,541808,1083264,2160640,4128768] BT.lf))) [6,512,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,512,135466,270924,541808,1083264,2160640,4129280] BT.lf) [6,512,135466,270924,541808,1083264,2160640,4146288] (BT.nd BT.lf [6,512,135466,270924,541808,1083264,2161152,4128768] BT.lf)) [6,512,135466,270924,541808,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [6,512,135466,270924,541808,1218474,2160640,4128768] BT.lf) [6,512,135466,270924,542320,1083264,2160640,4128768] (BT.nd BT.lf [6,512,135978,270924,541808,1083264,2160640,4128768] BT.lf))) [6,520,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,520,135466,270924,541808,1218474,2160640,4128768] BT.lf) [6,576,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,768,135466,270924,541808,1083264,2160640,4128768] BT.lf)) [6,1024,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,1024,135466,270924,541808,1083264,2160640,4129792] BT.lf) [6,1024,135466,270924,541808,1083264,2160640,4146288] BT.lf))))) [6,1024,135466,270924,541808,1083264,2161664,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1024,135466,270924,541808,1083264,2423372,4128768] BT.lf) [6,1024,135466,270924,541808,1218474,2160640,4128768] (BT.nd BT.lf [6,1024,135466,270924,541808,1624048,2160640,4128768] BT.lf)) [6,1024,135466,271948,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,1024,136490,270924,541808,1083264,2160640,4128768] BT.lf) [6,1056,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,1056,135466,270924,541808,1218474,2160640,4128768] BT.lf))) [6,1088,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,1280,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,1536,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,2047,135466,270924,541808,1083264,2160640] BT.lf)) [6,2047,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,2047,135466,270924,541808,1083264,4128768] BT.lf) [6,4352,135466,270924,541808,1083264,2160640,4128768] BT.lf))) [6,4394,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,17408,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,17520,65535,135466,270924,1083264,2160640] (BT.nd BT.lf [6,17520,65535,135466,270924,1083264,2160640,4128768] BT.lf)) [6,17520,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,17520,135466,270924,1083264,2160640,4128768] BT.lf) [6,32768,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,32768,135466,270924,541808,1083264,2160640,4146288] BT.lf))) [6,32768,135466,270924,541808,1083264,2160640,4161536] (BT.nd (BT.nd (BT.nd BT.lf [6,32768,135466,270924,541808,1083264,2423372,4128768] BT.lf) [6,32768,135466,270924,574576,1083264,2160640,4128768] (BT.nd BT.lf [6,32768,135466,303692,541808,1083264,2160640,4128768] BT.lf)) [6,33024,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,33280,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,33280,135466,270924,541808,1083264,2423372,4128768] BT.lf)))) [6,33792,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,34688,65535,135466,270924,541808,2160640] BT.lf) [6,34688,65535,135466,270924,541808,2160640,4128768] (BT.nd BT.lf [6,34688,135466,270924,541808,1083264,2160640,4128768] BT.lf)) [6,34688,135466,270924,541808,2160640,4128768] (BT.nd (BT.nd BT.lf [6,48015,135466,270924,541808,1083264,2160640] BT.lf) [6,48015,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,48015,135466,270924,541808,1083264,2160640,4146288] BT.lf))) [6,48015,135466,270924,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,56755,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,65535,135466,270924,541808,1083264,2033663] (BT.nd BT.lf [6,65535,135466,270924,541808,1083264,2160640] BT.lf)) [6,65535,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,65535,135466,270924,541808,1083264,2160640,4146288] BT.lf) [6,65535,135466,270924,541808,1083264,2423372] BT.lf))) [6,65535,135466,270924,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,135466,270924,541808,1083264,4128768,4192256] BT.lf) [6,65535,135466,270924,541808,1083264,4192256] (BT.nd BT.lf [6,65535,135466,270924,1083264,2160640,3652495] BT.lf)) [6,65535,135466,270924,1083264,2160640,4128768,4146288] (BT.nd (BT.nd BT.lf [6,65535,135466,270924,1083264,2160640,4146288] BT.lf) [6,65535,135466,541808,1083264,2160640,2423372] (BT.nd BT.lf [6,65535,135466,541808,1083264,2160640,3923379] BT.lf))) [6,131072,135466,262144,270924,541808,1083264,2160640] (BT.nd (BT.nd (BT.nd BT.lf [6,131072,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,131072,135466,270924,541808,1083264,2160640,4133162] (BT.nd BT.lf [6,131072,135466,270924,541808,1083264,2160640,4146288] BT.lf)) [6,131072,135466,270924,541808,1083264,2160640,4163456] (BT.nd (BT.nd BT.lf [6,131072,135466,270924,541808,1083264,2291712,4128768] BT.lf) [6,131072,135466,270924,541808,1083264,2423372,4128768] BT.lf)))))) [6,131072,135466,270924,541808,1214336,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,131072,135466,270924,541808,1218474,2160640,4128768] BT.lf) [6,131072,135466,270924,672880,1083264,2160640,4128768] (BT.nd BT.lf [6,131072,135466,401996,541808,1083264,2160640,4128768] BT.lf)) [6,131072,270924,541808,1083264,1218474,2160640,4128768] (BT.nd (BT.nd BT.lf [6,131072,270924,541808,1218474,2160640,4128768] BT.lf) [6,131080,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,131104,135466,270924,541808,1083264,2160640,4128768] BT.lf))) [6,131104,135466,270924,541808,1083264,2160640,4146288] (BT.nd (BT.nd (BT.nd BT.lf [6,131328,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,131370,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135168,135466,270924,541808,1083264,2160640,4128768] BT.lf)) [6,135210,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135210,270924,541808,1083264,2160640,3111039,4128768] BT.lf) [6,135210,270924,541808,1083264,2160640,4128768] BT.lf))) [6,135210,270924,541808,2160640,3111039,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135434,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,135458,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,135466,270924,541808,1083264,2160640,4128768] BT.lf)) [6,135466,135466,270924,541808,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [6,135466,135466,270924,541808,1083264,2423372,4128768] BT.lf) [6,135466,135466,270924,541808,1218474,2160640,4128768] (BT.nd BT.lf [6,135466,135530,270924,541808,1083264,2160640,4128768] BT.lf))) [6,135466,135978,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,136490,270924,541808,1083264,2160640,4128768] BT.lf) [6,135466,143658,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,151850,270924,541808,1083264,2160640,4128768] BT.lf)) [6,135466,168234,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,196607,270924,541808,1083264,2160640,4128768] BT.lf) [6,135466,270924,393216,406382,541808,1083264,2160640] BT.lf)))) [6,135466,270924,393216,541808,1083264,2160640] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,393216,541808,1083264,2160640,4128768] BT.lf) [6,135466,270924,397610,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,406382,541808,1083264,2160640,4128768] BT.lf)) [6,135466,270924,406382,541808,1083264,2160640,4146288] (BT.nd (BT.nd BT.lf [6,135466,270924,406382,541808,1083264,2423372,4128768] BT.lf) [6,135466,270924,524288,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,524288,541808,1083264,2160640,4146288] BT.lf))) [6,135466,270924,524288,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,524320,541808,1083264,2160640,4128768] BT.lf) [6,135466,270924,525312,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,525424,541808,1083264,2160640,4128768] BT.lf)) [6,135466,270924,541744,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,541808,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,541808,1083264,2160640,4146288] BT.lf))) [6,135466,270924,541808,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,541816,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,542064,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,542320,1083264,2160640,4128768] BT.lf)) [6,135466,270924,541808,574576,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,589823,1083264,2160640] BT.lf) [6,135466,270924,541808,589823,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,655360,1083264,2160640,4128768] BT.lf))) [6,135466,270924,541808,659754,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,672880,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,677242,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,677242,1083264,2160640,4146288] BT.lf)) [6,135466,270924,541808,677242,1083264,2423372,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,677242,1218474,2160640,4128768] BT.lf) [6,135466,270924,541808,948094,1083264,2160640,4128768] BT.lf))))) [6,135466,270924,541808,983167,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1048576,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,1048576,1083264,2160640,4146288] (BT.nd BT.lf [6,135466,270924,541808,1048576,1083264,2423372,4128768] BT.lf)) [6,135466,270924,541808,1048576,1218474,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1048832,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,1049088,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1049600,1083264,2160640,4128768] BT.lf))) [6,135466,270924,541808,1049600,1083264,2160640,4146288] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1050496,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,1081344,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1082240,1083264,2160640,4128768] BT.lf)) [6,135466,270924,541808,1082752,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083008,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,1083008,2160640,4058837,4128768] BT.lf))) [6,135466,270924,541808,1083008,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1083264,2160640,4146288] (BT.nd BT.lf [6,135466,270924,541808,1083264,1083264,2423372,4128768] BT.lf)) [6,135466,270924,541808,1083264,1083272,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1083296,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1083328,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,1087360,2160640,4128768] BT.lf))) [6,135466,270924,541808,1083264,1091456,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1099648,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1114111,2160640] (BT.nd BT.lf [6,135466,270924,541808,1083264,1114111,2160640,4128768] BT.lf)) [6,135466,270924,541808,1083264,1179648,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1184042,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1214336,2160640,4128768] BT.lf)))) [6,135466,270924,541808,1083264,1218474,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1218474,2160640,4146288] BT.lf) [6,135466,270924,541808,1083264,1218474,2423372,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,1310720,2160640,4128768] BT.lf)) [6,135466,270924,541808,1083264,1319500,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1345408,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1353676,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,1353676,2160640,4146288] BT.lf))) [6,135466,270924,541808,1083264,1353676,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1488878,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1508239,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,1572864,2160640,4128768] BT.lf)) [6,135466,270924,541808,1083264,1590384,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1607552,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,1624048,2160640,4128768] BT.lf))) [6,135466,270924,541808,1083264,1624048,2160640,4146288] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1624048,2423372,4128768] BT.lf) [6,135466,270924,541808,1083264,1759226,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,1770931,2160640,4128768] BT.lf)) [6,135466,270924,541808,1083264,1770931,2423372,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,1770931,4128768] BT.lf) [6,135466,270924,541808,1083264,1894396,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,1902293,2160640,4128768] BT.lf))) [6,135466,270924,541808,1083264,2031616,2033663] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2031616,2033663,2160640] BT.lf) [6,135466,270924,541808,1083264,2031616,2160640] (BT.nd BT.lf [6,135466,270924,541808,1083264,2031616,2160640,4128768] BT.lf)) [6,135466,270924,541808,1083264,2033663,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2033663,2160640,4146288] BT.lf) [6,135466,270924,541808,1083264,2033663,2160640,4192256] BT.lf))))))) [6,135466,270924,541808,1083264,2033663,2423372,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2033663,4128768] BT.lf) [6,135466,270924,541808,1083264,2033663,4146288] (BT.nd BT.lf [6,135466,270924,541808,1083264,2033663,4163456] BT.lf)) [6,135466,270924,541808,1083264,2033663,4192256] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2037759,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,2041855,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2041855,4128768] BT.lf))) [6,135466,270924,541808,1083264,2050047,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2066431,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,2097151,2160640,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3145728,4128768] BT.lf)) [6,135466,270924,541808,1083264,2160640,3180416,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3211136,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,3211136,4146288] BT.lf))) [6,135466,270924,541808,1083264,2160640,3342250,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3381635,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,3604480] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3604480,3652495] BT.lf)) [6,135466,270924,541808,1083264,2160640,3604480,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3652495,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,3652495,4146288] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3652527,4128768] BT.lf))) [6,135466,270924,541808,1083264,2160640,3653519,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3670015,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,3735536,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3787921,4128768] BT.lf)) [6,135466,270924,541808,1083264,2160640,3866624,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3923379,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,3923379,4146288] BT.lf)))) [6,135466,270924,541808,1083264,2160640,3923387,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3923443,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,3923891,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,3931571,4128768] BT.lf)) [6,135466,270924,541808,1083264,2160640,3932159,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4128776] BT.lf))) [6,135466,270924,541808,1083264,2160640,4128768,4128800] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4129024] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4129280] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4129792] BT.lf)) [6,135466,270924,541808,1083264,2160640,4128768,4130815] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4133162] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4141934] BT.lf))) [6,135466,270924,541808,1083264,2160640,4128768,4146288] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4150650] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4161535] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4161536] BT.lf)) [6,135466,270924,541808,1083264,2160640,4128768,4163456] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4167594] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4171724] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4176783] BT.lf))) [6,135466,270924,541808,1083264,2160640,4128768,4177919] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4179952] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4185523] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4186111] BT.lf)) [6,135466,270924,541808,1083264,2160640,4128768,4190207] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4194176] BT.lf) [6,135466,270924,541808,1083264,2160640,4128768,4194239] BT.lf))))) [6,135466,270924,541808,1083264,2160640,4128768,4194295] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128768,4194303] BT.lf) [6,135466,270924,541808,1083264,2160640,4128776] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4128800] BT.lf)) [6,135466,270924,541808,1083264,2160640,4129024] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4129280] BT.lf) [6,135466,270924,541808,1083264,2160640,4129792] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4133162,4137548] BT.lf))) [6,135466,270924,541808,1083264,2160640,4133162,4146288] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4133162,4192256] BT.lf) [6,135466,270924,541808,1083264,2160640,4146288] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4146288,4146288] BT.lf)) [6,135466,270924,541808,1083264,2160640,4146288,4150650] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4146288,4163456] BT.lf) [6,135466,270924,541808,1083264,2160640,4146288,4179952] BT.lf))) [6,135466,270924,541808,1083264,2160640,4161536] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4163456] BT.lf) [6,135466,270924,541808,1083264,2160640,4163456,4192256] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160640,4179952] BT.lf)) [6,135466,270924,541808,1083264,2160640,4194176] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2160648,4128768] BT.lf) [6,135466,270924,541808,1083264,2160672,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2160704,4128768] BT.lf))) [6,135466,270924,541808,1083264,2160896,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2161152,4128768] BT.lf) [6,135466,270924,541808,1083264,2161664,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2291712,4128768] BT.lf)) [6,135466,270924,541808,1083264,2292010,2423372,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2292010,2686064,4128768] BT.lf) [6,135466,270924,541808,1083264,2292010,4128768,4192256] BT.lf)))) [6,135466,270924,541808,1083264,2292010,4192256] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2359296,2423372,4128768] BT.lf) [6,135466,270924,541808,1083264,2422784,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,2423372,4128768] BT.lf)) [6,135466,270924,541808,1083264,2423372,2554734,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,2686064,4128768] BT.lf) [6,135466,270924,541808,1083264,2423372,2948732,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,3111039,4128768] BT.lf))) [6,135466,270924,541808,1083264,2423372,3211136,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,3473356,4128768] BT.lf) [6,135466,270924,541808,1083264,2423372,3652495,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,3923379,4128768] BT.lf)) [6,135466,270924,541808,1083264,2423372,4058837,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,4128768] BT.lf) [6,135466,270924,541808,1083264,2423372,4128768,4128768] BT.lf))) [6,135466,270924,541808,1083264,2423372,4128768,4133162] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,4128768,4137548] BT.lf) [6,135466,270924,541808,1083264,2423372,4128768,4146288] (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,4128768,4163456] BT.lf)) [6,135466,270924,541808,1083264,2423372,4128768,4192256] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,4128768,4192844] BT.lf) [6,135466,270924,541808,1083264,2423372,4146288] (BT.nd BT.lf [6,135466,270924,541808,1083264,2423372,4163456] BT.lf))) [6,135466,270924,541808,1083264,2684928,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,2686064,3211136,4128768] BT.lf) [6,135466,270924,541808,1083264,3209216,4128768] (BT.nd BT.lf [6,135466,270924,541808,1083264,4128768,4130815] BT.lf)) [6,135466,270924,541808,1083264,4128768,4192256] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1083264,4128768,4192844] BT.lf) [6,135466,270924,541808,1083264,4133162,4192256] BT.lf)))))) [6,135466,270924,541808,1218474,2033663,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,541808,1218474,2423372,4128768] BT.lf) [6,135466,270924,541808,1218474,4128768,4192256] (BT.nd BT.lf [6,135466,270924,541808,2033663,3111039,4128768] BT.lf)) [6,135466,270924,541808,2033663,4128768,4163456] (BT.nd (BT.nd BT.lf [6,135466,270924,541808,4128768,4163456,4192256] BT.lf) [6,135466,270924,541816,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,542064,1083264,2160640,4128768] BT.lf))) [6,135466,270924,542320,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,574576,1083264,2160640,4128768] BT.lf) [6,135466,270924,672880,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,270924,677242,812668,1083264,2160640,4128768] BT.lf)) [6,135466,270924,677242,1083264,2160640,2686064,4128768] (BT.nd (BT.nd BT.lf [6,135466,270924,677242,1083264,2160640,4128768,4146288] BT.lf) [6,135466,270924,677242,1083264,2160640,4146288] BT.lf))) [6,135466,270924,1083264,1590384,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,1083264,1624048,2160640,2686064,4128768] BT.lf) [6,135466,270924,1083264,2033663,3652495,4128768] (BT.nd BT.lf [6,135466,270924,1083264,2033663,4128768,4146288] BT.lf)) [6,135466,270924,1083264,2160640,3604480,3652495] (BT.nd (BT.nd BT.lf [6,135466,270924,1083264,2160640,3652495,4128768] BT.lf) [6,135466,270924,1083264,2160640,3652495,4146288] (BT.nd BT.lf [6,135466,270924,1083264,2160640,3652495,4163456] BT.lf))) [6,135466,270924,1083264,2160640,4128768,4146288] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,270924,1083264,2160640,4128768,4176783] BT.lf) [6,135466,270924,1083264,2160640,4133162,4146288] (BT.nd BT.lf [6,135466,270924,1083264,2423372,3652495,4128768] BT.lf)) [6,135466,270924,1083264,2423372,4128768,4146288] (BT.nd (BT.nd BT.lf [6,135466,270924,1083264,3652495,4128768,4192256] BT.lf) [6,135466,270924,1083264,4128768,4146288,4192256] BT.lf)))) [6,135466,270956,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,271180,541808,1083264,2160640,4128768] BT.lf) [6,135466,271948,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,275020,541808,1083264,2160640,4128768] BT.lf)) [6,135466,287308,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,303692,541808,1083264,2160640,4128768] BT.lf) [6,135466,401996,541808,1083264,2160640,4128768] (BT.nd BT.lf [6,135466,406382,541808,812668,1083264,2160640,4128768] BT.lf))) [6,135466,406382,541808,1083264,2160640,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,406382,541808,1083264,2160640,4128768,4137548] BT.lf) [6,135466,406382,541808,1083264,2423372,4128768] (BT.nd BT.lf [6,135466,541808,795212,1083264,2160640,4128768] BT.lf)) [6,135466,541808,812668,1083264,1353676,2160640,4128768] (BT.nd (BT.nd BT.lf [6,135466,541808,812668,1083264,2160640,2423372,4128768] BT.lf) [6,135466,541808,812668,1083264,2423372,4128768] BT.lf))) [6,135466,541808,1083264,1319500,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,541808,1083264,1353676,2160640,2423372,4128768] BT.lf) [6,135466,541808,1083264,1353676,2423372,4128768] (BT.nd BT.lf [6,135466,541808,1083264,1770931,2160640,4128768] BT.lf)) [6,135466,541808,1083264,2033663,2160640,2423372,4128768] (BT.nd (BT.nd BT.lf [6,135466,541808,1083264,2033663,2423372,4128768] BT.lf) [6,135466,541808,1083264,2033663,3923379,4128768] (BT.nd BT.lf [6,135466,541808,1083264,2097152,2423372,4128768] BT.lf))) [6,135466,541808,1083264,2152448,3923379,4128768] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,541808,1083264,2160640,2368076,4128768] BT.lf) [6,135466,541808,1083264,2160640,2423372,4128768] (BT.nd BT.lf [6,135466,541808,1083264,2160640,2423372,4146288] BT.lf)) [6,135466,541808,1083264,2160640,2423372,4163456] (BT.nd (BT.nd BT.lf [6,135466,541808,1083264,2160640,2423372,4192256] BT.lf) [6,135466,541808,1083264,2160640,3923379,4128768] BT.lf))))) [6,135466,541808,1083264,2160640,3923379,4146288] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,541808,1083264,2160640,3923379,4163456] BT.lf) [6,135466,541808,1083264,2160640,3923379,4192256] (BT.nd BT.lf [6,135466,541808,1083264,2160640,3931571,4128768] BT.lf)) [6,135466,541808,1083264,2292010,2423372,4128768] (BT.nd (BT.nd BT.lf [6,135466,541808,1083264,2423372,2686064,4128768] BT.lf) [6,135466,541808,1083264,2423372,3211136,4128768] (BT.nd BT.lf [6,135466,541808,1083264,2423372,3923379,4128768] BT.lf))) [6,135466,541808,1083264,3923379,4128768,4192256] (BT.nd (BT.nd (BT.nd BT.lf [6,135466,541808,1218474,2160640,2423372,4128768] BT.lf) [6,135466,541808,1218474,2160640,3923379,4128768] (BT.nd BT.lf [6,135466,541808,2160640,2423372,3111039,4128768] BT.lf)) [6,135466,541808,2160640,2423372,4128768,4163456] (BT.nd (BT.nd BT.lf [6,135466,541808,2160640,3111039,3923379,4128768] BT.lf) [6,135466,541808,2160640,3923379,4128768,4163456] BT.lf))) [6,135466,1083264,2160640,2423372,3652495,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,135466,1083264,2160640,2423372,4128768,4146288] BT.lf) [6,135466,1083264,2160640,3652495,3923379,4128768] (BT.nd BT.lf [6,135466,1083264,2160640,3923379,4128768,4146288] BT.lf)) [6,541808,1083264,1218474,2160640,2423372,4128768] (BT.nd (BT.nd BT.lf [6,541808,1083264,1218474,2160640,3923379,4128768] BT.lf) [6,541808,1083264,2160640,3923379,4058837,4128768] (BT.nd BT.lf [7,8,135466,270924,541808,1083264,2160640,4128768] BT.lf))) [7,32,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [7,256,135466,270924,541808,1083264,2160640,4128768] BT.lf) [7,512,135466,270924,541808,1083264,2160640,4128768] (BT.nd BT.lf [7,1024,135466,270924,541808,1083264,2160640,4128768] BT.lf)) [7,32768,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [7,65535,135466,270924,541808,1083264,2160640] BT.lf) [7,65535,135466,270924,541808,1083264,2160640,4128768] BT.lf)))) [7,131072,135466,270924,541808,1083264,2160640,4128768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,135466,135466,270924,541808,1083264,2160640,4128768] BT.lf) [7,135466,270924,406382,541808,1083264,2160640,4128768] (BT.nd BT.lf [7,135466,270924,524288,541808,1083264,2160640,4128768] BT.lf)) [7,135466,270924,541808,541808,1083264,2160640,4128768] (BT.nd (BT.nd BT.lf [7,135466,270924,541808,677242,1083264,2160640,4128768] BT.lf) [7,135466,270924,541808,1048576,1083264,2160640,4128768] (BT.nd BT.lf [7,135466,270924,541808,1083264,1083264,2160640,4128768] BT.lf))) [7,135466,270924,541808,1083264,1218474,2160640,4128768] (BT.nd (BT.nd (BT.nd BT.lf [7,135466,270924,541808,1083264,1353676,2160640,4128768] BT.lf) [7,135466,270924,541808,1083264,1624048,2160640,4128768] (BT.nd BT.lf [7,135466,270924,541808,1083264,2033663,2160640,4128768] BT.lf)) [7,135466,270924,541808,1083264,2033663,4128768] (BT.nd (BT.nd BT.lf [7,135466,270924,541808,1083264,2160640,3211136,4128768] BT.lf) [7,135466,270924,541808,1083264,2160640,3652495,4128768] BT.lf))) [7,135466,270924,541808,1083264,2160640,3923379,4128768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,135466,270924,541808,1083264,2160640,4128768] BT.lf) [7,135466,270924,541808,1083264,2160640,4128768,4128768] (BT.nd BT.lf [7,135466,270924,541808,1083264,2160640,4128768,4133162] BT.lf)) [7,135466,270924,541808,1083264,2160640,4128768,4146288] (BT.nd (BT.nd BT.lf [7,135466,270924,541808,1083264,2160640,4128768,4163456] BT.lf) [7,135466,270924,541808,1083264,2160640,4146288] (BT.nd BT.lf [7,135466,270924,541808,1083264,2160640,4163456] BT.lf))) [7,135466,270924,541808,1083264,2423372,4128768] (BT.nd (BT.nd (BT.nd BT.lf [7,135466,270924,541808,1083264,4128768,4192256] BT.lf) [7,135466,270924,1083264,2160640,3652495,4128768] (BT.nd BT.lf [7,135466,270924,1083264,2160640,4128768,4146288] BT.lf)) [7,135466,541808,1083264,2160640,2423372,4128768] (BT.nd (BT.nd BT.lf [7,135466,541808,1083264,2160640,3923379,4128768] BT.lf) [8,135466,270924,541808,1083264,2160640,4128768] BT.lf)))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,169898,326220,4146288],[]),([2,541808,1480618,2554444],[]),([2,672880,1480618,2423372],[]),([2,935024,1218474,2423372],[]),([2,935024,1218474,2554444],[]),([2,1000560,1218474,2423372],[]),([3,34688,135466,326220,4146288],[]),([3,131072,541808,1480618,2423372],[]),([3,131072,803952,1218474,2423372],[(96,0)]),([3,135466,541808,1345408,2554444],[]),([3,135466,541808,1476480,2554444],[]),([3,135466,672880,1345408,2423372],[]),([3,135466,803952,1083264,2554444],[(72,0)]),([3,135466,935024,1083264,2423372],[]),([3,135466,935024,1083264,2554444],[]),([3,135466,935024,1218474,2423372],[]),([3,135466,935024,1476480,2423372],[(72,0)]),([3,135466,1000560,1083264,2423372],[]),([3,169898,326220,541808,4128768],[]),([3,393216,541808,1218474,2423372],[]),([3,393216,541808,1218474,2554444],[]),([3,393216,935024,1218474,2423372],[(72,0)]),([3,393312,541808,1218474,2423372],[]),([3,397610,541808,1083264,2554444],[]),([3,397610,672880,1083264,2423372],[]),([3,397610,935024,1083264,2423372],[(72,0)]),([3,406382,935024,1218474,2423372],[]),([3,541808,917504,1218474,2423372],[]),([3,541808,935024,1218474,2423372],[]),([3,541808,983040,1218474,2423372],[]),([3,935024,1083264,1218474,2423372],[]),([3,935024,1218474,2423372],[]),([3,935024,1218474,2423372,4128768],[]),([3,948094,1218474,2423372,4146288],[]),([4,17520,135466,326220,1083264,4128768],[]),([4,34688,63488,135466,270924,4146288],[(72,0)]),([4,34688,135466,326220,541808,4128768],[]),([4,65535,135466,326220,1083264,4146288],[]),([4,131072,135466,541808,1345408,2423372],[]),([4,131072,135466,803952,1083264,2423372],[]),([4,131072,262144,541808,1218474,2423372],[(72,0),(128,0)]),([4,131072,270924,541808,1480618,2160640],[(56,0),(72,0),(128,0)]),([4,131072,270924,803952,1218474,2160640],[(56,0),(72,0),(128,0)]),([4,131072,397610,541808,1083264,2423372],[]),([4,135466,270924,541808,1345408,2291712],[(96,0)]),([4,135466,270924,541808,1476480,2553856],[(96,0)]),([4,135466,270924,672880,1345408,2160640],[(96,0)]),([4,135466,270924,935024,1083264,2160640],[(96,0)]),([4,135466,270924,935024,1083264,2423372],[(96,0)]),([4,135466,270924,935024,1083264,2553856],[(96,0)]),([4,135466,270924,1000560,1083264,2160640],[(96,0)]),([4,135466,270924,1099648,2686064,4146288],[]),([4,135466,270924,1099712,2686064,4128768],[]),([4,135466,270924,1099712,2948732,4128768],[]),([4,135466,271948,1624048,2160640,4146288],[]),([4,135466,271980,1624048,2160640,4128768],[]),([4,135466,271980,1759226,2160640,4128768],[]),([4,135466,287308,1083264,2686064,4146288],[]),([4,135466,288332,1083264,2160640,4146288],[]),([4,135466,324172,541808,1083264,4128768],[]),([4,135466,324172,541808,1218474,4128768],[]),([4,135466,326220,541808,1083264,4128768],[]),([4,135466,326220,541808,1083264,4146288],[]),([4,135466,326220,541808,1218474,4128768],[]),([4,135466,327679,1083264,2423372,4146288],[]),([4,135466,393216,541808,1083264,2423372],[]),([4,135466,393216,541808,1083264,2554444],[]),([4,135466,393216,541808,1218474,2423372],[]),([4,135466,393216,541808,1476480,2423372],[(96,0)]),([4,135466,393216,935024,1083264,2423372],[]),([4,135466,393312,541808,1083264,2423372],[]),([4,135466,401996,541808,1345408,2160640],[(96,0)]),([4,135466,401996,541808,1476480,2160640],[(96,0)]),([4,135466,401996,803952,1083264,2160640],[(96,0)]),([4,135466,401996,935024,1083264,2160640],[(96,0)]),([4,135466,406382,935024,1083264,2423372],[]),([4,135466,541808,917504,1083264,2423372],[]),([4,135466,541808,935024,1083264,2423372],[]),([4,135466,541808,983040,1083264,2423372],[]),([4,135466,541808,1083264,1441792,2423372],[]),([4,135466,541808,1083264,1507328,2423372],[]),([4,135466,541808,1083264,2031616,2423372],[]),([4,135466,541808,1083264,2032752,2423372],[]),([4,135466,541808,1083264,2049136,2423372],[]),([4,135466,541808,1218474,1441792,2423372],[]),([4,135466,541808,1218474,2031616,2423372],[]),([4,135466,541808,1345408,2423372,4128768],[]),([4,135466,541808,1345408,2423372,4137548],[]),([4,135466,541808,1345408,2423372,4146288],[]),([4,135466,541808,1345408,2423372,4192256],[]),([4,135466,541808,1345408,2423372,4192844],[])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,135466,541808,1345416,2423372,4128768],[]),([4,135466,541808,1345472,2423372,4128768],[]),([4,135466,541808,1345472,2423372,4146288],[]),([4,135466,541808,1353676,2423372,4162048],[]),([4,135466,541808,1476480,2423372,4128768],[]),([4,135466,541808,1480618,2423372,4128768],[]),([4,135466,575088,1353676,2423372,4128768],[]),([4,135466,803952,1083264,2423372,4128768],[]),([4,135466,803952,1083264,2423372,4137548],[]),([4,135466,803952,1083264,2423372,4146288],[]),([4,135466,803952,1083264,2423372,4192256],[]),([4,135466,803952,1083264,2423372,4192844],[]),([4,135466,803952,1218474,2423372,4128768],[]),([4,135466,803952,1345408,2423372,4128768],[]),([4,135466,803960,1083264,2423372,4128768],[]),([4,135466,804464,1083264,2423372,4128768],[]),([4,135466,812668,1083264,2422848,4146288],[]),([4,135466,812668,1083264,2423372,4145216],[]),([4,135466,812668,1083264,2423372,4146288],[]),([4,135466,812668,1099712,2423372,4128768],[]),([4,135466,812668,1218474,2423372,4146288],[]),([4,135466,812668,1345472,2160640,4146288],[]),([4,135466,935024,1083264,2160640,2423372],[(72,0)]),([4,135466,935024,1083264,2423372],[]),([4,135466,935024,1083264,2423372,4128768],[]),([4,135466,948094,1083264,2423372,4146288],[]),([4,151914,812668,1083264,2423372,4128768],[]),([4,168746,541808,1353676,2423372,4128768],[]),([4,393216,397610,541808,1083264,2423372],[(104,0)]),([4,393216,406382,541808,1218474,2423372],[]),([4,393216,541808,1083264,1218474,2423372],[]),([4,393216,541808,1218474,2423372],[(74,0)]),([4,393216,541808,1218474,2423372,4128768],[]),([4,397610,401996,541808,1083264,2160640],[(96,0)]),([4,397610,541808,1083264,2423372,4128768],[]),([4,397610,541808,1083264,2423372,4137548],[]),([4,397610,541808,1083264,2423372,4146288],[]),([4,397610,541808,1083264,2423372,4192256],[]),([4,397610,541808,1083264,2423372,4192844],[]),([4,397610,541808,1218474,2423372,4128768],[]),([4,397610,541808,1345408,2423372,4128768],[]),([4,397610,541808,1480618,2423372,4128768],[(132,0)]),([4,397610,803952,1083264,2423372,4128768],[]),([4,397674,541808,1083264,2423372,4128768],[]),([4,397674,541808,1083264,2423372,4146288],[]),([4,397674,812668,1083264,2160640,4146288],[]),([4,398122,541808,1083264,2423372,4128768],[]),([4,406382,541808,1083264,2423372,4132872],[]),([4,406382,541808,1087368,2423372,4128768],[]),([4,406382,541808,1218474,2423372,4128768],[]),([4,406382,541808,1218474,2423372,4146288],[]),([4,406382,542328,1218474,2160640,4128768],[]),([4,406382,677242,1083264,2423372,4146288],[]),([4,541808,948094,1218474,2423372,4128768],[]),([4,541808,983167,1218474,2423372,4128768],[]),([4,677242,812668,1218474,2423372,4128768],[]),([5,520,406382,541808,1218474,2160640,4128768],[(128,0),(168,0)]),([5,1024,135466,270924,1624048,2160640,4146288],[(56,0),(128,0)]),([5,1056,135466,270924,1624048,2160640,4128768],[(128,0)]),([5,1056,135466,270924,1759226,2160640,4128768],[(128,0)]),([5,1056,270924,677242,1218474,2160640,4128768],[(56,0),(128,0),(168,0)]),([5,17408,135466,270924,1083264,2160640,4146288],[(56,0)]),([5,17520,34688,135466,270924,2160640,4128768],[(80,0)]),([5,17520,135466,270924,1083264,2160640,4128768],[])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([5,17520,135466,270924,1083264,2160640,4146288],[]),([5,17520,135466,270924,1083264,2423372,4128768],[]),([5,33280,135466,541808,1353676,2423372,4128768],[]),([5,34304,135466,270924,541808,2160640,4128768],[(56,0)]),([5,34304,135466,270924,541808,2423372,4128768],[(56,0)]),([5,34432,135466,270924,541808,2160640,4128768],[(56,0)]),([5,34688,63488,135466,270924,541808,4128768],[(72,0)]),([5,34688,65535,135466,270924,2160640,4146288],[(72,0)]),([5,34688,135466,270924,541808,2160640,4128768],[(56,0)]),([5,34688,135466,270924,541808,2160640,4146288],[(56,0)]),([5,34688,135466,270924,541808,2423372,4128768],[(56,0)]),([5,34688,169898,270924,541808,2160640,4128768],[(56,0)]),([5,38826,135466,270924,541808,2160640,4128768],[(56,0)]),([5,56755,135466,270924,1083264,2160640,4146288],[]),([5,65535,135466,270924,541808,4163456,4192256],[]),([5,65535,135466,270924,1083264,2160640,4146288],[]),([5,65535,135466,270924,1083264,2423372,4146288],[]),([5,65535,135466,270924,1083264,4146288,4192256],[]),([5,65535,135466,326220,541808,1083264],[]),([5,65535,135466,326220,541808,1083264,4128768],[]),([5,131072,135466,262144,541808,1083264,2423372],[(96,0),(168,0)]),([5,131072,135466,270924,541808,1345408,2160640],[]),([5,131072,135466,270924,803952,1083264,2160640],[(168,0)]),([5,131072,270924,397610,541808,1083264,2160640],[(96,0),(168,0)]),([5,131072,270924,541808,1218474,2160640,4128768],[(56,0),(72,0),(128,0)]),([5,131072,270924,541808,1218474,2160640,4133162],[(56,0),(72,0),(128,0)]),([5,131072,270924,541808,1218474,2160640,4146288],[(56,0),(72,0),(128,0)]),([5,131072,270924,541808,1218474,2160640,4163456],[(56,0),(72,0),(128,0)]),([5,131072,270924,541808,1218474,2160640,4167594],[(56,0),(72,0),(128,0)]),([5,131072,270924,541808,1218474,2291712,4128768],[(56,0),(72,0),(96,0),(128,0),(168,0)]),([5,131072,270924,541808,1218474,2423372,4128768],[(56,0),(72,0),(128,0)]),([5,131072,270924,672880,1218474,2160640,4128768],[(56,0),(72,0),(96,0),(128,0),(168,0)]),([5,131072,401996,541808,1218474,2160640,4128768],[(56,0),(72,0),(96,0),(128,0),(168,0)]),([5,131080,270924,541808,1218474,2160640,4128768],[(56,0),(72,0),(128,0)]),([5,131104,270924,541808,1218474,2160640,4128768],[(56,0),(72,0),(128,0)]),([5,131104,270924,541808,1218474,2160640,4146288],[(56,0),(72,0),(128,0)]),([5,131104,270924,677242,1083264,2160640,4146288],[(56,0),(96,0),(128,0)]),([5,131328,270924,541808,1218474,2160640,4128768],[]),([5,131370,270924,541808,1218474,2160640,4128768],[])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([5,135168,270924,541808,1218474,2160640,4128768],[(56,0),(72,0),(128,0)]),([5,135210,270924,541808,1083264,2160640,3080192],[(96,0)]),([5,135210,270924,541808,1083264,2160640,4128768],[]),([5,135210,270924,541808,1083264,2160640,4146288],[]),([5,135210,270924,541808,1083264,2160640,4163456],[]),([5,135210,270924,541808,1083264,2423372,4128768],[]),([5,135210,270924,541808,1218474,2160640,4128768],[]),([5,135434,270924,541808,1218474,2160640,4128768],[]),([5,135458,270924,541808,1218474,2160640,4128768],[]),([5,135466,169898,270924,541808,2160640,4128768],[(56,0)]),([5,135466,196607,270924,1083264,2160640,4146288],[(96,0)]),([5,135466,270924,393216,541808,1083264,2160640],[(128,0)]),([5,135466,270924,393216,541808,1083264,2423372],[(128,0)]),([5,135466,270924,393216,541808,1083264,2553856],[(72,0),(128,0)]),([5,135466,270924,393216,935024,1083264,2160640],[(72,0),(128,0),(144,0)]),([5,135466,270924,393312,541808,1083264,2160640],[(128,0)]),([5,135466,270924,406382,935024,1083264,2160640],[(128,0)]),([5,135466,270924,541744,1083264,2160640,4146288],[]),([5,135466,270924,541808,917504,1083264,2160640],[(128,0)]),([5,135466,270924,541808,935024,1083264,2160640],[(128,0)]),([5,135466,270924,541808,983040,1083264,2160640],[(128,0)]),([5,135466,270924,541808,1083008,2160640,4128768],[]),([5,135466,270924,541808,1083008,2160640,4146288],[]),([5,135466,270924,541808,1083008,2160640,4163200],[]),([5,135466,270924,541808,1083008,2423372,4128768],[]),([5,135466,270924,541808,1083264,1441792,2160640],[]),([5,135466,270924,541808,1083264,1507328,2160640],[]),([5,135466,270924,541808,1083264,2031616,2160640],[]),([5,135466,270924,541808,1083264,2031616,2423372],[]),([5,135466,270924,541808,1083264,2032752,2160640],[]),([5,135466,270924,541808,1083264,2049136,2160640],[]),([5,135466,270924,541808,1083264,2160640,3604480],[]),([5,135466,270924,541808,1083264,2160640,4128768],[]),([5,135466,270924,541808,1083264,2160640,4128776],[]),([5,135466,270924,541808,1083264,2160640,4128800],[]),([5,135466,270924,541808,1083264,2160640,4128808],[]),([5,135466,270924,541808,1083264,2160640,4128864],[]),([5,135466,270924,541808,1083264,2160640,4129280],[]),([5,135466,270924,541808,1083264,2160640,4129288],[]),([5,135466,270924,541808,1083264,2160640,4129344],[])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,270924,541808,1083264,2160640,4129792],[]),([5,135466,270924,541808,1083264,2160640,4129824],[]),([5,135466,270924,541808,1083264,2160640,4129856],[]),([5,135466,270924,541808,1083264,2160640,4129904],[]),([5,135466,270924,541808,1083264,2160640,4130304],[]),([5,135466,270924,541808,1083264,2160640,4146176],[]),([5,135466,270924,541808,1083264,2160640,4146224],[]),([5,135466,270924,541808,1083264,2160640,4146288],[]),([5,135466,270924,541808,1083264,2160640,4146296],[]),([5,135466,270924,541808,1083264,2160640,4146800],[]),([5,135466,270924,541808,1083264,2160640,4161536],[]),([5,135466,270924,541808,1083264,2160640,4162048],[]),([5,135466,270924,541808,1083264,2160640,4162560],[]),([5,135466,270924,541808,1083264,2160640,4163200],[]),([5,135466,270924,541808,1083264,2160640,4179056],[]),([5,135466,270924,541808,1083264,2160640,4181137],[]),([5,135466,270924,541808,1083264,2160648,4128768],[]),([5,135466,270924,541808,1083264,2160648,4128776],[]),([5,135466,270924,541808,1083264,2160648,4146288],[]),([5,135466,270924,541808,1083264,2160672,4128768],[]),([5,135466,270924,541808,1083264,2160672,4128800],[]),([5,135466,270924,541808,1083264,2160672,4146288],[]),([5,135466,270924,541808,1083264,2160680,4128768],[]),([5,135466,270924,541808,1083264,2160704,4128768],[]),([5,135466,270924,541808,1083264,2160704,4128832],[]),([5,135466,270924,541808,1083264,2160704,4146288],[]),([5,135466,270924,541808,1083264,2160712,4128768],[]),([5,135466,270924,541808,1083264,2160736,4128768],[]),([5,135466,270924,541808,1083264,2161152,4128768],[]),([5,135466,270924,541808,1083264,2161152,4129280],[]),([5,135466,270924,541808,1083264,2161152,4146288],[]),([5,135466,270924,541808,1083264,2161160,4128768],[]),([5,135466,270924,541808,1083264,2161216,4128768],[]),([5,135466,270924,541808,1083264,2161228,4128768],[]),([5,135466,270924,541808,1083264,2161664,4128768],[]),([5,135466,270924,541808,1083264,2161664,4129792],[]),([5,135466,270924,541808,1083264,2161664,4146288],[(112,0)]),([5,135466,270924,541808,1083264,2161696,4128768],[(112,0)]),([5,135466,270924,541808,1083264,2161728,4128768],[]),([5,135466,270924,541808,1083264,2162176,4128768],[])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,270924,541808,1083264,2291712,4128768],[(96,0)]),([5,135466,270924,541808,1083264,2291712,4133162],[(96,0)]),([5,135466,270924,541808,1083264,2291712,4146288],[(96,0)]),([5,135466,270924,541808,1083264,2291712,4163456],[(96,0)]),([5,135466,270924,541808,1083264,2291720,4128768],[(96,0)]),([5,135466,270924,541808,1083264,2291744,4128768],[(96,0)]),([5,135466,270924,541808,1083264,2291744,4146288],[(72,0),(96,0)]),([5,135466,270924,541808,1083264,2422784,4128768],[]),([5,135466,270924,541808,1083264,2422784,4146288],[]),([5,135466,270924,541808,1083264,2422792,4128768],[]),([5,135466,270924,541808,1083264,2422848,4128768],[]),([5,135466,270924,541808,1083264,2422848,4146288],[]),([5,135466,270924,541808,1083264,2422860,4128768],[]),([5,135466,270924,541808,1083264,2423296,4128768],[]),([5,135466,270924,541808,1083264,2423308,4128768],[]),([5,135466,270924,541808,1083264,2423364,4128768],[]),([5,135466,270924,541808,1083264,2423372,2490368],[(96,0)]),([5,135466,270924,541808,1083264,2423372,3080192],[(96,0)]),([5,135466,270924,541808,1083264,2423372,3604480],[]),([5,135466,270924,541808,1083264,2423372,4128768],[]),([5,135466,270924,541808,1083264,2423372,4128776],[]),([5,135466,270924,541808,1083264,2423372,4128800],[]),([5,135466,270924,541808,1083264,2423372,4128832],[]),([5,135466,270924,541808,1083264,2423372,4129280],[]),([5,135466,270924,541808,1083264,2423372,4129792],[]),([5,135466,270924,541808,1083264,2423372,4132864],[]),([5,135466,270924,541808,1083264,2423372,4132872],[]),([5,135466,270924,541808,1083264,2423372,4145152],[]),([5,135466,270924,541808,1083264,2423372,4145216],[]),([5,135466,270924,541808,1083264,2423372,4146288],[]),([5,135466,270924,541808,1083264,2423372,4161536],[]),([5,135466,270924,541808,1083264,2423372,4162048],[]),([5,135466,270924,541808,1083264,2423404,4128768],[]),([5,135466,270924,541808,1083264,2424396,4128768],[]),([5,135466,270924,541808,1083264,2553856,4128768],[(96,0)]),([5,135466,270924,541808,1083264,2554444,4128768],[(96,0),(180,0)]),([5,135466,270924,541808,1083272,2160648,4128768],[]),([5,135466,270924,541808,1083272,2423372,4128768],[]),([5,135466,270924,541808,1083296,2160672,4128768],[]),([5,135466,270924,541808,1083296,2423372,4128768],[])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,270924,541808,1083328,2423372,4128768],[]),([5,135466,270924,541808,1087360,2423372,4128768],[]),([5,135466,270924,541808,1087368,2423372,4128768],[]),([5,135466,270924,541808,1099648,2423372,4128768],[]),([5,135466,270924,541808,1099648,2686064,4128768],[]),([5,135466,270924,541808,1099712,2423372,4128768],[]),([5,135466,270924,541808,1214336,2291712,4128768],[(96,0)]),([5,135466,270924,541808,1214336,2423372,4128768],[]),([5,135466,270924,541808,1218474,2291712,4128768],[(96,0),(168,0)]),([5,135466,270924,541808,1218474,2423372,4128768],[]),([5,135466,270924,541808,1218474,2423372,4146288],[(72,0)]),([5,135466,270924,541816,1083264,2160640,4128768],[]),([5,135466,270924,541816,1083264,2160640,4128776],[]),([5,135466,270924,541816,1083264,2160640,4146288],[]),([5,135466,270924,541816,1083264,2160640,4146296],[]),([5,135466,270924,541816,1083264,2160648,4128768],[]),([5,135466,270924,541816,1083264,2423372,4128768],[]),([5,135466,270924,542064,1083264,2160640,4146288],[]),([5,135466,270924,542320,1083264,2160640,4128768],[]),([5,135466,270924,542320,1083264,2160640,4129280],[]),([5,135466,270924,542320,1083264,2160640,4146288],[]),([5,135466,270924,542320,1083264,2160640,4146800],[]),([5,135466,270924,542320,1083264,2161152,4128768],[]),([5,135466,270924,542320,1083264,2423372,4128768],[]),([5,135466,270924,542320,1218474,2160640,4128768],[]),([5,135466,270924,542328,1083264,2160640,4128768],[]),([5,135466,270924,542328,1218474,2160640,4128768],[]),([5,135466,270924,574576,1083264,2160640,4128768],[]),([5,135466,270924,574576,1083264,2160640,4146288],[]),([5,135466,270924,574576,1083264,2160640,4161536],[]),([5,135466,270924,574576,1083264,2160640,4179056],[]),([5,135466,270924,574576,1083264,2423372,4128768],[]),([5,135466,270924,575088,1083264,2160640,4128768],[]),([5,135466,270924,575088,1083264,2423372,4128768],[]),([5,135466,270924,589823,1083264,2160640,4146288],[]),([5,135466,270924,672880,1083264,2160640,4128768],[(96,0)]),([5,135466,270924,672880,1083264,2160640,4133162],[(96,0)]),([5,135466,270924,672880,1083264,2160640,4146288],[(96,0)]),([5,135466,270924,672880,1083264,2160640,4163456],[(96,0)]),([5,135466,270924,672880,1083264,2291712,4128768],[(96,0)])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,270924,672880,1083264,2423372,4128768],[(96,0),(180,0)]),([5,135466,270924,672880,1214336,2160640,4128768],[(96,0)]),([5,135466,270924,672880,1218474,2160640,4128768],[(96,0),(168,0)]),([5,135466,270924,672888,1083264,2160640,4128768],[(96,0)]),([5,135466,270924,676976,1083264,2160640,4128768],[(96,0)]),([5,135466,270924,677242,1083264,2160640,4146288],[(96,0)]),([5,135466,270924,677242,1083264,2423372,4146288],[(96,0)]),([5,135466,270924,677242,1218474,2160640,4146288],[(72,0),(96,0)]),([5,135466,270924,935024,1083264,2160640],[(96,0),(98,0),(97,0)]),([5,135466,270924,935024,1083264,2160640,4128768],[(96,0)]),([5,135466,270924,948094,1083264,2160640,4146288],[(96,0)]),([5,135466,270924,1624048,2686064,3211136,4128768],[]),([5,135466,270924,4146288,4163456,4192256],[]),([5,135466,270956,541808,1083264,2160640,4128768],[]),([5,135466,270956,541808,1083264,2160640,4128800],[]),([5,135466,270956,541808,1083264,2160640,4146288],[]),([5,135466,270956,541808,1083264,2160672,4128768],[]),([5,135466,270956,541808,1083264,2423372,4128768],[]),([5,135466,270956,541808,1083264,2423404,4128768],[]),([5,135466,270956,541808,1083296,2160640,4128768],[]),([5,135466,270956,541808,1218474,2160640,4128768],[]),([5,135466,271180,541808,1083264,2423372,4128768],[]),([5,135466,271948,541808,1083264,2160640,4128768],[]),([5,135466,271948,541808,1083264,2160640,4129792],[]),([5,135466,271948,541808,1083264,2160640,4146288],[]),([5,135466,271948,541808,1083264,2161664,4128768],[]),([5,135466,271948,541808,1083264,2423372,4128768],[]),([5,135466,271948,541808,1083264,2424396,4128768],[]),([5,135466,271948,541808,1218474,2160640,4128768],[]),([5,135466,271948,541808,1624048,2160640,4128768],[]),([5,135466,271980,541808,1083264,2160640,4128768],[]),([5,135466,271980,541808,1218474,2160640,4128768],[(72,0)]),([5,135466,275020,541808,1083264,2160640,4128768],[]),([5,135466,275020,541808,1083264,2160640,4132864],[]),([5,135466,275020,541808,1083264,2160640,4146288],[]),([5,135466,275020,541808,1083264,2423372,4128768],[]),([5,135466,275020,541808,1087360,2160640,4128768],[]),([5,135466,275020,541808,1218474,2160640,4128768],[])]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,275020,545904,1083264,2160640,4128768],[]),([5,135466,275052,541808,1083264,2160640,4128768],[]),([5,135466,287308,541808,1083264,2160640,4128768],[]),([5,135466,287308,541808,1083264,2160640,4145152],[]),([5,135466,287308,541808,1083264,2160640,4146288],[]),([5,135466,287308,541808,1083264,2423372,4128768],[]),([5,135466,287308,541808,1083264,2686064,4128768],[]),([5,135466,287308,541808,1099648,2160640,4128768],[]),([5,135466,287308,541808,1218474,2160640,4128768],[]),([5,135466,287340,541808,1083264,2160640,4128768],[]),([5,135466,288332,541808,1083264,2160640,4128768],[]),([5,135466,291404,541808,1083264,2160640,4128768],[]),([5,135466,303692,541808,1083264,2160640,4128768],[]),([5,135466,303692,541808,1083264,2160640,4146288],[]),([5,135466,303692,541808,1083264,2160640,4161536],[]),([5,135466,303692,541808,1083264,2423372,4128768],[]),([5,135466,303692,541808,1218474,2160640,4128768],[]),([5,135466,303692,574576,1083264,2160640,4128768],[]),([5,135466,304716,541808,1083264,2160640,4128768],[]),([5,135466,307788,541808,1083264,2160640,4128768],[]),([5,135466,307788,541808,1218474,2160640,4128768],[(128,0)]),([5,135466,320076,541808,1083264,2160640,4128768],[]),([5,135466,326220,541808,1083264,2160640,4128768],[]),([5,135466,326220,541808,1083264,4128768],[]),([5,135466,327679,541808,1083264,2423372,4128768],[]),([5,135466,393216,401996,541808,1083264,2160640],[(128,0)]),([5,135466,393216,406382,541808,1083264,2423372],[]),([5,135466,393216,541808,1083264,2160640,2423372],[(96,0)]),([5,135466,393216,541808,1083264,2423372],[]),([5,135466,393216,541808,1083264,2423372,4128768],[]),([5,135466,397610,541808,1083264,2423372,4128768],[]),([5,135466,401996,541808,1083264,2160640,4128768],[(96,0)]),([5,135466,401996,541808,1083264,2160640,4133162],[(96,0)]),([5,135466,401996,541808,1083264,2160640,4146288],[(96,0)]),([5,135466,401996,541808,1083264,2160640,4163456],[(96,0)]),([5,135466,401996,541808,1083264,2291712,4128768],[(96,0)]),([5,135466,401996,541808,1083264,2423372,4128768],[(96,0)]),([5,135466,401996,541808,1083264,2554444,4128768],[(96,0)])]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,401996,541808,1214336,2160640,4128768],[(96,0)]),([5,135466,401996,541808,1218474,2160640,4128768],[(96,0),(168,0)]),([5,135466,401996,672880,1083264,2160640,4128768],[(96,0)]),([5,135466,402028,541808,1083264,2160640,4128768],[(96,0)]),([5,135466,402028,541808,1083264,2160640,4146288],[(72,0),(96,0)]),([5,135466,406092,541808,1083264,2160640,4128768],[(96,0)]),([5,135466,406382,541808,1083264,2423372,4128768],[]),([5,135466,406382,541808,1083264,2423372,4146288],[]),([5,135466,406382,541808,1218474,2423372,4128768],[]),([5,135466,406382,812668,1083264,2160640,4146288],[(96,0)]),([5,135466,541808,786432,1083264,2423372,4128768],[]),([5,135466,541808,795212,1083264,2423372,4128768],[]),([5,135466,541808,803952,1083264,2423372,4128768],[]),([5,135466,541808,812668,1083264,2423372,4128768],[]),([5,135466,541808,812668,1083264,2423372,4146288],[]),([5,135466,541808,812668,1218474,2423372,4128768],[]),([5,135466,541808,948094,1083264,2423372,4128768],[]),([5,135466,541808,983167,1083264,2423372,4128768],[]),([5,135466,541808,1083264,1310720,2423372,4128768],[]),([5,135466,541808,1083264,1319500,2423372,4128768],[]),([5,135466,541808,1083264,1345408,2423372,4128768],[]),([5,135466,541808,1083264,1353676,2423372,4128768],[]),([5,135466,541808,1083264,1353676,2423372,4146288],[]),([5,135466,541808,1083264,1488878,2423372,4128768],[]),([5,135466,541808,1083264,1508239,2423372,4128768],[]),([5,135466,541808,1083264,1894396,2423372,4128768],[]),([5,135466,541808,1083264,1902293,2423372,4128768],[]),([5,135466,541808,1083264,2031616,2033663,2423372],[]),([5,135466,541808,1083264,2031616,2160640,2423372],[]),([5,135466,541808,1083264,2031616,2423372],[]),([5,135466,541808,1083264,2031616,2423372,4128768],[]),([5,135466,541808,1083264,2033663,2423372,4128768],[]),([5,135466,541808,1083264,2033663,2423372,4146288],[]),([5,135466,541808,1083264,2033663,2423372,4192256],[]),([5,135466,541808,1083264,2037759,2423372,4128768],[]),([5,135466,541808,1083264,2041855,2423372,4128768],[]),([5,135466,541808,1083264,2050047,2423372,4128768],[]),([5,135466,541808,1083264,2066431,2423372,4128768],[]),([5,135466,541808,1083264,2097151,2423372,4128768],[])]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,135466,541808,1083264,2162687,2423372],[]),([5,135466,541808,1218474,1353676,2423372,4128768],[]),([5,135466,541808,1218474,1488878,2423372,4128768],[]),([5,135466,541808,1218474,2033663,2423372,4128768],[]),([5,135466,541808,1345408,2160640,2423372,4128768],[]),([5,135466,541808,1345408,2423372,4128768],[]),([5,135466,541808,1353676,1624048,2423372,4128768],[]),([5,135466,541808,1353676,2423372,4128768,4163456],[]),([5,135466,541808,1353676,2423372,4163456],[]),([5,135466,541808,2423372,3180416,4128768],[]),([5,135466,677242,812668,1083264,2423372,4128768],[]),([5,135466,803952,1083264,2160640,2423372,4128768],[]),([5,135466,803952,1083264,2423372,4128768],[]),([5,135466,812668,1083264,1353676,2160640,4146288],[]),([5,135466,812668,1083264,1624048,2423372,4128768],[]),([5,135466,812668,1083264,2160640,2423372,4146288],[]),([5,135466,812668,1083264,2423372,4128768,4146288],[]),([5,135466,812668,1083264,2423372,4146288],[]),([5,135466,812668,1353676,1624048,2160640,4128768],[]),([5,135466,1083264,2423372,2638960,4128768],[]),([5,136490,271948,541808,1083264,2160640,4128768],[]),([5,168234,303692,541808,1083264,2160640,4128768],[]),([5,397610,541808,1083264,2160640,2423372,4128768],[]),([5,397610,541808,1083264,2423372,4128768],[]),([5,406382,541808,677242,1083264,2423372,4128768],[]),([5,406382,541808,1083264,1218474,2423372,4128768],[]),([5,406382,541808,1083264,2160640,4133162,4137548],[]),([5,406382,541808,1083264,2423372,4128768,4133162],[]),([5,406382,541808,1218474,2423372,4128768],[]),([5,406382,677242,812668,1083264,2160640,4128768],[])]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,541808,1083264,2232618,2423372,4128768],[]),([5,541808,1218474,1353676,2423372,4128768],[]),([5,541808,1218474,2423372,3211136,4128768],[]),([6,0,135466,270924,541808,1083264,2160640,4128768],[]),([6,8,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,8,135466,270924,541808,1083264,2160640,4128776],[(128,0)]),([6,8,135466,270924,541808,1083264,2160640,4146288],[(128,0)]),([6,8,135466,270924,541808,1083264,2160648,4128768],[]),([6,8,135466,270924,541808,1083264,2423372,4128768],[]),([6,8,135466,270924,541816,1083264,2160640,4128768],[(128,0)]),([6,32,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,32,135466,270924,541808,1083264,2160640,4128800],[(128,0)]),([6,32,135466,270924,541808,1083264,2160640,4146288],[(128,0)]),([6,32,135466,270924,541808,1083264,2160672,4128768],[]),([6,32,135466,270924,541808,1083264,2423372,4128768],[]),([6,32,135466,270924,541808,1083296,2160640,4128768],[(56,0),(96,0),(128,0),(216,0)]),([6,32,135466,270924,541808,1218474,2160640,4128768],[(56,0),(96,0),(128,0),(168,0),(216,0)]),([6,32,135466,270956,541808,1083264,2160640,4128768],[]),([6,40,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,96,135466,270924,541808,1083264,2160640,4128768],[(56,0),(128,0)]),([6,256,135466,270924,541808,1083264,2160640,4128768],[]),([6,256,135466,270924,541808,1083264,2160640,4146288],[]),([6,256,135466,270924,541808,1083264,2423372,4128768],[])]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([6,256,135466,270924,541808,1218474,2160640,4128768],[(56,0),(128,0)]),([6,264,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,288,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,512,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,512,135466,270924,541808,1083264,2160640,4129280],[(56,0)]),([6,512,135466,270924,541808,1083264,2160640,4146288],[(56,0)]),([6,512,135466,270924,541808,1083264,2161152,4128768],[(56,0)]),([6,512,135466,270924,541808,1083264,2423372,4128768],[(56,0)]),([6,512,135466,270924,541808,1218474,2160640,4128768],[(56,0),(72,0),(128,0),(168,0),(216,0)]),([6,512,135466,270924,542320,1083264,2160640,4128768],[(56,0)]),([6,512,135978,270924,541808,1083264,2160640,4128768],[(56,0),(72,0),(96,0),(128,0),(168,0),(216,0)]),([6,520,135466,270924,541808,1083264,2160640,4128768],[(56,0),(128,0)]),([6,520,135466,270924,541808,1218474,2160640,4128768],[(56,0),(72,0),(128,0),(168,0),(216,0)]),([6,576,135466,270924,541808,1083264,2160640,4128768],[(56,0),(128,0)]),([6,768,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,1024,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,1024,135466,270924,541808,1083264,2160640,4129792],[(56,0)]),([6,1024,135466,270924,541808,1083264,2160640,4146288],[(56,0)]),([6,1024,135466,270924,541808,1083264,2161664,4128768],[(56,0)]),([6,1024,135466,270924,541808,1083264,2423372,4128768],[(56,0)]),([6,1024,135466,270924,541808,1218474,2160640,4128768],[(56,0),(96,0),(128,0),(168,0),(216,0)]),([6,1024,135466,270924,541808,1624048,2160640,4128768],[(56,0),(168,0)]),([6,1024,135466,271948,541808,1083264,2160640,4128768],[]),([6,1024,136490,270924,541808,1083264,2160640,4128768],[(56,0),(96,0),(128,0),(168,0),(216,0)])]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([6,1056,135466,270924,541808,1083264,2160640,4128768],[(56,0),(128,0)]),([6,1056,135466,270924,541808,1218474,2160640,4128768],[(56,0),(96,0),(128,0),(168,0),(216,0)]),([6,1088,135466,270924,541808,1083264,2160640,4128768],[(56,0),(128,0)]),([6,1280,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,1536,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,2047,135466,270924,541808,1083264,2160640],[]),([6,2047,135466,270924,541808,1083264,2160640,4128768],[]),([6,2047,135466,270924,541808,1083264,4128768],[]),([6,4352,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,4394,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,17408,135466,270924,541808,1083264,2160640,4128768],[(56,0),(128,0)]),([6,17520,65535,135466,270924,1083264,2160640],[]),([6,17520,65535,135466,270924,1083264,2160640,4128768],[(180,0)]),([6,17520,135466,270924,541808,1083264,2160640,4128768],[]),([6,17520,135466,270924,1083264,2160640,4128768],[(106,0)]),([6,32768,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,32768,135466,270924,541808,1083264,2160640,4146288],[(56,0)]),([6,32768,135466,270924,541808,1083264,2160640,4161536],[(56,0)]),([6,32768,135466,270924,541808,1083264,2423372,4128768],[(56,0)]),([6,32768,135466,270924,574576,1083264,2160640,4128768],[(56,0)])]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([6,32768,135466,303692,541808,1083264,2160640,4128768],[]),([6,33024,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,33280,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,33280,135466,270924,541808,1083264,2423372,4128768],[(56,0)]),([6,33792,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,34688,65535,135466,270924,541808,2160640],[(72,0)]),([6,34688,65535,135466,270924,541808,2160640,4128768],[(72,0)]),([6,34688,135466,270924,541808,1083264,2160640,4128768],[(56,0)]),([6,34688,135466,270924,541808,2160640,4128768],[(56,0)]),([6,48015,135466,270924,541808,1083264,2160640],[]),([6,48015,135466,270924,541808,1083264,2160640,4128768],[]),([6,48015,135466,270924,541808,1083264,2160640,4146288],[]),([6,48015,135466,270924,1083264,2160640,4128768],[]),([6,56755,135466,270924,541808,1083264,2160640,4128768],[(172,0)]),([6,65535,135466,270924,541808,1083264,2033663],[]),([6,65535,135466,270924,541808,1083264,2160640],[]),([6,65535,135466,270924,541808,1083264,2160640,4128768],[(172,0)]),([6,65535,135466,270924,541808,1083264,2160640,4146288],[(172,0)])]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,135466,270924,541808,1083264,2423372],[]),([6,65535,135466,270924,541808,1083264,2423372,4128768],[(172,0)]),([6,65535,135466,270924,541808,1083264,4128768,4192256],[(220,0)]),([6,65535,135466,270924,541808,1083264,4192256],[]),([6,65535,135466,270924,1083264,2160640,3652495],[]),([6,65535,135466,270924,1083264,2160640,4128768,4146288],[(192,0)]),([6,65535,135466,270924,1083264,2160640,4146288],[(73,0),(134,0),(106,0)]),([6,65535,135466,541808,1083264,2160640,2423372],[]),([6,65535,135466,541808,1083264,2160640,3923379],[]),([6,131072,135466,262144,270924,541808,1083264,2160640],[(96,0),(128,0),(216,0),(176,0)]),([6,131072,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,131072,135466,270924,541808,1083264,2160640,4133162],[]),([6,131072,135466,270924,541808,1083264,2160640,4146288],[(128,0)]),([6,131072,135466,270924,541808,1083264,2160640,4163456],[]),([6,131072,135466,270924,541808,1083264,2291712,4128768],[]),([6,131072,135466,270924,541808,1083264,2423372,4128768],[]),([6,131072,135466,270924,541808,1214336,2160640,4128768],[(56,0),(128,0),(216,0)]),([6,131072,135466,270924,541808,1218474,2160640,4128768],[(56,0),(128,0),(216,0)])]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([6,131072,135466,270924,672880,1083264,2160640,4128768],[]),([6,131072,135466,401996,541808,1083264,2160640,4128768],[]),([6,131072,270924,541808,1083264,1218474,2160640,4128768],[(56,0),(72,0),(168,0)]),([6,131072,270924,541808,1218474,2160640,4128768],[(56,0),(57,0),(72,0),(73,0),(128,0),(129,0),(182,0)]),([6,131080,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,131104,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,131104,135466,270924,541808,1083264,2160640,4146288],[(128,0)]),([6,131328,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,131370,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,135168,135466,270924,541808,1083264,2160640,4128768],[(128,0),(216,0)]),([6,135210,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,135210,270924,541808,1083264,2160640,3111039,4128768],[(96,0)]),([6,135210,270924,541808,1083264,2160640,4128768],[]),([6,135210,270924,541808,2160640,3111039,4128768],[]),([6,135434,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,135458,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,135466,135466,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,135466,135466,270924,541808,1083264,2160640,4146288],[(128,0)]),([6,135466,135466,270924,541808,1083264,2423372,4128768],[]),([6,135466,135466,270924,541808,1218474,2160640,4128768],[(48,0),(52,0),(128,0)]),([6,135466,135530,270924,541808,1083264,2160640,4128768],[(56,0),(128,0),(136,0)])]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,135978,270924,541808,1083264,2160640,4128768],[(56,0),(128,0),(136,0)]),([6,135466,136490,270924,541808,1083264,2160640,4128768],[(56,0),(128,0),(136,0)]),([6,135466,143658,270924,541808,1083264,2160640,4128768],[(128,0)]),([6,135466,151850,270924,541808,1083264,2160640,4128768],[(56,0),(128,0),(136,0)]),([6,135466,168234,270924,541808,1083264,2160640,4128768],[(56,0),(128,0),(136,0)]),([6,135466,196607,270924,541808,1083264,2160640,4128768],[(128,0),(180,0)]),([6,135466,270924,393216,406382,541808,1083264,2160640],[(168,0)]),([6,135466,270924,393216,541808,1083264,2160640],[(73,0),(128,0),(130,0),(129,0),(146,0)]),([6,135466,270924,393216,541808,1083264,2160640,4128768],[(72,0),(128,0),(144,0)]),([6,135466,270924,397610,541808,1083264,2160640,4128768],[(72,0),(128,0),(144,0)]),([6,135466,270924,406382,541808,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,406382,541808,1083264,2160640,4146288],[(96,0),(128,0)]),([6,135466,270924,406382,541808,1083264,2423372,4128768],[(128,0)]),([6,135466,270924,524288,541808,1083264,2160640,4128768],[]),([6,135466,270924,524288,541808,1083264,2160640,4146288],[]),([6,135466,270924,524288,541808,1083264,2423372,4128768],[]),([6,135466,270924,524320,541808,1083264,2160640,4128768],[]),([6,135466,270924,525312,541808,1083264,2160640,4128768],[]),([6,135466,270924,525424,541808,1083264,2160640,4128768],[]),([6,135466,270924,541744,541808,1083264,2160640,4128768],[]),([6,135466,270924,541808,541808,1083264,2160640,4128768],[]),([6,135466,270924,541808,541808,1083264,2160640,4146288],[]),([6,135466,270924,541808,541808,1083264,2423372,4128768],[])]
noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,541816,1083264,2160640,4128768],[]),([6,135466,270924,541808,542064,1083264,2160640,4128768],[]),([6,135466,270924,541808,542320,1083264,2160640,4128768],[]),([6,135466,270924,541808,574576,1083264,2160640,4128768],[]),([6,135466,270924,541808,589823,1083264,2160640],[]),([6,135466,270924,541808,589823,1083264,2160640,4128768],[(196,0)]),([6,135466,270924,541808,655360,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,541808,659754,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,541808,672880,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,541808,677242,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,541808,677242,1083264,2160640,4146288],[(128,0)]),([6,135466,270924,541808,677242,1083264,2423372,4128768],[(128,0)]),([6,135466,270924,541808,677242,1218474,2160640,4128768],[(96,0),(100,0),(128,0),(116,0)]),([6,135466,270924,541808,948094,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,541808,983167,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,541808,1048576,1083264,2160640,4128768],[]),([6,135466,270924,541808,1048576,1083264,2160640,4146288],[]),([6,135466,270924,541808,1048576,1083264,2423372,4128768],[]),([6,135466,270924,541808,1048576,1218474,2160640,4128768],[(152,0),(240,0)]),([6,135466,270924,541808,1048832,1083264,2160640,4128768],[]),([6,135466,270924,541808,1049088,1083264,2160640,4128768],[]),([6,135466,270924,541808,1049600,1083264,2160640,4128768],[]),([6,135466,270924,541808,1049600,1083264,2160640,4146288],[])]
noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1050496,1083264,2160640,4128768],[]),([6,135466,270924,541808,1081344,1083264,2160640,4128768],[]),([6,135466,270924,541808,1082240,1083264,2160640,4128768],[]),([6,135466,270924,541808,1082752,1083264,2160640,4128768],[]),([6,135466,270924,541808,1083008,1083264,2160640,4128768],[]),([6,135466,270924,541808,1083008,2160640,4058837,4128768],[]),([6,135466,270924,541808,1083008,2160640,4128768],[(98,0)]),([6,135466,270924,541808,1083264,1083264,2160640,4128768],[]),([6,135466,270924,541808,1083264,1083264,2160640,4146288],[]),([6,135466,270924,541808,1083264,1083264,2423372,4128768],[]),([6,135466,270924,541808,1083264,1083272,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1083296,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1083328,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1087360,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1091456,2160640,4128768],[]),([6,135466,270924,541808,1083264,1099648,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1114111,2160640],[(96,0),(18,0)]),([6,135466,270924,541808,1083264,1114111,2160640,4128768],[(204,0)]),([6,135466,270924,541808,1083264,1179648,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1184042,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1214336,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1218474,2160640,4128768],[(152,0)])]
noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,1218474,2160640,4146288],[(72,0),(152,0)]),([6,135466,270924,541808,1083264,1218474,2423372,4128768],[]),([6,135466,270924,541808,1083264,1310720,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1319500,2160640,4128768],[]),([6,135466,270924,541808,1083264,1345408,2160640,4128768],[(152,0)]),([6,135466,270924,541808,1083264,1353676,2160640,4128768],[]),([6,135466,270924,541808,1083264,1353676,2160640,4146288],[]),([6,135466,270924,541808,1083264,1353676,2423372,4128768],[]),([6,135466,270924,541808,1083264,1488878,2160640,4128768],[]),([6,135466,270924,541808,1083264,1508239,2160640,4128768],[]),([6,135466,270924,541808,1083264,1572864,2160640,4128768],[]),([6,135466,270924,541808,1083264,1590384,2160640,4128768],[]),([6,135466,270924,541808,1083264,1607552,2160640,4128768],[]),([6,135466,270924,541808,1083264,1624048,2160640,4128768],[]),([6,135466,270924,541808,1083264,1624048,2160640,4146288],[]),([6,135466,270924,541808,1083264,1624048,2423372,4128768],[]),([6,135466,270924,541808,1083264,1759226,2160640,4128768],[(204,0)]),([6,135466,270924,541808,1083264,1770931,2160640,4128768],[]),([6,135466,270924,541808,1083264,1770931,2423372,4128768],[]),([6,135466,270924,541808,1083264,1770931,4128768],[]),([6,135466,270924,541808,1083264,1894396,2160640,4128768],[]),([6,135466,270924,541808,1083264,1902293,2160640,4128768],[])]
noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2031616,2033663],[]),([6,135466,270924,541808,1083264,2031616,2033663,2160640],[(180,0)]),([6,135466,270924,541808,1083264,2031616,2160640],[(98,0)]),([6,135466,270924,541808,1083264,2031616,2160640,4128768],[]),([6,135466,270924,541808,1083264,2033663,2160640,4128768],[(140,0)]),([6,135466,270924,541808,1083264,2033663,2160640,4146288],[(140,0)]),([6,135466,270924,541808,1083264,2033663,2160640,4192256],[(140,0)]),([6,135466,270924,541808,1083264,2033663,2423372,4128768],[(140,0)]),([6,135466,270924,541808,1083264,2033663,4128768],[]),([6,135466,270924,541808,1083264,2033663,4146288],[]),([6,135466,270924,541808,1083264,2033663,4163456],[]),([6,135466,270924,541808,1083264,2033663,4192256],[]),([6,135466,270924,541808,1083264,2037759,2160640,4128768],[(140,0)]),([6,135466,270924,541808,1083264,2041855,2160640,4128768],[]),([6,135466,270924,541808,1083264,2041855,4128768],[(18,0)]),([6,135466,270924,541808,1083264,2050047,2160640,4128768],[(140,0)])]
noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2066431,2160640,4128768],[(140,0)]),([6,135466,270924,541808,1083264,2097151,2160640,4128768],[(204,0)]),([6,135466,270924,541808,1083264,2160640,3145728,4128768],[]),([6,135466,270924,541808,1083264,2160640,3180416,4128768],[]),([6,135466,270924,541808,1083264,2160640,3211136,4128768],[]),([6,135466,270924,541808,1083264,2160640,3211136,4146288],[]),([6,135466,270924,541808,1083264,2160640,3342250,4128768],[]),([6,135466,270924,541808,1083264,2160640,3381635,4128768],[]),([6,135466,270924,541808,1083264,2160640,3604480],[(98,0)]),([6,135466,270924,541808,1083264,2160640,3604480,3652495],[]),([6,135466,270924,541808,1083264,2160640,3604480,4128768],[]),([6,135466,270924,541808,1083264,2160640,3652495,4128768],[]),([6,135466,270924,541808,1083264,2160640,3652495,4146288],[]),([6,135466,270924,541808,1083264,2160640,3652527,4128768],[]),([6,135466,270924,541808,1083264,2160640,3653519,4128768],[]),([6,135466,270924,541808,1083264,2160640,3670015,4128768],[]),([6,135466,270924,541808,1083264,2160640,3735536,4128768],[]),([6,135466,270924,541808,1083264,2160640,3787921,4128768],[]),([6,135466,270924,541808,1083264,2160640,3866624,4128768],[]),([6,135466,270924,541808,1083264,2160640,3923379,4128768],[(204,0)]),([6,135466,270924,541808,1083264,2160640,3923379,4146288],[(204,0)]),([6,135466,270924,541808,1083264,2160640,3923387,4128768],[(204,0)]),([6,135466,270924,541808,1083264,2160640,3923443,4128768],[(204,0)])]
noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2160640,3923891,4128768],[(204,0)]),([6,135466,270924,541808,1083264,2160640,3931571,4128768],[]),([6,135466,270924,541808,1083264,2160640,3932159,4128768],[]),([6,135466,270924,541808,1083264,2160640,4128768],[(98,0)]),([6,135466,270924,541808,1083264,2160640,4128768,4128768],[]),([6,135466,270924,541808,1083264,2160640,4128768,4128776],[]),([6,135466,270924,541808,1083264,2160640,4128768,4128800],[]),([6,135466,270924,541808,1083264,2160640,4128768,4129024],[]),([6,135466,270924,541808,1083264,2160640,4128768,4129280],[]),([6,135466,270924,541808,1083264,2160640,4128768,4129792],[]),([6,135466,270924,541808,1083264,2160640,4128768,4130815],[(228,0)]),([6,135466,270924,541808,1083264,2160640,4128768,4133162],[]),([6,135466,270924,541808,1083264,2160640,4128768,4141934],[]),([6,135466,270924,541808,1083264,2160640,4128768,4146288],[]),([6,135466,270924,541808,1083264,2160640,4128768,4150650],[]),([6,135466,270924,541808,1083264,2160640,4128768,4161535],[]),([6,135466,270924,541808,1083264,2160640,4128768,4161536],[]),([6,135466,270924,541808,1083264,2160640,4128768,4163456],[]),([6,135466,270924,541808,1083264,2160640,4128768,4167594],[]),([6,135466,270924,541808,1083264,2160640,4128768,4171724],[]),([6,135466,270924,541808,1083264,2160640,4128768,4176783],[]),([6,135466,270924,541808,1083264,2160640,4128768,4177919],[]),([6,135466,270924,541808,1083264,2160640,4128768,4179952],[])]
noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2160640,4128768,4185523],[(252,0)]),([6,135466,270924,541808,1083264,2160640,4128768,4186111],[(228,0),(252,0)]),([6,135466,270924,541808,1083264,2160640,4128768,4190207],[]),([6,135466,270924,541808,1083264,2160640,4128768,4194176],[]),([6,135466,270924,541808,1083264,2160640,4128768,4194239],[]),([6,135466,270924,541808,1083264,2160640,4128768,4194295],[]),([6,135466,270924,541808,1083264,2160640,4128768,4194303],[]),([6,135466,270924,541808,1083264,2160640,4128776],[(98,0)]),([6,135466,270924,541808,1083264,2160640,4128800],[(98,0)]),([6,135466,270924,541808,1083264,2160640,4129024],[]),([6,135466,270924,541808,1083264,2160640,4129280],[(98,0)]),([6,135466,270924,541808,1083264,2160640,4129792],[(98,0)]),([6,135466,270924,541808,1083264,2160640,4133162,4137548],[]),([6,135466,270924,541808,1083264,2160640,4133162,4146288],[]),([6,135466,270924,541808,1083264,2160640,4133162,4192256],[(260,0)]),([6,135466,270924,541808,1083264,2160640,4146288],[(98,0),(82,0)]),([6,135466,270924,541808,1083264,2160640,4146288,4146288],[])]
noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2160640,4146288,4150650],[]),([6,135466,270924,541808,1083264,2160640,4146288,4163456],[]),([6,135466,270924,541808,1083264,2160640,4146288,4179952],[]),([6,135466,270924,541808,1083264,2160640,4161536],[(98,0)]),([6,135466,270924,541808,1083264,2160640,4163456],[]),([6,135466,270924,541808,1083264,2160640,4163456,4192256],[]),([6,135466,270924,541808,1083264,2160640,4179952],[]),([6,135466,270924,541808,1083264,2160640,4194176],[]),([6,135466,270924,541808,1083264,2160648,4128768],[(98,0)]),([6,135466,270924,541808,1083264,2160672,4128768],[(98,0)]),([6,135466,270924,541808,1083264,2160704,4128768],[(98,0)]),([6,135466,270924,541808,1083264,2160896,4128768],[]),([6,135466,270924,541808,1083264,2161152,4128768],[(98,0)])]
noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2161664,4128768],[(98,0),(114,0)]),([6,135466,270924,541808,1083264,2291712,4128768],[(96,0),(97,0),(182,0)]),([6,135466,270924,541808,1083264,2292010,2423372,4128768],[(96,0)]),([6,135466,270924,541808,1083264,2292010,2686064,4128768],[(72,0),(96,0)]),([6,135466,270924,541808,1083264,2292010,4128768,4192256],[(96,0)]),([6,135466,270924,541808,1083264,2292010,4192256],[(96,0)]),([6,135466,270924,541808,1083264,2359296,2423372,4128768],[(140,0)]),([6,135466,270924,541808,1083264,2422784,4128768],[(98,0)]),([6,135466,270924,541808,1083264,2423372,2423372,4128768],[]),([6,135466,270924,541808,1083264,2423372,2554734,4128768],[(96,0)]),([6,135466,270924,541808,1083264,2423372,2686064,4128768],[(148,0)]),([6,135466,270924,541808,1083264,2423372,2948732,4128768],[(148,0)]),([6,135466,270924,541808,1083264,2423372,3111039,4128768],[(96,0),(180,0)]),([6,135466,270924,541808,1083264,2423372,3211136,4128768],[]),([6,135466,270924,541808,1083264,2423372,3473356,4128768],[]),([6,135466,270924,541808,1083264,2423372,3652495,4128768],[(180,0)]),([6,135466,270924,541808,1083264,2423372,3923379,4128768],[(204,0)]),([6,135466,270924,541808,1083264,2423372,4058837,4128768],[(180,0)]),([6,135466,270924,541808,1083264,2423372,4128768],[(181,0)])]
noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,2423372,4128768,4128768],[(180,0)]),([6,135466,270924,541808,1083264,2423372,4128768,4133162],[(228,0)]),([6,135466,270924,541808,1083264,2423372,4128768,4137548],[(180,0)]),([6,135466,270924,541808,1083264,2423372,4128768,4146288],[(180,0),(228,0)]),([6,135466,270924,541808,1083264,2423372,4128768,4163456],[(228,0)]),([6,135466,270924,541808,1083264,2423372,4128768,4192256],[(180,0),(228,0)]),([6,135466,270924,541808,1083264,2423372,4128768,4192844],[(180,0)]),([6,135466,270924,541808,1083264,2423372,4146288],[(82,0),(181,0)]),([6,135466,270924,541808,1083264,2423372,4163456],[]),([6,135466,270924,541808,1083264,2684928,4128768],[]),([6,135466,270924,541808,1083264,2686064,3211136,4128768],[]),([6,135466,270924,541808,1083264,3209216,4128768],[(96,0)]),([6,135466,270924,541808,1083264,4128768,4130815],[(22,0)]),([6,135466,270924,541808,1083264,4128768,4192256],[]),([6,135466,270924,541808,1083264,4128768,4192844],[])]
noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,541808,1083264,4133162,4192256],[]),([6,135466,270924,541808,1218474,2033663,4128768],[(18,0)]),([6,135466,270924,541808,1218474,2423372,4128768],[(57,0),(73,0),(129,0),(181,0)]),([6,135466,270924,541808,1218474,4128768,4192256],[]),([6,135466,270924,541808,2033663,3111039,4128768],[]),([6,135466,270924,541808,2033663,4128768,4163456],[]),([6,135466,270924,541808,4128768,4163456,4192256],[]),([6,135466,270924,541816,1083264,2160640,4128768],[(98,0)]),([6,135466,270924,542064,1083264,2160640,4128768],[]),([6,135466,270924,542320,1083264,2160640,4128768],[]),([6,135466,270924,574576,1083264,2160640,4128768],[(98,0)])]
noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,672880,1083264,2160640,4128768],[(96,0),(97,0),(182,0)]),([6,135466,270924,677242,812668,1083264,2160640,4128768],[(128,0)]),([6,135466,270924,677242,1083264,2160640,2686064,4128768],[(96,0),(128,0),(188,0)]),([6,135466,270924,677242,1083264,2160640,4128768,4146288],[(96,0)]),([6,135466,270924,677242,1083264,2160640,4146288],[(57,0),(96,0),(97,0),(129,0)]),([6,135466,270924,1083264,1590384,2160640,4128768],[(72,0)]),([6,135466,270924,1083264,1624048,2160640,2686064,4128768],[]),([6,135466,270924,1083264,2033663,3652495,4128768],[]),([6,135466,270924,1083264,2033663,4128768,4146288],[]),([6,135466,270924,1083264,2160640,3604480,3652495],[]),([6,135466,270924,1083264,2160640,3652495,4128768],[]),([6,135466,270924,1083264,2160640,3652495,4146288],[]),([6,135466,270924,1083264,2160640,3652495,4163456],[])]
noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,270924,1083264,2160640,4128768,4146288],[]),([6,135466,270924,1083264,2160640,4128768,4176783],[]),([6,135466,270924,1083264,2160640,4133162,4146288],[(18,0)]),([6,135466,270924,1083264,2423372,3652495,4128768],[]),([6,135466,270924,1083264,2423372,4128768,4146288],[]),([6,135466,270924,1083264,3652495,4128768,4192256],[]),([6,135466,270924,1083264,4128768,4146288,4192256],[]),([6,135466,270956,541808,1083264,2160640,4128768],[]),([6,135466,271180,541808,1083264,2160640,4128768],[]),([6,135466,271948,541808,1083264,2160640,4128768],[]),([6,135466,275020,541808,1083264,2160640,4128768],[])]
noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,287308,541808,1083264,2160640,4128768],[]),([6,135466,303692,541808,1083264,2160640,4128768],[]),([6,135466,401996,541808,1083264,2160640,4128768],[(96,0),(97,0)]),([6,135466,406382,541808,812668,1083264,2160640,4128768],[(128,0)]),([6,135466,406382,541808,1083264,2160640,2423372,4128768],[(96,0)]),([6,135466,406382,541808,1083264,2160640,4128768,4137548],[(96,0)]),([6,135466,406382,541808,1083264,2423372,4128768],[(133,0)]),([6,135466,541808,795212,1083264,2160640,4128768],[]),([6,135466,541808,812668,1083264,1353676,2160640,4128768],[]),([6,135466,541808,812668,1083264,2160640,2423372,4128768],[]),([6,135466,541808,812668,1083264,2423372,4128768],[(141,0)]),([6,135466,541808,1083264,1319500,2160640,4128768],[(72,0)]),([6,135466,541808,1083264,1353676,2160640,2423372,4128768],[]),([6,135466,541808,1083264,1353676,2423372,4128768],[])]
noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,541808,1083264,1770931,2160640,4128768],[]),([6,135466,541808,1083264,2033663,2160640,2423372,4128768],[(196,0)]),([6,135466,541808,1083264,2033663,2423372,4128768],[(157,0)]),([6,135466,541808,1083264,2033663,3923379,4128768],[]),([6,135466,541808,1083264,2097152,2423372,4128768],[]),([6,135466,541808,1083264,2152448,3923379,4128768],[(18,0)]),([6,135466,541808,1083264,2160640,2368076,4128768],[]),([6,135466,541808,1083264,2160640,2423372,4128768],[]),([6,135466,541808,1083264,2160640,2423372,4146288],[]),([6,135466,541808,1083264,2160640,2423372,4163456],[]),([6,135466,541808,1083264,2160640,2423372,4192256],[]),([6,135466,541808,1083264,2160640,3923379,4128768],[])]
noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,541808,1083264,2160640,3923379,4146288],[]),([6,135466,541808,1083264,2160640,3923379,4163456],[]),([6,135466,541808,1083264,2160640,3923379,4192256],[]),([6,135466,541808,1083264,2160640,3931571,4128768],[(18,0)]),([6,135466,541808,1083264,2292010,2423372,4128768],[(72,0)]),([6,135466,541808,1083264,2423372,2686064,4128768],[]),([6,135466,541808,1083264,2423372,3211136,4128768],[]),([6,135466,541808,1083264,2423372,3923379,4128768],[]),([6,135466,541808,1083264,3923379,4128768,4192256],[]),([6,135466,541808,1218474,2160640,2423372,4128768],[(96,0)]),([6,135466,541808,1218474,2160640,3923379,4128768],[(18,0)])]
noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([6,135466,541808,2160640,2423372,3111039,4128768],[]),([6,135466,541808,2160640,2423372,4128768,4163456],[]),([6,135466,541808,2160640,3111039,3923379,4128768],[]),([6,135466,541808,2160640,3923379,4128768,4163456],[]),([6,135466,1083264,2160640,2423372,3652495,4128768],[]),([6,135466,1083264,2160640,2423372,4128768,4146288],[]),([6,135466,1083264,2160640,3652495,3923379,4128768],[]),([6,135466,1083264,2160640,3923379,4128768,4146288],[]),([6,541808,1083264,1218474,2160640,2423372,4128768],[]),([6,541808,1083264,1218474,2160640,3923379,4128768],[]),([6,541808,1083264,2160640,3923379,4058837,4128768],[])]
noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([7,8,135466,270924,541808,1083264,2160640,4128768],[(73,0),(128,0),(130,0),(169,0),(138,0)]),([7,32,135466,270924,541808,1083264,2160640,4128768],[(2,0),(73,0),(128,0),(169,0)]),([7,256,135466,270924,541808,1083264,2160640,4128768],[(2,0),(73,0),(169,0)]),([7,512,135466,270924,541808,1083264,2160640,4128768],[(2,0),(56,0),(73,0),(169,0)]),([7,1024,135466,270924,541808,1083264,2160640,4128768],[(2,0),(56,0),(73,0),(169,0)]),([7,32768,135466,270924,541808,1083264,2160640,4128768],[(56,0),(58,0),(73,0),(169,0),(138,0)]),([7,65535,135466,270924,541808,1083264,2160640],[(169,0),(174,0),(6,0),(138,0),(137,0),(18,0)])]
noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([7,65535,135466,270924,541808,1083264,2160640,4128768],[(73,0),(77,0),(169,0),(172,0),(174,0),(173,0),(138,0),(248,0),(249,0)]),([7,131072,135466,270924,541808,1083264,2160640,4128768],[(2,0),(73,0),(128,0),(169,0)]),([7,135466,135466,270924,541808,1083264,2160640,4128768],[(2,0),(128,0),(169,0),(173,0)]),([7,135466,270924,406382,541808,1083264,2160640,4128768],[(97,0),(128,0),(130,0),(129,0),(217,0),(86,0),(185,0),(189,0)]),([7,135466,270924,524288,541808,1083264,2160640,4128768],[(72,0),(130,0),(82,0),(144,0),(185,0)]),([7,135466,270924,541808,541808,1083264,2160640,4128768],[(130,0),(82,0),(86,0),(185,0),(189,0)]),([7,135466,270924,541808,677242,1083264,2160640,4128768],[(57,0),(128,0),(129,0),(169,0),(110,0),(14,0),(193,0),(197,0)])]
noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([7,135466,270924,541808,1048576,1083264,2160640,4128768],[(96,0),(128,0),(14,0),(193,0)]),([7,135466,270924,541808,1083264,1083264,2160640,4128768],[(96,0),(14,0)]),([7,135466,270924,541808,1083264,1218474,2160640,4128768],[(57,0),(73,0),(98,0),(128,0),(169,0),(106,0),(114,0),(14,0),(152,0),(153,0),(193,0),(197,0),(241,0),(18,0),(205,0)]),([7,135466,270924,541808,1083264,1353676,2160640,4128768],[(96,0),(98,0),(142,0),(114,0),(240,0),(241,0),(18,0),(201,0),(205,0)]),([7,135466,270924,541808,1083264,1624048,2160640,4128768],[(96,0),(98,0),(82,0),(106,0),(193,0),(18,0),(205,0)]),([7,135466,270924,541808,1083264,2033663,2160640,4128768],[(98,0),(140,0),(142,0),(141,0),(18,0)]),([7,135466,270924,541808,1083264,2033663,4128768],[(2,0),(97,0),(141,0)])]
noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([7,135466,270924,541808,1083264,2160640,3211136,4128768],[(96,0),(98,0),(178,0),(182,0),(114,0),(206,0)]),([7,135466,270924,541808,1083264,2160640,3652495,4128768],[(98,0),(178,0),(182,0),(202,0),(206,0)]),([7,135466,270924,541808,1083264,2160640,3923379,4128768],[(98,0),(204,0),(206,0),(205,0),(22,0)]),([7,135466,270924,541808,1083264,2160640,4128768],[(2,0),(3,0),(98,0),(97,0),(131,0),(135,0),(5,0),(83,0),(87,0),(139,0),(143,0),(179,0),(183,0),(147,0),(151,0),(14,0),(15,0),(193,0),(17,0),(202,0),(203,0),(207,0)]),([7,135466,270924,541808,1083264,2160640,4128768,4128768],[(98,0),(178,0),(182,0),(192,0),(202,0),(206,0)]),([7,135466,270924,541808,1083264,2160640,4128768,4133162],[(57,0),(98,0),(230,0),(240,0),(250,0),(254,0),(26,0)]),([7,135466,270924,541808,1083264,2160640,4128768,4146288],[(98,0),(82,0),(178,0),(182,0),(226,0),(230,0),(202,0),(206,0),(250,0),(254,0)])]
noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([7,135466,270924,541808,1083264,2160640,4128768,4163456],[(98,0),(106,0),(178,0),(230,0),(240,0),(254,0),(26,0)]),([7,135466,270924,541808,1083264,2160640,4146288],[(2,0),(3,0),(98,0),(97,0),(131,0),(135,0),(5,0),(82,0),(83,0),(87,0),(139,0),(143,0),(179,0),(183,0),(147,0),(151,0),(14,0),(15,0),(17,0),(202,0),(203,0),(207,0)]),([7,135466,270924,541808,1083264,2160640,4163456],[(2,0),(97,0),(106,0),(14,0),(15,0),(22,0)]),([7,135466,270924,541808,1083264,2423372,4128768],[(2,0),(97,0),(135,0),(5,0),(83,0),(87,0),(143,0),(181,0),(183,0),(151,0),(14,0),(193,0)]),([7,135466,270924,541808,1083264,4128768,4192256],[(2,0),(97,0),(14,0)]),([7,135466,270924,1083264,2160640,3652495,4128768],[(2,0),(74,0),(73,0),(10,0),(185,0),(194,0)]),([7,135466,270924,1083264,2160640,4128768,4146288],[(2,0),(74,0),(73,0),(138,0),(10,0),(145,0)]),([7,135466,541808,1083264,2160640,2423372,4128768],[(2,0)])]
noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([7,135466,541808,1083264,2160640,3923379,4128768],[]),([8,135466,270924,541808,1083264,2160640,4128768],[(2,0),(3,0),(98,0),(97,0),(131,0),(135,0),(5,0),(83,0),(87,0),(139,0),(143,0),(179,0),(183,0),(147,0),(151,0),(14,0),(15,0),(193,0),(17,0),(202,0),(203,0),(207,0)])]
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = (((((K_0 ++ K_1) ++ (K_2 ++ (K_3 ++ K_4))) ++ ((K_5 ++ K_6) ++ (K_7 ++ (K_8 ++ K_9)))) ++ (((K_10 ++ K_11) ++ (K_12 ++ (K_13 ++ K_14))) ++ ((K_15 ++ K_16) ++ (K_17 ++ (K_18 ++ K_19))))) ++ ((((K_20 ++ K_21) ++ (K_22 ++ (K_23 ++ K_24))) ++ ((K_25 ++ K_26) ++ (K_27 ++ (K_28 ++ K_29)))) ++ (((K_30 ++ K_31) ++ (K_32 ++ (K_33 ++ K_34))) ++ ((K_35 ++ (K_36 ++ K_37)) ++ (K_38 ++ (K_39 ++ K_40)))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert ((all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 (all_app c_3 c_4))) (all_app (all_app c_5 c_6) (all_app c_7 (all_app c_8 c_9)))) (all_app (all_app (all_app c_10 c_11) (all_app c_12 (all_app c_13 c_14))) (all_app (all_app c_15 c_16) (all_app c_17 (all_app c_18 c_19))))) (all_app (all_app (all_app (all_app c_20 c_21) (all_app c_22 (all_app c_23 c_24))) (all_app (all_app c_25 c_26) (all_app c_27 (all_app c_28 c_29)))) (all_app (all_app (all_app c_30 c_31) (all_app c_32 (all_app c_33 c_34))) (all_app (all_app c_35 (all_app c_36 c_37)) (all_app c_38 (all_app c_39 c_40)))))))

set_option maxRecDepth 100000 in
theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461426206440680 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 9 :=
  ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461426206440680 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 9 ≤ t :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

end PEqualNP.Outside.V_meta_9962__k9_aux

theorem PEqualNP.Outside.V_meta_9962__k9 :
  PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461426206440680 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 9 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461426206440680 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 9 ≤ t :=
  ⟨PEqualNP.Outside.V_meta_9962__k9_aux.upper, PEqualNP.Outside.V_meta_9962__k9_aux.lower⟩
