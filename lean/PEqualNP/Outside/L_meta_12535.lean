import Mathlib.Data.Tree.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12535

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The certificate checker, the restriction lemma and the relabeling below are taken from the merged proof of
-- L-meta-11082 by MartinMatoJames, which names its own sources in the next two lines. The certificate itself
-- (the table of unreachable live-wire states and its symmetry hints) and the circuit are new, found by our own search.
-- The six-input certificate and its checker are from L-meta-9553 in this repository.
-- The one-gate restriction and wire relabeling are from L-meta-9479, following L-meta-927.

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

def BT := BinaryTree (List ℕ)

def BT.lf : BT := BinaryTree.nil

def BT.nd (l : BT) (k : List ℕ) (r : BT) : BT := BinaryTree.node k l r

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
  | .nil, _ => false
  | .node k l r, x => leqL x k || (if ltL x k then BT.mem l x else BT.mem r x)

def BT.toList : BT → List (List ℕ)
  | .nil => []
  | .node k l r => BT.toList l ++ k :: BT.toList r

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .nil, x, h => by simp [BT.mem] at h
  | .node k l r, x, hm => by
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


def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)


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

def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def M_ : ℕ := 4294967295
def Y_ : ℕ := 4276676840
def XS_ : List ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760]
def PD_ : List (ℕ × ℕ) := [(1,27040924),(2,22205138),(3,20313589),(4,17196646),(5,18853807),(6,18041675),(7,18168121),(8,1441792),(9,1547420),(10,1528530),(11,1521141),(12,460390),(13,466863),(14,201547),(15,70969),(16,5632),(17,6044),(18,5970),(19,5941),(20,1798),(21,1823),(22,787),(23,277),(24,22),(25,23),(26,23),(27,23),(28,7),(29,7),(30,3),(31,1)]
def PM_ : List (ℕ × ℕ) := [(0,4276676840),(1,4276676840),(2,4276676840),(4,4276676840),(8,4276676840),(9,4276676840),(10,4276676840),(12,4276676840),(16,4276676840),(17,4276676840),(18,4276676840),(20,4276676840),(24,4276676840)]
def G_ : List (List ℕ) := [[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31],[0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31],[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31],[0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31],[0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31],[0,2,4,6,1,3,5,7,16,18,20,22,17,19,21,23,8,10,12,14,9,11,13,15,24,26,28,30,25,27,29,31],[0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31],[0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23,8,12,9,13,10,14,11,15,24,28,25,29,26,30,27,31],[0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15,16,20,18,22,17,21,19,23,24,28,26,30,25,29,27,31],[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31]]

noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,2863311530,4241280204,4293980400] BT.lf) [2,2863311530,4243385580,4293980400] BT.lf) [2,2863311530,4244438268,4290822336] (BT.nd BT.lf [2,2863311530,4244438268,4291348680] BT.lf)) [2,2863311530,4274834636,4293980400] (BT.nd (BT.nd (BT.nd BT.lf [2,3941264106,4244438268,4278190080] BT.lf) [2,3941264106,4244438268,4278239232] BT.lf) [2,3941264106,4244438268,4290822336] (BT.nd BT.lf [2,4004162218,4243648752,4291611852] BT.lf))) [2,4008372970,4244438268,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,178956970,3435973836,4042322160,4278190080] BT.lf) [3,707406378,3435973836,4042322160,4278190080] BT.lf) [3,1056964608,2863311530,3435973836,4042322160] (BT.nd BT.lf [3,2290649224,4008636142,4042322160,4278190080] BT.lf)) [3,2290649224,4008636142,4042322160,4278224896] (BT.nd (BT.nd BT.lf [3,2290649224,4008636142,4042322160,4287137928] BT.lf) [3,2290649224,4008636142,4177066232,4278190080] (BT.nd BT.lf [3,2829625512,3435973836,4210752250,4278190080] BT.lf)))) [3,2852126720,3435973836,4042322160,4289374890] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2852126720,3435973836,4210094320,4289374890] BT.lf) [3,2861074568,3435973836,4042322160,4289374890] BT.lf) [3,2861074568,4008636142,4042322160,4278190080] (BT.nd BT.lf [3,2863179944,3435973836,4042322160,4278190080] BT.lf)) [3,2863180456,3435973836,4042322160,4278190080] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4042322160,4261412864] BT.lf) [3,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [3,2863311530,3435973836,4042322160,4278222848] BT.lf))) [3,2863311530,3435973836,4042322160,4278224896] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4042322160,4278233088] BT.lf) [3,2863311530,3435973836,4042322160,4286611584] BT.lf) [3,2863311530,3435973836,4042322160,4287137928] (BT.nd BT.lf [3,2863311530,3435973836,4042322160,4289243304] BT.lf)) [3,2863311530,3435973836,4176539888,4278190080] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4176541936,4278190080] BT.lf) [3,2863311530,3435973836,4177066232,4278190080] (BT.nd BT.lf [3,2863311530,3435973836,4177066232,4278224896] BT.lf))))) [3,2863311530,3435973836,4177066232,4287137928] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4194304000,4293980400] BT.lf) [3,2863311530,3435973836,4205488810,4293980400] BT.lf) [3,2863311530,3435973836,4210094320,4278190080] (BT.nd BT.lf [3,2863311530,3435973836,4210094320,4289374890] BT.lf)) [3,2863311530,3435973836,4210620664,4278190080] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4210752250,4288716960] BT.lf) [3,2863311530,3435973836,4277203184,4278190080] (BT.nd BT.lf [3,2863311530,3941264106,4244438268,4278190080] BT.lf))) [3,2863311530,3974950124,4210752250,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,4006399180,4210094320,4278190080] BT.lf) [3,2863311530,4241280204,4278190080,4293980400] BT.lf) [3,2863311530,4241280204,4278255360,4293980400] (BT.nd BT.lf [3,2863311530,4241280204,4293980400] BT.lf)) [3,2863311530,4244438268,4278190080,4290822336] (BT.nd (BT.nd BT.lf [3,2863311530,4244438268,4278255360,4290822336] BT.lf) [3,2863311530,4244438268,4290822336] (BT.nd BT.lf [3,2863311530,4244438268,4290838464,4294951104] BT.lf)))) [3,2863311530,4244438268,4291611852,4293980400] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,3941264106,4244438268,4278190080] BT.lf) [3,3941264106,4244438268,4278190080,4278255360] BT.lf) [3,3941264106,4244438268,4278255360,4294901760] (BT.nd BT.lf [3,3941264106,4244438268,4278255360,4294951104] BT.lf)) [3,4008636142,4210752250,4244438268,4278190080] (BT.nd (BT.nd BT.lf [4,0,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,255,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,3855,2863311530,3435973836,4042322160,4278190080] BT.lf))) [4,43690,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,65280,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,65535,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,986895,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,11184810,2863311530,3435973836,4042322160,4278190080] BT.lf)) [4,16777215,252645135,2863311530,3435973836] (BT.nd (BT.nd BT.lf [4,16777215,2863311530,3435973836,4042322160] BT.lf) [4,16777215,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,50529027,2863311530,3435973836,4042322160,4278190080] BT.lf)))))) [4,168430090,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,251658240,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,251662080,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,252645135,858993459,2863311530,4278190080] (BT.nd BT.lf [4,252645135,2863311530,3435973836,4042322160,4278190080] BT.lf)) [4,252645135,2863311530,3435973836,4278190080] (BT.nd (BT.nd BT.lf [4,252706815,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,268435455,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,707406378,3435973836,4042322160,4278255360,4294901760] BT.lf))) [4,1056980736,2863311530,3435973836,4042322160,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1061109567,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,2155905152,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,2281701376,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,2281736192,2863311530,3435973836,4042322160,4278190080] BT.lf)) [4,2290649224,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd BT.lf [4,2290649224,2863311530,3435973836,4042322160,4278224896] BT.lf) [4,2290649224,2863311530,3435973836,4042322160,4287137928] (BT.nd BT.lf [4,2290649224,2863311530,3435973836,4177066232,4278190080] BT.lf)))) [4,2290649224,2863311530,4008636142,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4278190080] BT.lf) [4,2290649224,4008636142,4042322160,4278190080,4278255360] BT.lf) [4,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4278255360,4294936712] BT.lf)) [4,2290649224,4008636142,4177066232,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2829625512,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,2829625512,3435973836,4210752250,4278255360,4294901760] (BT.nd BT.lf [4,2852126720,2863311530,3435973836,4042322160,4278190080] BT.lf))) [4,2852126720,2863311530,3435973836,4042322160,4289374890] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2852126720,2863311530,3435973836,4210094320,4278190080] BT.lf) [4,2852126720,3435973836,4042322160,4278190080,4289374890] BT.lf) [4,2852126720,3435973836,4042322160,4278255360,4289374890] (BT.nd BT.lf [4,2852126720,3435973836,4042322160,4289374890] BT.lf)) [4,2852170240,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd BT.lf [4,2852170240,2863311530,3435973836,4042322160,4289331200] BT.lf) [4,2852170240,3435973836,4042322160,4278190080,4289374890] (BT.nd BT.lf [4,2852170240,3435973836,4042322160,4289374890,4294901760] BT.lf))))) [4,2861074568,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2861083272,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,2863311360,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,2863311530,2863311530,3435973836,4042322160,4278190080] BT.lf)) [4,2863311530,2863333375,3435973836,4042322160,4278190080] (BT.nd (BT.nd BT.lf [4,2863311530,2868903935,3435973836,4042322160,4278190080] BT.lf) [4,2863311530,2947526575,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,2863311530,3435973836,3941264106,4042322160,4278190080] BT.lf))) [4,2863311530,3435973836,3992977408,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3993038336,4042322160,4278190080] BT.lf) [4,2863311530,3435973836,4004162218,4042322160,4278190080] BT.lf) [4,2863311530,3435973836,4004179626,4042322160,4278190080] (BT.nd BT.lf [4,2863311530,3435973836,4008636142,4042322160,4278190080] BT.lf)) [4,2863311530,3435973836,4042322160,4261477888,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278124286,4278190080] BT.lf) [4,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4278190080] BT.lf)))) [4,2863311530,3435973836,4042322160,4278190080,4278233600] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf) [4,2863311530,3435973836,4042322160,4278190080,4278255615] BT.lf) [4,2863311530,3435973836,4042322160,4278190080,4279176975] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4279238415] BT.lf)) [4,2863311530,3435973836,4042322160,4278190080,4287137928] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4287168392] BT.lf) [4,2863311530,3435973836,4042322160,4278190080,4289374890] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4289396480] BT.lf))) [4,2863311530,3435973836,4042322160,4278190080,4289396650] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4293848814] BT.lf) [4,2863311530,3435973836,4042322160,4278190080,4293853166] BT.lf) [4,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278190080,4294967210] BT.lf)) [4,2863311530,3435973836,4042322160,4278190080,4294967295] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278193920,4294901760] BT.lf) [4,2863311530,3435973836,4042322160,4278224896] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278224896,4278255360] BT.lf))))))) [4,2863311530,3435973836,4042322160,4278224896,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278224896,4294936712] BT.lf) [4,2863311530,3435973836,4042322160,4278233600,4294901760] BT.lf) [4,2863311530,3435973836,4042322160,4278233600,4294954188] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278251008,4294901760] BT.lf)) [4,2863311530,3435973836,4042322160,4278255360,4287137928] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901775] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901930] BT.lf))) [4,2863311530,3435973836,4042322160,4278255360,4294902015] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294936576] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294944936] BT.lf)) [4,2863311530,3435973836,4042322160,4287137928] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287168392,4294936712] BT.lf) [4,2863311530,3435973836,4042322160,4289374890,4291611852] (BT.nd BT.lf [4,2863311530,3435973836,4176541936,4278255360,4294901760] BT.lf)))) [4,2863311530,3435973836,4177066232,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4177066232,4278190080,4278255360] BT.lf) [4,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4177066232,4278255360,4294936712] (BT.nd BT.lf [4,2863311530,3435973836,4210094320,4278190080] BT.lf)) [4,2863311530,3435973836,4210094320,4278190080,4278255360] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4210094320,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4210752250,4244438268,4278190080] (BT.nd BT.lf [4,2863311530,3435973836,4210752250,4278190080,4293980400] BT.lf))) [4,2863311530,3941264106,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3974950124,4210752250,4278255360,4294901760] BT.lf) [4,3941264106,4244438268,4278255360,4294901760] BT.lf) [4,4008636142,4210752250,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,255,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,3855,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,65280,2863311530,3435973836,4042322160,4278255360] BT.lf))))) [5,65280,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [5,65535,252645135,2863311530,3435973836,4278255360] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278190080] (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf)) [5,65535,2863311530,3435973836,4042322160,4278190080,4294901760] (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278255615] BT.lf))) [5,65535,2863311530,3435973836,4042322160,4278255615,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16777215,2863311530,3435973836,4042322160] BT.lf) [5,16777215,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,16777215,2863311530,3435973836,4042322160,4278190080,4278255360] (BT.nd BT.lf [5,16777215,2863311530,3435973836,4042322160,4278255360] BT.lf)) [5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,50529027,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,168430090,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,251662080,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,252645135,858993459,2863311530,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,252645135,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,252645135,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf) [5,252645135,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,252645135,2863311530,3435973836,4278190080] BT.lf)) [5,252645135,2863311530,3435973836,4278190080,4278255360] (BT.nd (BT.nd BT.lf [5,252645135,2863311530,3435973836,4278255360,4294901760] BT.lf) [5,252706815,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1061109567,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2281736192,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4278190080,4278255360] (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf)))))) [5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2852126720,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,2852126720,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf) [5,2852126720,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2852170240,2863311530,3435973836,4042322160,4278190080] BT.lf)) [5,2852170240,2863311530,3435973836,4042322160,4278190080,4278255360] (BT.nd (BT.nd BT.lf [5,2852170240,2863311530,3435973836,4042322160,4278190080,4294901760] BT.lf) [5,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2852170240,2863311530,3435973836,4042322160,4289396650,4294901760] BT.lf))) [5,2861083272,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311360,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,2863311530,2863311530,3435973836,4042322160,4278190080,4278255360] (BT.nd BT.lf [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,2947526575,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3993038336,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,3435973836,4004179626,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042322160,4278190080] BT.lf) [5,2863311530,3435973836,4008636142,4042322160,4278190080,4278255360] BT.lf) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278190080,4278190080] BT.lf) [5,2863311530,3435973836,4042322160,4278190080,4278190080,4278255360] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf))) [5,2863311530,3435973836,4042322160,4278190080,4278255360,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278190080,4278255360,4289374890] BT.lf) [5,2863311530,3435973836,4042322160,4278190080,4278255360,4289396650] BT.lf) [5,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278190080,4278255360,4294945450] BT.lf)) [5,2863311530,3435973836,4042322160,4278190080,4278255360,4294967040] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278190080,4289374890] BT.lf) [5,2863311530,3435973836,4042322160,4278190080,4289396650] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf))))) [5,2863311530,3435973836,4042322160,4278233600,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278233600,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278233600,4294901760,4294945450] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4278255615,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4279238415,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4287168392,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4289374890,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4289396480,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4293853166,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967210] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294902015] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188] BT.lf)))) [5,2863311530,3435973836,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4210752250,4244438268,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,252645135,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,252645135,2863311530,3435973836,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278190080] BT.lf) [6,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf) [6,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd BT.lf [7,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,2863311530,4241280204,4293980400],[]),([2,2863311530,4243385580,4293980400],[]),([2,2863311530,4244438268,4290822336],[]),([2,2863311530,4244438268,4291348680],[]),([2,2863311530,4274834636,4293980400],[]),([2,3941264106,4244438268,4278190080],[]),([2,3941264106,4244438268,4278239232],[]),([2,3941264106,4244438268,4290822336],[]),([2,4004162218,4243648752,4291611852],[]),([2,4008372970,4244438268,4278190080],[]),([3,178956970,3435973836,4042322160,4278190080],[]),([3,707406378,3435973836,4042322160,4278190080],[]),([3,1056964608,2863311530,3435973836,4042322160],[]),([3,2290649224,4008636142,4042322160,4278190080],[(72,7),(96,7)]),([3,2290649224,4008636142,4042322160,4278224896],[(72,7),(96,7)]),([3,2290649224,4008636142,4042322160,4287137928],[(56,7),(72,7),(96,7)]),([3,2290649224,4008636142,4177066232,4278190080],[(56,7),(72,7),(96,7)]),([3,2829625512,3435973836,4210752250,4278190080],[(56,3),(96,3)]),([3,2852126720,3435973836,4042322160,4289374890],[(56,9),(72,5)]),([3,2852126720,3435973836,4210094320,4289374890],[(56,3),(72,5),(96,5)]),([3,2861074568,3435973836,4042322160,4289374890],[(56,9),(72,5)]),([3,2861074568,4008636142,4042322160,4278190080],[(72,7),(96,7)]),([3,2863179944,3435973836,4042322160,4278190080],[]),([3,2863180456,3435973836,4042322160,4278190080],[]),([3,2863311530,3435973836,4042322160,4261412864],[]),([3,2863311530,3435973836,4042322160,4278190080],[]),([3,2863311530,3435973836,4042322160,4278222848],[]),([3,2863311530,3435973836,4042322160,4278224896],[]),([3,2863311530,3435973836,4042322160,4278233088],[]),([3,2863311530,3435973836,4042322160,4286611584],[]),([3,2863311530,3435973836,4042322160,4287137928],[(56,7)]),([3,2863311530,3435973836,4042322160,4289243304],[(56,7),(72,3)]),([3,2863311530,3435973836,4176539888,4278190080],[]),([3,2863311530,3435973836,4176541936,4278190080],[]),([3,2863311530,3435973836,4177066232,4278190080],[(56,7)]),([3,2863311530,3435973836,4177066232,4278224896],[(56,7)]),([3,2863311530,3435973836,4177066232,4287137928],[(56,7)]),([3,2863311530,3435973836,4194304000,4293980400],[(72,3)]),([3,2863311530,3435973836,4205488810,4293980400],[(72,3)]),([3,2863311530,3435973836,4210094320,4278190080],[(96,5)]),([3,2863311530,3435973836,4210094320,4289374890],[(96,5)]),([3,2863311530,3435973836,4210620664,4278190080],[(56,7),(96,5)]),([3,2863311530,3435973836,4210752250,4288716960],[(72,3)]),([3,2863311530,3435973836,4277203184,4278190080],[(96,5),(104,1)]),([3,2863311530,3941264106,4244438268,4278190080],[]),([3,2863311530,3974950124,4210752250,4278190080],[(72,3)]),([3,2863311530,4006399180,4210094320,4278190080],[(96,3)]),([3,2863311530,4241280204,4278190080,4293980400],[]),([3,2863311530,4241280204,4278255360,4293980400],[]),([3,2863311530,4241280204,4293980400],[]),([3,2863311530,4244438268,4278190080,4290822336],[]),([3,2863311530,4244438268,4278255360,4290822336],[]),([3,2863311530,4244438268,4290822336],[]),([3,2863311530,4244438268,4290838464,4294951104],[]),([3,2863311530,4244438268,4291611852,4293980400],[(108,1)]),([3,3941264106,4244438268,4278190080],[]),([3,3941264106,4244438268,4278190080,4278255360],[]),([3,3941264106,4244438268,4278255360,4294901760],[]),([3,3941264106,4244438268,4278255360,4294951104],[]),([3,4008636142,4210752250,4244438268,4278190080],[(76,3),(84,7)]),([4,0,2863311530,3435973836,4042322160,4278190080],[]),([4,255,2863311530,3435973836,4042322160,4278190080],[]),([4,3855,2863311530,3435973836,4042322160,4278190080],[]),([4,43690,2863311530,3435973836,4042322160,4278190080],[]),([4,65280,2863311530,3435973836,4042322160,4278190080],[]),([4,65535,2863311530,3435973836,4042322160,4278190080],[]),([4,986895,2863311530,3435973836,4042322160,4278190080],[]),([4,11184810,2863311530,3435973836,4042322160,4278190080],[]),([4,16777215,252645135,2863311530,3435973836],[]),([4,16777215,2863311530,3435973836,4042322160],[]),([4,16777215,2863311530,3435973836,4042322160,4278190080],[]),([4,50529027,2863311530,3435973836,4042322160,4278190080],[]),([4,168430090,2863311530,3435973836,4042322160,4278190080],[]),([4,251658240,2863311530,3435973836,4042322160,4278190080],[]),([4,251662080,2863311530,3435973836,4042322160,4278190080],[]),([4,252645135,858993459,2863311530,4278190080],[]),([4,252645135,2863311530,3435973836,4042322160,4278190080],[]),([4,252645135,2863311530,3435973836,4278190080],[]),([4,252706815,2863311530,3435973836,4042322160,4278190080],[]),([4,268435455,2863311530,3435973836,4042322160,4278190080],[(76,3)]),([4,707406378,3435973836,4042322160,4278255360,4294901760],[]),([4,1056980736,2863311530,3435973836,4042322160,4294901760],[]),([4,1061109567,2863311530,3435973836,4042322160,4278190080],[]),([4,2155905152,2863311530,3435973836,4042322160,4278190080],[]),([4,2281701376,2863311530,3435973836,4042322160,4278190080],[]),([4,2281736192,2863311530,3435973836,4042322160,4278190080],[]),([4,2290649224,2863311530,3435973836,4042322160,4278190080],[]),([4,2290649224,2863311530,3435973836,4042322160,4278224896],[]),([4,2290649224,2863311530,3435973836,4042322160,4287137928],[]),([4,2290649224,2863311530,3435973836,4177066232,4278190080],[]),([4,2290649224,2863311530,4008636142,4042322160,4278190080],[(96,1),(128,1)]),([4,2290649224,4008636142,4042322160,4278190080],[(72,7),(73,7),(96,7),(97,7)]),([4,2290649224,4008636142,4042322160,4278190080,4278255360],[(72,7),(96,7)]),([4,2290649224,4008636142,4042322160,4278255360,4294901760],[(72,7)]),([4,2290649224,4008636142,4042322160,4278255360,4294936712],[(72,7),(96,7)]),([4,2290649224,4008636142,4177066232,4278255360,4294901760],[(56,7),(72,7),(96,8),(128,7)]),([4,2829625512,2863311530,3435973836,4042322160,4278190080],[(72,1),(80,1)]),([4,2829625512,3435973836,4210752250,4278255360,4294901760],[(56,3)]),([4,2852126720,2863311530,3435973836,4042322160,4278190080],[(72,1)]),([4,2852126720,2863311530,3435973836,4042322160,4289374890],[(72,1)])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,2852126720,2863311530,3435973836,4210094320,4278190080],[]),([4,2852126720,3435973836,4042322160,4278190080,4289374890],[(56,9),(72,5)]),([4,2852126720,3435973836,4042322160,4278255360,4289374890],[(56,9),(72,5)]),([4,2852126720,3435973836,4042322160,4289374890],[(56,9),(58,1),(57,5),(72,5),(73,9)]),([4,2852170240,2863311530,3435973836,4042322160,4278190080],[]),([4,2852170240,2863311530,3435973836,4042322160,4289331200],[]),([4,2852170240,3435973836,4042322160,4278190080,4289374890],[]),([4,2852170240,3435973836,4042322160,4289374890,4294901760],[]),([4,2861074568,2863311530,3435973836,4042322160,4278190080],[(72,1)]),([4,2861083272,2863311530,3435973836,4042322160,4278190080],[]),([4,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311360,2863311530,3435973836,4042322160,4278190080],[]),([4,2863311530,2863311530,3435973836,4042322160,4278190080],[]),([4,2863311530,2863333375,3435973836,4042322160,4278190080],[]),([4,2863311530,2868903935,3435973836,4042322160,4278190080],[]),([4,2863311530,2947526575,3435973836,4042322160,4278190080],[]),([4,2863311530,3435973836,3941264106,4042322160,4278190080],[(72,5)]),([4,2863311530,3435973836,3992977408,4042322160,4278190080],[(72,5),(128,5),(80,1),(136,1)]),([4,2863311530,3435973836,3993038336,4042322160,4278190080],[]),([4,2863311530,3435973836,4004162218,4042322160,4278190080],[(72,5),(136,1)]),([4,2863311530,3435973836,4004179626,4042322160,4278190080],[]),([4,2863311530,3435973836,4008636142,4042322160,4278190080],[]),([4,2863311530,3435973836,4042322160,4261477888,4294901760],[]),([4,2863311530,3435973836,4042322160,4278124286,4278190080],[]),([4,2863311530,3435973836,4042322160,4278190080],[]),([4,2863311530,3435973836,4042322160,4278190080,4278190080],[]),([4,2863311530,3435973836,4042322160,4278190080,4278233600],[]),([4,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([4,2863311530,3435973836,4042322160,4278190080,4278255615],[]),([4,2863311530,3435973836,4042322160,4278190080,4279176975],[]),([4,2863311530,3435973836,4042322160,4278190080,4279238415],[]),([4,2863311530,3435973836,4042322160,4278190080,4287137928],[(56,7)]),([4,2863311530,3435973836,4042322160,4278190080,4287168392],[]),([4,2863311530,3435973836,4042322160,4278190080,4289374890],[]),([4,2863311530,3435973836,4042322160,4278190080,4289396480],[]),([4,2863311530,3435973836,4042322160,4278190080,4289396650],[]),([4,2863311530,3435973836,4042322160,4278190080,4293848814],[(148,7)]),([4,2863311530,3435973836,4042322160,4278190080,4293853166],[(148,7)]),([4,2863311530,3435973836,4042322160,4278190080,4294967040],[]),([4,2863311530,3435973836,4042322160,4278190080,4294967210],[]),([4,2863311530,3435973836,4042322160,4278190080,4294967295],[]),([4,2863311530,3435973836,4042322160,4278193920,4294901760],[]),([4,2863311530,3435973836,4042322160,4278224896],[]),([4,2863311530,3435973836,4042322160,4278224896,4278255360],[]),([4,2863311530,3435973836,4042322160,4278224896,4294901760],[]),([4,2863311530,3435973836,4042322160,4278224896,4294936712],[]),([4,2863311530,3435973836,4042322160,4278233600,4294901760],[]),([4,2863311530,3435973836,4042322160,4278233600,4294954188],[]),([4,2863311530,3435973836,4042322160,4278251008,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4287137928],[(56,7)]),([4,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901775],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901930],[]),([4,2863311530,3435973836,4042322160,4278255360,4294902015],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936576],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([4,2863311530,3435973836,4042322160,4278255360,4294944936],[]),([4,2863311530,3435973836,4042322160,4287137928],[(56,7),(58,1),(57,5)]),([4,2863311530,3435973836,4042322160,4287168392,4294936712],[(56,7)]),([4,2863311530,3435973836,4042322160,4289374890,4291611852],[(56,7),(108,3)]),([4,2863311530,3435973836,4176541936,4278255360,4294901760],[]),([4,2863311530,3435973836,4177066232,4278190080],[(56,7),(58,1),(57,5)]),([4,2863311530,3435973836,4177066232,4278190080,4278255360],[(56,7)]),([4,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,7)]),([4,2863311530,3435973836,4177066232,4278255360,4294936712],[(56,7)]),([4,2863311530,3435973836,4210094320,4278190080],[(96,5),(97,5)]),([4,2863311530,3435973836,4210094320,4278190080,4278255360],[(96,5)]),([4,2863311530,3435973836,4210094320,4278255360,4294901760],[]),([4,2863311530,3435973836,4210752250,4244438268,4278190080],[(84,3)]),([4,2863311530,3435973836,4210752250,4278190080,4293980400],[(96,3),(132,1)]),([4,2863311530,3941264106,4244438268,4278255360,4294901760],[]),([4,2863311530,3974950124,4210752250,4278255360,4294901760],[(72,3)]),([4,3941264106,4244438268,4278255360,4294901760],[(117,0)]),([4,4008636142,4210752250,4244438268,4278255360,4294901760],[(76,3),(84,7)]),([5,0,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,3855,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,65280,2863311530,3435973836,4042322160,4278255360],[]),([5,65280,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,16711935,2863311530,3435973836,4042322160],[]),([5,65535,252645135,2863311530,3435973836,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278190080],[(2,0),(73,3),(77,3),(97,7),(101,7)]),([5,65535,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278190080,4294901760],[(128,0)]),([5,65535,2863311530,3435973836,4042322160,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,65535,2863311530,3435973836,4042322160,4278255615],[(2,0)]),([5,65535,2863311530,3435973836,4042322160,4278255615,4294901760],[(128,0)]),([5,16777215,2863311530,3435973836,4042322160],[(6,5),(10,1)]),([5,16777215,2863311530,3435973836,4042322160,4278190080],[(73,3),(77,3),(97,7),(101,7)]),([5,16777215,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([5,16777215,2863311530,3435973836,4042322160,4278255360],[]),([5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,50529027,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,168430090,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,251662080,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,252645135,858993459,2863311530,4278255360,4294901760],[]),([5,252645135,2863311530,3435973836,4042322160,4278190080],[(2,7),(73,3),(77,3)])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([5,252645135,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([5,252645135,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,252645135,2863311530,3435973836,4278190080],[(6,3)]),([5,252645135,2863311530,3435973836,4278190080,4278255360],[]),([5,252645135,2863311530,3435973836,4278255360,4294901760],[]),([5,252706815,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1061109567,2863311530,3435973836,4042322160,4278255360,4294901760],[(172,0)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2281736192,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3435973836,4042322160,4278190080],[(2,7),(73,3),(97,7),(81,3)]),([5,2290649224,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,2290649224,2863311530,3435973836,4177066232,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(96,1)]),([5,2290649224,4008636142,4042322160,4278255360,4294901760],[(72,7),(73,7),(98,0),(157,0)]),([5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,1),(128,0),(80,1)]),([5,2852126720,2863311530,3435973836,4042322160,4278190080],[(2,5),(72,1),(74,1),(73,3),(97,7),(101,1)]),([5,2852126720,2863311530,3435973836,4042322160,4278190080,4278255360],[(72,1)]),([5,2852126720,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,1)]),([5,2852170240,2863311530,3435973836,4042322160,4278190080],[(2,6),(73,3),(97,7),(101,1)]),([5,2852170240,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([5,2852170240,2863311530,3435973836,4042322160,4278190080,4294901760],[(56,0),(168,0)]),([5,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2852170240,2863311530,3435973836,4042322160,4289396650,4294901760],[]),([5,2861083272,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2863311360,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311530,3435973836,4042322160,4278190080],[(2,5),(97,1),(101,1)]),([5,2863311530,2863311530,3435973836,4042322160,4278190080,4278255360],[]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2947526575,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(72,5)]),([5,2863311530,3435973836,3993038336,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4004179626,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4008636142,4042322160,4278190080],[(61,3),(97,5),(129,5),(86,3),(105,1),(137,1),(10,7),(117,7)]),([5,2863311530,3435973836,4008636142,4042322160,4278190080,4278255360],[]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(196,0)]),([5,2863311530,3435973836,4042322160,4278190080],[(2,5),(3,5),(75,1),(79,1),(5,3),(6,1),(7,1),(83,5),(87,5),(107,3),(111,3),(9,7),(115,7),(119,7)]),([5,2863311530,3435973836,4042322160,4278190080,4278190080],[(106,3),(110,3),(114,7),(118,7)]),([5,2863311530,3435973836,4042322160,4278190080,4278190080,4278255360],[]),([5,2863311530,3435973836,4042322160,4278190080,4278255360],[(138,3),(142,3),(146,7),(150,7),(18,0)]),([5,2863311530,3435973836,4042322160,4278190080,4278255360,4278255360],[]),([5,2863311530,3435973836,4042322160,4278190080,4278255360,4289374890],[]),([5,2863311530,3435973836,4042322160,4278190080,4278255360,4289396650],[]),([5,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(156,0)]),([5,2863311530,3435973836,4042322160,4278190080,4278255360,4294945450],[(156,0)]),([5,2863311530,3435973836,4042322160,4278190080,4278255360,4294967040],[]),([5,2863311530,3435973836,4042322160,4278190080,4289374890],[(57,5),(73,9),(142,3),(114,1),(146,1),(150,7),(18,5)]),([5,2863311530,3435973836,4042322160,4278190080,4289396650],[(142,3),(146,1),(150,7),(18,6)]),([5,2863311530,3435973836,4042322160,4278190080,4294967040],[(138,3),(142,3),(146,7),(150,7)]),([5,2863311530,3435973836,4042322160,4278233600,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4278233600,4294901760],[(134,0),(146,1),(157,0)]),([5,2863311530,3435973836,4042322160,4278233600,4294901760,4294945450],[(156,0)]),([5,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4278255360,4278255615,4294901760],[(152,0)]),([5,2863311530,3435973836,4042322160,4278255360,4279238415,4294901760],[(204,0)]),([5,2863311530,3435973836,4042322160,4278255360,4287168392,4294901760],[(152,0),(204,0)]),([5,2863311530,3435973836,4042322160,4278255360,4289374890,4294901760],[(172,0),(204,0)]),([5,2863311530,3435973836,4042322160,4278255360,4289396480,4294901760],[(204,0)]),([5,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[(204,0)]),([5,2863311530,3435973836,4042322160,4278255360,4293853166,4294901760],[(148,7),(204,0)]),([5,2863311530,3435973836,4042322160,4278255360,4294901760],[(157,0)]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967210],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([5,2863311530,3435973836,4042322160,4278255360,4294902015],[(157,0)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188],[(196,3)]),([5,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,7),(58,1),(57,5),(157,0)]),([5,2863311530,3435973836,4210752250,4244438268,4278255360,4294901760],[(84,3)]),([6,65535,2863311530,3435973836,4042322160,4278255360],[(6,5),(10,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,0),(73,3),(77,3),(97,7),(101,7),(128,0)]),([6,252645135,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,7),(73,3),(77,3),(169,0),(173,0),(205,0)]),([6,252645135,2863311530,3435973836,4278255360,4294901760],[(6,3),(14,0),(157,0)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,7),(73,3),(97,7),(128,0),(130,0),(169,0),(173,0),(81,3),(205,0)]),([6,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,6),(73,3),(97,7),(101,1),(169,0)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,5),(97,1),(101,1),(169,0),(173,0),(205,0)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(61,3),(97,5),(86,3),(105,1),(10,7),(117,7),(185,0),(189,0),(205,0)]),([6,2863311530,3435973836,4042322160,4278190080],[(2,5),(3,5),(75,1),(79,1),(5,3),(6,1),(7,1),(83,5),(87,5),(107,3),(111,3),(9,7),(115,7),(119,7)]),([6,2863311530,3435973836,4042322160,4278190080,4278255360],[(2,5),(3,5),(75,1),(79,1),(5,3),(6,1),(7,1),(83,5),(87,5),(107,3),(111,3),(138,3),(139,3),(142,3),(143,3),(9,7),(115,7),(119,7),(146,7),(147,7),(150,7),(151,7),(18,0),(19,0)]),([6,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(130,0),(174,0),(106,3),(110,3),(138,4),(142,3),(178,3),(182,4),(114,7),(118,7),(146,8),(150,7),(186,7),(190,8),(156,0),(158,0),(193,0),(18,0),(201,0),(205,0)]),([6,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[(106,3),(110,3),(114,7),(118,7),(14,0)]),([6,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[(106,0),(142,3),(114,2),(146,1),(150,7),(197,0),(18,6),(204,0),(206,0),(205,0)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,5),(3,5),(75,1),(79,1),(131,0),(135,0),(5,3),(6,1),(7,1),(83,5),(87,5),(107,3),(111,3),(139,4),(143,4),(9,7),(115,7),(119,7),(147,8),(151,8),(14,0),(15,0),(157,0),(17,0)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(178,3),(182,3),(186,7),(190,7),(157,0),(206,0)]),([7,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,5),(3,5),(75,1),(79,1),(131,0),(135,0),(5,3),(6,1),(7,1),(83,5),(87,5),(107,3),(111,3),(139,4),(143,4),(9,7),(115,7),(119,7),(147,8),(151,8),(14,0),(15,0),(157,0),(17,0)])]
set_option maxRecDepth 100000 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = (((K_0 ++ K_1) ++ K_2)).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app c_0 c_1) c_2)

theorem base : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 4276676840 ((if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) + (if x 3 then 8 else 0) + (if x 4 then 16 else 0))) s → 8 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

namespace Restrict

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

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

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

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
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

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end Restrict

def idx6 (x : Fin 6 → Bool) : ℕ :=
  (if x 0 then 2 ^ 0 else 0) + (if x 1 then 2 ^ 1 else 0) + (if x 2 then 2 ^ 2 else 0) +
    (if x 3 then 2 ^ 3 else 0) + (if x 4 then 2 ^ 4 else 0) + (if x 5 then 2 ^ 5 else 0)

theorem sum_eq (x : Fin 6 → Bool) : (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  rw [Fin.sum_univ_six]; rfl

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241824 * 2 ^ 32 + 3936414368) (idx6 x)

def reorder : Fin 6 → Fin 6 := ![0, 5, 1, 2, 3, 4]

def reordered (x : Fin 6 → Bool) : Bool := target (x ∘ reorder)

set_option maxRecDepth 100000 in
theorem required (s : ℕ) (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  have permuted : HasCircuitSize 6 reordered s := Restrict.relabel_size reorder target s h
  have changes : ∃ x : Fin 6 → Bool,
      reordered (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ reordered x :=
    ⟨fun i => decide (i = 1 ∨ i = 2), by decide +kernel⟩
  have nonconstant : ∃ y z : Fin 5 → Bool, reordered (Fin.snoc y true) ≠ reordered (Fin.snoc z true) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨t, shorter, residual⟩ := Restrict.gate_elim_one 5 reordered true s changes nonconstant permuted
  have restricted : (fun y : Fin 5 → Bool => reordered (Fin.snoc y true)) = (fun x : Fin 5 → Bool => Nat.testBit 4276676840 ((if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) + (if x 3 then 8 else 0) + (if x 4 then 16 else 0))) := by
    funext y
    revert y
    decide +kernel
  rw [restricted] at residual
  have := base t residual
  omega

def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [12, 13]⟩], 14⟩

set_option maxRecDepth 100000 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12535

open PEqualNP.Outside.L_meta_12535 PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_12535 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241824 * 2 ^ 32 + 3936414368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3936414368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have h' : HasCircuitSize 6 target s := by
    obtain ⟨C, ok, sz, ev⟩ := h
    refine ⟨C, ok, sz, fun x => (ev x).trans ?_⟩
    show Nat.testBit (4008241824 * 2 ^ 32 + 3936414368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = target x
    rw [sum_eq]; rfl
  have big := required s h'
  refine ⟨witness, by simp [Monotone2, witness], ?_, fun x => ?_⟩
  · have : witness.size = 9 := rfl
    omega
  · show witness.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3936414368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
    rw [witnessCorrect x, sum_eq]; rfl
