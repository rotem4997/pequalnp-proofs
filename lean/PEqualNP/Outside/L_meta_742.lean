import Mathlib
import PEqualNP.Defs

-- Generic Run normalization adapted from Digger-Rockwell PR801, Apache-2.0.
-- Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
-- Monotone preservation, directed coverage, and this finite certificate are new.


namespace PEqualNP.Outside.L_meta_742_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

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
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

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

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [simpStep, List.length_append]
      cases (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
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
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
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
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
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


abbrev prism : BFn 6 := fun x : Fin 6 → Bool =>
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) ||
  (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5) ||
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)

theorem prism_iff (x : Fin 6 → Bool) :
    prism x = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true := by
  constructor
  · intro h
    simp only [prism,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with ((((((((⟨h0,h1⟩ | ⟨h0,h2⟩) | ⟨h1,h2⟩) | ⟨h3,h4⟩) | ⟨h3,h5⟩) |
      ⟨h4,h5⟩) | ⟨h0,h3⟩) | ⟨h1,h4⟩) | ⟨h2,h5⟩)
    · exact ⟨0,1,by simp,h0,h1⟩
    · exact ⟨0,2,by simp,h0,h2⟩
    · exact ⟨1,2,by simp,h1,h2⟩
    · exact ⟨3,4,by simp,h3,h4⟩
    · exact ⟨3,5,by simp,h3,h5⟩
    · exact ⟨4,5,by simp,h4,h5⟩
    · exact ⟨0,3,by simp,h0,h3⟩
    · exact ⟨1,4,by simp,h1,h4⟩
    · exact ⟨2,5,by simp,h2,h5⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    fin_cases u <;> fin_cases v <;> simp_all [prism]

theorem prism_hasCircuit {C : Circuit} (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) (hs : C.size ≤ 9) :
    HasCircuitSize 6 prism 9 := by
  refine ⟨C,?_,hs,?_⟩
  · intro g hg
    obtain ⟨hop,hlen⟩ := hmono g hg
    refine ⟨?_,hlen⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro x
    rw [Bool.eq_iff_iff,hev x,prism_iff x]

theorem prism_run (h : HasCircuitSize 6 prism 9) :
    ∃ s, s ≤ 9 ∧ ∃ ws : List (BFn 6),
      ws.Sublist (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)) ∧
      Run (invF (n := 6)) meetF joinF prism s ws :=
  exists_run prism ⟨fun _ => false,fun _ => true,by decide⟩ 9 h

theorem encoded_prism_bridge (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL prism rows = goal k)
    (hmask : mask k = 2 ^ rows.length - 1)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ 9, ¬ NatRun (mask k) (goal k) s xs) :
    ¬ HasCircuitSize 6 prism 9 := by
  intro h
  obtain ⟨s,hs,ws,hsub,hrun⟩ := prism_run h
  have hr : NatRun (mask k) (encL prism rows) s (ws.map (fun a => encL a rows)) :=
    Run.map (fun a : BFn 6 => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hz : (ws.map (fun a => encL a rows)).Sublist xs := by
    rw [← hinputs]
    exact hsub.map _
  by_cases he : ws.map (fun a => encL a rows) = xs
  · rw [he] at hr
    exact hno s hs hr
  · exact hproper _ (List.mem_sublists.2 hz) he (required hr)

theorem prism_lower_from_full_exclusion (hno : ¬ HasCircuitSize 6 prism 9)
    (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) : 10 ≤ C.size := by
  by_contra hs
  exact hno (prism_hasCircuit hmono hev (by omega))


def MonoL (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

def HasMonoSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

theorem simplify_mono (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    · simp [simplify,simpAnd] at hg
    · cases a <;> simp [simplify,simpAnd] at hg
    · cases a <;> cases b <;> simp only [simplify,simpAnd,Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk,ite_false,Option.some.injEq] at hg
        subst hg
        exact Or.inl rfl
    · simp [simplify,simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    · simp [simplify,simpOr] at hg
    · cases a <;> simp [simplify,simpOr] at hg
    · cases a <;> cases b <;> simp only [simplify,simpOr,Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk,ite_false,Option.some.injEq] at hg
        subst hg
        exact Or.inr rfl
    · simp [simplify,simpOr] at hg

theorem simpPass_mono (n : ℕ) (gs : List Gate) (hgs : MonoL gs) :
    ∀ acc : List (Sum Bool ℕ) × List Gate, MonoL acc.2 → MonoL (simpPass n gs acc).2 := by
  induction gs with
  | nil => intro acc hacc; exact hacc
  | cons g gs ih =>
    intro acc hacc
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq)) (simpStep n acc g)
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hacc q hq
    · exact simplify_mono g.op _ _ (hgs g List.mem_cons_self) q (by simpa using hq)

theorem exists_sclean_mono {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasMonoSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ MonoL gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    have hm : MonoL acc.2 := simpPass_mono n C.gates
      (fun g hg => (hfan g hg).1) (init,[]) (by intro g hg; simp at hg)
    refine ⟨acc.2, o, hlen, (hinv y).2.1, hm, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl


theorem erase_dead_mono (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs) (hmono : MonoL gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ MonoL gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  have hmono' : MonoL gs' := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hmono g (List.mem_of_mem_take hg)
    · obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.1 hg
      exact hmono g₀ (List.mem_of_mem_drop hg₀)
  refine ⟨gs', o', hlen', hcl', hmono', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)


open Classical in
theorem run_live_mono (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (hmono : MonoL gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (fun a : BFn n => a) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hm := hmono g (List.mem_of_getElem? hg)
      rcases hm with hm | hm <;> rw [hop] at hm <;> cases hm
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
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
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
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')


open Classical in
theorem exists_run_mono {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasMonoSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a : BFn n => a) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ MonoL gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, hm, ho, hev⟩ := exists_sclean_mono f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, hm, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, hm, ho, hev⟩ := exists_sclean_mono f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, hm, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, hmono, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', hmono', ho', hev'⟩ := erase_dead_mono n gs o p hcl hmono ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', hmono', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact run_live_mono n gs o hcl hmono ho hnd gs.length 0 (by omega)


abbrev MonoNatRun := Run (fun a : Nat => a) (· &&& ·) (· ||| ·)

theorem prism_mono_run (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = prism x) (hs : C.size ≤ 9) :
    ∃ s, s ≤ 9 ∧ ∃ ws : List (BFn 6),
      ws.Sublist (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)) ∧
      Run (fun a : BFn 6 => a) meetF joinF prism s ws :=
  exists_run_mono prism ⟨fun _ => false,fun _ => true,by decide⟩ 9 ⟨C,hmono,hs,hev⟩

theorem prism_mono_encoded (rows : List ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = prism x) (hs : C.size ≤ 9) :
    ∃ s, s ≤ 9 ∧ ∃ zs : List ℕ,
      zs.Sublist ((List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
        (fun a => encL a rows)) ∧ MonoNatRun (encL prism rows) s zs := by
  obtain ⟨s,hs,ws,hsub,hrun⟩ := prism_mono_run C hmono hev hs
  refine ⟨s,hs,ws.map (fun a => encL a rows),hsub.map _,?_⟩
  exact Run.map (fun a : BFn 6 => encL a rows) (fun _ => rfl)
    (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun


abbrev MonRun := Run (fun a : Nat => a) (· &&& ·) (· ||| ·)

theorem bits_le {y s ws} (h : MonRun y s ws) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    apply ih
    intro a ha
    cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at ha
    · rcases ha with rfl | ha
      · exact hw _ List.mem_cons_self
      · exact hw _ (by simp [ha])
    · rcases ha with rfl | rfl | ha
      · exact hw _ List.mem_cons_self
      · exact hw _ List.mem_cons_self
      · exact hw _ (by simp [ha])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;> grind
    · rcases (mem_kept ka _ _ _).1 ht with ⟨_, rfl⟩ | ht
      · exact ha
      · rcases (mem_kept kb _ _ _).1 ht with ⟨_, rfl⟩ | ht
        · exact hb
        · exact hw _ (by simp [ht])


def next (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : MonRun (goal k) s (a :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
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
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
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

theorem next_complete {k t ws} (h : MonRun (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, MonRun (goal k) s ys → f ys = true) →
      next (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : MonRun (goal k) s ws) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k : Nat) (ws : List Nat) : Bool := covUp k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : MonRun (goal k) s ws) : covers k ws = true := by
  simp [covers, required_up h]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => covers k zs && !(found S N idx s zs))

theorem bar_sound {k S N idx} {s i : Nat} (hb : bar k S N idx s i = true)
    (h : MonRun (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k zs && !(found S N idx s zs)
    have hF (zs) (hz : MonRun (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx} {cap : Nat}
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h



theorem encoded_prism_mono_exclusion (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL prism rows = goal k)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (covUp k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ 9, ¬ MonRun (goal k) s xs) :
    ¬ HasMonoSize 6 prism 9 := by
  rintro ⟨C,hmono,hs,hev⟩
  obtain ⟨s,hs,zs,hsub,hr⟩ := prism_mono_encoded rows C hmono hev hs
  rw [hinputs] at hsub
  rw [hgoal] at hr
  by_cases he : zs = xs
  · subst zs
    exact hno s hs hr
  · exact hproper zs (List.mem_sublists.2 hsub) he (required_up hr)

theorem prism_lower_from_mono_exclusion (hno : ¬ HasMonoSize 6 prism 9)
    (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) : 10 ≤ C.size := by
  by_contra hs
  apply hno
  refine ⟨C,hmono,by omega,?_⟩
  intro x
  rw [Bool.eq_iff_iff,hev x,prism_iff x]

def rowsG : List ℕ := [10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 20, 20, 20, 20, 20, 20, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 3, 5, 6, 9, 18, 24, 36, 40, 48, 3, 5, 6, 9, 18, 24, 36, 40, 48, 3, 5, 6, 9, 18, 24, 36, 40, 48, 3, 5, 6, 9, 18, 24, 36, 40, 48, 3, 5, 6, 9, 18, 24, 36, 40, 48, 3, 5, 6, 9, 18, 24, 36, 40, 48]

def xsG : List ℕ := [0x582c160b0582c01ff007fc0000, 0xa8542a150a857fe000000001ff, 0x231188c46231180000ff803fe00, 0x542a150a8542a0000000003ffff, 0x984c26130984c00000ffffc0000, 0xe070381c0e0703ffff000000000]

def NN : Nat → Nat
  | 4 => 231
  | 5 => 1641
  | 6 => 3159
  | 7 => 1159
  | 8 => 37
  | 9 => 1
  | _ => 0

def HT : Nat → Nat
  | 4 => 0xffa2e0b4ff9a31e0ff126836fdef5c6bfda6527ffd5c1413fd08df37fbe482bdf88a630ef8532ed2f7cdc438f763af24f5fd6c8eefca2ca4efafd49bef2fe184eebaa760ee6e9199eaf9654be9f8ac3fe9a22246e8cf8c6be8085343e74e6c6de74894aae55a6f82e40ae96ae01e05e6e00ccc0be0032a77df51f98edcc26f22d736e114d711b0c5d5cf6ec5d55e7072d443f09fd3a5c054d2efaa43d2d688f9d2d19ab1d1d0c7d7d0ad50fdd07ab9f2ceb62806ce50691ecde02d7fcdd58ef4cc6e4a00cc12653acc04aab6ca3bbd13c9abfe62c9811291c8b40c71c6db0d4ec5e83442c4c30a54c2df2e2cc1b74f24be9c618ebe9349e1bdd1c059bd962802bbb38249bb10517aba7550a2ba37cf39ba193107ba14aebbb8c86b6ab665ded2b48c1835b3c1936ab309c3a0b27fa340b158a657b0030111af7b4f18af54d8aaae623cabada013a8ad16e111acc67462ac554c33abca2ce8ab93fc48a9403cf0a872ec4fa5f9c105a55f2798a47817b9a0e9a3319f604fb79eb4a09d9d4defb09cc322d39cb3d1849c989bcb9c579d949bd78b6a9b1c1d1b981061eb949edd249077786890593b7d903863658fbf20208efc3fd48d6f0b738c6ec2d58c5735c28b9dc1f48b1494e88a1aa63188e7d45984d703707f6dbe0b7ee5dac17edcb9d37e1604c97e0ebb7f7df8bcde7ddaf88a7d7879417d27e8b87d188d6f7b57663979ab1092792e4d4f78d0fe4778c5f1a778a7e523750b937e71f59f0970d832b2700be05e6fcad3316f90c4576ece11e86e15d9e66daf7a036da2269e6d646c596c7bae596bc3c1c86bb5a13e6b8f79396b8cb10069f1aa0869a9aaf3694d6bfa661d648162fc199262c4f9c862894b29620b76f4614e95f960a119175f6da50a5ef191e65e5219215e4c79815dd07fc95d5eb14f5c525c2d5b8e67395b28fbde59d93c3359614f3a592042935884f37e56f62df756bcfa7955d2dab254a19b635441432053edd2a64f90468e4f00f7ea4e7df06f4dc1ded74d7ad5634a532be44998141949869812444fe551421cd48f4183c6d83fc160923c36fe4a3ba9f7dd35dbb56333ea8a66330789a03103f00b30ce9ab72ee990612cc22ac5287a74fc281e3603277e035f267742ac2625a12e250a714c233220531d0a9fd6165c40c91627e2e312be9caf1260067211ac871c105de0320fe437620fdb3d9d0faa34610d2a0dd40cc40e850ca371d20c5e9d1b0c1bbfd90a3b78f608c6cd14085e8bc5085befc40839c6a705b3085d0256c1e40204e778013f8ed1009753c4
  | 5 => 0xffdc5cedff816febff7fde97ff49daf8ff2f4334feecd123fe9e5d14fe85c0e9fe7bd455fe30a711fe0c5183fe0bcc5afdd00289fdc53983fda6f85efd7bcbc9fd2405f6fd239833fd149afefcf9ce25fcdeee85fcd58b8efccbc8a3fc97fee7fc69dd15fc67f602fc02fa3cfbefacdffbe482bdfbce59eafbca3985fbbf176efbb756e5fb1af746faec4ee0fad4eb19fad22e75fab7e602faa0fafffa48e0f3fa13636efa0dfa54f9ed167af9b99d31f9685cc1f912d286f8f9f980f8613857f8601fddf8057680f7f694eef7cfee8af7bd88a4f79a3870f77c9500f742366ef73832dff72a6528f72644c3f716695cf7128677f6fafa51f6e1befdf6ce0770f6c2feb3f689cf2ef64fd887f60d40a7f5e519baf5dc8b34f54874d3f53453d0f527de03f51a2c87f4f7aa43f4f603e3f4cb1cbdf46eddc4f462c525f416a071f3d8a4c5f3cebab3f3ac313df369e48af35e64cdf3487eaaf2ba0f56f254e287f1d8db97f1aca71df1776750f12b861cf12255d5f0fc4b49f0d4509df0ae169bf064d7e0f0543aaaf0470a06f0445f8df02b9f57efcf605eefc2bf3defba5787ef77230bef36b82eeef579beeedaa99ceec66dffeeba8128eeac23e8eea7c8beee7324fcee6e9199ee4f8b6bee494632ee48703cee367cefedfee189edd54d74edb5eab1ed961c02ed5c5865ed18342eecea631eece79720ec9de4f8ec935c11ec8c81d7ec78869fec71da96ebd81b3ceb9a513ceb92d7a9eb90ceedeb8306a5eb6b4a5deb5474c8eb5014a4eb303bb6eadebb39eabe3c04eaafbe87eaa1abc7ea6048b8ea5ace97ea2c4a3ae9c4fe0ae9c3b213e96b8d08e90df407e8388ce4e824c5a9e7e27f4ce752c28ae721a1ede6c7dac4e6730a8fe5b370cae5985df0e59137d7e5821d11e55296c6e5455460e534b3d4e50d7c75e4ed170de4ccdc7de4c0cd26e4c070d5e487d660e46c60cbe46a3aeee4171e71e3803aeae347b176e2dfdca7e2dfd7b6e2dfca98e2d70819e2c38536e2c3729de26e19a5e24ac2f7e23d50e4e2376b8ee227e614e20dc72ae1f69c91e1b6dfd8e1b1a32de19f031de18dd338e1621a82e15ea285e1468205e12982e0e126eec8e12371ace0ceb175e0b5ca89e037b9dae028e7bbe02875a8dff1cdd3dfd808f9df86dd0bdf7fcba6df7329afdf51f98edf50b7b4df25986bdee86d46dea325e8de99718cde84c4f1de44e419ddcc9d07ddb3b8addd4a5a28dd4095f8dd339fb4dd308cefdd125c8adce2f2eedcc5b16adcc26f22dc949c1cdc0fe4e4dbe868fddbc345c0dbacab0fdb9e2a36db8480e6db3eeb7adb373eb1db1038f6dac37ef0da231e66d9f5659bd9a29091d928a845d91c4101d8aafb33d89ca136d82022d3d7e40da7d7d2d716d7cedbd4d714c5a4d6c2416dd6b2ec0bd6a6def4d693f243d65f0798d64a1ab2d622f34ad5f7dea9d5c5848dd58ace13d583199cd56ecd05d55e7072d53f182ed51774d5d4e82987d4e308b8d4b382ced47675abd45c2278d455991fd4473565d411550fd3c0b79fd3b8f8ddd39192f5d3822656d33cf4c0d334f953d33498d2d3342e84d32ae712d32364fcd30e1d8ed3033ad1d2f48669d2e87c21d26e9bf1d2204b29d21296aed21121f8d1d079edd1b23d02d15ca7d1d1362604d1224bf2d110f8c9d0b239b9d082e087d077f76fd0738013d04c597fd014862ecfe5bb0ccfd36623cf887f1fcf577fe1cf505fcfcf4f1e68cf2c59a7cf110ce0cee92001cebe3cb4cea6509dcea05d8bce6ea028cdd58ef4cdc43250cdaa4431cd94f280cd763635cd470888ccf6c379ccf3e769ccf34cd9ccea2f26ccc454cbccb8b967ccb035b7cca8eb4ecc42eb4bcc330155cc2cb258cc275a16cbd402adcbc53c97cbb0abffcb9f8e0ecb710f06cb48615acb278d0dcb17dc15cb0fcf5dcae4c107cae4b93ccadb6a68cad4d413caac6b0dca962c2cca92a34eca71f29eca6af3b5ca69af13ca56efc7ca1e70abca16c4fbca0cb655c9ed9620c9eaf21dc9a00c50c965c824c93445fec9199aa6c8f5751ac8cd5cbac85812c8c840564dc836c80fc7cddd7ac7b071bbc79383efc793650bc78a3dcac7787502c76c156dc75f5dfcc7564c7fc74c053dc70bb808c7010140c6c40573c6baf834c5edeb71c590dbf8c55e32cfc55ba925c54758c4c533bc63c4c10e03c4a80e83c49076fcc47443a7c44821e4c442ff27c4299d84c42967f8c4039135c3fbc942c3e4942ac3bc1ad5c32caec5c2ffc3bdc2bfe096c2b4e7dac268cb31c25f76e9c1cf85d9c1b74f24c1b07a86c19848f6c149f6afc1052df2c0f3591dc0db42a9c0bc2bbfc0b5f095c080a00ac07428b2c0561fa2c021909dc0003289bffe39efbfe8e93abfd4cde0bfc62e92bfb7fe01bfaa13f7bf67b8dcbf6413cfbf495060bf359154bf053a17bef9f8fdbed95cafbeaf711dbeaf568bbead8aaabea668f1be7748c3be6b691cbe4a60b1be3c7c2fbe3c12d9be23452bbdfd024cbded9a40bdbb8227bd301d72bd2b9117bd0977f1bcaa9969bc9c6b1abc80f6b4bc50e796bc238fa1bbdcab48bb787fb6bb76e23fbb18fb69bb1545e1badcf494bac77223babbd822ba9043ebba5b9aebba4d0384ba14aebbb9fc29e1b9b5b11fb9a3ec8eb985caa1b94e6aa9b93169b9b9102a02b904b531b8fe1db5b8faca93b8eb1259b8a922e1b876f5e8b84ea4a8b837f3fdb835d498b831a3a1b8098ab1b7f66755b7e73328b7d15d11b7b9791ab7b6b8bbb79c2c8ab798faeab738fd9bb715a542b6f37c4cb695f1e0b682d013b6233083b619fb24b60ae48bb5e38416b5cbe4acb5a31699b597849fb58fd16cb4da07d1b4c95862b4a76010b47abb91b4176f00b40b2797b40355a7b3eff692b3b7efecb36cd49db3642af9b3173302b2c88931b2a98fe0b2714165b24d6d2ab2091017b2078c86b205bdd6b1f73cfdb19b4a48b1791f07b14b9349b10088edb0e9c5dcb0bba239b066ea48b02a3938aff7b579afd5eb45afc60da6af9b545eaf9af785af6cbc6aaf58a26faf48e197af44c2f3aefb2823aee88a6aaebbc427ae9b9c22ae68625cadfbb6d6add4afdeada24130ad6dd86bad2dfde3ad0cf4f8ad0991faacfdf709accc3968acb81a5fac9ae328ac69704eac610b87abff1065abca2ce8ab93dff7ab844613ab7b24bbab3973e7aaed5defaac31e17aa8877f9aa81643eaa7708ccaa0493d7a9ff3beaa9f7870ba9e074b7a9aa5aada8dafbc6a872ec4fa8549f65a7b60206a797849ba78fe459a754a61ba6d0d826a66d98f5a5e191e6a5b8da20a5b7cda8a56908b4a4fe8509a4ba08a0a4b47838a49f74a4a48358e1a474a8a1a459b654a4551b17a42a6a09a4107825a3e6fb31a3e24caea3966da9a3647879a2fffa8da2a258eea29c7b57a249e124a2267d8ba1f1d204a1d6ff89a1b2bac1a14b6a1ca11cce32a0c6a68fa06fd7c2a02026969fadd1289f9b96889f8d42f09f8b29979f39e9889f2242779f0f5ea49eb9cc919eb7b2d49eb1c0ab9e7a868a9e488b019e31e0299e1c154b9dee114f9dc6684b9db899f19db870c39db842309dab5db29d82d32d9d6337669d4defb09d3569489c9cc85d9c94cb569c6ca3ec9c69b4229c2c8d459c2478279ba5e6899b7658c59b38dafc9b0348939af564e49aeb6eec9acd566e9aba50bf9aa4c0f29a938e129a82c5119a15789d99ddf50399ceb6ee996b80339950b709992ef9189918f35d98f73bb998c648d098a06bec989f8d70989b69ab9886360b987fd87e981061eb97f15bbd9731866e972bdc3796ede47296c2c9d596756c50965ed61796143f9a9600cc3095fa5049959a44a5956abdf99528ed5694fe2a9d94f4941394b36e2194732f4a945346f7940f56df93ca0e8593a769559378a5599345c5bf93223e9d93060d1192f68d27929011b1921986a392090f5291f54ff891b688799174b964916e58a8910c469e905ead37904726649012c8398fef83aa8fd9823f8fbc988b8f93bef78f91217b8f8db51a8f7be6788f63f0c48f5d15c58ee8826b8e8ee75f8e6df7998e629d788e28ade08e1895528e133c8e8dbfd7fc8dbb06bd8db341448d9ca6d18d86aa7b8cf062da8cecaa198ca21ce08c96825e8c7865e38c3911158c3130468c24a5df8bec5ed48bbfd6ec8ba1422c8b9688158b5f50a38b3f24e08b18a3c98b0411a68b0072d78aef42fb8ad6d59e8aa4d20d8aa160988a9d2c2a8a7081c78a4e5a208a23503889b93ab28990dd528973556e8972d2f38962b8af89219bf888d88ef788a25d7688a0d4e7883a1636882aecad87e9e40387e3581987cf3d828752d7b7873062bc87001f6d86f10fd986d8250b869afe34867e382f864f3b9886408a2386115bad85e91c1285d4a13985b1b53685a1dd6a859620a9857385ae854e7b6184dedc6384968e838478fbbd83f4643d83f027d183ecf89d83c33db1838cd21a8376d2e9836607bf8341f05a832d94ae82df5aea82bae75882947257828bfbe7820d5e118208ab17820481b281fbcf0c81e6afaf8153eb2c8145c3708142d6418129b59f812045cf810b2bb280d4084880d18f0680d1784c80bf70088091a5588043a5078030234680075da07fac70a87fa41c377fa02a397f72c0967f6631b97f5872ef7f3ec9857f23c04b7ec75d6c7ebb1b6b7eb1e6b77e7c5e6a7e7564ee7dda4a917dcb76b57d9d9cc17d904d7e7d78bc477d646d947d5893fa7d2f6ca07d1adbf57cecb5387ccd0f387cb9961f7c9433037c93898a7c7c2ff17c7bd0457c1eefd67bc21b7b7bacc9177b94457a7b79a39e7b346f407b24926d7aecebef7ae97aed7ae5e9527ae042267a9e56fb79957e3f794eafd179296d9378f9a7ff78b146af78a12204784d37d2784305c7782ee3a277b1a741778a8c54777afb14777925967763db827731edd57725a03276d5aedc76a5ca8f76976f7576948897768dd50a7663eefd7649fc4a76381d68761b1a6c760476e175fea88375f078ff75d6518475922f35753a8f8f752ebb857512df5874fc826c74f4c52974e04fd174b929417499b44d7473e56d744af86b742afcbd741634c37411c46a73da33b173d566fa73c86ee673c1ea257387e8667332f567731073a172db7dae72c9863872bb87c2729fa8f2723c03ad722b96b271ff861671fef95071ecfcc771c0fdd171a8b3107137418e71310cc1712ea42c71298425712512c970dcb0e3707b4eb57031e2e3702416af7005acd66fe585e86fe226f26f9014e86f3a79df6f2c68e66f153abe6f134afe6efc7f0f6ec83d546ea9d1bd6e9f0ed86e9dc4616e7cfd116e3463576e1f257d6dfc558f6dc32bd46daec7086d4735ef6cce7f176c7b80516c0f065b6c035cf16be6a6ed6bc6b3866bbab7816ba5aca36b7b68dd6b61b8146b30e2f96ad517916ac2ef6a6ac0be5b6ab5d2546a8c33f66a742d8c6a5d01a96a3f69596a34b74c6a30cd4b6a0af49869a4c63c6997d1d0690b613c69064b2368e1e77c68d704e468797bfa6855e06d685171b0672a6e3f6721395666e5b90466c9224666b8e0bf66b3e897666fdafb6660a36c6643ea64659a0ab1653cd63164df5bbc64bd9be964330c186419219e641584a263e02f4e63d9fe9463d62bbf63bd474f63b6a7e66395df51634925526345bce0630371bd62e4264962e1667362b266f4628f46c0624d95fd620b96296207dccb6204ea1261d6d80761d3f50d61a86e33619d2dcf619837a761761588611d290360fe0a4e60bf1f1c6089dfb16086b24160630760605562e15ff155aa5fd3bf5c5fd2f5ab5fbbcb765faf46045f770e675f3c3a8c5f3236fd5f31a1be5f116c235ef1c9365ed9c1e65eba8e245e788aad5e161e565d871fb95d6c18c35d59bcaa5d34d75e5d2e57ee5d23b4375cdc27b35c7cd71d5c5dacf95c0a08b45be9a3de5bb490135b8d41e45b8c09935b4fba065b2fca9a5b257c075b0725ed5afbbbce5ab316e25aa709865a65aa445a4fca5b5a01ff6859dfa69459d1759c59cc224559b9941f59b79dcb59a14efd5986b0d9596156cc59614f3a594ff29658edd93058cff7bb58a764f25884f37e583eb01b580ea7d057f91a5d57affd5b577e45ed577274fc56f354a456f13f8056df6eda56cc089c56b43de9569c25d3568131b35664ec9b565e35bf562818755621f9e655eb88c855d2dab255cbc3ff55c17e0e55acfc6e5543cd7355318cfe54c2be8954b9a42e54a454ae5496faf6547df794546a813654484c835435b81c5434a65153e2a72f53ca251253c4fd435389c87c537fc4ed52e20cc552c3524252c2481f52b96742526129ef52521bb5521159f0517b376b513954ed51343f22512c92e0510335e650be69105087dc5f507b08c0501ec9c75009923550079e9a4fc68c744f63532e4f6190764f124fbc4eff791c4ec3a72d4e967c774e538dff4e3094364e22ad5b4e1533034dd0131b4db0a5214d74c15e4d657cfa4d403c344d09d8b24c475da14c3a35eb4bde4b094bb6fcdf4b93a2564b860db64b6fb94d4b00d1cb4aa371da4a5bb42b4a163d694a0647da49b4f14949534c924939777a48f02985488594ce484dd18d48370b4a47ebd1f147a30495476f4b90476177d047523a214736fa1a470aa7b046ce555a46b26a5d46444664462646c945fc0a9b45d03146456eaaed456331d24558208944d02bfc44be1bb344868ad9446c57b744141a6444058be243ba4b0c43afc369439f598743569d96431a905c4306086442ecd23442cc6b6942bd830e42b4c46c42aedd30427a015542681922420e9059411714ef410adac540cc7c1c40397c56401a26f14018a9644003ff493fdef57b3fc943663fab02413f59f0683f1e1f733eff54093e8d9b7a3e801bd13e7d04503e6861673e674d793e2876a73de75a623dd45e6e3dbb60c83d8452893d3d84473d3b995e3d260a773d1308ca3c6754fe3be5c54f3bd9a8333bd861ab3b5ac1f83b4b5b3e3b3e43663b3a24c23b0d87df3ae606133ae5dac33ae4fa3c3abf30733a7fb0413a6c68ee3a622b303a50e03239a960f7394d6542394aa05f393114553926c5c238b0251d38a6a8c438a35af9388dc4193858d3e93840b086383d258a381ddffd37d8047e37a801873799f4533791d8ee370b10fe370604da368ae8d3366ccf223661a45b364d9430360a127735f49db935e525bd35d2c49635be366e35b162cc35b03b2035afb8f1359beb7a356db72b3523c24f347347d7346b87723467b4e1342fbabb3411e86033be62f433aa381332dfa8db32dc45f33263b3313248f57732201eca31b72432317db7b03142354830c760d830b7e71b30abd2a130468746303a5a6b302b08b42f9c386b2f85259e2f7ba5172f68b7cb2f59b0232f3d40bb2f3bb1e22f26ea232f0099c02ef617592ebe09912e85d23c2e5a28bc2e33c5c12e06c8172df9ad9a2de8d3452d96e18c2d55e48e2d21e2492cff23a92cd1332b2cc7b89a2caa14572c86e21a2c5942de2c5266d52c49659d2c236c162c0dc3e32bdf7bfe2babe6dc2b57655b2b39a0902b2756ce2b27407f2adf58d42ad15e3a2ac93a652abed47a2a7d8ad32a73489e2a24e9362a0bc45e29b92edc29b572f529b2caef29a1a2c52964c58c294e47902944de83286c87d4283e6ba7281e3603281d725427e2ed58278972292708f13626d9f70026a9eb3e26863fbf267a32c226583c7e2632842b261adfb82601820425fee43325eb5d0d25e6271b25ca409b25c1190e25ba0b672572dd24255b6bfd2541436d25409d2f25045fc52486e7a32462a1c5245771fa24320536240c862e23dd652a2375dbfc234a8be82348934e231e9fb0230f49ff23071b0122fb697d22c1693722b506ca22610a01224e1ab32210e17621cb603f2189138f215c2c012151460221177e53210f2e50210b952820ff67df20d27c0620bb651920ad69d520a72fcb2070fa062061bdaf2042586c203f2e672030bc6c200123001fb37d381f6733be1f29cb241f1b6d431f1aa4541ef1280e1ececb411eb175b21e5839391e2ea9ca1e1b70ac1ddd29dd1ddbf1941d926c731d8a6aa91d7308991d49bc011d1a5d321d0b7d241d0a40db1cf881d31cd4efa51cc97e391cc3b1b41cb0b9df1c9cc7ec1c792e781c77dcbb1c74bfaf1c5b7d931c5608c11c545d261c36ceed1c307b481c20c8cf1c0fa9cc1be6da771b9405df1b91ec161b7fc8d51b72fe7a1b55b5661b44c3181b25c2de1b20eebd1aef97251ad1e3001a9902581a9048661a802a001a5a294619f6feb919dd833019d9ab661979775c18aae8d718aa3e9b1871f88a18698c2e1866f4481803b65717fdf58a17c011c417b068641782a6fb174b97321742e5b5173ec71116fef59d169f5b2116735658165c40c9164b3f48163cc1cb16102e5d16056c6915d75b0f1505b34a14f8904c14a97451149fddc71469bfdd14645822143c4027142f8a8314010b2813f75b0d13dd29b313c3d76d13bd22aa13a6cb5b1341b636130266f71292f118128bf82a127cd01f12693315121e894b11f9400811cc4a6911c61b3411c3d608115469b21133d39810ffa3e610f3ae8210d0f1bc107e158c106ec8021011f2ca100dbdb2100273be0fd403be0fb1cc160fae40dd0f760d900f4b126b0f2e907e0f11b2260efcdec90eee5b970ee1d2680ec587da0eb864980e8ddecf0e3dd5e10e2ec39e0e20329d0dccda360dc26e160d6a83dc0d5f17a10d5563530cf761140cdfab720cb074f00cae7c560caac4510c6bc6eb0c41cc120c4176c00c23359b0bffd8610bed4fce0be289930bcfef930bb56fb10bab6c220b9f49f10b9073a50b6dfe080b124eb00ad879dd0ad2f6d70ac0e4480a91be150a6afb270a3394220a2eab9f0a03677a0a01cd0509eab71009d6c67b09beac1509a78d130982549c0957d8e0095136ea091c580c08e1036108c6cd1408b2e73608b241ff0870dd10086ff63208556cb00834836d07c1dc700759d3830721d4ff06fbe43f0653e7bb0643b58d06014a9c05e32f4d05b0e10a051ecf6204de8e0004c6920f04bf3608043f2038043bc55c0435d2ef0424457103fd941403cc081e03c8f6f303b52802039c52d9038c4e8e037c4961036e876503164a120303271e02f3d81702ec349e02e0dc2a02df4c8c02bbce3b02b0d8a802922fdd024af7f0023b66000237459b017e6bf000fe02e000ad50d4008842b200408612
  | 6 => 0xfffd9e84ffdb5d5aff9a934eff535ef9ff43ee55ff2f4334ff265cd5ff25fdf4ff03bde8feffe58bfedb078dfed5deb5feb1979bfea7a838fe82824cfe62e2e7fe505c17fe2b7403fe291023fe101b48fe0bcc5afded9304fdd00289fd8a44f8fd7c884cfd75b5f7fd6a6f25fd5314fbfd4b29f7fd3d0d4efd30faf1fd266eb8fd143ee5fd111c2bfccfe3c4fcc4d379fc91d7edfc8adbddfc5bf826fc431a08fc0c6671fbf83180fbf32b5ffbe6760bfbc7002ffbbcd56ffb840e1dfb732f4efb71cb4ffb58df44fb4e6e67fb4dd2dcfb43dbc0fb3976e5fb295c43fb20afabfb202c01fb1f5259fb1af746fb191323fb1355b8fb0bce0afafe8406faf49f40fad22e75fab623f3fab44e81faa0fafffa94a89cfa8afddcfa829c4cfa727cf7fa51c836fa3eecf4f9f961c5f9c6e33af9a0cc48f9892ee8f985d573f9685cc1f9520813f94319eef92004fcf913e23df913ba16f9111b30f8ffb126f8e7702ff8e46b65f8dd20e2f8d4d985f882c397f87ea4f3f87a3a57f8601fddf83deaf4f8241a2cf7f694eef7eb7f27f7dbd198f79a3870f7927402f7834fe3f72ced6bf72b348df72a6528f72644c3f7128677f70f9861f70f7c3bf6f6a335f6f31396f6e1befdf6ccedb5f69f2d7ef69c2384f6856781f6708620f64efd74f60d40a7f5f506f1f5d5caaaf5d3ab78f5bda359f5bbc9d0f5b39b8df58850fff585458ef57c2273f56ef6c5f564291cf54bc93ef5286c59f522ee78f500c2d3f4f5547ef4e0eb6ef4c235c8f4c15433f4b6a639f46eddc4f45e45baf44896c8f4187d19f4029165f3a9add4f3a6d9eef3a66eaff385bd49f379f12cf36f6413f36f34c1f3502f36f33ead7ef3391deaf2e4fc02f2da3761f2b2a66ff295b535f26b8779f254e287f25117daf2495bd4f244e8c3f243b6fef2364ffef216ceaef214d755f1ff4973f1f86b18f1c8a8dbf1c8157cf1c2c32cf1c105b4f1be915bf19e9ed2f13bc60df12d735af1178fc6f0fb0558f0f455e3f0ddf664f0dba4bbf0ae169bf0a281baf0860801f0622e7bf0543aaaf051726bf03cd209f03687edf003b29af002e2f5efe0597fefd3b058efc945dcefba32deef4bdca5ef09ad28eefb42b5eef579beeee7296beec66dffee7c0529ee760c5bee57364cee410740ee3ea962ee1bc0a3ee015bb0edf4e0b3edf052d2edcc0a13edb156f7eda9de6eed71456aed6d2f82ed60d812ed40ec4bed37148aed24f28bed085f17ecfe2237ecb845c3eca47273ec9b277cec8b60f9ec8246ceec3f5472ec2dfdfcec2d5fc0ec1ab03fec14959debd65d42ebcf34b9ebb705aceb9a513ceb8ca162eb6279adeb303bb6eb023381eadbf100ead2f571eacdec8beacb24cbea93f638ea89854cea83b3adea3b8697ea2c4a3aea1578a3ea008882e9fe2aa4e9f053d5e9d68ef5e9af7f88e9a6ddf6e95f28dbe900f8dde8e74d4fe8bc4a91e8b8915ae8b0c949e8aef755e88cbcd2e877f6cae8720e4ee860e1c8e8549ac0e8315305e82b1724e7f958bde7e6fc8ee7c5f3cce7b14639e7a7366ee788d1aee77dc1a9e71dc007e71cbc2ee709b00ce7004a4be6d1ab97e6c7dac4e6b94f51e6b004e1e6966fe7e657868ee653a441e6464ad0e63dbd49e6216f5ee611bde9e603832fe5ff43b9e5ea07e6e5b83d32e5a47960e597e839e5901efee584fae5e573bf08e5693bd0e565d829e560f1b0e558d8c7e54c5f13e54537a7e52ce529e51acb2ae51468c0e50b2aeee4e11d75e4cbb873e4c27046e4c0cd26e4b627a3e4b587f5e4b1c922e49f5232e46c60cbe4529199e4500cc9e43dc564e3e8578fe3ccc76de3c9f2f6e3b650f8e3b27c19e3ae93f2e37cd481e36a6fbbe36643e8e35da5b5e35956fee341fe15e31fd270e3157428e3098352e308a26ae2e9f35de2e0fcc4e2aecd14e2aaa4b7e297cbc6e28e9530e279cb45e26dd180e25c2eafe25b4419e2526764e2484866e23ed16be23d50e4e22bf440e2122bd8e210310fe20ef961e1fa1f01e1d11862e1b02acfe1a4e120e1a1e1aee1865e65e17e25b4e179281be1593b55e144cef5e12371ace11798d0e10be055e1007e9ee0eaae06e0c611ffe0b5ca89e0a6b977e06aaed2e055e5d1e0526754e034db68e02dd010e028e7bbe00f5da6dfe953c1dfd579eedfd13559dfc27cecdfbcc8fedfb3898ddfa87c9cdf9b3db2df97b20fdf915de8df8d02a0df878270df7329afdf50b7b4df4c82f7df23987ddf016cd8debeb58fdebd2999debc686adeb052eede9f9821de7e4d4dde5865f6de52b48fde3f6d31de394c87de184cffde06c5bbddd4b2aeddc5490eddc38abaddbcdde9ddb28709dd9f2555dd7aaa47dd6c1febdd3f90aadd37375edd1a1651dd02c15ddce6e0ffdce2f2eedcd0c814dc96cd09dc729b09dc3cad6ddc383cfcdbd4f789dbbf495fdbbe0e6fdb86ef61db8480e6db645754db5ffbe8db3e5709db3844fbdb2e1d5fdb27b873db0eb9ebdb06c264db0487dadaefe250dade824cdad74e2adad2fd44dac37ef0daa83aa8da9c6e6cda82b2dcda7c2bb2da230287da225efed9ec4061d9e26cbdd9df3790d9cdff3cd999ed03d96a1d37d965a92ed96080dfd93ba487d928a845d912bc5cd90e2d59d8f5785ed8dc7035d8d19bb5d8bfeebfd8b61a43d89ca136d875bfa3d868475dd85d96a5d825fa47d7f4bf3cd7de5dc3d7d18760d7cedbd4d7bb9052d7b63b55d7b4560fd79a0492d792607cd78ce42fd77f0816d7630cb4d75351ced74457c1d743cf0dd7419650d7386b7fd72dd098d714c5a4d712705bd705d246d6fb3b8fd6d9ced7d6c75935d6c4091cd6c2416dd6bca87dd6ad4ea8d69131ebd6430bb1d6389e44d6352d89d6347021d627dce8d609dc67d6069c17d5f2b081d5d2ffc3d5a7358cd58ace13d582866bd56f6680d5570f5bd5495dfed53c6df7d53c464ad51f6f39d51774d5d510f8b8d506b471d500d74fd4b066e8d498d848d488bd75d4813befd4692e0fd3fadbbfd3d94239d3c0b79fd39624e6d3678518d32f043fd32ae712d318d25cd2e87c21d2cd0bfad2c8a7f9d2c221abd2bf65bfd2b12d6cd2abdd16d2a601e1d2a52669d29b09bed2735951d25cd501d259c319d25991b9d2571b8cd2539f98d24d818dd22e4bc2d1f57c2bd1f065c3d1e45df8d1e2904bd1d933a6d1c6ad21d1b56bd0d17a20edd15f5c85d159a27ad14374c0d1419f42d1310f74d122bfe1d0bb50dcd0b60e78d07b5da7d074cbfdd0738013d06c58aad06bd8b2d06b45a6d062cd3ed039c3f4d02f49cdd01136e4d00c7d94cff5c191cfe8ce19cfe62c0fcfda3dadcfd6c62fcfd36623cfd3381bcf72c45ecf64c42fcf5215cacf3eacc4cf3ad10ccf28aeabcf18d981cf009dcaceee4f94ceeba21eced16beacece6079cece101acec8561dcec4c4f7ce9498fcce882266ce81a2edce814063ce507a39ce3e6f69ce35e412ce1b70fdcdf8d234cde4cca9cdd33802cdcc6d1ccdca8f97cdca3b06cdc21c5ecdba1453cd9944e4cd93d506cd8b2b11cd628c83cd575db1cd4bc81dcd3929f6cd2a09d1cd147cfaccfe4843ccf8566eccf6ea1bccf3e769ccef899acce43bc7cce04b85cc9fb9c5cc927cb3cc8b5e08cc8745c5cc488a37cc2cb258cc1d0a5ecc1be66dcbf827eccbd402adcbc1ed0ccbb0abffcbaee7e9cb98ce57cb848811cb55db73cb4f2094cb3ce36acb37e234cb244571cb1727cccaea9203cae4c107cad8326dcacecf9ccac88f71cabd8fa9cab30b78caac6b0dca991930ca769249ca71f29eca650c0bca58e415ca435068ca409e2dca2ee934ca07bfecca05fdffc9daf23fc9b4e369c9a24762c9a00c50c997baffc989d43ac97b30cac946962fc925d431c92384f6c9146fc4c90be4e0c8e5a33cc8c538d8c8c4b562c8c243e7c8bb9389c864d23bc84a115ec831fdf9c80628aac80406bdc7eb62a8c7e7c85fc7c10998c7bfe9b1c7af0372c7ada50cc7998ba8c79383efc75f5b99c7564c7fc70b4b8cc6e0934fc6c9fb90c6c030bfc68c0f91c689e8cac6766c8cc66b67d9c6555923c63df481c6240179c60f799ec60c803dc6016961c5fe08cdc5d967edc5c00a23c5862d60c5757cf6c57201bec570dde8c563cb2ac55a87ddc54758c4c5391dd0c52d1b88c52a31c0c50b8dd7c5074ee6c4d52b3cc4bb1fdcc4a34d10c44a4899c44a1453c42967f8c407e305c40205bcc3f1d700c3daa14bc3ca5831c3a658d6c3808881c366ab44c3638aa1c3533bc8c3473faac3300855c324e33fc30e27a6c306d41fc2fde3b5c2e44a96c2e26730c2cf4745c2c21b4dc2b8c820c2a2b612c2a01491c268feedc265d11fc2634f93c2572a18c2465cdec23f613fc23f13a4c225d7c7c1eda175c1e9a406c1e69006c1e1da87c1b4c9bac1ab821fc179c89ac177291cc168c5a2c1627032c14eccc6c149f6afc149e481c11ab946c115e7c4c0f92bbec0d16c93c0cc3a5dc0c6af2bc0c0ca22c0bebe3fc0b6feefc0b30796c09e130ac0995ecbc03d2daac034c313c0205ef1c0115ba5c004a46cc000479abff6a6b3bfcd59f6bfaa13f7bfa193cdbf8a6074bf861c92bf384964bf363a76bf11a2bdbf07c9dabeb0dba1beaf4706be883604be709e72be59b45ebe332981be14d35ebdfec150bdfae40dbdeb9727bde49763bdcc7138bdc2bceebdbb8227bda15bc9bd74b96ebd6d88e3bd5dbc61bd48e09bbd3b1171bd2b9117bd01e3ccbcf4fb1bbcda61d5bc9b5c44bc80f6b4bc669f09bc4e5ac6bc4c5239bc2442fabbe4e6f2bbdcab48bbd0b973bbbc108fbbb6a1ccbbb2e264bb9d1368bb9190b4bb85f7f0bb787fb6bb638cf1bb2e213fbb29b909bb2033bdbb10120bbaee7fc4baca2cc6bac67f34bac308efbab92321ba96bd10ba73fafdba70a471ba6ec848ba6c16d2ba68862cba5223c5ba37d63dba171387b9eecffbb9dc7f1db9cf47d9b9be4292b9b5b11fb995749cb97555f8b96f2570b93f56c9b93c87a3b93aea9cb91e94d9b904b438b8dc9f46b8bcdd07b8b0555fb8a96335b893e352b88ceda0b8861452b885b025b8841ba8b8819a55b8783a15b876f5e8b872dd3fb86f87aeb85c9b59b84dbe58b80ba1f0b8098ab1b8028471b7f8d396b7f070fab7e46552b7d6a7f1b7bc1ac1b798faeab781cb95b7415f9bb71fc5dcb6f6d19ab6e8cd9ab6e2cfb0b6dca0a2b69a35b1b6886780b64b4e5db62922b8b61a1ef4b5ea1a85b5cb9ab6b5bbc68fb5bb7640b59b24efb588fdafb55f2854b54e2abeb549fbcbb52e687fb52008e8b4ffc637b4f79fcab4f5a720b4ea9f39b4d40f54b4be39aeb4b6a56eb487e886b47983b8b46f8332b46ac4f9b465b610b459ca15b445717db43e6c0bb4297993b42539a3b4035878b3faa634b3eea95fb3df3931b3c7d28ab3c4d435b3c1f8acb3c00ebcb3b47c69b39d9c9fb39d7284b392f7afb39131d8b3851fb3b36f53dfb36d780ab36c248ab3642af9b316d041b2fcd4f6b2f86836b2ecb8adb2ec225bb2e8ac0fb2e24c52b2a869ccb2a79041b2914fc3b28285aab255d33fb24c4f40b2448ceab23f5828b2000ceeb1cabb43b1bb16d3b1b35dfab1a14d7ab18ed272b16bdfc5b1491027b11bf8dab117beb5b10af113b0fec880b0d469b4b0c36b66b0bba239b0b58d68b06e3c43b066ea48b0410137b0301a92b02f2f8cb01b5b6fb016d169b00cb112afff6d1daff8105daff6c5e6aff4613aafd5ee8aafd5eb45afbebbf5afbe9f6caf9e65acaf97b6b6af8d64dcaf85bc3daf41588aaefddbe0aeeb49faaea879d7ae967a97ae83df2eae70c515ae694c30ae5e249dae46994aae2bb860ae29329bae23ac2eae1f5737ae08f448ae0331f6adf77de9adf195ffade79270add481d6ad6dd86bad62e160ad4eb735ad2dfde3ad13e094ad10ab2facee7f8aace5341faccc3968acaa8671ac7e3c8aac5d2018ac38b6acac254622ac1cbab8ac0ec509ac08ace1abee4b7aabee3357abec48f4abe5c086abe3b361abd38145abc189d5ab8cd8cdab856d1cab7766adab745161ab5cd572ab5cad26ab4b152aab453d7fab3973e7ab31876fab1b93efab117415ab0337d1aafc4a6aaaf4ba54aaf2c80daaea6040aae98747aacce462aaa5ea14aa9f65abaa90e2afaa8ae32baa8703f2aa7708ccaa64098baa00f19fa9e980faa9e74373a9d5251fa9cec0a5a9a61d2ea99c199fa98f0620a97dfe93a97d2daca9715e25a96e0f66a938e4d1a91e3aefa91c11e9a91b3011a8fbcb6da8f87c6ca8e2188ca8b20bd0a8a9b36fa896d19aa849788aa7fcd258a7db2188a7c06a04a7b9bba9a7a8b494a7983a90a76d9c29a71c1e98a713aa82a6e7ad65a6d4d3fba6d371eba691ecdca68f81d3a68b11a7a66bfdbda60fc20ca60c623ba5ad3c5ba5abd90ba5a7f865a56f1715a56945dfa5662549a55c1729a553a404a52ea902a5111aada4fbb03fa4f2ab64a4edd7afa4c3b2f4a4be915fa4ba08a0a44006c1a43b18bca413df65a4030af4a4015613a3f6d981a3f4e458a3c4db8da3c26a5aa38aa3b5a374cd25a36c9e3aa3410cdba34026aaa33eaefda32b7b7ba3037854a2ffc55ca2fe9ca6a2e9c67da2e9541da292f32da289d496a28797b6a2809f2da2738744a24682eaa2296592a226e55ca21725e8a1f74c3ea1eb992da1af58f8a19caaa4a190c4dea16d3bb7a1686d79a1645991a14da6b6a1274820a124a175a10db470a1057e44a0dd4aa7a099455fa04eb6a2a02798dca00554da9ff0cdc69fdb1eef9faf9e5e9f9e740e9f8e64d89f8d14e89f60973f9f3c4fe09f2b65419f2a39469f2928859f1fc98e9efb600e9ef1aaa69ee6a4289ed4253a9ed0eb329ec145159ebb77939eb1c0ab9ea40e9c9e8bca2a9e89dfe69e7be7e79e7b14a09e7a868a9e6b6efe9e5cf5849e5bd09a9de9c0289ddb3f4f9dbf4fd49d8ce2829d70290f9d676aaf9d4433cd9d27eebb9d1c892f9cfad7719cc132c59c90b9299c878bf49c85fcba9c4ac7fd9c427b019c2c8d459c2b821b9c1cf5d39c1862309c0e37e49c000b0b9ba660f89b6d72419b6061ad9b58d1c99b4643749b2523ca9b20ffdb9b0348939af1af659ae5e8ed9ad57b839acf83c09aba50bf9aba3c659aba03a29aa84c139a88ac699a63830d9a4c64ae9a306f169a2121dc9a035e6b9a0019da99f3ad7399e2a09d99ddf50399c71a6e997bb2169973027a9951dabd98d9c3e998cdb64298c8f39898bc5375989c4ae4989c1cb19856152698544b629853c41698440d91982c6265980ed46f9805681797fe595697e6ddd69779d0e0976f09bf9754f8969748102e9742acb59740ba21973a948b972bdc37971e6f2d971da218971c36fe97161abe9705fdf396fc344796ede47296dd7c9696af808c967f46ef966394d49639589d9635fe1d9628b4ad9600cc3095d6f91995c988e395bbad1c95b5fb699548b0a595488241952e01dd951dfec8950e667d94f87e9b94f81b5594c4369294ab2dbd949e1097949c4492948d8905945346f7944f2f2c942583ff93f62c4b93dec7c493c038b7933952229337eae693131a0b930fad3892b4aa2e92911b429270179992519b4792507e879249e48b92366516922dda4b9220af6f921491e29208566491f2eb8a91e270f591e1c94f91c7e1cc91c5943891c3426791b1a0ce91a483aa9174b9649172de81911f91fb90f8383390dfb77390bfae56906b514190670ca990408d44903db8a690048d758fc258a78fb31c278f86b01a8f7f07798f6e8dcb8f3e8d538f32e9528f2485af8f0a03848ef3006a8ecf82648e9682548e8b63688e6923d38e629d788e5445788e28c25c8e01de568e0076c08df19ddc8def3ffe8db89e1d8da5efc98d9374c78d9341fa8d59bf7a8d4e0b688d3af1298d3793d58d2840a28d2765b08d2416518d17c7068cfeb56f8cfb283b8cf64c858cd9fd068cd4dc848cd237e18cca063c8c939e9e8c87e7188c53da148c04847f8bffca418bf437b68bf385c38bf0a1e48be5ef8e8bd0b98d8babf21f8b9a80ae8b9688158b8d6bf08b8721338b6e30418b4a164b8b43b2008b3b042b8b1ecdd78b18a3c98ad6ad188acdfcd18ac762368a9ce0de8a9182248a8fda848a8409938a7aa6a88a0c86518a09835d899c73158990dd52898e46ee898146468965710b896448348964445c8937291a8897a80e88925949888c03e88889db3288888fbd8886833d88519fc688322590881d7d978809c40e87ee459b87e88d2e87d5b17087cf3d8287cd0ab687904fdb878d8c87877f484e877dbcff876cd18e876864a187607ac5875e822b874dc393873e21f1872c697b87236b3d8700f26b86fbd80a86c9df4786b158c086ac42b186470327863ea6b886166e9f85ebe5c28577bd4d855fe8dd855e8d6784fcf5af84da9a3684d2fc7e84cbae8e84c8952c84c386938491cdb2847c8b24847391e1846d729e84619618844f733483f4643d83d55e0f83a21f7b837cfcae836a1c71836791de831b7698831b26cc8316015a830d582f82f14ef782deaee782d62cb882c362d482baf31c82ab4c6082a5095a828a1be982641b578252c8c282501175822a61e18220eca7820cc54b820c02db820ab78681f5765381f49a4281f37db981ab6704818dfbd2816b2e9b815ba278813bdd01813600eb813441f2812cd91e8128a77f811bbbec8112164d8102ca418101b8e280e1a7b280dbbf7c80d4084880d16ae280d0cefd8091a558808a19a4802a6c268028191080221a8580199b937fe359647fd91d567fd1bf967fccac417fc97ddc7f9fd29f7f8e04597f88921b7f858dc47f7cbc4b7f72c0967f5872ef7f549bdc7f492c467f373ae07f265f547f0433af7efeea217ed56a147eb502237e9a8f1a7e804b987e6c0a4f7e5dcd757e3bb78b7e38d2467e29ffda7dfa46777deb1ee07de9e3237dc8684f7dbe85757d98ee0d7d7365047d6ae8467d525afa7d3ec6d47d27d2007d0535247ceaf0497cd7c3ab7cb88af57ca177257c9ad9c57c7dd78a7c7496667c64c23f7c49ba4d7c1201857c0227f67beb68d47be098ea7bd68f7f7bc8a1d67b88ff1e7b48c25d7b31437a7b30e4367b2dcad47b20ad317b056dcc7aecebef7ae60ef97adfb9a57ad8c7897ad40ed47ab7a48e7ab51e767aa212677a9f9e027a94a6227a8746757a7fc72c7a749ba17a72e9b17a6277587a5fc6e17a570d687a469fca7a3973b27a3050ed7a26a7917a1517aa7a119a7a7a099f6f7a01c2ba79db5e2c79c1fbab79b285c0799b3d24798d86d6797bf6e479764d53796a0b3379523fc57944e1f57937db607927ec337920e7c4790cc35878f9a7ff78d120ee78c5696878b9f71478b9857d78800863784f3d4178478061783ebb0778219822780610717805008777fa39f677ee045177e3ea5877e01cf577dc0bff77d4aae277c7bff877b1a74177a055e3777afb14777983e4777925967778867b7767c75e77445d277740aa17773e2742773b8aae76ed4c1676e4752976d5aedc76d02f2276bac5ef76b55bc576b028e6769848cb768d4eb876698fea76548419763d395b76388c2875d0a6df759324de7588bc407582344f75759565752672f47522ebfe75176479750f262a750d6db175059e4a74d2589174b9294174a0ed33749d9ff4748d308d747896f0745edb28744940c9742fe74d7418629b74170bcc7411e15b73e5cf8373b6a92173b3d9fd73af4ca173aec1257381f04b737cdb82737905de7359c8747359b9f973598efe7332f56773217fec73163bca730a83c17305f8a772fec6eb72c5f28372c0dd7072b4c2b072b0c5a672806a3e726b84ff724ccffa72330a7c7219a8bd7216d12d72043cfa71ff04a471f4a58871ee23ba71ca6e2971c4a57271c25fa071be93da719c68357195b7887191c4d771868e6b716cd6b7714e7eee7149896b71327db37128ff2f710b5f61710740bd71019d7e70e4990d708c5096706099f670606e75704f18de703bd0047033ccf8702b12786fe1de786fc0d7276f8c8f866f7b58c46f5418456f50e1ea6f4dae416f4bc96b6f4a0a116f2655796f153abe6efb3e5f6eca5d596ebddbf66ead5e296e68d8ab6e5612016e4136406e34f16d6e32f8a36e21560f6de80e506dcc07996dc918bc6d93a7526d9144d86d87f9d56d8394f66d792ca16d6705e06d47c9ba6d4242316d1413e16d04e8616cec54bd6cd1c97e6cc65c666ca46ff96c9c9df06c6b462b6c5901a76c5881b06c406a016c354ad96c2d0aa06c24137c6c0cace06bf004f16bc5f5346bbd27706bb9e7d86bb4833a6ba5aca36b9f28136b8ccb1c6b61b8146b30a7516b287c2b6b113d2d6b0440846b03fd846b03e7c36ae8f77b6adadca86abdc7116ab5dac76ab5d2546a8c33f66a77f6756a3f69596a34cf006a2d76986a1d5fda69e418a669df9e0969dc91ad69b3df2c69a4c63c697673d969758625694e064369235c6e69064b2368ee7b23689cfad76891243f684557c46830fe556815194d680a69e867c4cd8367bc626267a61dcd678f90a967757dc6671649d966cff78b66c92246669afb4a6696cb6d669129eb6687ccf86678ee9c664d4473664a571666407237662b502b66216ce46619751765f8412865cf088765ce010b65b6c20765993c12658b06bb6569924b65647343653677b46528b1cb651c4e5f65063c5164e5e92264de117764d7a93d64b58a7464935ecf648cb682648707c96485c1d8643a7b266432a4e46418a03563ed2f7d63a5d4bc63a549ae6341fb9b63247a266315041f630c3f2e630a2c7f62ff5b0862fea0fe62f460ab629bdd0d628044056264e76062599513624ed552623027d7621a4b0662122e5761f002b261aebb6261acc8576198979861933a77618e36186187e0b0615da32d61508885613e3ed16131a819612f2d5261224c32610ea1ea60fe0a4e60f6e1aa60df52a460de6f8360d96ac660c00f566091c9dc6078eb3e6062c7a0605686b6603d92e160127cc0600ab5605fd4e7bf5fc066d25fb387135facb0bf5f714ba25f52dce45f3c3a8c5f3236fd5f2396035f1c66a55f1469945efc9bb55ee68f365eb542675eaa9d935e5fdda25e419e2c5e1cb3395e0a4afa5e07e4165dd4b0345dd069115dba06ea5daf57ec5d7c7bfa5d3846025d2e57ee5ced56be5cd388475cb68e095cb38b015cab618f5c8dcb3d5c87c04c5c799fb55c7618155c5849d85c27d6055c0ee37f5c0cdc2c5c071ded5bf03c635bdad4065bd377865bc921845bbad3ae5b9cf72a5b9762d65b65d0635b6360d15b568d3a5b50003e5b43778f5b2fca9a5b257c075aeae0795ad90d665ad8ed955ab316e25aa709865a8d76e65a3b6ba85a3985e65a302c2a5a2472775a232f8959cbc14059bb47fb59a6a5fb5990ffd659714f6b59421da0592c744f5926823a59030b5f58c26ff558b2816958ac8056587b0d2b5878a965583abd6d5837189c582d8741581e675f58038b3e57faa9c057e8b85557c9058657c548af57bf320857b63dd45794122f5792f8c85782524c577e45ed577d409f57461987574396a95736a09c571a5792570be0f05707a06056eea09356ecd25056e4aef756e301a456dc1b3e56cee32356b542ed5699d286568e52665687709356765f855670e226566873145667e1ac5630b6cc5604bd3755d7e0aa55c8b13e55b5c6dc557a9f39556de923554ebc3d552df60d552bfd73551b38d154f7e8b154c2be8954c1008554b82b1754a13e465495b91c54802e945475c7dc546bd051546a759154687ce7546859e3545adf745454324c545403185439d5e353fa794d53d8ae1f53d5d1a453d0616053cd443153c82f0753c0c2b6539e7440538cdfa75374917b534ca7105330d6725329ebc453254bee5314fe4052f9d9f152e20cc552cd766d52bf683e529ee5b9529d3c99528ea098527ee1ae5235eeec52309a535228998e5204db6d51d26f0b51c4cb7e51ac9e1a51a1f593513ce819513984b7512d054351218f24510742625104c7b150eebe7450df27a950db002850b610f750af9d6350a9ae4150a5d7c85093e5525087dc5f507b08c05062288250475d1c501ec9c75013da294ff38a8a4ff32dda4fd8b8564fd5ba584fd43ba74fc77aaf4fc68c744fc0c4b14fc08b834fba7d404fb76c0c4f96d7664f959d514f469bef4f3652d94f29bf324f1371a44f0cd1a94f0ca91c4f06e6564eee16dd4eedb41b4ec9ed204ec54e5b4ea093284e70bd794e6da9ad4e68863d4e3ded864e38e8c94e1b737c4e16fe7b4e1533034dfef4ef4df947d74de1a29e4ddaecec4db800874d7c39f94d7902384d6d13104d53f2d64d363ef84d275d504d0e6e8c4d09d8b24cdd8dd74cc7ebc74cc095d94cb436fb4ca195fb4c91c1d44c752be54c572b644c328f794c119b144c0f0d6e4bf359ef4bf112514bdc719c4bda52264b9fcdc84b3ce5e94b24ff7a4b2385ed4b1aba444b15a4104add66114acfab394aa9a62b4a92a4564a25f85e4a03b87649f7893a49f047ac49daf4be49b8c91949a8a04d498b9f9f4975d1454947ddba4930264948db026148d40eca48acf2044897dd56488ee7b0488d989b4872bb84486fe87a483226554829ecfe481db839481828a447ebd1f147b1725e478b907a4761b05c4759350b4758eec0475631a347476acb47053cd74704e2014700b16d46f8ed5146d7f2b946d45c6946d114c046b26a5d46aec9cc4684088746661c994664ef57466289624639714f4634d00545e579a045b8817b4563602845634b9b455c70e7450f82234509c9b54507516544e525c044e1e7f944cae77d44c679cb44af8ab044a394b4449ecaa444940412448430b9447a385744681e83444196cb443fa65743d23f6843c583a643a373d24391e524435ba36f435ae3bc4352b048433462c042edf41c42e3f08d42bfd57442bd830e42a5f564428b15e6427a015542764e1b4269016c42613ab74246d5c74225eb6a421b1c444200389741fca16a41f8f29141f892ce41e5dde341da3f2a41ab849e41ab6b73418958f94174eb404171b3c0416f02fd4121a979411904154111d6474100091840f5ad6740e0117e40bbd88e40b10a20409a089c407c1873407214e440543966401a26f13fff4d3e3ff16c753fd0e7e33fb815353f931f523f0ef8fc3eef3a9c3ee1842a3ed96dd23ed7b59e3ed735973ed4cd533ed148c03eb7b4a43e8d9b7a3e8ac1c93e8946d73e73864e3e6e35d53e2876a73e07f2113dfcf7523dc01d123db609803da9910f3d716d583d6cb1853d67dfbf3d3d84473d364a683d2d33023d260a773d254f383cf42a4f3cf25a503c9c38f03c9becfc3c4d94e03c357cde3c2deca33bf9fc893bf3c1453bf24ed93bd861ab3bd509683bbad05a3b5ae9833b4618043b17432e3b14e5503b0e62b83aebeb5d3abf30733aab2bfd3a9f87623a86ff3f3a57bcd53a502ba53a46b5a53a3d0bda3a223add3a22018e3a1f24ee39f9bf9239f7a80739f1951439f1616c39df393a39c9827139c7715d39b0983a39ae2697396e8b71396e6960394aa05f393ba360393aed1b39373dca3918c17638f5cbaa386b8801385d221b3854b289384bf2fe382f293c381e37b2381ddffd37f8d11c37db96f137c29b5c37b6eba437accf8837a448143799f45337792f423777a4a8375eae5137544bea3745e395372dbe0a372a677c372a60fa3717e712370d51cb370b10fe36e8e3ca36d026a636ce8a4c36b7fd4c36ab6c9f3693c655368ef817368cb122364b4be33647018c3637cba336292f3e35c3b38435be366e35afb8f1359beb7a35938bb6358d253c357541403566bff4354571fd35222020350e82a134ef155f34c9837734ad6aca346b87723467ad0c34222851341c3aa0341a2f1233df4dd833d08a6033d0835733cef98633784604333c1b503326fbc233193b7a3300838f32f121f632b9908b32ad727e3270927f32651ae73263b331325644cf32554cd3323e748432229b0131f603cb31e6ccb831d1fc2031ca76a3319755853183d85831803d7131695ce3315ea7ae3158eaee3156dba83132202d3121acb031066a5b3106285d30c760d830c65b8a30c1b70930bdf36e30bb924230a41b37308abb1e305ed6593055dbc9303a5a6b302dd06f3029d29d3007f5d92fe029a42fd8cd242f9f34162f92e3962f5007332f33467e2f106e352ef617592ede43332edce1542ec5d24c2ebe09912ea87c562e8650b12e7d88722e4c1b742e2885272e1e5b762e097dbc2df9ad9a2dc1d53e2dbb7a3c2dafa63e2d8931502d7f53432d5686652d50df052d3402042d311cc62d21fef52d10a8b52cfa54112cf85b672cf391482cf360c32cefcd0a2cef87792cddfc522cdb268a2cceba102c75608d2c6353162c506a2c2c4f33762c42b3012c37614a2c2f0ca82c2eeec52c236c162be837c02bdf7bfe2bb94a422b8d54532b86db942b84433f2b7bda0e2b62fc022b2af0292b1f9b152b0f88752b05d0162af45c3e2ad1cf432ac75dc22ab301382aaa1afc2a92ca622a85f11f2a55a4eb2a3bf9c42a12233229dd0c5629c8fefe29be774929a1a2c529a0f2ce299e35fc299097672945d45e2944de832905e68428a668dd289683dc288ca725286083be285a096f2855c407283731c828330708281f17172805793b280185d127fac48127f0aad127e2ed5827de03bd27dc216f27dac3c827b7988d27b248ce27a7b90227a6fff927a329192790535e27838146276f9f082751fcae274639642725f6532718fd692708f1362700902726ebf3aa26df21ec26d0f8dd26c67a2926c5515826b88f63266f3c9e2650b228262e9c36261adfb82619725f2605c96b2600a3a125f82e8a25d5cb0725c720ed25abebb0259c7c5e257925b02577367425621d1e2558a435253d839b2522042124f55ba524f3408524d93c7424ac644924a501a3248aab162480f0d124788c032474e4be24581ce8241991de240ddfe523fd60f523f6b30a23dd652a23ce2b2123cbe08123b614ad2396526e23928aec235f89b9235d910f23410012233c86a3230f49ff230683dd22cc7a6722b2d9d322a7f79d229396f6228c64c0228732fa22570bac2249dc04223545d522160715220cdabd22053b5922005d3921e0428a21ced60a21b8174821ab9f1521a62967219dd79921998ede21741cc9215bfda0215a04d82159d5bb21266d94211ec630211a22582113668b210b952820dfd60320d7871a20bce02f20b98c9920a7b09e207f037c2070fa062057b16220396f25200709361ffdeb251fb37d381f9db4ab1f8f18461f8a1b3b1f7dded61f7a14781f7595ef1f4bf31d1f3fc28f1f3e05df1f2913231f28db8b1f230fb11f1d12511ec641f41eae14cf1e8a002c1e68b4231e6609641e527cd81e1b70ac1df1e1a91de3d2851dc353421dbe545c1da9f8b01da97e181da47ebe1da13e771d9cc1601d94c9b91d80c3f41d71dd541d65c5cf1d5f2f001d56584b1d3390211d23cbc21d0b7d241cf3f9081ce886521c9cc7ec1c994fde1c84bfb81c74bfaf1c5f5cdc1c5b427d1c3e38c11c3862a81c3624371bf419611bde02c51bd9d3921bcf998d1bc742ea1bb336fc1ba868341b936a191b6cfb7a1b6bd89e1b60642c1b54d16c1b4f36ab1b4bade31b4a21801b3e38871b284b211b1af83f1b1270601b062c9b1af1aceb1ae626791ade61701add62ba1add48571ad52a091ad185c41aa1f2961a895e251a80c5371a54311b1a496ef81a42d3dd1a2ef12a1a2887e419f0f27919e3c9dc19dd833019c4bf6119b6c9d0199cb7b71996ee1d196feffe1961c68519609ab419471c151928f75b1923caed19226c93191e4c2e190eb39618f8cc9e18f45afb18f1013518ed351818aa3e9b18a3874c1866ced118652d8e185f82b5185567c8180798e61803a29d17f2ab2717e4f91117d2057117cf79c317c011c417b4d77317b0686417ab1eff17a39ac717a3818f1783fbd8176ae90e176356eb1762df66174625cf1742e5b5173ec711173ced1b17377ae7171a7b2016febb8916fe145516f40ac816eda23116eccc6916ea085d16e631ce16a5a7bb1691cf861677034d167356581666e52f16574af016562b6e163de5541621533d161a3f0b161733631614919e160f570515d75b0f15d2145a15a524f91596afcb159299c0158440a31535212415164db4151512c414f0087a14dee67014bb547a14b84de014aa448114791a6814645822145b8c2f145183cf14379e10142e2d211405ffbe13dca63613cb8b8e13c9804713bf87f213bb8df313b6cf3d1384b722137e61ff136f6bb7135d32ab1356ab671333c6bb132d2b561329ec2f12dec370129c877c126fc32112577f7d12474d99123c64f612353e3712073ebf11f9400811e6982311e427a311d20462119dea4c1181f7a4117a3852116b6243116193f211586efd114077801133c82e10f26bb110e283f310dd006010da8c9b10d37d2110d1a2e210c8acaa10bf07bc10b0d20a10b09d4a109a5004106ec802106664a210576ed4105455721052a5dd0fff52270ffde7780ffca6e90ff396fd0fe4aa870fd525a60fd403be0fbaaf350f82bd130f7b0f350f66f8d10f5ed1470f3b71430f33b4690f2e907e0f27a43a0f1eaab10f101e8f0f0b7fda0f0715610f034cd10ed58e4c0ecea0500ea1b8e00ea113130e9686960e934a9f0e8cd4b00e7ffc610e7d0aae0e76379b0e4ebd4f0e4e613a0e3b8ee60e1d56550e124d510e00c93e0de35a280dc5f5010d8762e10d66e9fb0d63a95c0d6349fd0d59bd000d54d0830d465a8e0d2ae3850d1f7e7e0cf698130ce4f1f90cdc3c500cc8fa4c0cc5e0ea0cb074f00cae7c560ca6e91a0c9b6de10c88ddc00c8799dc0c70dd9f0c35efda0c2dd59d0c0f73b70bf0ed3a0be0ec8f0bc832260bc373680bb3d9560baaa3ed0b94a6e80b8582f40b6dfe080b4a56d10b45cd980b449a3e0b2e8f470b227d100af4aa7e0ae70a0b0ad4fd3e0ad200340ac46d370aab62970aaa49bf0aa76bdc0a9206c00a84bc6a0a7c22610a7b3b180a621f8e0a5c4dcc0a3e75c70a3c36130a2c16c109cc994809c777d109bedadf09a4a2c009a0e9d4099e2d400998485f096803640947bcc90943eb07093cdaf70922cb3f091313c908ef7f7608eaea0e08e949a008c43aa208ad16c7088eac17087e91880857402c083d437f082564ce08252ac108133eb408091be3079a0a6a079573be078f1eba077ed67b077dc03907673680074b9f1507243d6406c1038f06b3cb5e0694b319067528fb066e319906468def063c8c5806390349061edf52061ceba80605a01805e4c25e05cb7db705ca9b3205c8a9a305b8f03305a9123905a1896a0551bbaf053271e605212be3050e4aa60501ed9804fb736504e4390004e27f6e04db1e3d04c25d6904bf360804add65804967fbe0486d03d046348ce045a2c6a044f27e60445afd104431d87042e2d350422b3960418463d03f8b90b03f600d803ea99e903cc081e03b27e0903a79ee0039dc6190393ddbc0380d1400378ae5a036536c8031b791702f94d7202f5f81d02e3bea602dd540b02762e7902578b4f025213ee023dee43023bb60a0237c2200220ef260205ab6d01fec38101cd2a3c01c0f4f201b75e6801b0d7ed01a161ed01966859016b311a0149057501343f78012dcf6a0126a67000f4770a00f35b1f008c2a3300771aee0075ab6400647be0005da531004e817c0033ef50002cafbe002031de
  | 7 => 0xff62644cff53e592ff0cb589feb6e5f6feaa56b6fe97e004fe5e6258fe40c2c6fd7678ecfd3d0d4efd266eb8fd14212cfcfc8f40fcda639bfcaa8629fc8fd07efc26045bfb53afcbfb30e725fb049d43fa7983b1fa38aa80fa2f9486fa17304ef9ab9deef9a0cc48f985d573f9685cc1f95b4587f9520813f9071422f903841bf8e7702ff76d477ef72ced6bf6f31396f6b3586bf6856781f6790a6df65f3d65f5e6f7c2f5e0ea0bf5ddd0a9f5c884b7f588cd5ef522ee78f51d1bcef51a8d13f50e7f3ff4fb6bd5f4c590aaf3f99de7f3f4c868f38ca997f386df31f306d948f2ab4025f2992d33f26b8779f1a00e69f13d548df1178fc6f1150388f072cc37f01dc8ecf0137863eff14cbeefd3b058efc945dcef591560ef50f308ef28737cef041215eebc5f3ceea327dfee8a6b6aee410740ee3ea962ee2c4cfcee181018edce03adedbf8c7aed3305b4ecfe2237ecc74698ec6c338cec3f5472ec1dfd45ec17662cebd2501beb9c2baeead5f6efeab89944ea9b6a90ea54ccf2e9e5ee96e9af7f88e9031d52e8d89ab5e8cff7a0e8cc37bfe8b66f10e8641b46e8549ac0e8317636e7f958bde7a7366ee788d1aee76e6975e75bd290e73270b9e6b004e1e5d3afd7e5b83d32e5901efee57b2c39e54c5f13e54821e4e4e31f97e45fdcebe426bacce3bafc20e3a91780e39e80f8e35ac809e2da7b59e279cb45e25c2eafe24249a4e2250eade17e25b4e16024c5e14c018fe12371ace0f69888e0a74e6ce08522c7e028e7bbe00cdac4dff6c8b6dfe953c1dfd49d11dfc27cecdfb45f6edf7329afdf4c82f7df2e4f4fdf1b7a45debc686ade9d3552de9ae85ede8d90f7de394c87de1d895ede184cffdd6c1febdd03c1a3dcdf07aadcb1d34edcb04e87dc86840cdc5b4b3cdc383cfcdc014d98dbe25a8bdbcd5daedbbe0e6fdb64b73fdb1667c8db0487dada372111da0c73dcd9b3f03ed991f788d93230e0d928a845d8c54c3fd89ca136d86ccb52d832f17dd8187a09d814c689d80fd26bd7f371a1d7de5dc3d7c54568d76167b9d743cf0dd72dd098d7184d8cd62370e6d5d9291dd53c464ad4f64480d4a14135d4813befd40f1976d388fd6dd36f8fa2d32ae712d2edb25ed2abdd16d2a52669d2973071d2539f98d23eacd3d221bf9bd1f57c2bd1f2c0d0d1b56bd0d1874a9fd18638cfd1704e8fd147a165d13c85a8d1310f74d0738013d055c864d039c3f4d01b1e90cff5c191cfd3381bcfc22558cf80e527cf64c42fcf4f2bcdcf3ad10ccf119fa2ced3dc9aced16beaceac0e24ce7ed94fce6966dfce1b70fdcd9c90edcd6f6e13cd21abc6cce480f0cc8df9f9cbf827eccbd402adcbab124dcae5319ccaac6b0dca945540ca58e415ca382992ca33607eca2f36afca11ed22c9e32647c9c7423dc98e22fcc941d88ec8fe18a3c8cb7951c8c243e7c8a94dacc8a5db25c846fef9c7d9e862c7c1c172c6e0934fc68c3cfac62b84d5c5fe08cdc5ae1994c597ad76c5862d60c56fb330c563cb2ac55595f6c542aa2bc4d5fe33c42967f8c3daa14bc3b9a92cc3ab4bf1c36074dfc35648a6c33e493ac2fe3c87c2f45901c29ca9b7c265d11fc246be08c2465cdec2249263c1e1da87c1b4c9bac149f6afc0f7315ac0e97724c0e762f1c054ec7ec04d3061c04c7e07c03a8981c034c313bfe4d2f6bf861c92bf6af9c1bf1786fabf0acfd5beb6416abeaf4706be95f27ebe7996d1be733be6be5142eabe1ab848be14d35ebdfec150bdfae40dbdbb8227bdb5a929bd7a9c93bd5cfffdbd2b9117bd1e6e50bcde2b60bcda61d5bc669f09bc4465c1bbdcab48bbbcc448bb7e72b2baf0d185bac30cb8ba64bbdbba35abc8ba128702b9f67228b9b47947b91e94d9b8b0555fb8a302b0b86f87aeb7e6503db7934143b781cb95b6c0418bb641ef9db6055928b5e96bffb5b392dab5a735bbb5a34db2b59169e7b538e649b481e69ab42e85a6b3c1f8acb3b5f3d7b39d9c9fb363672ab2f78e3bb2f549b7b2a28af0b2914fc3b27b4bcbb22ea1e6b1cd2a8db16194f4b1120051b05ea26fafae5a83af9df72faf85bc3daf7bcb8aaf691dbbaf5b4ee4ae78b52cae57121faddb119bad720169acdbc6b5acc17bb3ac6ab09aac509a51ac28897cac1cbab8ac0ec509abee3357aba87c11aba0149bab98c1fcab84a78eab7766adab31876fab304536aad421d8aacce462aaa5ea14aa924cdfa9eeba56a9afc25da97dfe93a96e0f66a91c424ba8207136a801f909a7fcd258a7e3ed28a7c1c183a7bbf502a769fa42a75652eda6d371eba64768e3a60fc20ca596e32da566834aa4fbb03fa4c3b2f4a4976674a4950896a435a3e2a410980aa3f73d33a3ee720aa3c26a5aa346b77da3095e8ba2e7379da284b30fa2610096a234c848a206eef0a1e1649da1c18542a1b07ae0a19f599da1686d79a1645991a099455fa04eb6a2a001eafb9fef24ed9f9e740e9f3e9f379eb8ce1b9e7b14a09e7552159e661a829e0d96e49dcc0a249dbf4fd49d7c332b9d4433cd9d25d23a9d2223099d03a6959cd0ceef9caea34a9c627c549c1862309c1767409c000b0b9bb6f2e49ba2be479b20ffdb9ae5e8ed9a5e72c09a0019da99df831599b018549951dabd994b6bc79930571c98ff929e98fb161098db53d198d02a7998a292729885561e987d6c6d98632a79982bedf697e15f399788db9b9779d0e097161abe96fec4149698f4999678f0109676c8f49600cc3095962c4e9543d00d952e01dd94f87e9b94eeccc294c43692948fdb009474c536945346f7942d7adc93a8d2739337eae692a3797b9265063f915ae70e91586c3b91428ebf90dc5c2e90a353f190390c2c902b27dc8f1171058f09c0c48ec2c9fa8eb6f26c8ea8c3558e6b93c88e6923d38e3dce018dfdce9b8df009ed8db89e1d8da5efc98d9341fa8d24172a8cf968c88cd9fd068c56df298c40a9268c1b68188c04847f8beba5db8bb9f4678b82dbf08b3b042b8b18a3c98a852b7b89e5a3a389b9b57b898e46ee8911427689008f5688fe2e7e8860bcc088134fd287ee459b87e6d87f87a02d0a874dc393874463ff873e21f186b063a685ebe5c285e536e385c30b3e85b3cb858596accf85389860851a270984e014c28471d0318400703283f0bc4083e5f9c183c30acd837cfcae82baf31c82a84b6082641b57822a61e181ffab7481efbbc581d4433981b9247d81af8f8281ab6704818e94898120ef858120385e8110935a80cce2358096879980756470801c5c7f800986517fc97ddc7f8e04597f6424d77e1becd57e0334b67d98ee0d7d7e8e597d36f2837d260abb7d13dc7a7d03944d7cfc8cc67ceaf0497c90a0787c794e177c7496667c693ec77c68aa2c7c64c23f7bdd438e7b4f87f07b4743147b30e4367b2dcad47b056dcc7ad8c7897aa67aff7a9137497a7b50517a469fca78f9a7ff78dc57767851015178294729780610717805008777ee045177d83a087767c75e775c2673774190867727b4527703a2d576ec8d3b76c82952768d4eb87686fed97604147975d0a6df75c1af18753e11a67505a63a75000dcf74d2589174aea02574a0ed3374552084738d390d7305f8a772ede5f672c1464a72c0736b72a1146a726b70207267efcd7216d12d7212ec82716cd6b7715cc91b7157a95971356d5b70b4b2e570137ae2701375e96ff7fae06ff14f3d6fcf23986f8c8f866ee5cdb06ead5e296e8c383f6e1ff74f6dc773b16d9062cf6d84079f6d6ad1276cdfdd196c9ede646c3395ca6c1dffc46bfbd41f6bf004f16bdb122c6bca68e96bc655016bbd27706b9f28136b61b8146b33dbef6b277ca26b113d2d6af6eb326ae8f77b6ab0b21269f0853769e418a669b9ab8d699d9f52699b81ec68f10d1a68ee7b2368d8983b68cf1e1f68a6c117687a1ad4683178b5682884a6680f4d1068032b5c67fc778867ae281167619fb9672bc3a9671649d9665c912e65dc1b71656473436550091b6511740964e5e92264c9ed11645dd60b643bfd97642ea20363ed2f7d638608a8637b376c6363a7966362af4062ef16e962c5ecb1628044056270e966626c51d16242407e62128e1e619dba8d618e361861764dbb612f2d5261095bc360ecb71060de6f8360d96ac660a74bf26075c101604f76886020bdb66000f52f5ffc64ed5ff6c63c5f3c3a8c5f2e51ce5f0c26295edf84645e8a81195e2570955e11741f5dba06ea5d2e57ee5d29d11f5cedb8e65c6da8bb5c390f105c1db5095c18a5705bdad4065bd544e55bd377865b7fd8145b38d6b05b2754765aca4f2a5a91607b5a3f08485a3b6ba859e8e36059cbc1405977a9a4596c6e44592c744f58bbe88e588a4ac65875974e5852a6c3581208555807eb3957cd2c9f57beccad574c4fa156e842d656a515d6562e9c2255e0cb1a55d998d755b9fd9855b48db454f42be35454031853f0425e53cd443153c42bd053c0c2b652bf683e52afe9e0526898ac518e82c8518e2006513b21fb50c29005508a9c45504de1325049894250356059501ec9c7500185224fdf597d4fda168f4fc68c744fc38af84fba7d404fa1be814f2fd26b4eee16dd4eeb68294e5ac3dd4e4928ba4e1b737c4df947d74db800874c0f0d6e4c0c0a044b85515a4b6f199e4a92a4564a2f392e4a2b794c4a25f85e4a0d0d89493525aa48cb76d74822d320481f82f5481828a4480980f1479ee90d46d7f2b946cee2cb469ff9614677237f4639be104639714f45ae1c13458fc644458bf06e455c5a0545559875453ac2f945336cd0452d0d6444af8ab043fc4efd4360726542bd830e42914a4b424d37014246bb8e41fca16a41e7190b41b8a0f5419099294162160141601d57414500a440ef4a28401a26f13f14d8c43f02e8a33eee00cb3dcc19e63d7396483d4b66033d364a683d31c5093cf662b83cde2ddf3cbc023a3c870b923c4244f63c2594b73bbcc6c73b9a9b223b5953d23b0bdde03af0d4043acea85f3a57bcd53a22018e39ae2697395f4ce0394a101a393ba36038f270de38e8b2c138aec72a38aae9e73801c63837c74ba936fb58e636be88623635c740361fdd103601238335be366e35b39559359169b43586882034fc2bb234cd018b34c8f2ff34706f613456bdd6341a2f123401ba8b33f4486e33dac49a336369a93343c2b833413e04330ed1d732da9197322a0be131cd2d0c31be1a3b31ab016731842a08312f26bd30fa5b2730c760d8305ed659302d389c2fb641ba2f9df4b52f6dee8b2f5b51632f5007332f3925be2ebe09912eaa99a52e4f2aed2e097dbc2dfc896b2ddac29f2dd7b1ee2dd1932c2dc9e0352cf360c32ce3adec2c9ad23f2c236c162bf904cb2b81677c2b65d6452b45de082af74c672ad79db32ac0c5cf2a0ee69d2a0baaf029eb2adf29b9e3522945d45e2944de83291c44ca28fa192528631707283731c827f0aad127e3eaae27e2ed5827d6512b27794f3626e72c3a260acaac256e6a812543a2b52526c9ac24ce6c4524a501a32474e4be244af77a23cbe08123b614ad2396526e238208fc235f89b9235d910f230f49ff227e409521fb492f21c182c821af852c218377c5213a429d20e803f820bce02f20a90d00207ff9572070fa0620396f252031cabe1fc9da5f1fb37d381f9db4ab1f8145081f7156c11e76284f1de922c11dc353421db9c76c1d25cfc01d16227f1cd0cc751c1873531b4f36ab1b48bd441afebc7c1af039a61ae626791adede441a97b6081a86a51a1a438eb11a025dc819c4bf6119a4b3b31947e92019471c15190eb39618f8cc9e188553a4187d6eec1877c0b7185b434718371bb617c73b011783fbd81762df661742e5b516f9ec2b16ad6ee11698f21f1621533d161733631614919e15eaf21215d8851315a19f991596afcb1595eec71593b80a1522d2dc150c92501487f3ce147a0133145b8c2f14458f0c13c704eb13bb8df31367bc06135d32ab135173e912ce4b461278cf10125558d112353e371229d6ba12204b7211a4d31b116b6243115767f8114a75f6114a454610fee45a109b6cbf108b753510390eab1032f1971016e3060ff396fd0fd525a60fcf53a50fbaaf350f5e14710f101e8f0f0715610e4feba50de35a280db9a5c90db3fbd40d7f27f50d64a27e0d6349fd0d0942190d0920130cb41cc80cb074f00ca6e91a0c43938d0c286dcc0be8eb580b4e368a0af5b2ec0a98b3ca0a5c4dcc0a49b6c40a35c3d309a8e0dc09770faf091929ad08fe0ada08ef7f7608eaea0e08a5873c088779c40868a3f708570c7e0855f5a307d3f05107bb8701079845d80767ce3d076612ac074b9f150744667e072cc82807243d6407223ad9070f4a9f069a1fe9067c427205e5346905ce2d2605cb7db704f5f29404e43900049d6ef60471d2b0044fa70b03887780034eeb600338031602eaf13102dd540b027e48560252f817021bc91701d13a5a01b75e6801966859015ce13e009beb9c0090ee7b007c5792005da531002e1ca6
  | 8 => 0xf6856781ee410740e54c5f13e279cb45db0487dace1b70fdc6e0934fbeaf4706bdfec150a6d371eba1686d79a04eb6a28da5efc985ebe5c27fc97ddc7b2dcad47ad8c789768d4eb874a0ed3363ed2f7d4e1b737c4df947d74a25f85e4639714f3d364a682c236c16283731c823b614ad235d910f1ae6267919c4bf6118f8cc9e13bb8df3116b62430fd525a60d6349fd07243d64
  | 9 => 0x2c236c16
  | _ => 0

def LT : Nat → Nat
  | 4 => 0x555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555
  | 5 => 0x666666666666666666666666666656666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666656666666666666666666666666666666666656666666666666666666666666666666666666666666666666666656666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666666666666666666666666666666656666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666656666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666665666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666656666666666666666665666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666666666666666666666
  | 6 => 0x777776777777777777776767777777777777777777777777777777777767777767767777777777767777777777777767767767777666777767777776777777777777777777776777777777777777777767777777777777777777777677767777777777776767777777777777777777777777777777776776777777777677777777777777777777777777777777767777777777777777777777777777777677776777777777777777777777777777777776777777777777776777776777777677777777777776677777777777777777777777777776777777777677777777777776777777777777777677777776777777767777777777777767777776777777777777767777777677777777776777676777777777777777777777777777777777776777777777777767777777777777777777777777777777777777777777767777777767776767777777777677777677677777777776777777777777777777777777767677777777777777777777777677777777776777777777777777777777777777777777777777777677777777777777777777767777777777777777777767777776777767777767777777677777777777777777777777677777777777777777776777776777777677777777777777777777777777777777777777777777777777777777767777777777777777777777777777767767777777777767777777777777777777777777767767777677777777777777777777777677777777777777767777777777777777777777777777777777777777777777777777777776777777777777777777777777777777777777777777777777777777777777777777767777767777777777777777777677777777777767777677777777777767777777777777777777777777767777776777777767777777777777777677777777777777777777777777776777777777777777777777777677777777777777777777777777777777777776777777767777777777767777777777777777777677777777777777777777777777777777777776777777777777777777777777777777777777777777767767777777777777776677777777777777777777777777777777777777777777777776777777777777777777777777777777777777776777777777777777777676767777777767777777777777777777777677777777777777777777767777777777777777777777777777777777777777777777777777767777777777777777777777777777777777777777767767777777777667677777776777767777777777777767777777777777777777777777777777777777777777777777777777777777777777677777777777777777766777777777777777777677777777777777777777777777667776677777777777777777777777777777777776777777777777777777777777777777777677777777777777777777777777777767777777777777777777777777777667767777777677777777777777777777777776777777777777677777777777777777777777777777777777777777777777767777777777777767777777777777777777777777777777777777776776777777777777777777777777777777677777777777777677776777777776776777777777776777777776777777777777777777777677777777777677777767777777777677777777777776667777777777677777777777777777767777777777777777777677777777677777777776777677777776777777777777777777777777777767677777777777777777777777677776777777777777776777777777777777677777777776777777777777777777777777777767777777776777777777777777777777777777776777777677776777777777777777777767777777777777777767767767777777777777777777777777777777777777777776777777777777777776777777777776767777777766777777777777767777777776777777777777776777777777777777777777777777677777777777777777777776777777777767777777677777777777777777777777777777777777777667777777777777777677777777777777777777777777777777777777777777777777777777777777777777777777777777777767777777777777767777777777777777777777777777777777777777777
  | 7 => 0x8888888887788888888888888776878878778788888887888888888888788788888778888888778888878878888888887888888787778887877878888888887788788688868878786788788878778888887888788788888686888888788778887887888687787887878888876878778878788788878888876886878888888888788888788788787888678888888878787768888888787888878888877768886887786888888888778788788888888888787888878888888878888888888887778888778877888778887888887878877888888788888888888777788788788887878888887878877878878888888888888778888688778788688788888888888888878887778878887888768887888887887878788888888888877877888887888888888778887888888788788788877778887688877787888888788788887878878888887878888888887878888888888878887768878788788887888888888888788788788887888888788888787887788888886888888768888887878888887878878888888888888888878787788888888886888687887888777788878878888878878888788888888788688878888888688888878888888888888777887888888888886888888887888888888888888678888878688788888788688888888888768887786888888887787778776888888878867886788887888887888788888788777888888776888777888788888878878788887888788888888877878778788887888678888887888888778888888888788788888878788888887888877888878
  | 8 => 0x7777777777777777777777777677777777777
  | 9 => 0x6
  | _ => 0

def DT : Nat → Nat
  | 4 => 0x2526cd4534077000000023b759a24d4d000000002306cd354349100000002869e4d01dc5100000002646cd6c570d000000002506ed353407700000002536cda24f4d000000002646cd5c484d0000000027a6cd7e1dc5100000002706cd7f1dc5c00000002646cd7457051000000023b7ed3529c7700000002306cd3539c9000000002306cd662dc5100000002307dd7f5705100000002877ed7f1dc510000000251915b34d47700000002307ed7f2c051000000026494db34f4d800000002307317f57051000000023070d5a3405100000002306cd353d88f0000000230749353408000000002307dd411dc5100000002308795c3405100000002707ed7f2c05100000002306cd724d4e900000002887a9353e05100000002707ed411dc51000000026494dc24d4d00000000253759a24d4d000000002646cd665705100000002307b9b34d4f8000000023070d7a1dc5100000002446cd7f5705100000002307edd65047700000002307ed7f2dc5100000002308855b340510000000287880d01dc51000000026494dc74d4d000000002616cd7f570510000000253915d64d4770000000253759c84d4d0000000023070d5c484d000000002636cd353d851000000025384db3340770000000230839d534077000000026494dbb4d4d0000000023070d7f5705c000000023b789d64d47700000002307dd352005100000002537add64d4d0000000023b7edd6504770000000253789b34f4770000000251789b34d47700000001b36896c4d4d00000000230759a64d4d000000002707ed352005100000002307edd64d49000000002707ed7f1dc510000000230759a2504d00000000253839b3360770000000253835d64d4d0000000023b839d63407700000002307ed7f2c0a70000000230751453407700000002636cd35360510000000251839b33407700000002626cd664d45100000002307edd64d48000000002307e9353dc5100000002307ed4129c77000000026494db3514d000000002707b1351dc5100000002646cd35484d800000002648855c34051000000023070d665705100000001eb6cd35484d000000002646cd3d484d000000002406cd7f29c77000000023b7edd64d48000000002526cd3539c77000000024070d7f57051000000023085d5c3405c00000002877e5351dc510000000253789d64d47700000002307e5352c05100000002306cd353dce8000000023070d7f5705100000002648713534051000000023070d7f2c05100000002526cd353607700000002526cd3d340770000000230881d5340770000000230789352d8770000000253839d63407700000002306cd6d2c05100000002307edc85fc5100000002306cd7f2ac770000000279945b3340770000000264915b35705100000002307ed3529c8000000002307ed7f29c7700000002869915c34051000000026494db3534d000000002646cd664f4510000000230838d02d87700000002307ed352d05100000002707ed7f29c77000000024085d5c3405100000002306cd7e56c510000000253789d668935000000026485d5c484d00000000230789d65047700000002307b13529c7700000002506cd3536077000000020e6cd6c34077000000027994dd63407700000002616cd353605100000002707e5351dc51000000027b6cd6b3a4770000000230751413407700000002307ed7f2d8770000000253839d6688d000000002306cd5b518d000000002306cd563405c00000002537b1d64d47700000002616cd3d34051000000023085d5b340510000000262915b34d451000000029ba20d01dc5100000002307e5d54d477000000027070d7f1dc5100000002536eda24d4d00000000286989353405100000002307edd64d4f700000002706cd6d1dc510000000230789d64d48000000002646cd6d570510000000253881d63407700000002467e9351dc510000000230851d634077000000026494db34d4f600000002307edd650480000000026485d665705100000002706cd7e1dc5100000002767ed351dc5100000002307513534090000000023085cd02dc5100000002776cd7f1dc5100000002306cd5a3408f00000002306cd5a3405c00000002306cd5c494d0000000026494dbb4d4d800000002307513534080000000026494db34d4e700000002646cd6a4d4510000000230839d634080000000023f7edd64d477000000026494dbb4f4d000000002507edd64d47700000002307ed7f51877000000023b7e9351dc5100000002406cd5634051000000026494dd24d4d000000002646cd5c518d000000002306cd7d1dc5c00000002307ed7f5445100000002307e5c84d451000000026494db34d4d800000002307e97d1dc51000000026485d5c340510000000297888d01dc5100000002306cd7a1dc5c000000026494db34f4d00000000230888d02d491000000026482db3570d0000000023071d5a3405100000002636cd5a34051000000023070d7f29c77000000027a7ed7f1dc51000000023b7ed352c0510000000253799b34d4770000000253839e27587700000002306cd7d3a07700000002989ecd01dc51000000023b749353407700000002306cd7e29c770000000253789bb4d477000000027a884d01dc5100000002406cd7d1dc5100000002466cd7d1dc51000000026285d3534051000000026371d35340510000000253839bb3407700000002306cd665705c00000002406cd5c484d000000002636ed353405100000002406cd7f5705c00000002306cd7f5708f00000002306cd7f5705c00000002646ed35484d000000002307edaf5fc7700000002467edd64d47700000002306cd7f2c05c0000000252751353407700000002306cd5b484d0000000023b7edd64d47700000002306cd7f570e8000000023071d7f5705100000002307edd65147700000002406cd66570510000000262945b34d4d00000000230755a24d4d000000002646cd6657121000000026485d353605100000002307edd65387700000002307ed412c05100000002177ad353405100000002307edd65e877000000026485d3d3405100000002537c1d64d47700000002406cd7f5705100000002306cd7e5187700000002646ed664d45100000002466cd7f5705100000002406cd7f2c051000000026494db3558d000000002307e935200510000000230755c84d4d000000002536cda24d4d8
  | 5 => 0x8fdb34d4d81dc51000008c1fb5fcb01dc51000008c1c35fd351dc5c000008c1c74d4d01d05100000916306cd351dc51000008c1b34d5213c8770000099230749353405100000901b35714a34051000008c1b34d0d01dc51000008c1b35d4e31dc5100000901b34d4d029c77000008c1c86cd353405100000911b34d4d01dc51000008c20e6cd21340770000094e0e6cd9a3407700000992536cd3534028000008c1e26cd351dc5c000008c1b35e8e91dc51000008c1cc538d01dc51000008c1b34f52734051000008e1b34d4f21dc5100000a21fb7ad3534051000008c1e26cd352c051000008c1b34d4ee3405c000008c1f14d5273405100000a5db34d4d01dc510000092db34d4d029c77000008e1bb4d4d81dc5100000002646cd5c484d000000901c3571353405100000901b3528d01dc5c000008c1b35fd351d051000008e20e6ccd01dc51000008c2174d527340510000098db34d4d01d05100000991c96cd664d45100000985b34d4d01dc51000009c1b34d5032c05100000992306cd3536051000008c1bb4d4d01d051000008c1b34d4d02d491000008edfb7593534077000009921f85d3534051000008c222340b51dc51000008c1b34d4d029c7700000901c34d4d01dc5c000008c1b35fd471dc5c000008e1bb4f4d01dc51000008c1b3534d01dc51000009ea226ccd01dc5100000a1a304d4d01dc51000008c1ce68935340510000096dbf4d4d01dc51000008c1eb6cd35340510000097db34d4f61dc51000008c1b34d52134080000008c1b34d4cd20051000008c1c35713534051000008c1b3528d01dc5c0000094e0e759353407700000992306cd3d34051000008c1f75f0d01dc51000008b5b34d4d01dc51000008c1b3528d02c051000008c1bf4d5031dc51000008c1b34d4d029c8b000009c1b35fc771442c000008c1bf504d01dc510000094e306cd45340770000094e476cd7f51c7700000901b35714734051000008e1b34d4d020051000008c1b3548d029c770000096db3599351dc51000009c1c86cd3534051000008c1b36697534077000008c1c34d4d023c77000008c1c34d4d01dc5c000008c1b34d52136077000008c1c34d4d02c051000008c221570d01dc510000094e0e6cce93407700000839b3588d01dc51000008c1b3599411dc510000094dd66393534077000008c1b36693538c770000092db34d4d01dc28000008e1b34d4d81dc51000008c1fb5fd3529c77000008c222758d02dc51000009c1b3474d01dc51000008c1fb4d5032c051000008c1b34d50829c7700000991b35711d34051000008c1b34f52134077000008c1b34d4d01d0510000094dd66893534077000009c1b34d4d029c7700000941d34d4d01dc51000008c1f14d52134077000008c1b34d4f223c77000008c1b34d4f21dc5c000008c1e26fd351dc5100000985b3564d01dc51000008c1b34d4f22c051000008c1bf4d4ee34051000008c2174d52134077000009c2477ed351dc51000008e1b34f4d01dc51000008c1e66cd351dc51000008c1b35d1464d477000008c20e6ccd01dc5c000008c2214d52c3405100000002307ed7f2c051000008c20e6ccd02c051000008c1b34d4f83408f000008c1b35995c24451000008e1f14d4d01dc510000094db364d353407700000991b35995c1dc51000008edb34d4d029c77000008c1fb7257f57051000008c1fb6fd411dc51000008c1fb759351dc3900000901b34d4d11dc51000008e2174d4d01dc51000008c1b24d4d01dc51000008c1b3599353b851000008c1d6689353409100000901b35fd5c34051000008c1b34d4fb3407700000992536ed35340160000094dd66293534077000008c20e789d61dc510000098a2d6cd3534051000008c1b35d1514d451000008c1fb7213534051000008c1d67255c51cd0000008c1b34d4d02ac77000008c20d6cd3534051000008c2175d1351dc510000096dbb4d4d01dc510000096db369d3534077000008c1b34d4ee3a0d000000992175710e34051000008edbf504d01dc51000008c1e76cd3534077000008c1bf528d01dc51000008c1bb4d5031dc510000096db04d4d01dc51000008c1bb504d01dc51000008c1b35712d484d0000008c1b34d4d02005c000009ee536cd6d1dc51000008c21c4d4d01dc51000008c1b35994a1dc51000008c1fb4d4d029c77000008c1aa4d4d021c77000008c1b3504d01dc4e000008c1fb6cd353e08f00000992214d4d01dc5100000a1db35fcd01dc51000008c1b36753534077000008c1b34d4d81dc5c000008c1fb725411dc51000008c21d4d4d01dc51000008c1b34d4d82c05100000901b34d5031dc51000008c1b35fcd02c05100000991b35711034051000008c1ce4d4d029c770000093db34d4d01dc51000008c1c3599351dc5100000901b3504d01dc5100000992066cd5c34051000008edfb4d4941dc5100000901b35fd4a1dc5100000a1e22570d01dc51000008c1f74d4f81dc51000008c1b35d4d021c770000092db34d5031dc51000008c1e26ed351dc51000008c1bf4d4f21dc51000008c1d66fd413407700000992536cd3534016000008c1bb4d4ee340510000094e476cd35360770000092db3504d01dc5100000a7288888d01dc51000008c1b34f4d01dc5c000009ee53889d6340770000094db368535340770000093db34d4d022c51000008c1fb4d49f1dc51000008c1b34f4d02c051000008c20e6fcd01dc51000008c1b34d4e321c77000008c1f14d4d01dc5c0000096db34d4d01dc51000008c1f14d4d02c0510000094db36893534051000008edb34d4d01dc55000008c1b34d5031dc5100000901c35fd351dc51000008c1c24d4d020051000008c2174d4d01dc5c000008c1d66899a4d4d0000008c2174d4d02c051000008c1b3504d01dc510000000253759a24d4d0000008c1b34d4d02d877000008c1bb4d4f61dc5100000992536ed3534077000008c20e6cd661dc510000094e476cd3d34077000008c18a4d4d02d8770000096db34d4d022c5100000901e26cd351dc51000009c1fb4d4d029c77000008c1b34d50322c5100000901b34d4ee34051000008c1f54d4d01dc5100000916306cd5c1dc51000008c1c24d4d81dc510000096db3548d01dc51000008c1bb528d01dc5100000002646cd6657051000008c1b3504d022c51000008c1fb6cd7f2c051000008c1b3549031dc510000092de26cd351dc51000009c1b35fcd02c051000009c1fb4d4f81dc51000008c1c35fd351dc51000008c1ce4d4d01dc280000092db34d4ee34051000008c1b3548d02d877000008c1bf4d4d020051000008c1d67254134077000008c1b368935340a700000901b35fd471dc51000008c1e26cd351dc51000008c2175712734051000008c1b34d4d01dc50000008c1b34d4ee34051000008c1b35993520051000008c1bf4d4d81dc51000008c1b34c9213407700000901b3528d01dc51000009c1b34d5031dc51000008c1fb6cd411dc51000008c1c34d4c51dc51000008c20e789b3668770000094e306cd7a3a477000009c1b3504d01dc51000008c1e26cd3522c51000008c20e7c1b31dc5100000a1a30570d01dc510000092db3528d01dc51000008c1b34d4f61dc510000092db35b5351dc51000008c1bb4d4f21dc5100000002307edd650477000008c1b35d5273405100000901c34d4d01dc51000008c1e26cd521dc51000008b5b3570d01dc510000096db34d4df34077000008edb34d5031dc51000008c1b3548ee34051000008c1bf4f4d01dc51000008c20e6ecd01dc5100000992538c1b34d4d8000008edb3504d01dc51000008c1b34d50337c77000008c1b34d52738c51000008c1f15d4ee34051000008c1b3598a31dc51000009923085d5c340510000094e456cd351dc51000008c1b34d4d02404e000008c1b3528d01dc51000006cd8a5b135340770000092dc34d4d01dc51000008c1b3504df34077000008c20e6c0d01dc51000008c1b35b5351dc51000008c1b34d4d01e05c000008c1fb5fcd02c051000008c1fb6fd35200510000094dc86cd35340510000094e306cd4d34077000008c1b35993d1dc51000008c1b3548d01443500000941b34d4e31dc51000008c1f1599351dc51000008c1b34d5032c0a7000008c1b34d4e71dc4e00000992538c1b34f4d000000901b34d4f21dc51000008c1c34d4d01dc51000008c1b3528d022c51000009c1e26cd351dc51000008c1c74d4d81dc51000008c217599351dc51000009c1b34d4ee34051000008c1e2759474d477000009020e6ccd01dc51000008c1b34d4d01b05c000008c1b35fd5c14439000008edbf4d4d02005100000992456cd351dc51000008bdb34d4d01dc5100000992536cd3536051000008c1b35f9351dc510000092db34d4f21dc51000000026494dbb4d4d0000008c1bb4d4d0200510000096db34d4f221c77000008c1c34d4d022c51000008ede26cd351dc510000092e0e6ccd01dc51000008c2175712134077000008c1b34d4d0240510000094dd66cda24d4d0000008edb34d4ee3405100000991b34d5213e0d0000008c1e26cd3537c77000008c1fb4d4d02d877000008c1b35fca71dc2c0000096dce4d4d01dc51000008c1c3548d01dc51000008c1b34d4ee37cd00000094dd66898a4d4d0000008c1b34d4f21dc510000094e386cd3536077000008c1d66cd41340770000094deb6cd3534051000008c1b35fce92c051000008c1ce4d5031dc51000008c1fb759352007700000992536cd3d34051000008edfb6cd411dc51000008c1bb4d4d81dc51000008c1d66294134077000008c1b35d56c3407700000992174d52734051000008c20e6ccd01dc51000008c1b35fcd02dc51000008c1ce504d01dc51000008c1b34d4e71dc51000008c1c35fd5c1442c000008c1b34d4d02004e000008c1b36693549cd00000094e306cd3534074000009c1b3528d01dc5100000911b3534d01dc51000009162d6cd351dc51000008c1fb7253520051000008c1f64d4d01dc51000008c1b05fcd01dc5100000941b35fd353a477000008c1b35d52134077000008c1b34d4f222c5100000901b34d4d020051000009ba306cd353e0e900000919b34d4d0200510000094e386cd3d34077000008c20e6ccd022c5100000a1a644d4d01dc51000008c1b3548f21dc51000008c1b34d4e722c51000008c1b34d4d81dc4e000008edb3528d01dc51000008c1b34d52138c77000009c1c34d4d01dc51000008c1bb4f4d01dc51000008c1b36993534051000008e1b35d4d01dc51000008c1d66fd35340800000092db34d4d020051000008c1b3528df3407700000901b34d4d81dc51000008c1b76893534051000008e1b34d4e31dc51000008c1c3564d01dc51000008c1d24d4d01dc510000091e307ed3529c77000008edc34d4d01dc5100000a22796ccd01dc51000008c1b35d56f34051000009c1fb4d5031dc51000008c1e2739351dc51000008c1fb6cd3524051000008c1f74d4ee34051000008c1b34d4d020051000008c1c34d4df34077000008c1b34f4d01dc4e0000092db34d4d81dc51000008c1ce4d4ee340510000091e306cd7f2c051000008c1fb759b350477000009c1b34d4f21dc5100000a1a2d4d4d01dc51000008c1d24d4d022c5100000901b34f4d01dc5100000901f14d4d01dc5100000002707ed7f1dc510000096db36893534051000009c20e6ccd01dc51000008c1b34d4d81dc51000008ee227593534077000008c215839d634077000008c20e7594734077000008c1b3564f21dc51000008c1b36893540c5100000902174d4d01dc5100000991b35995c340510000092db34f4d01dc51000008edb34d4f21dc51000008c1b36894134051000008edd66cd4134077000008c1b3548d02005100000991b35c5664d4510000092df14d4d01dc5100000819b34d4df34077000008c1b3519353407700000a1db34d50b1dc51000008c1b34d4f237c77000008c1b35fd0929c770000094e0d6cd3534051000008c2226cd5c3405c000008ee0e6ccd01dc51000008c1d67253534080000008c1b35fd5c1443500000992174d52134077000008c1fb759351dc21000008c1b34d50b2c0510000092e174d4d01dc51000008c1b34d4d822c51000008c1ce528d01dc51000008c20e6ccdf340770000091630835b34d45100000941b34d4e934077000008c1b3621353a491000008edf64d4d01dc51000008c1b34f4d01dc51000008c1f64d4df34077000008c1f14d4d01dc51000008c1b3548d81dc5100000a223b7ed351dc51000008c2215b5351dc51000008c1b35453534051000008c1b356d3234051000008e1b36693534077000008c2174d4d01dc51000008c1fb6cd352005100000992536edb34d4d00000085dde4d4d01dc51000009c1b34d4d020051000008c1b34f4d022c51000009ee536cd3536077000008c1b34b8d022c51000008c1b35fc941dc5c000008c1b35fd5c1c451000008c1f14d4d022c5100000002307edd64d480000008c1b35d4d01dc5c000008c1e26cda24d451000008c1b35d4d02c051000008c1c35fd5c1dc51000009e9b34d4d02dc51000008c1d66cd3534090000008c1fb7594134077000008c1e27593524477000008c2174d4d022c51000008c1bb4d4d01dc4b000008c1f1548d01dc51000009ddb34d4d01dc51000008edb34d4d020051000008c1b34d4e31dc5c000008c1b34d52734087000009c1b34d4d81dc510000094e477edd64d477000009c1b35fcd01dc51000008c1b34d4e32c051000008c1b35f0ee34051000008c1b35ad353a477000008c1b34d4df34080000008c1fb5fca31dc51000008c217548d01dc51000008c20b6cd3534077000009ee536cd3d34077000008c1b3558d021c77000008c1ce4d4f21dc51000009c1b3519353407700000992476ed3534051000008c1b355cd01dc51000008c1b34dcd02c051000008c1fb5fd2e1dc51000008c1ea6cd353e051000008c20e738d01dc51000008c1eb79db34d4d0000008edb34d4d81dc51000008c1b54d4d02c051000008c1b34d4df36077000008c1fb5fc981dc51000009c1b34f4d01dc51000008c1b3514d020051000009c1f14d4d01dc5100000991b35712e34051000008c1ec6cda74d477000008c1f65e8d01dc51000008c1b36894a34051000009c1b35453534051000008c1d34d4d01dc5100000901b34d4d01e051000009c2174d4d01dc5100000992477edc94d451000008c1b35993549d2100000992175713534051000008edb34f4d01dc5100000a22797ecd01dc51000008c1b35fcd02c0a7000008c1fb4d4f829c77000008c1b3514d81dc51000008edf14d4d01dc51000008c1b34f4df34077000008c1c36893534051000008c1b35b55c1dc51000008c1f14d4df34077000008c1d66cd3534080000008ee174d4d01dc5100000901b34d4d01b051000009e9b34d4d01dc51000008edfb6cd352005100000992536cd3d4d4d0000008c1d66293534080000008c2174d4df34077000009c1fb6cd7f1dc51000008c1ce4d4d020051000008c1b3538d0200510000094e306cd353d877000008c1b35710e3405c000008c1b366935340b0000008c1fb7597f51c770000096db34d4d029c77000008c1b34d4f733451000008c2175995c1dc5100000991b3599353e051000008c1b34d50329c770000094de26cd351dc51000009c19e4d4d01dc51000008c1fb519353407700000a1a7b5fcd01dc51000009e6306ccd01dc51000008c1b3504d029c77000008c1bf5d4d01dc51000008c1ce4d4d81dc51000008c1b3689353c851000008c1e27599a4d4770000000253789d64d477000009adb34d4d01dc51000008c1b35b5354b051000008c1f0759351dc51000008c20e6cda234051000008c1bf4d4e31dc51000008c217570d01442c000008c20e758d024477000008c1b34ed2134077000008c1ec6cd351dc51000008e1b34d4d021c77000008c1cc4d4d020051000008c1b35d5661dc51000008c1fb5453534051000008c1b35e4d01dc51000008c1ce4f4d01dc51000000023070d7f57051000008c2014d4d01dc51000008c1fb759b34d480000008c1fb5fcb025051000009e9b34d5081dc510000092db34c8d01dc51000008c1b35fd5c14430000008c1e26cd3529c77000008c1b34d4ee340a7000008c2206cda734077000008c1b34d4f624451000009c1fb5fcd01dc5100000991b34d52034051000008c1b34c8d01dc51000008edd66cd3534080000008c1eb789b34d451000008c1f14d47714439000008c2206c0d01dc51000009c1b34d50329c770000094e306ed3536077000008c1b34d50d1dc51000008c1bb4d4d01dc57000008b5e26cd351dc510000094e306cd3539c7700000992306cd5634051000008c1b35a9351dc51000009fa536cd3d3407700000991b35b5351dc51000008c6174d4d01dc51000008c1fb504941dc51000008c1b35fcaf1dc51000008c1fb4d4b01441f000008c1b36893536051000008c1bf6693534077000009ee536cd7f3a477000008c1fb759353e0910000094e306ed3d34077000008c1b3528d029c7700000992386ed353405100000902226cd5c34051000008c1bb5d4d01dc510000099217599351dc51000008d1b36893534051000008c1b3504d01dc5500000985c34d4d01dc51000008c1b3669664d477000009c1b35fce91dc510000094e3074935340770000094e0e6ccd01dc51000008c1b34d527484d0000008c1b36893d34051000008c1c35714a34051000008c1b34d4ce1dc51000008c1bb4d4e31dc51000008c1fb7593534080000008c1f16893534051000008c1c34d4d029c770000091630839b31dc51000008c1b35714634077000008c20e7599a34077000008c1b35fd5c170510000000253839d634077000009e9fb4d4d01dc51000008c1b34d4d02c087000008c20e721b334051000008e1b34d52734051000008c2176893534051000008c2206ccd01dc51000009ee306cd7f1dc5c000009c1b34c8d01dc51000008c1c3528d01dc5c00000901b35fc941dc51000008c1b34d50b1dc51000009e9ce4d4d01dc510000097db34d4d021c77000008c1fb4d50329c770000094e306cd353607700000901b35d4d01dc51000008c1b34d4e31dc4e00000985b34d4f21dc51000008c1b34d4f61d051000008c217570d01dc5100000992536cd5c51cd00000094de2759b34d477000008c1b34d4d01d451000008c1b34d52534077000008c1b34d4f229c7700000901b34d4e31dc51000008c1b35fd032c05100000985b34d4f8340510000094de27598a4d4770000092db35d4d01dc5100000992174d4d014416000008c1d24d4d01dc1f00000002307ed7f29c77000008c20e6ccd029c77000008c1e7789b34d4770000094e306cd3d340770000092db34d4e31dc51000008c1b35490b1dc51000009c2476cd7f1dc5100000946306cd3534077000008c1c36cd7f57051000008c1b35d4d01dc5100000992476cd7f57051000008c20b6cd5c34077000008b60e6ccd01dc510000096db34d5031dc51000008c1c34d4d01d051000008c1c35714734051000008c1bb66935340770000096db3504d01dc51000008c1b34d4e31dc510000092db34d4e322c51000008c1b36a13534051000008c2224d4d02d877000008c1b3505031dc51000008c1f06cdaf4d477000008c1b35d4d022c51000008c1c86cd7f3405100000911b34d4d81dc51000008c1b34d5061dc51000008c1fb4c8d01dc51000008c1e26dd351dc51000008c1d66cd353d891000008c2046cd353e091000008c1b34d4e322c51000008c1b34d4d029c80000008ee307edd64d477000008c1b34d4f21d051000008e1b34d52134077000008c1b3548e31dc5100000985fb6cd353e051000008c1ce4c8d01dc5100000901b36693534077000008c1bf4d4d021c7700000901b35710e34051000008c1b35bd6c4d4d00000094de2759353407700000991b35193534077000008c1b34d5273405c000009163085d351dc51000008c1b34d4d829c77000008c2214c8d01dc51000008c1b35fcd029c770000096de26cd351dc51000008c1b3614d01dc51000008c1bf504d02005100000991b357121438d00000094de26cda24d4510000092db366935340770000096db34d4ee34051000008c1b3534d81dc51000008c1b35993521c77000009c1b35d4d01dc51000008c1b34d5033b851000008c1c34d4d11dc51000008c1e26cd411dc5100000992306cd3d360510000097db3558d01dc51000008c1c35fd5c34051000008c1b3504ee34051000008c1bb4d4d01f451000008edfb759351dc5100000992174d4d01dc51000008c1b35993b1dc51000009c1b34d4e31dc51000008c1b36693534077000008c1ec6cda24d451000008c1b34f4d029c770000094e0e759b33407700000949b34d4d01dc4e000009163082db34d477000008c1b14d4d01dc510000096db34d4d014435000008c1f14d4d029c77000008edb35d4d01dc510000094e0e7598a34077000008c20e835b334051000008c1b35d4df340770000094db36893534016000008c1b34d52b34077000009c1b34dcd01dc51000008c2174d4d029c77000009c1b54d4d01dc51000008c1f17ad3534051000008edb34d4e31dc51000008c1b3669353408b0000096db3528d01dc51000008b5f14d4d01dc51000008c1b34d4e337c77000008c1b36bd3534077000009920b6cd3534077000008c1b3529031dc51000008c1fb4d4942005100000a22646ed3534051000008c1b36695234077000008b6174d4d01dc51000008fdc24d4d01dc51000008c1fb5fc951dc5100000991bb4d50e34051000008c1b34d4d02d051000008c1b35713533451000008c1b34d4d81d051000008c1fb6cd7f29c77000008c1e26cd353b851000008b9b34d4d01dc510000096dc34d4d01dc51000009c1b35fcd029c77000008c2177255c3405100000949b34d4d01dc51000008c1c34d5031dc51000008c1fb5fc941dc51000008c1b34d4d020055000008e1b34f4d81dc51000008c1c3504d01dc51000008c20e6dcd01dc5100000902306cd7f57051000008c19e4d4d029c7700000a62304d4d01dc51000008c1b34d4cd1dc5c000008c1b34d521340b00000093db34d4e71dc51000008c1bb4d4d021c77000008c1c35fd4a1dc510000092dce4d4e31dc51000008edb34d4d21dc51000009c1b36693534077000008c1bf4d52734051000008c1b35fd5c4d45c0000094dbb6293534077000008c1e24d4ac1dc5100000992307093534051000008e1b34d4d01dc5c000008c1ce5d4d01dc51000009edb35b135340770000096db34d4f21dc51000009e6536ccd01dc51000008e1b34d4d02c051000008c1fa4d4cd1dc51000008c1d66893534051000008c1b3504d024051000008c1e26cd4a1dc51000008c22275941340770000096e0e6ccd01dc51000008c1b3528ee3405100000992536cd3534017000008c1ce4d4e31dc51000008edb36693534077000008c1b35993549c510000094e0e6cda234051000008c1b3504f21dc5100000992536cd3534035000009c1b36bd3534077000008c20e6cd031dc510000094dec6cd351dc51000008c1e86cd351dc51000008c1f96c1351dc51000008c2226ccd02dc5100000901b34d4d021c770000093dd24d4d01dc51000008c1e270d351dc5100000a227b7ed7f1dc51000008c1b35d47714439000008c22970d5c34051000009e9b34d4d029c77000008c1c34d4ee34051000009ee406cd7f1dc51000008c2206cda234051000008c1ce4d4e322c510000096db3548f21dc51000008c1f74d4771441f000008c1b357127484d000000901c3528d01dc51000008c1fb5fcd029c7700000a22307ed411dc510000092db34d4d021c7700000901b3571353405c000008c1f179d3534077000008c1b3558d01442c000008c1b34d4f734051000008c2178353534051000008c2227595c34091000009c1fb5fc941dc510000094dd6645353407700000992536cd3534048000008c1c35fd471dc510000096db34d4d020051000008c1b34d4d021c770000094dde759353407700000819b34d4ee34051000008c1b34d4f23b851000009e6307adb334051000008c1b34d50320051000008c20e789b31dc51000009e62d6ccd01dc51000008c1c3528d01dc51000008c1b3504d02005100000992536cd3536016000008c1b3571353408f000008c20e6ccee34051000008c1b3571353405c000008c20d82db34d4d00000099217725353405100000992306cd5c484d0000008c1b368975340510000094dd667935340770000096db34d4d81dc51000008c1ce6693534077000008c1b34d4d022c870000093db34f4d01dc51000008c1ec4d4941dc51000008c1b34d4cf1dc51000008c1bf4d52134077000008c1f96cd351dc51000009c1fb4d4771441f000008c1fb6bd3534077000008c1b35fce929c77000008c1bb4d52734051000008c1b35b1664d477000008c1b36893538c51000008c1b3548d021c77000008c1b3504d81dc5100000991b34c8d01dc51000008c1b35fcd02d87700000a1db34d4d02c051000009923071d3534051000008c2267594134077000008c1bb558d01dc5100000992536cd3d34016000008e1bf4d4d01dc51000008c1b34d4d02c05c000008c1b35fca11dc51000008c1b359935484770000091630759351dc51000008c1b3528f21dc51000008c20e340ac1dc510000096db34f4d01dc51000008c1b35c93534051000008c1fb6cd353dc510000096df14d4d01dc51000008c1b35fd5c14433000008c1b34c8d029c77000008c1d67213534051000008c1b34f5031dc51000008c222570d02d877000008c1b34d4e833477000008c1f14d5031dc51000008c1e26cd352005100000991b35712134051000008e1b3599351dc510000096e174d4d01dc51000008c1f1504d01dc510000094e206ccd01dc51000008c1c34d4f21dc5100000901b34d52734051000009c1b34d4d021c77000008c2174d5031dc51000008c2136ccd01dc51000008edb34d4f734051000008c217504d01dc5100000992306ed3534051000008c2146ccd01dc51000008c20e70cd01dc51000008c1fb6cd4120051000008c1b35bd664d451000009924a6cd353605100000991b35995c43851000008c1b34d4f737cd000000991b34d527484d00000094de9789b34d4770000092db34d52734051000008c1b34d4ee36051000008c1b3438d02dc51000008edb34d4d021c770000091e306cd7f29c7700000991b35895c34051000009c1b35fd031dc51000008d1e26cd351dc51000009ea22758d01dc51000008edb3504d02005100000992306cd353404e000008c1b36899a4d4d0000008c1eb7593534051000008c1b34d52734051000008c1b3528d020051000009e63079db334077000008b5d64d4d01dc51000008c1e26cd3d1dc51000008fdb34d4d01dc51000008c1fb759351dc1f00000992536cd3536077000008c20e6ccf21dc51000008c1b3558d01dc51000008c1b34f4ee34051000008c1f1789351dc51000008c217570d024451000008c1f14d4ee340510000099217570d01dc51000008c1b35714f3405c00000941b34d4d01dc51000008c217789351dc51000008c1bb4d52134077000008c1c34d4d020051000008c2174d4ee34051000008c1b3528d81dc51000008c1d66cd353dcd0000008c1b3549273405100000992536cd3d34077000008e1bb4d4d01dc51000008c1bf4d4d01dc5c000008c1d3504d01dc51000008c1b34d4d81c451000008c1bf4d4d02c051000008c1b34d4d01dc4f000008c1c34d4d81dc51000008c1b35e8f734051000008c1b3571353a0d0000008c2227593534080000008c1f1528d01dc51000008c1ce4d4d021c77000008c1b3599351dc5c00000901b34d52134077000008c1b34d4f22005100000901b34d4cd1dc51000008c1b3599352c051000008c1d66cd4134080000008c1d24d4e71dc5100000919b34d4cd1dc51000008c1b35d4d029c770000094db3689474d4d0000008c217528d01dc51000008c1b34f4d01c451000008c20e6ccd02005100000901b35fd5c4d451000009c1b34d52734051000008c1c34f4d01dc51000009d9b34d4d01dc51000008fdfb6cd351dc510000092db34d5213407700000a1a305d4d01dc51000008c1fb759351dc25000008c1b34d4f73a451000008c1b34d4e329c77000008c1c75713534051000009462d6cd3534077000008c1b35b13534077000008b5b35d4d01dc51000008c1fb5fcac1dc51000008edb34d4d01dc4800000a22307ed352005100000941fb6cd351dc51000008c1da4d4d01dc5100000901b35fd351dc5c000008c20e6ccd81dc51000008c1b34dcd029c77000008edb34d527340510000096dec6cd351dc51000008c1b34d52134077000008c1b34d4cd1dc51000008c1b54d4d029c77000008c20d7593534051000008c1b34d52737cd0000008edfb759351dc1f000008c1c74d4d01dc5c00000779b34d52134077000009e2707ed351dc51000008d20e6ccd01dc51000008c1b34f4f21dc51000008c1b35995c49c51000008c1f14d4ee37cd0000008e1b34d4d01dc51000008c1b35713539c91000008c1f14d4f21dc51000008c1bb4f4d81dc51000008c1b34d5213408b000008c1b34f4e71dc51000008c1b35c1351dc51000008c20e7c4d01dc51000008c2174d4f21dc51000008c1b35fd3523c77000008c1fb759351dc28000008c1b35fd351dc5c000008c1b35d1351dc51000008fdb3514d01dc51000008c1b35492134077000008c1b35bd353405100000991b35710e34051000008c217838d01dc51000008e1b34d4d022c510000094e30759a24d4d00000094dd66a93534077000009e630789b31dc5100000992536cd353e0e9000008c1bb4d4d01dc5c000008c1c86cdaf4d4d0000008c1fb4d50c2c051000008c1b36893534087000008c1bb4d4d02c051000000026494db34d4d8000008c1b34d4d820051000008e1b3548d01dc5100000a1db04d4d01dc510000095db34d4d01dc51000000026485d5c34051000008c20e789b368851000008c1b04d4d02c051000008c1d257135340910000097dbb4d4d01dc5100000901b3571353405100000992306cd6657051000008fdd66cd353407700000919b35713534051000008c1d24f4d01dc51000009ee30884d01dc51000008c1bf599351dc510000094e476ed3534077000008c1ce4d52734051000008c1b3568d01dc51000008c1b34d4c51dc5c000009c1b34d52134077000008c20e82db3340770000094de26cd351dc16000000026494db34f4d000000992306cd4534051000008c1b34f4d02005100000991b357135484d000000941d66cd3534077000008c1f14d4d02005100000901b34d4d01dc5c000008c1b35e8771442c000008c1b35fd46340770000094dd6689353405100000992536cd353406c00000901b34d4d02c05100000a0a406cd7f1dc5100000919b34d4d01dc5c000008c1d34d4d024051000008c2174d4d020051000008c1d6689353401f00000991b34d51734051000008edb34d52134077000008edb34d4cd1dc51000008c1b34f4d81dc51000008c1c34d4d01e051000008c1b34d4df334770000092db34d4d01dc5c0000092db34d4d02c051000008c1f14d4d81dc51000009c1b35d1351dc51000008c1b35fd5134051000008c1fb5fca725077000008c1b35995c484770000096e206ccd01dc51000008c2174d4d81dc51000008e1b34d4df3407700000a1db34d4d01dc51000008c1b34d4d023c77000008c1b34d4d01dc5c000008c1b35711b34051000008c1b3545464d4d0000008c1b34d4d02c051000008c217519353407700000a22307b1351dc5100000991b35993549c51000008c217340a31dc51000008c1f14f4d01dc5100000a6e306ccd01dc51000008c1b35f4cd1dc51000008c1b34d50b2d877000008c1b3571213402c0000097db34d4d01dc51000008c1b35fd5c32451000008c1fa4d4d01dc51000008c2174f4d01dc51000008c1b35fd4f1dc5c000008c1b34d4d022c5c000008c1e2759351dc5100000a1db3548d01dc51000008c2175453534051000008c1b3548d01dc5c0000094e0e789b31dc51000008c1fb4d4a71dc1f000008c1b3548d02c051000008c1d66cd35334770000096db35d4d01dc51000008c1fb759411dc51000008c1ce4d52134077000008c1b35fd5c1702c000008c1b35d5031dc51000008c1bb599351dc510000096db34d4e31dc51000008c1b35fd353a077000008c2214d5213407700000992538c1bb4d4d0000008e1ce4d4d01dc51000008c1fb5fd352c051000008c1c24d4d01dc51000008c1b3504e31dc510000094e0e6ccd01dc1600000901bf4d4d01dc51000008c21782d3534077000008c1b35f9321dc51000009c1b34d4d01dc5c000008c1e17593534077000009c1b34d4d02c051000008c1d44d4d01dc4e00000992176cd5c34051000008c5b34d52134077000008c1c75fd351dc51000008c1b3504c91dc51000008c1b3564d023c770000092dbf4d4d01dc51000009e9b35fcd01dc5100000901b3599351dc51000008c1b34d4d81dc4b000008edb34d4d01dc5c000008edb34d4d02c05100000992536cd3534019000008c1b356d35340510000094e306cd5634077000008c1fb7353520051000008c1b34d4df340b000000992536ed3534051000008c1e26cd751dc5100000991b3599354847700000901b34d4e834077000008c1bf4d4d01dc510000092db3599351dc5100000992306cd353e0e8000008c1b35d4ee34051000008c1b35fd0329c7700000992476cd353605100000a2230880d01dc51000008c1b3504d21dc51000008c1b34d4ee38c510000094e386ed3534077000008c1b3599351dc510000096db36693534077000008c1d44d4d01dc51000008c1bf4d4d022c51000008c1b368935484d00000094db36899a4d4d0000008c22270d5c34051000008c1b36693540c77000008c1b35b15c34077000008c20e758d01dc5100000992476cd3d34051000008c1bf548d01dc51000008c1b36694134077000008c1f75713534051000008c1b34d4e83407700000a1dfb4d4d01dc51000009e6307c4d01dc51000008e1b36893534051000008c1b34d4d021c74000008c1b35712134077000008c1b35993522c51000008c1fb4d4d02c05100000992536cd35360d0000009c2307ed7f1dc5100000991b34d52134016000008c1b3599521dc5100000901b35fd351dc51000008c1b3528e31dc5100000919b35fd351dc51000008c1ce4d4d01dc5c000008c1b3538d01dc5c0000094e306cd353dce9000008c1ce4d4d02c051000008c1b34d4fd1dc51000008c1c35fc941dc51000008c1c74d4d01dc51000008c1b35fd5c3a491000008c1b3558d02445100000901bb4d4d01dc51000008c1c35d4d01dc51000009c1bf4d4d01dc51000008c1aa4d4f21dc5100000a227b888d01dc51000008c1b35fd5c1dc5c000008c1b35d15c1dc51000008c1cc5713534051000008c1b34d527340a7000008c1c34d4e31dc51000008c1d673535340800000092dbb4d4d01dc51000008c1b35193234077000008c1c2514d01dc51000008c1e26cd9a4d477000008c1b34d52c484d0000008c1b34d4fc34051000008c1f06cd351dc51000008c1b3669353b8d0000008edbf4d4d01dc51000009c1b3599351dc5100000991b35995c4d451000008c1b34d4e7244770000098db34d4d01dc51000008c1bf4d4df34077000008c1b35d4ee37cd0000008c1cc4d4d01dc5c00000a22647ed353e0510000094db3689353a4d0000008c1bb4d4d01dc51000008c1b35d4f21dc51000006cda25893534051000008c1b369d3534077000008c1b34d4d02dc51000008c1b34d50a34051000008c1b34d4e324051000008c2174c8d01dc51000008c1b04d4d01dc51000008edb3599351dc510000099253759c94d4d0000009c1fb4d4d02c05100000991b35711434051000008c1b35993537c77000008c1bb4d4d022c51000008c20e6cce31dc51000008c1b34d4d01dc4e000008c1b35b4941dc51000008c1b36694a3407700000992306cd4d34051000008c1bb548d01dc51000008c1d24d4d02447700000901b34d4d01dc5100000991b35b13534077000008c1b3689353405c00000981b34d4d01dc5100000919b34d4d01dc51000008c1b0548d01dc51000008c1b34d4d81dc57000008c1b34d4d022c4e0000094de26cd474d477000008c1c36693534077000008c1fb7593520051000008c1c35710e34051000009ee536ed3534077000008c1fb759414d477000008c1b35995c1442c00000991b34d521340770000092db34d4d01dc51000009c1f06cd351dc51000008edfb6fd351dc51000008c2174d527484d0000008c1b35d4d0200510000096db34d4d021c7700000901b34d4d022c51000008c1e2759a24d451000008c1b34d5082dc51000008c1b35fd353a490000008c1b34d50321c7700000a1a305b13534077000009d5b34d4d01dc51000009c1bb4d4d01dc5100000901b3548d01dc51000008c1b34d4e3200510000094e306cd3d36077000008c1b3504d021c77000008c1b34d4d01dc51000008c1b34f4d01dc570000092db34d4d022c5100000992386cd3536051000009c1b04d4d01dc51000008c1ce599351dc51000008c1b35d4d81dc51000008c1b34ccd01dc5100000991b35d1351dc51000009ee53884d01dc51000008c1b3669353c87700000901b35fd5c1442c0000092db3548d01dc51000008e1b34d4d029c77000008c1b34d4c920051000008edbb4d4d01dc510000096db3548d021c77000008c1f74d4e834077000008c1fb6cd351dc4e000008c20e6cd9a3407700000992174d4f834051000008c1bb4d4df34077000008c1b34d4d022c51000009e9b34c8d01dc51000008c1c96cd5c484d000000002306cd7f5705c00000992386cd3d34051000008c1b3548d01dc5100000919fb6cd351dc51000008c1f15d4d01dc51000008c5b3599351dc51000008c1d66cd563409100000a1a305bd35340510000094e30789d64d477000008c20e6cdaf34077000008edfb725351dc51000008c1b35fd5c1442c00000a21ea4d4d01dc51000008c1e26cd3521c77000008c1b34f4e31dc51000008c1fb6a97f1dc51000008c1b34b8e31dc51000008c1b34d4d220051000008c2175d4d01dc51000008c1b34d4ee34087000008c1f14d4e31dc5100000a667b888d01dc51000008c1d56c13534077000008c1b3548d022c5100000911b35713534051000008c2166ccd01dc5100000901b34d4df3407700000a2e646ed3534051000008c2174d4e31dc51000008c1b34d5081dc51000008c1b35955c34051000008c1bf6893534051000008edd66fd3534077000008c1b36693534080000009c1b34d4d01dc51000008c1b35fcb01442c000008c1fb4d4d02dc51000008c1f75fd351dc51000008c1b3514d01dc4e000008c1b34d4f621c770000092db34d4df34077000008c1b34d4e93409000000911b34d4d01dc5c00000985b357135340510000094e307093534077000008c1fb4d4a61dc510000094e15839b3340770000094de2759351dc51000008c1b3564d01dc510000094e0e6cd47340770000098a306cd3534051000008c1ce4d4d02dc51000009e630758d01dc51000008c1b3689664d451000008edb34d4d01dc510000096db34d52734051000008c1e2759351dc1f000008c1b36693536077000009c1b34d4d022c51000008c1b3528d021c77000008c1b34d4df34077000008c1b34d52740c5100000985b34d4d023c7700000a22647b1351dc51000008c20e759a23405100000a7a889ecd01dc51000009c1b3548d01dc51000008c1b35052734051000008c1ec759351dc51000008c1b3474d02c051000008c1b35995c1dc51000008c1b35714a3405c000008c1fb759411dc1f000008edb34d4d022c5100000a323b7ed351dc51000008c1b35f0e834077000008c1c34d4d021c77000008c1ee6cd3534077000008c1b34d4d02c0a7000008c1cc5fd351dc51000008c1d56cd3534077000008c1b34d4df3408b000008c1b36bd7f3407700000991b35993514416000008c1b36693d34077000008c1b34d4f83a491000009ee3070d7f1dc5100000919d66cd3534077000008c1b3514d01dc51000008c1b3534d01dc5c00000941b3504d01dc5100000901f74d4d01dc5100000992307dd353e051000008edb3548d01dc51000008c1f16693534077000008c1b34d4d01d85100000901ce4d4d01dc51000008c1d34d4e31dc510000091e307ed352c051000009c1fb5fd351dc51000008c1b3548df3407700000919b3538d01dc51000008c1b35f4d01dc51000008c1c3571353405c000008edd67253534077000008c1b3568d01d051000008c2176693534077000008c1f15d4df34077000008c1fb759351dc4b000008c2207b1b31dc51000008c21e4d4d01dc5100000991c96cd35484d00000092dce4d4d01dc5100000901b35fd5c1dc510000094e067593534077000008c1e26cda266935000008c1b34d4f221c770000092e214d4d01dc51000008c1f64d4f734051000008c1e26cd3549c5100000a1a7b4d4d01dc510000094e30839d634077000008edfb6cd351dc51000008c1f74d4d01dc51000008c20e6ccd021c77000008c1b34d4d81f451000008c1ce4d4d01dc51000008c1b3538d01dc510000092dce4d4d022c51000009c1b34d4df34077000008c1b35e8d01dc51000000023b7edd64d477000008c1bb6893534051000008c1b369da24d4d000000919cc4d4d01dc51000009edb35fd6c34077000008c2214d4d01dc51000008c1b34d4d023c74000008c1b06893534051000008c1b34d4d01d05c000008c1b3571473405c000008c1b3548f221c77000008c1ce4d4d022c510000096db34d521340770000094e3071d3534077000008edb34d4df34077000009c1b34d4d02c0a7000009ee306cd6d1dc51000008c1fb6cd451dc51000008c1b34f4d01f451000008c1b3558f61dc51000008c1b34d52140c77000008c1ce548d01dc510000094e0e758d01dc51000008c1b3505213407700000a22646cd3536051000008c1b35292734051000008c1b34d52a34051000008c1cc4d4d01dc5100000991b34d50e36051000008c20e758d01dc1f00000941b34d4d01dc1600000901b36893534051000008e1b34d5031dc51000008c1b34d4d021c80000008c1d66a5a24d4d000000a2264880d01dc51000008e1b3504d01dc51000009c1fb4d4d01dc5100000901b35f0d01dc51000008c220758d01dc51000008c1bf4d4d029c7700000991b3599351dc51000008c1c34d5273405100000a22648895c3405100000a21eb6cd35340510000092db368935340510000094e306ed3534077000008c2175993549c51000008c1ce4d5081dc5100000a22646cd3d3405100000992306cd353d851000007adb34d50e340510000094e4a6cd3536077000008c1fb6cd4e1dc5100000991b34f50e34051000009c1ce4d4d01dc51000008c1b34d4d821c77000008c1b34d50734077000008c1fb6cd7a1dc51000008c1b35712134091000008c1b35993529c77000008c1fb5fca71dc5100000991b357121340770000094db36293536077000008c1b36893534051000008edd66cd3534077000009edb35acd01dc5100000911c74d4d01dc51000008c1b34d4d11dc5c000008c1e26cd35484770000094de26cd9a4d477000008c1fb759353147700000a1a30599351dc51000008edd66293534077000008c1b35fd5c3405c000008c1b34d5213b8d0000008c1b34d4ee334510000094df06cd351dc51000008edce4d4d01dc51000008c1b35f0d01dc51000008c1b34d5273c851000008b5b3599351dc51000008c1ce4d4df34077000008edb35e8d01dc51000008c1b34f4d021c77000008c1fb4d4d02c0a7000008e1e26cd351dc51000008c20e6cda2668d0000008c1b35e8df34077000008c1f14d4d021c77000008c20e6cd273405100000941b34d4d024051000008c1d66553534077000008e1b34d4ee34051000008c1f0721b34d451000008c1b34d4f83a0770000094db36293d34077000008c1c96cd665705100000911b35fd351dc5100000002406cd7f57051000008c2174d4d021c77000008c1d66cd45340770000094db04d4d01dc51000008c1b36895234051000008c1fb4d4f82c051000008c21f85d5c3405100000985b34d4d0144160000092db34d52c34051000008c2174ecd01dc51000008c1c7534d01dc51000008c1c86c13534051000008c1b35292134077000008c1b35b5354847700000985b35fd351dc51000009e2706cd7f1dc510000096db34d4d01dc5c00000a1e224d4d01dc510000096db34d4d02c051000008c1b34d52c34051000008c1b34d4d02004800000992306ed3536051000008e1b3528d01dc51000008c1b34d5031dc5c000008edfb759b34d477000008c1b34d5032c05100000992306cd3539c5100000a1db34d4d02d877000009c1b36893534051000008c1c34d52134077000008c1d66cd4e34077000008c1b3504d01dc5c000008c1b3504d02c051000008c1bb4d4d029c77000008c1b34d4d02d8b0000008c2175993548477000008c1b34d4d02dca7000008c1d6689474d4d0000008fdb34d4d020051000008c1d66cd7a34077000008c1fb759352001f0000094de26cd353a477000008c1c35fd5c4d451000008c1b35fd4a1dc5c000008e1c34d4d01dc51000008edb3689353405100000992306ed3d34051000008c1b34d52736051000008c1b36893537cd0
  | 6 => 0x2306f9b34d4d01dc51002706cd35340b02505100230731b34d4d01dc51002948c1b3548d01dc51002306cd9a4d4d01dc1000000916306cd351dc5100238889b34d4d01dc510025b6cd353407714416002568c1b34d4d01dc51002306cd353e0d01dc5c0023073935340b91dc51002306cd7537cd01dc51002306cd353407714408002306cd353e0d02c051002306cd354c8d01dc51002306cd6f5893534051002306cda26893534051002306cd3540c7714416002338c1b34d4d01dc51002707edb34d4d01dc51000008c1c86cd3534051002888c1b34d5273405100000911b34d4d01dc51002718c1b34d4d01dc510023070d7f4d4771442c002306cd413407714416002306cd353408014428002307edd651d3534077002538c9b34d4d01dc51002306cd3549d0e34051002306cd35400df34077002538c1b351d3534077002306cdaf4d4d01dc51002307495c4d4d01dc51002538c1bb6cd3534077002306cd353a4c51dc5100230841b34d4d01dc5100230739353407714407002306cd353c8d021c7700230835b34d4d01dc51002307edb3564d01dc5100230759b34d4d01dc57002306cd5c4d4d020051002306fd35340941dc51002307a9b34d4d01dc51002648c22b6cd35340510025b8c1b34d4f21dc51002306cda25fd35340510023b7edb34d4d01dc51002306cd35340971dc51002306cd35340a71dc00002307ed7f4d4991dc51002466cd3534077144390025b6cd353407714404002406cd353a4d01dc5100230789b34d4771442c002306cd35340771605100230759aa4d4d01dc51000008c2174d52734051002306cd6d4d51d1dc51002306cd352e47714439002648c1b34d4f83a45100230789b34d477144010023073935340d01dc5100000985b34d4d01dc51002306cd353c0d01dc51002307edb34d4df3407700000992306cd3536051002306cd353b8d01442c002306cd353607714428002306cd56340771b051002306cd353b8d014401002306cdb36893534051002306cd3540c77144040027b8c1b34d52134077002406cd4a340771442c00230759b34d4d024477002306cd413407714404002306cda26293534051000008c1b34d4d029c77002478c1b35fd351dc51002306cd664d4941dc510024b6cd353a4d01dc51002306fd353407718451002306cd5c4d4d81dc51002306cd353407717851002648c9b34d4d01dc51002306cd7f570d01dc5100230759b34d4d02001f002648c1b34d4d01e051002307598a4d4d0244770023073935340911dc51002306cd4e340911dc5100253839b34d4d01dc51000008c1b3534d01dc51002306cd353407b1dc51002306cd964d4d01dc5100000a1a304d4d01dc510027b8e1b34d4d01dc51002478c1bb4d4d01dc51000008c1eb6cd35340510023077db34d4d01dc5100230759b35d4d01dc51002306cd35340771443900230789b34d47714416000008c1c35713534051000008c1b3528d01dc5c00000992306cd3d34051002306cd974d4d01dc510024070d35340771442c002306cd7f51c771442c00230775b34d4d01dc51000008b5b34d4d01dc5100230709353e0d01dc51002306cd353b8d014416002307598d4d4d01dc51002306cd353a4d01dc51002306cd664d47718451002307ed35340b025051000008c1bf504d01dc5100230881b34d4d01dc5100230759b34d4e31dc51002306cd7f340b01dc51002648c1b34d4d01b051002306cd35498d01dc51002306cd353407716451002306cd5c4d4d014430002306cd5c4f4d01dc5100230725b34d4d029c77002306cd35384d01dc51002306cd5c4b8d01dc510023071d35340771443500230759b34d4d01dc52002306cd4a340771442c002306cd4a3407714401002307c55c4d4d01dc51002648c1ec6cd351dc51002536cd8e4d4d01dc51002306cd35425031dc510029e9ee306ccd01dc51000008c1c34d4d01dc5c002698c1b34d4d020051002306cda24d4d02e451002306cd5c4d8d01dc51002478c1fb725351dc51002308c1b34d4d021c77002306cd353a4d022c510023085d5c4d4d01dc51002646cd664d4d01dc510023080db34d4e31dc51002538c1b34c8d01dc5100230759b54d4d01dc510026494db34d4d01dc1600230789b34d477144040023073135340911dc5100247901b34d4d01dc51002306cd35444d01dc51002306cd353b8d01440400230829b34d4d01dc510023070d35340771442c000008e1b34d4d81dc51002306cd6e4d521340770023070d353407714401002306cd523a4d01dc51002307edce4d4d01dc510025b6cd35340771dc5100230889b34d4d01dc5c002306cd35358d01dc51002306cd484d4d01dc51002306cda24d4d014407002536cda24d4d01dc51002888c1b34d52134077002306cda44d4d01dc51002306cd7f4d4771443500230889b34d4d02c051002306fd353e0d01dc51002306cd3540c771dc51002306cd4a3407714416002306cd354850e34077002306cd474d4d029c77002538c1b34f53534077002306cd35340af1dc510024b91db34d4d01dc51000008c1b34d4d01d051002306cd35340a71dc02002306cd41340771dc51002306cda24d4d034051000009c1b34d4d029c77002306cd353407715851002307ed35340991dc51002307edb35fd5c1dc5100230739ce4d4d01dc510027b94db34d4e9340770027b6cd624d4d01dc51002306cd35340771443f002306cd754d4d01dc51002888e1b34d4d01dc51002306cd353407114416002386cd35438d01dc51002306cd664d4f81dc51000008c2174d52134077002306ed35340941dc51000008e1b34f4d01dc51002307edb34d477144390023070d353407714416002306cd5e4d4d01dc51002478c1b34d4d01dc51002306cd35340871dc51002306cd354d4e31dc5100230771b34d4d01dc5c00230759b35714734077002306cda24d4d024451002306cd353c8771442c002888c1b35d1351dc51002306cd353c87714401002706cd353a4d01dc51002306cd7f4d4771c451002908c1b3599351dc51002306cd4a3407714404002306cd714d4d01dc51002306cd35340871dc10002306cd5c4e4d01dc51002536cd8a4d4d01dc5100230725b3571473405100230839b3340771442c00230759b36693534077002306cd41504d01dc5100230839b33407714401002306cd374d4d01dc51002418c1b34d4d01dc510026e8c1b34d4cd1dc51002306cd5c4d4d017051002306ed353407718451002306fd35340801dc51002307599a6293534077002306cd4a340771442e0000094dd6629353407700230869b34d4d01dc51002478c1b34d4d022c51000008c20d6cd3534051002307b5e26cd351dc510027b8c1b34d4d01dc5c0023b6cd353a4d01dc51002306cd3534077144270023087db34d527340510024b6cd3538c771443d0023070d3534077144040027b8c1b34d4d02c05100230789b34d4771dc51000008c1e76cd3534077002306cd353a4df34077002478c1b3548d01dc51002306cd52340871dc51002406cd35340941dc51002306cd353c87714416002306cd353b8d01dc51002306cd75340771443d002306cd35340771705c00264969b34d4d01dc51002306ed3536077144160023085db34d52734051002307c9b34d4d01dc51002306cd35340b829c7700230839b334077144160024d8c1b34d4d01dc51002306cd664d5211dc51002306cd9f4d4d01dc510026494db34d4f834051002306cd353407a1dc51002306cd354b4d01dc51002306cd7f4d4d029c77002306cd3538c771443d0024b6cd35340941dc5100230861b34d4d01dc51002307edb36893534051002306cd35340951dc51002306cd353407714417002306cd3540cd02c051002406cd353407718451002646cd354b8d01dc51002306cdb34d4d029c77002307edd64d4d0244770025e8c1b34d4d01dc51000008c1fb4d4d029c77002868c17f4d4d01dc51002306cd353407714435002648c2206ccd01dc51002306cd35480d01dc51002306cd35340a728c77002876cd35340ac1dc51002306cd8a4d4d029c77002306cd35340801442c002308c1b34d52734051002306cd804d4d01dc51002306cd353408014401002306cd353c87714404002306cd35340bb1dc510022d6cd7f4d4d01dc51002868c1b34d4d01dc51002478c1fb6cd351dc51002306cd35340b02b051002648c2226cd5c34051002306cd864d4d01dc510023f8c1b34d4d01dc510023083a066ccd01dc51002306ed3d3407714416002306cd35340941dc51002648c1b34d4d0144190027091db34d4d01dc51002306cd3538c8b1443d0024b6cd353407718451002306cd75340771440b002306cd9a4d535340770023070db3571353405100230839b33407714404000008c1b35fcd02c051002538c1b35d4d01dc5100230889bf4d4d01dc510026491db35713534051002306ed353e0d01dc510000093db34d4d01dc51002307eddd4d4d01dc510025b6cd35340871dc61002306cd4a340771dc5100230725b35fd5c34051002306cd5c43cd01dc51002306cd66589351dc51002508c1b34d4d01dc510027e8e1b34d4d01dc51002306fdb3504d01dc51002306cd474d4d01dc5500230759b34d4d01dc39002306cd35340a726077002306cd3538c771440b002306cd754d4df34077002306cd35360771442c002306cd3536077144010027b94e226ccd01dc510025b6cd353407714400002538c1b34d4e31dc51002306cdaf6a93534077002458c1b34d4d01dc51002306cd8b4d4d01dc51002888c1b34d4d01dc5c002306cd7b4d4d01dc51002478edb34d4d01dc51002306cd353407718451002306cd353409422c51002306cd35340771c451002538c1b34d4d01dc52002888c1b34d4d02c051002306cd4e3407714439002918c1b35fd351dc5100000992536cd3534016002306cd35340801441600230889b3599351dc510023070db34d4d01dc5c002306cd3540c7714400002306cd35438d01dc5c002478c1b34d4df34077002306cd9a635353407700230739353a4d01dc51002306cd35438d02c0510023070d35340771dc51002306cd353407714448002388c1bb4d4d01dc51002306cd413407714400002306cd353e0d01dc4e0000096db34d4d01dc5100230725b74d4d01dc51002306cd52340941dc51002306cd35340b929c77002306cda26693534051002307edc94d4f81dc510000094db36893534051002306cd3549cd014451002648c1b35d4d01dc51002306cd35431031dc51002306cd35340ae1dc51002306cd3538ce31dc51002306cd35340771444a000008c1b34d5031dc510028e8c1b34d4d01dc51002848c1b34d4d01dc510026e8c1b35713534051002307edd64d4771441f002306cd904d4d01dc51002306cd353acd01dc51002306cd3d340771442c002406cd353e0d01dc51002306cd353408b18451002306cd7f570e91dc51002306cd3d3407714401002306cd3549cd01441000230719b34d4d01dc51000008c1b3504d01dc51000008c1b34d4d02d877002306cd353607714416002307c535340771442c002307c5353407714401002306cd9a4d4d01dc3d002648c1b34d4e31dc51002889edb34d4d01dc51002306cd35340a71dc07002306cd353408b14448002306cd75340771441f0025f6cd35340771b051002648c1b34d4d834051002306cd353408014404002306cd523407718451002306cd35340c11dc51002306cd35340901dc510023085d35340771442c00230759b44d4d01dc51002306cd353b4d01dc51002307ed7f4d4941dc510023085d3534077144010024b6cd353e0d01dc510027b8c1bf4d4d01dc51002968c1b34d4d01dc51002306cd353b8df340770025b725b34d4d01dc51002306cd35340d029c7700230731353407714439002306cd353c8771dc510000096db3548d01dc51002306cd3538c771441f0023085db34d52134077002306cd604d4d01dc5100230725b34d5031dc51002706cd35340941dc51002306cd353bcd01dc5100230839b3340771dc51002306cd3d340771441600230725b3504d01dc51000008c1c35fd351dc51002a48c1b34d4d01dc51002306cd353607714404002306cd5c49d0e3405100230809b34d4d01dc51002307c5353407714416002538c1b3571473407700230789b34d47714400002538c1b35fd353a477002306cd353e0d01dc51002306cd35340c31dc510025c8c1b34d4d01dc510027b8c1b3599351dc51002306cd353407717c51000008c1bf4d4d020051002306cd35340a724477002306cd35324771441f002306cd353b8d01440000230759b34d4d021c77002306cd9a4d4d01dc0b002306cd734d4d01dc51002308c1b34d52134077002306cd7f4d477144300023085d353407714416002538c1b366935340770023b6cd35340941dc51002908c1b34d4d01dc51002706cd353407718451002478c1ce4d4d01dc5100253759b36293534077000008c1e26cd351dc51002306cd353e0d31dc51002306cd353407714424002648c1b34d4d01e451002306cd3537cd025077002306cd35340811dc5100230899bf4d4d01dc510025b6cd474d4d01dc51000008c1b34d4ee34051002306cd35340771441400230705b34d4d01dc510025b6cd353407714402002306cd353e0d022c51002306cd41340771444b002388c1b34d4d01dc51002306cd3d340771440400000901b3528d01dc51002306cd474d5031dc5100230889bb4d4d01dc51002306cd353409f1dc5100230811b34d4d024477002368c1b34d4d01dc510027c8c1b34d4d01dc51002306cd353407718051002306cd3540c7714402002478c1b35fd5c1dc51002306cd59340771c451002306e1b34d4d01dc51002307c5353407714404002848c1fb6cd351dc51002918c1b34d4d01dc51000009c1b34d5031dc51002306cda24d4e934051002306cd47504d01dc510028e9c1b34d4d01dc5100230715b34d4d01dc510023b6cd353407718451002306cd523e0d01dc51000008c1fb6cd411dc51002938c1b34d4d01dc51002306cd4134077144020023085e064d4d01dc51002306cd6c4d4d01dc51002306cd35348771441f002538c1b34d4e931477002306cd35340b029c94002306cd7b4d4df34077002306cd3537cd01dc61002386cd35360d01dc510023085d353407714404002617edb34d4d01dc510023076db34d4d01dc51000008c1b34d4f61dc51002648c1b36693534077002648c1d67253534051002648c1b35710e34051002888c1bf4d4d01dc5100230789c96cd351dc51002306cd35340801dc5100230889d6340a31dc5100000901c34d4d01dc51002306cd4a3407714400002307ed35340951dc51002478c5b34d4d01dc5100230725b34d4ee34051002306fd35438d01dc51002838c1e26cd351dc51002306cd35484d01dc51002307edb34d4d029c77002306cd4a528d01dc51002306cd35340771443a000008edb3504d01dc51002306cd9a4d4d01dc1f002306cd35484d01dc10002306cd6e599351dc51000008c1b3528d01dc51002307393538c771443d000008c1b35b5351dc51002306cd5c4d50b1dc510023076db34d4d022c51002306cd354d4d021c7700240889b34d4d01dc51002306cd353407714445002307ed35340941dc51002888c1b3599351dc51002306ddb34d4d01dc51002307edeb6cd3534051002386cd353407714451002306cd35360771dc51002306cd35340771b8510023070d3534077144000027b8c1f06cd351dc51002307edb34d4f81dc510023082e066cd3534077002408c1b35713534051002306cd664d50e1dc51002706cd353e0d01dc51002306cd5c51cd0244510022d7edb34d4d01dc51002306dd8a4d4d01dc51002306cd35340aa1dc51002306cd35404d01dc5100230839e26cd351dc51002306cd353408c1dc51002386cd3534077144100023070d4a4d4d01dc51002306cd414d4d020051002306cd3b4d4d01dc510025892db34d4d01dc5100230789b351d351dc510024b889b34d4d01dc510027b8c1bb4d4d01dc51002306cd7f4d47717051000008c1c34d4d01dc510023072db34d4d01dc510023073935340941dc51002306cd35340781442c00230789b34d47714402002306cd353407714411002306cd474d4ee34051002307fdbb4d4d01dc51002538c1d66353534077002538c1b34d4e934077002658c1b34d4d01dc510025b6cd7f4d4d01dc51002306cd353b0d01dc51002306cd353b8d014402000008c217599351dc51002306cd624d4d01dc51002408c1b34d4d01dc5c002306cd3534077188510023b6cd353e0d01dc5100230725b3528d01dc510026a8c1b34d4d01dc510027b8c1b04d4d01dc51002306cd5c4850e34077002306cd353c8871dc61002306cd35490d01dc51002306cd7f4d5031dc51002306cd353407714430002306cd3d340771dc51002478c1b3689353405100230809b34d4df340770025b6cdb34d4d01dc51002306cd353e0df34077002588c1b34d4d01dc51002306cd524d4d021c77002306cd35340a41dc510027d8c1b34d4d01dc51002307c535340771dc51002306cd7f504d01dc5100230889b34d4d01dc510025b6cd8a4d4d01dc51002306cd35340bc1dc5100230701b34d4d01dc51002306cd35370d01dc51002306cd75570d01dc51002306cdb34d5031dc5100230789b3639351dc51002306cd353c8771440000230739353407718451002306cd514d4d01dc51002536cda26293534051002306cd353407712c160025391db35fd351dc51002306cd353406c1442c002306cd35378d01dc51002306cd35340911dc55002306cdb3504d01dc51002306cd8a4d5031dc510026c8c1b34d4d021c77002646cd3549d0e34051000008c1b34d4d0240510023085d35340771dc5100230759b34d527340510026494db351d3534077002306cd35340871dc3d00230839b33407714400002307edb34d4801dc5100230725c34d4d01dc51002306cd8a504d01dc51000008c1b34d4ee37cd0002306cd5c4d4e31dc51002889edfb4d4d01dc51002306cd35344d01dc51000008c1b34d4f21dc5100230759b3558d01dc51000008c1d66cd4134077002307edb34d4d01d051002306cd874d4f21dc510027b901b34d4d01dc51002306cd453e0d01dc51002306cd35340ad1dc5100230889b34d4d022c51002878c1b34d4d01dc51002306cd5234077188510023089db34d521340770026491db34d4d014416000008c1bb4d4d81dc51002308aa0e6ccd01dc51002308c1b34d4d01dc5c00230789b3689351dc51002306cd4a51cd01dc51002999edb34d4d01dc51000008c20e6ccd01dc51002306cd5d4d4d01dc51002308c1b34d4d02c051000008c1b34d4e71dc51002306cd4a3407714402002306cd353407714415002306cd35368d01dc51002306cd5c4dcd01dc51002306cd354851434077002406cd35340771705100230771b34d4d01dc5100230889b3548d01dc51002306cd35340911dc53002538c1b34d4f734051000008c1f64d4d01dc51002707ed35340941dc510023b6cd35340801dc510027b92db34d4d01dc51002306cd35460d01dc510023070db35fd351dc51002306cd5f4d4d01dc51002306cd7f570d0244510026491db35fd351dc51002306cd354bcd01dc510025f8c1b34d4d01dc51002306cd353d4d01dc51002306cd3534077144210025b6cd35340b91dc51002306fdb34d4d020051002888c1bb4d4d01dc51002446cd353a4d01dc510023070d474d4d01dc51002306cd35340871dc0b00230789b35fd351dc5100230725b34d4f21dc51002306cd3540cb91dc5100230865b34d4d01dc51002538c1b34d4d021c770023070d353407714402002306ed35438d01dc51000008c1b3548f21dc51002306cd7f4d4ee34051000008c1bb4f4d01dc51002306cd41340b91dc510027b8c1b34d4d01dc5100230789b36cd351dc5100230839c96ccd01dc51002306cd3549d15340510026a8c1fb6cd351dc51002307fdb34d4d01dc510025b6cd353407714407002306cd5c4d4d01e451002306cdb34d4ee3405100230739353e0d01dc51002306cd353408014400002838c20e6ccd01dc51002306ed35340771b05100230789b3629351dc51002306cda24d4d025051002306cd353408f1dc51002306cd35340bd1dc51002306cd35340901444b002306cd8a4d4ee34051002306cd3540c7714407002306cd353407717051002306cd35340771443b000008c1d24d4d01dc51002306cd3536cd01dc51002307ede76cd3534077002306cd354d52734051002306cd35340b01445100270889b34d4d01dc510025b6cd35340d01dc51002306cd413407714407002307edb84d4d01dc5100230889d651d3534077002306cd353407717010000008c1b34d4d020051002306cd564d4d01dc510027b8c1b34d4d022c51002306cd35340b014410002306cd3540cd01dc51002306cd353a4d029c77002306cd35488d01dc51002306cd7f4d4d51dc51002306cd474d4f21dc51002648c1b34d4d021c7700288901b34d4d01dc51002307edb34d4d11dc51002306cd353607714400002306cd41340d01dc51002306cd353c87714402002306cda24d4d0184510023083a0e6ccd01dc510023088db34d4d01dc51002306cd9a571353407700230759c95713534051002306cd4d3a4d01dc510024070db34d4d01dc51002406cd35438d01dc510027b8c1b3548d01dc510023b889b34d4d01dc51002308adb34d4d01dc510025b6cd35340911dc51002308560e6ccd01dc510025391db34d4d01dc51002306cd35340a11dc5100230839b351cd01dc5100230899b34d4d01dc51002306cd7f528d01dc51002306cd35468d01dc5100230839b33407714402002306cd35340ac1dc51002306cd353e0e91dc5100230889b34d4df3407700230759b34d4d020077002306cd35340871dc1f002306cd3540c911dc51002708c1b34d4d02c051002307a5b36693534077000008c1b34d4d81dc510028892db34d4d01dc51002306cd35388d01dc510023062935340ac1dc51002538c1b34d4d01dc17002646cd354850e34077002306cdb3528d01dc510023076dce4d4d01dc5100230789b34d4b91dc5100230759b34d52134077002306cd5c4d4d014433002306cd41340911dc51002306cd354c0d01dc510024b6cd35438d01dc5100230725b34d4d020051002306cd353b8d02e451002538c1b34d4d01dc35002307edb34d47714421002307edb74d4d01dc51002306cd8a528d01dc51002306cd41340801441f002306cd353407714446000008c1b35193534077002306cd3d3407714400002306cd824d4d01dc51002306cd35340781dc51002306cd6e4d4d01dc510023070d7f4d4d01dc51002307c5353407714400002306cd3549cd01443d00238759b34d4d01dc51002888c1b34d4d01dc510027b8d5b34d4d01dc5100230789b34d47714407002688c1b34d4d01dc51002306cd353407718c510023070db34d4d01dc51002306cd35438d01dc510026491db34d4d01dc5100288779b34d4d01dc51002306cd353b8d0144070027b9c1b34d4d01dc510023085d353407714400000008c1b34f4d01dc51002306cd52340ac1dc510023085db3599351dc51002308c1bf4d4d01dc5100230725b34d4d81dc510023070d8a4d4d01dc51001de6cd35438d01dc51000008c1f14d4d01dc5100230889b3570d01442c002306cd3540cb02505100230789b34d4d01dc51002858c1b34d4d01dc51000008c1b35453534051002306cd35340771b051002306cd353b8d03405100230839b3688d01dc510025b7edb34d4d01dc51002306cd5c4d4d01442d000008c2174d4d01dc51002888c1b34d4d022c51002306cd474d4d020051002306cd7f4d4d024051002306cd3549d2734051002306cd35340771a851002306cda24d4f834051002478c1b34d4d029c77000008c1fb6cd3520051002306cd3534080144020027b8edb34d4d01dc51002307edb34d5031dc51002306cd35438d022c51002306cd353a4d01d051002538c1b34d4d01dc48002308c1b3599351dc51002706cd3540cd01dc51002306cd4a340b91dc5100230819d64d4d01dc51002306cd7f4d4f21dc51002307edb3504d01dc510027b8c1b34d4df34077002888c1b3548d01dc51002306cd3549cd01440b00230789b34d4911dc51002306cd35394d01dc51002306cd424d4d01dc51002538c1b34d52734051002306cd5c4d4d01f451002306cd353b8d02445100230725b34f4d01dc51002306cd52438d01dc51000008c1e26cda24d4510025391dfb6cd351dc51002306cdb34d4f21dc5100230839b35fcd01dc51002307c5c94d4d01dc51002306cd353d8d01dc5100230889ce4d4d01dc510026e8c1b34d4d01dc51002306cd354d52134077002306cd474d4d81dc51002538c1b34d4d81dc16002306cd7f51cd01dc51002306cd8a4d4f21dc510029496db34d4d01dc51002306cd7f250771442c002306edb34d4d81dc5100230735bf4d4d01dc51002306cd353607714402002306cd35340911e851002306cd353407715c16000008edb34d4d020051002306cd4a3407714407002306cd35354d01dc51002446cd35340771443500230839b36ccd01dc510023070d35340b91dc51000009c1b35fcd01dc51002306fd353407714451002306cd75340771442c0023085dc94d4d01dc51002306cd774d4d01dc51002306cd7534077144010029c8c2226ccd01dc51000008c20b6cd353407700230839b3628d01dc51002307d9b34d4d01dc51002888c1fb5fd351dc51002386cd354d4d01dc51002306fd353407714410002306cd3540c991dc51002306cd4a340d01dc51002306cd6d4d4d01dc51002408c1b35fd351dc51002306cd3538c771442c002306cd3538c7714401002306cd35400ee34051002306cd35340a91dc51002648c1b34d52734051002648c1b362135340510023070d353407714407002889c1b34d4d01dc51002306ed353407714419002306cd664d47714451002306cd474f4d01dc510026491dfb6cd351dc51002538c1b34f4d01dc1600288991b3571353405100230759b34d4d01dc21002306edb34f4d01dc51002306cd3d3407714402002706cd35438d01dc510028d901b34d4d01dc51002307c5474d4d01dc51002306cd35340771201f002648e1b34d4d014416002306cd35340771bc51002646cd5c4d50e34051002306cd4a340911dc51002307c5353407714402002306cd35340771440f002306cd664d47714410002306cd35340a21dc51002307ede26cd351dc510023070d35340d01dc51002306cd753407714416002889ee30888d01dc510028494db34d4d01dc51002306cd3549cd01441f002536cd904d4d01dc51002306cd353b8df340b90029e8c1b34d4d01dc51002066cd35340b91dc51002306cd1d340941dc51002818c1b34d4d01dc51002307edb34d4ee34051002306cd3c4d4d01dc51002307d935340c51dc510023085d664d4d01dc510023085d474d4d01dc51002306cd353a0d01dc51002306cd353c8b91dc51000008c1d34d4d01dc510023085d353407714402002888edb34d4d01dc51002308a5b3528d01dc51002306cd4d3407714435002306cd7f4d4d02005100230749b34d4d01dc51002306cd35484d01dc3d002306cd353a4d11dc510027e8c1b34d4d01dc51002306cd35340a725077002306cd5c484d01dc51002306cd3538c77144160023b6cd35438d01dc5100230839b3340b91dc51002888c1b34d4df340770027b8c1ce4d4d01dc51002306cdb34d4d0200510023b8c1bf4d4d01dc510023070d35340911dc5100230759b34d4d01dc5c002306cd35438df34077002306cd35340771444c00230759b34d4d02c051002306cd353c87714407002478c1fb4d4941dc51002616cd35340771c451002306cd8a4d4d020051002386cd35340771443d002306cd5c4d4d021c77000008c1f14d4df340770023083db34d4d01dc51002308c1bb4d4d01dc51000008c1d66cd3534080002308a5c34d4d01dc510028d8c1b34d4d01dc51002306cd353407716c5100240901b34d4d01dc51002306cd753407714404002306cd7f4d4d81dc51002307edb35fd471dc510024a8c1b34d4d81dc51002306cd665710e1dc5100230839b33407714407002306cd35340771444d000009e9b34d4d01dc51002306cd35340a71dc61002307edb34d4d51dc510029a8c1b34d4d01dc510025f759b34d4d01dc51002306cd3549d2134077002306cd353c8d01dc51002307ed35340ac1dc5100230895b34f4d01dc51002306cdb34d4d81dc5100230889b36893534051002306ed35360d01dc510025391dd66cd3534077002306cd3547cd01dc51002306cd3538c771440400230839b3340d01dc51002306cd35484d01dc0b002307edb3528d01dc51002306cd353d0d01dc51002306cd3539cd01dc51002306cd8a4d4d81dc51002306cd7f340a31dc5100230801d64d4d01dc5100230889d64d4d024477002538c1b34d52134077002538c1b34d4cd1dc51002306cd62570d01dc51000008c1b34d50329c7700230789b3669351dc51002306cda767935340770000094de26cd351dc51002306cd353c8911dc51002306cd9a4d4d01dc2c002306cd9a4d4d01dc01002306cd5c438d01442c000009e6306ccd01dc51002306cd3d4d4d81dc51002306cd7f4f4d01dc51002306cd7f4b8d01dc51002386cd35340771440b002306cd834d4d81dc5100230889b3570d01dc51002888c1fb4d4d01dc510024b92db34d4d01dc51002307c57f4d4d01dc51002306cd35340771441900230839b3340911dc510023074d35340771444b002538e1b34d4d01dc51002346cd8a4d4d01dc51002306cd35340b9200510023087db34d4d01dc510025b6cd353a4d01dc51002408c1b34d4d01dc51002307edc34d4d01dc51002306cdb34f4d01dc51002306cd35340a01dc51002887edde4d4d01dc51002306cd523c8d01dc51000008c20e6cda234051002306cd353e0d024451002306cd7f340981dc51002306cd7f4d8d01dc51002306ed353407714451002306cd944d4d01dc51002306cda74d4d01dc51002306d9b34d4d01dc51002468c1b34d4d01dc51002306cd464d52e34077002307c5b34d4d01dc51002998c1b34d4d01dc510023085d7f4d4d01dc51002306cd8a4f4d01dc51002306cd3540ce91dc5100230725b34d4d01e051000008c1ec6cd351dc51002478c1b34d4d11dc51002307c58a4d4d01dc51002306ed353407714410002306cd354d4d01dc5c002306cd413a4d01dc51002888c1ce4d4d01dc51002648c1b34d52134077002648c1b34d4cd1dc51002306cd354d4d02c0510023085db34d4d01dc51002706cd35340a725077002306cd3534080144070024b8c1b34d4d01dc51002306cd35340c41dc510023073935438d01dc51002306cd3d4f4d01dc51002306cd9a4d4d01dc160026491dc96cd3534051002306cd353407714443002306cd35360b91dc510023085d8a4d4d01dc510025b8c1b34d4d021c77002306cd834f4d01dc51002306cd353e0d029c77002306cd914d4d01dc51002306cd35340d020051002306cd514d52e34051002306cd35484d01dc1f002306cd35340771444e002648e1b34d4d01dc510027b8c1b368935340510023085d354b8d01dc51002306cd75340771dc5100291991b34d4d01dc51002307edb34d4f21dc51002308c1b34d4d01dc51002306cd3536077144070024b8c1b34d4d022c5100230789b36898a4d451002306cd35340771441800230779b34d4d01dc51002406cd35340771445100230839fb6ccd01dc51002386cd35340771441f002306cd8c4d4d01dc51002888c5b34d4d01dc51002306cd353409120051002306cd3538c771dc510026e8c1d66cd3534077002306cd3d340b91dc51002306cd9a4d4d01dc04002306cd7f4d47714433002306cd35360d01dc51002406cd35340771441000230759b35fd4734077002307c535340b91dc51002316cd35438d01dc51000008c1b34c8d01dc5100230759bf4d4d01dc51002646cd35484d01dc51002306cd353f8f21dc510024b6cd353407714451002306cd7f4e4d01dc510023f6cd353407714428002308c1b34d4d022c51002306cd35340771703d002306cd9e4d4d01dc5100230789b34d4e91dc510023085d35340b91dc51002306cd35340b01443d0025b91db34d4d01dc510026a94db34d4d01dc510025b6cd35340871dc51002306cd5c4d52734051002306cd3d340771440700282901b34d4d01dc51002306cd353b8e934051002306f5b34d4d01dc510024b6cd353407714410002308c1b3548d01dc51002306cd35360911dc51002306cd3538c8b1dc51002307edb34d4f824451002307c5353407714407002478c1b34d5031dc51002306cda54d4d01dc510023074d7f4d4d01dc51002738c1b34d4d01dc51002306cd353fce31dc5100230735b34d4d01dc51002646cd664d50e1dc5100230759b3599351dc51002478c1b3504d01dc51002306cd3d340d01dc51002306cd353407714451002306cd35340771440a002306cd35414d01dc51002458c2226cd351dc510023085d353407714407002306cd3535cd01dc510023074db34d4d01dc51002307c535340d01dc51002308a1b34d4d01dc51002306cd353407714410002306cd353407d1441600253759b36413534077002307ed35340a725077002818c1d66cd35340770026494db34d4e934077002306cd35340791dc510023085d35340d01dc51002646cd624d4d01dc51002306cd7f51ce91dc51002888c1b36893534051002306cd35340b51dc51002307edb34d4d020051002306cd35340771700b002306cd353a4d51dc51002306cd3d340911dc51002306cd35340771a05100230839b3668d01dc51002538c1b34d4d01dc5c002306cd35340b01440b002306cd35340861dc51002648c1b34d4d0144280000094e0e6ccd01dc51002406cd353407714433002306cda24d50e34051002306cd353408b14451002538c1b34d4d02c051002358c1b34d4d01dc51000008c1b34d527484d0002307c535340911dc51002307c5b34d4df34077002828c1b34d4d01dc51002306cd7f340b025051002307ed353e0941dc51002708c1b34d4d01dc51002306cd4a3a4d01dc51002306cd353408b1441000230789b36893534051002648c1b35713534051002306cd5234077144510023085d35340911dc510026f8c1b34d4d01dc510027a6cd35340a31dc51002306cd35340871dc64002306cd5c4d4d032451002306fd354d4d01dc51002307edb34d4d81dc51002306cd754d4ee34051000008c2206ccd01dc51002306cd9a4d4d01dc77002306cd4f4d4d01dc5c00230759c94d4d01dc51002306cd523407714410002306cd5c438d01dc51002868c1624d4d01dc51002306cd35340be1dc5100230889b34d4d029c7700288991b34d4d014416002478c1e26cd351dc51002538c1b34d4f83a4770023b8c1b34d4d01dc51000008c1b34d50b1dc51002306cd35340871dc2c0027b94db34d4d01dc510023070d353a4d01dc51002306cd35340871dc010000094e306cd3536077002478c1b34d4ee34051002306cd35340771c051002646cd35438d014416002648c1b34d4d01dc5c002308c1b34d4df340770025b6cd35340941dc51002648c1b34d4d02c0510027b8c1b35fc771442c00253789b3629351dc51002306cd35340771443300230821b34d4d01dc51002306cd664d5351dc51000008c217570d01dc510024f6cd353407714448002306cd924d4d01dc510023070d4a340771442c002306cd3540c941dc510022d889b34d4d01dc51002306cd5c4d4d01702c0027b8c1c86cd3534051002307edb34f4d01dc51002306cd35340771701f002306cd41340941dc5100230839d64d4d01dc51002706cd353407714451002307c53537cd02e477002306cd35340b01441f002307edf14d4d01dc5100230839b36898a34051002998c1fb4d4d01dc510023089db34d4d01dc51002306cd7534077144000025b6cd35340771845100230759b34d4f834091002306f1b34d4d01dc5100230765b34d4d01dc51002306cd9b4d4d01dc5100230759bb4d4d01dc51002706cd3534077144100000094e306cd3d3407700230759b34d4d02dc5100230889c96cd5c34051002478c1b35fd471dc51002306cd35450d01dc51002306cd5c4d52134077002306cd35340871dc160000092db34d4e31dc510023085dfb4d4d01dc51002498c1b34d4d01dc51002306cd3540c7718451002306fd35340771443d002306cd3538c7714400002306cd353c8e91dc51002306cd353b8ee34051000008c1b35d4d01dc51002538c1b34d4d01dc6c002306cd413407718451002536cd8a4d4d01dc160023b6cd3534077144510027b8c1b3474d01dc51002478c1b3528d01dc51002306cd35340771442d002306cd3545cd01dc5100230839b33a4d01dc51002306cd3537cd01dc51002386cd5c4d4d01dc51002306cd614d4d01dc51002709c1b34d4d01dc51002307598e4d4d01dc510023b6cd3534077144100024b8c1ce4d4d01dc51000008c1b34d4e31dc51002306cd3f4d4d01dc510027b8c1b34d4d029c77002398c1b34d4d01dc51002306cd3537cd01dc10002306cd664d4771443d0025b6cd523407718451002306cd353407d1dc51002889ee224d4d01dc51002306cd35340871dc04002307c1b36a9351dc51002478c1c34d4d01dc510023b8c1fb6cd351dc5100230789b34d4941dc51002306cd35340b029c5100240759b34d4d01dc5100230781b34d4d01dc510029e91e306cd351dc51002538c1b35fd473407700230725b35d4d01dc51002306cd474d4d01dc57002308c1ce4d4d01dc51002306cd864d4ee34051002306cd353e0e924451002306fd35340771440b002306cd353b8d0250510029e8c1b3570d01dc51002306cd544d4d01dc5100230759a24d4d01dc51000008c1b34d4e322c51002538c1bf4d4d01dc51002306cd3540cd029c77002307e1b34d4d01dc5100253789b34d4d01dc51002306cda96693534077002306cd664d5271dc5100230725b34d4e31dc510024b759b34d4d01dc51002706cd3540c941dc510025b6cd353e0d01dc51002306cd60504d01dc51002306cd35340911e051002306ed354d4d01dc5100230789b34d477184510023b8edb34d4d01dc51002306cd934d4d01dc51002306cd353408014439002306cd664d4771440b002306cd3540cf81dc51002306cd353b8d018451002538c1b3599351dc51002306cd353407719851002306cd353a4d02005100288991b34d4d01dc51000008c1b35fcd029c77002306cd413e0d01dc51002307b1b34d4d01dc51002306fd35340771442200230725b54d4d01dc51002478c1b34d4f21dc51002306cd353c8871dc51002646cd35438d01dc5100230759b34d4d01dc51002306cd7551cd01dc51002318c1b34d4d01dc51002306cd3549cd01442c002307bdb34d4d01dc51002306cd753407714402002306cd3549cd0144010023088a0d6cd3534051002648c1bf4d4d01dc51002306cd354a0d01dc51002648c1bb4d4d014416002306cd9a4d4d01dc000028b8e1b34d4d01dc510023085d3549d0e34051002307598a4d4d01dc51002306cd3538c771444b002306cd694d4d01dc51002478c20e6ccd01dc51002306cd35340911b05100230739353407714451002306cd4a340941dc51002306cd353407714409002306cd353dcd01dc51002888c1b34d4d029c77002306cd353406114435002306cd9c4d4d01dc51002306cd474d4e31dc51002898c1b34d4d01dc51002306cd353a4d81dc5100230889b84d4d01dc5100000992174d4d01dc51002306cd3538c771440200253839b3628d01dc51002307393534077144100023080db34d4d01dc51002306cd35438d029c77002306fd35340771441f002708c1fb4d4d01dc51000008c1b36693534077002386cd35340771441b002307edd64d4771442300230759b34d4d022c51002306cd353407714447002306cd353b8d030451002406cd354d4d01dc51002648c1b3599351dc510028891e307ed351dc51002306cd35340871dc77002306cd474dcd01dc510023070d35340941dc51000008c1b35d4df34077002306cd844d4d01dc51002306cd4a340771845100230759b3548d01dc51002306ed35340771443d002306cd3549cd014416002306cd5c4d4e934091002306cd664d4771441f002648c1b34d4e834077002306cd41340801dc51002306cda26453534051002306cd3537cdf340770024b6cd354d4d01dc51002876cd5c4d4d01dc51002306cd353407714449002306cd3d3a4d01dc5100230789b34d4f81dc51002306cd35340961dc51002306cd5c4d4d01dc5c002306cd353a0d032477000008c1b36bd3534077002798c1fb6ccd01dc51002306cd5c4d4d02c051002307c5353a4d01dc510023085db3570d01dc51002306cd353e0ee34051002306cd354851d340770029ca21b34d4d01dc51002308c1b368935340510023b8c1d66cd3534077002306cd35454d01dc51002306cdaa4d4d01dc5100230725b366935340770027b94dd66cd353407700230725b35710e3405100230889b74d4d01dc510023070d353407718451002307ed3540c941dc510023070d35340771c451002478c1b34d4d0200510023085d353a4d01dc51002307edd65fd351dc51002306cd354d4d01dc51002306cd3549cd01440400230759b34d5081dc51002538c1b34d4d01dc19002306cd353c8941dc510027b6cd7f588d01dc51002306cd7f4d4e91dc4b002386ed353407714416002306ed35340771440b002306cd7f5d4d01dc5100270759b34d4d01dc51002306cd35340b02c051002538c1bb4d4d01dc51002406cd35340771443d002306cd35340771441a002306cda26793534051000008c1fb5fc941dc5100230839b3340941dc51002306cdb35d4d01dc51002648c1b34d4d01441600230839b36693534077002478c1b34d4d81dc510025b889b34d4d01dc51002306cd3546cd01dc51002306cd7f4d4e31dc51002306cd354d4d022c510027b8c222758d01dc51002306cda14d4d01dc51002306cd8a5d4d01dc5100230855b36693534077002306cd8d4d4d01dc51002306cd9a51d3534077002306cd884d4d01dc4e002307edbf4d4771441f0024b6cd35340771443d002306cd9a4d4d01dc02002306cd35340c61dc51002306cd353c8771845100230889b34d5031dc51002306cd353c8771c451002306cd4a3e0d01dc510023075db34d4d01dc51002306cda24d4d014451002306cdb34d4e31dc510023b759b34d4d01dc51002306cd524d4d01dc51002306cd35340921dc5100230889b3504d01dc51002808c1b34d4d01dc51002306cd354c4d01dc5100230759b34d4df34077002306cd35484d01dc2c00230709353407714428002306cd8a4d4e31dc51002478d1b34d4d01dc51002306cd35484d01dc0100230839b3340771845100230759b35853534077002306cd7f4d4c91dc51002306cda24d4d0144100000096db34d4f21dc51002307c5754d4d01dc510023085d354850e34077000008c1d66893534051002306cd35340a51dc51002306cd353e0d01c451002648c1bb4d4d01dc510026c8c1b34d4d01dc51002648c1b369d3534077002306cd7f571351442c002478c1b34f4d01dc51002406cd35340771440b002306cd3539c7714448002306cd35340771443d0026d92db34d4d01dc51002306d5b34d4d01dc510023b6fd35340771441f0024b6cd353408b1443d00253901b34d4d01dc51000008c1ce4d4e31dc51000008c1b35993549c510023070d353e0d01dc51002478c1f14d4d01dc51002488c1b34d4d01dc51002386cd35340771442c002386cd353407714401002306cdab4d4d01dc51002648c1b04d4d01dc51002306cd3542cd01dc51002308a1b3570d01dc510029e8b5b34d4d01dc51002538c1b34d4d834077002306cd353407714412002306ed35340771441f00230725b34d4d01f451002706cdaa4d4d01dc51002478c2174d4d01dc51002306cd35340b21dc51002306cd523c877184510024b6cd35340771440b002646cd5c4d51534051002306cd75340b91dc510025392db34d4d01dc51002306cd52548d01dc51002306cd353409420051002306cd35484d01dc16002306cd7f4d4771702c0026d8c1b34d4d01dc51002306cd353408b1443d002706cd354d4d01dc51002306cda26693534077002306cd7f340951dc51002306cd353407714406002306cd7f4d4d21dc51002306cd3549cd01dc51002306cd884d4d01dc5100230889b3570d024451002306cd413407714421002536cd914d4d01dc51002306cd3538cb91dc510027b96db34d4d01dc51002306cd35360771443500288991fb4d4d01dc51002306cd52340771443d002306cd75340771440700264901b34d4d01dc51002386cd353407714416002306cd35340771440b00230889e26cd351dc51002307edd64d4d01dc51000008c1b34d4f7340510027b8c1b34d5031dc51002306cd35340871dc00002538c1b34d4d01dc51002306cd594d4d01dc51002307c5353b8d01dc51002306cd353e0f21dc51002307493534077144480024b6cd3538cd01dc5100230889b34d4ee34051002306fd5c4d4d01dc51002306cd353408018451002406cd35340c91dc51002306cd35360941dc51002307edc94d4771441f00299991b34d4d01dc51002648c1b34d4f832451002306cd7f340941dc510023b6cd354d4d01dc510027b8c1b3504d01dc510026d8c1b34d4d022c5100253779b34d4d01dc5100230811c94d4d01dc51002538c2286cd3534077002307f9b34d4d01dc51002306cd9a5fd3534077002306cd353a4d01dc4b002306cd75340d01dc51002306cd3538c771440700230839b33e0d01dc51002306cd354d4df34077002406cd5c4d4d01442c00288991c96cd3534051002306cd35484d01dc04002406cd35340771441f0026485db34d4d01dc510026492db34d4d01dc51002306cd3d3407714417002306cd35340771442b000008c1b34d4d021c7700230759b34d4d02446c00230759ce4d4d01dc51002306cdb3669353407700264725b34d50e34051002448c1b34d4d01dc51002306cd353408b1440b002809c1b34d4d01dc51002306cdae4d4d01dc51002306cd4f4d4d01dc51002306cd353407714403002306cd3538cd01dc51002538c1b34d4d022c51002306cd9a6293534077002306cd66571351dc51002306cd3540d031dc51002306cd584d4d021c770029c8c1b04d4d01dc51002536cd9e4d4d01dc51000008c20e789b31dc51002306cd353607718451000008c1c3528d01dc51002307edb34d4f81c451000008c1b3504d02005100230759bf4d4d01dc1f002306cd353407714422002386cd353407714404002306cd75340911dc51002888c1fb4d4f81dc510024b6cd35340771441f002306cd52340771440b002306cd3d340941dc51000008c1b3571353405c002306cd554d4d01dc51002406cd35340771702c002706cd35340771443d00230811b35fd351dc51002538c1b3548d01dc51002648c1b34d4d01dc510023080dce4d4d01dc51002307c535340941dc51002306cd454d4d01dc510023088935340ac1dc51002306cd35340c91dc51002306cd3538c911dc51002538c1d67253534077002618c1b34d4d01dc5100230899b3504d01dc51002306cd3538cd022c5100230889b3528d01dc51002306cd5c450d01dc51002306cd35340b62b07700230725b34d4d021c770023085d35340941dc51002306cd5c4d4d01442c000008c1b3548d021c77002306cd35340771441f002307edaa4d4d01dc510029d8c1b34d4d01dc51002306cd604d4d020051002306cd353407714431002306cd353409d1dc51002306cd5c4d4d024448002308c1b34d4d029c770023b6cd35340771443d002306cd3d34077184510027b8c1e26cd351dc51002889edb35fcd01dc51002307edb3621351dc510028896db34d4d01dc51002648c1b34d4d022c51002307c5353407718451002306cd353407714413002648c2006cd35340510027b8c1b34d4ee340510026896db34d4d01dc51002306cd3537cd01dc3d000008c1b359935484770023070d353407714430002306cd3d3407714448002306cd353e0d020051002888c2224d4d01dc510025b6cd35438d01dc510028f8c1b35713534051002306cd353408d1dc51002888c1b34d5031dc51002306cd9a4d4d02e477002538d5b34d4d01dc5100230889c34d4d01dc51002648c1b3548d01dc510023085d353407718451002706cd35340771440b002306cd35340771702c002306cd35439031dc51002888c1b3504d01dc51002306cd3534077170010023d8c1b34d4d01dc51002306cd3534077144200027094db34d4d01dc51002306cd353408b1441f002306cd35340b01442c002306cd35340b014401002307edb35fc941dc51002308b5b34d4d01dc51002307adde6cd3534051002306cd35348d01dc51002306cd41438d01dc510026494db35713534051002706cd7f340941dc51002306cd7537cd02e47700230739354d4d01dc51002306cd4e4d4d01dc51002307edb35d4d01dc51002306cd3d3607714416002306cd474d4d021c77002306cd9a4d4d01dc07002306cd52340771441f002306cd35484d01dc77002306cd7a4d4d01dc51002306cd35340871dc02002306cd353e0d81dc51002306cd35340771b451002306cd4c4d4d01dc510029c8c1b34d4d01dc510023b6cd35340771440b002307edb34d4e31dc5100230759c94d4d01dc1f002306cd3548cd01dc51002536cd8a51d35340770023067935340941dc51002538edb34d4d01dc5100000992306ed3534051002306cd474ecd01dc51002306cd9a4d4d034077002306cd3537cd01dc0b002306cd35340a71dc51002538c1b34d4df3407700230771c34d4d01dc51002386cd35340771dc51002648d5b34d4d01dc5100230759b36893534051002306cd3534077170160027b8c1b3528d01dc5100230889b34d4f21dc51002306cd35340b014416002306cd35340a71dc10002306cd7f4d4e924477002306ed5c4d4d01dc510024b73935340771443d00270991b34d4d01dc5100230759a26293534051002306cd3549cd014400002306cd35340802005100230739b34d4e31dc51002388c1b34d4d81dc51002306cd353a8d01dc51002a08c1b34d4d01dc51002306cdac4d4d01dc510023088a0e6ccd01dc51002306cd3d3e0d01dc51002306cd4a3407717051002558c1b34d4d01dc51002306cd9a4d4d02447700230809f14d4d01dc51002306c15c4d4d01dc51002306cd5c438d024451002a28c1b34d4d01dc51002307c5353e0d01dc51002307edb34d4771441f002306cd6f4d4d01dc51002306cd353407714425002646cd5c438d01dc51002888c1e26cd351dc51000008c1b36899a4d4d000230811b34d4d01dc51002706cd35340771441f000008c1b34d527340510027b8c1c34d4d01dc51002888c1b34d4ee34051002306cd353407714441002708c1b34d4d029c7700230789b34d50e1dc510025391db34d4d01dc160023073935340771443d002648edb34d4d01dc510023085d353e0d01dc5100230815b34d4d01dc51000008fdb34d4d01dc51000008c1fb759351dc1f002306cd35438ee34051000008c1b3558d01dc51002306cd353407717004002306cd5c4d4d01dc4e002648c1b34d4df34077002306d1b34d4d01dc5100230789e26cd351dc51002306cd35340b0144040023070d353407717051000008c1f14d4ee34051002388c1b34f4d01dc510023078db34d4d01dc510027b94db3474d01dc51002908c2174d4d01dc5100000941b34d4d01dc510023b6cd35340771441f002306cd353407714434002406cd5c4d4d01dc51002306cd35340831dc51002306cd3537cd01dc1f002306cd4b4d4d01dc5100230739353408b1443d002938c1f14d4d01dc51002306cd7f4d4d021c77002307ed7f340941dc51002306cd84570d01dc5100230725b34d52734051002538c1d66cd3534077002646cd35450d01dc51000008e1bb4d4d01dc51002306cdb34d4d021c77002306cd3540ca7250770027b8c1b34d4f21dc510024b6cd5c4d4d01dc51002306cda24d535340510023073935340771440b002538c1d662935340770029592db34d4d01dc51002306cd7f4ecd01dc5100230889b34d4d020051002307edb36693534077002538c1ce4d4d01dc51002306cd8a4d4d021c77002306cd353d8771b051002888c1b3528d01dc51002706cd35340a71dc510028b8c1bb4d4d01dc510027b8c20e6ccd01dc51002306cd353407714428002306cd7c4d4d01dc51002538c1b35e8d01dc510023070db3528d01dc51002306cd4a438d01dc51002306cd353407719451002306cd353dcd031451002306cd353a4d01dc57002306fd35340771442c002306fd353407714401002538c2214d4d01dc5100230839e26cd8a1dc510025b6cd353c8d01dc510023085d35484d01dc51002306cd35458d01dc510023079dde6cd3534077002306cd5c4d4d01dc51002958c1b34d4d01dc5100230759b34d4d01dc2200230889b34d4d81dc51002307393538cd01dc51002306cd884d4e91dc51002307edb34d47714425002306cd664d52734051002888c1c34d4d01dc51002538c1b36113534077002306cd474d52734051002306cd3549cd014402002306cd353a4d0244770023070dc34d4d01dc51002307a5b34d4d01dc510023070d35438d01dc5100230891b34d4d01dc51002648c1f74d4d01dc51002306cd664d4771442c002306cd664d477144010023085d664d50e1dc51002648c1ce4d4d01dc51002538c5b34d4d01dc51002306cd784d4d01dc51002648c1c96cd3534051002506cd35340771444b002307dd35340c91dc51002306cd35340771442900230889b3340a31dc51002306cd35340771dc5c002306cd353407715451002306cd35484d01dc00002306cd5c4d4d022c51000008c1b35b13534077002306cd7f3a4941dc51002537598a4d4d01dc5100230759b34d4d01dc1f002306cd35340b01dc51002306fd353407714416002306cd35340b921c770024c8c1b34d4d01dc51002306cd753a4d01dc51002306cda24d4d01443d0023b7edb34d4771441f002307598a4d4d01dc1f0023b6cd353407714425002306cd814d4d01dc510023073935340771441f00230889b34f4d01dc51002306cd5c548d01dc510023079db34d4d01dc51002306cd9a6693534077000008c1b34d52134077000008c1b34d4cd1dc5100230889f14d4d01dc510024f8c1b34d4d01dc51002386cd353407714400002998c2224d4d01dc510027b8c1b34d4d020051002306cd353a4e31dc51002306cd35340771440c002888c1b34d4f21dc51002306cd35340871dc07002306cd664d47714416002688c1b34d4f21dc51002306cd353a4d01dc520023088a174d4d01dc51002406cd7f4d4771442c002306cd353407714c51002306cd35438f21dc51002788c1b34d4d01dc51002888c20e6ccd01dc51000008e1b34d4d01dc510026494e306cd3534016002306fd353407714404002648c1bb6cd3534051002307edb34d47714428002306cd35340d021c7700230849b34d4d01dc5100230839b3438d01dc51002306cd35390d01dc51002306cd674d4d01dc51002698c1b34d4d01dc510023081db34d4d01dc51002306cd664d5101dc51002307ed35340a71dc510027b8c1b34d4d81dc510028b8c1b34d4d01dc510027b8c1b35fcd01dc510025b8c1b34d4d01dc510026491db34d4f834051002306cda24d4d01440b002307fdb34d4d81dc51002728c1b34d4d01dc51002538c1b3689353405100230839e26ccd01dc51002306cd35340771443800230725b34d52134077002536cdaa4d4d01dc51000008c1b35fd351dc5c000008c1b35d1351dc5100230759b34d4d029c77002706cd5c4d4d01dc51002308c1b34d5031dc51000008c1b35bd353405100000991b35710e340510029c8c1c96cd3534051002306cd35340771a451002306cd353409121c77002306cd664d47714404002306cd7f4d52734051002308c1b3504d01dc51002306cd35340771441b0027b8d1b34d4d01dc51002306cd755d4d01dc510023088a0b6cd3534077002478c1fb759351dc5100238725b34d4d01dc51002306cd7f4d4771442c00230721b36a93534051002306cdb34d527340510025b6cd9e4d4d01dc51002478c1b35fc941dc510029ea22304d4d01dc51002306cda26698a4d4d00027b8c1b34f4d01dc510023b6cd5c4d4d01dc51002306cd8a4d52734051002307edd66cd351dc1f002478c1b35d4d01dc51002306cd3538c771443f00230759b34d4d01dc250027b8c1f14d4d01dc51002506cd7f4d4d01dc51002706cd35340b01dc51002306cd35340771c851002306ed35340771442c002306ed3534077144010025b8c1b3548d01dc510026494db34d4d01441600000901b35713534051002306cd5c4d4df34077002307c5b34d4ee34051002307edb44d4d01dc5100230889b34e4d01dc51002648c1b368935340510027b8c1b34d8d01dc51002646cd35454d01dc510024b6cd35474d01dc510026e8c1b34d4f834051002306cd664d52134077002306cd35340c01dc51002306cd7f340ac1dc51002306cd474d52134077002888c1b34d4d0200510027b8c2174d4d01dc51002307c535340bd1dc51002306cd654d4d01dc51002306cd35484d01dc02002478c1b34d4e31dc510025b6cd3534077144510024b6cd35340771444400230739353407714441002306cd35438d020051002648c1b35f0d01dc51002306cd384d4d01dc51002306cd453407714428002306cd9a4d4e934077002306cd3540c77144510025b6cd353407714410002306cda24d4d01441f0023b759b34d4d01dc1f002306cd7c340c91dc5100230795b34d4d01dc5100000901b34d4d01dc5c002386cd474d4d01dc51002306cd413407714451002538e1b34d4d01dc16002306cd35340b61dc510028d8c1c34d4d01dc51002538c1fb7593534077002a18c1b34d4d01dc51002386edb34d4d01dc51002386cd353407714402002789c1b34d4d01dc51002306cd35314771442c002306cd3540c7714410002306cd35474d01dc51002308895c340ac1dc51002307edb34d4d021c77002308c1e26cd351dc51002888c1b34d4d81dc51002306fd35340771dc51002306cd353407714444002306cd353407714426002306ed353407714416002306cd413407714410002306cd753b8d01dc51002538c1b34d52c34051002308c1b34d4ee34051002306cd354d4d029c770027b8c1fb6cd7f1dc51002306cd35438d81dc5100230789de6cd351dc51002306cd3549cd02e451000008c1b34f4d81dc51002306cd35380d01dc51002406cd35340771442c00230729b34d4d01dc51002406cd35340771440100230845b34d4d01dc51002408c1b3528d01dc51002888c1b3519353407700230759b34d4d01d051002306cd4d4d4d01dc51002306cd353407717000002306cd353c4d01dc51002708c1b34d5031dc51002306cd35340b01440000230759b34d4d01dc28002307c5353b8d02e451002306cd353f8d021c77002306cd664d4771dc51002306cd0e340a31dc51002888c222570d01dc51002307edd64d4d01dc22002306cd4a4d4d01dc5c002306cd7f570d01442d002648c1b34f535340510024b6cd35340771442c002306cd35364d01dc51002306cd3549cd014407002698edb34d4d01dc510024b6cd35340771440100000a1db34d4d01dc51000008c1b34d4d023c77002306cd35374d01dc51002888c1b34f4d01dc51000008c1b34d4d01dc5c002378c1b34d4d01dc51002306cd35430d02c051002306a9353407718451002478c1b34d4d21dc51002306fd414d4d01dc51002306ed353407714404002408c1c34d4d01dc51000008c1b34d4d02c051002306cd7f5b13534077002306cd7f4d4771442e002306cd353407719051002888c1f14d4d01dc51002306cd3d438d01dc51002306cd75340bb1dc51002306cd865d4d01dc51002306cd353c8f21dc51002306cd75340941dc51002306cd3549cd034051002888c1b35453534051002307395c4d4d01dc51002307c535438d01dc5100230725b35713534051002648c1fb7253534051002406cd353407714416002958c1ce4d4d01dc51002808c1b34d4d029c770023b8c1b3504d01dc5100230789b34d47714451002888c2174d4d01dc51002307edd64d4d01dc1f002307ed35340b01dc51002306cd35340771442c002306cd434d4d01dc510000097db34d4d01dc51002306cd7f4d52134077002306cd353407714401002306cd353b8d014451002308c1b3528d01dc510023085d35438d01dc51002306cd3538c941dc51002306cd35340911dc48002306cd35340771444000230789b34d47714410002478c1b366935340770027f8c1b34d4d01dc51002306cd35340a71dc3d000008c1e2759351dc51002306cdb34d52134077002306cd353b8d0144100024b6cd353407714416002648c1b34d4d01441d002306cd3549cd024451002306cd884d4d024451002306cd7b5d4d01dc51002306cd75340771845100230725b34d4d01dc5c002306cd8a4d521340770028f8c1b34d4d01dc51002536cd9a6293534077002386cd7f4d4d01dc510024a8e1b34d4d01dc5100230725b34d4d02c051002306cd37340941dc51002306cd353408b1442c00230759b84d4d01dc51002308c1c34d4d01dc51002306cd353408b14401002306d535340941dc51002406cd353407714404002386cdb34d4d01dc51002306cd3538c77184510026494db34d4d01dc51002306cd353407714416002386cd8a4d4d01dc5100230759b34d4d01dc53002306cd353407717451002306cd52340771442c002306cd523407714401002306cd35340771ac51002306cd353407714437002306cd7f5bd353405100230745b34d4d01dc5100230791b34d4d01dc5100230741b34d4d01dc510024b6cd353407714404002888c19e4d4d01dc51002818c1b35fcd01dc51002386cd3d4d4d01dc51002306cd35340821dc51002306cd35340a71dc0b002306cd4a340771445100230785b34d4d01dc51002306cdad4d4d01dc51002538c1b34d4d029c77002306cd35440d01dc51000008c1c24d4d01dc51002306cd474d4d01dc5c002306cd7f340a725077002306cd35398d01dc51002306cd474d4d02c051002306cd353407717002002306cd4a3407714410002306cd353408b14416002307f1b34d4d01dc510023086db34d4d01dc51002306cd35340b014402002306fdbf4d4d01dc5100230819b34d4d01dc51002306cd35484d02e477002306ed35340771dc51000009c1b34d4d02c051002306cd35340b71dc51002308c1b34d4f21dc51002306cd6b4d4d01dc51002306cd744d52e1dc51002307edb34d52734051002306cd353407714404002307edd64d4f81dc51002306cd5234077144160023070d353407714451002306cd994d4d01dc51002828c1b3528d01dc51002308c20e6ccd01dc51002538c2046cd3534077002306cd3549d0f34051002706cd35340771442c002706cd353407714401002306cd753e0d01dc51002306cd353407719c51002386cd35340b91dc51002306cd35340771442e002306fd3534077144000023070d3534077144100025391db351d3534077002306cd35484d01dc07002306cda25713534051002386cd35340771441d002306cd9a4d4d0250770027e8c1b34f4d01dc51002648c1b34d4d029c77002306cd35340770f4280027b94db34d4d01dc160029c94db34d4d01dc51002306cd353a4d021c77002306cd353408b14404002678c1b34d4d01dc51002306cd353e0e31dc51002306cd35484d034077002306cd35340cd1dc5100288992224d4d01dc51000008c1bf4d4d01dc510025b759b34d4d01dc510027b8c1b35fce91dc51000008c1b35d4ee34051002386cd3534077144070023b6cd35340771442c002306cd35350d01dc510023b6cd35340771440100230831b34d4d01dc51002536cd8a4d4e934077002306cd664d4771440000230889d64d4d01dc51002306cd523407714404001b3629624d4d01dc51002306cd35340a71dc1f002406cd35340771dc51002306cd3537cd01dc2c00230759b34d5031dc51002306cd3537cd01dc010027f8edb34d4d01dc51002306cd353b8df34051002306cd9a4d4d01dc61002888c9b34d4d01dc51002306cd353c87714451002706cd353407714416002306cd353e0c91dc5100230759b3504d01dc51002386cd35340d01dc51002306cd35424d01dc51002306cd35340841dc51002938c1b35d4d01dc51002306cd35484d024477002306cd35334911dc51002306cd353e4d01dc51000008c1b3599351dc51002306cd353c8771441000230839b334077144510024b6cd35340771dc51002a58c1b34d4d01dc51002306cd35340771442f002306cd35340b82c051002306cd644d4d01dc51002306cd7f4d4d01dc5c002308c1b34d4d02005100230839b33407714410002306cd744d4d01dc51002538c1b34d4d01dc2800230725bf4d4d01dc51002306cd9a6413534077000008c20e758d01dc51002306fd41340771441f002306cd7f4d4d02c0510023b6cd353407714416002386cd35340911dc51000008c1b34d4e8340770023088535474d01dc51002307b5b34d4d01dc51002306cdb34d4d01dc5c002306cd3537cd01dc16002306cd353407716851002307e1b34d4ee34051002306cd353e0d01e451002306cdb34d4d02c051000008c1b35712134077002306cd35340771dc51002306cd404d4d01dc51000008c1fb4d4d02c051002706cd353407714404002306cd8a4d4d01dc5c0024b6cd353408b1dc51002306cd353e0d21dc51002306cd8a4d4d02c051002307edc95713534051002306cd4a340771442d00230725b3599351dc51002308c1b34d4d81dc51002306cd3540c961dc51002306cd35340a729c7700000901b35fd351dc51002307c5f14d4d01dc51002306cd353407f1dc510025d8c1b34d4d01dc510023087e174d4d01dc51002478c1b34d4d021c77002306cd353408721c77002648c1b357147340510025b6cd354d4d01dc51000008c1c74d4d01dc5100230789d66cd351dc51002538c1b34d4d01dc550023b6cd353407714404002306cd353408b1dc51002306fd474d4d01dc510027b91e306cd7f1dc51002307edb34d52134077002306cd35360d81dc5100230801b34d4d01dc5100230759b34d4ee34051002306cd9a4d4f834077002306fd35340771440200230735b34d4d020051002306cd354d5031dc5100230789d6629351dc51002306cd3537cd01dc04002306cd353fcd01dc51002306cd75588d01dc51002348c1b34d4d01dc510028f8c1fb4d4d01dc51002306cd35340801445100000a227b888d01dc51002306cd414d4d01dc510023073935340771442c0023085e174d4d01dc5100230739353407714401002306cd52340771dc51002308c1b34f4d01dc51002928c1b34d4d01dc51002306cd353408014410002306cd444d4d01dc51002387edb34d4d01dc51002306cd684d4d01dc51000008c1e26cd9a4d47700230889b35d4d01dc51002308c1f14d4d01dc51002306cd66599351dc51002306cd35340b91dc5c002306cd6651d351dc51002306ed353407714400000008c1f06cd351dc51002306cd353408b22c51002307ed35250771441f002306cd35340b92c051002306cd664d47714402002888c1b34c8d01dc51002306cd7f570771442c0025b6cd353c87718451002538c1b34d4d01dc53002307c5de4d4d01dc5100230759b34d4f61dc51000008edbf4d4d01dc51002306cd353fcd022c510026494dd66cd353407700230811b34d4f81dc51002588c1b34d4e31dc510025b6cd524d4d01dc51002306cd3d360d01dc51002306cd353607714451002308c2174d4d01dc5100230889b34d4e31dc51002308add64d4d01dc51002306fd3534077144230028c8c1bf4d4d01dc51002306cd3549ce934051000008c1bb4d4d01dc51000008c1b369d3534077000008c1b34d4d02dc510026494dc96cd353405100230709b34d4d01dc51002306cd353607714410002306cd353407717007002307393534077144160026c96db34d4d01dc51002306cd35340b014407002306cd464d4d01dc510025b6cd35340771443d00230759b3528d01dc51000008c1b04d4d01dc51002306cd35340771541f002706cd35340771dc51002306cd35340771cc51002306cd5c4d4d024451002306cd353407714405002306cd35340771442a002306cd35340d01dc5c002306cd3540c771443d002306cd35340d02c051002538c1b34d4d01dc1b0023b8c1b34d4d020051002306cd41340771443d002306cd3d340771445100230789b34d5351dc51002708c1b35fcd01dc51002406cd353407714400002307c5353407714451002306cd354d4ee34051000008c1b34d4d01dc4e002438c1b34d4d01dc51002306cd5c474d01dc51002648c1b35fd5c34051002306cd353409421c7700230759c34d4d01dc51002306cd3d340771441000230725bb4d4d01dc51002306cda94d4d01dc51002406cd4a4d4d01dc510023b6cd35340771dc51002306fd7f4d4d01dc51002668c1b34d4d01dc51002306cd35340911dc5c00230739353407714404002307c5353407714410002306cd5c4d4d029c770023085d353407714451002306cd35340b024451002306cd353e0d01f45100000901b34d4d01dc51002306cd3537cd01dc77002306cd3542cac1dc510027b8c1b35d4d01dc5100230789d64d4d01dc510024b6cd353407714400002307edb3505351dc51002306fdb34d4d01dc51002306cd3549d21438d000000919b34d4d01dc510025b6cd35340771440b00230811b34d4d01d0510023085d3534077144100027b94db35fcd01dc510025b94db34d4d01dc510023073db34d4d01dc51002306fd8a4d4d01dc51002306cd35340871dc61002306cd3540c771440b0027b8c1b34d4e31dc5100000991b34d52134077002538c1b34d5031dc51002306cd7f599351dc51002306cd353408e1dc510000092db34d4d01dc51002306cda24d4d01442c002306cda24d4d014401002306cd41340771440b002306cd7f40c941dc51002538c1b3504d01dc51002306cd35340b029c77002306cd3534077144000000096db34d4d021c77002306cd7f570771442e002306cdb3599351dc51002306cd353e0e9244770023b6cd414d4d01dc51002478c1b34d5273405100230759b34d4f21dc51002306ed474d4d01dc510027b8c1b34dcd01dc51002538c1bb4d4d01dc16002308b1b34d4d01dc5100230889b36693534077002306edbb4d4d01dc51002306ed353407714402002998c1b351d3534077002306cd4a4d4d01dc51002306cd354b11d34051002306cd8a599351dc510023082db34d4d01dc5100240725b34d4d01dc5100230789b34d4771443d002306cd714d52734051002306cd35410d01dc51002306cd35430d01dc51002308a9b34d4d01dc51002306cd353b8d01443d00288991b34d4f8340510023a8c1b34d4d01dc5100230839d66ccd01dc51000008c1b34d4d01dc51002306cd874d4d01dc510000092db34d4d022c510023085d5c438d01dc510026496db34d4d01dc51002646cd35438f834051002306cd504d4d01dc51002307edb34d4d023c7700230839d6628d01dc51002306cd353408b14400002307edb34d4d01dc5c002306cd52340871dc61002306cd584d4d01dc51002306cd35340a81dc510024b725b34d4d01dc51002307edb34d4d02c051002306cda24d4d014416002306cd35340cb1dc51002648c1b34d5031dc510027a8c1b34d4d01dc51002306fd35340b91dc510023070d354d4d01dc51002306cd753b8d02e451002648c1b3504d01dc51002306cd523407714400002306cd7f584d01dc51000008c20e6cd9a340770025b6cd35340771441f002306cd35484e934077002306cd35340ca1dc51002328c1b34d4d01dc51000008c1b34d4d022c51002548c1b34d4d01dc51002306cd3540c771441f002306cd35478d01dc51002888c1b35d4d01dc510023071db34d4d01dc51002406cd474d4d01dc510023073935340771dc5100230725b34d4d01dc5100230789b34d4771440b002306cd35408d01dc51002306fd353407714407002406cd353407714402002306cd35340851dc51002306cd41340771441f000008c1b3548d01dc51002538c1e26cd351dc51002306cd75438d01dc51002306cd353e0d021c770023089e174d4d01dc51002306cd664d4b91dc51002306cd87548d01dc51002306cd353b8d01440b0029e8c1d64d4d01dc51002386cd353a4d01dc51002838c1b34d4d01dc51002306cd354b52734051002538c1b34d4ee340510023c8c1b34d4d01dc51002306cd353409c1dc51002306cd35340881dc51000008c1f15d4d01dc5100230895bb4d4d01dc51002889ee226ccd01dc51002888c1b34d4e31dc51002306cd4a340771443d002306cda24d4d014404002306cd58548d01dc51002798c1de6ccd01dc51002306fd35340d01dc510024b6cd474d4d01dc51002306cd35438e31dc51000008c1b35fd5c1442c002306cd5c440d01dc51002306cd35340c21dc51002307c53537cd01dc510024b6cd3534077144020027b8c1b3669353407700230839b36a8d01dc5100230759b34d4d020051002306cd354d4f21dc5100230759b3505353407700230739353408b1dc51002306cd664d4771440700230725b34d4d022c51002306cd35340b11dc51002598c1b34d4d01dc5c002706cd35340771440000230789b36698a4d47700230819b3570d01dc510023b6fdb34d4d01dc51002306cd35340771444b002306cd3549cd025051002306ed7f4d4d01dc51002888c1b54d4d01dc5100230839b34d4d01dc510025a8c1b35fd351dc510023070d35340771443d002646cd35474d01dc51002306fd35340911dc5100230725b3548d01dc51000008c1b34d5081dc5100230855b34d4d01dc51002306cd664d4d01dc51002306cd474d4d01dc51002538c1b34d4d01dc16002648c1e26cd351dc51002306edb34d4d01dc51002306cd353407714402002306fd35340801441f002998c1b34c8d01dc51000009c1b34d4d01dc51002648c1b34d4ee3405100230759b34d4d81dc51002306cd3540ca71dc510028a8c1b34d4d01dc51002306ed8a4d4d01dc510027b8c1b36bd3534077002306cd35340b728c510023b6cd353407714400002306cd353b8d032451002306cd4a340771440b002307b1b3679351dc51002306cdb04d4d01dc51002306cd353407c1dc51002307e1f14d4d01dc51002538c1b3528d01dc51002748c1b34d4d01dc51002306cd3549cd018451002648c1b34d4d01e85100230789b34d4771441f002538c1b35b5351dc51002306cd3537cd01dc00002306cd35340c81dc51002306cd524d4f21dc51002306cd664d4911dc51002478c1b34d52134077002306cd7f4d4d01dc4e002306ed3d4d4d01dc51002306cd353b8d01441f002306cd353408a1dc51000008c1b3564d01dc51002648c1b34d4d014417002306cd474d4d022c51002306cd8e4d4d01dc510026494db34d4d01441d002307edc95fd351dc51002306cd353408b14402000008edb34d4d01dc5100230759b35713534091002306cd35340bf1dc51002648c1b34d4d01443500230889d6570d01dc51000008c1b34d4df34077002306cd3534077144230028c8c1b34d4d01dc51002406cd7f4d4d01dc510023070d35340771440b002306cd353c8771443d002306cd5251cd01dc51002478e1b34d4d01dc51002307edb3504771441f00230759b34f4d01dc51002306cd4f528d01dc51002538c1c34d4d01dc5100270725b34d4d01dc51002306cd523407714402002306cd35340cc1dc51002307c5d64d4d01dc51002307b5b36893534051002406cdb34d4d01dc5100230759c951d353407700230839b3340771443d000008c1b35995c1dc51002306cd354d4d020051002306cd5c4d4d014439002306cda24d4d01dc51002307edbf4d4d01dc5100230775b35713534051002306cd353409b1dc51002888c1b36693534077002306cd353ccd01dc51002406cd8a4d4d01dc51002648c1b3528d01dc510024b6cd7f4d4d01dc510026485d35438d01dc5100230895b34d4d01dc510023085dd64d4d01dc51002306ed35340b91dc510027b94db351d3534077002648c1b35710f34051000008c1b34d4d02c0a7002306cd9a4d50e34077002306cd7f340961dc51000008c1b34d4f83a491002306cd494d4d01dc510023b725b34d4d01dc51000008c1b3514d01dc510024b6cdb34d4d01dc51002306cda04d4d01dc510023b6cd41340771441f002306cdaa5fcd01dc510024f6cd5c4d4d01dc51002307edb34d4771444b00230759914d4d01dc51002306cd5c528d01442c00230789b3669353407700230725b34d4df34077002306cd35340771440d002306cd4a340771441f0024b6cd8a4d4d01dc51002538c2227593534077002306cd35340b81dc51002306cd35340a71dc2c002428c1b34d4d01dc51002306cd35340771440e002307c1b34d4d01dc51002306cd354b52134077002306cd35340a71dc01002306cd353407717039002307edb3599351dc51002306cd354d4d81dc51002306ed35340771440700230889b34d4d021c77002306cd7f4d4d01dc51002306cd353c8771440b002648c1c34d4d01dc5100253819b34d4d01dc51002648c1b34d4d0144480024a8c1b34d4d01dc51002706cd474d4d01dc51002538c1b34d4f21dc51002306cd353a4d01dc5c002306cd35340ba1dc51002706cd353407714402002306cd3549cf834051002306cd8851cd01dc51002306cd353a4d02c05100230779d64d4d01dc51002458c2066cd351dc510000092dce4d4d01dc51002306cdb34d4d01dc5100230839b3340771440b002306cd8f4d4d01dc510023f6cd353e0d01dc51002306ed35340d01dc51002538c20e6ccd01dc5100230889b34ecd01dc510025a8c1b34d4d01dc5100230739353407714400002306cd634d4d01dc510023070d5c4d4d01442c002306cd4a340771702c002306cd35340a31dc51002306cd8a4d4d01dc51002306cd7f4d4d31dc510023070d35340771441f0025b6cd5c4d4d01dc51000008c1b34d4f221c77002648c1b34d4d814416002889919e4d4d01dc51002306cd35484d025077002406cd35340b91dc51002538c1f64d4d01dc51002306cd7f4d4d022c510023b6cd474d4d01dc51002306cd5c4d5031dc51002306cd353407714436002646cd35440d01dc51002306cd35340801443d000008edfb6cd351dc510029f8c1b34d4d01dc51000008c1f74d4d01dc510023b6cd353407714402002307599e4d4d01dc51002306cd35340a61dc51002306cd3d4d4d01dc51002306cd35340a71dc160025391db34d4e934077002306cd354b8d01dc51002306cd474d4df34077000008c1ce4d4d01dc51000008c1b3538d01dc51002306cd5c504d01dc51002306cd984d4d01dc51002306cd5c4d4d02d877002306cd834d4d01dc51002306ed35340911dc51002307c5354d4d01dc51002306cd3537cd01dc02002307edb34d47714423002306e5b34d4d01dc51002306cdb34d4d022c51002306cd7f548d01dc5100264819b34d4d01dc5100230839b36698a34077000008c1b35e8d01dc510023070d35340771702c002386cd35340941dc510024b6cd35340b91dc51002648c1b34d4f21dc51002306cd35340981dc51002306cd8a4d4d022c51002306cd364d4d01dc51002306cd35340c51dc51002406cd353407714407000008c2214d4d01dc51002306cd354b0d01dc510023085d354d4d01dc51002307edc94d4d01dc51002306cd35484d01dc61002306cdb3548d01dc5100230889d64d4d01dc1f002648c20e6ccd01dc51002648c1b34f4d014416002306cd35360771443d002306cd3540cb01dc51002306cd353e8d01dc51002306cd8a548d01dc51002307c5b35d4d01dc51002406cd35340d01dc51000008c1ce4d4d022c51002648c1b34d4f834051002306cd353c8771441f002307edb35fc961dc5100230759b3504d01dc1f0024b6cd3534077144070028c8edb34d4d01dc5100230881b3678d01dc51002306cd3537cd02fc77002306cd3549d2134051002306cd35340b91dc510027b8c1b34d4d021c77002386cd353407718451002306cd35340a71dc04002306cd353407715051002306cd35340771441d00230739c94d4d01dc51002306cd35340801440b002306cd35340771444200230839b3340771441f002538c1b34d4d020051002306cd5c51cd01442c0024b6cd35340d01dc51002306cda96893534051002306cd764d4d01dc51002478c1b34d4d01dc5c002307edb35fd351dc51002406cd35340911dc51000008c1cc4d4d01dc51002306cd35340b31dc51002478c1b34d4d02c051002706cd7f4d4d01dc510024b8c1b34d4e31dc51002788c1b34d5031dc51002466cd35340911dc51002306cd353407714407002306cd3d340771443d0027a759b34d4d01dc51002306cd2e340771443d002306cd664d5274385100230789b3571351dc5100230759b34d4d01dc4b002306cd35340b922c51002888c1fb4d4771441f0025b96db34d4d01dc51002307c535340771443d002306cd35420a31dc51002307edbb4d4d01dc51002308c1b35d4d01dc51002706cdb34d4d01dc5100230761b34d4d01dc51000009c1fb4d4d01dc51002306cd5c4d4ee34051002386cd353607714416002306cd35360771440b002306cd894d4d01dc51002538c1b34d4d81dc510024b6cd35340911dc51002306cd3544cd01dc5100230759b351d3534077002706cd8a4d4d01dc51002306cd35340d01dc5100000991b3599351dc51002306cd353407715c510023085d35340771443d002306cd52340b91dc51002306cd35340771441e002307a5e26cd351dc510025b6cd35340771a4510023b6cd7f4d4d01dc510000094e306ed3534077002307598a51d353407700230721b34d4d01dc510027b8c2226ccd01dc51002306cd5c4d4d01e851002306cd394d4d01dc51002308c1b34d4e31dc5100230739474d4d01dc51002888c1b44d4d01dc51002306cda34d4d01dc51002307c575340b91dc51002306cda24d4d014400002648c1b34d4d020051002306cd353408b14407002306cd35340771443c00230739353407714402002306cd7f4d4df34077002706cd354b8d01dc51002306cd353407e1dc510026e8c1b34d4e934077002306cd35484f8340770023b6cdb34d4d01dc51002306cd35424d029c77002306cd3534cd01dc51002306cd3a4d4d01dc51002306cd35340c71dc51002306cd5c4d4d014435002307edb34d4c51dc51002306cd35340911dc5100230889b34d52734051002306cdb34d4df340770023b6cd8a4d4d01dc51002306cd523407714407002306fd353a4d01dc51002306cd35340d022c51002306cd353407714432002308a9b36893534051002386cd3d3407714416002306cd3d340771440b000008c1b36893534051000008edd66cd3534077002306cd35340801441f002306cd35464d01dc51002306cd8a4d4df34077002306e9b34d4d01dc51002538c1b34f4d01dc51002307c535340771440b0023085d3549cd01dc51002386cd353e0d01dc51002308a5b34d4d01dc51002538c1f14d4d01dc51002407edb34d4d01dc5100230711b34d4d01dc51002648c1b34d4d81dc51002648c1fb6cd353e051002306cd52340d01dc51002888c1b34d4d021c77000008c1b35f0d01dc51002306cd35340b025451002306cd753407714451002307cdb34d4d01dc510024e8c1b34d4d01dc51002306cd954d4d01dc51002306cd5c528d01dc510023085d35340771440b002306cd35438d021c77002306cd353409a1dc51002306cd3e4d4d01dc51002306cd353407717035002306cd353409e1dc51002706cd35340b91dc51002538c2174d4d01dc51002306cd353409122c51002306cd664d4e91dc51002306cd35340a71dc770023b6cd35340c51dc51002306cd35340771443e002306cd35344771442c00230825b34d4d01dc51002306cd753407714410002306cd7f570d01442c002306cd35360771441f0024b7edb34d4d01dc51002306cd3537cd031477002306cd35400d01dc51002306cd35448d01dc51002306cd3538c7714451002648d1b34d4d01dc51002306cd35340941dc5c002306cd3b438d01dc51002306cd35340871dc6c002306cd52340911dc51002306cd5c4d4d01c451002306cd35340b025051002306cd353407714851002388e1b34d4d01dc5100230725b36893534051002307adb34d4d01dc51002306cd35340771441c002306cd3538c7714410002706cd3534077144070023070d5c4d4d01dc51002648c1b34f4d01dc510023e8c1b34d4d01dc5100230759c94d4d0244770023b6cd35340b91dc51002306cd354852134077002648c1f14d4d01dc51002306cd35420d01dc510024b739b34d4d01dc51002306cd353408b1443e002306cd35340931dc51002306cd3537cd02e477002307edb34d4d01dc51002706cd35340d01dc51002306cd353408f1dc71002798c1b34d4d01dc51002306cd35340771845c002307ed35340a31dc51002648c2174d4d01dc5100230759b34c8d01dc51002306cd3d340771441f0027b8c1b34d52734051002306cd35340b018451002307397f4d4d01dc5100230836066cd3534051002306cd3543cd01dc5100259901b34d4d01dc51002308c1b366935340770023b6cd353407714407002307c535340771441f002307f5b34d4d01dc51002307ddb34d4d01dc51002307edb34d4d31dc510023071d353a4d01dc51002306cd664d5214387700230839b36893534051002306cd3537cd01dc0700230739b34d4d01dc51002307d1b34d4d01dc51002478c1bf4d4d01dc51002307ed354b8d01dc51000008c1b34d52c34051002306cd6c5893534077002306cd353c877194510029c8c1b35fcd01dc51002306cd353f8d01dc510023085d35340771441f002706cd35340911dc51002307edb34d4d022c51002306cda251d35340510023073935340a31dc510023b6cd35340d01dc51002307398a4d4d01dc51002306cd354a4d01dc51002307edb34d4801441f002306cda24d4d014402000008c1b34d5032c0510028e8c1b34d4d02c051002306cd7f340a71dc51002306cd5c4d4f21dc51002948c1b34d4d01dc51002307ed35340981dc5100230885b34d4d01dc51002306cd3537cd0340770025b6cd35340771442c0025b6cd3534077144010026494db34d4d01dc1b002307edb3548d01dc51002306cd35340991dc5100230839b3570d01dc51002306cd534d4d01dc5100230759b34d4d031477002306cd7f4d47714439002306cd5c4d4e71dc51002478c1b3599351dc51002306cd3540c771442c00230739b34d4d022c51002306cd3540c7714401002306cd66570d01dc51002306cd35340771d051002306cd5c51cd01dc510023b6cd35340911dc51002306cd35340891dc51002306cd7f4d4e91dc51002306cd41340771442c002306cd41340771440100230889b34d52134077002306cd71599351dc51002598c1b34d4d01dc510023b6cd35340801441f002306cd3537cd0244770026e91db34d4d01dc510027f8c1b3504d01dc51002a38c1b34d4d01dc51002306cd7a340c51dc51002306cd9a4d4d01dc51002306cd353e0e934091002306cd7f528771442c002306cd35470d01dc51002306ed353a4d01dc51
  | 7 => 0x8c1b34d4d0250771440491e306cd35340771dc518c1b36cd3534077144078c1fb6cd474d4d01dc519ee306cd5c4d4d01dc518c1b35fd35340d01dc518c1fb6cd3534077144028c1b36293534077144078c1b36cd35340d01dc51002306cd3549d0e34051002538c1b351d353407792e306cd35340771443d8c1b34d4f8340771442c8c1b34d4f834077144018c1b362935340d01dc518c1b34d4d01dc61144048c1b35fd35340911dc518c1b34d4d02e4b91dc518c1b34d53534077144518c1b36cd35340911dc518c2306cd35340771443d8c1b362935340911dc518c22b6cd5c4d4d01dc518c1b34d53534077144108c1b357135340ac1dc5100230759b34d4d024477002306cda26293534051000008c1b34d4d029c77a66538c1b34d4d01dc51002478c1b35fd351dc518c1b34d4f834077144168c1b34d4d02e47714407002306cd7f570d01dc518c1b34d4d0340b91dc51002306cd35340771443900230775b34d4d01dc518c1b34d4d01dc5101c07002306cd353a4d01dc51a22306cd5c4d4d01dc518c1b34d4d0250771dc518c1fb6cd7f4d4d01dc518e2306cd3534077144168c2306cd35340771440b8c1b357135438d01dc5194e308c1b34d4d01dc51002306cd4a340771442c8c1b34d4d034077144078c1b34d4f834077144048c1b34d4d01dc511443d8c1b34d4d02e4911dc518c1fb6cdb34d4d01dc518c1fb6cd8a4d4d01dc518c1b34d4d01dc510f4108c1b34d4d01dc77184518c1b34d4d0340d01dc518c1dd725b34d4d01dc518c1b34d4d024477144078c1c96cd353a4d01dc510023070d35340771442c8c1b35fd35340991dc51992308c1b34d4d01dc51002306cd354850e340778c1b34d4d0340911dc518c1b34d4d01dc511440b94e306cd3534077144518c2226cd35340771442c8c2226cd353407714401002306cd35340771443f002306cd754d4d01dc518c1b34d4d01dc510400b8c2306cd35340771441f8c1d6759b34d4d01dc5194e306cd3534077144108c1fb6cd35340b91dc518c1b34d4d0244911dc519ee306cd353407714444002478c1b34d4d01dc51002306cd35340871dc51992306cd9e4d4d01dc518c1b351d353a4d01dc518c1b34d4d134077144018c1b34d4e934077144028c1b36698a4d4d01dc51002536cd8a4d4d01dc51a22306cd35340771a4518c1fb6cd353407714407002306cd374d4d01dc518c2226cd3534077144168c1b34d4f8340771dc51992306cd3534077144518c1b34d4d0244771443e8c1fb6cd35340d01dc51992306cd3534077144108c1b34d4e9340bf1dc5191e30725b34d4d01dc518c1b34d4d01dc511441f002306cd353b8d01dc518c2006cd353e0d01dc519ee306cd35340771442c8c222819b34d4d01dc518c1b34d4d01dc5107c109ee306cd3534077144018c1fb6cd35340911dc51002306cd353407a1dc518c2226cd353407714404002306cd3538c771443d002306cd35340951dc51002306cd3534077144178c1d66cd354d4d01dc518c1b34d4d01dc5c1442c8c1b34d4d02507714400002306cd35340771443591e306cd474d4d01dc51002306cd35340bb1dc51002478c1fb6cd351dc5191e306cd353407714402002306cd35340941dc518c1b35fd353a4d01dc519ee306cd3534077144168c1b34d4d01dc61144008c1b36cd353a4d01dc518c1c96cd35340951dc5196a306cd353a4d01dc518ee306cd35340771441f8c1b3629353a4d01dc5191e306cd8e4d4d01dc51002306cd353407718451002306cd35340771c4518c1b34d4d01f4771440b8c1fb7edb34d4d01dc51002306cd3534077144488c1c96cd35340941dc518c1d66cd35340771443d0000096db34d4d01dc519ee306cd353407714404a22306cd35340771442ca22306cd353407714401000008c1b34d5031dc518c1c36cd35340771442c8c1b34d50e340771442c002848c1b34d4d01dc518c1b34d50e3407714401002306cd904d4d01dc518c1b34d5354d4d01dc51000008c1b3504d01dc51002306cd3536077144168c2226cd35340771dc518c1b351d353407714417002889edb34d4d01dc518c2306cd5c4d4d01dc51a3e888c1b34d4d01dc518c1c96cd353407718451002306cd5234077184518c1b34d4e9340b91dc51002306cd35340c11dc51002968c1b34d4d01dc5191e306cd7f4d4d01dc518c1b351d35340941dc51a22306cd3534077144168c1d66cd35340771440b8c1b34d4d0250771440294e30759b34d4d01dc51002706cd35340941dc518c1b34d50e340771441691e306cdb34d4d01dc518c1b34d4e93407714407002306cd3d340771441696a478c1b34d4d01dc5191e306cd8a4d4d01dc51002306cd353e0d01dc518c1b34d4e9340d01dc518c1b351d3534077184518c1b34d4d01dc61144028c1b34d535340771443d8c1b3571353407714451000008c1e26cd351dc51a22306cd353407714404000008c1b34d4ee340518c1b34d4d024477144398c1dd6cd35340911dc518c1b35713534077144108c1b34d50e340771440499230759b34d4d01dc519ee306cd35340771dc51002388c1b34d4d01dc518c1b34d4e9340911dc518c1b35d535340b91dc51002306e1b34d4d01dc51002918c1b34d4d01dc518c1c96cd353e0d01dc518c1d66cd35340771441f91e306cd35340b91dc51002306cd35340801dc518c1b34d535340771440b94e306cd354d4d01dc51002306cd35484d01dc518c1b35fd35340941dc5191e306cd3534077144078c1b34d4d01dc510f43d000008c1b3528d01dc518c1b36cd35340941dc51002307ed35340941dc51002306ddb34d4d01dc518c1b351d353e0d01dc51002307edb34d4f81dc518c1b34d4f834077144028c1b362935340941dc51002306cd664d50e1dc5191e306cd35340d01dc51002306cd35404d01dc518c1b34dd3534077144078c1fb6cd353a4d01dc5194e306cd8d4d4d01dc518c1b34d4ee340b91dc518c1b35fd353407718451002306cd3b4d4d01dc51000008c1c34d4d01dc51992306cd354d4d01dc51002306cd3534077144118c1b36cd353407718451002538c1b34d4e934077002306cd624d4d01dc51a22306cd35340771dc5191e306cd35340911dc51002306cd3534077188518c1b36293534077184510026a8c1b34d4d01dc518c1b34d50e340771dc518c1b34d4d01dc510f40b002306cd353407714430a12306cd7f4d4d01dc5194e306cd35340771443d8c1b34d535340771441f00230889b34d4d01dc518c1b34d4d01e87714407902306cd35340771442c8c204759b34d4d01dc518c1b34d4d02e4941dc518c1b35855c4d4d01dc51002306cd35344d01dc51000008c1b34d4f21dc518c1b34d4e3340771443d8c1c96cd353407714430000008c20e6ccd01dc518c1b34d4d02507714407002306cd3534077144158c1b34d4d01dc5102c0b992306cd35340771443d8c222725b34d4d01dc518c1b34d4d02e4771845194e306cd35340771440b8c1b35fd353e0d01dc5194e538c1b34d4d01dc5191e307edb34d4d01dc518c1b34d4d0340941dc518c2306cd35340771442c002306cd3534077144218c2306cd3534077144018c1b36cd353e0d01dc518c1b34d4d01dc510f41f8c1b3629353e0d01dc518c1b34d4d01dc61144070027b8c1b34d4d01dc518c1b34d4d0250911dc518c1b34d4d0340771845100230789b3629351dc518c2226cd474d4d01dc51992306cd35340771440b002306cd35340bd1dc518c1d66cd5c4d4d01dc51002306cd3534077170518c2226cd353407714402992538c1b34d4d01dc518c2306cd353407714416000008c1b34d4d020051002306cd3540cd01dc518c1b34d4d024477184518c1b34d4d01dc5107c0b8c1b34d4d01dc511442c94e306cd35340771441f8c1b34d4d01dc51144018c1b34d4d834077144169ee30725b34d4d01dc518c1b34d4f8340b91dc51002308adb34d4d01dc518c1b34d4d01dc510b0100025391db34d4d01dc518c1b34d4d01dc5104001002306cd35340ac1dc51002306cd353e0e91dc51000008c1b34d4d81dc51992648c1b34d4d01dc518c2306cd3534077144048c1b34d4e93a4d01dc518c1b351d3534077144218c1fb6cd35340941dc518c1b34d4f83407714407992306cd35340c91dc51002306cd353b8d02e4518c1b34d50e3407714400002306cd35340781dc518c1b34d4d01dc51144168c1b357135454d01dc51992306cd35340771441f8c1b34d4f8340d01dc51002888c1b34d4d01dc518c1b35fd624d4d01dc518c22b725b34d4d01dc519ee306cd474d4d01dc518c1b34d4d01dc51058109ee306cd3534077144020023070db34d4d01dc51002306cd35438d01dc510026491db34d4d01dc51000008c1b34f4d01dc518c1b3571354d4d01dc518c1fb6cd3534077184518c1fb6cd35340771c451000008c1f14d4d01dc518c1b34d4d01dc5107c1f8c2226cd7f4d4d01dc5100230789b34d4d01dc51002306cd35340771b0518c1b34d4f8340911dc51000008c2174d4d01dc518c2226cdb34d4d01dc518c1b34d4d01dc51144048c2226cd8a4d4d01dc51a2230725b34d4d01dc518c1b34d4d01dc51040048c1b34d4e9340771443f8c1c96cd35438d01dc51a72648c1b34d4d01dc518c1b34d4d01e477144040026e8c1b34d4d01dc51002306cd7f51cd01dc5191e306cd353a4d01dc51002306cd35354d01dc518c2306cd35340771dc518c1b357135340771443d00230839b3628d01dc518c1b34d4d01e07714402a22306cd474d4d01dc518c1fb6cd353e0d01dc51a22306cd3534077144028c2226cd35340b91dc518c1b359935438d01dc519ee306cd7f4d4d01dc518c1b351d35438d01dc518c1b34d50e34077144029ee306cdb34d4d01dc518c1b36215c4d4d01dc510029e8c1b34d4d01dc519ee306cd8a4d4d01dc51002818c1b34d4d01dc518c2226cd3534077144078c1b357135340771440b8c1b34d501340911dc5194e306cd5c4d4d01dc51002306cd35340a7250778c1b34d4d01dc7714451a46307edb34d4d01dc518c2226cd35340d01dc518c1b34d4d01dc77144108c1b34d4e9340771443591e478c1b34d4d01dc518c1b34d4e9340941dc518c1d66cd35340771442c002306cd353c8d01dc518c1d66cd3534077144018c6306cd3534077144018c2226cd35340911dc519ee306cd35340b91dc51992306cd5c4d4d01dc51a22306cd35340771440ea22306cd7f4d4d01dc518c1b34d4e934077184518c1b35fd35438d01dc518c1b357135340771441fa22306cdb34d4d01dc519ee306cd35340771440700230889b3570d01dc51002888c1fb4d4d01dc51002306cd3534077144198c1d66cd3534077144168c1b36cd35438d01dc518c1b34d4d02447714415a22306cd8a4d4d01dc51002408c1b34d4d01dc51002306cd353e0d024451a06306cd474d4d01dc518c1b362935438d01dc51002307c5b34d4d01dc51002998c1b34d4d01dc519ee306cd35340d01dc51a22306cd354b8d01dc518c1e26cd8a4d4d01dc510023085db34d4d01dc510024b8c1b34d4d01dc518c2227edb34d4d01dc519ee306cd35340911dc518c1c96cd353407714419002306cd914d4d01dc518c1b34d535340771442c8c1b34d53534077144018c1d66cd35340771440491e306cd35340941dc51a72306cd5c4d4d01dc51002308c1b34d4d01dc51a22306cd35340b91dc5100230779b34d4d01dc518c1b34d50e340b91dc518c1b34d4f83a4d01dc51002306cd35360d01dc51002307c535340b91dc5191e306cd3534077184518c1b34d4d021c7718451992306cd35340771441b8c1c96cd914d4d01dc51a22306cd3534077144078c1b34d5353407714416002306cd9e4d4d01dc518c1b34d50e340771440794e306cd35474d01dc518c230725b34d4d01dc51a7a306cd7f4d4d01dc51a22306cd35340d01dc518c1b34d4d01dc5104000a12478c1b34d4d01dc519ee307edb34d4d01dc518c1b34d4d01dc510f42c8c1b34d50e340d01dc518c1b34d4d01dc510f401002306cd353407714451002306cd35340771440a002308a1b34d4d01dc51002306cd3534077144108c1b34d5353407714404a22306cd35340911dc51002306cd35340791dc518c1b34d50e340911dc518c1d66cd35340771dc51002358c1b34d4d01dc518c1b34d4d0250941dc518c2306cd474d4d01dc518c2306cd3534077144028c1b34d4d01dc510f416002708c1b34d4d01dc518c1c96cd353407714451002648c1b357135340518c1b34d4d01dc510b00b91e306cd353e0d01dc518c1b34d4d01dc5102c0194e306cd35340771442c94e306cd3534077144018c1c96cd35340771441000230759c94d4d01dc518c1b34d5013a4d01dc51002306cd5c438d01dc518c1b35715c4d4d01dc518c1b34d4d025077184510023b8c1b34d4d01dc510027b94db34d4d01dc519ba306cd35340911dc51002306cd3534077144338c1b34d4d01dc510f404a22307edb34d4d01dc51002306cd3540c941dc51a46478c1b34d4d01dc518c1b34d4d01dc510580b8c1fb6cd35438d01dc518c1b351d35340771445194e306cd3534077144168c1b34d4d01dc61184518c1b34d4d01dc5114402992306cd35340771442c8c2226cd353a4d01dc51992306cd3534077144018c2286cd474d4d01dc518c1b351d3534077144108c1b34d4d01dc51040020025b6cd353407718451002306cd35450d01dc518c1b34d535340771dc518c1b34d4d01dc510b01fa3e648c1b34d4d01dc518c1b34d4d01dc5107c01000008c1b35d4d01dc518c2306cd7f4d4d01dc518c1b34d4d01dc5102c04002306cd35340771442d002306cd3537cd01dc5194e306cd353407714404002306cd614d4d01dc51992306cd3534077144168c2306cdb34d4d01dc51000008c1b34d4e31dc518c1b34d4f8340941dc518c2306cd8a4d4d01dc51002306cd353407d1dc518c1b34d4d01dc5107c168c1f16cd35340b91dc518c1b34d4f834077184519aa478c1b34d4d01dc519ee306cd353a4d01dc518c1b34d4d01dc771443d992306cd35340771440491e30889b34d4d01dc518c1b35fd3534077144518c1b35fd3534077144108c1b36cd353407714451a7a307edb34d4d01dc518c1b34d4d01dc5107c048c1b351d35450d01dc518c2306cd35340b91dc5100288991b34d4d01dc518c1b36293534077144518c1b34d4d022c771443d8c1b36cd353407714410002646cd35438d01dc5100230759b34d4d01dc51002318c1b34d4d01dc518c1b36293534077144108c1b34d4f8340c11dc51002307598a4d4d01dc518c1b3585474d4d01dc518c1b34d4d01dc771440b8c2306cd353407714407002306cd35340771440994e306cd35340771dc518c1b46cd3534077144018c1b34d4d23407714404002306fd35340771441f000008c1b366935340778c2306cd35340d01dc518c1b34d4f83e0d01dc518c1d6725b34d4d01dc51002306cd844d4d01dc51a22306cd353a4d01dc518c1b34d4d02e477144519ee478c1b34d4d01dc518c1b34d50e3a4d01dc518c2306cd35340911dc51002306cd35340961dc518c1b34d4d02e47714410992306cd35340771dc51002306cd35454d01dc518c2226cd35340941dc51002306cdaa4d4d01dc518c1b34d4d01dc5114407002306cd354d4d01dc518c1b357135340771442c8c1b35713534077144018c1b34d4d01dc771441f8c1b34d4d01dc51040078c1d66cd474d4d01dc518c1b34d4d034077144518c1d66cd3534077144028c2226cd3534077184518c1b34d4d034077144108c1b35fd35340771442d8c1b34d4d01dc57144108d6306cd353407714407002648c1b34d4d014416002306cd8d4d4d01dc518c1b34d4d024477144510024b6cd35340771443d002306cd353c877184518c1c96cd354d4d01dc518c1b35713534077144168c2307edb34d4d01dc518c1b350535340771441f8c1b34d4d01dc510f400002306cd524d4d01dc518c1b34d4d024477144108c1b3611474d4d01dc518c1d66cd3534077144238c1fb779b34d4d01dc51a22478c1b34d4d01dc518c1b34d5013e0d01dc519ee306cd35340bb1dc5191e306cd35438d01dc519ee306cd35340941dc51002306cd35340771443d002306d5b34d4d01dc51a5a30889b34d4d01dc519aa306cd353e0d01dc518c1b3571353407714404002306cd75340b91dc518c1b351d354d4d01dc519ee306cd3534077184518c1b34d53534077144028c1b34d4d01dc5102c008c1b34d503340941dc518c2226cd353e0d01dc51002306cd353408b1443d8c1b34d4df340b91dc518c1b357135340771442e002306cd3549cd01dc518c1fb6cd3534077144518c1d66cd7f4d4d01dc51002306cd884d4d01dc518c1c96cd35340771443d8c1fb6cd3534077144108c1d66cdb34d4d01dc51002386cd353407714416002306cd35340771440b002307edd64d4d01dc51002538c1b34d4d01dc51a127b8c1b34d4d01dc518c1d66cd35340a31dc518c1d66cd8a4d4d01dc51002306cd7f340941dc51000008c1b34d4d021c778c1bf6cd35340771441f8c1b36117f4d4d01dc51a5a7b8c1b34d4d01dc51002306cd353407714403002306cd3538cd01dc51002306cd9a6293534077a22306cd35340941dc51002306cd3534077144228c1b351d35340771443d8c1c96cd35340771440b8c1b34d50e340941dc518c1b34d4d01dc510f40294e30725b34d4d01dc518c1b56cd353407714402002648c1b34d4d01dc518c1b34d4d01dc5107c008c1b358535340911dc51002306cd35340c91dc519ee306cd353e0d01dc518c1d66cd35340b91dc51a22306cd3534077184518c1b357135340771dc51002306cd5c4d4d01442c8c1b35fd354d4d01dc51002306cd35340771441f8c1b34d50e34077184518c1b36cd354d4d01dc51002888c2224d4d01dc518c1d66cd3534077144078c1b3629354d4d01dc518c1b351d35340771440b99230725b34d4d01dc5194e306cd474d4d01dc518c1b34d4d01dc5102c02002306cd35340771702c94e306cd353407714402002306cd35348d01dc518c2226cd3534077188518c1d66cd35340d01dc518c2306cd353a4d01dc518c1c96cd35340771441f8c1b34d4d01dc510b02c8c222889b34d4d01dc51a5a888c1b34d4d01dc518c1b34d4d01dc510b0018c1b34d4d01dc51004010029c8c1b34d4d01dc518c1d66cd35340911dc51002306cd35340a71dc518c1b35fd35340771443d992306cd474d4d01dc51992306cd353407714402a22306cd353e0d01dc518c1b34d535340b91dc518c1b36cd35340771443d8c1b34d50e3e0d01dc518c1b362935340771443d8c1b351d35340771441f8c1b34d4d01dc510b0168c1b34d4d01dc5105801002307edb34d4771441f8c1b34d4d01dc5107c028c1b34d4e934077144518c1b34d4e9340771440a002306cd35340771442500230811b34d4d01dc51000008c1b34d527340518c1b34d53534077144078c1b36217f4d4d01dc51002306cd3534077144419ee306cd3534077144110023073935340771443d8c1b34d4e934077144108c1b35fd35340771440b002306d1b34d4d01dc51a46888c1b34d4d01dc518c1b34d535340d01dc5194e306cd7f4d4d01dc5191e308c1b34d4d01dc510023b6cd35340771441f9ee30889b34d4d01dc518c1b36cd35340771440b8c1fb759b34d4d01dc5194e306cdb34d4d01dc518c1b34d4d01dc510b0048c1b34d4d01dc51058168c1b34d4d01dc51010018c1b362935340771440b96a538c1b34d4d01dc5194e306cd8a4d4d01dc518c1b34d4d02e4771443d8c1b34d535340911dc51002538c1d66cd35340778c1b34d521438d01dc518c1b34d4f23407718451002306cd353407714428992306cd7f4d4d01dc518c1b34d4d01dc510f407002306cd35340771945194e306cd35340c51dc518c22b889b34d4d01dc518c1b34d4d01dc5105804992306cdb34d4d01dc51002306cd5c4d4d01dc5191e306cd3534077144518c1b34d4d0340771443d8c1b35fd35340771441f992306cd8a4d4d01dc518c1fb6cd35340961dc518c1b34d4d02e4771440b002306cd353a4d02447794e306cd35340b91dc5191e306cd3534077144108c1b36cd35340771441f94e306cd35340771441d9ee7b8c1b34d4d01dc51002648c1c96cd35340518c1b362935340771441f002306cd3534077154518c1b34d4d0244771443d8c1fb6cd354d4d01dc5100230759b34d4d01dc1f002306cd35340b01dc51a2230889b34d4d01dc518c1b34d4d01dc5102c078c1b34d4d01dc510100494e306cd3534077144078c1c96cd5c4d4d01dc518c2306cd35340941dc518c2226cd35438d01dc51000008c1b34d521340778c1b34d4d01dc771442c8c1b34d4d01dc77144018c1b34d4d0340771440b94e306cd35340d01dc51992306cd35340b91dc518c1b34e535340771440b002306cd353407714c51000008e1b34d4d01dc518c2306cd3534077184518c1b34d4d3340771440b8c1b34d4d0244771440b8c1b34d4d02e4771441f91e306cd35340771443394e306cd35340911dc510027b8c1b35fcd01dc51992306cd3534077144070025b8c1b34d4d01dc518c1b3571474d4d01dc518c1b34d4d01dc77144168c1b35713534077144028c1fb6cd35340771443d8c1b34d4d02507714451992306cd35340d01dc51002306cd35340771a4518c1b34d4d01dc5107c07002306cd35340771441b8c1b34d4d02507714410a227b8c1b34d4d01dc51002306cd7f4d4771442c9ee306cd35438d01dc518c1ce6cd35340771443d8c1dd759b34d4d01dc518c1b34d4d0340771441fa22306cd35340bd1dc518c1d66cd353a4d01dc51992306cd35340911dc518c1b34d4d01dc61144518c1b34d4d01dc77144049c2306cd35340941dc518c1b34d4d01dc61144108c1fb6cd35340771440b8c1b34d4d0244771441f94e307edb34d4d01dc51a7a30889b34d4d01dc518c2306cd353e0d01dc518c1b34d4d01dc5314402002306cd35474d01dc518c1b3611353a4d01dc51002306cd3534077144448d2306cd353407714404002306ed353407714416002406cd35340771442c8c1b35fd5c4d4d01dc518c1fb6cd3534077144228c1b36cd5c4d4d01dc51992307edb34d4d01dc51a22888c1b34d4d01dc518c1b36295c4d4d01dc51a22306cd35438d01dc518c1b34d5353a4d01dc518c1b34d4f83407714451992306cd3543cd01dc51000008c1b34d4d01dc5c8c1b34d4d01dc510b0008c1b34d4d01dc51004008c1b34d50e438d01dc51000008c1b34d4d02c05191e30759b34d4d01dc51002306cd3534077190518c1fb6cd35340771441f8c1b34d4f8340771441000230725b357135340518c1b352935340771442ca067b8c1b34d4d01dc518c1b34d4d01dc771dc51002306cd35340771442c002306cd3534077144010023085d35438d01dc510028f8c1b34d4d01dc518c1b34d4d01dc51058008c1b357135340b91dc518c1b86cd3534077144100026494db34d4d01dc518c1c96cd35340771442c8c1b34d4e9340771443d002306cd3534077144168c1c96cd3534077144018c1b35713534077144078c230889b34d4d01dc51a3e30725b34d4d01dc518c1b34d4d01dc5101000002306cd35440d01dc5191e306cd354d4d01dc518c1b357135340d01dc5100230819b34d4d01dc518c1d66cd35340941dc518c2047edb34d4d01dc518c1b34d4d01dc55144078c1c96cd353407714416002306cd3534077144048c1b351d35340771442c8c1b34d4e9340771440b8c1b351d3534077144018c1b34ed3534077144108c1b34d4d01dc510b00294e306cd353a4d01dc518c1b34d4d01dc51008018c1b357135340911dc51002306cd35340771442e8c1d66cd3534077184518c2226cd353407714451000008c1bf4d4d01dc518c228889b34d4d01dc518c1c96cd3534077144048c2226cd35340771441000230889d64d4d01dc5191e306cd35340771443d8c1b351d3534077144169ee308c1b34d4d01dc518c1bb6cd3534077144168c1b34d4d01dc51058028c1d66cd904d4d01dc51992306cd353a4d01dc51000008c1b3599351dc518c1b34d535340941dc518c1b34d4e9340771441f8c1fb6cd5c4d4d01dc518c1b351d3534077144048c1b34d4d01dc510100291e306cd35340771440b002306cd35340771dc51a66888c1b34d4d01dc5194e478c1b34d4d01dc518c1b35fd35340771442c8c1b35fd3534077144018c1d66cd353e0d01dc518c1b34d53534077184519ee306cd3534077144518c1b36cd35340771442c8c1b36cd3534077144018c2176cd35438d01dc519ee306cd3534077144108c1b362935340771442c8c1b3629353407714401002306cd353408b1dc5100230801b34d4d01dc51002348c1b34d4d01dc51a22308c1b34d4d01dc518c1c96cd35340771dc51002306cd414d4d01dc518c1b34d4d0250771443d8c1b35fd3534077144168c2306cd35438d01dc51992478c1b34d4d01dc518c1b35493534077184518c1b36cd3534077144168c1b362935340771441691e306cd35340771441f8c200725b34d4d01dc518c1b34d4d01dc611443d8c2046cd353a4d01dc51000008c1bb4d4d01dc518c1b34d4d02e4771442c8c1b34d4d02e477144018c1b34f53534077144168c1b35fd3534077144048c1b34d5353e0d01dc518c1b351d35340771dc518c1b34d4d01dc77144028c1b34d4d0250771440b002306cd5c4d4d02445194e306cd35340941dc51a22306cd3534077144518c1b36cd3534077144048c1b34d4d01dc510b0078c1b34d50e34077144518c1b34d4d01dc5101c018c1b3629353407714404a22306cd3534077144108c1b34d50e34077144108c1b34d4d0340771442c8c1b34d4d02e477144168c1b34d4d034077144018c1b34d4d01dc611440b94e306cd3534077184518c1b34d4d0244771905100000901b34d4d01dc51002306fdb34d4d01dc518c1b34d9353407714404992306cd35340941dc518c222759b34d4d01dc518c1b34d4d01dc51058078c1b34d4d0244771442c002306cd35340871dc618c1b34d4d024477144010000092db34d4d01dc518c1b34d4f8340771443d8c1b3571353a4d01dc51002306cd3534077144008c2226cd35340771440991e306cd3534077144258c1b34d4d034077144168c1b34d4d02e477144048c1b34d4d0250771441f002306cd4a4d4d01dc51992306cd3534077184518c1b34d4d53407714410000008c1b34d4d01dc518c1b35fd35340771dc518c1b34d4d01dc5101c048c1b34d4d024477144168c1b3621353e0d01dc518c1b34d4d01dc611441f8c1b36cd35340771dc518c1b34d4d01dc52144018c1b34d4f8340771440b8c1b362935340771dc518c1b34d4d0340771440494e306cd353e0d01dc51002328c1b34d4d01dc51000008c1b34d4d022c518c1fb6cd35340771442c8c1fb6cd3534077144019ee30759b34d4d01dc5100230725b34d4d01dc51002306cd41340771441f8c2226cd354d4d01dc51000008c1b3548d01dc518c1b34d4d029c941dc518c1b34d4d024477144048c1b34d4f8340771440391e306cd5c4d4d01dc51992306cd353e0d01dc518c1b34d4d01dc51008008c1fb6cd3534077144168c1b34d4d02e4771dc51002306cd35340771444b00230839b34d4d01dc518c1c9725b34d4d01dc51002306cd664d4d01dc51002306cd474d4d01dc51002538c1b34d4d01dc168c1b34d4f8340771441f002306edb34d4d01dc51002306cd353407714402000009c1b34d4d01dc518c1b34d4d01dc77144079ee306cdaa4d4d01dc518c2226cd35340771443d8c1b76cd35340771440b8c2308c1b34d4d01dc518c1fb6cd3534077144048c1b34d4d0340771dc51002306cd8e4d4d01dc519ee306cd354d4d01dc518ca306cd353407714402000008edb34d4d01dc51002306cd35340bf1dc51a2230759b34d4d01dc518c1c96cd474d4d01dc51000008c1b34d4df34077002306cd3534077144238c1d66cd35438d01dc518c1c96cd3534077144028c1b34d4d0244771dc518c1d66cd35340771b051002306cda24d4d01dc518c1b34d4d0200771441f8c2226cd35340771440b8c1b357135340941dc5194e30889b34d4d01dc518c2306cd353407714451002306cd35340771440e8c1b351d474d4d01dc518c2306cd3534077144108c1b351d353407714402002306cd7f4d4d01dc518c1b36293534077144008c1b34d4d01dc51008029ee306cd35340771443d8c1b35713534077184518c1b34d4d02c0941dc51002306cdb34d4d01dc519aa648c1b34d4d01dc518c1b35713534077144480025a8c1b34d4d01dc51002306cd35340a31dc51002306cd8a4d4d01dc5199230889b34d4d01dc518c1b34d4e9340771442ca22306cd354d4d01dc518c1b34d4e934077144018c1fb6cd35340771dc518c1b34d535438d01dc51002306cd3d4d4d01dc51002306cd354b8d01dc51000008c1ce4d4d01dc518c1c96cd7f4d4d01dc518c1b34d4d01dc51144518c2226cd35340771441f002306cd35340981dc51002306cd364d4d01dc51002306cd35340c51dc519ee306cd35340771440b8c1c96cdb34d4d01dc518c1b34d4d02e47714400002307edc94d4d01dc519ee538c1b34d4d01dc518c1b34d4d01dc51144108c2007edb34d4d01dc518c1c96cd8a4d4d01dc518c1b34d4e934077144168c1b34d4d01dc5104010002648c1b34d4f8340518c1b34d4f834077144288c1b34d4f83407719451002306cd35340b91dc518c1b35fd35340771444b002306cd35340771441d8c1b34d4d01dc5101c008c1b3571353e0d01dc518c1b35fd474d4d01dc51a22306cd35340771443d002307edb35fd351dc5196e306cd3534077184518c1b35fd3534077144028c1b34d50e340771443d002306cd3534077144078c1b36cd474d4d01dc519ee648c1b34d4d01dc518c20e6cd8a4d4d01dc518c1b36cd3534077144028c1b34d4e934077144048c1b3629474d4d01dc5191e306cd35340771442c8c1b362935340771440291e306cd35340771440100230759b351d3534077002306cd35340d01dc518c1c96cd35340b91dc51002306cd353407715c519ee306cd35340771441f0027b8c2226ccd01dc51002306cd394d4d01dc518c1b34d527438d01dc51002306cd3534cd01dc51a22306cd35340771440b8c1b351d35340981dc518c1c96cd353407714407a22538c1b34d4d01dc51002306cd35340911dc518c2226cd3534077144418c1b34d50e340771440b94e306cd35438d01dc51000008c1b36893534051002306cd35340801441f91e306cd353407714416a6630759b34d4d01dc518c1c96cd35340d01dc518c1b351d35340b91dc518c1b34d4d02e477144028c1b36898a4d4d01dc51002306cd35340771443ea727b8c1b34d4d01dc5191e306cd35440d01dc518c1b35fd7f4d4d01dc518c1c96cd35340911dc51a22648c1b34d4d01dc518c1b351d353407714407002306cd35340b025051002306cd3534077148518c1b34d4d01dc5101c028c1b36cd7f4d4d01dc51992306cd35438d01dc5191e306cd3534077144048c230759b34d4d01dc519ba538c1b34d4d01dc518c1b36297f4d4d01dc518c1b34d4e9340771dc518c1b351d35340d01dc518c1b36cdb34d4d01dc51002306cd3537cd02e4778c1b34d4d0250771442ca22306cd35340771441f002307edb34d4d01dc518c1b34d4d025077144018c1b34d4d034077144028c1b36cd8a4d4d01dc518c1b34d50e340771441f8c2226cd5c4d4d01dc518c1b36298a4d4d01dc51002306cd3543cd01dc518c1b351d35340911dc5100230739b34d4d01dc518c1b34d4d024477144028c1b34d4d01dc611442c8c1b34d4d01dc61144019ba648c1b34d4d01dc518c1b34d4d025077144168c1fb725b34d4d01dc518c1d66cd353407714451002306cd35340991dc518c1b35fd35340b91dc51a06538c1b34d4d01dc518c228759b34d4d01dc518c1d66cd353407714410002306cd5c51cd01dc51002306cd7f4d4e91dc518c1b36cd35340b91dc518c2306cd354d4d01dc518c1b362935340b91dc518c1b34d4d01dc6114416002306cd9a4d4d01dc518c1b35fd353407714407
  | 8 => 0x2306cd353a4d01dc51002478c1b34d4d01dc51002306cd35340941dc51002306cd353407718451002306cd353e0d01dc5100230889b34d4d01dc510027b8c1b34d4d01dc51002888c1b34d4d01dc51002306cd35438d01dc51002308c1b34d4d01dc51002306cd353407714451002306cd35340771441000230759b34d4d01dc51002306cd354d4d01dc51002306cd35340771443d002306cd35340771440b002538c1b34d4d01dc51002648c1b34d4d01dc51002306cd35340771441f002306cd5c4d4d01dc51002306cd35340771442c002306cd353407714401002306cd353407714416002306cd353407714404002306cd35340771dc51000008c1b34d4d01dc5100230725b34d4d01dc51002306cd474d4d01dc51002306cd353407714402002306cd7f4d4d01dc51002306cdb34d4d01dc51002306cd8a4d4d01dc51002306cd35340b91dc51002306cd353407714407002306cd35340d01dc51002306cd35340911dc51002307edb34d4d01dc51
  | 9 => 0x8c1b34d4d01dc51
  | _ => 0

def VT : Nat := 0xffffffffffffffffffffffffe00ffffffffffffffffffffffc01ffffffffffffffffffffff803ffffffffffffffffffffff007fffffffffffffffffffffe00ffffffffffffffffffffffc01fffffffffffff7fbfdfeff7fbfffffffffffffff7fbfdfeff7f80000ffffffffffeff7fbfdfeff7ffffffffffffffeff7fbfdfeff7ffff00003fffffe7f3f9fcfe7f0000000003fffffdfeff7fbfdfefffffffffffffffdfeff7fbfdfefffffffffc0000fd7ebf5fafd7e80000ffffc0000fcfe7f3f9fcfe7ffff000000000fc7e3f1f8fc7e3ffffffffffffffc7e3f1f8fc7e3ffffffffc0000fc7e3f1f8fc7e3ffff00003fffffc7e3f1f8fc7e00000ffffffffffbfdfeff7fbfdfffffffffffffffb7dbedf6fb7dbffffffffffe00fb7dbedf6fb7d80000ffffffe00fafd7ebf5fafd7ffffffffc01fffafd7ebf5fafd7ffff0000001fffa7d3e9f4fa7d3ffffffffc0000f97cbe5f2f97cbffffffffc0000f8fc7e3f1f8fc7ffffffffc0000f87c3e1f0f87c3ffffffffffe00f87c3e1f0f87c3ffffffffc01fff87c3e1f0f87c3ffffffffc0000f87c3e1f0f87c3ffff000000000f87c3e1f0f87c00000ffffc0000f7fbfdfeff7fbfffffffffffffff77bbddeef77bbffffff803fffff77bbddeef77b80000ff803fffff67b3d9ecf67b3ffff00003fffff5fafd7ebf5fafffff007fffffff5fafd7ebf5fafffff007fc0000f57abd5eaf57abffff00003fffff4fa7d3e9f4fa7ffff00003fffff47a3d1e8f47a3ffffff803fffff47a3d1e8f47a3ffff007fffffff47a3d1e8f47a3ffff00003fffff47a3d1e8f47a3ffff000000000f47a3d1e8f47a0000000003fffff379bcde6f379bffffff803fe00f2793c9e4f2793ffff000000000f178bc5e2f178bffff000000000f0f87c3e1f0f87ffff000000000f0783c1e0f0783ffffff8000000f0783c1e0f0783ffff007fc0000f0783c1e0f0783ffff00003fe00f0783c1e0f0783ffff0000001fff0783c1e0f0783ffff000000000eff7fbfdfeff7ffffffffffffffeff7fbfdfeff7fffff007fc01ffeef77bbddeef77ffff0000001ffedf6fb7dbedf6fffff007fc0000ec763b1d8ec763ffff000000000ebf5fafd7ebf5fffffff803ffffebf5fafd7ebf5fffff0000001ffeb75badd6eb75bffffff803fe00eaf57abd5eaf57ffffff80001ffeaf57abd5eaf57ffff007fc01ffeaf57abd5eaf57ffff00003ffffeaf57abd5eaf57ffff0000001ffeaf57abd5eaf57ffff000000000eaf57abd5eaf57fe000000001ffea753a9d4ea753ffff000000000e974ba5d2e974bffff000000000e8f47a3d1e8f47ffff000000000e8743a1d0e8743ffffff8000000e8743a1d0e8743ffff007fc0000e8743a1d0e8743ffff0000001ffe8743a1d0e8743ffff000000000e7f3f9fcfe7f3fffffffffffe00e7f3f9fcfe7f3fffff007fc0000e773b9dcee773bffffff803fe00e673399cce6733ffff000000000e5f2f97cbe5f2fffffffffc0000e5f2f97cbe5f2fffff007fffe00e5f2f97cbe5f2fffff007fc01ffe5f2f97cbe5f2fffff007fc0000e5f2f97cbe5f2fffff000000000e5f2f97cbe5f2c01ff007fc0000e572b95cae572bffff000000000e4f2793c9e4f27ffff000000000e472391c8e4723ffff007fc0000e472391c8e4723ffff00003fe00e472391c8e4723ffff0000001ffe472391c8e4723ffff000000000e3f1f8fc7e3f1fffffff803fe00e371b8dc6e371bffffffffffe00e371b8dc6e371bffffff803ffffe371b8dc6e371bffffff803fe00e371b8dc6e371bffff000000000e371b8dc6e37180000ff803fe00e2f178bc5e2f17ffff000000000e271389c4e2713ffffff8000000e271389c4e2713ffff00003fe00e271389c4e2713ffff0000001ffe271389c4e2713ffff000000000e1f0f87c3e1f0fffff000000000e170b85c2e170bffffff8000000e170b85c2e170bffff007fc0000e170b85c2e170bffff00003fe00e170b85c2e170bffff000000000e0f0783c1e0f07ffff007fc0000e0f0783c1e0f07ffff0000001ffe0f0783c1e0f07ffff000000000e070381c0e0703ffffffffc0000e070381c0e0703ffffff803fe00e070381c0e0703ffffff8000000e070381c0e0703ffff007fc0000e070381c0e0703ffff00003ffffe070381c0e0703ffff00003fe00e070381c0e0703ffff0000001ffe070381c0e0703ffff000000000e070381c0e0703fe00000000000e070381c0e070001ff000000000e070381c0e07000000000000000dfeff7fbfdfefffffffffffffffdeef77bbddeef7fe00fffffffffdeef77bbddeef7fe0000003ffffde6f379bcde6f00000fffffffffddeef77bbddeec01fffffffffffddeef77bbddeec01ffffffc0000dd6eb75badd6e80000fffffffffdcee773b9dcee40000fffffffffdc6e371b8dc6e3fe00fffffffffdc6e371b8dc6e001fffffffffffdc6e371b8dc6e00000fffffffffdc6e371b8dc6e00000ffffc0000dc6e371b8dc6e0000000003ffffdaed76bb5daed7fe00ffffc01ffda6d369b4da6d00000ffffc0000d96cb65b2d96c80000ffffc0000d8ec763b1d8ec40000ffffc0000d86c361b0d86c3fe00ffffc0000d86c361b0d86c001ffffffc0000d86c361b0d86c00000ffffffe00d86c361b0d86c00000ffffc01ffd86c361b0d86c00000ffffc0000d66b359acd66b0000000003ffffd5eaf57abd5eac01ff007ffffffd56ab55aad56a8000000003ffffd4ea753a9d4ea4000000003ffffd46a351a8d46a3fe0000003ffffd46a351a8d46a001ff00003ffffd46a351a8d46a00000ff803ffffd46a351a8d46a00000007ffffffd46a351a8d46a0000000003ffffcae572b95cae57fe000000001ffc86432190c864000000000001ffc5e2f178bc5e2c01ff007fc0000c46231188c46200000007fc0000c06030180c0603fe00000000000c06030180c060001ff000000000c06030180c06000000ff803fe00c06030180c06000000000000000bfdfeff7fbfdfffffffffffffffbfdfeff7fbfdfc01ffffffffe00bf5fafd7ebf5f80000ffffffe00bddeef77bbddec01ffffffc0000bc5e2f178bc5e00000ffffc0000bbddeef77bbddffe00fffffffffbbddeef77bbddc0000ffffffe00bb5daed76bb5dbfe00ffffffe00bb5daed76bb5d801ffffffffe00bb5daed76bb5d80000fffffffffbb5daed76bb5d80000ffffffe00bb5daed76bb5d80000ffffc0000bb5daed76bb5d80000ff803fe00badd6eb75badd7fe00ffffc01ffba5d2e974ba5d00000ffffc0000b95cae572b95c80000ffffc0000b8dc6e371b8dc40000ffffc0000b85c2e170b85c3fe00ffffc0000b85c2e170b85c001ffffffc0000b85c2e170b85c00000ffffffe00b85c2e170b85c00000ffffc0000b359acd66b35980000ff803fe00b0582c160b0580000000003fe00afd7ebf5fafd7c01ff007fc0000abd5eaf57abd5ffe00ff803ffffab55aad56ab5580000ff803fe00aad56ab55aad57fe000000001ffaa552a954aa5500000000000000a7d3e9f4fa7d3c01ffffffffe00a753a9d4ea75380000ff803fe00a5d2e974ba5d2c01ff007fc0000a3d1e8f47a3d1c0000ff803fe00a351a8d46a351bfe00ff803fe00a351a8d46a351801ffff803fe00a351a8d46a35180000ffffffe00a351a8d46a35180000ff803fe00a150a8542a15080000007fc0000a05028140a0503fe00000000000a05028140a050001ff000000000a05028140a050000000000000009fcfe7f3f9fcffffffffffc01ff9fcfe7f3f9fcfc01ffffffc00009ecf67b3d9ecf7fe00ffffc01ff9e4f2793c9e4f00000ffffc00009dcee773b9dcefffffffffc00009dcee773b9dcec01ffffffffe009dcee773b9dcec01ffffffc01ff9dcee773b9dcec01ffffffc00009dcee773b9dcec01ff007fc00009dcee773b9dcec0000ffffc00009d4ea753a9d4e80000ffffc00009cce673399cce40000ffffc00009c4e271389c4e001ffffffc00009c4e271389c4e00000ffffffe009c4e271389c4e00000ffffc01ff9c4e271389c4e00000ffffc00009bcde6f379bcdffe00ffffc01ff9b4da6d369b4d80000ffffc00009acd66b359acd7ffffffffc01ff9acd66b359acd7fe00fffffffff9acd66b359acd7fe00ffffc01ff9acd66b359acd7fe000000001ff9acd66b359acd40000ffffc00009a4d269349a4d3fe00ffffc00009a4d269349a4d00000ffffffe009a4d269349a4d00000ffffc01ff9a4d269349a4d00000ffffc000099cce673399ccc0000ffffc0000994ca6532994c801ffffffc0000994ca6532994c80000ffffffe00994ca6532994c80000ffffc000098cc6633198cc7fe00ffffc000098cc6633198cc401ffffffc000098cc6633198cc40000ffffc01ff98cc6633198cc40000ffffc0000984c26130984c3ffffffffc0000984c26130984c3fe00ffffc01ff984c26130984c3fe00ffffc0000984c26130984c001ffffffc0000984c26130984c00000fffffffff984c26130984c00000ffffffe00984c26130984c00000ffffc01ff984c26130984c00000ffffc0000984c26130984c00000ff8000000984c26130984c00000007fc0000984c26130984c0000000000000095cae572b95cac01ff007fc0000944a25128944a001ff00000000090482412090483fe000000001ff904824120904800000ff8000000904824120904800000007fc00009048241209048000000000000008fc7e3f1f8fc7fffff007fc01ff8ec763b1d8ec77fe000000001ff8dc6e371b8dc6c01ff007fc00008bc5e2f178bc5ffe000000001ff8ac562b158ac57ffff0000001ff8ac562b158ac57fe00ff80001ff8ac562b158ac57fe00007fc01ff8ac562b158ac57fe000000001ff88c46231188c4401ff000000000884422110884400000ff8000000884422110884400000007fc000088442211088440000000000000087c3e1f0f87c3c01ff007fc000085c2e170b85c2fffff007fc000085c2e170b85c2c01ffffffc000085c2e170b85c2c01ff007fc000084422110884420000000000000082412090482413fe00ff80000008241209048241000000000000008140a05028140801ffff80000008140a050281408000000000000080c06030180c07fe00007fc000080c06030180c04000000000000080402010080403ffff00000000080402010080403fe000000000008040201008040001ff000000000804020100804000000ffffc0000804020100804000000ff8000000804020100804000000007fc000080402010080400000000003fe008040201008040000000000001ff8040201008040000000000000007fbfdfeff7fbfffffffffffffff7fbfdfeff7fbfffe00ff803ffff7f3f9fcfe7f3f80000ff803ffff7ebf5fafd7ebf7fe0000003ffff7c3e1f0f87c3e0000000003ffff77bbddeef77bbc01fffffffffff77bbddeef77bbc0000ff803ffff773b9dcee773bbfe00ff803ffff773b9dcee773b801ffff803ffff773b9dcee773b80000fffffffff773b9dcee773b80000ff803ffff773b9dcee773b80000ff803fe00773b9dcee773b8000000003ffff763b1d8ec763b0000000003ffff75badd6eb75bac01ff007ffffff753a9d4ea753a8000000003ffff74ba5d2e974ba4000000003ffff743a1d0e8743a3fe0000003ffff743a1d0e8743a001ff00003ffff743a1d0e8743a00000ff803ffff743a1d0e8743a0000000003ffff73399cce6733980000ff803fe0070381c0e0703800000ff80000006fb7dbedf6fb7ffe000000001ff6bb5daed76bb5ffe00ff803ffff6b359acd66b3580000ff803fe006ab55aad56ab57fe000000001ff67b3d9ecf67b3c01ffffffffe00673399cce673380000ff803fe0065b2d96cb65b2c01ff007fc00006532994ca65328000000000000063b1d8ec763b1c0000ff803fe00633198cc66331bfe00ff803fe00633198cc66331801ffff803fe00633198cc6633180000ff803ffff633198cc6633180000ff803fe006231188c46231000000000001ff6030180c060303fe000000000006030180c06030001ff0000000006030180c06030000000000000005fafd7ebf5faffffff007ffffff5fafd7ebf5fafffe0000003ffff5eaf57abd5eaf7ffff00003ffff5eaf57abd5eaf7fe00ff803ffff5eaf57abd5eaf7fe00007ffffff5eaf57abd5eaf7fe0000003ffff5eaf57abd5eaf7fe000000001ff5eaf57abd5eaf4000000003ffff5e2f178bc5e2f0000000003ffff5daed76bb5daec01ff007ffffff5d2e974ba5d2e8000000003ffff5cae572b95cae4000000003ffff5c2e170b85c2e3fe0000003ffff5c2e170b85c2e00000ff803ffff5c2e170b85c2e00000007ffffff5c2e170b85c2e0000000003ffff5aad56ab55aad7fe000000001ff582c160b0582c3fe0000000000057abd5eaf57abc01ff007ffffff572b95cae572b8000000003ffff56ab55aad56ab4000000003ffff562b158ac562b3fe0000003ffff562b158ac562b00000ff803ffff562b158ac562b0000000003ffff55aad56ab55aafffff007ffffff55aad56ab55aac01fffffffffff55aad56ab55aac01ff007ffffff55aad56ab55aac01ff007fc000055aad56ab55aac000000003ffff552a954aa552a801ff00003ffff552a954aa552a80000ff803ffff552a954aa552a80000007ffffff552a954aa552a8000000003ffff54aa552a954aa7fe0000003ffff54aa552a954aa401ff00003ffff54aa552a954aa40000007ffffff54aa552a954aa4000000003ffff542a150a8542a3ffff00003ffff542a150a8542a3fe0000003ffff542a150a8542a001ff007ffffff542a150a8542a001ff00003ffff542a150a8542a00000fffffffff542a150a8542a00000ff803ffff542a150a8542a00000007ffffff542a150a8542a0000000003ffff542a150a8542a0000000003fe00542a150a8542a000000000001ff542a150a8542a000000000000005028140a05028001ff007fc00005028140a050280000000003fe005028140a05028000000000001ff5028140a05028000000000000004fa7d3e9f4fa7fffff007fc01ff4ea753a9d4ea77fe000000001ff4da6d369b4da6c01ff007fc00004ba5d2e974ba5ffe000000001ff4aa552a954aa57ffff0000001ff4aa552a954aa57fe0000003ffff4aa552a954aa57fe000000001ff48241209048240000000000000047a3d1e8f47a3c01ff007fc000045a2d168b45a2fffff007fc000045a2d168b45a2c01ff007fffe0045a2d168b45a2c01ff007fc01ff45a2d168b45a2c01ff007fc000044a25128944a27fe0000000000044221108844220000000003fe004422110884422000000000001ff44221108844220000000000000042211088442213fe0000003fe004221108844221000000000000004120904824120801ff00003fe0041209048241208000000000000040a05028140a0401ff0000001ff40a05028140a04000000000000040201008040203ffff00000000040201008040203fe000000000004020100804020001ff000000000402010080402000000ff8000000402010080402000000007fc000040201008040200000000003ffff40201008040200000000003fe004020100804020000000000001ff4020100804020000000000000003f9fcfe7f3f9fc0000ff803fe003b9dcee773b9dffe00ff803ffff3b1d8ec763b1d80000ff803fe003a9d4ea753a9d7fe000000001ff379bcde6f379bc01ffffffffe00371b8dc6e371b80000ff803fe00359acd66b359ac01ff007fc00003399cce673399c0000ff803fe0033198cc66331980000ffffffe0033198cc66331980000ff803ffff33198cc66331980000ff803fe0030180c0603018000000000000002f97cbe5f2f97ffffffffffffff2f97cbe5f2f97fffff007fc01ff2f97cbe5f2f97ffe00ff803ffff2f97cbe5f2f97c01ffffffffe002f178bc5e2f1780000ff803fe002e974ba5d2e977fe000000001ff2d96cb65b2d96c01ff007fc00002b95cae572b95fffffff803ffff2b95cae572b95ffe00fffffffff2b95cae572b95ffe00ff803ffff2b95cae572b95ffe000000001ff2b95cae572b95c0000ff803fe002b158ac562b15bfe00ff803fe002b158ac562b1580000ffffffe002b158ac562b1580000ff803ffff2b158ac562b1580000ff803fe002a954aa552a957ffff0000001ff2a954aa552a957fe00ff80001ff2a954aa552a957fe0000003ffff2a954aa552a957fe000000001ff28140a05028143fe00ff800000028140a0502814000000000000002793c9e4f2793fffffffffffe002793c9e4f2793c01fffffffffff2793c9e4f2793c01ffffffffe002793c9e4f2793c01ff007fc00002793c9e4f2793c0000ff803fe00271389c4e2713801ffff803fe00271389c4e271380000ffffffe00271389c4e271380000ff803ffff271389c4e271380000ff803fe002592c964b2592fffff007fc00002592c964b2592c01ffffffc00002592c964b2592c01ff007fffe002592c964b2592c01ff007fc00002412090482412001ff00003fe002412090482412000000000000002391c8e472391ffe00ff803fe002391c8e472391c01ffff803fe002391c8e472391c0000ffffffe002391c8e472391c0000ff803ffff2391c8e472391c0000ff803fe00231188c462311bffffff803fe00231188c462311bfe00ff803ffff231188c462311bfe00ff803fe00231188c462311801ffffffffe00231188c462311801ffff803fe00231188c46231180000ffffffe00231188c46231180000ff803ffff231188c46231180000ff803fe00231188c46231180000ff8000000231188c4623118000000003fe00231188c46231180000000000000229148a452291401ff000000000221108844221100000ff800000022110884422110000000003fe002211088442211000000000000002190c86432190ffe00000000000211088442211080000ff800000021108844221108000000003fe0021108844221108000000000000020904824120904000000000000020100804020103ffff00000000020100804020103fe0000003ffff20100804020103fe000000000002010080402010001ffffffc00002010080402010001ff000000000201008040201000000ff803fe00201008040201000000ff8000000201008040201000000007fc000020100804020100000000003fe002010080402010000000000001ff2010080402010000000000000001f8fc7e3f1f8ffffff007fc01ff1e8f47a3d1e8f7fe000000001ff1d8ec763b1d8ec01ff007fc00001c8e472391c8e400000000000001b8dc6e371b8dffe000000001ff1a8d46a351a8d7fe00ff80001ff1a8d46a351a8d7fe00007fc01ff1a8d46a351a8d7fe0000003ffff1a8d46a351a8d7fe000000001ff1a0d068341a0d0000000003fe00180c06030180c00000ff8000000180c06030180c00000007fc0000180c06030180c00000000000000178bc5e2f178bc01ff007fc0000158ac562b158ac01ffffffc0000158ac562b158ac01ff007fffe00158ac562b158ac01ff007fc01ff158ac562b158ac01ff007fc0000150a8542a150a80000ff8000000140a05028140a0000000003fe00140a05028140a000000000001ff140a05028140a00000000000000120904824120900000ff80001ff120904824120900000000000000110884422110880000007fffe00110884422110880000000000000108844221108840000007fc01ff10884422110884000000000000010080402010083fe000000000001008040201008001ff000000000100804020100800000ffffc0000100804020100800000ff8000000100804020100800000007fc000010080402010080000000003ffff10080402010080000000003fe001008040201008000000000001ff1008040201008000000000000000f87c3e1f0f87fffffffffc01ff0f87c3e1f0f87fffff007ffffff0f87c3e1f0f87fffff007fc01ff0f87c3e1f0f87ffe000000001ff0f87c3e1f0f87c01ff007fc00000e8743a1d0e877ffff0000001ff0e8743a1d0e877fe00007fc01ff0e8743a1d0e877fe0000003ffff0e8743a1d0e877fe000000001ff0d86c361b0d86fffff007fc00000d86c361b0d86c01ffffffc00000d86c361b0d86c01ff007fc01ff0d86c361b0d86c01ff007fc00000c06030180c0600000007fc01ff0c06030180c06000000000000000b85c2e170b85fffff0000001ff0b85c2e170b85ffe00ff80001ff0b85c2e170b85ffe00007fc01ff0b85c2e170b85ffe0000003ffff0b85c2e170b85ffe000000001ff0b0582c160b0580000007fc00000a8542a150a857ffff007fc01ff0a8542a150a857ffff0000001ff0a8542a150a857fe00ffffc01ff0a8542a150a857fe00ff803ffff0a8542a150a857fe00ff80001ff0a8542a150a857fe00007fc01ff0a8542a150a857fe0000003ffff0a8542a150a857fe000000001ff0a8542a150a857fe000000000000a8542a150a85400000000001ff0a8542a150a85400000000000000a05028140a053fe000000000000a05028140a05000000000001ff0a05028140a05000000000000000984c26130984c0000ff800000009048241209048000000000000008844221108847fe000000000000884422110884400000000001ff08844221108844000000000000008040201008043ffff007fc000008040201008043fe000000001ff08040201008043fe000000000000804020100804001ff000000000080402010080400000ffffc0000080402010080400000ff803ffff080402010080400000ff8000000080402010080400000007fc000008040201008040000000003fe000804020100804000000000001ff0804020100804000000000000000783c1e0f0783fffff007fc00000783c1e0f0783c01ffffffc00000783c1e0f0783c01ff007fffe000783c1e0f0783c01ff007fc01ff0783c1e0f0783c01ff007fc0000070381c0e0703800000000001ff068341a0d06834000000003fe0006030180c0603000000000000000582c160b0582fffff007fc01ff0582c160b0582fffff007fc00000582c160b0582c01ffffffffe000582c160b0582c01ffffffc00000582c160b0582c01ff007ffffff0582c160b0582c01ff007fffe000582c160b0582c01ff007fc01ff0582c160b0582c01ff007fc00000582c160b0582c01ff0000000000582c160b0582c0000007fc00000582c160b0582c000000000000005028140a0502801ff00000000005028140a050280000007fc000005028140a0502800000000000000482412090482401ff000000000048241209048240000007fc000004824120904824000000000000004020100804023ffff0000001ff04020100804023fe000000000000402010080402001ff007fc00000402010080402001ff000000000040201008040200000ffffffe00040201008040200000ff8000000040201008040200000007fc000004020100804020000000003ffff04020100804020000000003fe000402010080402000000000001ff040201008040200000000000000030180c060301bffff000000000030180c06030180000ff8000000030180c0603018000000003fe00030180c06030180000000000000028140a0502817fe00000000000028140a05028140000ffffc0000028140a050281400000000001ff028140a0502814000000000000002010080402013fe000000001ff02010080402013fe000000000000201008040201001ff000000000020100804020100000ff803fe00020100804020100000ff8000000020100804020100000007fc000002010080402010000000003fe000201008040201000000000001ff0201008040201000000000000000180c06030180c01ff0000000000180c06030180c0000007fc00000180c06030180c000000003ffff0180c06030180c00000000000000100804020100bfe000000000000100804020100801ff007fc00000100804020100801ff000000000010080402010080000ff803fe00010080402010080000ff8000000010080402010080000007fc000001008040201008000000003fe000100804020100800000000001ff01008040201008000000000000000804020100807fe000000001ff00804020100807fe000000000000080402010080401ff007fc00000080402010080401ff000000000008040201008040000ff8000000008040201008040000007fc000000804020100804000000003fe000080402010080400000000001ff00804020100804000000000000000000000000003ffff00000000000000000000003fe00ff800000000000000000003fe00007fc000000000000000003fe0000003fe0000000000000003fe000000001ff00000000000003fe000000000000000000000000001ffff80000000000000000000001ff007fc00000000000000000001ff00003fe000000000000000001ff0000001ff0000000000000001ff000000000000000000000000000ffffc0000000000000000000000ff803fe00000000000000000000ff80001ff000000000000000000ff8000000000000000000000000007fffe00000000000000000000007fc01ff000000000000000000007fc000000000000000000000000003ffff00000000000000000000003fe000000000000000000000000001ff000000000000000000000000000

def S (s j : Nat) : List Nat :=
  (List.range (fld (LT s) 4 j)).map (fun t => fld VT 108 (fld (DT s) 10 (8*j+t)))

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)

def Z (s : Nat) := bar 54 S NN idx s

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL prism rowsG = goal 54 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (covUp 54 zs &&& lo 54) ≠ lo 54 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x0 : span (Z 4) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x8 : span (Z 4) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x16 : span (Z 4) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x24 : span (Z 4) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x32 : span (Z 4) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x40 : span (Z 4) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x48 : span (Z 4) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x56 : span (Z 4) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x64 : span (Z 4) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x72 : span (Z 4) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x80 : span (Z 4) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x88 : span (Z 4) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x96 : span (Z 4) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x104 : span (Z 4) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x112 : span (Z 4) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x120 : span (Z 4) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x128 : span (Z 4) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x136 : span (Z 4) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x144 : span (Z 4) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x152 : span (Z 4) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x160 : span (Z 4) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x168 : span (Z 4) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x176 : span (Z 4) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x184 : span (Z 4) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x192 : span (Z 4) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x200 : span (Z 4) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x208 : span (Z 4) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x216 : span (Z 4) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x224 : span (Z 4) 7 224 = true := by decide +kernel
theorem z4 : span (Z 4) 231 0 = true := (@span_join (Z 4) 112 0 119 (@span_join (Z 4) 56 0 56 (@span_join (Z 4) 24 0 32 (@span_join (Z 4) 8 0 16 h4x0 (@span_join (Z 4) 8 8 8 h4x8 h4x16)) (@span_join (Z 4) 16 24 16 (@span_join (Z 4) 8 24 8 h4x24 h4x32) (@span_join (Z 4) 8 40 8 h4x40 h4x48))) (@span_join (Z 4) 24 56 32 (@span_join (Z 4) 8 56 16 h4x56 (@span_join (Z 4) 8 64 8 h4x64 h4x72)) (@span_join (Z 4) 16 80 16 (@span_join (Z 4) 8 80 8 h4x80 h4x88) (@span_join (Z 4) 8 96 8 h4x96 h4x104)))) (@span_join (Z 4) 56 112 63 (@span_join (Z 4) 24 112 32 (@span_join (Z 4) 8 112 16 h4x112 (@span_join (Z 4) 8 120 8 h4x120 h4x128)) (@span_join (Z 4) 16 136 16 (@span_join (Z 4) 8 136 8 h4x136 h4x144) (@span_join (Z 4) 8 152 8 h4x152 h4x160))) (@span_join (Z 4) 32 168 31 (@span_join (Z 4) 16 168 16 (@span_join (Z 4) 8 168 8 h4x168 h4x176) (@span_join (Z 4) 8 184 8 h4x184 h4x192)) (@span_join (Z 4) 16 200 15 (@span_join (Z 4) 8 200 8 h4x200 h4x208) (@span_join (Z 4) 8 216 7 h4x216 h4x224)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x0 : span (Z 5) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x8 : span (Z 5) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x16 : span (Z 5) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x24 : span (Z 5) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x32 : span (Z 5) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x40 : span (Z 5) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x48 : span (Z 5) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x56 : span (Z 5) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x64 : span (Z 5) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x72 : span (Z 5) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x80 : span (Z 5) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x88 : span (Z 5) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x96 : span (Z 5) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x104 : span (Z 5) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x112 : span (Z 5) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x120 : span (Z 5) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x128 : span (Z 5) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x136 : span (Z 5) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x144 : span (Z 5) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x152 : span (Z 5) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x160 : span (Z 5) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x168 : span (Z 5) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x176 : span (Z 5) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x184 : span (Z 5) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x192 : span (Z 5) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x200 : span (Z 5) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x208 : span (Z 5) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x216 : span (Z 5) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x224 : span (Z 5) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x232 : span (Z 5) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x240 : span (Z 5) 8 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x248 : span (Z 5) 8 248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x256 : span (Z 5) 8 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x264 : span (Z 5) 8 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x272 : span (Z 5) 8 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x280 : span (Z 5) 8 280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x288 : span (Z 5) 8 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x296 : span (Z 5) 8 296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x304 : span (Z 5) 8 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x312 : span (Z 5) 8 312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x320 : span (Z 5) 8 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x328 : span (Z 5) 8 328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x336 : span (Z 5) 8 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x344 : span (Z 5) 8 344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x352 : span (Z 5) 8 352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x360 : span (Z 5) 8 360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x368 : span (Z 5) 8 368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x376 : span (Z 5) 8 376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x384 : span (Z 5) 8 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x392 : span (Z 5) 8 392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x400 : span (Z 5) 8 400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x408 : span (Z 5) 8 408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x416 : span (Z 5) 8 416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x424 : span (Z 5) 8 424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x432 : span (Z 5) 8 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x440 : span (Z 5) 8 440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x448 : span (Z 5) 8 448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x456 : span (Z 5) 8 456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x464 : span (Z 5) 8 464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x472 : span (Z 5) 8 472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x480 : span (Z 5) 8 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x488 : span (Z 5) 8 488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x496 : span (Z 5) 8 496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x504 : span (Z 5) 8 504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x512 : span (Z 5) 8 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x520 : span (Z 5) 8 520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x528 : span (Z 5) 8 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x536 : span (Z 5) 8 536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x544 : span (Z 5) 8 544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x552 : span (Z 5) 8 552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x560 : span (Z 5) 8 560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x568 : span (Z 5) 8 568 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x576 : span (Z 5) 8 576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x584 : span (Z 5) 8 584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x592 : span (Z 5) 8 592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x600 : span (Z 5) 8 600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x608 : span (Z 5) 8 608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x616 : span (Z 5) 8 616 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x624 : span (Z 5) 8 624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x632 : span (Z 5) 8 632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x640 : span (Z 5) 8 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x648 : span (Z 5) 8 648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x656 : span (Z 5) 8 656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x664 : span (Z 5) 8 664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x672 : span (Z 5) 8 672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x680 : span (Z 5) 8 680 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x688 : span (Z 5) 8 688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x696 : span (Z 5) 8 696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x704 : span (Z 5) 8 704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x712 : span (Z 5) 8 712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x720 : span (Z 5) 8 720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x728 : span (Z 5) 8 728 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x736 : span (Z 5) 8 736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x744 : span (Z 5) 8 744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x752 : span (Z 5) 8 752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x760 : span (Z 5) 8 760 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x768 : span (Z 5) 8 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x776 : span (Z 5) 8 776 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x784 : span (Z 5) 8 784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x792 : span (Z 5) 8 792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x800 : span (Z 5) 8 800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x808 : span (Z 5) 8 808 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x816 : span (Z 5) 8 816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x824 : span (Z 5) 8 824 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x832 : span (Z 5) 8 832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x840 : span (Z 5) 8 840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x848 : span (Z 5) 8 848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x856 : span (Z 5) 8 856 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x864 : span (Z 5) 8 864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x872 : span (Z 5) 8 872 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x880 : span (Z 5) 8 880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x888 : span (Z 5) 8 888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x896 : span (Z 5) 8 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x904 : span (Z 5) 8 904 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x912 : span (Z 5) 8 912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x920 : span (Z 5) 8 920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x928 : span (Z 5) 8 928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x936 : span (Z 5) 8 936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x944 : span (Z 5) 8 944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x952 : span (Z 5) 8 952 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x960 : span (Z 5) 8 960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x968 : span (Z 5) 8 968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x976 : span (Z 5) 8 976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x984 : span (Z 5) 8 984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x992 : span (Z 5) 8 992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1000 : span (Z 5) 8 1000 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1008 : span (Z 5) 8 1008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1016 : span (Z 5) 8 1016 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1024 : span (Z 5) 8 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1032 : span (Z 5) 8 1032 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1040 : span (Z 5) 8 1040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1048 : span (Z 5) 8 1048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1056 : span (Z 5) 8 1056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1064 : span (Z 5) 8 1064 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1072 : span (Z 5) 8 1072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1080 : span (Z 5) 8 1080 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1088 : span (Z 5) 8 1088 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1096 : span (Z 5) 8 1096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1104 : span (Z 5) 8 1104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1112 : span (Z 5) 8 1112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1120 : span (Z 5) 8 1120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1128 : span (Z 5) 8 1128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1136 : span (Z 5) 8 1136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1144 : span (Z 5) 8 1144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1152 : span (Z 5) 8 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1160 : span (Z 5) 8 1160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1168 : span (Z 5) 8 1168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1176 : span (Z 5) 8 1176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1184 : span (Z 5) 8 1184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1192 : span (Z 5) 8 1192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1200 : span (Z 5) 8 1200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1208 : span (Z 5) 8 1208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1216 : span (Z 5) 8 1216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1224 : span (Z 5) 8 1224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1232 : span (Z 5) 8 1232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1240 : span (Z 5) 8 1240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1248 : span (Z 5) 8 1248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1256 : span (Z 5) 8 1256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1264 : span (Z 5) 8 1264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1272 : span (Z 5) 8 1272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1280 : span (Z 5) 8 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1288 : span (Z 5) 8 1288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1296 : span (Z 5) 8 1296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1304 : span (Z 5) 8 1304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1312 : span (Z 5) 8 1312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1320 : span (Z 5) 8 1320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1328 : span (Z 5) 8 1328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1336 : span (Z 5) 8 1336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1344 : span (Z 5) 8 1344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1352 : span (Z 5) 8 1352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1360 : span (Z 5) 8 1360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1368 : span (Z 5) 8 1368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1376 : span (Z 5) 8 1376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1384 : span (Z 5) 8 1384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1392 : span (Z 5) 8 1392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1400 : span (Z 5) 8 1400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1408 : span (Z 5) 8 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1416 : span (Z 5) 8 1416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1424 : span (Z 5) 8 1424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1432 : span (Z 5) 8 1432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1440 : span (Z 5) 8 1440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1448 : span (Z 5) 8 1448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1456 : span (Z 5) 8 1456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1464 : span (Z 5) 8 1464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1472 : span (Z 5) 8 1472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1480 : span (Z 5) 8 1480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1488 : span (Z 5) 8 1488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1496 : span (Z 5) 8 1496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1504 : span (Z 5) 8 1504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1512 : span (Z 5) 8 1512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1520 : span (Z 5) 8 1520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1528 : span (Z 5) 8 1528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1536 : span (Z 5) 8 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1544 : span (Z 5) 8 1544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1552 : span (Z 5) 8 1552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1560 : span (Z 5) 8 1560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1568 : span (Z 5) 8 1568 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1576 : span (Z 5) 8 1576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1584 : span (Z 5) 8 1584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1592 : span (Z 5) 8 1592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1600 : span (Z 5) 8 1600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1608 : span (Z 5) 8 1608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1616 : span (Z 5) 8 1616 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1624 : span (Z 5) 8 1624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1632 : span (Z 5) 8 1632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1640 : span (Z 5) 1 1640 = true := by decide +kernel
theorem z5 : span (Z 5) 1641 0 = true := (@span_join (Z 5) 824 0 817 (@span_join (Z 5) 408 0 416 (@span_join (Z 5) 200 0 208 (@span_join (Z 5) 96 0 104 (@span_join (Z 5) 48 0 48 (@span_join (Z 5) 24 0 24 (@span_join (Z 5) 8 0 16 h5x0 (@span_join (Z 5) 8 8 8 h5x8 h5x16)) (@span_join (Z 5) 8 24 16 h5x24 (@span_join (Z 5) 8 32 8 h5x32 h5x40))) (@span_join (Z 5) 24 48 24 (@span_join (Z 5) 8 48 16 h5x48 (@span_join (Z 5) 8 56 8 h5x56 h5x64)) (@span_join (Z 5) 8 72 16 h5x72 (@span_join (Z 5) 8 80 8 h5x80 h5x88)))) (@span_join (Z 5) 48 96 56 (@span_join (Z 5) 24 96 24 (@span_join (Z 5) 8 96 16 h5x96 (@span_join (Z 5) 8 104 8 h5x104 h5x112)) (@span_join (Z 5) 8 120 16 h5x120 (@span_join (Z 5) 8 128 8 h5x128 h5x136))) (@span_join (Z 5) 24 144 32 (@span_join (Z 5) 8 144 16 h5x144 (@span_join (Z 5) 8 152 8 h5x152 h5x160)) (@span_join (Z 5) 16 168 16 (@span_join (Z 5) 8 168 8 h5x168 h5x176) (@span_join (Z 5) 8 184 8 h5x184 h5x192))))) (@span_join (Z 5) 104 200 104 (@span_join (Z 5) 48 200 56 (@span_join (Z 5) 24 200 24 (@span_join (Z 5) 8 200 16 h5x200 (@span_join (Z 5) 8 208 8 h5x208 h5x216)) (@span_join (Z 5) 8 224 16 h5x224 (@span_join (Z 5) 8 232 8 h5x232 h5x240))) (@span_join (Z 5) 24 248 32 (@span_join (Z 5) 8 248 16 h5x248 (@span_join (Z 5) 8 256 8 h5x256 h5x264)) (@span_join (Z 5) 16 272 16 (@span_join (Z 5) 8 272 8 h5x272 h5x280) (@span_join (Z 5) 8 288 8 h5x288 h5x296)))) (@span_join (Z 5) 48 304 56 (@span_join (Z 5) 24 304 24 (@span_join (Z 5) 8 304 16 h5x304 (@span_join (Z 5) 8 312 8 h5x312 h5x320)) (@span_join (Z 5) 8 328 16 h5x328 (@span_join (Z 5) 8 336 8 h5x336 h5x344))) (@span_join (Z 5) 24 352 32 (@span_join (Z 5) 8 352 16 h5x352 (@span_join (Z 5) 8 360 8 h5x360 h5x368)) (@span_join (Z 5) 16 376 16 (@span_join (Z 5) 8 376 8 h5x376 h5x384) (@span_join (Z 5) 8 392 8 h5x392 h5x400)))))) (@span_join (Z 5) 208 408 208 (@span_join (Z 5) 104 408 104 (@span_join (Z 5) 48 408 56 (@span_join (Z 5) 24 408 24 (@span_join (Z 5) 8 408 16 h5x408 (@span_join (Z 5) 8 416 8 h5x416 h5x424)) (@span_join (Z 5) 8 432 16 h5x432 (@span_join (Z 5) 8 440 8 h5x440 h5x448))) (@span_join (Z 5) 24 456 32 (@span_join (Z 5) 8 456 16 h5x456 (@span_join (Z 5) 8 464 8 h5x464 h5x472)) (@span_join (Z 5) 16 480 16 (@span_join (Z 5) 8 480 8 h5x480 h5x488) (@span_join (Z 5) 8 496 8 h5x496 h5x504)))) (@span_join (Z 5) 48 512 56 (@span_join (Z 5) 24 512 24 (@span_join (Z 5) 8 512 16 h5x512 (@span_join (Z 5) 8 520 8 h5x520 h5x528)) (@span_join (Z 5) 8 536 16 h5x536 (@span_join (Z 5) 8 544 8 h5x544 h5x552))) (@span_join (Z 5) 24 560 32 (@span_join (Z 5) 8 560 16 h5x560 (@span_join (Z 5) 8 568 8 h5x568 h5x576)) (@span_join (Z 5) 16 584 16 (@span_join (Z 5) 8 584 8 h5x584 h5x592) (@span_join (Z 5) 8 600 8 h5x600 h5x608))))) (@span_join (Z 5) 104 616 104 (@span_join (Z 5) 48 616 56 (@span_join (Z 5) 24 616 24 (@span_join (Z 5) 8 616 16 h5x616 (@span_join (Z 5) 8 624 8 h5x624 h5x632)) (@span_join (Z 5) 8 640 16 h5x640 (@span_join (Z 5) 8 648 8 h5x648 h5x656))) (@span_join (Z 5) 24 664 32 (@span_join (Z 5) 8 664 16 h5x664 (@span_join (Z 5) 8 672 8 h5x672 h5x680)) (@span_join (Z 5) 16 688 16 (@span_join (Z 5) 8 688 8 h5x688 h5x696) (@span_join (Z 5) 8 704 8 h5x704 h5x712)))) (@span_join (Z 5) 48 720 56 (@span_join (Z 5) 24 720 24 (@span_join (Z 5) 8 720 16 h5x720 (@span_join (Z 5) 8 728 8 h5x728 h5x736)) (@span_join (Z 5) 8 744 16 h5x744 (@span_join (Z 5) 8 752 8 h5x752 h5x760))) (@span_join (Z 5) 24 768 32 (@span_join (Z 5) 8 768 16 h5x768 (@span_join (Z 5) 8 776 8 h5x776 h5x784)) (@span_join (Z 5) 16 792 16 (@span_join (Z 5) 8 792 8 h5x792 h5x800) (@span_join (Z 5) 8 808 8 h5x808 h5x816))))))) (@span_join (Z 5) 408 824 409 (@span_join (Z 5) 200 824 208 (@span_join (Z 5) 96 824 104 (@span_join (Z 5) 48 824 48 (@span_join (Z 5) 24 824 24 (@span_join (Z 5) 8 824 16 h5x824 (@span_join (Z 5) 8 832 8 h5x832 h5x840)) (@span_join (Z 5) 8 848 16 h5x848 (@span_join (Z 5) 8 856 8 h5x856 h5x864))) (@span_join (Z 5) 24 872 24 (@span_join (Z 5) 8 872 16 h5x872 (@span_join (Z 5) 8 880 8 h5x880 h5x888)) (@span_join (Z 5) 8 896 16 h5x896 (@span_join (Z 5) 8 904 8 h5x904 h5x912)))) (@span_join (Z 5) 48 920 56 (@span_join (Z 5) 24 920 24 (@span_join (Z 5) 8 920 16 h5x920 (@span_join (Z 5) 8 928 8 h5x928 h5x936)) (@span_join (Z 5) 8 944 16 h5x944 (@span_join (Z 5) 8 952 8 h5x952 h5x960))) (@span_join (Z 5) 24 968 32 (@span_join (Z 5) 8 968 16 h5x968 (@span_join (Z 5) 8 976 8 h5x976 h5x984)) (@span_join (Z 5) 16 992 16 (@span_join (Z 5) 8 992 8 h5x992 h5x1000) (@span_join (Z 5) 8 1008 8 h5x1008 h5x1016))))) (@span_join (Z 5) 104 1024 104 (@span_join (Z 5) 48 1024 56 (@span_join (Z 5) 24 1024 24 (@span_join (Z 5) 8 1024 16 h5x1024 (@span_join (Z 5) 8 1032 8 h5x1032 h5x1040)) (@span_join (Z 5) 8 1048 16 h5x1048 (@span_join (Z 5) 8 1056 8 h5x1056 h5x1064))) (@span_join (Z 5) 24 1072 32 (@span_join (Z 5) 8 1072 16 h5x1072 (@span_join (Z 5) 8 1080 8 h5x1080 h5x1088)) (@span_join (Z 5) 16 1096 16 (@span_join (Z 5) 8 1096 8 h5x1096 h5x1104) (@span_join (Z 5) 8 1112 8 h5x1112 h5x1120)))) (@span_join (Z 5) 48 1128 56 (@span_join (Z 5) 24 1128 24 (@span_join (Z 5) 8 1128 16 h5x1128 (@span_join (Z 5) 8 1136 8 h5x1136 h5x1144)) (@span_join (Z 5) 8 1152 16 h5x1152 (@span_join (Z 5) 8 1160 8 h5x1160 h5x1168))) (@span_join (Z 5) 24 1176 32 (@span_join (Z 5) 8 1176 16 h5x1176 (@span_join (Z 5) 8 1184 8 h5x1184 h5x1192)) (@span_join (Z 5) 16 1200 16 (@span_join (Z 5) 8 1200 8 h5x1200 h5x1208) (@span_join (Z 5) 8 1216 8 h5x1216 h5x1224)))))) (@span_join (Z 5) 208 1232 201 (@span_join (Z 5) 104 1232 104 (@span_join (Z 5) 48 1232 56 (@span_join (Z 5) 24 1232 24 (@span_join (Z 5) 8 1232 16 h5x1232 (@span_join (Z 5) 8 1240 8 h5x1240 h5x1248)) (@span_join (Z 5) 8 1256 16 h5x1256 (@span_join (Z 5) 8 1264 8 h5x1264 h5x1272))) (@span_join (Z 5) 24 1280 32 (@span_join (Z 5) 8 1280 16 h5x1280 (@span_join (Z 5) 8 1288 8 h5x1288 h5x1296)) (@span_join (Z 5) 16 1304 16 (@span_join (Z 5) 8 1304 8 h5x1304 h5x1312) (@span_join (Z 5) 8 1320 8 h5x1320 h5x1328)))) (@span_join (Z 5) 48 1336 56 (@span_join (Z 5) 24 1336 24 (@span_join (Z 5) 8 1336 16 h5x1336 (@span_join (Z 5) 8 1344 8 h5x1344 h5x1352)) (@span_join (Z 5) 8 1360 16 h5x1360 (@span_join (Z 5) 8 1368 8 h5x1368 h5x1376))) (@span_join (Z 5) 24 1384 32 (@span_join (Z 5) 8 1384 16 h5x1384 (@span_join (Z 5) 8 1392 8 h5x1392 h5x1400)) (@span_join (Z 5) 16 1408 16 (@span_join (Z 5) 8 1408 8 h5x1408 h5x1416) (@span_join (Z 5) 8 1424 8 h5x1424 h5x1432))))) (@span_join (Z 5) 104 1440 97 (@span_join (Z 5) 48 1440 56 (@span_join (Z 5) 24 1440 24 (@span_join (Z 5) 8 1440 16 h5x1440 (@span_join (Z 5) 8 1448 8 h5x1448 h5x1456)) (@span_join (Z 5) 8 1464 16 h5x1464 (@span_join (Z 5) 8 1472 8 h5x1472 h5x1480))) (@span_join (Z 5) 24 1488 32 (@span_join (Z 5) 8 1488 16 h5x1488 (@span_join (Z 5) 8 1496 8 h5x1496 h5x1504)) (@span_join (Z 5) 16 1512 16 (@span_join (Z 5) 8 1512 8 h5x1512 h5x1520) (@span_join (Z 5) 8 1528 8 h5x1528 h5x1536)))) (@span_join (Z 5) 48 1544 49 (@span_join (Z 5) 24 1544 24 (@span_join (Z 5) 8 1544 16 h5x1544 (@span_join (Z 5) 8 1552 8 h5x1552 h5x1560)) (@span_join (Z 5) 8 1568 16 h5x1568 (@span_join (Z 5) 8 1576 8 h5x1576 h5x1584))) (@span_join (Z 5) 24 1592 25 (@span_join (Z 5) 8 1592 16 h5x1592 (@span_join (Z 5) 8 1600 8 h5x1600 h5x1608)) (@span_join (Z 5) 16 1616 9 (@span_join (Z 5) 8 1616 8 h5x1616 h5x1624) (@span_join (Z 5) 8 1632 1 h5x1632 h5x1640))))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x0 : span (Z 6) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x8 : span (Z 6) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x16 : span (Z 6) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x24 : span (Z 6) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x32 : span (Z 6) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x40 : span (Z 6) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x48 : span (Z 6) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x56 : span (Z 6) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x64 : span (Z 6) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x72 : span (Z 6) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x80 : span (Z 6) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x88 : span (Z 6) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x96 : span (Z 6) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x104 : span (Z 6) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x112 : span (Z 6) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x120 : span (Z 6) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x128 : span (Z 6) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x136 : span (Z 6) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x144 : span (Z 6) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x152 : span (Z 6) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x160 : span (Z 6) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x168 : span (Z 6) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x176 : span (Z 6) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x184 : span (Z 6) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x192 : span (Z 6) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x200 : span (Z 6) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x208 : span (Z 6) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x216 : span (Z 6) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x224 : span (Z 6) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x232 : span (Z 6) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x240 : span (Z 6) 8 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x248 : span (Z 6) 8 248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x256 : span (Z 6) 8 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x264 : span (Z 6) 8 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x272 : span (Z 6) 8 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x280 : span (Z 6) 8 280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x288 : span (Z 6) 8 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x296 : span (Z 6) 8 296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x304 : span (Z 6) 8 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x312 : span (Z 6) 8 312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x320 : span (Z 6) 8 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x328 : span (Z 6) 8 328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x336 : span (Z 6) 8 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x344 : span (Z 6) 8 344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x352 : span (Z 6) 8 352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x360 : span (Z 6) 8 360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x368 : span (Z 6) 8 368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x376 : span (Z 6) 8 376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x384 : span (Z 6) 8 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x392 : span (Z 6) 8 392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x400 : span (Z 6) 8 400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x408 : span (Z 6) 8 408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x416 : span (Z 6) 8 416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x424 : span (Z 6) 8 424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x432 : span (Z 6) 8 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x440 : span (Z 6) 8 440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x448 : span (Z 6) 8 448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x456 : span (Z 6) 8 456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x464 : span (Z 6) 8 464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x472 : span (Z 6) 8 472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x480 : span (Z 6) 8 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x488 : span (Z 6) 8 488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x496 : span (Z 6) 8 496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x504 : span (Z 6) 8 504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x512 : span (Z 6) 8 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x520 : span (Z 6) 8 520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x528 : span (Z 6) 8 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x536 : span (Z 6) 8 536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x544 : span (Z 6) 8 544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x552 : span (Z 6) 8 552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x560 : span (Z 6) 8 560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x568 : span (Z 6) 8 568 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x576 : span (Z 6) 8 576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x584 : span (Z 6) 8 584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x592 : span (Z 6) 8 592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x600 : span (Z 6) 8 600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x608 : span (Z 6) 8 608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x616 : span (Z 6) 8 616 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x624 : span (Z 6) 8 624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x632 : span (Z 6) 8 632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x640 : span (Z 6) 8 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x648 : span (Z 6) 8 648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x656 : span (Z 6) 8 656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x664 : span (Z 6) 8 664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x672 : span (Z 6) 8 672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x680 : span (Z 6) 8 680 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x688 : span (Z 6) 8 688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x696 : span (Z 6) 8 696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x704 : span (Z 6) 8 704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x712 : span (Z 6) 8 712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x720 : span (Z 6) 8 720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x728 : span (Z 6) 8 728 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x736 : span (Z 6) 8 736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x744 : span (Z 6) 8 744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x752 : span (Z 6) 8 752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x760 : span (Z 6) 8 760 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x768 : span (Z 6) 8 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x776 : span (Z 6) 8 776 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x784 : span (Z 6) 8 784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x792 : span (Z 6) 8 792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x800 : span (Z 6) 8 800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x808 : span (Z 6) 8 808 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x816 : span (Z 6) 8 816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x824 : span (Z 6) 8 824 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x832 : span (Z 6) 8 832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x840 : span (Z 6) 8 840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x848 : span (Z 6) 8 848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x856 : span (Z 6) 8 856 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x864 : span (Z 6) 8 864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x872 : span (Z 6) 8 872 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x880 : span (Z 6) 8 880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x888 : span (Z 6) 8 888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x896 : span (Z 6) 8 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x904 : span (Z 6) 8 904 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x912 : span (Z 6) 8 912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x920 : span (Z 6) 8 920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x928 : span (Z 6) 8 928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x936 : span (Z 6) 8 936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x944 : span (Z 6) 8 944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x952 : span (Z 6) 8 952 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x960 : span (Z 6) 8 960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x968 : span (Z 6) 8 968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x976 : span (Z 6) 8 976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x984 : span (Z 6) 8 984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x992 : span (Z 6) 8 992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1000 : span (Z 6) 8 1000 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1008 : span (Z 6) 8 1008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1016 : span (Z 6) 8 1016 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1024 : span (Z 6) 8 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1032 : span (Z 6) 8 1032 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1040 : span (Z 6) 8 1040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1048 : span (Z 6) 8 1048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1056 : span (Z 6) 8 1056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1064 : span (Z 6) 8 1064 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1072 : span (Z 6) 8 1072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1080 : span (Z 6) 8 1080 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1088 : span (Z 6) 8 1088 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1096 : span (Z 6) 8 1096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1104 : span (Z 6) 8 1104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1112 : span (Z 6) 8 1112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1120 : span (Z 6) 8 1120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1128 : span (Z 6) 8 1128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1136 : span (Z 6) 8 1136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1144 : span (Z 6) 8 1144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1152 : span (Z 6) 8 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1160 : span (Z 6) 8 1160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1168 : span (Z 6) 8 1168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1176 : span (Z 6) 8 1176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1184 : span (Z 6) 8 1184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1192 : span (Z 6) 8 1192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1200 : span (Z 6) 8 1200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1208 : span (Z 6) 8 1208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1216 : span (Z 6) 8 1216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1224 : span (Z 6) 8 1224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1232 : span (Z 6) 8 1232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1240 : span (Z 6) 8 1240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1248 : span (Z 6) 8 1248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1256 : span (Z 6) 8 1256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1264 : span (Z 6) 8 1264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1272 : span (Z 6) 8 1272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1280 : span (Z 6) 8 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1288 : span (Z 6) 8 1288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1296 : span (Z 6) 8 1296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1304 : span (Z 6) 8 1304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1312 : span (Z 6) 8 1312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1320 : span (Z 6) 8 1320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1328 : span (Z 6) 8 1328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1336 : span (Z 6) 8 1336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1344 : span (Z 6) 8 1344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1352 : span (Z 6) 8 1352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1360 : span (Z 6) 8 1360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1368 : span (Z 6) 8 1368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1376 : span (Z 6) 8 1376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1384 : span (Z 6) 8 1384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1392 : span (Z 6) 8 1392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1400 : span (Z 6) 8 1400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1408 : span (Z 6) 8 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1416 : span (Z 6) 8 1416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1424 : span (Z 6) 8 1424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1432 : span (Z 6) 8 1432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1440 : span (Z 6) 8 1440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1448 : span (Z 6) 8 1448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1456 : span (Z 6) 8 1456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1464 : span (Z 6) 8 1464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1472 : span (Z 6) 8 1472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1480 : span (Z 6) 8 1480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1488 : span (Z 6) 8 1488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1496 : span (Z 6) 8 1496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1504 : span (Z 6) 8 1504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1512 : span (Z 6) 8 1512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1520 : span (Z 6) 8 1520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1528 : span (Z 6) 8 1528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1536 : span (Z 6) 8 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1544 : span (Z 6) 8 1544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1552 : span (Z 6) 8 1552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1560 : span (Z 6) 8 1560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1568 : span (Z 6) 8 1568 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1576 : span (Z 6) 8 1576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1584 : span (Z 6) 8 1584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1592 : span (Z 6) 8 1592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1600 : span (Z 6) 8 1600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1608 : span (Z 6) 8 1608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1616 : span (Z 6) 8 1616 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1624 : span (Z 6) 8 1624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1632 : span (Z 6) 8 1632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1640 : span (Z 6) 8 1640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1648 : span (Z 6) 8 1648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1656 : span (Z 6) 8 1656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1664 : span (Z 6) 8 1664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1672 : span (Z 6) 8 1672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1680 : span (Z 6) 8 1680 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1688 : span (Z 6) 8 1688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1696 : span (Z 6) 8 1696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1704 : span (Z 6) 8 1704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1712 : span (Z 6) 8 1712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1720 : span (Z 6) 8 1720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1728 : span (Z 6) 8 1728 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1736 : span (Z 6) 8 1736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1744 : span (Z 6) 8 1744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1752 : span (Z 6) 8 1752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1760 : span (Z 6) 8 1760 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1768 : span (Z 6) 8 1768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1776 : span (Z 6) 8 1776 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1784 : span (Z 6) 8 1784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1792 : span (Z 6) 8 1792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1800 : span (Z 6) 8 1800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1808 : span (Z 6) 8 1808 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1816 : span (Z 6) 8 1816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1824 : span (Z 6) 8 1824 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1832 : span (Z 6) 8 1832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1840 : span (Z 6) 8 1840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1848 : span (Z 6) 8 1848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1856 : span (Z 6) 8 1856 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1864 : span (Z 6) 8 1864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1872 : span (Z 6) 8 1872 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1880 : span (Z 6) 8 1880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1888 : span (Z 6) 8 1888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1896 : span (Z 6) 8 1896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1904 : span (Z 6) 8 1904 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1912 : span (Z 6) 8 1912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1920 : span (Z 6) 8 1920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1928 : span (Z 6) 8 1928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1936 : span (Z 6) 8 1936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1944 : span (Z 6) 8 1944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1952 : span (Z 6) 8 1952 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1960 : span (Z 6) 8 1960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1968 : span (Z 6) 8 1968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1976 : span (Z 6) 8 1976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1984 : span (Z 6) 8 1984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x1992 : span (Z 6) 8 1992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2000 : span (Z 6) 8 2000 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2008 : span (Z 6) 8 2008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2016 : span (Z 6) 8 2016 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2024 : span (Z 6) 8 2024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2032 : span (Z 6) 8 2032 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2040 : span (Z 6) 8 2040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2048 : span (Z 6) 8 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2056 : span (Z 6) 8 2056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2064 : span (Z 6) 8 2064 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2072 : span (Z 6) 8 2072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2080 : span (Z 6) 8 2080 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2088 : span (Z 6) 8 2088 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2096 : span (Z 6) 8 2096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2104 : span (Z 6) 8 2104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2112 : span (Z 6) 8 2112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2120 : span (Z 6) 8 2120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2128 : span (Z 6) 8 2128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2136 : span (Z 6) 8 2136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2144 : span (Z 6) 8 2144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2152 : span (Z 6) 8 2152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2160 : span (Z 6) 8 2160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2168 : span (Z 6) 8 2168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2176 : span (Z 6) 8 2176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2184 : span (Z 6) 8 2184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2192 : span (Z 6) 8 2192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2200 : span (Z 6) 8 2200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2208 : span (Z 6) 8 2208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2216 : span (Z 6) 8 2216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2224 : span (Z 6) 8 2224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2232 : span (Z 6) 8 2232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2240 : span (Z 6) 8 2240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2248 : span (Z 6) 8 2248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2256 : span (Z 6) 8 2256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2264 : span (Z 6) 8 2264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2272 : span (Z 6) 8 2272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2280 : span (Z 6) 8 2280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2288 : span (Z 6) 8 2288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2296 : span (Z 6) 8 2296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2304 : span (Z 6) 8 2304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2312 : span (Z 6) 8 2312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2320 : span (Z 6) 8 2320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2328 : span (Z 6) 8 2328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2336 : span (Z 6) 8 2336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2344 : span (Z 6) 8 2344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2352 : span (Z 6) 8 2352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2360 : span (Z 6) 8 2360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2368 : span (Z 6) 8 2368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2376 : span (Z 6) 8 2376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2384 : span (Z 6) 8 2384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2392 : span (Z 6) 8 2392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2400 : span (Z 6) 8 2400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2408 : span (Z 6) 8 2408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2416 : span (Z 6) 8 2416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2424 : span (Z 6) 8 2424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2432 : span (Z 6) 8 2432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2440 : span (Z 6) 8 2440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2448 : span (Z 6) 8 2448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2456 : span (Z 6) 8 2456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2464 : span (Z 6) 8 2464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2472 : span (Z 6) 8 2472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2480 : span (Z 6) 8 2480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2488 : span (Z 6) 8 2488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2496 : span (Z 6) 8 2496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2504 : span (Z 6) 8 2504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2512 : span (Z 6) 8 2512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2520 : span (Z 6) 8 2520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2528 : span (Z 6) 8 2528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2536 : span (Z 6) 8 2536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2544 : span (Z 6) 8 2544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2552 : span (Z 6) 8 2552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2560 : span (Z 6) 8 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2568 : span (Z 6) 8 2568 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2576 : span (Z 6) 8 2576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2584 : span (Z 6) 8 2584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2592 : span (Z 6) 8 2592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2600 : span (Z 6) 8 2600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2608 : span (Z 6) 8 2608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2616 : span (Z 6) 8 2616 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2624 : span (Z 6) 8 2624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2632 : span (Z 6) 8 2632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2640 : span (Z 6) 8 2640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2648 : span (Z 6) 8 2648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2656 : span (Z 6) 8 2656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2664 : span (Z 6) 8 2664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2672 : span (Z 6) 8 2672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2680 : span (Z 6) 8 2680 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2688 : span (Z 6) 8 2688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2696 : span (Z 6) 8 2696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2704 : span (Z 6) 8 2704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2712 : span (Z 6) 8 2712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2720 : span (Z 6) 8 2720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2728 : span (Z 6) 8 2728 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2736 : span (Z 6) 8 2736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2744 : span (Z 6) 8 2744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2752 : span (Z 6) 8 2752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2760 : span (Z 6) 8 2760 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2768 : span (Z 6) 8 2768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2776 : span (Z 6) 8 2776 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2784 : span (Z 6) 8 2784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2792 : span (Z 6) 8 2792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2800 : span (Z 6) 8 2800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2808 : span (Z 6) 8 2808 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2816 : span (Z 6) 8 2816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2824 : span (Z 6) 8 2824 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2832 : span (Z 6) 8 2832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2840 : span (Z 6) 8 2840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2848 : span (Z 6) 8 2848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2856 : span (Z 6) 8 2856 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2864 : span (Z 6) 8 2864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2872 : span (Z 6) 8 2872 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2880 : span (Z 6) 8 2880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2888 : span (Z 6) 8 2888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2896 : span (Z 6) 8 2896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2904 : span (Z 6) 8 2904 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2912 : span (Z 6) 8 2912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2920 : span (Z 6) 8 2920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2928 : span (Z 6) 8 2928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2936 : span (Z 6) 8 2936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2944 : span (Z 6) 8 2944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2952 : span (Z 6) 8 2952 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2960 : span (Z 6) 8 2960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2968 : span (Z 6) 8 2968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2976 : span (Z 6) 8 2976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2984 : span (Z 6) 8 2984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x2992 : span (Z 6) 8 2992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3000 : span (Z 6) 8 3000 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3008 : span (Z 6) 8 3008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3016 : span (Z 6) 8 3016 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3024 : span (Z 6) 8 3024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3032 : span (Z 6) 8 3032 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3040 : span (Z 6) 8 3040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3048 : span (Z 6) 8 3048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3056 : span (Z 6) 8 3056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3064 : span (Z 6) 8 3064 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3072 : span (Z 6) 8 3072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3080 : span (Z 6) 8 3080 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3088 : span (Z 6) 8 3088 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3096 : span (Z 6) 8 3096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3104 : span (Z 6) 8 3104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3112 : span (Z 6) 8 3112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3120 : span (Z 6) 8 3120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3128 : span (Z 6) 8 3128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3136 : span (Z 6) 8 3136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3144 : span (Z 6) 8 3144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3152 : span (Z 6) 7 3152 = true := by decide +kernel
theorem z6 : span (Z 6) 3159 0 = true := (@span_join (Z 6) 1576 0 1583 (@span_join (Z 6) 784 0 792 (@span_join (Z 6) 392 0 392 (@span_join (Z 6) 192 0 200 (@span_join (Z 6) 96 0 96 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 8 0 16 h6x0 (@span_join (Z 6) 8 8 8 h6x8 h6x16)) (@span_join (Z 6) 8 24 16 h6x24 (@span_join (Z 6) 8 32 8 h6x32 h6x40))) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 8 48 16 h6x48 (@span_join (Z 6) 8 56 8 h6x56 h6x64)) (@span_join (Z 6) 8 72 16 h6x72 (@span_join (Z 6) 8 80 8 h6x80 h6x88)))) (@span_join (Z 6) 48 96 48 (@span_join (Z 6) 24 96 24 (@span_join (Z 6) 8 96 16 h6x96 (@span_join (Z 6) 8 104 8 h6x104 h6x112)) (@span_join (Z 6) 8 120 16 h6x120 (@span_join (Z 6) 8 128 8 h6x128 h6x136))) (@span_join (Z 6) 24 144 24 (@span_join (Z 6) 8 144 16 h6x144 (@span_join (Z 6) 8 152 8 h6x152 h6x160)) (@span_join (Z 6) 8 168 16 h6x168 (@span_join (Z 6) 8 176 8 h6x176 h6x184))))) (@span_join (Z 6) 96 192 104 (@span_join (Z 6) 48 192 48 (@span_join (Z 6) 24 192 24 (@span_join (Z 6) 8 192 16 h6x192 (@span_join (Z 6) 8 200 8 h6x200 h6x208)) (@span_join (Z 6) 8 216 16 h6x216 (@span_join (Z 6) 8 224 8 h6x224 h6x232))) (@span_join (Z 6) 24 240 24 (@span_join (Z 6) 8 240 16 h6x240 (@span_join (Z 6) 8 248 8 h6x248 h6x256)) (@span_join (Z 6) 8 264 16 h6x264 (@span_join (Z 6) 8 272 8 h6x272 h6x280)))) (@span_join (Z 6) 48 288 56 (@span_join (Z 6) 24 288 24 (@span_join (Z 6) 8 288 16 h6x288 (@span_join (Z 6) 8 296 8 h6x296 h6x304)) (@span_join (Z 6) 8 312 16 h6x312 (@span_join (Z 6) 8 320 8 h6x320 h6x328))) (@span_join (Z 6) 24 336 32 (@span_join (Z 6) 8 336 16 h6x336 (@span_join (Z 6) 8 344 8 h6x344 h6x352)) (@span_join (Z 6) 16 360 16 (@span_join (Z 6) 8 360 8 h6x360 h6x368) (@span_join (Z 6) 8 376 8 h6x376 h6x384)))))) (@span_join (Z 6) 192 392 200 (@span_join (Z 6) 96 392 96 (@span_join (Z 6) 48 392 48 (@span_join (Z 6) 24 392 24 (@span_join (Z 6) 8 392 16 h6x392 (@span_join (Z 6) 8 400 8 h6x400 h6x408)) (@span_join (Z 6) 8 416 16 h6x416 (@span_join (Z 6) 8 424 8 h6x424 h6x432))) (@span_join (Z 6) 24 440 24 (@span_join (Z 6) 8 440 16 h6x440 (@span_join (Z 6) 8 448 8 h6x448 h6x456)) (@span_join (Z 6) 8 464 16 h6x464 (@span_join (Z 6) 8 472 8 h6x472 h6x480)))) (@span_join (Z 6) 48 488 48 (@span_join (Z 6) 24 488 24 (@span_join (Z 6) 8 488 16 h6x488 (@span_join (Z 6) 8 496 8 h6x496 h6x504)) (@span_join (Z 6) 8 512 16 h6x512 (@span_join (Z 6) 8 520 8 h6x520 h6x528))) (@span_join (Z 6) 24 536 24 (@span_join (Z 6) 8 536 16 h6x536 (@span_join (Z 6) 8 544 8 h6x544 h6x552)) (@span_join (Z 6) 8 560 16 h6x560 (@span_join (Z 6) 8 568 8 h6x568 h6x576))))) (@span_join (Z 6) 96 584 104 (@span_join (Z 6) 48 584 48 (@span_join (Z 6) 24 584 24 (@span_join (Z 6) 8 584 16 h6x584 (@span_join (Z 6) 8 592 8 h6x592 h6x600)) (@span_join (Z 6) 8 608 16 h6x608 (@span_join (Z 6) 8 616 8 h6x616 h6x624))) (@span_join (Z 6) 24 632 24 (@span_join (Z 6) 8 632 16 h6x632 (@span_join (Z 6) 8 640 8 h6x640 h6x648)) (@span_join (Z 6) 8 656 16 h6x656 (@span_join (Z 6) 8 664 8 h6x664 h6x672)))) (@span_join (Z 6) 48 680 56 (@span_join (Z 6) 24 680 24 (@span_join (Z 6) 8 680 16 h6x680 (@span_join (Z 6) 8 688 8 h6x688 h6x696)) (@span_join (Z 6) 8 704 16 h6x704 (@span_join (Z 6) 8 712 8 h6x712 h6x720))) (@span_join (Z 6) 24 728 32 (@span_join (Z 6) 8 728 16 h6x728 (@span_join (Z 6) 8 736 8 h6x736 h6x744)) (@span_join (Z 6) 16 752 16 (@span_join (Z 6) 8 752 8 h6x752 h6x760) (@span_join (Z 6) 8 768 8 h6x768 h6x776))))))) (@span_join (Z 6) 392 784 400 (@span_join (Z 6) 192 784 200 (@span_join (Z 6) 96 784 96 (@span_join (Z 6) 48 784 48 (@span_join (Z 6) 24 784 24 (@span_join (Z 6) 8 784 16 h6x784 (@span_join (Z 6) 8 792 8 h6x792 h6x800)) (@span_join (Z 6) 8 808 16 h6x808 (@span_join (Z 6) 8 816 8 h6x816 h6x824))) (@span_join (Z 6) 24 832 24 (@span_join (Z 6) 8 832 16 h6x832 (@span_join (Z 6) 8 840 8 h6x840 h6x848)) (@span_join (Z 6) 8 856 16 h6x856 (@span_join (Z 6) 8 864 8 h6x864 h6x872)))) (@span_join (Z 6) 48 880 48 (@span_join (Z 6) 24 880 24 (@span_join (Z 6) 8 880 16 h6x880 (@span_join (Z 6) 8 888 8 h6x888 h6x896)) (@span_join (Z 6) 8 904 16 h6x904 (@span_join (Z 6) 8 912 8 h6x912 h6x920))) (@span_join (Z 6) 24 928 24 (@span_join (Z 6) 8 928 16 h6x928 (@span_join (Z 6) 8 936 8 h6x936 h6x944)) (@span_join (Z 6) 8 952 16 h6x952 (@span_join (Z 6) 8 960 8 h6x960 h6x968))))) (@span_join (Z 6) 96 976 104 (@span_join (Z 6) 48 976 48 (@span_join (Z 6) 24 976 24 (@span_join (Z 6) 8 976 16 h6x976 (@span_join (Z 6) 8 984 8 h6x984 h6x992)) (@span_join (Z 6) 8 1000 16 h6x1000 (@span_join (Z 6) 8 1008 8 h6x1008 h6x1016))) (@span_join (Z 6) 24 1024 24 (@span_join (Z 6) 8 1024 16 h6x1024 (@span_join (Z 6) 8 1032 8 h6x1032 h6x1040)) (@span_join (Z 6) 8 1048 16 h6x1048 (@span_join (Z 6) 8 1056 8 h6x1056 h6x1064)))) (@span_join (Z 6) 48 1072 56 (@span_join (Z 6) 24 1072 24 (@span_join (Z 6) 8 1072 16 h6x1072 (@span_join (Z 6) 8 1080 8 h6x1080 h6x1088)) (@span_join (Z 6) 8 1096 16 h6x1096 (@span_join (Z 6) 8 1104 8 h6x1104 h6x1112))) (@span_join (Z 6) 24 1120 32 (@span_join (Z 6) 8 1120 16 h6x1120 (@span_join (Z 6) 8 1128 8 h6x1128 h6x1136)) (@span_join (Z 6) 16 1144 16 (@span_join (Z 6) 8 1144 8 h6x1144 h6x1152) (@span_join (Z 6) 8 1160 8 h6x1160 h6x1168)))))) (@span_join (Z 6) 200 1176 200 (@span_join (Z 6) 96 1176 104 (@span_join (Z 6) 48 1176 48 (@span_join (Z 6) 24 1176 24 (@span_join (Z 6) 8 1176 16 h6x1176 (@span_join (Z 6) 8 1184 8 h6x1184 h6x1192)) (@span_join (Z 6) 8 1200 16 h6x1200 (@span_join (Z 6) 8 1208 8 h6x1208 h6x1216))) (@span_join (Z 6) 24 1224 24 (@span_join (Z 6) 8 1224 16 h6x1224 (@span_join (Z 6) 8 1232 8 h6x1232 h6x1240)) (@span_join (Z 6) 8 1248 16 h6x1248 (@span_join (Z 6) 8 1256 8 h6x1256 h6x1264)))) (@span_join (Z 6) 48 1272 56 (@span_join (Z 6) 24 1272 24 (@span_join (Z 6) 8 1272 16 h6x1272 (@span_join (Z 6) 8 1280 8 h6x1280 h6x1288)) (@span_join (Z 6) 8 1296 16 h6x1296 (@span_join (Z 6) 8 1304 8 h6x1304 h6x1312))) (@span_join (Z 6) 24 1320 32 (@span_join (Z 6) 8 1320 16 h6x1320 (@span_join (Z 6) 8 1328 8 h6x1328 h6x1336)) (@span_join (Z 6) 16 1344 16 (@span_join (Z 6) 8 1344 8 h6x1344 h6x1352) (@span_join (Z 6) 8 1360 8 h6x1360 h6x1368))))) (@span_join (Z 6) 96 1376 104 (@span_join (Z 6) 48 1376 48 (@span_join (Z 6) 24 1376 24 (@span_join (Z 6) 8 1376 16 h6x1376 (@span_join (Z 6) 8 1384 8 h6x1384 h6x1392)) (@span_join (Z 6) 8 1400 16 h6x1400 (@span_join (Z 6) 8 1408 8 h6x1408 h6x1416))) (@span_join (Z 6) 24 1424 24 (@span_join (Z 6) 8 1424 16 h6x1424 (@span_join (Z 6) 8 1432 8 h6x1432 h6x1440)) (@span_join (Z 6) 8 1448 16 h6x1448 (@span_join (Z 6) 8 1456 8 h6x1456 h6x1464)))) (@span_join (Z 6) 48 1472 56 (@span_join (Z 6) 24 1472 24 (@span_join (Z 6) 8 1472 16 h6x1472 (@span_join (Z 6) 8 1480 8 h6x1480 h6x1488)) (@span_join (Z 6) 8 1496 16 h6x1496 (@span_join (Z 6) 8 1504 8 h6x1504 h6x1512))) (@span_join (Z 6) 24 1520 32 (@span_join (Z 6) 8 1520 16 h6x1520 (@span_join (Z 6) 8 1528 8 h6x1528 h6x1536)) (@span_join (Z 6) 16 1544 16 (@span_join (Z 6) 8 1544 8 h6x1544 h6x1552) (@span_join (Z 6) 8 1560 8 h6x1560 h6x1568)))))))) (@span_join (Z 6) 792 1576 791 (@span_join (Z 6) 392 1576 400 (@span_join (Z 6) 192 1576 200 (@span_join (Z 6) 96 1576 96 (@span_join (Z 6) 48 1576 48 (@span_join (Z 6) 24 1576 24 (@span_join (Z 6) 8 1576 16 h6x1576 (@span_join (Z 6) 8 1584 8 h6x1584 h6x1592)) (@span_join (Z 6) 8 1600 16 h6x1600 (@span_join (Z 6) 8 1608 8 h6x1608 h6x1616))) (@span_join (Z 6) 24 1624 24 (@span_join (Z 6) 8 1624 16 h6x1624 (@span_join (Z 6) 8 1632 8 h6x1632 h6x1640)) (@span_join (Z 6) 8 1648 16 h6x1648 (@span_join (Z 6) 8 1656 8 h6x1656 h6x1664)))) (@span_join (Z 6) 48 1672 48 (@span_join (Z 6) 24 1672 24 (@span_join (Z 6) 8 1672 16 h6x1672 (@span_join (Z 6) 8 1680 8 h6x1680 h6x1688)) (@span_join (Z 6) 8 1696 16 h6x1696 (@span_join (Z 6) 8 1704 8 h6x1704 h6x1712))) (@span_join (Z 6) 24 1720 24 (@span_join (Z 6) 8 1720 16 h6x1720 (@span_join (Z 6) 8 1728 8 h6x1728 h6x1736)) (@span_join (Z 6) 8 1744 16 h6x1744 (@span_join (Z 6) 8 1752 8 h6x1752 h6x1760))))) (@span_join (Z 6) 96 1768 104 (@span_join (Z 6) 48 1768 48 (@span_join (Z 6) 24 1768 24 (@span_join (Z 6) 8 1768 16 h6x1768 (@span_join (Z 6) 8 1776 8 h6x1776 h6x1784)) (@span_join (Z 6) 8 1792 16 h6x1792 (@span_join (Z 6) 8 1800 8 h6x1800 h6x1808))) (@span_join (Z 6) 24 1816 24 (@span_join (Z 6) 8 1816 16 h6x1816 (@span_join (Z 6) 8 1824 8 h6x1824 h6x1832)) (@span_join (Z 6) 8 1840 16 h6x1840 (@span_join (Z 6) 8 1848 8 h6x1848 h6x1856)))) (@span_join (Z 6) 48 1864 56 (@span_join (Z 6) 24 1864 24 (@span_join (Z 6) 8 1864 16 h6x1864 (@span_join (Z 6) 8 1872 8 h6x1872 h6x1880)) (@span_join (Z 6) 8 1888 16 h6x1888 (@span_join (Z 6) 8 1896 8 h6x1896 h6x1904))) (@span_join (Z 6) 24 1912 32 (@span_join (Z 6) 8 1912 16 h6x1912 (@span_join (Z 6) 8 1920 8 h6x1920 h6x1928)) (@span_join (Z 6) 16 1936 16 (@span_join (Z 6) 8 1936 8 h6x1936 h6x1944) (@span_join (Z 6) 8 1952 8 h6x1952 h6x1960)))))) (@span_join (Z 6) 200 1968 200 (@span_join (Z 6) 96 1968 104 (@span_join (Z 6) 48 1968 48 (@span_join (Z 6) 24 1968 24 (@span_join (Z 6) 8 1968 16 h6x1968 (@span_join (Z 6) 8 1976 8 h6x1976 h6x1984)) (@span_join (Z 6) 8 1992 16 h6x1992 (@span_join (Z 6) 8 2000 8 h6x2000 h6x2008))) (@span_join (Z 6) 24 2016 24 (@span_join (Z 6) 8 2016 16 h6x2016 (@span_join (Z 6) 8 2024 8 h6x2024 h6x2032)) (@span_join (Z 6) 8 2040 16 h6x2040 (@span_join (Z 6) 8 2048 8 h6x2048 h6x2056)))) (@span_join (Z 6) 48 2064 56 (@span_join (Z 6) 24 2064 24 (@span_join (Z 6) 8 2064 16 h6x2064 (@span_join (Z 6) 8 2072 8 h6x2072 h6x2080)) (@span_join (Z 6) 8 2088 16 h6x2088 (@span_join (Z 6) 8 2096 8 h6x2096 h6x2104))) (@span_join (Z 6) 24 2112 32 (@span_join (Z 6) 8 2112 16 h6x2112 (@span_join (Z 6) 8 2120 8 h6x2120 h6x2128)) (@span_join (Z 6) 16 2136 16 (@span_join (Z 6) 8 2136 8 h6x2136 h6x2144) (@span_join (Z 6) 8 2152 8 h6x2152 h6x2160))))) (@span_join (Z 6) 96 2168 104 (@span_join (Z 6) 48 2168 48 (@span_join (Z 6) 24 2168 24 (@span_join (Z 6) 8 2168 16 h6x2168 (@span_join (Z 6) 8 2176 8 h6x2176 h6x2184)) (@span_join (Z 6) 8 2192 16 h6x2192 (@span_join (Z 6) 8 2200 8 h6x2200 h6x2208))) (@span_join (Z 6) 24 2216 24 (@span_join (Z 6) 8 2216 16 h6x2216 (@span_join (Z 6) 8 2224 8 h6x2224 h6x2232)) (@span_join (Z 6) 8 2240 16 h6x2240 (@span_join (Z 6) 8 2248 8 h6x2248 h6x2256)))) (@span_join (Z 6) 48 2264 56 (@span_join (Z 6) 24 2264 24 (@span_join (Z 6) 8 2264 16 h6x2264 (@span_join (Z 6) 8 2272 8 h6x2272 h6x2280)) (@span_join (Z 6) 8 2288 16 h6x2288 (@span_join (Z 6) 8 2296 8 h6x2296 h6x2304))) (@span_join (Z 6) 24 2312 32 (@span_join (Z 6) 8 2312 16 h6x2312 (@span_join (Z 6) 8 2320 8 h6x2320 h6x2328)) (@span_join (Z 6) 16 2336 16 (@span_join (Z 6) 8 2336 8 h6x2336 h6x2344) (@span_join (Z 6) 8 2352 8 h6x2352 h6x2360))))))) (@span_join (Z 6) 392 2368 399 (@span_join (Z 6) 192 2368 200 (@span_join (Z 6) 96 2368 96 (@span_join (Z 6) 48 2368 48 (@span_join (Z 6) 24 2368 24 (@span_join (Z 6) 8 2368 16 h6x2368 (@span_join (Z 6) 8 2376 8 h6x2376 h6x2384)) (@span_join (Z 6) 8 2392 16 h6x2392 (@span_join (Z 6) 8 2400 8 h6x2400 h6x2408))) (@span_join (Z 6) 24 2416 24 (@span_join (Z 6) 8 2416 16 h6x2416 (@span_join (Z 6) 8 2424 8 h6x2424 h6x2432)) (@span_join (Z 6) 8 2440 16 h6x2440 (@span_join (Z 6) 8 2448 8 h6x2448 h6x2456)))) (@span_join (Z 6) 48 2464 48 (@span_join (Z 6) 24 2464 24 (@span_join (Z 6) 8 2464 16 h6x2464 (@span_join (Z 6) 8 2472 8 h6x2472 h6x2480)) (@span_join (Z 6) 8 2488 16 h6x2488 (@span_join (Z 6) 8 2496 8 h6x2496 h6x2504))) (@span_join (Z 6) 24 2512 24 (@span_join (Z 6) 8 2512 16 h6x2512 (@span_join (Z 6) 8 2520 8 h6x2520 h6x2528)) (@span_join (Z 6) 8 2536 16 h6x2536 (@span_join (Z 6) 8 2544 8 h6x2544 h6x2552))))) (@span_join (Z 6) 96 2560 104 (@span_join (Z 6) 48 2560 48 (@span_join (Z 6) 24 2560 24 (@span_join (Z 6) 8 2560 16 h6x2560 (@span_join (Z 6) 8 2568 8 h6x2568 h6x2576)) (@span_join (Z 6) 8 2584 16 h6x2584 (@span_join (Z 6) 8 2592 8 h6x2592 h6x2600))) (@span_join (Z 6) 24 2608 24 (@span_join (Z 6) 8 2608 16 h6x2608 (@span_join (Z 6) 8 2616 8 h6x2616 h6x2624)) (@span_join (Z 6) 8 2632 16 h6x2632 (@span_join (Z 6) 8 2640 8 h6x2640 h6x2648)))) (@span_join (Z 6) 48 2656 56 (@span_join (Z 6) 24 2656 24 (@span_join (Z 6) 8 2656 16 h6x2656 (@span_join (Z 6) 8 2664 8 h6x2664 h6x2672)) (@span_join (Z 6) 8 2680 16 h6x2680 (@span_join (Z 6) 8 2688 8 h6x2688 h6x2696))) (@span_join (Z 6) 24 2704 32 (@span_join (Z 6) 8 2704 16 h6x2704 (@span_join (Z 6) 8 2712 8 h6x2712 h6x2720)) (@span_join (Z 6) 16 2728 16 (@span_join (Z 6) 8 2728 8 h6x2728 h6x2736) (@span_join (Z 6) 8 2744 8 h6x2744 h6x2752)))))) (@span_join (Z 6) 200 2760 199 (@span_join (Z 6) 96 2760 104 (@span_join (Z 6) 48 2760 48 (@span_join (Z 6) 24 2760 24 (@span_join (Z 6) 8 2760 16 h6x2760 (@span_join (Z 6) 8 2768 8 h6x2768 h6x2776)) (@span_join (Z 6) 8 2784 16 h6x2784 (@span_join (Z 6) 8 2792 8 h6x2792 h6x2800))) (@span_join (Z 6) 24 2808 24 (@span_join (Z 6) 8 2808 16 h6x2808 (@span_join (Z 6) 8 2816 8 h6x2816 h6x2824)) (@span_join (Z 6) 8 2832 16 h6x2832 (@span_join (Z 6) 8 2840 8 h6x2840 h6x2848)))) (@span_join (Z 6) 48 2856 56 (@span_join (Z 6) 24 2856 24 (@span_join (Z 6) 8 2856 16 h6x2856 (@span_join (Z 6) 8 2864 8 h6x2864 h6x2872)) (@span_join (Z 6) 8 2880 16 h6x2880 (@span_join (Z 6) 8 2888 8 h6x2888 h6x2896))) (@span_join (Z 6) 24 2904 32 (@span_join (Z 6) 8 2904 16 h6x2904 (@span_join (Z 6) 8 2912 8 h6x2912 h6x2920)) (@span_join (Z 6) 16 2928 16 (@span_join (Z 6) 8 2928 8 h6x2928 h6x2936) (@span_join (Z 6) 8 2944 8 h6x2944 h6x2952))))) (@span_join (Z 6) 96 2960 103 (@span_join (Z 6) 48 2960 48 (@span_join (Z 6) 24 2960 24 (@span_join (Z 6) 8 2960 16 h6x2960 (@span_join (Z 6) 8 2968 8 h6x2968 h6x2976)) (@span_join (Z 6) 8 2984 16 h6x2984 (@span_join (Z 6) 8 2992 8 h6x2992 h6x3000))) (@span_join (Z 6) 24 3008 24 (@span_join (Z 6) 8 3008 16 h6x3008 (@span_join (Z 6) 8 3016 8 h6x3016 h6x3024)) (@span_join (Z 6) 8 3032 16 h6x3032 (@span_join (Z 6) 8 3040 8 h6x3040 h6x3048)))) (@span_join (Z 6) 48 3056 55 (@span_join (Z 6) 24 3056 24 (@span_join (Z 6) 8 3056 16 h6x3056 (@span_join (Z 6) 8 3064 8 h6x3064 h6x3072)) (@span_join (Z 6) 8 3080 16 h6x3080 (@span_join (Z 6) 8 3088 8 h6x3088 h6x3096))) (@span_join (Z 6) 24 3104 31 (@span_join (Z 6) 8 3104 16 h6x3104 (@span_join (Z 6) 8 3112 8 h6x3112 h6x3120)) (@span_join (Z 6) 16 3128 15 (@span_join (Z 6) 8 3128 8 h6x3128 h6x3136) (@span_join (Z 6) 8 3144 7 h6x3144 h6x3152)))))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x0 : span (Z 7) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x8 : span (Z 7) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x16 : span (Z 7) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x24 : span (Z 7) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x32 : span (Z 7) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x40 : span (Z 7) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x48 : span (Z 7) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x56 : span (Z 7) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x64 : span (Z 7) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x72 : span (Z 7) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x80 : span (Z 7) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x88 : span (Z 7) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x96 : span (Z 7) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x104 : span (Z 7) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x112 : span (Z 7) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x120 : span (Z 7) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x128 : span (Z 7) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x136 : span (Z 7) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x144 : span (Z 7) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x152 : span (Z 7) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x160 : span (Z 7) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x168 : span (Z 7) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x176 : span (Z 7) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x184 : span (Z 7) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x192 : span (Z 7) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x200 : span (Z 7) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x208 : span (Z 7) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x216 : span (Z 7) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x224 : span (Z 7) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x232 : span (Z 7) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x240 : span (Z 7) 8 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x248 : span (Z 7) 8 248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x256 : span (Z 7) 8 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x264 : span (Z 7) 8 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x272 : span (Z 7) 8 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x280 : span (Z 7) 8 280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x288 : span (Z 7) 8 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x296 : span (Z 7) 8 296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x304 : span (Z 7) 8 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x312 : span (Z 7) 8 312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x320 : span (Z 7) 8 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x328 : span (Z 7) 8 328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x336 : span (Z 7) 8 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x344 : span (Z 7) 8 344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x352 : span (Z 7) 8 352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x360 : span (Z 7) 8 360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x368 : span (Z 7) 8 368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x376 : span (Z 7) 8 376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x384 : span (Z 7) 8 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x392 : span (Z 7) 8 392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x400 : span (Z 7) 8 400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x408 : span (Z 7) 8 408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x416 : span (Z 7) 8 416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x424 : span (Z 7) 8 424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x432 : span (Z 7) 8 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x440 : span (Z 7) 8 440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x448 : span (Z 7) 8 448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x456 : span (Z 7) 8 456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x464 : span (Z 7) 8 464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x472 : span (Z 7) 8 472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x480 : span (Z 7) 8 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x488 : span (Z 7) 8 488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x496 : span (Z 7) 8 496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x504 : span (Z 7) 8 504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x512 : span (Z 7) 8 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x520 : span (Z 7) 8 520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x528 : span (Z 7) 8 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x536 : span (Z 7) 8 536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x544 : span (Z 7) 8 544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x552 : span (Z 7) 8 552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x560 : span (Z 7) 8 560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x568 : span (Z 7) 8 568 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x576 : span (Z 7) 8 576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x584 : span (Z 7) 8 584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x592 : span (Z 7) 8 592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x600 : span (Z 7) 8 600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x608 : span (Z 7) 8 608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x616 : span (Z 7) 8 616 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x624 : span (Z 7) 8 624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x632 : span (Z 7) 8 632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x640 : span (Z 7) 8 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x648 : span (Z 7) 8 648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x656 : span (Z 7) 8 656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x664 : span (Z 7) 8 664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x672 : span (Z 7) 8 672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x680 : span (Z 7) 8 680 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x688 : span (Z 7) 8 688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x696 : span (Z 7) 8 696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x704 : span (Z 7) 8 704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x712 : span (Z 7) 8 712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x720 : span (Z 7) 8 720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x728 : span (Z 7) 8 728 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x736 : span (Z 7) 8 736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x744 : span (Z 7) 8 744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x752 : span (Z 7) 8 752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x760 : span (Z 7) 8 760 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x768 : span (Z 7) 8 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x776 : span (Z 7) 8 776 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x784 : span (Z 7) 8 784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x792 : span (Z 7) 8 792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x800 : span (Z 7) 8 800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x808 : span (Z 7) 8 808 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x816 : span (Z 7) 8 816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x824 : span (Z 7) 8 824 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x832 : span (Z 7) 8 832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x840 : span (Z 7) 8 840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x848 : span (Z 7) 8 848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x856 : span (Z 7) 8 856 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x864 : span (Z 7) 8 864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x872 : span (Z 7) 8 872 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x880 : span (Z 7) 8 880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x888 : span (Z 7) 8 888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x896 : span (Z 7) 8 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x904 : span (Z 7) 8 904 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x912 : span (Z 7) 8 912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x920 : span (Z 7) 8 920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x928 : span (Z 7) 8 928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x936 : span (Z 7) 8 936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x944 : span (Z 7) 8 944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x952 : span (Z 7) 8 952 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x960 : span (Z 7) 8 960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x968 : span (Z 7) 8 968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x976 : span (Z 7) 8 976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x984 : span (Z 7) 8 984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x992 : span (Z 7) 8 992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1000 : span (Z 7) 8 1000 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1008 : span (Z 7) 8 1008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1016 : span (Z 7) 8 1016 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1024 : span (Z 7) 8 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1032 : span (Z 7) 8 1032 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1040 : span (Z 7) 8 1040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1048 : span (Z 7) 8 1048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1056 : span (Z 7) 8 1056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1064 : span (Z 7) 8 1064 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1072 : span (Z 7) 8 1072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1080 : span (Z 7) 8 1080 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1088 : span (Z 7) 8 1088 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1096 : span (Z 7) 8 1096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1104 : span (Z 7) 8 1104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1112 : span (Z 7) 8 1112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1120 : span (Z 7) 8 1120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1128 : span (Z 7) 8 1128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1136 : span (Z 7) 8 1136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1144 : span (Z 7) 8 1144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1152 : span (Z 7) 7 1152 = true := by decide +kernel
theorem z7 : span (Z 7) 1159 0 = true := (@span_join (Z 7) 576 0 583 (@span_join (Z 7) 288 0 288 (@span_join (Z 7) 144 0 144 (@span_join (Z 7) 72 0 72 (@span_join (Z 7) 32 0 40 (@span_join (Z 7) 16 0 16 (@span_join (Z 7) 8 0 8 h7x0 h7x8) (@span_join (Z 7) 8 16 8 h7x16 h7x24)) (@span_join (Z 7) 16 32 24 (@span_join (Z 7) 8 32 8 h7x32 h7x40) (@span_join (Z 7) 8 48 16 h7x48 (@span_join (Z 7) 8 56 8 h7x56 h7x64)))) (@span_join (Z 7) 32 72 40 (@span_join (Z 7) 16 72 16 (@span_join (Z 7) 8 72 8 h7x72 h7x80) (@span_join (Z 7) 8 88 8 h7x88 h7x96)) (@span_join (Z 7) 16 104 24 (@span_join (Z 7) 8 104 8 h7x104 h7x112) (@span_join (Z 7) 8 120 16 h7x120 (@span_join (Z 7) 8 128 8 h7x128 h7x136))))) (@span_join (Z 7) 72 144 72 (@span_join (Z 7) 32 144 40 (@span_join (Z 7) 16 144 16 (@span_join (Z 7) 8 144 8 h7x144 h7x152) (@span_join (Z 7) 8 160 8 h7x160 h7x168)) (@span_join (Z 7) 16 176 24 (@span_join (Z 7) 8 176 8 h7x176 h7x184) (@span_join (Z 7) 8 192 16 h7x192 (@span_join (Z 7) 8 200 8 h7x200 h7x208)))) (@span_join (Z 7) 32 216 40 (@span_join (Z 7) 16 216 16 (@span_join (Z 7) 8 216 8 h7x216 h7x224) (@span_join (Z 7) 8 232 8 h7x232 h7x240)) (@span_join (Z 7) 16 248 24 (@span_join (Z 7) 8 248 8 h7x248 h7x256) (@span_join (Z 7) 8 264 16 h7x264 (@span_join (Z 7) 8 272 8 h7x272 h7x280)))))) (@span_join (Z 7) 144 288 144 (@span_join (Z 7) 72 288 72 (@span_join (Z 7) 32 288 40 (@span_join (Z 7) 16 288 16 (@span_join (Z 7) 8 288 8 h7x288 h7x296) (@span_join (Z 7) 8 304 8 h7x304 h7x312)) (@span_join (Z 7) 16 320 24 (@span_join (Z 7) 8 320 8 h7x320 h7x328) (@span_join (Z 7) 8 336 16 h7x336 (@span_join (Z 7) 8 344 8 h7x344 h7x352)))) (@span_join (Z 7) 32 360 40 (@span_join (Z 7) 16 360 16 (@span_join (Z 7) 8 360 8 h7x360 h7x368) (@span_join (Z 7) 8 376 8 h7x376 h7x384)) (@span_join (Z 7) 16 392 24 (@span_join (Z 7) 8 392 8 h7x392 h7x400) (@span_join (Z 7) 8 408 16 h7x408 (@span_join (Z 7) 8 416 8 h7x416 h7x424))))) (@span_join (Z 7) 72 432 72 (@span_join (Z 7) 32 432 40 (@span_join (Z 7) 16 432 16 (@span_join (Z 7) 8 432 8 h7x432 h7x440) (@span_join (Z 7) 8 448 8 h7x448 h7x456)) (@span_join (Z 7) 16 464 24 (@span_join (Z 7) 8 464 8 h7x464 h7x472) (@span_join (Z 7) 8 480 16 h7x480 (@span_join (Z 7) 8 488 8 h7x488 h7x496)))) (@span_join (Z 7) 32 504 40 (@span_join (Z 7) 16 504 16 (@span_join (Z 7) 8 504 8 h7x504 h7x512) (@span_join (Z 7) 8 520 8 h7x520 h7x528)) (@span_join (Z 7) 16 536 24 (@span_join (Z 7) 8 536 8 h7x536 h7x544) (@span_join (Z 7) 8 552 16 h7x552 (@span_join (Z 7) 8 560 8 h7x560 h7x568))))))) (@span_join (Z 7) 288 576 295 (@span_join (Z 7) 144 576 144 (@span_join (Z 7) 72 576 72 (@span_join (Z 7) 32 576 40 (@span_join (Z 7) 16 576 16 (@span_join (Z 7) 8 576 8 h7x576 h7x584) (@span_join (Z 7) 8 592 8 h7x592 h7x600)) (@span_join (Z 7) 16 608 24 (@span_join (Z 7) 8 608 8 h7x608 h7x616) (@span_join (Z 7) 8 624 16 h7x624 (@span_join (Z 7) 8 632 8 h7x632 h7x640)))) (@span_join (Z 7) 32 648 40 (@span_join (Z 7) 16 648 16 (@span_join (Z 7) 8 648 8 h7x648 h7x656) (@span_join (Z 7) 8 664 8 h7x664 h7x672)) (@span_join (Z 7) 16 680 24 (@span_join (Z 7) 8 680 8 h7x680 h7x688) (@span_join (Z 7) 8 696 16 h7x696 (@span_join (Z 7) 8 704 8 h7x704 h7x712))))) (@span_join (Z 7) 72 720 72 (@span_join (Z 7) 32 720 40 (@span_join (Z 7) 16 720 16 (@span_join (Z 7) 8 720 8 h7x720 h7x728) (@span_join (Z 7) 8 736 8 h7x736 h7x744)) (@span_join (Z 7) 16 752 24 (@span_join (Z 7) 8 752 8 h7x752 h7x760) (@span_join (Z 7) 8 768 16 h7x768 (@span_join (Z 7) 8 776 8 h7x776 h7x784)))) (@span_join (Z 7) 32 792 40 (@span_join (Z 7) 16 792 16 (@span_join (Z 7) 8 792 8 h7x792 h7x800) (@span_join (Z 7) 8 808 8 h7x808 h7x816)) (@span_join (Z 7) 16 824 24 (@span_join (Z 7) 8 824 8 h7x824 h7x832) (@span_join (Z 7) 8 840 16 h7x840 (@span_join (Z 7) 8 848 8 h7x848 h7x856)))))) (@span_join (Z 7) 144 864 151 (@span_join (Z 7) 72 864 72 (@span_join (Z 7) 32 864 40 (@span_join (Z 7) 16 864 16 (@span_join (Z 7) 8 864 8 h7x864 h7x872) (@span_join (Z 7) 8 880 8 h7x880 h7x888)) (@span_join (Z 7) 16 896 24 (@span_join (Z 7) 8 896 8 h7x896 h7x904) (@span_join (Z 7) 8 912 16 h7x912 (@span_join (Z 7) 8 920 8 h7x920 h7x928)))) (@span_join (Z 7) 32 936 40 (@span_join (Z 7) 16 936 16 (@span_join (Z 7) 8 936 8 h7x936 h7x944) (@span_join (Z 7) 8 952 8 h7x952 h7x960)) (@span_join (Z 7) 16 968 24 (@span_join (Z 7) 8 968 8 h7x968 h7x976) (@span_join (Z 7) 8 984 16 h7x984 (@span_join (Z 7) 8 992 8 h7x992 h7x1000))))) (@span_join (Z 7) 72 1008 79 (@span_join (Z 7) 32 1008 40 (@span_join (Z 7) 16 1008 16 (@span_join (Z 7) 8 1008 8 h7x1008 h7x1016) (@span_join (Z 7) 8 1024 8 h7x1024 h7x1032)) (@span_join (Z 7) 16 1040 24 (@span_join (Z 7) 8 1040 8 h7x1040 h7x1048) (@span_join (Z 7) 8 1056 16 h7x1056 (@span_join (Z 7) 8 1064 8 h7x1064 h7x1072)))) (@span_join (Z 7) 40 1080 39 (@span_join (Z 7) 16 1080 24 (@span_join (Z 7) 8 1080 8 h7x1080 h7x1088) (@span_join (Z 7) 8 1096 16 h7x1096 (@span_join (Z 7) 8 1104 8 h7x1104 h7x1112))) (@span_join (Z 7) 16 1120 23 (@span_join (Z 7) 8 1120 8 h7x1120 h7x1128) (@span_join (Z 7) 8 1136 15 h7x1136 (@span_join (Z 7) 8 1144 7 h7x1144 h7x1152))))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x0 : span (Z 8) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x8 : span (Z 8) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x16 : span (Z 8) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x24 : span (Z 8) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x32 : span (Z 8) 5 32 = true := by decide +kernel
theorem z8 : span (Z 8) 37 0 = true := (@span_join (Z 8) 16 0 21 (@span_join (Z 8) 8 0 8 h8x0 h8x8) (@span_join (Z 8) 8 16 13 h8x16 (@span_join (Z 8) 8 24 5 h8x24 h8x32)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x0 : span (Z 9) 1 0 = true := by decide +kernel
theorem z9 : span (Z 9) 1 0 = true := h9x0

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · intro i hi
    exact span_ok z4 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z5 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z6 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z7 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z8 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z9 i (Nat.zero_le i) (by simpa [NN] using hi)

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : MonRun (goal 54) s xsG) : False := by
  have hl := run_len h
  have hlen : xsG.length = 6 := by decide +kernel
  rw [hlen] at hl
  have hlo : 5 ≤ s := by omega
  interval_cases s
  · exact bar_all checked 5 (by decide) 303 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 5 303)) h)
  · exact bar_all checked 6 (by decide) 592 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 6 592)) h)
  · exact bar_all checked 7 (by decide) 206 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 7 206)) h)
  · exact bar_all checked 8 (by decide) 11 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 8 11)) h)
  · exact bar_all checked 9 (by decide) 0 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 9 0)) h)

theorem no_small : ¬ HasMonoSize 6 prism 9 :=
  encoded_prism_mono_exclusion rowsG xsG 54 enc_inputsG enc_goalG proper_failG noRunFull

end PEqualNP.Outside.L_meta_742_aux

theorem PEqualNP.Outside.L_meta_742 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 10 ≤ C.size := by
  intro C hm hev
  exact PEqualNP.Outside.L_meta_742_aux.prism_lower_from_mono_exclusion PEqualNP.Outside.L_meta_742_aux.no_small C hm hev
