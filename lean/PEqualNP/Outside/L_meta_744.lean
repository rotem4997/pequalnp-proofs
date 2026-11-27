import Mathlib
import PEqualNP.Defs

-- Generic Run normalization adapted from Digger-Rockwell PR801, Apache-2.0.
-- Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
-- Monotone preservation, directed coverage, and this finite certificate are new.


namespace PEqualNP.Outside.L_meta_744_aux

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


abbrev wheel : BFn 6 := fun x : Fin 6 → Bool =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) ||
  (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)

theorem wheel_iff (x : Fin 6 → Bool) :
    wheel x = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true := by
  constructor
  · intro h
    simp only [wheel,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with (((((((((⟨h0,h1⟩ | ⟨h1,h2⟩) | ⟨h2,h3⟩) | ⟨h3,h4⟩) | ⟨h0,h4⟩) |
      ⟨h0,h5⟩) | ⟨h1,h5⟩) | ⟨h2,h5⟩) | ⟨h3,h5⟩) | ⟨h4,h5⟩)
    · exact ⟨0,1,by simp,h0,h1⟩
    · exact ⟨1,2,by simp,h1,h2⟩
    · exact ⟨2,3,by simp,h2,h3⟩
    · exact ⟨3,4,by simp,h3,h4⟩
    · exact ⟨0,4,by simp,h0,h4⟩
    · exact ⟨0,5,by simp,h0,h5⟩
    · exact ⟨1,5,by simp,h1,h5⟩
    · exact ⟨2,5,by simp,h2,h5⟩
    · exact ⟨3,5,by simp,h3,h5⟩
    · exact ⟨4,5,by simp,h4,h5⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    fin_cases u <;> fin_cases v <;> simp_all [wheel]

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

theorem wheel_mono_run (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = wheel x) (hs : C.size ≤ 9) :
    ∃ s, s ≤ 9 ∧ ∃ ws : List (BFn 6),
      ws.Sublist (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)) ∧
      Run (fun a : BFn 6 => a) meetF joinF wheel s ws :=
  exists_run_mono wheel ⟨fun _ => false,fun _ => true,by decide⟩ 9 ⟨C,hmono,hs,hev⟩

theorem wheel_mono_encoded (rows : List ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = wheel x) (hs : C.size ≤ 9) :
    ∃ s, s ≤ 9 ∧ ∃ zs : List ℕ,
      zs.Sublist ((List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
        (fun a => encL a rows)) ∧ MonoNatRun (encL wheel rows) s zs := by
  obtain ⟨s,hs,ws,hsub,hrun⟩ := wheel_mono_run C hmono hev hs
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



theorem encoded_wheel_mono_exclusion (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL wheel rows = goal k)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (covUp k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ 9, ¬ MonRun (goal k) s xs) :
    ¬ HasMonoSize 6 wheel 9 := by
  rintro ⟨C,hmono,hs,hev⟩
  obtain ⟨s,hs,zs,hsub,hr⟩ := wheel_mono_encoded rows C hmono hev hs
  rw [hinputs] at hsub
  rw [hgoal] at hr
  by_cases he : zs = xs
  · subst zs
    exact hno s hs hr
  · exact hproper zs (List.mem_sublists.2 hsub) he (required_up hr)

theorem wheel_lower_from_mono_exclusion (hno : ¬ HasMonoSize 6 wheel 9)
    (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) : 10 ≤ C.size := by
  by_contra hs
  apply hno
  refine ⟨C,hmono,by omega,?_⟩
  intro x
  rw [Bool.eq_iff_iff,hev x,wheel_iff x]

def rowsG : List ℕ := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48]

def xsG : List ℕ := [0xa4290a4290a4290000000000fffff, 0x10c4310c4310c4300000fffff00000, 0x218862188621886003ff00000003ff, 0x45114451144511400000003ffffc00, 0x862188621886218003ffffc0000000, 0xf83e0f83e0f83e0ffc000000000000]

def NN : Nat → Nat
  | 4 => 240
  | 5 => 2026
  | 6 => 3518
  | 7 => 1174
  | 8 => 37
  | 9 => 1
  | _ => 0

def HT : Nat → Nat
  | 4 => 0xff7cfc4cfd4e0f38fcc3c7affc0d9dedfb955247faa675d1fa365cfcf9c37fc2f9bcedd5f30e5196f2f59754f2dbea50f1127f52f0a30887f0929ee7ec8e5b81e801f5a7e76f85fee66e9294e5a7b64ee5a14fd8e5653fe0e55d4388e542dd2de4bc0162e415949fe30b919fe2c96988e1000523e033c6ecdfd85fb3df2c803ddd23db41dc1aee82dbad8731db8f2eabdb8cf071daed6a49da6fd9f7d9003244d8d65eb2d8c93eb7d79a8c95d74a6416d5efc2aad430e369d0e065cdd0be7ed4cba912d8c63c557dc63bd5f3c5667264c32c284bc1e17096c1926d92c10212bcc0ce7e0fc0adcb7abfa88356bf0707d6bebf4a03bdeb86c1bd7e6ac4bc1e6ce8ba94fde3b8e54c0ab6f81498b54f789db33eebf9b2a6200cb2262d29b1c86b63aeb8ac3eac45263dabb36ef3aaf47a8caacdff2aa8296909a7fb0319a6e8afb2a5ddbd21a4677460a3ebccb0a3a028f0a374c35ea14a3e49a0cde485a04f435d9c9ed3bf9ba8adcf990537d697e9806d972ee48996a9b45a968d1a9a9672e674955609c093df081a9381f0f792755335924e04c38fb235e18f7527e38ec3596b8ea8a7f28d9de6f28a023abe88afd91486901b9f8665517383aa24d383172b958275ede0808efaf97f504b4a7f47806c7f2a2f4f7e9f02e47d425be07cb734927b4366cd7a1763767a1475aa7911266878e1e4bb78bc1c2571e6978e7197011370817360700f569d6f6e1f756dbcdb7c6d675eed6d3936b96aa8e81f69fd35e169a630a768cb6c3f689d9666679a78206691f15365c3372f64a1f10360fd7f465f02017b5de0f3495d63ef6b5d1bb4965bd007a45bce3bf5597fc1bb58d4b40058331e59576b0d2d55cea5ce553b66e15433da69537af84a5308f15a511e18304f0a75e14ea445934c913e8c4c7004ca4c3c29fa4c09c2da4afd3fb14a67ad534930acb448cbcd37479b390a4783831f473782d6451a330c44f83f9c44458d7c4433d5c242b580da424a4cd93ef7836f3ca5f5ea3b660c8d39ed310f3971904838daf22d376e5d683726f6b6366fbde9365f8c733454b2723322236032fb230c32838cda3215eef731baaad731683a3e309f27b030795dc82f90f94d2ea21cd72d6c4e912cfa62db2b3e4366290b44f7251b0b1924c02944230820b1222124a92162e4051fe0ca951db587f91d8b6c721cc7cf831c623ba21c3333d61a96ed211a880aba19c7c1ae1878770f182b550a17ba14161628bb761514f60813f71aa9129c914612073d9110c550550e65fa0b0d844c3a0bc071c50a65cc50097ae2f6091609d50915ccba08bd5e6207488c9905e5e89403ebff81019c88e20078ff9b
  | 5 => 0xfff9d8cbffdde877ffdb795fffcdd989ffc0975aff8fe0edff888956ff76255eff30b142ff0cf262fed1f020fea90f13fe9cfea6fe7e2b22fe674ae0fe63b307fe5665c0fe446642fe3f7ea2fe2bfd7dfe1cd7fafe045ae5fdf5a7defdf113f2fd4d9c9dfd378fecfd198eaffd13c698fd0553a4fd0293a8fcf864d3fccd8a19fcb37127fbfe5aaefbe62072fbcb8061fbbd29ccfba361d2fb6d1a80fb577425fb4799cefb40604dfb3724cbfaf6909dfa9c4774fa73fd87fa5e8b23fa50dda6fa40b3fffa2b140ffa0d9c2cf9e083f1f9e04d12f9dd734cf9c9b1d3f9beabfbf9a78e73f972d991f96411caf9455a8df8b41f93f8b4164ff8af1157f87c53edf860d94df83ef155f837d762f7f270e2f7db26a5f71f7c72f6cee04df6bc3d58f6b09fcbf6aa200bf66a5989f65e22dff6537ef7f6509d27f6387328f616b91ff58a36b6f56a869ef5604b44f5185fb8f50f23dff4f8077ef4e78c15f4e40555f4d2df1af4c9a255f44225a4f43fe39df3ecb4a1f3d2b70bf3adbfd4f3979c69f35880caf31eff27f3184ad3f303b36cf2e9fd68f2d7467ff2a6feb3f27cff99f22d691ef2020c9af1f723d7f1d5e1e2f1bdec93f1bdc9dcf1970442f1900fb6f1658448f15bac96f126f0ebf122b209f0dd67eff0a5bea8f0802933f065c5e7f05c6fc4f0163131f0140bd5effad6b9eff0a697efc17cbeef9cd2feef8c7c96ef6dc8f4ef468bc3eeee07c7eeec10e8ee8b1a5bee8ad6f7ee86022cee852ed3ee6eeb9aee5166f9ee429d4eee37fd7dee17beb7ee137fdbedfdc6f8edd81fe8edd2c58dedc5e9c4ed988fcded4fa227ed297ec2ed10c487ed0f7437ed0f5c30ec889baeec818ecaec5537e2ec489aefeb9d06aeeb930a80eb91f88aeb81e7a2eb4649c1eb3f502aeb3735e7eb259beceb0b7814eaa1f6c2ea66e204ea5558efea1c0a47e9e417b7e95520c9e92569b4e9236f85e92169ace91d9bcee8cdbee4e8996cd9e88d6427e87dcb3fe8768280e86245b4e85b8960e830e02be8076825e7e13ce1e7c28fc6e79b909fe7994561e78a2dbde776c4d0e7328995e716c6f3e6fe79b2e6bd2f82e6b309c7e6a687f4e676307fe665f896e6599f3ae646ffbfe61d5b54e5f159d6e5bfd00ce57a771fe57a5468e56b0768e55dcb87e55737e9e5236bb0e5220ed4e4ee13dfe4d33051e49085a3e46c4c67e448ca0fe4314398e3ffd8c0e38d74f7e37e074ae361d385e35686dae33c500be329a073e2f598fae2d9e5bce2c93555e29ce424e247a4e7e2285241e1e6c659e1c9e637e1b8c59ae1a56b25e17b794be15eb77fe134df21e12dbee5e0f1f464e0e207c7e0b30b0ae0ae485ae0a8df86e06f291fe06a7ebbe00a45e8dfecc58fdfec5b8bdfea3395dfcb9453df9a7a17df8c8b89df7cedeadf799905df70c732df4be27bdf3e94c7df3dd6d4df234c54de6f4532de68f21dde6088cbde5ba1c3de15849ede0d0c7fddbcb790dda30b6bdda10263dd23db41dd1e8126dd184c76dcdf5114dccb38a7dc88bd2cdc875f57dc8460d2dc786ecedc64a400dc40ed12dc35cb8edc233280dc1ac982dbf35817dbc74a98dbc1bfcbdb768a88db4c87a3db246663db1bb320db0f82b7db085a19dafbb7fddaf7aadbdad64418dacbfe18da6ef840da58d0dada2f5e5dda1629c6d9f5f3dfd9dfec0dd9d6b9e1d9b7edc6d9a8b48cd98ff1b7d971c66fd9599540d94d9368d93aa1f2d9254bacd9197826d8dff63cd8d9f6fad8bf54bcd8818fe9d808ab1cd7db4634d7d7eb35d7b028b0d7a4d77ed799cc63d7898b21d75d7488d74b5c5fd6dd0598d6d7a2fcd6c03089d66d6eb4d657e76cd63a6f89d6097afdd5faa868d5d1ceecd5c9c9c8d5c90379d5bbaae2d5b70458d59c0157d5857342d5722dead56658a8d501d908d4847137d47d258cd4632e98d4412f34d3f68329d3d37a5fd3ba0485d39e3bafd39aecf9d388b39ad370768bd35be941d34a72f1d348bcf3d3326fecd317b149d2d09421d2c3f36ad2af492cd299228ed293ae63d28ae385d260aae0d250b1d4d1ef98a1d1c2582ad19759fbd165bec4d15ceb80d159f31dd142c3bed10f4dfdd1086104d0fe7e28d0f676e7d0e065cdd0c865f4d0917de3d090c734d07e4e15d07b994dd038c030d02e2596d01c0c41d0107d4dd00d7301cffb67b9cff73779cff20b58cfa0ddeccf331514cf2685adce9ddbd7ce89e580ce4892bfce24143bcdd98ebbcdd7f58acdd656e1cdb65dd2cdb2af06cd9eed2dcd9e7b37cd5ac68fcd41c213cd25410bcd0a3b4cccea021eccd29205ccbdf7f7ccb35c61cca52a0acc783e6dcc66ae8acc4d3178cc170dbbcc07c87fcbffb0f5cbef0fa2cbe99307cbb82185cb9f24edcb8d3e34cb85af7ecb69ce34cb5656efcb4f96e2cb416901cb25cacdcb0e2ff8cacedb3dcac1bb42caac0075ca55f318ca406971ca0d3225c9deaa34c9c4c7afc9bc93afc9a99108c99dd480c99d91c9c915a4d1c8f99ed1c877618ac8704ab4c86b7051c855f5d7c831cb0ac82a929dc7f3a480c7c9da0bc7c6f1bdc79cc9fac773982fc728f6f7c66c649fc65536a5c6489b82c63c557dc624794ac61e04a8c5f81844c5f76cb7c5f2991ac5db7e80c53de200c529faa7c4dd0458c4da0979c4c9c0a2c4bc6590c4bb41cac4a3760fc47159f3c470a955c45196e7c40286d8c3ee438fc3e14343c3a356f7c3988d1fc37a42b6c36d9694c352b9b6c34194e2c3309d04c2e0b4e4c2a2b73cc2940accc2928802c2872876c2710ce9c22db4cec2167b3bc1948016c183d12dc16c595fc11dbc73c10212bcc0bf33c0c0bea8d4c0b2c5c2c09e2ef7c053cf12c03625d5c03167b0c0039f3fbff23585bfed563ebfcf5225bfbf5eabbfbcc453bf9b89e5bf8266eebf423a0abf08fe7fbe9fee88be983debbe983ae9be8597bcbe48126abe1e2f50bdf31022bdc0d686bdbfb856bdada02dbdabd291bda84ca8bd921c09bd808682bd7f929fbd658fabbd5a2f42bd513115bd34bb60bd24fe0bbd2078d0bd076994bce0bcdbbca04a70bc746853bc52db3cbc2c8eb9bbfefccbbbd10bb7bbcd91abbbc48968bb8723c2bb6ca90bbb4d941abb2fd706bb1ff96bbb0f8468baf54be5baf25caebad2b7ffbab5582ebab2a4e0ba985991ba83991aba444f66b9e5a6a5b9c014a9b9acb6bfb9a042e5b98cf925b986512fb95a4478b957faa3b93843b2b8caff03b88cf9f8b868f094b82d33e1b7e7d76ab7e5541cb7d43b2db7d126e2b7b0c985b798a2b3b7902f7ab78df837b76d3568b769e579b760726ab73e6f5ab713696ab706823cb6f30b02b6a5e808b6989a04b68944adb6838e6ab67d90b6b6637eb6b661abe7b6283a55b6067fd9b604dab9b5deedabb5959a39b5761229b524a4d6b4ec294eb4cb6030b4357e79b427dcf2b40add34b3ffab95b378bf63b364b545b3646460b33ddef9b32e1f91b2e6b22ab2d8884bb28a62c0b28a27f2b25c7914b1fea249b1f5ad06b1dd3efbb1ccc9f8b1b1c6a7b19fd6c6b148de89b13edc7db1291ac2b1279736b10fab49b1016385b0d8d311b0b1eceab099d1a9b05f17afb05f0a9fb038d760b0276158b0235686b01e0184b00bd4d6afb5fac9af8d8deeaf827372af49efbaaf43ae4eaf3c753caf386a58aee9ad1baee46fdeae91a3a1ae6aae69ae4c1595ae333a1dae0236ceadd7f187ad7f6347ad70ef6aad70dd75ad57d580ad53e281ad4d204ead4983b1ad2b892cad15e20bad02713cacf29774ace92424acc6f5c9ac9146c7ac7090f6abcee9bdabb4e9d4ab768172ab70d507ab3f9355ab1ea95eab0f5159ab0cd50faaf2ababaa8a9670aa8a84bcaa647771aa1b162baa0e39a5a9f6070fa9d14cefa9cc8606a9cbd30fa97c7fb2a96f9fe7a954ddc1a9511244a94472afa9433c71a91087f1a8eaafafa8e4282aa8c6cfefa88676b8a87ec9faa878bf09a85d8420a847dbdda839a1c3a8315c7aa8066858a7fa8624a7f9b9f1a7dd121ea7c2cbd4a7b40066a79d1d2da77c1776a776f42da76ec842a7595cdda7456c41a71efa4ca6b275a6a6b00dd4a69869a3a69512d7a68d2d95a640286ca633924aa61f0821a5ea3c35a5b1700fa5af398aa59fb33ca5649cb9a5246d3ea5129123a4f24973a4617b49a45555a6a416e10da4119a1ba409a335a3edef17a39e88bca38d4d11a37e03b1a36900e3a3533a68a34f6207a3448364a331f05ea2f372f5a2f01bbca2d1b302a29632daa2953700a2792ee1a265c113a22f61d3a220d332a1ec3cc8a0ff8f8ca0fd1bfba0f001b6a0d2647da090fc8fa07732a0a0306618a0127941a0105e589fd05de59fc21a379fbc6e9b9fbbc8ed9f83637a9f7f8d139ee3212d9eaf36379e4a1b389e38e8689df5c2ec9dc446649dab106c9d9f33e19d9306f99d627bbd9d46cb969d45287d9d0fdd799d03ec459ce86a709c7f6c5b9c79cd5b9c3f021b9c1fbb609be009a39ba0b5c29b526ca19b3cdf0d9af6a0c59ad7bf4e9aac23d29a7a30639a7736079a6c61a99a5e29b999e815d299b2a8ad999f636e997e16b3996ab19599666db399618ebd9933af649925f30598c0aba9986fa8f39861bd0198154e7c981465d997b1e36c978a4dcc977608499757417e97512c329734ad829710a15496eb0cf096c5694396c45a9696b6c0a896890eb09672e674965e085296541a4296538462964440769631c56d96224b9f95fff9f995ca6be5958daff2957472f79570147894f67ee3949fb34a946ee81c94647a9c94175b0593f7720e93dc68f993aea4c3937ea4c3937825d9937144659359ded39345293e92d663dc9292c1ee928d00a6928b659a928a9283927813209271822b927124a3926bfbdd923ae6889208e3e291e27b3291c371c69172ffb7916de84d916d84c391690803915145e4913ca4619119fa9991091c699104b2fe90dc95a090bccad5908ee4b6908c8e0f908b56919037b4c3903700f79025cd149024a06a8fcb97d68fb296b98fadbc2f8f7b5a908f54d60f8f1027df8f0503c08ed922a18eb7361d8e9449da8e9297988e7565e88e1ab4458e0f5f868e0a206e8e0464b68e0025da8debd10f8deb42708ddf65c38da93f398da4c0318d546a938d4f74738d447d7b8d3094288d2ff2ee8d1192498cdff52c8cb3877f8cb217278caa53288ca7391a8ca237ac8c8071c68c73650b8c631fb08c2fe33f8c29eb338be767298bb32acf8baec7e58b7d29a28b33e6bd8b32efc08adf60dc8abd03ad8a7defa38a47e0588a46f6188a2e5ef78a100eee8a00cb0289dc04fa89b3210289a607d989855f5a89800d048975caf789585c898951535388fec68f88f806a788d44f2288b7797588b437a9888c327e88793c91887192fb886c31258868bb118867a9df884ff4c8882632a487f4fa1d87d4eeb087811b98877eb9a68761276e875d233a8757d1d68737528f873394e8871f1212871451b587133b1e86d8b71586b75819869264e3868ad39b8665517386529e95864ae80e86471d0f863f9230863b0d02863ad1da8630efae8616750586157ea2860b2a4085db197785d8aa1a85cf7cda85c6eff3859efb0b85820bd18529b43c850213d184e7dbf084e2aed184e0172884ab9d57847a682c8474af3a846b47b78463cc11843e391e8434a290839fc114838440e88381e053834bcda98300df4682fe402d82fc7cb482d45c6682abb15682aaea9582a69ff7829d6e49826bc443826b85cb821021cd81f61091819e119d817f6f8081748cb8815c85ea8115ea8080dc1921809a14f0807e7ce5803e592e800bd21d8005006a7fe796eb7fe5dda67faaba467f9bea9f7f590fc87f42f9717f08a41c7ea73bf47e81a67f7e7a9f8b7e4ab8627e2638057dbcbe397da08f677d81ced77d71086a7d5a2fbf7d46899c7d1fe1b37d0b27257cec1e737cdd842c7cdb4c5b7cb65e107ca405fd7ca1a82a7c9e06e67c517fab7c4b9b4d7c2bba577c0322e97bdce3e17bb753697ba442497b6a9b737b5983eb7b017d907af01c907accc50c7acafea67a9b1ecd7a89064f7a70b92e7a497a7779be24d679b93cd8799691827971fbda794bef5a791a3477791819a1790bcc4d7906ee0078f6667778ec3e9d78e6aa8378e4288678dceada78d118c678b328fd78af0eb078313ab878299fc577f66a0d77e3713e77b8cca9777732707766f6cc77399cd3773008af772f805776e45bb87699f8917696eeea76917806766dc5877664875f76273d637602ee0f75ee058975ea797375b29b1d75a157e77577806e7538d93275323e90752509047524a1957517265d75037fdf743e660d74307190741fd03d740cc42a740165d673df49cc73c42742737649027356b6e2734763da73139b9c7310043c72fb7ff272ef566772acada3729eba2571baafbc719701137173ebd27156fa9b71540bdd70a939e6708c1d81706af4147051f0a3704f2bcb7046ef4f701b02866feb7fe76fe9b05a6fd09d1a6fcc155e6fca4b1c6fbbe7346f84f2686f31bed66f1649746eff71e86eb5bb916eb0beeb6e89c4816e7689b46e6bdd726e4ec5436dc871bd6d8d62dd6d8b932c6d69e1d06d0f3bed6ce8fb836cb7a6376cad2bdc6cab56816c76c5ff6c6b993c6c5e6d786c54ab396c3ac33c6c3a2e8f6c26f9546c187e586c0cf2356bbbacf36b7696186b72557d6b6eb8236b3e5a046b1908cf6b0e8acd6ae2207b6ae21ab26ad6ff5f6abda7b76aa8f1d16a8135d66a5ddc146a289ce26a222e0a6a0c276c69b4379b69ac9bf769abecf1699433bd698fdc5568fec26468f2e30868ee76d968aef6ed6882d75c67ecfc1c67e7e37d67cbe7f467ba03c167a2dff56772faa56770ee2f67546350674f79c8674e3e1d66daa21766c99ee766c207f866a09cfc665dc08e664283e166259244660aaaa766095a7265dff45f65de60c865d4480c65a692d7659aa16f659825b365977996657720ea656e4073653f114b653047136503088464f0c77664e83ba164a14238645a5513645a5208643ef18964258287640aa78d640936dd6408b36e640402a663fe209063d34c3863c51c3463c378f063b68a6c63a1f9af636e09fa635580b66318915d63058a7262f7214362f47a5862cea74962ca35a962bd8c3b62addf1b627fac9a6264a75e6222d29862216bef620b4fcf61dd775a61bdd5d961aedf2e61a8175e61a18fc16152605e60bc06af6076b5f26061fbe6603ee20e6038d6b1601e0daf5fff0bc95ff8d5505ff815f75fd79e3d5fc76ae65fc1212d5fa1a8815f8b96d35f744bc75f2ee0095f230b945f1911395f1880b05eddf4b95edbd1be5eb9cf995eb0838d5eae66e85e03edf55df0240d5decd15e5dba43515d3f02475d2666765d1ce9e95ce886c95cd8a36c5cc6cb2d5cbe460f5ca81f625c8202be5c75cc845c6e4a8a5c2e0ecf5c2596bb5c0a6d2e5bed1c5b5bc9332a5bb4cc465baca9d25b95a9dc5b6980b75b4cbcde5b4c22cf5b3ec8c25ad40f515ac7ed1d5ac6ae3e5ab5a8f95ab475835aac67cf5a7735195a332c3d5a058b4d59f38af659db79ff59badc0659af320a59a50cc7599ddbc7599aeb5459995cbe5914ef1e590abc5c58fcf8b358e3cf2758d3c143589e3ad65848089058331e5957fc12b357d8f72657c69ad657c2958057b5cfb457b53f135781641d5773a04556f0823556ed8b4256d1773f56892f8c56862aba5681017b56764dd4564b34cf5612438f559a01e6558ce1aa553b66e154e8ec6c54e1bc1654db34bd54d8cf4d54ba89d054b42d0154a9d0cd54a7e6a354a34413549fbf06549f0ce35474520c54650a35543ee39554056809540004a953c1c8d5537e3ca0534f69f95308f15a52f5fbd152e1398a52bbe78b52817dd5526076cb5213e5c3520a7ddd51da95df51b7fd655176cddd515f0039514ce62250fbc3ff50f7e19b50e2323050d9747550b44bf750a51155504bb09e501fdec5500e30bf4ffa49944ff0fa9f4fe10a374f956d704f85e66a4f50178b4f44da984ed8b5654ec92a3e4eac08664e5af9cf4e37ed614e3108814e267b2d4e1d59ef4e19b9ae4e0ddb564e001ef74df375c94de7bf234de66bd24de20a9f4d96db364d87217c4d7837064d74e0c84d666fae4d41b81c4d381e924d0050f34ce12a264c69f26a4c086de04bb7524f4ba737454b95c4094b8709be4b2625054b0b4f5d4ace14d44ac4335d4ac3e1104aac90ec4a3010324a022be8498d2bfd498627d649617f684934c3b2492ddc96490c26bb48fdd59548fd4d3d48fd2df048f92a9648eea10d48ea81b148b8d76a48b1c57748ac9fd148a5392b48851666482cfb044807816e4804e03e47cd59ba47c225ad47b089b4477baf954769e94d4750b71c473526ba470bf48546b9069c46995d0a46850fa2465a59c545fa039245ec086145d9f82245cf32bc45b0c08245775aa84564f5eb45016de544ddc0a544cde32244b46c2744a7b8ee446f699944584c5444556e5d442ae7e84419a3fa43da951643c4e20b434719ff43286fc942e3887c42ab898842a319e2427825d4425265a1422587c4421fbd8941e8cf6c41c54ea741b1828d41a8f754419e952b418dd9ce4176713a4158898940f6bb0640f11aed40e9c1fa40a1850b407b24b040198f0e40001f953ffb49b63fd832013f9d6fe63f93ef8b3f684fcd3f5f3c813f5851aa3f44f1263ee8d22b3edb547d3ed15b363e8a9f4a3e52ff283e28dea43e157a663d7d07d33d6c4a1e3cf2ab1a3cf0317f3cea67223ce0b9773cd524c13cc54a053cb5e3c93c9a2a773c6ee0ea3c6a6cbe3c4f02bc3c48783a3c3746c33bff3bac3bc5becd3ba8e6743ba7826d3ba625103b6952ac3b55cd453b451bc43b32648f3b285dd53b0dbcc33af0a0d73a8497603a4f65c43a11d7d23a0237033a015e5e39eee26139968473397498cf395e373c393ea716391da93338fbd68238eb196c38e69ccf38daf22d38c1c168389a94c4384a365838350afd382fa40e380106bd37f69afd37e8a36437dc7eb0379f7ce03761098c3754e3d7374a1696372d9061371a98183702baf136d8e6e536a9c6a2367ff05336413b9e35f2accc35dda4f135a5c22e35980ffe356dd48c356118f6355318a0351044b834cb373e34cab864349e86ba3490e60a3461a36c3454b2723451209b343cf58d343540093380edaf3364cbd833563ef53345c9f233255c08331a5e9f32ad5dc232ad56f13298b96b3294566632797b8b326fe35b3257fce6322d27db3223679231fd824a31e8375731c296a531ae292931683a3e31431dae3130890f30f80ad330c4f43430bc375a30879c7f3051c5c3300cea242fa0b4332f90f94d2f6571002f6051e92f5b80cf2f4614d92f333e192f0dbfe62ef4becb2ebfea3c2ebd2be62e961c0c2e91f7da2e91dd302e751b642e62241e2e30cd672e07693c2dd0d7232dad32922d70ad262d6686282d348e9e2d1807622cdcfa352c65632b2c30c3c92c30284b2c18dafd2c0771b12c075cb62bcc3ad32b3e43662ae41c332ac6aa342abfd51e2abc42782ab766482aa00f182a72cc2929dfbd4229cfedb529a5a9692985e554297fea55291c5faa291a80502911ec2328c6d676281515fa27ea302e27c9825927bbf99f27b06eac27855c252752f862272ce0b3271ad50026fdb85526eb7c0326b2154e26985f842676be1f266008fc25fbb50725a734f4257bb771255744ed253747fc25327472251f69ae250f60442501275f24e71eab24b8260b24a4df0e249055fe244583e7244096bb24402d7f2438631c240bef9824078aed23d5b9af23c357c323c1b9b723c1b5c723927e63235882f72354eee8234efb6122ffb93a22fc6e4522c6fd13225d8d5821e61d1021bd077f21415e2720f8df1b206a2f3f2068eb17202752d12021edb71f97b7671f7f73d51f7bcadd1f60408f1ec7b4d11e922ecb1e7f4ff01e4766161dfa79401dd299181dcf586a1d75042b1d3c74e11ca7d9341ca3040f1c91adf61c8a2e621c3fe8bf1c2e35171c0b02d51c08faa21c08724a1c07f9991bd5e9a01ba638251b7f484b1b7a74821b21e8de1b195c3f1ae9817f1accc1b71a98a2bf1a8b58471a7d4cb31a53e4111a4162f21a300c911a1e12ad19d8fb5b19d68b0e19c26793199b9fe6199879a419630e561948ca7e1927a0d8190fa19018e4d37f18da57c918d9fa8118a3a9371886d382181cf0e717ff8b9d17f6af8a17e71aab17adaf7017a7f55c179c2c8617539ccb174612d81735869e170f0f5a16bba09916905d7016869e90166f2df21669366315fd085415ec71d015ac6995153445bc15116ca11509fc371508cb9b14e3388714ddec77142f9c6c140e87bd13fb730213f354aa13f12e9813c9fc2e13b3298e13ae7e9b138ffea6138492d41379d3af13782fd513724fab1349c96a13476b75131d04a8130e25ec12f8a72c12c3f711128743b812811aa3124a6af4123ce807122000c9120ca7b411ee769211c5a4f611bfa81611ab4c901188b9f911702a841169f4ee115c388f11509160114f1e3611261e90112052f11118eabd1114f92211099b041108ca1410fcab6a10f2a9db1095dfe5106cbafc10489df11016f3f20fcdb10b0f7641a10f6b9ede0f6169310f5a27c90f522f650f3f10020f1ef3f50f0c7cf60eee4e7b0ee2690a0ed15d970eb14c510e6cd6560e4d987b0e4bb4a30e1d4a820e1177b40dbebea80db4d6120d7aee740d64333f0d2234820cf1c06d0c99d1db0c97f0f70c96850d0c44baea0c041e350bc502960ba76f520b6011760b01eb300ad820060abeb08d0aaaa1ed0aa7c7b50a5c294f0a570d0f0a4732660a3c106a0a3b77b60a2d37a30a1dcd7909f8cd6b09d7c3020988d085097e4c9a0969b2c109640434092cfa63092940e10921c4760914e96c08fe313708f60c4608e76f9c08ae5e0508a39762089a770308669618083132fc082adb16082995eb0817593d0804fff207f17a7307dc1acb07cb6a0007b13c12078c3540076077a70705dd26070101c206ee422306e43b3806e2a09b06ad32af069c61fd068d42fb0629f1a2061a398205f9729305de361b05c4230905b2b9e6059338d605821eaa057a1de404f78bc804e7751704e405f804c305ea04c1d1e504bdfc1a04891ac60487b19204767799046ddc2b0464d8b6046353e904157d5003f9f3c503edde0103bff23703b020d403964b6b0392c18c0391bc07033f5f4b0304f3b802fe55f502d2fd7f02c532e102c1eb1502b6ea0e02ab127702a0ec4d0297d9c2028de82302407451022ece6b0229269f01e0392701d145d501ca75c3017f797c016d17610115c7b000fbdeef00f94e4600edf1f000cb40b8009ffb8d008359160063ef48003c59450023ec08
  | 6 => 0xfff17c22ffece0ffffe0385cffce1a7dffad15b4ff94e92aff8e951dff841a94ff7f4117ff554b09ff1f3047ff1ec686ff129454ff017b18ff014459fe969683fe7f90effe6f9e7bfe39f770fe2b1e5afe07096efe067606fdedc804fde671dbfdd37ca3fdad3346fdac53aafd519cbefd438da6fd438449fd3f8917fd2d160dfd1e647dfced90adfceb255bfcdb7a65fcacf576fc8e31f6fc72fac8fc6f9e5ffc46acfcfc2fc87dfc17679dfc0a3308fc04202bfbe62072fbd72f85fbd03f88fbbc8aecfba361d2fba32b3cfb9ac63dfb8a04a2fb886d19fb773d2bfb73b733fb6b3c67fb639fcffb629c97fb3724cbfb0ea96ffaffe731faee350ffadfe282fad9eb9cface7e7cfab3ceb3faa509a2fa918b6ffa8a26bcfa88cf5afa748642fa51e13dfa3eea99fa2a34b3fa1432a3fa10bb6ef9c18b9df9b91895f9a4de9ff982063df97a1beef976632df9662d70f95e9f5df9442971f9314d4ff917e619f914e7edf8d2315ef8b6d5cef8aaad87f8a6b1a5f88ab08cf887afbff85cec66f850c1a2f84f34b4f844594af82a49a6f7d89b44f7c1a7bdf7af8f94f78fee2bf78bb55cf77de070f76d6b6df766d289f74e04e4f7056b9af6f43ad9f6eeea94f6dcb328f6d05438f6c3f7dcf6bb8270f6b4b579f639783bf63905d5f6337ed5f6313d4ef62724cef62259ccf60ad8bdf606da01f5d9c11cf5d89a19f5d0439af5cfeebff5bc91faf5b4158ef5735bc7f56c079af531961cf4f4b387f4ef8355f4e0660af4cdcb6cf4c6d99bf48d1059f43cae9df42a82b9f4257ac2f423eb1df422851af40990f7f3f03af7f3d45fa8f3d36177f3c2dfbdf3b6813ef3b0da72f3aea626f3a409ebf3a2b4e0f37e7843f373c931f361cf82f34a6e1cf345ea06f342ca41f340c5aef33d87f9f326f78bf31fd052f319c3f1f3159e2af2da3e91f2c165bbf2bd9deaf2a6feb3f2a26d7bf289c599f2619371f22d691ef215e963f1ea73e8f1df404df1d908e9f1b86fc1f1ab79a7f1a880c2f1a3a82af19f2f80f188e157f14d1a80f13efca2f1392605f12682d8f11d5bbdf117d034f1042e62f0fcdd02f0e4b34df0a90cc3f09890c5f05ed930f051cc60f00c667bf003461beffad6b9eff99181efe7b9ceefc9eb46efc17cbeefb4b1f6efa930b4efa8346eefa7a4afef8c5823ef7b48efef76096aef631111ef5f2ec5ef563cecef468f2eef300c77ef17c07cef11d382eeee18b5eeea21cbeee78f36eed52656ee954bfbee69ef41ee346181ee31c66fee17beb7ee137fdbee06f8fdedf6d739edd00ae0edce1ea1edcd4ae4edb1f551eda32176ed9ec879ed987118ed826a8bed756d87ed4e3a5fed2c5b67ed2960d5ed28dc2eeced7b80eccd8c11eccc03fcec868b7eec6894efec5d2090ec59197eec4cc959ec3106eeec222b61ec12510aec1100baebe4cabfebe1374eebe0ac8eebd751cceb90bf5deb8d6752eb8c1b43eb831b4deb81e7a2eb7f3ae5eb4649c1eb2c8f10eb259beceb021d06eaf492c6eae91ac1ead050afeab53471eab22ca4ea811193ea7211feea376de0ea35b865ea2c833bea264460ea14b39cea0d5b06e9f370fee9de792ce9d3a330e9ced66fe9b10be3e9b01841e9a16b6be986ce2fe96af133e9678b0ee95dd206e95520c9e9470b29e9374d60e90d42c3e8ee20a8e8de3675e8daba68e8ac04a6e896d4b5e8836427e85fe698e84af89de82e2426e808da47e8086d4fe7fed31be7ee65a5e7bd254ee7a3e320e79cb573e7969296e794b3f5e78ebd93e77c9063e770ef98e75986cbe731d4e0e71ac709e6fc2b9be6f51e0ce6f1f2d4e6f114c0e6d55b3ee6cea1fee6b309c7e686c47ae6849ad5e67c0e8ce66a2ab8e665f896e6369bfbe62dbeeae5f98abee5d18bb7e5bcac85e59b5c98e5990463e5906582e588ecdfe572ac05e56e1c30e5441355e53fc644e53b1a41e52098c5e5183cb0e510a6d1e4fb872ee4f7610de4f07e72e4ebc459e4d254e0e4cfe6c2e4cfc30ae4cf466ce4c941d2e4b43ed5e445e3ffe44164cde43171cce4292985e3efa062e3ec282ae3e3e952e3c12d83e3a9596fe38d74f7e37e074ae3589d5de32f1f60e31f6d76e31e73b6e2fb13efe2ef9a00e2e9f651e2e5762fe2cf0fafe2bbb3c7e2a55b41e2a3e1bfe296c586e27aae70e2778d6be272ba79e2495314e238dbc8e21369a6e1f35344e1e6c659e1c89ec7e1c73cece1c67d1be1c5d31ce1c4e065e1a514d6e19f4e8ee19e70a7e18e25e3e181ce8ce17e49c5e171884ee1691929e15bd8c1e14ae06fe1411635e13f16f5e134d658e0eecaeae0e68452e0e207c7e0bc5a4fe0a9b722e09a590ae0999f90e07d06e1e0678a3ae04159fce035b96ce01f9e19dff3f6e4dfe59ac5dfc2c4bedfb26527df9e9644df7cedeadf786c80df6d4e4cdf405098df16fbe2df13d65bdf0492ccdefe4a1edef386b0dee462a6dee32612decae459deb9ab56de9d5272de980fecde651844de51875dde3f1b44de288f9dddfb870eddf3f86cddde0bf6ddda2b73ddd8f81fddbcc0c7ddae540bdd8161d9dd7feacedd7eeed4dd66f00fdd471f46dd45082bdd3ad3f3dd231c67dd1e8126dd042db5dce52f0ddcde1253dcd0add9dcae1a9edcab981ddc8d6bd6dc5f5e8fdc55b253dc4aba8bdc40ed12dc3b69c0dc267b0ddc24b1c5dc1f1451dc162cf3dbb23682dbb113bfdb98da36db92bfaedb7a25a2db73537adb42cfdadb26ad4fdb22fe82daff0b62dafbb7fddaf7629ddaf4e49adab7f343dab4a84fdab2b4b4daa403bbda96cf6dda5ac943da5ac23fda5a0d4cda56b2d2da522a6ada4f57b6da4c20f2da41fa56da3efbbbda25238bda251e54da144c5bda0af13dd9f6e172d9f54648d9e8b5fed9d505c9d9b9c151d9a8b48cd97e701bd97b4866d968a299d95d969dd94a0b47d9457947d93bc306d9254bacd90be1fbd8f216a3d8d9f6fad8c8d98bd8c56eead8c4e5d7d8bf54bcd8a1f75ed89eff73d89a1dded89848f9d88ceb0fd88642efd87d8221d8615adcd85e7521d8327bbad81b04a9d817ff3dd81743fed805dcded7f2cab5d7db837dd7a72f2ad79132edd7467608d741178cd73b708cd738794bd71c5a1bd70cb5dfd70b5091d6fdb629d6e3242dd6bae656d6b320efd69e1e5cd69cbec7d69348e5d678432dd674ec9ed66d6eb4d66bd2cbd6693c62d667303fd5d1ceecd5c7d510d5c49586d5aee8e4d5866d22d583da0ad57f3624d57efb02d5514fa9d54ab06fd53ad438d53574eed51f6f85d51d1ec9d5035073d4eaf802d4ca8ffcd4c3fcd3d4c363cbd46b2887d44e62c3d3ff4164d3df8bd9d3dc28a5d3b9d6cad3b61692d39de7b0d3901b36d38c56a7d37a0eb8d379f5acd345bb6ad32df4a7d3210e36d32029c7d31f8657d31aabc0d2f0cb39d2e4b81bd2e30dd7d2e188d6d2cad8bdd2802b22d2781809d2714901d26a567bd2645fbbd2478ec8d240a5c2d20061c6d1b8eddfd198d3a2d18930d4d18421bcd16b0943d149cd45d13b7960d12c9ddcd10a47e5d1042659d101711fd0f676e7d09fcdd9d09bd9ebd09a88e3d096bf1dd090b19fd07e4e15d07ba5b7d0445041d02e2596d024c703d01c4e75d01399bbcff8936fcff80418cff64a68cfedd8e6cfed38c5cfea2893cfe9ad82cfe90fb5cfd4145bcfd00841cfc9c6d7cfc2d30ccfb52d24cfb2bf65cfa6df83cfa55da1cf6a5b56cf128135cf1209d0cf030a06cee03fc8cecf6930cec97842cebd6672ceb0b745ce666a03ce61e398ce5f5708ce46a55ace33de27cdf24caacde20905cdddca29cd9eed2dcd96bd48cd931a65cd7a1540cd6bc124cd5ea77ccd4d1417cd46d370cc8aec19cc75b75dcc5ce6dbcc5bf0cfcc518f63cc39c990cbffb0f5cbef0fa2cbdd3698cbd85df5cbb5d294cba5f615cb9eb80fcb85af7ecb749dd1cb6ccb55cb416901cb32889fcb10940fcb10385dcafc2fc2caf49fb3caf49a2ecac03c93caa90299ca8669bfca796a3fca74bb81ca736bc8ca52603cca4e6b02ca2ab94cca258f9bca237151c9ed86cbc9e42f62c9d067c0c9c4c7afc9c0bb91c9a66d8dc98617e9c97a3a83c95efa89c95bbd9bc94f58f9c9212fe7c9124b5bc8de8b47c8dd429cc8b83d40c89f6fa8c8748ec4c8507a92c8454e2ec831cb0ac82d31e6c8272433c813b3a6c806d2bbc804164ec7e51de3c7c24653c7c02730c77defcdc75f707dc7504f5fc7288260c6e568a4c6ded834c6cf0f50c6c57e6fc6bd503bc6b8e259c6b8525bc69c3438c675a217c666b893c6273333c61e04a8c60da2efc5e517c7c5e44c7dc58cef58c57c0caac550e01fc54a2805c53de200c52c68cec527a688c51f79b2c51a10fdc5163d51c5129a38c5005371c4cc847fc4c14ff3c4a9da73c4a5c371c497d862c47159f3c468cfc0c460ceb5c45196e7c44e0028c424be68c41b3b8bc40cba5fc3e44d6ec3e2e64ec3ce9334c3b5aee2c3988d1fc38f77aac37c7afdc3777e5ec36e33b3c35ba0c7c34f6d9dc34c90edc34194e2c31daa0ac30e6b28c3078889c30194d0c2f08935c2b3df52c2b07f92c2b005b3c2a46c09c2928802c28f07f8c28bdce2c289fa6ec27538e1c26b6cf0c2256381c21d3361c219e1b3c1f47d4bc1cfde88c1bdbd7ec195ea9ec17ffea0c16476edc1461f5fc1284bb0c1271fc3c1236ba8c11f5bc6c1121e0ac0f6152fc0e42dcbc0d61992c0d22264c0a60d0ec0a3cdbac0855db0c055321bc03167b0c02077cfc00dfb25c0039f3fbff94d89bff23585bfeab908bfbf5eabbfb9a0d8bfb897f9bfaeda5dbf93b1d3bf6ae274bf5ec64bbf582d67bf49d241bf423a0abf3a0f16bf377f92bf23cf8abf1ed43ebf09ae71befb5e9abef3c923bedefa30bed22e9ebeb124babea60112be8597bcbe826738be813698be80a611be6dbf5ebe5e295ebe48c5debe314b8abe26e664be20607abe10613abdeff847bde8a0b4bdc1f950bdbfb856bdada02dbd96c0ebbd88ac1ebd7f929fbd70425fbd6c5f27bd658fabbd64528ebd610f9bbd60fe73bd5bb210bd3db05bbd34bb60bd2494cabd240c77bd1c8addbd189c68bd17e8b4bcfaedadbce8cb74bce7c90abce04e4dbcd33f6ebcb3cb3ebcad535fbca0e008bc9c5151bc79d533bc73b8cebc658054bc3c5dadbc287053bc1f9be1bc1e560ebbd0d0e1bbc4ba23bbc48968bbb1baf0bbb16b2dbbb04781bb92c865bb9142d9bb736fc0bb5467bfbb532a60bb4d941abb4c7c77bb41633dbb32583ebb16dcc8bb120c82bb0f8468bb0f2797baf3a5b3baf21a71baf07d5bbad2b7ffbab8f6bcbaa8d356ba9d59f4ba97c669ba93c859ba7b37a3ba77dc3cba618532ba4b389fba36e5b9ba1db18aba0c69bfb9ff474bb9fc0127b9cca001b9ad11f8b9acb6bfb91cf2b5b91ba16fb8fe298cb8c82395b8a61efcb891a8f9b8889e35b861e6c5b8498c04b8448319b82abaf8b7e8e485b7d40e5cb7c88278b7bce9f4b7b92987b7b1f668b7a6bf63b79db521b79a62d3b78feaf0b78c1d09b73e6f5ab7139e36b711e03bb70a3741b7059260b6f30b02b6f23614b6dfc134b6dedcffb6d23af4b6cea033b6c2ff68b6b84d77b6b7a8eab6989a04b68944adb675dd89b6459a8cb63e6714b63aafddb6365829b6302f95b62e6ddab5ecc4acb5ddd786b5da5aa0b5ba5417b5970a96b58a6f9bb5851aedb5585639b52fdca2b51170b5b5036290b4f24247b4ec294eb4e77bdfb4e07a2eb4d99f87b4d2504fb4cba814b4b796acb4b0026fb46f151cb45c346ab45b13feb4515f33b43bbf8cb4263159b4104742b3d95925b3bbee7ab3a46830b3936f15b388cdcfb37b8965b364a999b359a489b35565adb351dfb2b3513f71b34c7f09b349cab8b3333585b32dbb7cb3296975b31e7790b31b0156b31638feb3054a4cb2f65b51b2ecb51eb2e409d3b2bf2aa9b2adffd5b29cb97eb24e8869b23b215bb229e43bb228cf01b220aed9b217d8fbb1fea249b1e4cdccb1ddcce9b1ccc9f8b1bc6968b1999df1b1880113b1764a1eb168e633b14ffe14b13d0af9b13444f1b13064ccb12d1c57b11e2943b11cdc09b10e1d7eb1097a38b100c145b0fbba0cb0f73989b0e11f56b0ce567bb09be7f8b097fbe4b0882f93b085de65b0840924b07c70adb05f0a9fb0514176b0489863b046c2c6b04057f3b03093a1b0276158b00bd4d6aff8bf85aff718d0aff02f3bafd34029afce226fafcdf54fafa6e215afa44f1caf9bb7baaf99d5ddaf81aee5af79fd00af6deb41af6c4148af60d760af4c8579af429346af215200aeff63b6aee9ad1baed5a826aec0baf3aeaea4fdae7f4dc6ae738e4eae6aae69adff2faeadf90c12adeb6226add99919add91692adba9832ada22875ad8b0ac4ad8a8769ad7bc43cad69377bad4e9efbad372f52ad2b61c5ad27b76bad1a0b20ad15aaafad04bb04acfc4c04acc75102acbf47f4acbab334aca5d1baac6bffbeac243c67ac0bce81abf4ef99abf10ad1abbe0c78ababe361abaa2480ab79348bab768172ab651305ab4ff9ccab4b9c0bab367723ab2c09bbab1ea95eab12c673ab0887afab0581f9aaec2f1caad2960daaab294daa8d940eaa743376aa6cf101aa62f976aa385a0da9c1bf5aa9a117f1a9901c93a9809c3ea96dff45a9509733a948ace4a91921b2a91087f1a90cc64aa8fe6937a8fba9cfa8e4282aa8df9999a8bfed1ca8b063c6a88ab93ea886c900a88676b8a87ec9faa87e7b49a878bf09a8774234a868ced9a867c85ea848935ea837eca4a8121474a80cd354a7fb58b2a7fa899aa7f9b9f1a7db5ad3a7c348bea79d1d2da7942060a77cdef7a776c319a771fdd3a76b4bf0a75742a6a7456c41a72b533fa7166b08a6eb450ea6e9f71fa6af1b43a69e4db5a69d2a8ea69869a3a68b0e9aa67054c5a6646a2da66244aea65db9f2a65d6061a63f4caca62b2947a62287f4a61f0821a6075453a604b16ba5fc2fbea5e84ef6a5d969b3a5b1700fa5b1159aa571652fa55028e7a53aede3a5384202a536560fa534a712a4f5eda9a4e10383a4deb02ba4bed3bca49031bba48fca5da484708ba47d2730a47943fda47407a7a4589441a44ae482a43da1d0a435b781a40e16d3a40bba07a3edef17a3dda641a39ef25ba32fc17da32a9019a32a69d1a31aa5bba30bdf30a2e32da1a2c06442a27068c6a26066f8a258c7f9a22978dba226fdf1a21ce88da1ff103ea1d9a66fa1cf6499a1c9e189a1b45dffa1ad9d68a19dd527a17abb64a16d1925a14be4c7a14a26a0a14622a6a14441c3a112dd6aa0fe65e7a0fd1bfba0ee70faa0dd7b71a0c67450a0ad8f0aa0a604fca0a28c63a0a1b28ea08b2eb4a084facea0759722a06c06aba04f3ce5a045df2fa01e22baa00e5ab2a0095a1b9fe7fefc9fde075b9fcbccad9f9793249f8ae2569f794f779f3866389f362c359f0c84589efcab6f9ec84d929ec5c7909ec36b3a9e907fc19e6f4dd39e69dc609e4a1b389e3609c79e0796769e05a19d9dec95bc9dd53b9f9dc8b6569dc446649dab037e9d8969b59d8930f69d77ea7b9d75e2049d6abd319d46cb969d3c852e9d35de599cf87ec19cbd8eaa9cb181009cab2f069c941bce9c4c285e9c4138ae9c0aaa229bc9aa2e9b92901d9b6e70139b681c729b59b30a9b544fc59b2d2c899b11f7c89ae913b39adce1899ad32e169ad099919abc339b9aa226b29a9957a69a917a079a8b14519a6f63669a5520849a2fe84e9a1203769a11ee949a107c9099fac4b799d6814599ce815f99c87548999ea720997edff39979f02f9977010d997581219966cec199618ebd9959892a994cffee990907779903010b98f49b7598dd33ad989128b79882a083987c944d9869310a9848f016984868fc9847119a984259c198374eef98338bf39823600f9810237d980f9b2597c84df697953b6e978febfe978a4dcc9788e35b97793403976e4b019765238c9753788897366bf196c8ba9496a4f2209691f0199659127a9650a2ca964a8c42963f114396380db1962ae5479618b52e9604d49695e9185595c033e79596c1e2958945ca957472f7956bad8e956b8340955e377f955bbc8f955b1b69955242d7954bb6f395413cfb9540dc2a951ddb0294f03f9294e2024994e180a494df3caa94d2f25994c25c4c94bdf78994b6739c94a5ef95949ceb6e949c5c709498697594765f61946bb3d494647a9c9446ca0a9445614b94434b5694320f459408b5d993f7ba7b93eccb3793d7a15c93d57c4d93d3654c93b80e0a93aea4c3937ad43a937825d993541db0934e75819343e61d93412a8f93251c56931b951a930c949192fbb16892f2b6c192ef118992e7108992e5b52b92ddd59c92bed475929f1e70929c0b37929c01479292f76e928f137a926bb17d9262421a925252ca92522e2992419be29214cc2f920a436891ca630f91c57dde91c371c691bf83d3919d8ff59196061a9182448891776d039168eae691504cab914196c7913b96c5913553a091320b7190fb1d5490d4e2d490c795509098b57490927ac29090a7339078bf1a906986ee90663c74904c839a9040eac59037b4c3902e4798902954ed9025cd14902276c49020eeb590187f1190161cb59008ad1e8fff20168ffd2a748fe0e28f8fad50fe8f95343d8f84b6868f632bb08f5af8488f4f1aa98f3f208f8f262ced8f22f4ea8f0503c08ef9af688ef768458ef281778ee4c5188ecfbf648ec758d48ec07a288eaf9d668e9defeb8e8fb8a28e5514f88e2756198df720938ddf65c38dbe9a658dba80cc8db2083c8d7f32d68d7a06438d6f6d318d55ef1e8d4e50738d4b00c18d2ff2ee8cfb1ec58cd7c50e8ccb20518caa53288ca5796d8ca4fe5e8ca26ef68c946b008c2f15678c00e5678be9ff248baedb678b9dbd4f8b99a3e48b6fcd3e8b6150a48b5fea7a8b5eea3e8b33e72c8b3223a18b2e48b48b28fc5d8afe75fa8aeb69a18ae8f3ac8adf60dc8ab61e028a9b28538a7acf0d8a45a6288a2e5ef78a1e3eed8a10202689f104cc89d2c7cd89b9975e89b3950289ae7ee689a4bbee899d486f8979d6be89603622895797328939ff6d891f3eb68902bf3b88fe0cf488fa355788be807f88bde5ce88967bb9889337e788837ab488793c91885faa478850c106884c8c978830543e88189cb687ed4c3187e8274187bc09be87978151877908a68769366287601ca987070a4186ce130d86b1cac886b1b04b86ad6df8869101648687993f8672b1cb867140d48662b3f186523eee8650b200864e5b41864ce0d2864b7058864ae80e863ad1da86167505861085ef86035fe885e3588e85d58e3985c7ed5985b2227485a9bc8a85a2250d859006b0858b8b49858867f985734d8285665cca8554642585525b5e8543288185341b57852f5a168520162a85170b2584f909ed84ebdf3e84c8bad184c4b2bc84bfdc8f84ab9d5784841fdc8458513984578d54844d31bf8439a7e68434afc38434a290842b40bf840544c683f1ad5a83ed039483d0e58f83b8396583b27e2b838c173f8369db8a834886a283439baf833f6ab68336b31982fc92de82ef85ff82e490cc82d7427382d45c6682bf8eaa82b897e282b5a24182a7757d82a2793c82850a9a8276a1328252e01082113a7981f414de81f0b67681d541ad81cc5f38816c5abe8166683781471a778139d13381346e818113226280f4e92180ef57a680c7664980c2dc0280b9a78e8095e422809447c9807e7ce5805c492c80516a3a804e630a80149dd1801285e37ff437ef7fdda5a47fa459457f9e042e7f99ea677f99a3097f9674087f3c112c7f3725e87f308d047ef9f3ca7eee9c917ed78dc77eb7ae747eb6884b7eacff337eaa93b27eaa1f457ea73bf47ea66b327ea616077e9c6fb67e8566697e81a67f7e6738677e4f2ab17e3daee27e2888167e27b3077e13f6a57e1046697df9b33d7df780fc7de22dae7ddda7437dd4583f7daff6bf7dac78917da3dd057d918a0c7d7dbba17d6ceee87d2c63487cf5d8eb7cec1e737cb65e107ca913617ca1a82a7c7db3c77c5431787c3df93f7c368a0f7c34f0d47c2548c07c0b9d977c0566c27befec2b7bbe005d7bb343357ba442497b78898f7b62a92f7b5983eb7b57c6807b474ea27b3fa4047b3a8b977b2b89fd7b05effc7afb99587ae98acd7ae06e867ab4e6f37ab0e62d7ab085877aaa4d497a8a9d997a89064f7a7a07b87a7043cc7a6c27f67a66c5dd7a5799c77a2e0f207a2678237a1d74c07a020efc79f9ac0079f7210379f1b92179dbc29d79d4665679d3f86d79c2bde379ba175d79adc446798b235179763b9279612be87956e9ba794d08727946bd81793918d6791819a17913cace78fcf0bd78c77fb878bfb15978b3a9f07899dc52788b19b478800a37786d3ad37856ffe4784b1b2078484be9782ace0b78299fc57827c1ac780df1cf77ffd2bd77cb2eb477988a757766f6cc774cd083773008af770c83b776f7f69076f49a8176d5e17c76babf3a76b1750c76a54a427699f891768ed6dc766dc5877664875f766163e47660399e765eaee97628063a7613e94b7608e34176014bb575fe547975f46b7875ec4ef975e5e83b75cc8b8e759e92807593ee827558d18b75508365754d5fad7538d932751dbbea750effa175005ae674ac1c0974a8fa3474a1666d7492c3eb746a78507466da54743a65b5742ec4ea742b177573f5d37e73e743cd739cf452736d2b24735e5a1d73427027733993127339129b73363d077310043c730c0b89730802a172f89bb872e0aa5072cf419272ba9e9d72b77ebc728f4b8c725431ec723c445771f214a671e7354571c7b83971a6d05d71790dc1716644fa716401db7160b9c87158af3c71538d5f71486e71711397a07112bb837109fc9a70d1e64570c144f270bc3c3f70bb94ad70b6288b70a939e6707437c570608f307057e4ce7051f0a3704f2bcb704a9a93703f6fcc702f8b417029a1137018249670139e5170064063700474b96fffea6c6fc11f416f6dfdec6f6391a56f601dc06f57497b6f4c5dbb6f464ade6f2e30e26f21e87c6f1684206f09757a6f004d786ef0ef416ee25e9c6ed83f676ecf949f6ec00a836ebfef216eb823e46e9fd1086e933d826e89c4816e5597146e55435c6e526dc36e4ec5436e334b596e2d33c86e1eed256dc85c8a6dc33faa6dbaa4db6daa0b876d96bcfb6d8c60446d7372636d705b256d63186d6d4a094c6d47b9596d238a076d1aafe46cfd451a6cf7003e6cec87166ce58ee96cad2bdc6c88bcec6c8752136c840a446c5e6d786c3c3f606c22c9036c1c168c6bf239126bda4f756bbbacf36bb1a8526ba3fbde6ba361586b9c0c696b764bb96b60edf36b57c57b6b4200b66b1908cf6af355e16af039f86ae56dbe6ad507206ac00b236a75b9296a3233926a1f059a6a1858cf6a1017506a0c276c69ee7e1969e8f3a369c54a0469ac063369a06c0d698fdc556983feee697ba2ee697b121c693fe464693d32ae693c953e693b8908692d98d06922a099690b231f6905dc1868e9ac8368ced64f68aef6ed68a28afc689dd0356886aea2688547d068765e426838dddd6813ca32680288c667e8577c67e6821467d4c5426799216a678ae464678a097f6772faa56734171767189e956704ede966dc9a4366d3d24066d361bf66c99ee766b1963c66a09cfc669e91b866986b02669766776683b28e6669d185665dc08e663f01cd6634112266311f18662f0b53661bdd816616a7246610bc78660f87ac660813b0660663846603906e65d2785b65ba64c765b95dde65a692d7657c20cb656371336524bd7b6515394a650c182764d5d48f64cc1d1264c4fcca64c3ae5264a81f5a649e6d3664921674649193fb648f308b647c229b64715b3b6468ad8b64621328642642566425d05464146f5a63f3d65763de597463d34c3863b68a6c63b1f934639f3cbb638506786361a17e635fb75b6357cd0c6355930263520952634a1f16634236e8634094f7633edb076337ae9e6310d92a6305a29262f47a5862d6e8e962c5a47162c188f162b7488a62addf1b62a00ec96299379e6298f0386298cddd6295ccb3629245cd627fd57d6251c7ef62481f32622387e7620b4fcf6207701561f32ed561f3198661dee6f661d20d2d61cbf1fd619fbef36181391d615aeb2e6152605e6118abe261172ac160ec4dfb60e4a9de60da9bcb60a2733e608cd655607b392d6055e838604cab8b60386c786017aba36015a4d95ff8d5505fe889db5fe1b9b85fb5e01a5fa9245b5fa4ed4f5fa1a8815f957fab5f7a9a795f67c0005f532b6d5f4d78e75f3d3a175f230b945f1e07815f0ffe485eddaa5a5ed50b0c5eb1ddf75eacdcd35eabdd315eab5c2f5ea69e245ea3748f5e7eec0f5e6a94555e6718c45e5282585e4c11285e4408ee5e40429d5e1476c55e12b85f5e10fae35dceb24d5dba43515db43cb15dab40815d99328d5d6c75b35d56de4f5d51480d5d4f358a5d2a9af75d28c5ef5cf1b0905cda9d065cd1062f5ccc339e5cc6cb2d5cc09c5d5c95e1f85c80a85e5c7efc405c7d82ae5c6e9a975c62d02a5c573aa75c35b5dd5c355b735c215e685c1996cf5bf090345bde26155bdb33525bd32fd55bcf15555bc9332a5bbaabbc5bab0cb85ba9c8385ba508fa5ba4697c5b9539735b771aa15b5b79fd5b5b37185b4e0a665b360ae75b2e03085b2c78d15b1d52545af448605aefeb445ad40f515ab658c95aa70db45a9493385a707bb25a4ecb515a4e2b315a26ecf859faa5a859be5e9e59badc0659a6606e599b5c8059995cbe598aa965597b3fa45978925f596f72515967abb2594b8bb6593ef34e593dafdf591cbee55914a65d590abc5c5901602b58ff6dee58f08a9558c8e7a858c8cf3158bd80fd58ba0bab588c1c1c58831d8e587f97ae585a12045853991b583f8248581b61e057ff15dd57fc12b357df254857d031ad579fc759579f0f62579066e45782ec955731411a5721f24c5714ca40570e2b9256b9ac2456add83a569eff485682f0a0566442df56628388564ed0595641d826562adeee5622fe28560e537d560d07ef560895fa55f525de55eaaae355ce601155ab8a18559595405592509c5588406e557231845567b2e6555bf761553e20d855313fef55250944551a4fe054d0536b54ba367c54b37da954a7e6a354a34413549a0e305490608b5489e0705488fe515486a38254798c5d54679324543155095402fb4d53f92b1c53f2515153e3489953c1503353bbe26b53ad1ecd5389da7e5374c083535a5b7a5359440c534a63d6533fb72b52fb217f52f8e99c52d39ecb52c2cd3f52abd0a8528e462c5271d8c0526ff6b7526328b05223a35052168a3a5210a3dd520a7ddd51f95eeb51f7885451f4426551ed2bcc51d296685197ba9c518c99b55176cddd517492a8517443b451587bd75158635d511d29005119c25650fda2cc50ef23cd50e2323050d9563c50ce8ed350ca266c50c841b650b94d0e50b56283508f097350738434507305d550711d5950511ce05048b6c2503e493f50221dfa501e500e501ab264500e30bf500341474ff0deae4fd8482a4f9cf3be4f7d1b6f4f6540434f531b924f505d234f0659364f0545a44ef295734eebea704eac75d04e9ad7434e7f03754e6b9f9b4e65b9184e65b0794e53e2b24e4a58064e471d424e1d59ef4e06daa34dbe4a1e4dbb22634db65d7a4d66ec114d50ff4a4d44cdbf4d381e924d17dbf34d00d5864ccda5654cc95f114cc33eaf4cadeb2e4ca709424c9619054c8e20054c8c83de4c7ba51d4c77762a4c722d6a4c443de34c400dc14c3336204c23a6444c07a7934c03dca84bf8bf9d4bc88bf44bc45c7d4bb809844b8ccde04b7cb7ac4b78da724b6f0d8c4b6a9ef34b5e27f64b5d2f5c4b546e024b41ec554b40500f4b2acebc4b1ad5584b10102d4aabdc374aa07a174a7806aa4a57be8c4a30103249fd23a649db788549d857b849d671ba4998c1f64993cc7f498d2bfd49768862494e40574934c3b24916f285490e3c0c48fdd59548e81ccd48aa715c48a3ae6248991e75488516664881ac1748781993484276e448406b6b481adc4a480d17f447f9809c47f8c49947f857f847dfb88d47cd929447cb9e6947c308044779d17c4773d76b476b102b47678ec84750b937474d543d473526ba472e87874722d794471d3e844713fa47470eb57947090df146cc716146b4756446a6d930467c915546738316466ae74a465cd673465a59c546447e3f46377a7a45ebcf5d45e7772945cf514b45ce838245c9447545ba579845b5aed945b373b4457070cc456c11e44560f825455ee2cf453f09484539de1f45365ae8450c64854507157e45016de544f7fb4b44f013b644bb1d8c44a9b71c44808248447299314463d4494460ada64458f3564456651444378a814402fa6843f261b243da647643d37dd543af5b3b43a69136439d96864387b38d4373d6764368fe1343248e9d43074bba42ee0fb342ed3e1c42e652a442a23b96429ba8274289bfac426a9c2d4247212d424166f0423d4be5422d7ebd422b3fad421fbd89421900e64218746e4213a3f0420ef21a4206ad4a41f9e68141f843e241e6313b41e005af41da237541c155c541b1828d41ad160b41a7868c418809b4416e21bc4164971041608db34148132441454e27413f6a66411ff4dc41162a6940ddff9040ca217040bf0f8240b61a85409b69bd4077d235406b2b8d405c4d6a40382fa9402c0fee401b149040198f0e4019873640191c8a400ef04a40001f953ff6b87e3ff0cf633fd3b74f3fc31f9e3fbd527e3fbc89923f9e2e4f3f93fe043f8992f93f7a9bb23f6f0a453f6bf2cf3f5f3c813f4ad80a3f2aec753f1d616d3f11b3c73f10cc5d3ef1f6ef3ed8bcc03ece27313eb017703ea395cc3e8e5ca33e69dc503e52bec23e3f98043e28dea43e1e0b123e1449183e0012a43de7baa73da4fff23d97c9543d8eb35f3d7ac2133d6c4a1e3d57a6ca3d4d97573d3db0953d05233e3cf317ef3cf2ab1a3cd4c4c43ccac6983cbde0533cba0c7b3ca8dc9e3c91157b3c7faf3b3c71ee813c6ee0ea3c6195ca3c6096063c5b2c593c51a1ad3c2bc0933c1d8bd23bfaaa743be80fa63be31e4d3bdbde633bafab593ba4f0463b8e984c3b84de4b3b6952ac3b4bc03e3b4844e43b402a2b3b3a3fc43b362cbb3b3402dc3b32fd0a3b10275f3b0a97503b081f2d3afc57593af1a7213aecd4f83ad3a8fe3ac19a113abd47ee3ab280a23aac1cd93aa2ac5e3a88e5243a46a8473a41238f3a25a7c53a19080b39f35c4239b9584939b8767d39b68952398be3d1398623e33979d2e9395d654d3959a6043936afec39322981392677303900716738d238aa38cfb2e938bee27938b08fd538a12ea53895843c38848d03387ec5cd3851ea0e384a5b293833b799382d98dd3809b24a37f93f1137eedd8337e52fde37e0ab7737dc7eb037a0744a379bcd333737a5bc3735434d36f0ab9136eef33136edbcdf36b5e0fc36ad7d9b3699e9f8363a6f40362c1966361d33753602a56935ee1b9435eb1fb835e6dd6535e21eed35d8efc635c6c4b835c4c60a35b4319b358792a0354e2e3e352bdb983520ec543516b7c93509ea1335058b6834f33b5a34d0db6634a4061334867a88347019743466bd1e3453ae53344ef6e534345cc1341e0aa1341ad0de340ab8f633e02cd733de854133d9713633c7886333be385c33bcf88033834bb73380edaf3364cbd833563ef53345c9f23320cad032ff10d732d8e10132b4b4a232b276c432b16601329fc2e4328af6873274b5dc3268d4c73252a9c732485f243235781731f153ef31ef11ae31c61c8b31b8239131ac2da831a2303b319f04e1319a45ee3194c0f7318c533131869c45316ec5dd314854fa310e9a3b30fe21cd30fd92c530fc201930d9d75a30d8aed330d4cd5c30c4f43430c0312d30bd33e830ad53c930a2e93d306cbfbe306757c13057bd78302af627300df6f13005b5ef2ffe020b2ffb64b82fda165e2fd87b0d2fd80cd72fc7c3f02fc3b6bf2fc0c9082f9df8d02f7b64662f6c8a882f4e0d3e2f4653e82f4168d72f171f212f0fe5992ee5f2f72ed1c2272ecba7742ebfea3c2e9ed9762e9a219d2e9190662e8577f12e62241e2e457c812e3928152e38e3032e33c8ec2e324bf62e082cfe2df4eb4c2ddf84a72dad32922d9549972d9461642d05cab52ce774182ce37bf92cd90f262cd901e02cd3abcc2ca8ee1f2ca1455a2c9ab0222c77a4572c769cd82c70dc4c2c5f160d2c5c65bc2c376fd52c2c47ea2c149efd2c1449c52c0079e22bf33af72be66bfb2be282ce2bb15a072bab94b12b9fa6602b8abcbb2b7110eb2b5422f42b41b2652b3219012b1d587a2b1d1d5e2b17799e2b091c8d2b02150f2ae8aa552accee3f2ac83e7c2aa4a1b52a9b6a492a9135ed2a84bc282a7cfccf2a72cc292a5788a92a505a3f2a450c832a4493132a18e3b629fc82af29f0b86c29de4c0529dcf58529cfedb529cbbe7e29c4d13129a5a96929a551db29898d1e297dd2a72979e3b5295ed991295ad81029598617291c85532915320a28ff0e0028f2497f28e75f8f28de43ed28dcef9328a735ec28907161288411e0287af85228686d482863eac92824a486281594e828156f4728121e7027faedb827dccfd127a691b627957418278e5f42278d469a278ae75627856942276cc1262764aef4275a378d2745e3e22726a7de270bc5a826ff710826dce0a626bdb41826b9ef6426a8701d2699147f26705e2c266cb4b826598f1f2654bdf92624a413261dcfdc261d0615261c6183260fe26b2607e0cc2607568825ffc20425f6272a25f0c75e25a734f42588b183258405a225716f2b256a78b1255120de2548392d253b008e253abb222525a9bb251f69ae25161fa42503cd0524f48de624eca7e724e4af3e24cdf8cf2486e69d2464f166245f9b942452b11b2439643c2420f631242076d02420146523eec0f823e6155723e5366e23dc4fa223ceb66223ac04c5238ac316238683cc2384e07e2369480b23681b12235577e52354eee8233259ee232f42eb232b9f1023191e09230d91ed230d7c1b22fc6e4522f854ce22e2619f22c3d99822b234e522ab53dc2299b22a2208b0ff21f3119a21e7c6b521e61d1021da361621d35b3821d1c2e221c0d5622188936021875aac214115ff20ee6cad20cc34cc20b03e1a2088d9cd2068a42920638d8a205dbfca20588247201f23c0201b115e2018cd202010cc151ffbef4f1ff6bf7f1fcf2b091fca69e31f8565f21f7bcadd1f766f511f5baf571f43e8e21f41b6501f3b5f7e1f2b5cb61f2986cf1efcc1d81efac0791ed576c01ed0e99b1ed0a1521e92247f1e8716221e85a8891e77c35e1e5426621e35793a1e25fa651e23f4101e2399a81e17d5041df328f21dc32f7c1dc2891a1d88f0201d7a79bd1d7457521d687aff1d479bc41d46a7581d3df8851d3b872c1d311b961d179ed71d1048321d01919c1cfbd5151cf9737a1cde32141cd6ad791cd227081cc37d041cbcf5681cb8cfbd1ca1070b1c9791da1c7c15981c52e5561c4559e61c3fe8bf1c392c1c1c2315b61c08faa21bf28e791bd5e9a01bd0cf761bb685b21baed36f1baaa65c1b8a8c5a1b7a74821b6c2de11b68d6481b4cd2f21b4a9eea1b4138df1b36bcaf1afd222e1af0d7711ada73701ad515631abb29691a9444791a8000951a6c3d6b1a56feaa1a4ca88119e9cc7519d80f3719a5da66198211461941a451192c5154192ade20192a79a9190fa1901901e35518da87de18caf53818b79b4e18854c691882424a187b25e8187a91bf18633094185bc00918553f98184a5701183d9d4e181467ab17bf667e17ba3b2f17b7d4b317ab4b84179c2c861789ade6177dcef41777bc54175b9d9717461a40173045f71720709216f4706216de3ac016a50220168343df166f2df216673a641665f470166440c9164e09e31634ae9b1624330f1616b1a7161686d615ef3eb215de18a215cea12515ca8b9415c72a0815a7d85d159efd03157b6f36155fef53155a703b15501691152dce451521611b151f358b1519287415139fe71505838414f3d43414f2306414e3388714e1cc2314bddaa314bce6171498309a14709ff714701860146eaacd146e1b78146a38651435d23f14150cd31412033b14081de81404a5d913fd1dbf13e6cdcc13c9fc2e13c2f45f13b879db13af36fe137bae4a13782fd513712027135d374b1349361213424a35133689aa1320fa9313101440130d22cf12c3f71112c159db12948b32128072f6124eaf0b124a34e712431647123ac24a1238ee4d1226ea83122475b41223dffe122000c91215c839120ca7b412078e2911ed072a11c79e4711bfa81611bd9d341194f84f117f612c117b55dd116f91a21169f4ee115c388f1158bd1a1130a2c811048ec01100b26710e4867710daa9da10d92e6010cb233f10ba152e10b8eae8108de243107d2cdb107204ac103d5072100d00340fe3c5a90fe332fa0fd8e8cc0fd74cb60fb8c27c0f97c7560f9654a20f90aad80f6ebf2a0f6c1d200f661cff0f4d9e2d0f24e8060f1fe9810f0c7cf60ee1f78c0ede5cbc0ed0fe690ecf11cf0eceef180eacbb190eac95200e9800fb0e86e8540e7f89880e76a9840e757f390e738d1b0e6211a50e5a091b0e3fbb670e35bf430e22f6900ddece0b0dd2a7ec0dc041510db94fbd0dae59a20da68ee00d99d0060d812c3d0d765d3c0d6f1f6a0d5c65320d553ac80d381afb0d3743390d2785f90d22d64f0cff8bb90cf9e39a0cd2a1fa0cc53e420cc27bdf0cc11e0a0cb92bc00c9bb3dd0c8dd95b0c7d7fe80c7a17d20c49ff870c4029b20c3cb5070c2099d60bb5a1210bac53b20b9c3f970b9bd4370b72d24c0b67f2510b65517a0aa7c7b50aa1cea60a8c4f940a87e5720a81fb450a803d810a4ae45b0a4860120a2ecc9b0a2d37a30a16b26509f8082809befc1709bae73709b9540309a85b7209a50f05098e6eb7097c6189097b61d70962691f09569d5309480e130945f0a5092cfa63092940e10914e96c0907fb0b08f1948408af751d08ab188208a64b9f08a5818808a2565508957a1e088a4ade086a4890086590b708590851083acf98082db9d0082995eb08162d6f080e133e07f9f7fa07f89e4f07b5d03507852e630771fc8d0771e22b0768229b0757ad980749448f0740ed53072cc24706fefbf206fd5eeb06dd851f06d5fa4006d1751206d1329206ca67c906c757be06b7c8c206aaec530670588d0629f1a20604345705db98e505cbf5c705bd9bd105b2b9e605879eea057e27b305717f42055b5b92054dbfde0542056705196e7b0517b6fd050b174a04fc56f004fa342104d6d7da04cb0aa004a1225304a03e0e047677990473ddd1046a3436043df8f2042b3a310427c115042368b6041bf64504157d500410022d03f5500803ce73af03ca288c03c4926d03b9c22b03a10291039f019303954d9b038aa32c0387bad80386de01036ac4760352aa91034e0314034cda360333d659031f393602fb1ddb02c1eb1502ad6e7b02a8cb980293488a027407c4026857a002508024024793c1023490ec01fda2cf01b5aab101b0c6bc01a1275e019a2e920199007d018a6d0e01706aec016d1761014ec02b01419f57011a4c9a0118bdbb0113d542010e9af500fbbd0800c8a382009ffb8d0082a33e006c39b30023ec08001ff414001375ac000cbf36000379be
  | 7 => 0xff8e951dfe9f4b1afe718741fe685cfdfdf35342fd8506c8fd7ad0ccfd30c350fcf9d533fcb3f5f7fc76bf5bfc6f9e5ffc5d83dffc465fe1fc3f0ce8fc167efefbd72f85faf1d515fa90140bfa900f66fa88cf5afa5925eefa27c675fa105623f9b8e1bbf975cfb9f9662d70f9468ce6f91db746f9193d11f914e7edf8d2315ef8c1244ef82b7957f8049b61f779a1c0f76d6b6df766d289f757597ef7056b9af6f9d0b5f6f8fab5f6d5bd39f6ca94b2f69d3dbdf6505507f5d0439af5bd0ef3f5b04e35f553bb3df547e128f53372edf4be1e7df4637499f423eb1df422851af3e9f06df3cf57eff361cf82f34f95abf31fd052f2d0ba32f2a6feb3f2a26d7bf28ba424f22bb1c5f211582bf1d30ad1f17c971ff16c0dcef0b0230ff077ccf0f0633fa8f0384790efa8346eee51329dee137fdbee06f8fded19e45eed13c6f6ecf863bcece88b2aeccd8c11ecc11a10ecbd5166ec9cec43ec59197eec55dcacebdc0952eba53f2ceb538696eb4649c1eac218e1ea65da56ea264460ea14b39ce986ce2fe962a209e905b7d5e9048fe7e8d52fb3e8d34f22e8bf9dfbe896d4b5e8630b03e85fe698e84db1f7e805bf65e7ced148e77c9063e764c758e6f94033e6eb7b13e6d8e295e6d33d7ce67a32ade63aad4de572ac05e561098de53b1a41e5183cb0e500b4cee4c41813e44152c7e40d6bd0e3edb2ffe3ec282ae3558a7ce34a9c52e31e73b6e2e9837fe2ce3a75e2c37fcde298cbf5e24fe470e20ed86ee1f35344e1c4e065e171884ee15bd8c1e0e4859be02be7b6e021c427e01ad256e000abeadfe23ec7debd5fecde9d5272de93c8eede75f70ede4cd3e9de2f9a98ddd466e7ddbf2dfadd67e6e2dd471f46dd346693dd1e8126dcdf8294dcc112cedc6b1147dc28ed58dc20208ddc1cb0a7dadf6ad8da5ac943da35ba01da25238bda206389d9fecbe4d9c9b3f3d91b75afd9134394d8c8d98bd89848f9d85e7521d817ff3dd8033fa8d7efc5e5d7cc518bd77bd632d777d16bd76bae8fd7311cd7d70b5091d6e8fb56d67a3b41d6693c62d5279bebd4e8168bd4c363cbd4b0ea63d4a78534d44f39a6d42711d2d3c8ce21d391e004d32c19d0d2cad8bdd2ae89cfd26cb7c9d2490101d239c36dd22b5315d21487c7d1dd99aad18930d4d172781ad170e90bd0fa4375d0e1d095d0aa5a20d090d321d07e4e15d069fb97d0344029cfd4145bcefb73cdceca7559ce46a55acdf6cb20cdeeba9ecd69db3ccd4d1417ccfa9470cc9e0178cc7e53eecc5ac488cc416e80cc3ece8ecbd2e48fcb85af7ecb78b62fcb72c537cb3436a8cb0fcc24cad7a3b0cad046c4ca89620fca237151c9925c01c98617e9c96dd8e0c8c7a10ec8aa35ddc86f1cdfc8626685c8611f03c84b66bec82f977fc82a30e6c8272433c7c02730c7960ee3c773b328c75f707dc7591944c746dab1c6b45121c677bb84c61e04a8c5d5a755c4d07aefc4b869ffc469be09c41b3b8bc3f1205bc3ce426ac36eb021c34194e2c2fca2e4c2af4e1ac23d49fdc23743b0c1f44f9ac1f2f838c1efec13c1bdbd7ec0d8bc53c08903a3c06afd24bf8f39d3bf49d241bf423a0abf23cf8abe26e664bdfcd229bddd2913bdada02dbd98b1d5bd610f9bbce7c90abcd33f6ebca8b85bbc71ca3ebc488bcfbc4796d8bbc2569dbb8e7409ba618532ba535ae7ba4b389fba1db18ab9d06fe2b9c6097fb9ba234fb9acb6bfb98fdc44b8e4d31db8a61efcb8a3b554b86cc737b82f7456b82ac807b81c69cfb7e4534db7ad6530b7938f26b7897102b6f8cffcb6e5f1d6b6d59adfb6ca0efbb6c0ec8cb675dd89b64423d8b6365829b62e6ddab5e4c839b5bfefc4b5ba20d7b5a542d9b5776a0cb5556abdb4ec294eb4b81155b4a53c4fb4203d47b4104742b3a12463b388cdcfb364a999b3591d9fb35565adb3054a4cb2d6bac7b2bf2aa9b29e8999b2997eacb295230bb22e1559b229e43bb229b113b220aed9b1ddcce9b1cd1e1bb1a4d745b18f9989b1880113b1520276b12d1c57b10c0347b0dd238fb063534baf81aee5af6deb41af429346af137d1aae4f87ffadd8ba87adcef77aada1cc6aad98ee9dad8e2fd1ad6ade4dace10035acbe7635ac878818ac006a7eabc25581aba431e3ab1ea95eab1d3437aab491d7aa422f6caa4050f0a9f5419ca9edbb9fa9cdf025a9ca05d0a9c1bf5aa949eacca886b9d2a82c16d0a819c276a814c2d5a7f16e81a7d53d75a7cf83d8a795a003a7183130a6dcbc63a69869a3a665b908a658cf29a630f628a5e60a8da5e2487ca5cbfa0ca5a2c31ca5937e9ea569e6fba4f5eda9a47407a7a45e0ff5a44ae482a40d0f97a3df3844a3b9cf32a2d7b95ca22b959ca226fdf1a2185755a1d3a84aa1a7d6f5a195e8a1a1771552a1685195a0fd1bfba0f46c06a0dd7b71a0a604fca04c6621a01e22baa00d4a829ff3909b9fcaadce9fb40b3b9f65c0f89ec5c7909e907fc19e3d915e9e3862c09e3554f79e1c85299df124159d75e2049d0680e19c9a92af9c4d36639c3fa0bd9c3cddbb9c3907d99c1648469b6e70139b32f2119adc8b329a6fbebf9a3051f09a2d23409a2bcf809970efe99849f1569848f016984868fc9847119a983404d29810237d980cbe8f97d5d07297b5fc4a978febfe9774a2cb9758cdb696f27a3d96d9800e96cb16a6967ced16964027d79600a27795e9c9ce95e9185595413cfb9513224694d2f25994c25c4c94647a9c9433924a9408b5d993eccb3793c5e33d93b74f75937ad43a937825d9935bb5e793541db092fbb16892b715f7928974f7927c60bd925252ca91c676c2919368e491320b71910b3c1690f766a59057eef89049e664902e47988f7cddee8f6557238f2e69068ef768458e7368d88e4b12d18e3038118dd3a5198dc897948db73fb38d6df03a8d690a058d5b33738d58f75d8d321be88cc1b0478c946b008c69da498c651d4f8c4ec5b38c0f74dd8c099caf8ba4b1038afb527f8ac1b23f8a87c12f8a6e65d18a5b2e838a483bcf8a21010289ecf62489e5f6e689c46e0a89af03ca891f3eb6885aa33a87b37c8d87601ca98703ee608702c4ed86d10e4f86cf07598682be2886813a6b8650b200864338c885c35c2185ac37e0858bb0838583d6c185666a7a84bfdc8f8496f82b84152ed083790b06835d99308359362a82cc0b488255c4738240c297820ca94181f1483f81c4c4ac8139d13380a8bbe380a7c5bf7fa36b047f9e042e7f6c7ce77f1ec4a37f07ddff7e8926b27dd9d2ff7da412037da3dd057d6a7e497d052aaa7cb65e107c089cb17bdd85e17bbe005d7bb7c35b7b80d53e7b783dfb7b414fde7b2ceb0d7abe24027aaa4d497a9d7f097a5df9a97a0dd35279f9ac0079b1405a79995b2b7946bd8178b3a9f07891d449785cc8287827c1ac78115be87801107b77cb2eb477ca225e779d0e0d7796ac5c776bca0d7766f6cc773a196476e6cc2976acbc247699f89176954cba766163e47660399e7638e19775d04e94751dbbea74ef5f1774a649ab74a1666d7457c521743a65b573d3002773b715857398631a736d2b24735f54b4730802a17233de90720b026e71f0ccea71747c897160b9c870f1f3bf70ea5c1070a939e6707437c570608f30702afa096f501da56f464ade6f42c2516ef5a6a16ebfef216e17e6e06d5ce5a96cf959836cad2bdc6c6f0bd96c58f5406bb293e86b57c57b6b2a6b506af039f86ae9bdf96ac00b236a56189f6a2c3f376a0c276c69ecb9d769d76f0c69c6a6f8698cca54697ba2ee696a14006961ba716955dc37693fe464693c953e692d98d068e4d5ff68ced64f687286026853f2396800493067feaedd67f332a76794903267942c9f6768e3c3673799a76731f5a6672a66f766eff9c966d3d24066a09cfc66758c57664e9f71661f61436603906e65ebc76365e8732665cdced765ba64c765ac420365528362653bb36f65051cf164a6e7ed6492167463f9abd663ea4bbe63e5a35c63d34c386359bb1863563471633a49cf63094beb62fd282062f91bb46299379e6298cddd629245cd6235148361a574be619ac42161935d506148e1c6613007a060da9bcb60b86bac608cd6556049867b5ff8d5505fe0a2b85fdf16f65fb5e01a5f532b6d5f4d78e75f33ba825efa14dc5db43cb15d99328d5d88f76c5d56de4f5d52094f5d445ff75d2a9af75d04da975cc6cb2d5cc5c8ff5c7efc405c6eb31a5c355b735ba446235b884aab5b4812d95b088d795af448605aa70db4598dad175949df6e592eb1095913ad8e58f7c2ec58ba0bab58146cb7580f23af5801463057f20bfa57aeee2f579f0f625795790257915ff95714ca4056a09be5564ed059562bae3255dd5f9f5592509c555bf761553f55b2553e20d85493dd1f5486a38253ffeca053f0310c53c0ce5c5359440c52c82ebc52c2cd3f522bbba1519ce7cb518bafd0516e1b8150b562835053654b503e8213500e30bf4fcfe4034f65dbb24f505d234ef5c39b4e4a58064df753e84d8273d84d42ee784d00d5864cc349424c9619054c88cc1e4c6fc0364c39a5524bfecaaa4bfd73484bdd125a4bcae0fc4ba1c6664b78da724b5d2f5c4b56a4a34b546e024b1966f04b10102d4b0b7ef54abcffdf4a73478a4a11e09b49e81cd949cbc0f84996cc2f4960b5df495746cf4934c3b2491d19d24917c16f490e3c0c48f5805f48b3af8c48aa715c4888d7bb484276e44834a24b47d80f5347bcfb7447abfddf47a32ce54775404447476d944718ad4c46f9334146d49161467c9155466e4483465a59c545e0194f45cf514b45b5aed945b373b445afb0c145aee27c45a093ef44f82958449c85be4402fa6843ecbef04368fe134362b51142d1d2c742c5aeff42a6931f425581394229666f4206ad4a41f843e2417597fa40ffe62f40c8f81240001f953fe5a1dd3fbd527e3f5f3c813f1594083ed1eec93e9fbad23e8b3d783e28dea43e25581d3de7baa73d69a77e3d32b9613d21289d3d1946ea3d0d14863cf2ab1a3ce2ae003cd6f71e3cd626693c6d40793c5d345e3c4f632c3c1057313bf2d0343ba349b63b6c5b993b6b31533b577ad13b3a3fc43abb4da53a8905643a331595395d654d39339440393229813926773038cc4ffd38bf00873832cef237f74cd137eedd8337ea11c0376bd328375dc833372c4dc836f0ab91367e8898362eab8a35eb1fb835e6dd6535c4c60a354e2e3e3547ec973533b0ba3508673735007ce834ffc84534bd18ee348830b033fe6a1733c7886333bee4b733b5204833a592963345c9f233238e5a32d420ca329fc2e431ef11ae31c029f6319139b73173183d3168c1f530d9d75a30ad53c93062bd303047b7372f9df8d02f74620b2f53a7e92e3890852e25da892ddf84a72d63beee2d38a6b62cf677cf2cd901e02ccb1fd42ca45ce72be282ce2bde235a2bb15a072b84605c2b8190622b6957a22b6800402b33ea372b287ae02afc4a992af961862aa6aab72a9135ed2a60b3ff2a17c59229cbbe7e298dc2cf291c855328c9d04027b14d60279dab862785c2b1276cc126276b27b2275b48762741188e270db9dd26ed138a26ce347d26bdb4182654bdf92607e0cc25f65d1525d74dbe25a734f425666daf255348582540da21253b008e24ba9931248f5eb92439643c2420146523d4221a2369480b236624ab235706fd2354eee8232f42eb2320d6ef231cf39022db185f22c3d99822a6c2a42298c421228c82cb2261d6042232c44821e7c6b521d3711021d0f79821875aac217e7fcf216c90952112b92c20f90cff209035ad208027aa201f23c020153fef1faf8a7f1f3d09ad1ef6441a1ecbe1501e99b1221e6607ff1e23f4101d479bc41d2fe6521d0db6251cf9f6fc1c9d64041c7c15981c4e541e1c3fe8bf1bf28e791b3399341ada7370193d07391927af9b1901e35518b79b4e189b29de18643bc11848782217b927d11780e58c171920a816de3ac0166f2df2164e09e3161ca80c161890f015cf9e281518788c14f3d43414e2c0d614bce6171498309a1462bee4144338031412033b13fd1dbf136c41c81348486912ca96ac12c159db12beda451242bb581230448b12138de9120bcd3b11ed072a117557c5115c388f11542be211287706110d3ffd10d92e6010ba152e106cf9fa10355dee0febbd210f3457fb0edeef030ede5cbc0ed7c5030eceef180ec553370e9f69a30e86e8540df5d3040d6f48f30d6dfa330d3934510d2a268b0d2785f90cd2a1fa0cccc8290c9bb3dd0c418caa0c00c1290bbe77270b7ba4550b48b0520b283c230b092af20aec1d5a0aac97fa0aa7c7b50a6a323a0a1cf78e09b954030982528a097b61d7096a45ec096011e40942cd2a08deedee08aae3e5083acf9807fbbe2207f9f7fa07dae96a07c255130791fd720748931c073c5c1b07356a7a0711a4ff070fa5ba0692b980062e4eca0628f14705cb9faa055b0edd049bacd60484a78b04603f270442230e042560bd042368b603a102910395266b034cda3603339259031f393602cf2de6028e23e60274c02e026857a0022dc4ce0229139f01fcd0470113d54200b737340025cda0
  | 8 => 0xf766d289f361cf82f2a26d7be896d4b5e85fe698e77c9063d70b5091d2cad8bdca237151c8272433ba618532b675dd89b6365829b2bf2aa9a44ae482a226fdf1a0dd7b719847119a93eccb377bbe005d7827c1ac77cb2eb4766163e45d56de4f5359440c4d00d5864206ad4a395d654d37eedd83354e2e3e2354eee822c3d99814f3d43412c159db0e86e8540cd2a1fa031f3936
  | 9 => 0x2354eee8
  | _ => 0

def LT : Nat → Nat
  | 4 => 0x555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555
  | 5 => 0x6666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666666666666666666666666666656666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666665666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666566666666666666666665666666666666666666656666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666656666666666666666666666666666666665666666666666666666666656666666665666666666666666666666666666666566666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666
  | 6 => 0x77777777777777777777777777777777777777777777767776777777777677777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777677767777777777777777777777777677767777777777777777777777667777777777777777777777777777777777767676777777777777777777777777767777777777777777777777777777777776777767777777777777777777777777777777777776677777777777777777777677777777777777777777677777777777777677777777777777777777777777777777767777777777677777777777777767777777777777777777777777677777776776777677777777777777777777777777777777776777677777777777777777777777777777777777777777777777777777777777767777767767777777777777777777777777777777777776777777777777766777776776777777777777777777776777777777777777767777777777777777777777767777777677777777777767767777777767777777677777777767777777777777777777777777777677676767777777767777777777767777777777777667767767777767777777777777777777777767777777767777767777677777777777777776777777777777777777777767777677777777667777777777777777777677777777777777777777777777777777777777777777776776777777777777777777777777767777766777777777777777777767777767777777777777777777777777777777767777767777777777777777777677767777766767777777776776777777677777776777777777677777677777777777777777777777677777777777777777777777777777767777777777777777777777777777777767777776777777677777777777777777777777777777777777777777776777777777777777777777767777777777777777777776777777777777777777777777677777777777676777777777777777777777777777767777777777777777777777677677777777777777777677777777777776777777777677767777777777777777777776777767777777777777777777777677777777777777777777777777766677777777777777777777777776777777677777777777777777677777777777777777777777777677777777777777777777777677776777777777777777777776676777777777776776777777777777776777777777777777777777777767777777777777677777676777777767667777777777777777767777777777777777777776777777777777777777777777777776777667777777777777777777777777777776777677777777777777777777677767777767777777767777777777677777677777777777776777777777777776777777676777776777777777777776777777777777777777777776677777777777777767777677777777776777777777677777777777776777776777777677777777777777777777767777777777777677777777777777777677777777777777776777777777677677777777776777777777777777677777777777777777777777777777777777777776677777777777777777777777777777777767777777677777777677777777777777776777777777777777777777677777776777777777777777777777777777777777777777767777776776776777767777777777777777777677777777777776777777777777777777767777777777777777777777777777777777767777777777767777777777777777777777677767777777777776777777777777776777777776777776777777776777777777777776777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777766667777777777777777777777777777777776777777777777777777777777777776777767777777767777777777777777777777777777777777777777777776777777777677677777777777777777777777777777777777777777777777777777777776777777777677777777777777777777777777677777767777777776777777777777777777777777677777777777777777777777777777777777777777777777777677676777776777777777777777777777777677777777777777777767777777777767777777777777777777777777776777777777777777767777677777777677777777777676777677777667777777777777777777777777777767777777777777777777777777777777777777777777777777777777767777777767777777777777766677777777777777677777777777777777777777767777677777777777777767777777677777777777777777776777777777777777767777777767767777
  | 7 => 0x7888888888878888788878888878887788887787888888788888887788787867888888888878678888788878888688777888888787888788888887877888887887888888777788888887888888878688888887878888877778888888788788788888887888888878888886887887888788888886888888878788888888877887888868888788868888888788887677886877788888878778886887888888888888887877888888688878778778788887877888787888777888888888888886888888887888888888886888888888778788888788888868778788888778888878888888788888888777878887888888888778776877887687788878878888788878888888888887888888888888888887887888888788888878888888888878887888888788688788888878887887788788788886888687788788787888787888878867788788788868887878788688887888777878888888888887688878887888887888688888877788888878786887778877878878687878888778888878888878878788778787888787888878868878788878788888888778787888888888688788787888888888878687778888878788888877888687688886878888868888888888887888787788887888878877778888888878886887788887788788887888788787888888888788787888878888887778868887887787886788878888878878888887888888877888878678788778888887678888787788778887888887868887788888787887888887787888888888688787888887878888888888888888887787878887888788
  | 8 => 0x7777777777777777777777777777776777777
  | 9 => 0x6
  | _ => 0

def DT : Nat → Nat
  | 4 => 0x2646ad483389200000002736ad273b49200000002866ad5e52cce00000002946c55e3386d00000002a77895e3386d00000002a7781273386d00000002596c55e3387c00000002596e54933892000000029a789273386d000000026e6ad5c3386d00000002736e54b3c89200000002a89be0f49c6d00000002596ad4b3c8a70000000286731273389200000002a77092733892000000026e6ad583386d00000002866ad273c49200000002a8958ce2486d000000029c894ce2486d0000000294789273387300000002736ad4b35092000000025978527338b400000002597f5e049c6d00000002946ad5d3386d00000002597314a3389200000002a89ea492486d00000002596ad5e3886d00000002597f97a2486d00000002596ad5c40c6d00000002597fd302786d00000002646ad5b3386d00000002597fde25e86d00000002596ad5e52cd400000002596ad4a3c49200000002817fd302486d00000002996ad5e3386d000000026e6ad2740c6d00000002597fde24d06d000000029c6ad49338920000000269779273386d00000002736ad273c89e00000002736ad473389200000002796ad273ac9200000002796ad7a2486d00000002596ad5e52ce900000002596e5353c89200000002646ad5e52cce00000002a7880ce2486d00000002a89ea0549c9200000002596e54b3c89200000002597852733873000000029d9be3c3386d00000002736ad4b3c899000000026e6ad273fc6d000000029d9bdab594ce00000002597fd353c89200000002597f9273c09200000002597897c1b45500000002596ad353a49200000002597895e3388100000002597f14b3c892000000026e6ad27338b400000002596c54b3389900000002817fd273c89e00000002797f9272486d000000029c6ad702486d00000002797fde249c6d00000002796ad273c09200000002597fd2727873000000029da1e333389200000002598ad493389200000002597f5352486d00000002817fd272487300000002697fde24c06d000000029da1dab590ce00000002796ad4b3c8920000000259779303386d000000026e771273386d00000002596ad273c49e000000029c6ad4b3c8920000000286721273389200000002596ad353c89900000002596ad5d524ce00000002a89bde949cce00000002816ad273c49200000002866ad27338ac00000002596ad273c09900000002597fd272d84200000002786ad4b3389200000002597fde249c7a00000002597895e38c6d00000002a77fd273c89200000002596f54b3389200000002879e9ab6149200000002697fd352486d00000002596ad4b3c899000000029c7895e3386d000000027a85dab49c6d0000000287949273389200000002866ad4a3389200000002697f1272486d0000000259789cb578ce00000002946ad543386d0000000259781cb49cce00000002597355e3385900000002596ad543387c00000002697f9272486d00000002a77f5272486d00000002736ad493389200000002697fde249c6d000000028f6ad273c89200000002596ad273c4b5000000027a945ab2486d00000002596c55b3386d00000002697fde249c7300000002597897b5786d00000002646ad5e3786d00000002598ad4b3c89200000002597dd272786d000000026e6ad5e52cce00000002879ea0749c92000000026e7fde249c6d00000002736c54b3389200000002646ad5e52cd400000002867fd273c89200000002817dd272486d00000002947895e3786d00000002596c55e52cce00000002596e5273b49200000002597895e3787c00000002597fd3a2486d00000002796ad273ec6d00000002596e15e52cce00000002597fd273c8a800000002596ad5e52d0300000002597fd393c892000000029c6ad7b2486d0000000259765273786d00000002876ad9349cce00000002946ad5e3506d00000002646ad4a3389200000002596ad5e3507c0000000269789273786d00000002736ad353c892000000029da1dab6089200000002879e9ab49d0d00000002736ad273c09200000002597fde249ced00000002597f9302486d00000002597795e52cce00000002646ad5e3387c00000002596e54b3509200000002597fde24c06d000000029c8acce2486d000000028b7fd272486d00000002597895e3786d00000002866ad423389200000002596ad5c3506d00000002736ad4b3c89200000002597fde24c07300000002597315e52cce000000029d9bdab6346d00000002646e54b33892000000029c6ad513386d00000002947895e3387c00000002596e5273c89e00000002a89be3a3386d00000002597fde249cb4000000029c6ad5d3386d00000002597fd353c89e00000002866ad2739c9200000002816e5273c89200000002646ad5c3386d000000029d6ad942486d0000000294765273386d00000002817fd353c89200000002596ad4b4103300000002a78a8ce2486d00000002597895e51cce0000000269789273387c00000002598a9ff3c89200000002597fd352487300000002597dde25786d00000002866ad27338b500000002597fd273c89e000000026e6ad27338b100000002597f127248730000000259789303786d00000002596e54b3c89900000002817fd273c89200000002596ad7b5746d00000002816ad273a4920000000259789273388000000002a772d273389200000002596f94b3c89200000002947895e3386d00000002596ad273c8a20000000294781273386d00000002597895e3387c0000000259781273387c00000002598a9fd2486d00000002a89ea0e49c6d00000002597fde249c7300000002596ad4b3509900000002817f5272486d00000002598b0f22485a00000002596ad5e52cdc000000029c6ad3e338920000000269785273386d00000002596c55e3786d00000002a8865273389200000002797e1272486d00000002646ad4b3389900000002596ad27408f000000002596ad473389900000002596ad5452cf200000002597855c3386d00000002596c55e52cd400000002796ad762486d00000002597fde256c6d00000002816ad273c89900000002796ad274086d000000026e785273386d00000002597fd273c8b50000000294789303386d00000002596ad4b408f20000000259789303387c00000002697fd272786d00000002646c55e52cce00000002596ad483509200000002a77c5272486d0000000259789273787300000002596ad5d3786d00000002597fdd949cf2000000029d914ce2486d00000002596c54a3389200000002597fd483c892000000026f90dab49cce000000026f955ab49c6d00000002a7755273386d
  | 5 => 0xa05ab49cce2906d00000965e25ed272486d00000aa29d76d273386d00000965ff49cd92786d00000991ab49cde2486d00000965c26ad2d33892000009a5ff6ad302486d000009ea6f6ad762486d000009a5ab49cce2786d00000965ab501273389200000965ab52cf23209200000965ab525273389200000a05d96ad273386d00000a767a6ad702486d00000965b94a0ce2486d00000965f16ad272786d000009664b631273386d00000965d56ad27338b100000a1e596ad2739cac00000965b549cde2486d00000965ff49cf22789200000965ab4d4ce2b06d00000965dc560ce2c492000009661349cff2486d000009b9ab52d2733892000009cdab49ceb3389200000965ab5f95e3506d00000965ab5d9023386d00000965ff7893049c6d00000965ff49cf22783400000965ab49cfb3387700000965ab49cce2647a00000965c26e52733892000009cdab49cf22487700000991b149cce2486d000009660e7c5ab49c6d00000966488c5ab49c9200000965ab560ce2c49200000a05ab520ce2486d000009a5ff789271b41900000a05ff49cd92486d00000965ab5a9273386d00000965ab4d4d92486d00000965ab5e8ed3389200000965ab520ce2481000000965ab575243386d00000965ab508ce2906d00000965ab49cce2a07c000009ea596ad273b49200000965ab49cde2487700000965e2579273786d00000965d96ad273c8ce00000965de49cce1b41900000a05f16ad272486d00000a51ab5c1272486d000009e5ab49d042486d00000991ab52d273509200000a76598953e3389200000965f1755c26ad27000009be596ad5e3786d00000aa287755273386d00000991c26ad273389200000966255d8ce2486d00000a05ff49cf22483400000965ab568ce2c492000009cdab49cd42486d00000965ab49cfb338b100000965ab5c1272487c000009cdab52d273c89200000965c26d52733892000009662849cce2486d00000966206ad702486d00000965ab520f23389200000a51e2578ce2486d00000a86646ad4b3389200000965ab4c0eb3389200000a05ab49cd92786d00000965b149cce2487700000a76596ad705446d00000965ab560ce1b422000009b9ab49d133386d00000965ab49cde2c49200000aa259789303386d00000965e549cce2486d000009a5ab508ce2486d00000991ab49d032486d00000aa2597dd272486d00000965fd6ad272486d00000965e2578ce2487c00000965ab63cff2486d00000965f16ad422486d00000991ab52d2d3389200000a05ab545273386d00000965d26e54b338920000096625338921b45200000aa2598152733892000009ea59815ab49c9200000a9e2c52cce2486d00000965fe49ccb2486d00000965ab5ed5749c6d000009662c6ad4b35092000009cdab4b4ce2486d00000965c849cce2486d00000a51e249cde2486d00000965b152d273389200000a4a6f6ad27338b6000009cdb952cce2486d00000965ab560ce2786d00000965ab49cd423c6d00000965ab5794b3506d00000965ab49cf23649e00000965b149cce2c49200000965ab4c0d42486d00000965b15f15e3386d00000a1e736ad4b3389200000a9e2c49cce2486d00000965ab490de2486d00000965e249cde2487c00000965ff789272487300000965dc49cce2b06d00000a51af49cce2486d00000965ab5e4ce2486d00000965ab52cce29c6d000009cdb949cce2486d00000a05d56ad273386d00000965ab579273506d00000965ff49c921cc34000009662c7fcce2488100000965ab4d4ce2a06d00000965ab49ced24825000009cdab49ccf2486d00000965ff6ad272487a00000965ab4f92735092000009be596ad274386d000009a5ab49cce2246d00000965af49cce2487c00000965ab49cdc2d89200000965ab545423386d000009662a6a0ce2486d00000965e26ad27370b600000965ab49cce29c6d00000965ab49cce2b06d00000965b852d273389200000a51a249cce2486d00000965ab49cf032c9200000965ab49ce72906d00000965dc49cd92486d00000a05ab560ce2486d00000a51ab49ceb3389200000a05ab49cf236492000009662c7fd4b3c89200000965ab5c1352486d00000965ab49cff3ac9200000a767a6ad4b3c89200000ad6a8735273389200000965ab578e32486d00000965ab49cde2786d00000965ab4d1043c86d00000965c849cce2487300000965df49cce2486d00000965ab49cd92486d00000965ab52d2740c9200000965ab6093e49c9200000a19ab49cce2486d00000966327a1ab3386d00000965ab49d032c492000009cdb549cce2486d00000965d56ad423386d00000966206aceb3389200000a05ab49cfb3386d00000aa259880ce2486d00000991ab49cce2486a00000965ab4f92d3389200000965b94c0ce2486d00000a19ee6ad273389200000aa287709273389200000a71ab578ce2486d00000965ab579273a46d000009cdfc49cce2486d000009a5ab49ce72486d000009cdab52cce24877000009662a709ab3389200000a51ab49cd42486d00000965ab5794b3381500000aa287831273389200000965b149cce2786d00000a76598ccce2486d000009e5ab49ccb2486d000009a5ab49cce2646d00000966255c13e49c9200000aa29d72d273389200000a05ab49cde2486d00000965ab49cce2b07300000965f16ad272646d00000965ab49d0d3386d000009922c6ad4b3389200000966398c5ab49cce000009cdab49cce2487700000965ab49cd42487c00000965b94f9273389200000991de49cce2486d00000a05a849cce2486d000009ea6f6ad273fc6d00000991ab49cce23c6d00000991ab5794b3386d00000965b149cce2486e00000965e2735303386d00000a1e6f6ad27338b100000966206acd42486d00000991ab4c0ce2486d00000965b952cf2248250000096649839ab3386d00000965c26ad273389e00000a71ab49cde2486d00000965ab508fb3386d00000965ab49cd924873000009ea597fd272786d00000965b54c0ce2486d00000991ab579273386d00000a76596ad543386d00000965e26d5303386d00000a05b149cce2486d00000965ab49ceb2483000000965cb6ad5e3389200000965ab6150d3386d00000a51ab4b4ce2486d00000965ab49cf22485a00000991ab4f9273389200000965ab4b4ff2486d000009661349cce2486d000009ea6f6ad27338b400000965ab5452739c6d000009cdab49cce2c49200000965ab508de2486d00000965c8508e72486d00000965a849cf23389200000965f849cce2b06d00000965ab4b4ce2487c00000965f56ad272486d00000965b54f9273389200000965c85d8ce2486d00000a76596ad643386d00000965ab4d4eb3389200000a1e7a6ad273909200000a05c26ad273389200000a51b949cce2486d00000a1e6f6ad6c49cce00000a724e6acce2486d000009be596ad27440ce00000966126ad273386d00000965ab4c0ce2487700000965ab49cce2a06d00000a067a7fd272486d00000965dc5c1272486d00000965b949cff2486d00000965ab528ce2486d00000a76596ad833389200000965e8709ab49cce00000965ab49d042487a00000965cc49ce92486d00000965f849cd92486d00000a51e249cce2d86d00000965b949cce2487c00000a51ab578ce2906d00000965d56ad2739c6d00000965cb6a1273389200000965b1508ce2486d00000002596ad5e52cd400000965ab5c1272486d000009cdab490ce2486d00000966206e4ce2486d00000965ab508e72b06d00000a1e597312733892000009662949cce2486d00000965e249cce2d87c00000965b54c0ce2487300000965de52d273389200000965ab4e4ce2486d00000965ab578ce2907c00000965f776dab49c6d00000965ab5d8ce2b06d00000965ab49cf22484300000965de49cce2c49200000965ab52d273388f00000965ab4d4d42486d00000991ab49cff2486d00000965ab49cce2c48f00000965ab560e72486d00000965ab520ce2d46d00000965ac4d4ce2486d00000965fb49cce2486d00000965ab56cce1b41000000965b952cf22486d00000965ab4c0ce2c49200000965c26ad423389200000a51b549cce2486d00000965ab560ce2646d00000991ab49cce2487c00000965ff49cce2486a00000a51ab49cde2906d00000965cc510ce2486d00000965b549cff2486d000009a5ff6ad272486d00000966207c5d56ac6d000009a5ff789ab49c6d00000991cc49cce2486d00000965ab5d8d92486d00000a19ab49cdc2486d00000a767a6ad7c2486d00000965ff49cf22485600000992206acce2486d00000965b949cf22486d00000965ab63cce2486d00000965b549cce2487c00000965ab49cde2907c00000965ab5fcce2486d000009cdab49cce2786d00000965ab49cfb39c6d00000965fa49cce2486d00000965ab52cd42482500000abe69789273386d0000096648881ab2486d00000966206d4ce2486d000009be596ad583fc6d000009663f6acce2486d00000aa2878b14b3389200000a7659894ce2486d00000a51ab49cce2487700000a51e2579273386d00000965ab5c1272487300000965ab4d1043386d00000965e249cde2486d000009cdab49cf22646d000009ea596ad273c89e00000965ff789303386d00000965ab49cff2487700000965ff4d4f22486d000009cdab49cc52486d00000a526f6ad5e3386d000009662549cce2b06d00000965ab49cce2786a00000a767a6ad8a2486d000009cdab52cce2481000000965e2579273387c00000aa29d6ad702486d00000965ab49cde2646d00000965eb49cce2b06d00000a1e6f721273389200000a51db6ad273386d000009be596ad5e3387c00000a767a6ad273b89200000965ab49cf52486d00000965ab5794b3381100000966206acce2487700000965dc49cff2c49200000965b94d4ce2486d00000965ab49ccb2646d00000965dc49ceb3389200000965e2578de3386d000009663c5952733892000009662549cd92486d000009a5ff6ad272487300000965ab5ed5e2486d000009a5ab49cc82486d00000965ab49d103ecce00000a76596ad8d2486d00000ac2876ad27338b600000a51ab49cce2c49200000965ab5c15449c6d00000965fc49cf22486d00000965df56cce2486d00000a067a6ad273c89200000965e249cce1b45500000965b149ce72486d00000965ab4c0ce2786d00000965ab49cff2c49200000002646ad5e52cce000009a5ab49cce2906d000009cdab52cf233892000009662076dab3386d00000965ab49ceb3389200000a05ab49cce2486a00000965f85c1272486d00000965ab5e8ce2486d00000965b149cce2646d00000a42736ad273c89200000966506ad273389200000965f16ad272906d00000965e26ad7a3386d0000096604721272486d00000965cc52d273389200000991ab4d4ce2486d00000a1e6f6ad27338ac00000965ab4a0ce2646d00000966206acce2c49200000aa2598e8ce2486d00000965ab4f9273389e000009e5ab4c0ce2486d00000965dc49cd42486d00000965c26ad2739c92000009cdab508ce2486d000009be598f1273386d00000965ab49cce2488100000965b54d4ce2486d000009b9ff6ad272486d00000965ab60d7049c9200000965ff789301b41900000a51ab490ce2486d00000965c26ad273389900000a51e249cce2487c00000965b149cce2306d00000965e2741273387300000965ab614eb3389200000a05ab4c0ce2486d000009660e815ab49cce00000965ff5f1272786d000009660f771272486d000009ea6f771273386d00000965ab5794b3381000000965ab4d0ce2486d00000a76596ad704f89200000965e26ad343386d000009ea596ad852486d00000965e26955e3386d00000965ab49cd42486d00000965ab49cff1b42200000991ab52cce24825000009be597a5ab49cce00000965ab5a0ce2486d00000965ab5d9702486d00000aa20d49cce2486d00000965ab49cf22782500000965ab51cce24825000009a5f16ad272486d00000965ab4e4dc2486d000009663c545273386d00000965ab494ce2486d000009be596ad6549cce000009660f6ad272486d00000965b949cce2647700000966207c5c26ac9200000a05ab4f9273389200000965ab4d4ce24877000009ea6f7ed272486d00000aa287880ce2486d000009665249cce2486d00000965dc4b4ce2486d00000aa2597892733873000009663a83dab2486d00000965ab609272486d00000a19ab49cce2d89200000a19e26ad27338b600000a51ab49cce2786d00000a05ff5f1272486d00000965ab550ce1b445000009660749d0d3386d00000965ab49cff2786d00000965ab5955149cce00000a9dab49cce2a06d00000a05ab49cf22482500000002596e54b3c89200000965ab5c0921b45200000965ab4b4ce2486d00000a19cd6ad273389200000965ab490f22486d00000965ab49cce2787c00000a722c7fcce2486d00000965b952cce2486d00000a51ab578de2486d00000965ab4d4ce2c49200000965ab4d0ce2487300000965ab5cd272486d00000966206acce2786d000009a5ab545273386d00000965b16ad5e52cce00000966255c1272486d00000965ab49cd42487300000965ab49ce92486d00000965ab5093e3389200000965f16ad5149c6d00000965e9755ab49cce000009663c560ce2486d00000965f849ceb3389200000965f772dab49c9200000965ab560ce2906d00000965ab578de2487c00000965b949cce2486d00000965be5f1272486d00000965e251d273389200000a05ab49cff2486d00000965ab49cce2e86d000009ea597e1272486d00000965ff789271b43000000965ab49ce32487c000009cdab52cce2646d0000096639881ab3386d00000991dc49cce2486d00000965ff49cf22483900000a05ab49cce2487c000009cdab49ce72486d00000002597fd353c892000009a5d56ad273386d00000965cf49cce2486d0000096633609272486d000009a62c7fd272486d00000965ab4c0ce2246d00000a06206acce2486d000009cdab49cce2646d00000965ff4d4ce2486d00000965f1755ab49c6d000009ea596ad273eceb00000965ab595583389200000965ab510ce2486d0000096620755c26acce000009ea596ad8349c9200000aa29d7c5272486d00000991ab49cce2486d00000965ab4b4ce2487300000965f849cd42486d00000a1e596ad8533892000009ea6f6ad273ac9200000965ab5d8eb33892000009ea6f6ad7a2486d000009a5ab560ce2486d00000a76596c54b3389200000965fc52cce2486d00000966486ad272486d00000965b549cce2486d000009cdab484ce2486d00000a51ab508ce2486d000009e5ab49cf22486d00000965ff6ad7c29c6d000009ea596ad762486d00000965c849cce2b06d00000966116ad272486d00000965f16ad582486d00000965ab49cde2906d000009be59771583386d00000aa287721273389200000965ab508ff2486d000009ea6f859ab49c6d000009660949cce2486d00000a42736ad4b33892000009ea6f6ad273c8b600000965b949cce2487300000965dc49cce2487700000965ab508ce2487c00000966176ad273386d00000965fc49cce2486d00000a76596ad5e3506d00000965ab5ed4749c92000009664b49cce2486d000009ea596ad274086d00000a05ff49cce2786d00000965ab4d4ce2786d00000a51cb6ad273389200000a1e598cd2733892000009be596ad583386d00000a767a6ad5e4106d000009a5ab49cfb3386d00000965c849cd92486d00000965f7789272486d00000965ab4c0e72486d00000965f16ad273ec6d00000965ab6096449c6d00000965ab49cce2487700000965f749c921b43400000965ab5d8d42486d00000a71ab49cf22486d00000965b149cce2906d00000965ab4c0ce2646d00000965f84b4ce2486d00000965e149cce23c6d00000aa2876ad27338ac00000965e2735273387300000991ab49cce24873000009662072dab33892000009a5ab49cde2486d00000a767a6ad922486d000009662549ceb3389200000965ab52cce24833000009cdab49cee33892000009be596ad5a3386d00000965ab4d4e32486d00000965ff4d4921b41900000965ab4f92739c9200000965ab561513386d00000965dc49cce2c49200000965cd6ad3933892000009a5ab49ccb2486d00000965db6ad273386d00000965ab658ce2486d00000965b549cce2487300000a05ab4d4ce2486d00000965ab52cf22483000000965ab4f9273389900000965ff49cf23389e00000965e26d5273387300000965c26ad27338a400000965ab55d4749cce00000965ab49cd92b06d00000965b949cf22d89200000aa29d755273386d000009662e6c54b3389200000965ab52cf22642500000965ab49cce2c49200000965d9709ab49cce00000a51ab49cce2907c00000965ab52cf224852000009a5b149cce2486d00000a1e596ad6449cce00000965fe49cce2486d000009e5be49cce2486d00000965d56ad583386d00000965f16c5272486d00000965fc49c921b41900000966497c5ab2486d000009662549cd42486d00000965ab579043786d00000965ab4c0ce2487a00000991f849cce2486d00000a51e249cce2486d00000965ff689273c89200000a05ff49cf23389200000965ab4d4f23389200000965dc49cce1b42200000965f85d8eb3389200000965b95d8ce2486d000009660749ceb3389200000a1e596ad4239c9200000965ab545273786d00000a51ab49ce72486d00000965eb5a0ce2486d000009a5c26ad273389200000aa29d7895e3386d000009ea597e1762486d00000965ff6ad273b49200000965ab490ce2486d000009ea5981d272486d00000965e249cce2487c00000a51ab49cce2646d00000965ab49cce2d46a00000965f1709ab49c9200000966246acce2486d000009ea6f6ad5b3386d00000965ab49cff2646d00000a767a6ad273ec6d00000a76646ad5e3386d000009e1ab49cce2486d00000965ab49ce72487c000009662a6acce2486d00000965ab584ce2486d00000a71ab450ce2486d00000965ab49cef2486d00000965ab49cce2647c00000965ab49cf03389200000966206ace72486d00000965c849cce2483d00000965ab49cce2ec9200000965dc49cce2786d00000966254b4ce2486d00000965ab560fb3386d00000aa2877b9273389200000965b1545273386d00000991ab5d8ce2486d00000965d56ad273786d00000966206acce2646d00000aa259811272486d000009662b505273389200000a05ab49cf23389e00000965f849cce2487700000a05ab49cce2486200000965c85c1272486d00000965ff6ad2723c6d00000965b55d8ce2486d00000965ff6ad302486d000009664b60d273389200000965ff789ab4c06d00000965ab49cce2786d00000965ab49d103fc9200000965ab52cf22646d00000965b14b4d42486d00000a51ab5ed272486d00000965ab560de2486d00000966516acce2486d00000965c26ad5149cce00000965e2578de1b445000009e5ab52cce2486d000009be596ad2740c6d00000965bd49cce2486d00000965fc5d8ce2486d00000a967a6ad274106d000009cdab49cce2906d000009664b5d8ce2486d00000965d56c5273386d00000965ab49cce2b03d000009e5ab49cbd2486d00000965ab49cf22646d00000a05dc49cce2486d00000a76596ad702486d00000965ff7892733873000009660e6ad273386d00000965ab578de2486d00000966396ad273386d000009ce2b49cce2486d00000965e26ad5e3786d00000aa29d938ce2486d00000a1e597ad273389200000965f849cce2c49200000a767a939ab2486d000009e5ab49cce2486d00000965ab5c1272b06d000009e5e26ad273386d00000965ab5d8ce2487700000965ab49ce32486d00000965fc49d023386d00000a51ab474ce2486d00000965ab52cf22482b00000965a8578ce2486d00000965ff789271b41900000965ab49cfb3786d00000ad6a88b0ce2486d00000965b1560ce2486d00000a05ab49cce2486d000009922549cce2486d00000a9dcd49cce2486d00000965ab49cfb32c6d00000965e06a1273386d00000965d5709ab49cce00000a71ab52cce2486d00000965e86ad273386d00000aa29d709273389200000965ab474ce2487c00000a1e6f6ad273a49200000a51ab55d273386d0000096648895272486d00000992596ad5e52cce00000965ff6ad302487300000965ab4d4e72486d00000991b149cd42486d00000a19ab4e4ce2486d00000965ab49cce2787300000a71ab49cce2486d00000965ab52d2737092000009b9b849cce2486d00000965c26ad583389200000965ab4d4ce2646d000009cdf16ad272486d00000965dc508ce2486d00000965b149cfb3386d00000a1e5981d273389200000965ab5d8ce2c49200000965e2578ce1b447000009ea6f6ad7c5786d00000965ab4c0ce2906d00000965e2578ce1b45200000965ff789273c8b600000965ab5794b35092000009a5ab49ced338920000096632709ab3389200000965ab49cce2486b000009662549cce2487700000965ab508ce2486d00000aa27a7bd272486d00000a1e6f6ad443389200000a1e6f789cd49cce00000965b149cde2486d00000965ff789271cc1900000965c26ad273ecce00000965cd6e54b3389200000965c849ceb3389200000965ab578d41b44500000a1e59811ab49c9200000965ab4f927338a400000a05ab49cce2487300000a51ab578ce2487c00000965be49cce2646d00000991b14b4ce2486d00000965cb6ad273389200000965f849cce2786d000009ea6f7fde249c6d00000965ab49d0e2486d00000965ff6ad272d092000009a5ab49cce23c6d00000965ab64d273386d000009cdab545273386d000009a5ab4c0ce2486d00000965c26ad2737892000009a5e26ad303386d00000a767a8acce2486d00000aa29d904ce2486d00000965ab569032486d00000965f16ad302486d000009662549cce2c49200000965c26a12733892000009ea6f6ad2744c6d000009660e7e1273386d00000a51ab49cde2487c00000965ab49ceb338ac000009be59779273386d00000965c849cd42486d00000965eb49cce2c49200000966057c5ab49c9200000a1e6f6ad583386d000009a5ab4f9273389200000965b152d273509200000965ab508ce2487300000a05f849cce2486d00000965f16ad3e49c920000096633508ce2486d00000965c26c52733892000009cdd56ad273386d00000a51ab49cce2906d00000965ab49cdc2786d00000965ab5d8ce2786d00000965ab49cff2906d00000965ab49ceb3649200000965ab49cce29c8100000965be49cce2487a00000965ab65527338920000096625490ce2486d00000965ab49cce2907c000009b9ab49cce2d86d00000965ab49cce2446d000009661363cce2486d00000a1e6f6ad5a3386d00000965ab498ce2486d00000a9dff49cce2486d000009cdab560ce2486d00000965ab570ce23c6d00000965dc49ce72486d00000965ab545303386d00000002596ad4b3c89900000965e27355e52cce00000966206acce2906d00000965ab49cd42506d00000965ab49cd42b06d000009a5ab4c0ce2487300000991ab5794b3389200000965ab5a0ce2b06d00000965dc49cce2646d00000965ab579473389200000965ab52cce2646d00000965c84b4ce2486d00000965b152d2d3389200000a05ab5d8ce2486d00000aa26f74d273386d00000965ab49ce72486d00000965f8508ce2486d00000a76596ad822486d00000965ab49d0d3acce00000965ab5453e49cce00000991ab578ce1b44500000965ab49cce2646d000009a5ab49cff2486d000009cdab49cfb3386d00000a51f16ad272486d000009ea596ad274346d00000965e149cce2486d00000965d56ad303386d00000965ab591423386d00000965ab5792d3506d000009be59771273fc6d000009662549cce2786d000009a5ab49cce2586d000009662c7fd302486d000009a5ab49cce2487c00000a767a6ad513386d000009ea6f77d273386d00000a1e59721273389200000966546ad273386d00000965f16ad272487c00000aa29d7dd272486d00000965ab49cfb3b4ce000009b9ab49cce23c6d000009662b49cf22486d00000965ab49cce2d842000009b9ab49cce2086d000009a6206acce2486d00000965ab4b4ce2b06d00000a766f6ad4f3386d000009662c52ce32486d000009cdab49cde2486d00000965ab614e72486d00000966207c5ab2486d00000a7659895702486d000009be596ad273fc6d00000aa2877fd273c8920000096639895273386d00000965d56ad3e49cce000009cdab49ccb2486d000009a5ab49cce2d092000009b9ab579273386d00000965ab49ce92b06d00000965ab49d103389200000a1e6f6ad2744cce00000a51ab579043386d00000991c849cce2486d000009662c49ce32486d00000a9dab49ce32486d00000991b152d273389200000965ab4b4d92486d000009ea5984d272486d00000965b949cce29c6d00000965b949cce2b06d00000a767a8b1ff2486d00000a062549cce2486d00000965ab5ed272486d00000965ab4d4ce2487100000965de568ce2486d00000a51ab545273386d00000965ab49ce72487300000aa2597d5272486d00000965f76ad5e2486d00000a1e596ad27338ac00000965ab5613e3389200000965ab579043387c00000965ab545273fc6d000009cdb149cce2486d00000965ab49cce2487a00000965ab4d4ce2906d00000965ff789271b41a00000965ab4c0fb3386d00000965e26ad273387a00000965ab49cce26473000009be596ad27338b400000aa28778927338b600000965ff6ad273c89e00000965ab525243389200000991ab579273506d00000965ab545273387c000009cdab4a0ce2486d00000965b949cd92486d00000965ab49cee33892000009b9ab49d043c86d00000965ab510ce2b06d00000965ab5c1273ac9200000966206ad513386d00000aa287735273389200000991ab49cce2506d00000991ab49cce2b06d00000965b149cce2486a00000965ab4c0de2486d00000965ab4f9273ecce00000a7659921ab2486d000009cdc26ad273389200000a1e6f6ad2740c6d00000a51d56ad273386d00000aa29d8dcce2486d00000965c849cce2487700000965ff7897c5786d00000965ab4c0cb2486d00000965d56ad273fc6d00000a9dab49cf23389200000965ff49c921b44200000965ab55d273386d00000a86646ad5e3386d00000965b549cce2b06d00000965dc560ff2486d00000965b949cf2248340000096625508ce2486d00000965b849cce2d86d00000965ff4d4d92486d00000965fb5e8ce2486d00000965d56ad273387c00000965f849ce72486d00000a05ff6ad273c892000009662c6c54b33892000009a5ab4d4ce2486d00000966436ad273389200000991ab49cd92486d000009ea597ed272486d00000965ab49cce2406d00000a765992cce2486d00000965ab4f9273789200000a51ab560ce2486d00000965f849cce2646d00000965f16ad352486d00000002697fde249c6d000009cdb949cce248770000096620755ab3386d00000991ab5792d3386d00000965ab5794b3382200000a51e2578ce1b44500000965ab49cce2d46d00000965b15794b3386d00000965ab560ff2486d00000965ab49cf22d89900000aa2697fd272486d00000aa29d880ce2486d00000965b14c0ce2486d00000a1e596ad27434ce00000965ab49cce2488000000965b549cd92486d00000965e249cde1b41900000965ff4d4f22483400000aa29d6ad7b2486d00000966556ad272486d000009ea596ad8f2486d00000965ab560ce2487c00000a51ab578ce2486d00000965ab555273386d00000a51e26ad5e3386d00000965ab49cce2b07700000965e2578ce1f04500000965c849cce2c49200000965b1579273386d00000965ff789271b42200000965eb49d0e2486d0000096649815ab3389200000a51ab49cfb3386d00000965ab4d4d92786d00000965b14f9273389200000966047a1ab49c6d00000965ab578ce2487c00000a3dab49cce2486d00000965ab49cff3ec6d00000965c26ad303389200000965e26ad5e3387c00000965ab5d8e72486d00000965ff789271b41c00000a1e6f6ad423389200000965ab5794b49cd400000965ab49cd92487700000965ab5d8ce2646d00000965ab49cfb3387c000009cdab5052733892000009e5ab5f15e2486d00000965ff49cf22483d00000965ab545353386d00000a51ab49cde2486d00000966206acfb3386d00000965ab49cce2486c00000965b8579273386d00000965ab5c12d2486d00000965de49d032486d00000965ab49cce2c4ac00000aa29d6ad573386d00000a51a849cce2486d00000965ab49d0323c6d00000965dc49cce2906d00000965ab49cde2487c00000965ff6ad272487300000a05ab4d4d92486d00000965ff789ab49c7300000965ff49c921b44000000965c849cef2486d000009662b52cce2486d00000965a849cce2487c00000966206acde2486d00000a19ab52d273389200000965ab5792740c6d00000965d949cce1b44500000965b95c1272486d000009663c49cce2486d00000965ab49cd92c49200000965e9771273389200000965ab49cce2906d00000a51b149cce2486d000009ea596ad273ac9200000965d56ad353386d000009ea596ad7a2486d00000966206a0ce2486d00000a9de249cce2486d00000965b149cff2486d00000965cd49cce2a06d000009662549ce72486d000009662b49cce2486d00000965ab49d043c89e00000965d96ad273386d00000966255453e49cce0000096631881ab3389200000965b149cce2487c000009662549cce2646d00000a1e6f779273386d00000965e96ad273389200000965c849cce2786d00000965ab578de1b41000000965ab4d4f236492000009a5dc49cce2486d00000966206c4ce2486d00000a51c26ad273389200000965ab49cfb1b430000009663a7a5ab3389200000965ab595273389200000991ab5c1272486d00000a9e3749cce2486d000009a5e249cce1b44500000965f1771272486d00000965ab5d8ee3389200000aa2876ad273bc9200000966236acce2486d00000965c26ad273fc92000009ea036ad272486d00000965ab49ceb3509200000965e249cce1b45000000965ab520ce2486d00000a1e596e5273c89200000a19ff49cce2486d00000965e2578ce1b44b00000965b55c1272486d000009a5ab49cce2486d00000965ab49cc824873000009a5e26ad273386d000009a5ab49cd22486d00000a05ab49d043c89200000965f16ad272486d00000965ab49d023b8ce00000965ab4d4fb3386d000009be59771273386d0000096620709ab3389200000aa25983d272486d00000a767a6ad4133892000009cdab4c0ce2486d00000a05c849cce2486d00000991ab5794b49cce00000965ab49cce2907300000a1e6f6ad2739c9200000965ff49cf22483400000966255ed272486d000009660749ce72486d000009b9ab49d043386d000009664b5c1272486d00000965e8721273386d00000a76598e5ab3386d00000965ab5794b3501000000965ab4d0d42486d00000965a949cce2486d000009a5ff6d5272486d00000965ab49ce92483400000965ab4d4de2486d00000965ab5c1272487700000a71ff6ad7c2486d00000965ab4b4eb33892000009cdab4f9273389200000965ab49cd92786d00000965dc545273386d00000a19ab49cce2786d000009be598e9ab3386d00000965a84d4ce2486d000009cdab52cf22482500000002596c55e52cce00000965ab579273386a00000a05ab49cce2b06d00000965ab5794b3388900000965ab545273386d00000965ab570ce2486d00000965b949ceb33892000009a5ab49cce2487300000965c8508ce2486d00000965cd6ad4b33899000009a5e26ad2733873000009662b551273386d00000965b14d4ce2486d00000965f849cce2906d000009662555d273386d00000a1e6f6ad273fc6d000009ea597e1273ac9200000965f16ad272487300000965b949cf22487700000a1dab605273389200000965dc755273386d00000965ab5c1272c49200000a71ab49cce29c6d00000a05ab49cd92486d00000966426ad273386d00000965de579273386d00000965ab4b4d42486d00000965ab49ccd2486d00000a51ab51d273389200000965b949cce2488100000965ab575273386d00000965ab49cf63389200000aa2877d5272486d00000965c26ad353389200000965d56ad273386d00000965ab514ce2486d000009662a7d5ab2486d00000991ab49ceb3389200000965dc560ce2486d00000aa2597c5d549c6d00000965ff49cce2a06d00000965ab4f93033892000009ea597fd352486d000009cdab49cff2486d00000965b152cce2482500000965ab508ce2b06d00000aa2876ad423389200000965b949cd42486d00000965ff6ad5b2486d000009663a755ab3386d000009b9ab49cce2486d00000965b952d273c892000009cdab49cce2487c000009b9e26ad273386d00000965b549ceb3389200000965ab5d8ce2906d000009ea596ad763ac92000009a5f849cce2486d00000a1e596ad683389200000965ab5c1242486d00000aa259921272486d00000965ab560ce2486d00000965f87c5272486d00000a19ab49cf233892000009ce206acce2486d00000965ab545273387300000965e2578ce1b44500000965ff4e4ce2486d00000965dc49cfb3386d00000965ab508d92486d00000966326acce2486d00000965ab49d0e2b06d00000991ab5794b33810000009ea597f1272486d00000aa29d6ad513386d00000a767a6ad3e33892000009cdab52cf22486d00000991ab49cd42486d000009ea5992d272486d00000a6e94789273386d00000965cc49cce2486a00000a1e596ad8249c9200000965e06ad273386d00000965ab568ce2486d00000a4a6f6ad274106d00000965ab49cfb3386d00000965ab631273386d000009661a49cce2486d00000965dc49cde2486d00000965b94b4ce2486d00000ade9d8b0ce2486d00000a51ab4c0ce2486d00000965b549cd42486d00000965ff4d5273c892000009cdab49cf22486d00000965c66ad273389200000965d56ad273387300000965ab49cff23c6d000009662c7fd2724873000009a5ab5d8ce2486d00000965ab4c0ff2486d00000a51f76ad272486d00000965ab625272486d00000965ab52ccb2486d00000965ab5c1272786d00000965f16ad762486d00000a1e596e54b3389200000965ff789272306d00000965ab4c0ce2586d00000a05f56ad272486d00000965ab4e4ce2786d000009662549cce2906d00000965ab4c0ce2487c000009b9ab49cce2487300000965f36ad272486d00000965ab49cde2486d00000965ab49ce32a06d00000965f8545273386d00000965c849ce72486d00000965ab49ce22486d00000a1e596ad273a49200000aa25976d273386d00000a46817fd272486d00000a51ab4f9273389200000965ab560ce2487300000965ab49ccb2486d000009662c6acce2488100000965c849cce2646d00000965e26ad2732c6d00000965a849cce2486d00000965ff49cf22483600000965ab4f9273fc9200000966207ddab2486d00000965b949ccf2486d00000991ab4b4ce2486d00000965ab49cd42487700000965c56ad273389200000a51e249cce1b41900000965cc579273386d00000965ab49cce2d08f00000966316ad273389200000965ab510e92486d00000965b54b4ce2486d00000a05ab5c1272486d00000991ab49ce92486d00000965ab4e8ce2486d000009cdb949cce2646d000009cdab4d4ce2486d00000965b149cce2486d00000966206ad3e3389200000965e249cce1f01900000965f8755273386d000009663c635272486d00000966496acce2486d00000965ab49cfb3387300000a76596ad514f8ce00000991b949cce2486d00000965ab49ce72b06d00000965dc709273389200000a767a7e1272486d00000aa2876ad2739c9200000a1e596ad4433892000009a62549cce2486d00000965ab5d9513386d00000965ab49cf12486a00000965ab49cf2338a8000009ea596ad353c89200000966257c5272486d00000965ab52d2735092000009a5ab56cce2486d00000965f8560ce2486d00000965ab49cd42c49200000965ab5f15e3506d00000965ab5a0ce2c49200000965c26ad273389200000965ab49cde2487300000aa2878dd273389200000a1e5972127338ac00000965ab4b4ce2487700000aa2597c5c249c9200000965ab508ce2483d00000a65ab49cce2486d00000a51ab49cff2486d00000965ab6356549c9200000965b849cce2486d00000965ab52cf22649200000991ab510ce2486d00000965b952cce2487700000965ab49cd92646d000009ea6f6ad27338b100000aa2598a8ce2486d00000965ab5f0ce29c6d00000a51ab49cce2487c00000965ab4e4f23389200000965ab5c1422486d00000965e249cce2f07c00000965d56ad763386d00000965ab5794b350ce000009a6597fde249c6d00000965ab49cff2487c00000a767a6ad762486d000009be596ad5b3386d000009be597ad273386d00000965f849cfb3386d00000965ab544ce1b45200000a76596ad7b2486d00000a52206acce2486d00000991b549cce2486d00000965b949cce2487700000965ab49cce2bc6d00000965ab49d032486d00000966206acff2486d00000965b149cce24873000009be386ad273386d00000965ab49cf22643400000965ab49ceb3389e00000002597fde24c06d0000096625545273386d00000aa2597fd302486d00000966206acce2487c00000965ab49d0d39c6d00000a767a6ad274086d00000965ab4b4ce2c49200000965ab52cf22482800000965ab49cff2d092000009be596ad8d49c6d00000965f849cde2486d00000965ab49d041b433000009cdab49cce2647700000965ab52d273a49200000965ab6318349cce00000a51ab578ce1b41000000965ab4f9353389200000a1e6f771273386d00000991ab49cce2487700000965c849cce2d46d00000002597895e3786d00000aa259839273386d00000a46816ad273c89200000aa2598e5273386d00000965b949cce2c492000009ea6f6ad273ec6d00000965b849cce24873000009ea59839ab49c6d00000965ab5d8fb3386d00000965ab505273389200000965be4c0ce2486d00000965ab578ce1f01000000965ff5f1352486d00000965ab631763386d00000a76596ad573386d00000965b549cce248770000096625755273386d00000a05ab49ceb3389200000965ab6355149c6d00000965ab49cd42786d00000002736ad4b3c89200000965ab4d4f22482500000965ac49cce2786d00000966497e0ce2486d00000aa259755c249cce000009cddc49cce2486d00000aa2597a1273386d000009cdab52cce2486d00000965ab5d8de2486d00000a1e6f7b9ab49cce00000991ab52d27338920000096625560ce2486d00000965aa49cce2486d00000965ab5d8cb2486d00000965ab49cd42486e00000965ab51d273389200000991ab49cce2c49200000aa2876ad27338b500000991ab5f15e3386d00000965b9490ce2486d00000965ab59d2733892000009cdab49cce2486d00000a76596c55e3386d00000a51ab4d4ce2486d00000965f8709273389200000965ab49ce72483d00000965ab5794b3386200000965ab4d4ff2486d00000965b549cce2c49200000a9dab578ce2486d00000a05ab49cd42486d00000965ab49d0232c6d00000a05ac49cce2486d00000a71ab49cce2488100000965ab61cce2486d00000965ab508eb3389200000965ab49ced3389200000965ab4d4ce2487c00000965b149cdc2486d00000965b15d8ce2486d000009662549cfb3386d00000965ab4b4ce2786d00000965e26ad273b4ce00000965ab49cd424867000009661349d103389200000a1e596ad273bc9200000965ab5c1514f92700000965ff49cf22786d00000965ab651272486d00000965ab5c1272646d00000965ab49cce2486a00000a69ab49cce2486d00000965ab635582486d000009be596ad58338b100000965c849cce2906d00000966446acce2486d000009a5ff789272486d00000965f149c921b45600000965dc4c0ce2486d000009662549cde2486d00000965b949cce2786d00000965c26ad763389200000965e24c0ce1b445000009a5ff49c921b43400000aa25972d273389200000965de49cce2486d00000a9d9849cce2486d00000965ab49cce23c6d00000a9da849cce2486d00000a05ab4b4ce2486d00000965ab4c0ce2486d00000965ab508d42486d00000aa29d7354b3389200000965e26ad303386d00000965ab4c0d22486d00000965b949cf22646d000009cdab49cce2487300000a05ff49cf22486d00000965ab5514149cce00000965b949cc52486d00000a76598f0ce2486d00000965dc4f927338920000096631895273389200000965f76ad272486d00000a1e596ad273c89900000965ff49cf22486700000aa29d6ad473389200000965ff4d4ce2786d00000965f85d8fb3386d00000965b952cce2481000000965c8520ce2486d00000a76598acce2486d00000a75ab58cce2486d00000966056ad273389200000991ab49cce2786d000009a5c849cce2486d00000a2dab49cce2486d00000a05b949cce2486d00000965ab4f927338920000096632811ab2486d00000965f1721272486d00000965ab609422486d00000965ff6d5302486d00000965ab5a10e2486d00000965b549cce2786d00000966196ad273389200000965ab52cf22482500000a76596ad653389200000a1e597a1ab49cce00000991ab49cce2486e00000965ab49cd92906d00000965ab63d103389200000965be49cf22486d000009cdab551273386d00000965e2578ce1f06d0000096625709273389200000a71b949cce2486d00000965b952cf23389200000a05ff4d4ce2486d000009cdf849cce2486d00000966488e5ab49c6d000009cdab49cf22d89200000aa2876ad483389200000965ab49cce23c7300000a51dc49cce2486d000009a5ab49cce2b06d00000965ab4c0ce2487300000965e26ad303387300000ac287735273389200000965dc49cff2486d00000965d549cce1b45600000991ab49cce2486700000965ab49ceb39c9200000965ab49cce2787700000965f16ad272b06d00000965ab49cce2c42200000a05b549cce2486d00000965b9508ce2486d00000965ab49ceb3389900000965dc49cce2487c00000a1e596ad423389200000a51ab49cce2486d00000965c8545273386d00000965ff789271cc6d00000965e249cce24881000009a5df49cce2486d00000965ab49cf22647700000965ab49cff2486d000009a5ab49cd92486d0000096620770ce2486d00000965ab49cce2e09200000966334f9273389200000965ab5d1272486d00000965ff4d4f23389200000a05ab4d4ce2786d00000965ab49cce2487c000009cdab5d8ce2486d00000aa29d6ad3e3389200000965cc49cce2486d00000966206acce2486d00000a05ab49cce2487700000991ab508ce2486d00000a1e596ad2743892000009ea6f6ad9249c6d00000965e2578ce1b45600000965ab49cce2c49e00000aa259881f12486d00000a76596ad513386d000009e5ab5f1272486d00000965f84c0ce2486d000009be5977d273386d000009ea6f6ad273b49200000965d5721273386d000009cdab49d023386d00000965ab49cd42646d000009662a7fcce2486d00000aa29d7fd7c2486d00000965ab49cce2d09200000965b5508ce2486d00000965ab52d273c89900000965e26ad27338b4000009ea596ad274409200000965c8508ce2b06d00000aa2878a8ce2486d00000965ab49d083c89e00000966057e127338920000096604709ab49c9200000abe697fd272486d00000a6e946ad5e3386d00000965ab52cce2482e00000965ab4d4f23389e00000965f84f9273389200000965c8560ce2486d00000965ab4d4ce2486200000a722c6acce2486d00000a767a6ad543386d00000a51ab49cce2487300000965f5765ab49c6d00000002597fd273c89e00000a9dcd52d273389200000965ab545273646d00000965ab49cff24873000009662551d273389200000a05ab49cce2c4920000096632720ce2486d00000a19e2735273389200000965ab5913e49cce00000965ff49cce2786d000009a5b54c0ce2486d000009ce2549cce2486d00000965ab508ce2487700000965ab49cce2587300000965ab4b4e72486d00000965ab4a4de2486d000009ea596ad273b89200000965b15794b3389200000965d76ad273386d00000965ab5c1272906d00000965ab4b4ce2646d00000965c849cfb3386d00000966206acce2487300000965ab579273706d00000965dc4d4ce2486d000009662b5c1272486d00000965b952cce2646d00000965ff789273146d00000a05ab4d4f23389200000965ab49cf12486d00000965ab560ce2b06d00000965d56ad273646d00000a1e596ad4b3389900000965ab5d93e3389200000002817fd273c89200000965b949ce72486d00000965fd6a1272486d00000965b1578ce1b44500000a1e596ad2739c9200000965b949cce2646d00000a05ff49cce2486d00000965ab4d4ce2486d00000965c849cde2486d00000a51f849cce2486d00000aa259881d53386d000009be5984d273386d00000965ab52d1d3c89200000965ab508ce2c49200000965f849cff2486d00000965ff6ad7a2486d00000965ab49ccf2646d00000a062a6acce2486d00000a76596ad8c3386d00000965ab560d92486d00000965db72dab49cce00000965c249cce2485600000a05ab49cef2486d00000002947895e3386d00000965f849cce2487c000009a5ab5c1272486d00000a71ab490ce2486d00000a1e6f6ad27338b600000965be52cce2486d00000966254c0ce2486d00000991ab49ce72486d00000966207e0ce2486d00000965ab49cce2886d00000002597895e3387c00000991ab49cce2646d00000965ab4f8ce2485200000965ab49d0e2c49200000965ff49c9e1b41900000965e249cde2906d000009a5fb49cce2486d00000a19ab49cce2485b00000965be49cce2486d00000965b549ce72486d00000965ab49cde29c6d00000965ab49cfb3646d00000965ab49cde2b06d00000965c849ce72b06d00000a05ab49cce2786d00000965ff6ad342486d00000a51ab5d8ce2486d00000965b549cce2646d00000966254f92733892000009662a6acf23389200000965ab5d8ff2486d00000965ab551273c86d00000a76598c5ab33892000009cdcd6ad4b3389200000965b1579273506d00000965ab4d4ce2487300000965ab5d8ce2487c00000965c8709273389200000a767a894ce2486d00000991ab49cce2306d00000965ab52cce2647700000002597fde249c7300000aa2597fd272487300000965b149cce2506d00000a05ff49c921b41900000965ab49ce72487700000965b149cce2b06d00000a1e6f6ad5e52cce00000965ab5c15149c6d00000965ab49ceb338a400000965ab49cce2647700000965ab49cf23389e000009be596ad8f3386d00000a76596ad4b3509200000965ab49d093386d00000965f849c921b43000000965e2735393389200000965ab508ce2786d00000965ab49ccc2486d00000965b149cd92486d00000a19b149cce2486d00000aa259765273386d00000965ff601352486d00000965c26ad27338ac00000a522549cce2486d00000965e2579213386d000009ce596ad4b3c89200000965b15792d3386d00000aa2597a52733892000009662549cff2486d000009be59789273786d00000965d56ad7049c6d00000965f84d4ce2486d00000965ab49ce72c49200000965dc49cce2486d000009662549cce2487c00000a1e596ad27338b500000965ab56cff2486d000009661349cfb3386d00000a05ab49cf23389200000965ab49cce2c49900000a9dab49cce2487c00000965ab49cd42906d00000965c26ad273649200000965ab49d023c86d000009a5ab49ceb338920000096625880ce2486d00000a05ab508ce2486d000009a5ab5e8ce2486d000009663a770ce2486d00000a1e6f6ad27410f200000965ab5d8921b43000000965ab5c1582486d00000965f16ad273ac9200000a7659895513386d000009662c338921b45a00000aa269789273386d00000965ab49d0a2486d00000965ab49cce2486d00000965fc49cee3389200000965ab49d063386d00000aa2597c5272486d00000aa259881c23389200000965e2490ce2486d000009663a6acce2486d000009be596ad273fcb100000965ab56cce2d092000009660f7a5ab49c9200000965ab5c1273ec6d00000a76596ad413389200000965ab6317049c6d00000991b1579273386d000009a5ab49cd42486d00000965ab4b4ce2906d00000965ab614ce2486d000009cdc849cce2486d00000966186ad272486d00000965dc49cce2487300000a1e6f731273389200000965fb49cfb3386d000009e5ab579274106d00000965ab545273acce00000965e249cce1cc4500000965ff789302486d00000a76646ad4b3389200000a76596ad473389200000965b949cce2906d00000965ff4c0921b43400000965c849cce2486a00000965ab49cce2487300000965ab49ce72786d00000965ab63cfb3386d00000965e26ad273387300000965ab49cd224873000009be596ad683386d000009663349cce2486d000009665749cce2486d000009662f7fd302486d000009ea6f6ad274106d00000965d149cce2486d000009e5ab649272486d00000965ab5ed242486d000009cdab49cce2b06d00000966254d4ce2486d000009be5983dab49c6d00000965e2578de2486d00000965f5709ab49c92000009660a6ad2733892000009a5ab4b4ce2486d00000a9dab4d4ce2486d00000965ab5794b410f200000965d56ad273acce00000965b15c1272486d00000965e249ce32486d00000965ab5514b3386d00000965f16ad2d2486d00000965b96ad4b3c89200000a767a6ad273ac9200000aa259755273386d00000965b14e4ce2486d00000965ff6d5272487300000965ab545273506d00000991ab49cce2906d00000965c84c0ce2486d000009e5ab49cce2646d000009cdab49cd92486d00000965ab49cce2b06a00000965ab52cce2641000000965ab560ff2c49200000a05ab49ce72486d00000965ab551273386d000009a5b949cce2486d00000a1e596ad483389200000965ab560eb3389200000965b549cce2906d00000a05ab49cce2646d00000965c26ad7049c9200000965f16e5272486d00000965f849cce2486d00000965b15794b49cce000009b9ab49cf2338b600000a71e249cce2486d00000965c84f92733892000009cdab49cf22483400000aa2598c8ce2486d00000965ab49d072486d00000a19ab49cce2486a00000965ab591273386d00000965d56ad273506d00000965af49cde2486d00000965ff6ad353c89200000965ab52cf23389900000965ab4c0ce2b06d00000965ab5f0921b45500000965ab49cfb3acce000009b9ab4d0ce2486d00000965dc5d8ce2486d000009a5e2735273386d00000ade9d6ad7c2486d00000965ab5e8fb3386d00000965ab60d273389200000965ab5452d3386d000009b9ab49cd42486d00000a51ab4a4ce2486d000009660f755ab49c6d00000965ab49cce2907700000965ff49cce2d46d000009ea596ad273ec6d00000991f16ad272486d000009ea596ad8c49c6d00000965ab578ce2488100000965ab560d42486d00000a76596ad3e3389200000965ab508e72486d0000096620338921b45600000966255c15149c6d000009a5b549cce2486d00000965a249cde2486d000009a5e26d5273386d00000965ab4a4ce2487c00000965ab49cdc2486d00000965ab5d8ce2486d00000965ab49cef2d46d000009e5ab49cce2487a00000965ab4c0d92486d00000965ab508ce2646d00000965ab4f927338ac00000a71ab5f0ce2486d000009664549cce2486d00000965ab52d023386d00000965ab49ceb3789200000965f16d5272486d00000965b9545273386d000009ea6f6ad583386d00000965e272d273389200000a76876ad3b3389200000965ab5e8cb2486d00000965d56ad2d3386d00000a1e59721423389200000a19ab579273386d00000965f849cce2487300000a51c849cce2486d00000965cd49cce2485900000966566acce2486d00000965ab49d023386d00000965ab5790b3786d00000965a549cce2786d00000965ab49cfb3506d00000965c849cff2486d00000965ab5c14149c9200000965ab49cce2c4a400000965ab4f9273649200000965ab49cde2488100000965cd52d27338a8000009a5ab49cce2487700000aa2598c5273389200000965c849cce2487c0000096633591273386d00000965b149ceb3389200000965f16ad272487700000965d56e5273386d00000a967a6ad7c2486d00000991ab545273386d0000096620720ce2486d00000aa259924ce2486d000009ea59925ab2486d000009664f6ad272486d00000a51e249cce2906d00000965b5545273386d00000a1e596ad42338ac00000a51ab49cce2b06d000009a5b549cce24873000009662549cce2486d00000a05a549cce2486d000009664049cce2486d00000965ab5d8ce2487300000991ab4b4d42486d000009e5ff6ad272486d00000a9dab49cce2486d00000965ab49cff2b06d00000965b9560ce2486d000009cdab5c1272486d00000965e249cce2907c00000a05ab49cce2d46d00000965ab4b4fb3386d00000965ab49cf22e49900000965ab56cce2486d00000aa259709273389200000965ab528ce2486a00000965eb49cce2486d000009a5ab49cce2c49200000965e26ad5b3386d00000965ab49cce2b07c000009662b490ce2486d00000965b15794b3381000000991d56ad273386d00000a06597fd273c89200000965f16ad272c49200000965cc49cce2b06d00000965b149cd42486d00000965ff765273386d000009be5977127338b100000a51ab49cd92486d00000965be5f15e2486d00000a1e598c9ab3389200000966206acce2b06d00000965df49cff2486d00000aa287765273386d00000965d56d5273386d00000965ab5452733877000009662a765ab3386d00000965f849cfb3acce00000965ab578ce1b45900000965b849cf2338b600000965ab4b4de2486d00000965b949cfb3386d00000965ab635272486d00000965ab49cd92487c00000991ab560ce2486d000009ea597e1273ec6d00000965fb49ced33892000009be596ad27338b1000009cdb949cf22486d00000965ab49cce2787100000a52597895e3386d00000965c26ad273509200000965ff520ce2486d00000966206acd92486d00000a1e736ad273c89200000965ab49cf2338b500000965ab5794b3383d000009ea6f7e1272486d00000965ab49ce72646d00000965f85d8ce2486d00000a767a7f1272486d00000965b5560ce2486d00000965b84d0ce2486d000009660749cce2486d00000965b849cd42486d000009a5ff789273386d00000965b949cde2486d00000965ab49cf229c6d00000965df49cce2d092000009662549cce2487300000965ab4d5043c89200000965ab520ef2486d00000965d56ad273387700000965ab5c1302486d00000a1e597212739c9200000a526f789273386d00000965b14b4ce2486d00000991ab568ce2486d00000965ab579274107a00000aa2877c5272486d00000965c84d4ce2486d00000991ab49cfb3386d00000965ab54527338b100000965e249cde2d86d00000965ab578ce1b44e00000965ab578de2906d00000965ab5d8fb3acce00000aa29d894ce2486d00000965ab60d763389200000aa29d8b0ce2486d00000965ab484ce2646d00000a05ab49cce2487100000965b549cfb3386d000009be59789273387c000009ea596ad763ec6d00000966046ad272486d00000965ab52d2d3509200000965ab560ce248770000096607614ce2486d00000965ab5c13e49c92
  | 6 => 0x2596ad273389e1b445002597e15e49cce2486d002596ad27364921b46d00259755ab49cf23386d002598b1ff49cf22486d002596ad273389e1b40200259755ab661273386d002736ad27450ce2486d002596ad705b5272486d002597ddab695272486d0029d9e9ab49cf22486d002a8a759849cce2486d002596ad2744cce1b422002816ad27338921b45b002596ad68338a92486d002b0965ab579273386d002646ad27350921b410002879662c6ad4b338920026e6ad273c8ce2486d002596adab49cce2786d002946ad27378ce2486d002596ad27338921b45800281a05ab49cce2486d00287965de49cce2486d002596ad4b338c82486d002596ad273ecce1b410002596ad27338a41b40b002596ad5e378921b44500287965ab49cce23c6d002598b1b949cce2486d002596ad7c49cd92486d002596ad583c8ce2486d002597fd273389e2486d002596ad98560ce2486d00287965ab4c0ce2486d00259749ab49cce24877002596ad6f49cce2486d002596ad76338922086d0029d965ab628ce2486d002596ad27338921b40c0025989527338b62486d002596ad27378ce2487c00259755ab49cce1b401002597fdab49cce24873002597fd273389e1b43400000991b149cce2486d002596ad27338c82486d002596ad7049c921b4250027a9bdab49cce2306d00000965ab560ce2c492002646ad27338922246d002596ad27338921d46d002596ad27350921b407002596ad27338bd2906d0029d965ab49cee338920027a965ab49ceb2f492002816ad27338921b4450029d965ab474ce2486d00259882206acce2486d00000965ab4d4d92486d002816ad27338921b402002736ad27338921dc6d002596ad4349cce2486d002596ad27378921b410002596ad76578ce2486d00259905ab52cce2486d002597ad27338b62486d002596ad5e49cce1b415002596ad27338921b44600292965ff6ad272486d002597fdab49c921b419002596ad3f49cce2486d002597fde26ad271b419002596ad27338ce2906d0027a965ab49ceb3389200259895cd49cce2486d00287965ab4f92733892002596ad273ecf23386d00259965dc49cce2486d002816adab49cce2486d002596ad9849cfb3386d002596ad7649cfb3386d002596ad58338921b401002596ad42338921b45b002b7965e249cce2486d002648b1ab49cce2486d00281965ab49cf233892002646ad2d338921b410002596ad273e0ce2486d00259905ab49cce2486d002596ad273c8921b426002596ad30450ce2486d002596e527338992486d0025994dab49cce2486d002596ad35338922486d002696ad27338921b40b00259789ab4d4ce2486d0025978927338921b44b002597b5c849cce2486d002596ad273389e2786d002596ad5349cce2486d002599222c6ad272486d002598b1b549cce2486d002597c5ab49c921b40b002596e5273c8921b425002817fd27338921b434002596ad35338921b43400259965ab49cce2486d0029b965ab49cce2906d002596c527338921b410002596ad273c8de2486d002596ad424ecce2486d002736ad4b49cce2486d002946ada549cce2486d002a3965ab49cde2486d00287965ab49cf224825002596ad9849cde2486d002597fdf849cce2486d002696ad27338bd2486d002596ad5e338921b44700287965ab49cce2a492002597c1ab49cce2486d002596ad2d338921b407002596ad273ecce1b401002879bdab49cce2d8920025989527338922086d002596ad5e338921b452002596ad3e49d1433892002596ad42338921b445002597fdab49cf22d8920025977127338921b404002596ad42338921b402002597c5ab49cbd2486d0027a965ab49cd42486d0025977127410ce2486d002696ad27338ce2486d002736ad2749cce2486d0027a965ab52d273c892002596ad4b49cd4248100025972127338921b4000028797dab49cce2486d0029d9e9ab450ce2486d002598955e49cce2486d002596ad27338921b40a002597c5ab49cce2486d002596adab508ce2486d002596d1ab49cce2486d002879bdcd6ad273389200259709ab49cce2481000259881ab694ce2486d00294a1dab49cce2486d002597b5ab49cce2b06d002598b1ab49cce24877002816ad273389e2486d002596ad27364921b435002596ad2d338921b412002597fdab49c921cc19002596ad27338921b4040028c9a5ab49cce2486d002596e527338921b407002596ad27414ce2486d002596ad27320921b419002596ad27378921b4010026f965ab5c1272486d002596ad27338921b43d002596c5273c8ce2486d00287965ab49cff2486d002596c59849cce2486d002597fd273c8ce2483400259835ab49cce2486d00000965c849cce2486d002596ad27410ce2486d002816ad273389e1b434002596ad27338b32486d00000965b152d2733892002a8965c849cce2486d002596ad4b49cce2488900287965ab49cce2487c0027a965ab5b5272486d002596ad7049c921b46d002596ad27378921b452002596ad27338a41b419002596ad5949cce2486d002596ad5149cce1b40b00280965ab579273386d002596ad27338b124889002596ad27350d42486d0027a9bdff6ad272486d002597fdab5d8ce2486d002596ad27338921b460002597b9ab49cce2483d0026f965fb49cce2486d00259821ab49ceb338920026f965ab49cce2c48200287966206acce2486d002596ad27364ce2786d002596ad27478ce2486d00259965ab49cce2487300259811cd6ad272486d002596ad4b4c0ce2486d000009cdb949cce2486d002596ad27338ac1b40000259709ab49cf2338920027a965ab4b4ce2486d00000965ab579273506d002596ad70545272486d002596c5b149cce2486d00259709ab6612733892002596ad8d579272486d0027a9be596ad274106d002596ad5149cce2f46d002946ad27450ce2486d002596c527338921b401002596ad4b4b4ce24810002596ad27384ce2486d002646ad27338921b407002596ad273acce24825002596ad7c5c1272486d002596ad273389924877002598b1ab49cce2c492002596e1273c8ce2486d002596ad273c8ce27892002596ad27450ff2486d002596ad273389221c6d002ae965ab52d2733892002946ad27338a41b445002596ad5149cce3386d00000965ab49cce29c6d00000965ab49cce2b06d002596ad3049cce2486d002596ad273c8921dc2500259789ab4c1273386d002596ad8649cce2486d002596ad273c8ce27834002596d527338921b40700259755ab49cce1b40b002596ad27450ce2487c002b4965ff49cce2486d002a8965ab49cce2b06d002596ad2733892188340029d965ab49cce2906d002596ad27364921b40000259939ab338921b452002596ad4b4f927338920027a965b949cce2486d002596ad2739c921b45b00287975ab49cce2486d002596ad27338bc2906d00259881ab450ce2486d002596ad27338a41f045002696ad27338921b419002596ad27338921cc0400259709ab49cce2480100269789ab49cce1b419002816ad27364ce2486d002598b1ff52cce2486d0029d965ab545143386d002596ad27338991b45b0027a965ab49ccf2486d002596ad2d350ce2486d002596ad27338921b44d002596ad27410ce24873002597c5ab49c921b4190029d9e9ab52cce2486d00000965df49cce2486d00259755ab49cce2f46d00000965ab49cd92486d002596ad3e49d273389200000a19ab49cce2486d002596ad58338921b40b002596ad27338b22486d0025977127338922486d0029d9e9ab49cbd2486d002a8965ab49cd92486d00259789dc49cce2486d00259965f849cce2486d00259895ff49cce2486d002596ad27350921b42500259755ab49cce3386d00287965c849cce2485b0025978927338921b445002598b1ff49cce2486d00292965ab49d042486d002596c9ab49cce2486d002596ad76338c82486d002596ad4b49cf2248250025977127338921b434002596ad27338921dc07002596ad9149cfb3386d00259735ab5794b338920029d9e9ab49cce2486d002b3965ab49cce2486d002596ad7049d1d2486d002a8a1e2c49cce2486d00000aa259880ce2486d002816ad273c8ce24834002596ad2739c921b4450029d965ab4a8ce2486d0027a991ab49cce2486d002596ad58338bd2486d002596ad2739c921b402002596ad27338b12a492002596ad27338922486d002646ad4b49cce2481000259789ab49cce2486d002596ad27338991b445002596ad2743cce2486d002596ad354d4ce2486d002596ad27338921b4570029d9a5ab49cce2486d002596ad27338991b4020025973527338921b456002598edab49cce2486d002a8965bf49cce2486d002596ad273ecce1b40b002596ad58338ce2486d002596ad27408ce3206d002596ad27338921b434002596adab49ce72486d0027a965b549cce2486d0029d965f16ad272486d002736ad27338921b41000287965ab4d4ce2486d002596ad27338921b405002596ad3049cce24873002598e9e26acce2486d002596ad58338b124882002946ad4b49cce2486d00000965ab49d0d3386d0026f965ab49ceb33892002596adab49cce2646d002597e127338921b404002598bdab49cce2486d000009cdab49cce248770026f965ab5e8ce2486d002596ad4b49cff2486d002596ad5e49cce1b41100269965b549cce2486d002597e127410ce2486d002596ad5149cce1b41900287965ab49cce2b05b002596ad273fcb12486d002a89be59789273386d002596ad273ecce2f46d00259965ab5d8ce2486d002696ad27338921cc19002596ad27410f22d892002598ddab49cce2486d002598b1ab49cce2786d002596ad273acce2486d002596ad27358ce2486d002646ad27350ce2486d002596ad4b49cce2487c002596ad27338b12480700287965ab5092733892002946ad2749cce2486d00287965c86ad2733892002596ad2d338921b4250026f966166ad273386d002596ad27378921b40b002596ad35338921b4360025972127338b62486d0026f965ab49cf2338b6002596ad2749cff2486d002596ad273ecce3386d002596e54b338921b425002596ad27338921b44a002596ad27364921b43b00259881ab52cce2486d002596ad27338921b46900000965b54c0ce2486d00000991ab579273386d0027a965ab49cce24877002736ad273c8ce2486d00287965ab52cce24825002596ad27338921b426002596ad2749cce2487c002736ad9849cce2486d002596ad4b49cce2481200280965ab49cf22486d002ad965b149cce2486d002596ad35450ce2486d002596ad27378bd2486d0029d965ab579043386d002596ad27338922206d002598e62c6ad273386d002596ad7c49ceb3389200259831e249cce2486d002a8965ee49cce2486d002596ad27338922046d00259735c849cce2486d002596e527338921b425000009661349cce2486d002596ad27338921b41b0026a965ab49cce2486d002597d5ab689272486d002598b1ab52cce2481000259881ab49cce2486d002596ad2748cce2486d00259755ab49cce1b419002596ad27338921b45a0026f965ab49cd42486d002596ad273389224873002598b1ff49c921b4190027a965ab5f1272486d002596ad76338921b404002596ad27378ce2486d00259789ab49cce248730029d965ab545273386d002597212739cce2486d002596ad27370921b43d002596c527338921b40b002596ad2733c921b42500000965f56ad272486d0027a9bdab49d042486d002596ad76410ce2486d002818b1ab49cce2486d002596ad5e52cce1b410002596ad27338cb2486d002596ad27338921cc34002596ad30338921b410002596ad9749cce2486d002596ad27350921b46d002596ad27338952486d002597fdab49c921b41a0029d965ab648ce2486d002596ad27338b62b06d002596ad1d338921b44500000965ab49cce2a06d002736ad27338921b401002a8a1dab49cce2d892002a29a5ab49cce2486d002596ad273a0ce2486d0028e965ab49cf233892002596ad7049c921b400002596ad58338921b419002596ad27338921b408002596ad273a4921b462002736ad27338991b425002596c527338bd2486d002599662549cce2486d002596ad5e49cce1b4100027a965ab49cce2c492002596ad3649cce2486d002a8965d549cce2486d002a7965ab49cce2486d00259851ab49cfb3386d002597ed27338c52486d002646ad27338921b425002596ad27338921b431002598b1ab52cf2338920025972127338922086d00259709ab49cce2480b0025992d6d49cce2486d002596c527338ce2486d00259735ab49cce2b06d002596ad7c49cd42486d002596ad3e49cce24810002596ad2745cce2486d0029d965d56ad273386d002a8a1dcd6ad2733892002598953e49d143389200000965ab5c1272486d00287965ab49cce24862002596ad27364b62486d002596ad5449cce2486d0027a965ab629272486d002596ad273c8ce23c6d002596ad2739cce2b06d002a8965ab5c1272486d002596d527338921b425002596ad303c8ce2486d002596ad4d49cce2486d00000965ab4e4ce2486d002597fdab5f15e2486d0026f965ab4b4ce2486d002597215e49cce2486d002598e1ab49cce2486d002596ad984c0ce2486d002596ad27338922286d002597e127338922486d00259709ab49cce2f492002596ad273ecce1b419002597e1e249cce2486d002598c61c6ad2733892002596ad4b49cd433892002596ad8e49cce2486d002596ad273389e1b407002598b1ab508ce2486d00000965fb49cce2486d002598d5ab508ce2486d002596ad27338921b443002596ad2d338921b46d0025989527338921b40400259735ab49cd92486d0029d965ab560ce2486d002597e127338921b434002b0965ab49cce2486d002596ad4b338921dc250026f965ab49ce92486d00287965bf6ad2733892002596ad44338921b46200259709ab49cce33892002596ad2739ce42486d002a8965ad49cce2486d002929bdab49cce2486d002596ada549cce2486d002596ad6449cce2486d002596ad4b4d4ce2486d0027a965ab490ce2486d002596ad27338ab2486d0025989527410ce2486d002596ad70545274506d002646ad27338921b462002596ad2d338921b414000009a5ff6ad272486d002946ad5e338921b445002596ad3e49cf233892002596ad30338921b43000287965dc49cce2486d0026f965b949cce2486d002596ad27338ac2086d002596ad984f9273389200000a767a6ad7c2486d002596ad273eceb33892002596ad273fcff2486d00000965b949cf22486d002a4965ab49cce2486d002596ad27378921b4190027e965ab49cce2486d00000965ab63cce2486d002597fdab49c921b420002596ad30338921b4010025982dc849cce2486d0029d965ab578ce2486d002597e1273ecce2f46d002596ad27344ce2486d002596ad27444eb338920029d965e26ad5e3386d002596ad27338921dc25002597e1273acce2486d002597fd27338921b456002596ad3549cce2486d002596ad7c4b4ce2486d0027a965ab49cfb2486d0026d965ab49cce2486d002596e527338921b46d002596ad5e338921f045002596ad5e49cce2b06d002b2a05ab49cce2486d002596c5ab579273386d00284965ab49cce2486d0029d965ab49cfb3386d00259855ab49cff2486d002946ad27338921b41000287965ab49cce2486d002596ad273ccce2486d002597fdab49c921b422002af965ab49cce2486d002596ad27448ff2486d002596ad76338922486d002816ad27338921b407002596ad2740cce2486d002596ad27364922086d00259789ab49cdc2486d00000a7659894ce2486d002596ad273fc921b410002596ad27338921b41500259789ab5d8ce2486d00000965e249cde2486d0026f965ab510ce2486d002596ad3e49cce24801002597fdab49c921b41c0026f965e2735273386d002596ad76338921b434002596ad7e49cce2486d002a8a76598b0ce2486d002946ad27378921b4450026f991ab49cce2486d002596e57c49cce2486d002596ad27338921f010002596ad27338a41b45b0025977127450ce2486d00287965ee6ad2733892002596c527338921b4190027a965ab49cce2786d002596ad5e49cd92486d002596ad27338921b4360029d965ab49cde2486d002596ad27408ce2486d00259881ab338921b410002596ad27338921b44c002646ad27338921b46d002596ada749cce2486d0026f965b549cce2486d002596ad27338b1248250027a965ab49cd02486d0029d965ab49ccb2486d002596ad27378921f045002596ad763ecce2f46d0029d965a849cce2486d002596ad7a338c52486d002946ad273c8ce2486d002a8965af49cce2486d002596ad763acce2486d002598b1ff338921b452002a3a51ab49cce2486d002596ad2747cce2486d002597c5ab675272486d002946ad9849cce2486d002596ad27450ce2486d002596ad273fcf22486d0027a965ab49cc52486d002597fdc849cce2486d002a89659c49cce2486d002596ad273acce24800002596d527338921b46d002596ad9849cff2486d0026f965ab49cce2186d00259709ab49cce2481900259799b949cce2486d002596ad27338a41b445002596ad27438a92486d002a5965ab49d043386d002596ad273c8ce2487c002646ad7c49cce2486d002596ad27338a41b402002596ad9849cce2487c002736ad27338921b40b002596ad42338921b40700000965ab49cff2c49200291965ab49cce2486d002a8965a249cce2486d002596ad27338921e46d0027f965ab49cce2486d0029d965b149cce2486d00000965ab49ceb33892002596ad8049cd92486d002819e9ab49cce2486d00000965ab5e8ce2486d002596ad27338b62483d002596ad4b49cce2486200259881ab3c8ce2486d002598f1ab49cce2486d00264965b149cce2486d00287965ab49cce2487300259789ab49cce2d83d002a8965ab49ceb33892002596ad624d4ce2486d0025989527338922486d0029d9664e6acce2486d00259881ab660ce2486d002696ad27338921b45b00287965ab6292733892002596adab49cce2906d0026f965ab49cce2487700259895e249cce2486d002596d57c49cce2486d002596ad2738c921b456002946ad27338921b4010029d965ab4a0ce2486d002909cdab49cce2486d002597c5ab49c921b45b002736ad27338bd2486d0025989527338921b434002596ad273fc921b401002596ad7049cb62486d002598adab49cce2486d002598b1ab49ce72486d002b59662c6acce2486d002596ad27338921b45f002596ad27338921dc6d002ae965e249cce2486d00259735ab49cce2483d002597fdab49cce29c6d002597fdab49cce2b06d00000965ab49cce24881002736ad27338ce2486d002596ad27338921f001002598b1ab49cce2646d002596ad27350921b4000029d965c26ad273389200280965ab49cce2486d0025992d7c49cce2486d00259735ab5c1272486d002597714b49cce2486d00259881ab338921b401002596ad27338921f047002598f5ab49cce2486d002696ad27338921b44500000965ab5794b3381000000965ab4d0ce2486d002696ad27338921b4020025977127338b12486d002596ad27450ce24873002596ad7c49cce248770025970dab49cce2486d00000965ab49cd42486d002596ad27338921b450002597c5ab49c921b44500000965ab5a0ce2486d002596d527338921cc6d002597fdab49cd92486d002597c5ab49c921b402002596ad5e338921b44b0026f965ab49cce2c492002a8965ab49cd42486d0026f965ab5f15e3386d0027a965ab508ce2486d002a8965ac49cce2486d002597712749cce2486d002596ad27338921b461002696adab49cce2486d002596ad35338921b410002596ad27338921b433002596ad30338921b40b00287965f849cce2486d002596ad4b49cce2486d002a8a75ab450ce2486d002596ad273c8ce24856002596ad273389e1b425000009660f6ad272486d002596ad273e8ce2486d002597c5ab6ad272486d002596ad27338b12486d0026f965dc6ad273386d0029d985ab49cce2486d002a5965ab52cce2486d002596ad273389d2486d002596ad273c8921b430002596ad5149cce1b45b002a8965ef49cce2486d002596ad27338992646d0025972142338921b45b0027a965ef6ad272486d0028d965ab49cce2486d002596ad7049c922086d002597fdab49cf22483400000965ab609272486d002596ad27338921b423002596ad2749cce2486d002598b9b149cce2486d002596ad30338bd2486d002596ad2d338921b400002596ad27338921f86d002596ad273c8991b425002596ad27338921b45c002596ad27314921b425002a5965ab49cce2486d002596ad3e49cce2480b002a5965e26ad273386d002596ad7c49cce2c492002596ad5e410ce1b445002596ad27378921b44b002596ad273c8921b452002596ad30338ce2486d00259965c849cce2486d002598e9ab49cce2486d002596ad70579272486d002596ad4b3389209410002596ad353c8ce2486d002596ad984d4ce2486d00000965ab4b4ce2486d002597ddab49cce2486d002597e127450ce2486d0026f965ff789273386d002a8965ab4b4ce2486d002596ad5149cce1b44500298965ab49cce2486d002816ad27338921b42500000965b952cce2486d002596ad3e49cce2f492002596e527338921b400002596ad5149cce1b402002a8965ff49cf22486d00259755ab49cce1b45b00287965ab5d8ce2486d002736ad27338921b41900259809ab49cce2486d0025978927338921f06d002596ad27338991b428002597c5c26ad272486d0029d966416acce2486d00000966255c1272486d002596ad2739c921b407002596ad66545273386d00000965ab49ce92486d002596ad8549cce2486d002596ad42338ac1b45b002596ad6c49cce2486d00273965b949cce2486d00259789ab5b1273386d002596ad3e49cce338920026f965ab49d133386d002596adab545273386d00000965f849ceb3389200259701ab49cce2486d002596ad27338991b407002596ad42508ce2486d00288965ab49cce2486d00259721ab508ce2486d002596ad27338921b42400277965ab49cce2486d00000965b949cce2486d00259735af49cce2486d002596ad4b49cce2487300259775ab49cce2486d0027a965ab579274106d002596ad8849ceb338920025972127338921b404002a8965b949cce2486d002596ad35338921b401002598cd4b49cce2486d000009ea597e1272486d002596ad27338a41b448002597a5d36ad2733892002596ad4b3c8ce24825002596ad58338921b45b002ba965ab49cce2486d00259965ab49cce2b06d002596ad273acce2d892002596ad6b560ce2486d0025972127410ce2486d00259761ab49cce2486d002596ad27338921b4110029d965ab4f9143389200259755ab49cce1b44500259741b549cce2486d002a8a75ab52cce2486d002646ad27338921b4000026f965ab49cce2786d00259755ab49cce1b402002a8965e249cce2d86d002596ad2749cce24873002946ad27338921b40b002596ad3349cce2486d002597c9ab49cce2486d002596ad76450ce2486d0029d9cdab49cce2486d00287965ab49cce2486f002597fd27338921b439002596ad273fc921b40b000009cdab49cce2646d0027a965ab649272486d0025979dab49cce2486d00000965ff4d4ce2486d002596ad6249cce2486d00000965f1755ab49c6d00259735ab49ceb3389200000965ab510ce2486d00259755ab6ad273386d002596ad273389e1b46d002596ad42338921b425002596d527338921b40000259771ab560ce2486d002596ad35364921b43400259965ab49cd92486d002a8a75ab49cce2486d00000991ab49cce2486d00259771273fcce2486d00286965ab49cce2486d002a8965cd49cce2486d002596ad27338921f00b002596ad273ecce1b45b002596ad27338921b45e002596f927338921b430002596ad58338921b445002946ad27338bd2486d002a8991ab49cce2486d002596ad27338921d06d00000965ab5d8eb33892002596ad58338921b402002b8965ab49cce2486d00292965ab49cce23c6d0029d969ab49cce2486d002879662549cce2486d002597fd273c8921b43b002596ad273fcbd2486d002596ad30338921b419002596ad27338ac1b4040027a965ab49ce72486d00259789ab4c0ce1b41900259881ab338921b40b002596d527338921b41e00000966486ad272486d00000965b549cce2486d002597a1bf6ad273386d002946ad27338ce2486d000009ea596ad762486d002596ad27410ce2506d002596ad27338921b43c00000965c849cce2b06d00259855dc49cce2486d002596ad27338921b86d002596ad27410ce2b06d0025978927338921b456002597e14b49cce2486d00000965ab49cde2906d002596ad27350b62486d0027a965ab49cce2646d002a8965b549cce2486d002596adab560ce2486d002596ad7c49cce2786d002596ad27338bd2487c002597fdab5c1272486d002596ad273fcce2486d002596ad68338b62486d002596ad5e338921b4450025977127338921b4100027d965ab49cce2486d002819bdab49cce2486d00259789ab578ce1b44500259919ab49cce2486d00259841ab49cce2486d0026e6ad27338921b422002596ad27378921b45b002596ad273fcb124882002597212739c921b45b0026f965d36ad273386d002596ad14338921b45200259881ab338bd2486d00000965fc49cce2486d002596ad6452d273386d002596ad27338ce2487c002596ad273acce24882002596ad27338921dc00002596ad273389e1b439002596ad273ecce1b4450027a9bdab49cce2d86d002596ad27364921b404000009664b49cce2486d002596ad3e49cce24819002597e12749cce2486d002816ad27338921b46d002596ad273ecce1b40200259855ab49cce2486d00000965ab4d4ce2786d002596ad27338921b41d002596ad27394ce2486d00259735ab49cd42486d002866ad27338921b43d000009be596ad583386d00259755c26ad273386d002596ad27448ce2486d002597fdad49cce2486d0029ba51ab49cce2486d002596ad27410d92486d00259881ab338ce2486d00273965ab49cce24877002596ad27338921b410002596ad27338921b467002598dd27338921b4560025989527450ce2486d002596ad273c8921b42b002b0a1dab49cce2486d002596ad5e49ceb338920029d965ab4c0ce2486d002596adab49cfb3386d00000965ab49cce248770029d965f76ad272486d002a8965ab49cce24877002a8965e2579273386d00259771273c8ce2486d002596ad27378921b445002816ad7c49cce2486d002597719849cce2486d002596c527338921b45b002596ad27378921b40200259859ab579273386d002596ad7652cce2486d0025972127338922486d00287965ff6ad273c892002596ad27410f224834002596ad2d338b62486d002b5965ab49cf23389200259789c849cce2486d0025984d273e0ce2486d002597fdab49c922306d0026f965ab49cce2146d00264965ab579273386d002596ad2739cac1b45b00000965dc49cce2c492002598821c6acce2486d002596ad30338921cc19002596ad273b0ce2486d0026f965ab508ce2486d00000965db6ad273386d0029d965ab4f92733892002596adab49cde2486d002596ad4249ce72486d002596ad27338b1248000025972127338921b43400259721ab49ce72486d002598b1ab49cce2906d002596ad27350922086d00000965b549cce2487300000a05ab4d4ce2486d002596ad273c8ce2486d002a3965ab49cce2486d002596ad273c8d22486d002596e5b949cce2486d002596ad9849cce2486d002596ad27338921d86d002596ad7649cce2486d002596ad27368ce2486d002a8965f1661272486d0029d9662c7fcce2486d002596ada849cce2486d002596ad42338921b46d00259735ab4b4ce2486d002596ad4b338921b43000259935ab49cce2486d00259709ab49cce2485b0025977127338921b401002596ad5e49cd42486d002946ad27338921b41900000965ab49cce2c4920027a9bdab49cce2086d002596e527338b62486d002596ad27470ce2486d002596ad272f4921b430002596c527338921b445002597d9ab49cce2486d00259755d36ad273386d002596c527338921b40200259929f16ad272486d002a8965ab49cce2c492002596ad273fc921b419002596ad35338921b40b002596ad4b338991b42500287965ab49cce2d89200287965e26ad27338b6002596ad4b49cce2486f002598f62549cce2486d00259801ab49cce2486d002596ad27338921b430002597fdaf49cce2486d002596ad27338942486d002596ad27338a72486d002596ad27338ac2486d00259789ab49cce1b430002596ad27338961b419002596ad27338921cc10002596ad27338ae2486d0027a9bdab579273386d00259789ab49cce2506d002596ad4b338921b45200259789ab49cce2b06d002596ad27338921f019002596ad2739c921b425002596c5ab49cce2486d002596ad7c508ce2486d002596ad2743cce2b06d0025972dab49cce2486d002596ad27338921b40100259735b949cce2486d002596ad853c8ce2486d002596ad273c8ce24839002596ad27338ac1b434002596ad27338991b42500259875ab49cce2486d002596ad27338c22486d002596ad35338bd2486d00000a51e249cce2486d00259881ab338921b41900287965cd6ad273389200000965ab4d4f233892002596ad27420ce2486d00259709ab49cce24845002596ad27338921b447002598954b49cce2486d002698b1ab49cce2486d002596ad2d338922086d00259709ab49cce248020025984d27410ce2486d00259965ab5c1272486d002596ad27338921b4520029d97dab49cce2486d00259789cd49cce2d86d002a2965ab4c0ce2486d00287965ab49ce7338920029d966376acce2486d002a76ad4b49cce2486d002597fda249cce2486d002646ad27338b62486d002596ad35338ce2486d002598b1f16ad272486d0029da51ab49cce2486d002596ad27364922486d002a89664e49cce2486d002596ad7d49cce2486d0026f965ab49cce2246d00000965ab490ce2486d00259789ab49cd92486d002597fdab49ceb338920027a9664e6ad272486d002a8a1da249cce2486d00286789ab49cce2486d00000965e249cce2487c00000965f1709ab49c92002596ad273389a2486d0029d965ab49cff2486d002597fde249cce1b41e00259709ab6ad2733892002598a9ab688ce2486d002a8965ab490ce2486d002946ad27338921f045002596ad21338921b425002596ad5e4b4ce2486d002596ad704f92745092002a8965ff49cce2486d002598952749cce2486d002596ad27364921b43400270965ab49cce2486d002596ad273c8ce24873002596d527338b62486d0027a965ff6ad272486d002596ad9849cce24873002596ad27338921b413000009662a6acce2486d002596e1ab49cce2486d0029d965ab49cce2487c00264735ab49cce2486d002596ad8f3e0ce2486d002596e527338922086d00000965ab49cef2486d002596ad5b49cce2486d002596ad27338bc2487c00287965ab5794b33892002a8965ab49cef2486d002596ad5e338921b44800269965ff6ad272486d00259789ab578ce1b448002596ad58338922146d0029d966206acce2486d002597e127338921b410002597fdab49cce24881002598f9ab560ce2486d0029d9ea596ad7c2486d002596ad7049c921b40400295965ab49cce2486d00259735b549cce2486d002596e127338921b422002596ad273389e1b40000267965ab49cce2486d002597e1ab49cfb3386d002596e55e49cce2486d002596ad27338a41b407002596e5ab49cce24877002596ad7049d042486d002596ad27338a41f06d002596ad39338921b43d002596ad27434ce2486d002a8965d5661273386d002596ad4b338921b42700293965ab49cce2486d002596ad27338921cc01002596ad27338c12486d00000965ff6ad302486d002596ad27338982486d002597fdab49cd42486d002596ad27338b624877002879bdab52d273389200259885ab49cce2486d00000965ab49cce2786d002596d5b549cce2486d00259895ab545273386d00259729ab49cce2486d002597fdab52d273c89200259709c26ad2733892002598b1ab545273386d002a8965ab49cce2786d002646ad27338922086d0026f965ab49ce72486d0029d965ab578ce1b410002596ad273c8ce24835002596ad27338921b42700259859ab49cf22486d002597e1273c8ce2486d0026f965ab49cce2646d002696ad27338922306d002597e19849cce2486d002597e17649cce2486d00259735ab49cce2487700000965ab49cf22646d0029d965ab45cce2486d002596ad2739c921b46d00259789cd579273386d00000a76596ad702486d002596d527338922086d002646ad5e49cce2486d002597fd27338921b43b002596ad27354ce2486d002596ad27398ce2486d000009660e6ad273386d00000965ab578de2486d002816ad27338921b40000000966396ad273386d002736ad27338921b45b002596ad76338921b410002596ad2742cce2906d002596ad514f9273386d002596ad35338921b419002596ad27338991b46d002596ad8f410ce2486d002596ad70545273386d0027a965ab49cc82486d000009e5ab49cce2486d0026f965ab49cce2a46d0025978927484ce2486d00000965ab49ce32486d002596c52d49cce2486d002816ada249cce2486d00276965ab49cce2486d002596ad27338921b418002696ad27338921b40700287965ab49d043c89200000965ff789271b419002596d55e49cce2486d00287965ab49cce2485d002a8965ff49c921b419002a6965ab49cce2486d002598b1d56ad273386d002597c5ab49c921b4070025977127338921b40b00000a05ab49cce2486d002596ad27338b62c492002596ad4b338921b42b002596ad9149cce2486d0027a965ab49cce2906d002596ad7c49ce72486d00287965c849cce2486d002a8a762c49cce2486d002ad965ab49cce2486d0026f965ab49cce2306d00000965d5709ab49cce002a8a05ab49cce2486d0026f965ab560ce2086d002596ad27464ce2486d002597fdab4b4ce2486d002597e127338921b40100000965e86ad273386d002596ad27338921b43e002596ad7c49cce2646d0027a9662b49cce2486d002597e127338c22486d0027a965ab49cf82486d002596ad27338922346d002a89664149cce2486d00259735ab52d2733892002736ad27338921b445002596ad273389220877002596ad27338a82486d00259965ab49ceb338920027a9bdab49cf22486d002736ad27338921b402002596ad763c8ce2486d0025977127338bd2486d002596ad27338921b42b00259735ab49cce2c492002596ad27338921b40b002596ad985d8ce2486d002596ad765d8ce2486d002598b1ab560ce2486d002596ad8149cce2486d00000a71ab49cce2486d0029d965ab4d4ce2486d002596ad27440ce2486d0025977127338ce2486d002596ad5a338922246d002596ad5e49cce24877002736adab49cce2486d002597fdb949cce2486d002596ad42338921b400002596ada249cf2338920025977127338b124882002596ad7049c922486d00290965ab49cce2486d00259789ab5c1272486d002596ad27338bd2486d0025972127450ce2486d002597fdab49ccf2486d002598f14f49cce2486d00259799ab49cce2646d00287965ab49cce2b06d0025989527338921b41000259839ef6ad273386d002596ad30338921b45b002597fde249cce2d86d002596ad27338922386d00259789ab4e4ce2486d002596ad27338a12486d002596ad7049c921b434002596ad27338921e86d0027a9a5ab49cce2486d002596ad27338b61b42200000965ab508ce2486d0027a96dab49cce2486d002596ad27338ce2486d002596ad76338921b401002596ad5149cce1b407002596ad27348ce2486d002598b1ab49cfb3386d0025980dab49cce2486d002596ad273acce24804002a8965f149cce2486d002596ad5849cce2c492002a8965ab508ce2486d002596ad7b49d212486d0027a965f16ad272486d002596ad27338b124882002596ad273c8ce2486f002596ad3549cd92486d002596ad27338c92486d00259789ad49cce2486d002596ad27410eb3389200259965ab49cd42486d002699a5ab49cce2486d002596ad273b8ce2486d0028c965ab49cce2486d002596c527350921b410002647fdab49cce2486d00287965ab49cd92486d002a8a1dcd49cce2486d0027a965ab49d042486d002596ad3e49cce2485b0029d965ab450ce2486d002596ad27430ce2486d002596ad5e49cce2c49200000965cb6ad2733892002596ad4649cce2486d002596ad30338921b445002596ad6553d27338920029b965ab49cce2486d002598b1ab49cde2486d00259895273c8ce2486d00000965ab49d0e2486d002596ad30338921b402002596ad27450ce2b06d002598959849cce2486d002597fdb549cce2486d00259871ab49cce2486d002596ad4b4a4ce2486d000009a5ab4c0ce2486d00259779ab49cce2486d002596ad27338921cc0b002b7965ab49cf22486d002596ad27338b62786d00259755ab49cce1b407002599362549cce2486d002596ad273d0ce2486d002596ad3e4ed2733892002596adab4c0ce2486d002a8965c26612733892002596ad2736cce2486d002596ad27350921b404002596ad2949cce2486d002596ad27338a41b425002596ad27338a42906d002598c62c6ad2733892002596ad3e49cce24845002596ad27338bd24873002596ad5749d213386d00259851ab49cce2486d002596ad27410d42486d002596ad3e49cce24802002596ad27450d92486d002596ada349cce2486d0025977127338921b419002596ad27338821b42200259735ab49cce2786d002596ad4b49d043c8920027a965ab545273386d00259965ab4b4ce2486d0025989527338921b401002596ad664f92733892002596ad58338921b407002598b1b149cce2486d00259789273386d11419002596c52d338921b410002596ad27338ce2487300275965ab49cce2486d002596ad27338c02486d002596ad27338921b42d002597fdab49cce24877002597214b49cce2486d002596adab4f9273389200000a51ab49cce2906d002597fde2579273386d002596ad30338921b41c0026f965ab53d273386d0027a9bdab49d043386d002a0965ab49cce2486d002596ad5e49cce1b42200291965ab49cd92486d00287965ab508ce2485b002598b1ab4a0ce2486d002946ad27338921b45b002596ad27338921b40300292965ab49cce2486d002596ad27338921b419002596ad27338b92486d002816ad27338b62486d00259735ab49cce2486e0028c965ab49cce2487300259789ab49cce1b419002596ad27348921b419002596ad273fc921b45b002596ad27400ce2486d002597fdab5f1272486d00000965ab49cce2907c002879bdab49cf233892002597212749cce2486d002596ad5e338921f06d002597e127338921b40b00259965b949cce2486d0025981d273c8ce2486d002598b1c26ad2733892002596ad273ecce1b407002596ad27338921f05b0027a965d56ad273386d002596ad273389e2086d002596ad2739c921b4000029d965dc49cce2486d0027a9662c7fd272486d002596ad2d338921b404002696ad27338921b42500281735ab49cce2486d0029d965ab52cce2486d002596ad273acce24892002596ad5153d273386d00259789ab49ceb3389200000965ab52cce2646d002596ad2740c922246d002596ad2d410ce2486d002596ad27338991b40000259881ab338921b45b002596ad3149cce2486d002596ada649cce2486d002597c5ab49c921b425002597e127338bd2486d002596ad3749cce2486d002597a1cd6ad273386d002596ad8e5c1272486d002596ad4b49cce2b06d002597fdb549c921b419002596ad273389222c6d002946ad27338921b445002a8965e249cce2486d00259771ab49cff2486d002597fdab49cce2c492002596ad273acce24834002a8a1dab52d2733892002596ad5e49cce2786d00287965f56ad272486d002946ad27338921b402002596ad915d8ce2486d00000965ab49ce72486d002597f127338c82486d002596ad27410f21b42200273965ab49cce2646d002596ad273fc921b44500259859ab49cce2486d002597e127338ce2486d0029d965ab49cce2486d002596ad27378921b407002596ad273fc921b402002a8965ab49ce72486d0027a965ab560ce2486d00000965ab5453e49cce002596ad273c8ce2d89200000965ab49cce2646d00264965ab49cce2486d002596e527338921b40400259789ab49cf2338b6002596ad27378921f06d002596ad27338bc2486d002597fdab49c921cc6d002946adab49cce2486d002596ad27338921f045002646c527338921b410002597fdab629272486d002a8965ab49cce2646d002596ad2749cce2b06d002596ad27338bf2486d0026f965ab49cce2906d002596ad27338921f002002596ad273eceb338bd002596ad42338b62486d002597b1ab49cce2c492002596e527410ce2486d002596adab49cff2486d002596ddab49cce2486d002596ad27338921c46d002596ad76338921b40b002596ad273aceb33892002596ad4b49cd92486d002ab965ab49cce2486d002816ad27338922086d00259881ab338921b44500000a1e59721273389200259965b549cce2486d002a89663749cce2486d0027a965ab49cfb2f46d002596ad27410cf2486d002796ad5e49cce2486d00259881ab338921b402002596ad27338a41b46d002596ad5e52cce248100027a965ab49ceb2486d002596adab49cce2487c002596ad27338921cc1900259789ab49cce1cc1900287965ab5c1272486d002596ad27350922486d00259739ab49cce2486d002596e9ab49cce2486d00259789ab49cd42486d00259731ab49cce2486d00259735ab508ce2486d002aa965ab49cce2486d0027a965ab49cfb3386d0027a9bdab49cbd2486d00000966207c5ab2486d002596ad76338bd2486d002597fdab490ce2486d000009be596ad273fc6d00259789ac49cce2486d002879bdab49cce2246d002596ad2749cd92486d002816ad5e49cce2486d002596ad5e338921b45600259881ab6acce2486d002596c527338921b4070029d965ab5b0ce2486d002596ad27350921b434002596ad4239cce2486d002596ad2742cde2486d002596ad27438b62486d002596ad5149cce1b425002646ad27338921b404002596b127338921b434002a8a1dff49cce2486d002597a5ab49cce2486d00000965ab49d1033892002596ad5853cce2486d0027a9bdab49cce2486d002596ad27370ce2486d002596ad76338ce2486d0025983de26ad272486d002596ad27338921e06d0027a9bde26ad273386d002596ad7c49cce2906d002596ad5e3386d11410002646ad27410ce2486d0025971dab49cce2486d002a89662049cce2486d00259851f849cce2486d00000965ab5ed272486d00259965ab49cce24877002596d527338921b404002596ad6549cce2486d0027a965ab49cde2486d0025c965ab49cce2486d0026f9a5ab49cce2486d002596ad5e52cf233892002a8965ab5ed272486d0026f96dab49cce2486d00000a1e596ad27338ac002596d527410ce2486d0029d965ab49cce2487300259709ab49cce2480700000965ab49cce2487a002596ad27338b72486d002596ad7c578921b4300026f965f16ad272486d002596ad7049d142486d002596ad42338922086d002696ad27338921b46d00287965ab49ce72485b002596ad35338921b45b0025989527338921b40b002597a9d56ad273386d002598b9ab49cce2486d002597e127338921b419002596ad2d338922486d00259755ab49cce1b425002597c5ab49c921b46d0025966127338921b456002a2965ab49cce2486d00259789ab4b4ce2486d00259881c26acce2486d002596ad4b49cf224826002597fdab49cce2786d00000965ab49cee33892002597fde249cf22486d00281965ab4d4ce2486d002596ad5e508ce2486d002596ad2d338921b43400000aa287735273389200274965ab49cce2486d002738b1ab49cce2486d002596ada449cce2486d002597fd273c8921b434002596ad27338921dc040025972127338921b410002597fdab49cd02486d0027a965b149cce2486d0025972127338921b4670025989527338bd2486d002696ad7c49cce2486d002b3965b949cce2486d002596c54b49cce24810002596ad27338921b406002596ad6949cce2486d00259965ab49cce2c492002596ad27410ce24877002596ad8c5b5273386d002596ad58338921b425002597fdab49cc52486d002597c5ab5f1272486d002596e527338922486d00000965ab55d273386d002596d53049cce2486d00259839ff6ad273386d00259789b949cce2486d0025989527338ce2486d002596ad35338921b445002598ad27474ce2486d002a8965ab55d273386d002596ad35338921b402002596ad3e49d1633892002596ad27338921b459002596e527338921b434002b7965ab49cce2486d0029d965f849cce2486d002596ad5e49cd41b410002696d527338921b4190026f965ab545273386d0026f965ee6ad273386d0025977927338922246d002a8965a549cce2486d0027a965c26ad2733892002596e5ab49cce2646d002817fdab49cce2486d002596adab4d4ce2486d002596ad27338921b44b002596ad76338921b419002596ad273dcde2486d002596ad4b49cce2a06d0000096620755ab3386d00000965ab49cce2d46d00000965ab560ff2486d00294965e249cce2486d002596ad2739cb62486d0029d96625450ce2486d002596ad7749cce2486d00259721273c8ce2486d002596c527350ce2486d002a8965ab49cce2d46d002596ad42338921b45d00259905ff49cce2486d0028a965ab49cce2486d002597219849cce2486d002736ad27338992486d002596ad5249cce2486d002596ad4b49cce2483d002596ad273ecce1b425002596ad5149cce1b46d002597c5d56ad272486d002596ad27338941b410002596ad27338ac1b410002596ad27338b62646d002596ad27338b124804002696ad27338921cc6d002598961c49cce2486d002a8a1dab49cce2486700259789cd49cce2486d00000a51ab578ce2486d002646ad27338922486d002736ad273c8921b42500287966376ad273389200264789ab49cce2486d002596ad27410ce2c49200287965ab49ceb3389200000965b1579273386d002597fd35338921b434002596ad7c579043386d002596ad5e49cce2246d002596ad7052d272486d00259735ab49ce72486d0029c7fdab49cce2486d002596ad8d49cce2486d0025977127338922186d002646ad27338921b434002597e176338bd2486d002aca51ab49cce2486d002596ad51545273386d002598b1ab4c0ce2486d002596ad2739ce72486d002596d527338922486d00259735ab49cce2646d0026b965ab49cce2486d00000965ab578ce2487c002596ad27338921b44e00259789b549cce2486d0026f965d56ad273386d0025972127338ac2486d002596ad7c545273386d002596ad27378921b425002596ad27378a42486d002596ad27364921b4100025972127338921b4010029d965ab5d8ce2486d002596ad7049d272486d002596d527338921b434002596f9ab49cce2486d002ac965ab49cce2487c002596ad5e4b4ce1b41000259755ab49cce1b46d002596ad27338922186d002596ad273c8ce2b06d002596ad3949cce2486d002596ad9849cce2b06d002a8a1dab49cf233892002597fdab508ce2486d002598bdb549cce2486d00259895ab4f92733892002597fdab5f0921b452002598c9bf6acce2486d00000a51ab49cde2486d002598b1ab4f92733892002596ad353389e2486d002596ad27338a62486d0026f965ab560ce2486d002736ad27338921b407002596ad27450eb33892002597fd27338921b43d0029d965ab49d023386d002596ad9d49cce2486d0025989527338921b419002596ad27338921b444002596ad2739c922086d00287965ab49cd42486d002596ad353389e1b43400259965ab49cce2786d0029f965ab49cce2486d002596ad273389224877002596ad27338ca2486d00259789ab49cce248770029d9ea2c6acce2486d002596ad27410ce1b422002596c527338921b425002596ad27338992086d00000965ab49cde2487c00259755ab5f1273386d002596ad58338921b46d002596ad27338a41b400002598b1ff5f1272486d00000965ff6ad2724873002596ad273c8d92486d0027a965ab5052733892002596ad27338972486d00259811ab49cce2486d002596ad9849cd92486d002596ad27338ac2b06d0025977127338921b45b002596ad3e4f927338920029d9e9ab5f1272486d002596ad5e49ce72486d002b5965ab578ce2486d002596ad27338921dc34002596ad7e49cd42486d002596ad704f92733892002596ad27338921b41a002596ad8f49cce2486d002596ad27338ac1b40100259789ab49cce1b41a002596ad28338921b425002596ad5e49cce2646d000009663c49cce2486d00000965ab49cce2906d0026f965ab49cfb3386d000009ea596ad273ac9200259889ab49cce2486d002596ad27338921b46300259765ab689273386d002a896620660ce2486d0025976dab49cce2486d002a8965ab49cce2906d00279965ab49cce2486d002596ad7c560ce2486d002596ad27338a71b452002596ad27338921b45b002597a9c26ad2733892000009662b49cce2486d00259709ab49cce24825002596ad6b49cce2486d00000965d96ad273386d0026f965ab49cff2086d00259755d56ad273386d0029d9662549cce2486d002596ad273ecce1b46d002596ad273389e1b40400259771dc49cce2486d002596ad27450d42486d002596ad273389e1b43d00289965ab49cce2486d0025992a206acce2486d002816ad35338921b434002596ad27364921b40100281965ab49cce2486d002646ad5e49cce1b41000000965e96ad27338920025977127338921b445002596ad5e484ce2486d002596ad27410ce2786d002696ad27338c52486d0025982dab49ce72486d002596ad27338b124892002597895e49cce1b44a0025977127338921b402002948b1ab49cce2486d002596ad7c578ce2486d00259789ab49cce2c492002597354b49cce248560026f965ab49cde2486d00287965ab4b4ce2486d002596ad27434f23386d00259789ab5f15e3386d0027a9cdab49cce2486d002596ad27420d92486d0025989dab49cce2486d002596ad27338921dc26002598b1ab49cff2486d002596ad27338921b442002696ad27338921b400002596ad3b49cce2486d002596ad30338921b40700000965ab5952733892002596ad27338b1248340026f965ab49ccb2486d0027f965ab49cd42486d002596ad35364ce2486d00259771ab49cce2486d002596ad7c49cfb3386d002b5965a849cce2486d002597c5ab49c921b400002596ad27378921b46d002596ad8c5f1273386d002596e527338921dc25002596ad7e4b4ce2486d002598b1ab49cce2487c00000965ab520ce2486d002596ad27338921b445002596ad273e4ce2486d0029c965ab49cce2486d002596ad27338921b402002a8965ab520ce2486d000009a5ab49cce2486d002596ad4b49ceb33892000009a5e26ad273386d002596ad6649cce2486d00287965b949cce2486d002598b2206acce2486d002a89a5ab49cce2486d002b0965cd49cce2486d002a896dab49cce2486d002816ad27338921b40400000965f16ad272486d002596ad27338921cc1a000009be59771273386d0000096620709ab33892002596adab49cce2486d002596ad27338921b420002596ad3e49cce24807002596ad5e49cce2487a00260965ab49cce2486d002a8965f16ad272486d0026f965b149cce2486d002596ad844f92733892002596ad353c8ce24834002598c5ab49cce2486d002816ad27410ce2486d002596ad7c49cde2486d00259879ab49cce2486d002596ad2d450ce2486d002596ad8a578ce2486d002596ad2749ceb3389200292965ab49cce2d89200000965ff49cf224834002597fde249cce2486d00259965ab508ce2486d002596ad7a49cce2486d00259709bf6ad2733892002596ad27338921cc5b002596ad27338921b422002596c527338921b46d00259789ab49cce1b422002a8a1de249cce2486d002597fd27338921b434002597fdab49ce72486d002596ad7049c921b4100026f965ab49cce24c6d002598957049d142486d0025972127338921b40b002596ad27338921b41c002596ad4c49cce2486d002597fdab49cce2646d002b1965ab49cce2486d0027a965ab49cce23c6d00259789ab49cce1b41c00000965ab49cd92786d002596ad2734cce2486d002596ad2744cce2486d00287991ab49cce2486d0027a965ab4c0ce2486d0026f965c26ad2733892002596ad27338921b43f002596e527450ce2486d002596ad5149cce1b400002596ad4b49cd42486d00285965ab49cce2486d002596c57c49cce2486d002596ad27338921b44f002598cd3b49cce2486d002596ad273c8ce2483d0025972127338bd2486d002596ad273fc922306d00287965b549cce2486d00259709ab49cce2486d00269965ab4c0ce2486d002596ad27338a52486d002596ad583fc922086d002af965b549cce2486d002596ad27338921cc45002596ad42338921b404002596ad5e52d2733810002596ad3449cce2486d002736ad4b338921b4250029d965cd6ad4b33892002596ad27338921cc0200000965ab545273386d00259831ab49cce2486d002596ad273389e2486d002596ad2749cd42486d000009a5ab49cce2487300000965c8508ce2486d002596ad42410ce2486d002596ad7049cf22486d0025972127338ce2486d00259789ab49cce2786d002a8965ab545273386d002596ad6849cce2486d0027a965ab4f92733892002946ad27338921b407002596ad985c1272486d002597c5ef6ad272486d002946ad27338921f06d002596ad273fc921b40700259755ab671273386d002596ad27338b624871002596adab49cce24873002596ad273389e1b434002596ad273ecfb3386d00259935ab5c1272486d002596ad27488ce2486d002596ad27338ac1b40b002596ad8252d272486d002596ad27338921b440002598cdab49cce2486d002597e127338921b45b0026f985ab49cce2486d00259709ab5f12733892002736ad27338921b425002646ad27450ce2486d002596ad27444fb3386d00259755ab49cce1b40000000a05ab49cd92486d002b79662c49cce2486d002596ad27338b62906d002596ad273c8992486d00000965ab4b4d42486d002596e527338921dc6d002596ad27338921f00700266965ab49cce2486d00259839ab49cce2486d0025976dab695273386d002598e5ab49cce2486d00259771d349cce2486d002596ad27338921f07c002596ad27338921cc2200294965ab49cce2906d002596ad27338b42488c00287965ab49cce24877002596ad5e49cd43386d002598b1ab4d4ce2486d002596d527450ce2486d002a1965ab49cce2486d00259809ab49cd42486d00259881ab338921b407002596ad4b4b4ce2486d002596ad27338bd2b06d00000965d56ad273386d002596ad7049c921b401002597fde249c921b4190027f991ab49cce2486d00000965dc560ce2486d002596ad27364921b40b00259735ab49cce2906d002a8965d56ad273386d002596ad58338921b400002816ad27338922486d00000965ab508ce2b06d002596ad2c49cce2486d002597fd272486d0d01900281789ab49cce2486d002596ad27338ce2b06d002596ad86508ce2486d00259755c26ad27338920025974dab49cce2486d002597e127338921b445000009b9ab49cce2486d002597a1ab49cce2486d002596ad2d49cce2486d002597e127338921b402002596ad644ed273386d002816ad27338921b434002596ad4239c921b45b0027a97dab49cce2486d002596ad273c8921b428002596ad27364bd2486d002596e54b49cce2486d00000965ab560ce2486d002596ad27350921b411002598e9d36acce2486d002596ad76338921b45b002949e9ab49cce2486d002596ad273ecce3146d00000965e2578ce1b445002596ad27338921b421002597e1ab49cce2486d002a8965ab560ce2486d00287965ab52d2733892002596ad4149cce2486d002596ad27390ce2486d0029d9661c6acce2486d002596ad27338921b448002596ad27450ce248770027a965ab49cff2486d002696ad27338b62486d002598f9dc49cce2486d002596ad27364ce2486d00000966326acce2486d00287965ab49cce2c492002596ad4b49cce24815002596ad273ecce1b400002596ad27338921c06d00259965ab49ce72486d002597c5ab49cb62486d002596e52749cce2486d002596ad2746cce2486d002596ad27338a42086d002596ad30338921b4250027a965ab49cce2487c0025972127338921b419002596ad273acce2481000259965ab49cce2646d00000991ab49cd42486d0029d965ab4a4ce2486d002b0965ff49cce2486d002596ada049cce2486d00287965ab49cce2485c002596ad27338922146d00269735ab49cce2486d00000965ab568ce2486d002596ad27338c32486d00000965ab49cfb3386d0027a966206acce2486d002ac965ab49cce2486d002598f9ab49cce2486d00259749ab49cce2486d002598f15e49cce2486d00000965ab631273386d002596ad42338922486d002596ad5e49cce2906d002596ad27338921f056002596ad76338921b445002596ad9a49cce2486d002739bdab49cce2486d002646ad4b49cce2486d002a8965ab49cfb3386d00259789ab508ce2486d002597c5cd6ad272486d002596ad273c8ce24834002596ad76338921b4020026f965ab49cce2d86d002596ad27378921b400000009cdab49cf22486d002596ad4749cce2486d002596ad85390ce2486d002596ad42338921b4340027a965ab49cce2d092002596ad3e49cce24825002597fd3549cce2486d002696d5ab49cce2486d002596ad27440f8338920026f965ab649273386d002736ad27338921b46d002596ad27338921dc77002596ad27458ce2486d002596ad4449cce2486d002b5aa1ab49cce2486d002596d54b49cce2486d002596ad2739c921b404002596adab5d8ce2486d002596ad27450ce2c492002596ad27338c42486d0026f965ab49ced33892002646ad2749cce2486d002b2965ab4d4ce2486d0026f969ab49cce2486d00000965ab49cde2486d00000965c849ce72486d002596ad27410e72486d002596ad273c8eb33892002596ad27338991b404002596ad273b8ce32092002596ad9849ceb33892002596ad7649ceb338920029d965ff6ad7c2486d002596ad4749d2133892002596ad35338921b407002a8965ab49cde2486d0026f965ab49cce2486a0029d965c849cce2486d00287965ab5b127338920025989527338921b45b002596ad27338ac1b41900000965ab49ccb2486d002b4965ab52cce2486d002596ad27410ce2646d0027a975ab49cce2486d002596ad273b4ce2486d00000965a849cce2486d002879662a6acce2486d0027a965ab49cf22486d002696ad27338922086d002a89659849cce2486d002596ad655792733892002596ad27350921b410002596d52749cce2486d0027a965ab5d9272486d002596ad5149cce2d86d002596ad5e49cce1b46200000991ab4b4ce2486d002736ad7c49cce2486d002596ad27338921b437002596ad5e4a8ce2486d002596c527338921b400002596ad27338921b46a002597c5ab49c922086d0026f965dc49cce2086d002597fd27338921b436002596ad2737cce2486d00000966316ad2733892002596ad27338921b41f00259929ab49cce2486d002596ad4149d1d33892002696ad5e49cce2486d002b4965ab49cce2486d002596ad273dcce2487c0028e965ab49cce2486d002596ad4b49cce248770028e965e26ad273386d002596ad27338921b465002596ad27364921b419002597c5ab579272486d00259735ab545273386d00000965b149cce2486d002596ad273acce24801002596ad3549cce2786d002596ad27338922246d002598b1dc49cce2486d0026f965ab561273386d00000966496acce2486d0026f965ab5794b3386d0025989527338921b445002a8965b149cce2486d002598b1ab52cce2486d0026f965ab49cce2086d0026f965ab4c0ce2486d00000965ab49ce72b06d0025989527338921b402002596ad343c8ce2486d002596ad8649ce72486d00287965ab49cce2786d002946ad27338921b42500259709ab49cce24800002596ad27338921fc6d0029d965ab49cce2b06d002596ad273c8d42486d002946ad27338a42486d002596ad2749cce24877002597d5ab49cce2486d002596ad9849cd42486d002596ad27441043389200259755ab49cce2d86d0027a965ab49cc22486d002a8a1e597352733892002596ad7049c921b40b0025991dab49cce2486d002596ad273fc921b425002596ad30338921b46d00000965ab52d273509200259895ab49cce2486d00259709ab68927338920026f965ab579273386d002596ad3849cce2486d002598b1ab49cce2486d00271965ab49cce2486d002598d5ab49cce2486d002596ad2d338921b410002596ad5e52cce1b4140027a965ab4d4ce2486d002596ad27338921f025002879bdab49cce2485b002596ad27338a42487c00000965c26ad2733892002596ad5649cce2486d002597e1f849cce2486d002597fdab49cce2906d002596ad27338be2486d00287965ab49cce2486e002596ad9949cce2486d0026f965ab4f92733892002736ad27474ce2486d002a8965c26ad2733892002ae965ab49cce2486d002597adab49cce2486d00259755cd6ad273386d002596ad7049cbd2486d0029d965ab49cd92486d002596ad5149cce2086d002596ad27338921b45400259815ab49cce2486d00000965b849cce2486d002596ad4b49cce2c492002596ad58338b62486d002a8a75cd49cce2486d002a89ea597fd272486d00259881ab338921b425002596cdab49cce2486d002596ad273389220452002816ad3549cce2486d00259819f16ad272486d002596ad35338921b456002596c5ab49cd42486d002596ad7c4c0ce2486d002596ad5e49cce1b414002596ad27338b12c492002596ad3e49cce2486d002596ad27350921b40100000a51ab49cce2487c002596ad4b338992486d002596ad7049cce2486d002596ad27450ce2786d002596ad3d49cce2486d00287a05ab49cce2486d002596e527338921b410002596ad5e545273386d002596ad4e4c0ce2486d002596ad2749cce2c49200000965f849cfb3386d002596ad2739c922486d002596ad4b3c8921b42500000965b949cce24877002598d9c26ad273389200259705ab49cce2486d00259735ab560ce2486d00259789ab49ce72486d00287965ab49cce24867002596ad5049cce2486d002596ad2d3c8ce2486d002596ad2743ce72486d002596ad27338921b417002596ad27338921b44900000965ab49d032486d0026f965ab49d043c86d002596ad984b4ce2486d002596ad514f92733892002bc965ab49cce2486d00259925ef6acce2486d00294965ab578ce2486d002596ad27338992486d002596ad2739c921b43400259789ab49cce2646d002596d530338921b4190029d965ab5c1142486d002596ad7c4f92733892002596ad273ecce2d86d002598c9cd6acce2486d0025973127338921b4620000096625545273386d00259755ab49cce2086d00297965ab49cce2486d002596ad27338991b434002596ad273c8921b4250025977158338922086d002597e1ab5d8ce2486d002697fdab49cce2486d0025981dab49cce2486d002596ad27338a92486d002598b5ab49cce2486d002596ad30338921cc6d0029d9e9ab5f0ce2486d002596ad3549cf233892002596ad4b338921b428002597fdf16ad272486d002596e5273c8ce2486d002646ad27338921b410002598b1ab49cce2487300259755ab579273386d002596e59849cce2486d002816ad27450ce2486d00259735ab49cfb3386d002949bdab49cce2486d002596ad27338921b4320025978927338921b44a002596c5ab4b4ce2486d0025977127338921b407002596ad58560ce2486d00287965ab49cf233892002596ad2d338921b401002596ad27378b62486d0026f965ab49cff2486d002596ad27338922306d002596ad58338922086d002596ad27490ce2486d00259789ab49cce2306d0025972dab6952733892002596ad27338921b468002596d527338921b41000287965ab508ce2486d00000965ab5d8fb3386d00000965ab5052733892002946ad27338921b46d00294965ab49cde2486d002596ad90560ce2486d002596ad27338921c86d002596ad27338921b428002a8a762c6acce2486d0026f965ab49cce2586d0026f965ab49cce2487c002b2965ab49cce2486d002596ad273fc921b46d002596ad4b49cce2481100291a05ab49cce2486d002596ad6949cce2b06d002598a9ab49cce2486d0027c965ab49cce2486d002596ad5e560ce2486d0026f965cc49cce2486d0025978927378ce2486d002596ad27338921b407002596ad273c8ce2483600259735ab49cde2486d0026f966206acce2486d002596ad8449cce2486d002597c5d56ad9849c6d002596ad27338921f06d002596e527338921b401002596ad273389c2486d00287965ab49cce2b092002946ad27484ce2486d002646ad273c8ce2486d002646ad9849cce2486d002596e527338991b425002596ad7049c921b419000009cdab52cce2486d002946ad7c49cce2486d002596ad35338921b425002736ad27338921b400002596ad4b49cce2786d002596ad273ecce2086d002596c527338b62486d00259881ab338921b46d00000991ab52d2733892002596ad27460ce2486d002596ad273acce2480b002596ad7c49cff2486d002a8965cd52d2733892002596ad273b4ce31492002596e527338921b4520029d9e9ab474ce2486d002596c1ab49cce2486d00000965ab51d2733892002739cdab49cce2486d002596d5273c8ce2486d002596ad3c49cce2486d00259965ab49cce2906d002596ad27338921dc10002596ad27338921b412002596d59849cce2486d002597fdab545273386d002596ad42450ce2486d002598b1f849cce2486d002a8965ab51d2733892002597fdab4c1272486d0028d965ab49cce2786d002596ad7c49cce2487c002596ad5e49cfb3386d002596ad7549cce2486d000009cdab49cce2486d002596ad27338b42486d002596ad2749cce2786d00263965ab49cce2486d002596ad6349cce2486d002a89cdab49cce2486d00259735b149cce2486d0027a965dc49cce2486d002596ad273acce2f492002596ad2742cce2486d002596ad27378922086d002646c5ab49cce2486d00259881ab5f0ce2486d002646ad27338921b401002697fdab49c921b419002596ad273fcce2c492002596ad4b49ce32486d002596ad27338921ec6d00259709ab49cce2d89200259931ab49cce2486d0027a965ab49cbd2486d002598d1ab4f9273389200000965ab49ced33892002596ad273acce33892002596ad8b49cce2486d002596ad5749cce2486d0029d965ab5c1272486d002816ad4b49cce2486d002596ad5e49cde2486d002a8969ab49cce2486d00000965ab49cce2486a002596d527338921b4010027a965ab49cce2486d002596ad273c8ce248770027a965ab49cd22486d002596ad27338a41b404002596ad273f4ce2486d002a8965ab49cce2486a002596ad4b49cce24810002596ad9849cce24877002596ad27338921b42e002596ad27350921b40b002597fdd56ad273386d002596ad5e49ccb2486d002596ad27338921cc07002596ad27448ce2c49200259735c26ad273389200259789a549cce2486d002a8a75ff49cce2486d002596ad27410ce2906d002596ad27338b1248100029d9e9ff6ad272486d002596ad7c578ce1b4100028da05ab49cce2486d00259881d56acce2486d002596ad27338b52486d00269965ab49cce2486d002596ad29338921b445002816ad2749cce2486d002598b1ab5d8ce2486d002596ad27338921b4560025b965ab49cce2486d00269965e26ad273386d0025969527338921b434002596c527338922086d002596ad30338921b4000025972127338921b45b00259965f16ad272486d002597fde249c921b420002596ad6e49cce2486d002596ad27350bd2486d00000965de49cce2486d0025981d27390ce2486d0026f965ab49cf83386d002a89661c49cce2486d002597fdab560ce2486d0026f966416ad273386d002596ad27338a02486d00000965ab49cce23c6d002596c55e49cce2486d0026f965ab4d4ce2486d00000965ab4c0ce2486d002596ad27338921dc01002596ad27350ce2486d00000965e26ad303386d0027e965ab49cce2646d002596ad4b49cf233892002a8965ab4c0ce2486d002596ad27338921b40e00000965f76ad272486d002596ad27338991dc25002596ad27380ce2486d002596ad4f49cce2486d002596ad3e49cce2480000287965ab49ce72486d002596ad273c8ce2c492002596ad7c49c921b43000259709ab49cce24882002596ad5e4a0ce2486d002596ad35338921b46d002596ad9849cce2c492002596ad4b508ce2486d002596ad6249cce2786d0025972127338921b445002696ad27338921b404002596ad5e49cce24c6d002597c5f16ad272486d002596ad7149cce2486d0025983dab49cce2486d00000966056ad273389200287965ab49cce2646d002596ad27338921b40d0025972127338921b402002596ad2d338921b40b00259711ab49cce2486d002597fd27338921b467002596ad27338c72486d002696ad27410ce2486d002597c5ab49c921b404002596ad27338ac1b45b002597e127338921b407002597fdab49cfb3386d002598b1ab338921b45200000965ab4f9273389200259709ab5792733892002a8a1dab49cce2485b0027a965ab49cce24873002597c5ab49d042486d002596ad4249cce2486d002596ad273dcce2486d002a8965ab4f92733892002596ad8249cce2486d002596ad6d49cce2486d00259721ab49cce2486d002596ad273acce24819002596ad7249cce2486d002596ad273bc921b467002879bdab49cce2d86d002596ad7c4d4ce2486d002596c5ab52d2733892002596ad27474f22486d0029d965ab4ecce2486d002598962549cce2486d00000965ab52cf224825002597e5ab49cce2486d002596ad2d338bd2486d00259965ab545273386d002598b22549cce2486d0029d9e9ab49cc82486d002a8965e249cce1b41900269965ab49cce24873002596e527338921b42b0025977127338921b425002596ad27338b124801002596e527338921b40b002596ad4b338921b425002a8965ff5f1272486d002596ad27450e72486d00259821ab49cce2486d002596ad27364921b45b002596ad2d338ce2486d002597fdab49cde2486d0025978927338a41b445002596ad27404ce2486d0026f965ab49d043386d002596ad514f927450ce002736e5ab49cce2486d002596ad27450ce2646d002597c5c26ad9849c92002596ad27338ac1b445002596ad6c49cf23389200281965ab49cd92486d002596ad27338ac1b402002597e1273acce2f492002598953e49cce2486d002597a9ab49cce2486d002a8a1d9849cce2486d002596ad273a8ce2486d002596ad273389e1b41000000965ab4c0ce24873002696ad3049cce2486d002ad991ab49cce2486d002596e527338bd2486d00282965ab49cce2486d002596ad27338921b425002598957049cce2486d002596ad27338a42486d002946ad27338921b400002596ad27338921c434002596ad273a4ce2486d00259789ab49cce2906d00000965dc49cff2486d002736ad27338b62486d00265965ab49cce2486d00259819c26ad273389200259931f849cce2486d0027a965f849cbd2486d002596ad76338921b4070027a965ab551273386d002596ad273fc921b400002596ad27338921b438002596adab49cce2b06d0029d965ab49ceb33892002596ad27338a41b434002596e527338ce2486d00259965d56ad273386d002596ad5149cce1b40400259765ab49cce2486d002596ad27350921b419002a89661649cce2486d00259815ef6ad2733892002646ad27338921b40b0027a966166ad272486d0027a965f849cce2486d00000a1e596ad4233892002596ad27338921dc27002596ad27364921b445002596ad27338921f00000000a51ab49cce2486d002596ad5149d043386d00259789cd49cce2483d002596ad27338921b810002597fdb149cce2486d002596ad2733cce2486d002596ad27364921b4020027a965ab49cf22d892002597a5e26ad2733892002596ad27338921f46d00273735ab49cce2486d002a8a51ab49cce2486d00259925ff6acce2486d00000965ab49cff2486d002596ada149cce2486d0026e965ab49cce2486d002596ad6049cce2486d002596ad27338921b42a00259805ab49cce2486d002879bdab49cce2086d00259881ab338921b400002a8965ab49cff2486d002596edab49cce2486d002596d527338921b40b0025977dab49cce2486d002596ad27338991dc6d002596adab49cd92486d002596ad273c8ce2786d00000965ab49cce2487c00259965ab560ce2486d002646ad27338bd2486d002596ad9849cce2786d002596ad27338921b462002816ad27338921b410002a8965ab49cce2487c002816ad27338921b467002597c5d56ad273386d00000965cc49cce2486d002596ad763acce2f492002596ad27338a41b44a002879bdab579273386d002596ad273c8d02486d002596ad9e49cce2486d00000966206acce2486d002597ad27338a92486d002646ad27338ce2486d002596ad273389219c1000259755ab49cce1b404002696ad27338922486d002597fdc26ad2733892002596d527338bd2486d00269789ab49cce2486d00000a76596ad513386d002a8966206acce2486d002596ad273ecf83386d00259931ab5d8ce2486d0027a965ab5d8bd2486d002597fd27364921b4340029d965ab49cd42486d00259755ab49d043386d002596ad273c8ce2486e002596ad273f0ce2486d002597c5ab49c922486d0026f965dc49cce2486d002597c5e26ad272486d002696ad27338921b43400264965ab49cd42486d00000965ab49cce2d0920029d9e9ab49d042486d00259921ab49cce2486d002736ad27338922086d002596fdab49cce2486d002596d527338ce2486d002596ad5b338922306d002596ad4b49ce72486d002596ad2d338921b419002a4965ff6ad272486d0027a965ab5d8ce2486d002596d9ab49cce2486d002596ad27338921cc250026f965e249cce1b445002596ad30338b62486d002597c5ab49c921b434002596ad27378ce2906d00259965ab49cfb3386d0025989527338921b407002596ad27338921dc0b002596ad273389e1b401002596ad4b49cce2646d0025977127338921b46d002598b1cd6ad4b33892002596ad58338921b404002596ad2f49cce2486d002816ad273c8ce2486d00273965ab49cf22486d002598da206acce2486d002736ad5e49cce2486d002596ad27420ce2786d002816ad9849cce2486d0026f965ab49cce2486d002596ad58410ce2486d002596ad2749ce72486d002b5965ab49cce2486d0026f965e26ad273386d00259755c26ad9849cce002596ad273c8ce24867002596ad2739c921b45c002596ad27338921b41600290965ab49cce2487700259735ab4c0ce2486d002596ad27360ce2486d002a8975ab49cce2486d002596ad27338bd24877002596ad273649e2486d002596ad2749cce2646d002596e527338921b419002796ad27338921b430002596ad42338921b410002596ad3e49cce2d892002596ad27338921b46d00259965ab49cde2486d002599221c6ad272486d00000965ff49cce2786d002597717c49cce2486d002596ad27338921b451002596ad273649e1b434002596ad27338ce24877002596ad27338921b414002596ad273389216c3d00259821f849cce2486d0029d965ab4b4ce2486d002596ad273ecce1b404002596d5ab4c0ce2486d00272965ab49cce2486d002596ad27338b02486d00264965ab4b4ce2486d002816ad27338921b401002596ad27410fb3386d002596ad5149cce2486d002597b9ab49cce2486d002596ad27338b12480b002596ad835b5273389200259735ab4f92733892002596ad27484ce2486d00259789ab545273386d002596ad7049c921b45b002596ad7c49cce2486d002596ad35338921b400002597e127338921b425002596ad7c49cd22486d00259881f16ad272486d0029da1e596ad4b338920025984dab49cce2486d002596ad5149cce1b434002596ad273c8b624825002a5965ab5f0ce2486d00259789cd49cce1b419002596ad30338922086d0027a9662549cce2486d002598b14b338921b456002646ad27338921b419002596ad423c8ce2486d002596ad4e49cce2486d00259965b149cce2486d002596ad27378921b404002596ad98508ce2486d0029d965b949cce2486d002596ad27338921b439002596ad27338bd2c492002596ad765b4ce2486d002596ad27480ce2486d00000a1e596ad2739c9200000965b949cce2646d00000a05ff49cce2486d00000965ab4d4ce2486d002596ad27410de2486d002596ad27338921b4660027a965ab56cce2486d002a8965ab4d4ce2486d002596ad5e4c0ce2486d002816ad27364921b434002596d527338921b41900259899ab49cce2486d002596ad27338ce2c49200259789b549cce1b419002598b127338921b4560026f965ab49cce24873002a76ad27338921b456002596ad7049c921b44500259755ab49cce2486d0029c6ad27338921b45200259789d56ad273386d00259799ab49cce2486d002596ad5f49cce2486d002946ad27338b62486d002596ad4b474ce2486d002596ad7049c921b402002596ad3e49cce248820029e965ab49cce2486d00287965ab49cce24871002a8a75e249cce2486d00259961ab49cce2486d002596ad273fcb62486d002596ad42338ac2486d002598edd56ad273386d002596ad27338921cc6d00259965c26ad273389200259755ab49cce1b43400000a1e6f6ad27338b6002596ad27364d92486d00294a51ab49cce2486d002596ad8a49cce2486d00259789ab49cce1cc6d00287965ab49cce2906d002596ad42338921b4010029d965ab458ce2486d002596adab5c1272486d002596ad76338921b425002596c527338921b404002596ad27338b62586d00259751ab49cce2486d0029d991ab49cce2486d002737fdab49cce2486d002596ad5e4f92733892002596ad27338b62487c002596c527338921b43d002596ad2735cce2486d002596ad27474ce2486d002596b9ab49cce2486d00294735ab49cce2486d002596ad58338922486d002596c527410ce2486d00264991ab49cce2486d00259789ab560ce2486d00287965d96ad273386d00294965ab49cce2487c002597895e338921b44500259735ab49cff2486d00000965be49cce2486d002596ad27338921dc19002596ad27338b92487700259881ab338b62486d00296965ab49cce2486d00000a05ab49cce2786d0029d965b549cce2486d002596ad7c49cce24873002598b9ab4b4ce2486d002596ad58338921b4340029d9e9ab578ce2486d002597edab49cce2486d002596ad273c8d924834002596b5ab49cce2486d00000966254f9273389200259735ab49cce2487c002597c5c26ad2733892002596ad4e49cce24873002a8a75ab484ce2486d00259771273fc922086d002596ad27338921b42c00261965ab49cce2486d00259709ab49cce24804002598b1c849cce2486d002598d5c849cce2486d002596ad27434e43386d0026f965f849cce2486d002596ad5e49d043c86d002a8a75ab5f0ce2486d00259881cd6acce2486d0029d965fc49cce2486d0025978dab49cce2486d002596ad27450ce2906d002596ad273389e1b40b00259709ab49d0433892002a89659d49cce2486d002596ad273bcce2486d002596e5ab49cf22486d002596ad273ecce2486d002596ad27338921b43500259789ab49cfb3386d002596ad8c49cce2486d002596d527338921cc19002596ad2739c921b410002596ad27444ce2486d002598d1ab49cce2486d002946ad27338922086d002879a5ab49cce2486d00259881d56ad273386d002596ad8d53d272486d002597e127338921b46d00262965ab49cce2486d002596ad5849cff2486d002af9a5ab49cce2486d002596ad273ecce1b4340025978927378921b445002596ad5149d173386d002596ad273fc922086d002596ad27338991b41000292965ab52d273389200000965ab5c15149c6d002596ad27454ce2486d00287965f16ad272486d002596ad4b3c8ce248270029d965ab49cce24877002596ad2e49cce2486d002596f1ab49cce2486d002596ad27338bd2786d002596ad27338b124819002596ad9049cff2486d00000965ab49cce26477002596ad27338921b40f002596ad27338921cc7300000965ab49cf23389e00259725ab49cce2486d002596ad5e49d041b430002946ad5e49cce2486d0029d966256acce2486d0029d9be596ad5e3386d002596ad27338922087c0025989527338921b4250029d9662c6acce2486d002596ad27378922486d002597fdab4c0ce2486d002597b5ab49cce2486d002596ad273acce2485b00259789ab49cde2486d002596ad5e49cff2486d002596ad27338ce2786d002736ad27338c82486d002596bd27338921b445002596ad8e545273386d002597e17c49cce2486d002596ad273eceb3386d00259881ab338922086d00259769ab49cce2486d002598b1ab49cce2b06d002596ad8349cce2486d002596ad27378921b434002596ad5e49cce2586d002596ad5e49cce2487c002596ad5e52cce24812002816ad27338921b40b0025977127338921b4000029d965db6ad273386d002596ad273c8e72486d002596ad27340ce2486d0026f965ab5d8ce2486d002596ad273389b2486d002596ad9849ce72486d002596ad273388c1b41000259741ab49cce2486d00259815ff6ad2733892002696ad27450ce2486d002596bdab49cce2486d0029d965ab4f8ce2486d002596ad9249c921b430002596ad273c8ce2646d00259881ab578ce2486d0029d965ab5c0ce2486d002596ad9849cce2646d002596ad27338c52486d002597fdab4f9273389200259789ab49cce3146d0027a965ab5f15e2486d00273965ab52cce2486d002597c5ab49d142486d002596ad9c49cce2486d002596ad5e378ce2486d0025968927338921b445002596ad76338921b46d002598c1ab49cce2486d00000965dc49cce2486d00264965ab52d27338920029d965ab49cce2c492002596ad835f12733892002816ad27338bd2486d002596ad273acce24845002598b1ab49cd92486d002596ad27338921b400002596c527338922486d002596ad2738cce2486d00000a05ab49cf233892002a8965dc49cce2486d00259789b149cce2486d002596ad273acce24802002596ad273f8ce2486d002596ad35338b62486d002597fde249cce1b419002596ad4b49cce24871002596ad2739cac2486d00287965ab545273386d002596ad27338921b455002596ada249cce2486d002816ad27338ce2486d002596c527338921b43400273965ab49cce2486d002596ad27350921b45b002b7a75ab49cce2486d002596ad5449d1d3386d00287965e27352733892002596ad2739c921b401002596ad27338991b430002596adab49ceb338920025978927338921b447002596ad4b49cce2906d002596ad27338921b41e0027a9bdab5f1272486d002596ad7c5d8ce2486d00000965ab49cce2486d00259789ab49cce1b41e002596ad27338932486d0025978927338921b45200259881f16ad982486d002a8a75a549cce2486d002879bdab49d043386d00000aa2597c5272486d00259789ab49cce24c6d002596ad27338991b401002a8965ab49cce2486d00259735ab4d4ce2486d0025972127338921b407002598e61c6ad273386d00259709ab49cce24892002596ad42338921b40b0025a965ab49cce2486d000009663a6acce2486d002596ad27378de2486d002596ad27338ac2a46d00259789c26ad2733892002596ad27338ad2486d002596ad2749cce2906d002596ad27338921bc6d0027a965ff789272486d00259709ab49cce24834002b9965ab49cce2486d0026f9662549cce2486d0025986dab49cce2486d002597fdab4c0921b41900287965d56ad273386d0027a965ff49c921b434002596ad27350921b445002596ad5149d143386d002736ad27338921b404002598d9ab49cce2486d002596ad273389e1b419002596ad27350921b40200259741ab49cce24873002596ad42338bd2486d002947fdab49cce2486d002596ad273c8ce2d82200000965ab614ce2486d002596ad27468ce2486d002736ad27410ce2486d002596ad4b4a8ce2486d0025989527338921b46d002bd965ab49cce2486d0027a965ab49d132486d002597fdab49cff2486d002597e1273ecce2486d002879bdab49cce2486200259735ab52cce24825002596ad273389220c6d002596ada5578ce2486d002596adab49cd42486d002596ad2d338921b45b002596ad42338ce2486d002596ad35338922086d002596ad7c338921b452002696ad4b49cce2486d002596ad27338921cc00002596b1ab49cce2486d002596ad824ed272486d002596ad27338ac1b407002597fdab49cce2487c002a8965c249cce2486d00287965ab560ce2486d0025977d27338922306d002a9965ab49cce2486d002a4965ab578ce2486d002597c5ab52d272486d002596ad2a49cce2486d00259965ab4c0ce2486d002598955149cce2486d002596ad34338921b422002596ad27338b51b4670025989527484ce2486d0025987dab49cce2486d002596ad27338921b43a002596ad4849cce2486d002a59e9ab49cce2486d002596ad27338921e830002a89660c49cce2486d002596ad27350921b422002596ad5e4d4ce2486d00259881ff6acce2486d002596ad2b49cce2486d002598957c49cce2486d0027a9660c6ad272486d002597bdab49cce2486d0027a965c849cce2486d002596ad27338921b42900000965ab49cce24873002696ad2749cce2486d00259755ab49d143386d00000965e26ad2733873002596ad27338921b43b000009663349cce2486d002b7965ab5f1272486d0029d965ab49cce2786d002a8965ab49cce24873002596e527338921b45b002816ad27338921b419000009ea6f6ad274106d002597c5ab49d272486d002596ad27338921b464002596ad27438ce2486d002596ad27364921b407002596c55e49cce1b41000259881c26ad2733892002596ad27338922106d002596ad2d338921b44500287965ab49cce2485b002596ad27338921b409002596ad27338921b453002596ad2d338921b40200287965ab568ce2486d00259965ab4f9273389200287965ab49cfb3386d0026f965ab49cce2c46d002596ad763ecce2486d0025e965ab49cce2486d002598f5ab545273386d002596ad58450ce2486d002596ad30338921b40400259881d56ad983386d0026c965ab49cce2486d002596adab4b4ce2486d00000aa259755273386d002879bdab49cce2486d002596ad5e52d043386d002879bde26ad273386d002597fdab49cf22486d00259811bf6ad272486d002596ad30410ce2486d002596ad804d4ce2486d00283965ab49cce2486d00287965ab4ed27338920029d965ab52cce24810002597e127338921b400002596e5ab52cce2486d002596f95e49cce2486d002596e527338921b4450027a965ab49cce2b06d002a8965d349cce2486d002596e527338921b402002646ad27338921b45b00000965ab551273386d00287965ab49cde2486d00259895ab5c1272486d002596ad5152d273386d002596ad5e49cce1b43d0025977127338b62486d0029da05ab49cce2486d002598b1ab5c1272486d00259789cd52d2733892002596ad5e49d043386d002597e1ab49ceb338920025978927338b61b44500000965f849cce2486d002596ad3e49cce24804002596ad273ace43389200287965a849cce2486d002596e5ab49cce2486d002596ad5e338a41b445002b39cdab49cce2486d002596d527338921b45b002596ad27450fb3386d002596ad42338921b419002a8965f849cce2486d0025972127338ac1b45b002597fdab49c921b430002596ad8849cce2486d002596ad3e49d04338920027a965f86ad272486d002596ad5149d273386d0027a965ab49ce42486d002596ad2739c921b40b002736ad27338922486d0027a965df49cce2486d002597214249cce2486d002596ad273fcf82486d00273789ab49cce2486d00259771cd49cce2486d00259721c849cce2486d002596ad27338b62486d0027a965ab49cd92486d00000965ab591273386d0026f965ab5b1273386d002596ad704f9272486d00259789ab49cce2d86d0025f965ab49cce2486d002596ad705c1272486d0029d965ab52cf2338920027a9bdab49cc52486d002596ad27338991b40b002b7965ab490ce2486d002736ad27338921b434002646ad27338921b44500294965ab49cce2486d0029d965ab53cce2486d002b5965cd6ad2733892002596ad9249cce2486d002596ad304c0ce2486d00000965ab49cfb3acce002596ad27338a41b410002646ad27338921b40200287965b149cce2486d00259755ab52d273386d00000965ab60d273389200259965ab49cff2486d00268965ab49cce2486d002596ad27450de2486d002596ad76338921b400002596ad2739cbd2486d002596ad2d49cd42486d002597fdab4d4ce2486d002596c527338921b415000009ea596ad273ec6d00259735ab49cce2486d002598d22549cce2486d002596d527338921b445002646adab49cce2486d002596ad27338bd2646d00259789ab49cce2486a00259965ab49cce2487c002696ad30338921b4190027a965ab49cf22483400287965ab49d1333892002596d527338921b40200000a76596ad3e33892002596ad27338921dc5b00000965ab508e72486d002596ad27378a41b445002596ad2739cce2486d0025983dd36ad272486d000009a5b549cce2486d002596ad9f49cce2486d0029d965ab508ce2486d00259755ab49d273386d0029d965ab5b4ce2486d002596ad273c8c82486d00000965ab49cdc2486d00000965ab5d8ce2486d0025972127338921b425002597715849cce2486d00259966206acce2486d002596ad27338ce2646d002596ad27338aa2486d002596ad5852cce2486d0025977127338922086d002a8965ab5d8ce2486d002596d5ab49cce2486d002596d527338921b420002596ad4249cce2b06d00287965c26ad273389200259721ab49cce2b06d002596ad58338b12486d002946ad27338921b404002a1965ab4b4ce2486d0027b965ab49cce2486d002596ad7849cce2486d002596ad273c8ce2906d00259841f16ad272486d002596ad9849cce2906d002597e1ef49cce2486d002879660c6ad2733892002596c527450ce2486d002596ad273fc921b404002596ad27338891b419002946ad27410ce2486d002597715e49cce2486d002596ad48338921b46700000965ab49d023386d0029d965cb6ad2733892002596ad5849cce2486d002597f1ab49cce2486d002596ad273389223c6d002596ad5e52cce2486d002596ad27410ff2486d002736e527338921b42500259789ab5794b3386d002596ad27338922086d002596ad27338921dc45002596ad30338922486d002596ad9b49cce2486d002696ad27338921b410002597895e49cce1b4450025992dab49cce2486d00259789ab4c0ce2486d002596ad27338921f004002596ad27338921dc02002596ad27338b624873002596ad9049cce2486d00259881f16acce2486d002596ad2d4b4ce2486d0026f965ab49cff3386d002597c5ab49c921b4100026f965ab578ce1b445002598c9ab49cce2486d002596ad27410ce2487c002596ad4b49cfb3386d002596ad30338921b434002596ad27338b12485b002596ad27338c62486d002596ad3249cce2486d0025d965ab49cce2486d002596ad7049c921b40700259881ab338921b404002596ad6b49cce2c492002596ad5e49cce2486d002596ad27338ac1b425002596ad845c1272486d00287965ab49d032486d002596adab49cce2487700259789ab579273386d0025989527338921b40000287985ab49cce2486d002597fdab49cf224835002598bdab4c0ce2486d00259881ab410ce2486d00259709ab49d1433892002596ad27338a41b401002a89662c52cce2486d00259735ab49cce24873002596ad3e49cce24892002596ad5a49cce2486d002596ad2749cfb3386d002596ad7b49cce2486d00259789ab4f92733892000009662549cce2486d002596ad4b49cde2486d00259721bf49cce2486d002696ad273c8ce2486d002596ad3e49cce24834002598b1ab49ceb3389200259771ab49cce2c492002696ad9849cce2486d002596ad273389f2486d00000a9dab49cce2486d002a89662549cce2486d002596ad27364921b425002596ad27338b124845002597c5ab49cf22486d002a89662c49cce2486d002596ad273acce2f892002596d5ab49cce24873002597fde25f1272486d002596a14b49cce2486d002597c5ab661272486d002596ad27338b124802002596ad2739c921b4190025982dab49cce2486d00259881c26ad983389200000965ab56cce2486d00000aa259709273389200000965eb49cce2486d002a1991ab49cce2486d002597d1ab49cce2486d0026f965c849cce2486d002597fd7c49c921b434002596ad27338ac1b462002596ad2749cde2486d0027a965ab49cbe2486d002596ad7c4a4ce2486d002596ad8049cce2486d002596ad27338991b419002596ad27338b92646d00287965ab49ce433892002596ad27410f22486d002bb965ab49cce2486d00000965b149cd42486d00259819ab49cce2486d002597e127338b62486d002596ad27338921b45d002596adab49cce2c492002596ad5149cce1b410002596ad27338a81b456002598955149d143386d002596ad27338922087300281965ff49cce2486d00259965ab4d4ce2486d002596ad27338a32486d0025972127338921b46d002596ad273c8920d025002a5965ab49ccb2486d002596ad27374ce2486d002646ad2d49cce2486d002596ad4b49cce248220029478927338921b445002696ad27338921b4010027a965ab5c1272486d002596c54b49cce2486d002b0965ab49cce2d86d002596ad69508ce2486d00259749b949cce2486d00000965ab635272486d002597c5ab49c921b401002597e1cd49cce2486d00259841d56ad273386d002596ad5e49cce24873000009be596ad27338b1002598b1ab49cd42486d0027e9cdab49cce2486d002597fddc49cce2486d002596ad2d350921b410002596ad27410921b430002946ad27338922486d002598b1ac49cce2486d002736ad27338921dc2500294789ab49cce2486d0029d965ab49ce72486d0025978927338921f045002879be596ad27338b6002596c52749cce2486d002596ad273fc922486d002597217c49cce2486d00000965f85d8ce2486d00259925ab49cce2486d00259789ab49cff2486d002b0965ab49cce2486a0026f965ab49cce2506d002946ad27338921b43400259939ab49cce2486d0026f965ab49cce2b06d000009660749cce2486d0029d965ab49cce2646d002a8a75ab578ce2486d002596ad885d8ce2486d002596ad5149cf23386d002879cdab49cce2486d00259755ab49cce1b410002596ad27338962486d002596ad583fcce2486d00259709ab52d2733892002596ad98545273386d002596ad273389e1b45b002596ad273fc921b434002596ad27338922487c002596ad35338921b404002597b1dc49cce2486d002596ad2849cce2486d00259789ab49cce2487c002597fdab49cce2486d002596ad76338b62486d00000965b14b4ce2486d002596ad27338ac1b46d00259831ab52d2733892002596ad35410ce2486d00281965ab49cce2786d002a8a1dab49cce2486d002596ad27338921f034002596ad27338921b44100259881ab338922486d00259881e26acce2486d002879ea596ad273c8920029d965ab544ce2486d002597e127338922086d002b6965ab49cce2486d00259709ab49d27338920029d965ab484ce2486d00259809b149cce2486d00000aa29d8b0ce2486d0026f965ab49cd92486d002598ee206acce2486d00259881ab338921b434002596ad58338921b4100029d965ab5f0ce2486d00259759ab49cce2486d002597b1ab49cce2486d00259735ab5d8ce2486d00000966046ad272486d002596ad273acce24807002596ad27338921b42f00000965ab5c13e49c92002598b1ab4b4ce2486d002596ad5149cce1b401002596ad7c49cce2b06d00259791ab49cce2486d
  | 7 => 0x259755ab661273386d9be596ad27338922486d965ab57927338b62486d9be59789ab49cce2486d965cd6ad27338922086d9be596ad27338921b434965ab6495e49cce2486d965ab49cce248921b46d965e26ad27338921b46d965ab49cce2486d16c0b9ea596ad27450ce2486d002596ad27338921b40c965ab49cf2390ce2486d965ff7bdab49cce2486d965cd6ad5e49cce2486d965ab49cce2486d1b434002596ad27338c82486d965ee789ab49cce2486d965ab5f127338922486d965ab49cce2f4921b45b002597fdab49c921b419965e26ad7c49cce2486d965ab52d27338921b407965ab56127338922086d965ab49cce248822086d965ab5f127338921b434002596ad42338921b45b965ab49cce338921b45b965ab49cce2486d1140b965ab49d04338921b40f002596ad273e0ce2486d00259905ab49cce2486d965ab49cce2486d02c02965ab49d27338921b407965ab57927338922086d965ab49cd0338921b404002596ad35338921b43400259965ab49cce2486d965ab6ad27338921b40b002596c527338921b410965ab49cce2f4921b445a027a965ab49cce2486daa259965ab49cce2486d965af6ad27338921b404965ab49cce2f4921b402965ab5795e49cce2486d002596ad3e49d1433892a1e596ad27338921b425965ab49cce338921b445965ab49cce338921b402965ab49cce2486d01000965ab6ad27338bd2486d965ff6ad27338b62486d9662c6ad27338921b410002596ad27338921b40a002597c5ab49cce2486d965ab6ad27338ce2486d9ea596ad4b49cce2486d002596ad27338921b4049be596ad2745cce2486d002596ad27338921b43daa2596ad27338921b40400000965c849cce2486d002596ad27410ce2486d965ff735ab49cce2486d965ab52d27338921b456aa2596ad27410ce2486d9ea596ad2749cce2486d965ab49d14338921b4259ea596ad27338921b45c965ab49cce2486d16c199662c6ad273c8ce2486dac26f965ab49cce2486d9662c6ad9849cce2486d00259709ab6612733892965ff6ad27338922086d00000965ab49cce2b06d002596ad3049cce2486d965ab49cce2486d11419a1e6f965ab49cce2486d965ab49cce248771b425ad687965ab49cce2486d002596ad2739c921b45b9662c6ad27338921b401965ab49cce2486d06402965ff6ad5e49cce2486d002696ad27338921b419a76596ad27338921b45b965cd6ad27338921b40ca1e596ad27338921b46d965ab6ad27338921b41900000965ab49cd92486da92596ad7c49cce2486d965ab49cce2486d040070025978927338921b445002598b1ff49cce2486d0029d9e9ab49cce2486d965ab49cce2486d0d000966596ad27338b62486da1e596ad7c49cce2486d965ab52d27338921b4259be596ad27450ce2486da76596ad27338921b445002596ad27338922486da76596ad27338921b40200259789ab49cce2486d965f86ad27338bd2486daa2596ad27338922486daa259789ab49cce2486d002596ad27338921b434965ab49d14338921b46da76596adab49cce2486daa2596ad27338921b434965ab49d27338921b42596659735ab49cce2486d965ab49cf2338921b407965ab66127338921b407002596ad273ecce2f46d965ab54527450ce2486d002598ddab49cce2486d002596ad273acce2486d965ab49cce2d8921b404965ab5f127450ce2486d965ab49d04338b62486d9ea596ad27338921b4109664e7fdab49cce2486d002596ad27338921b44aa026f965ab49cce2486d965ab64927410ce2486d002596ad27338921b426965ff7fdab49cce2486d965cd6ad27338921b404965ab49cce2486d01c01966596ad27338922086d966416ad5e49cce2486d965cd6ad27410ce2486d002596e527338921b42500259881ab49cce2486d0027a965ab5f1272486d002596ad27378ce2486d966596ad5e49cce2486d9be596ad4b49cce2486d9ea596ad273c8ce2486d965ab49cd4338921b410ad6596ad4b49cce2486d9ea596ad9849cce2486d965ab52d27338921b46d002596ad5e49cce1b410965ab49cce248821b4049662c6ad27338921b42b9662c6ad27338921b40b9be596ad2749cce2486d965ab49d04338922086d965ab52d27338921b414a966f965ab49cce2486d002596ad2745cce2486d976596ad27338921b40400000965ab5c1272486d965ab57927338921b404965ab49d27338921b46d9ea596ad27338921b4019662c6ad27338bd2486d965ab57927410ce2486d965ab5f14b49cce2486d9662c6ad27338ce2486d002b0965ab49cce2486d965ab49cce2d8922486d002596ada549cce2486d965ab5f12749cce2486d965e26ad27338b62486dac2a8965ab49cce2486d965ab49cce2d8921b434965ab49cce2486d09410002a4965ab49cce2486d0029d965ab578ce2486d002596ad27338921dc25002596ad3549cce2486d965cd6ad27338922486da1e596ada249cce2486d965e2735ab49cce2486d965ab6294b49cce2486d9662c871ab49cce2486da76596ad27338922146d966597fdab49cce2486d00287965ab49cce2486d965cd6ad27338921b434aa287965ab49cce2486d002596ad27338921b415965ab49cf2338921b425965ab66127338921b425002596ad27338921b436965ab49d14338921b40096637735ab49cce2486d965ab49cce2486d02c07965ab49cce2486d16c5b965ab49cce248922086d965e26ad27338922086d965ff6ad27338921b404002596ad27450ce2486d965ab49cce248821b434965ff6ad27410ce2486d9662c6ad27338921b419aa2596ad27450ce2486d965ab49cce2f4921b407965ab57927338922486d965e26ad5e49cce2486d002596ad27338a41b445ad29d965ab49cce2486d965ab49cce2486d09401965ab57927338921b434965ab49cce338921b407965ab49cd2338921b407965ab49cce2486d16c4500000965ab49ceb338929be596ad27338921b410965ab49cce2486d16c0200259881ab660ce2486d965ab49cce2486d1b410965ab6ad27338921b45b002596ad27338921dc6d9ea596ad27338921b40ba76598b1ab49cce2486d965ab57927338921b44a00280965ab49cce2486d965ab49cce2486d11445965ab49cce2486d114029be596ad273c8ce2486d965ab5f127338921b410965ab49cce2486d008029be596ad9849cce2486d9ea596ad27338bd2486d00000965ab49cd42486d96659965ab49cce2486d965ab4a527338921b407965ab6ad27338921b445965ab49cf2338921b46d965ab6ad27338921b402965ab66127338921b46d9ea596ad27338ce2486d002596ad4b49cce2486daa2596ad4b49cce2486d002596ad27338b12486d965ab6adab49cce2486d9be596ad27338921b401a1e596ad27338b62486d965ab5f1273c8ce2486d965ab49d043e0ce2486d965ff6ad27338922486d965ab49cce2486d06407965ab6617c49cce2486d965ff789ab49cce2486d002596ad2749cce2486d002596ad27338921b45caa2596ad2749cce2486d966596ad27338921b404002a5965ab49cce2486d965ab49cce2486d1b401965ff6ad27338921b434966596ad27410ce2486da1e59735ab49cce2486d00000965ab4b4ce2486d965cd6ad27338921b415965d56ad9849cce2486d965ab5f127338921b401965ab49d14338b62486d002596ad6c49cce2486da76596ad27338921b407965ab629273c8ce2486d965ab49cce2486d0100400000965b949cce2486d965ab49cce2486d0940b965ab49d04338921b404a1e596ad27338922086d965cd6ad27450ce2486da4a7a965ab49cce2486d9ea596ad27338921b419965ab49d04410ce2486d002596ad27338921b411965ab49cce2f4921b425a1e596ad5e49cce2486d9a6596ad27338921b419965ab49cce338921b425002a8a75ab49cce2486d00000991ab49cce2486d002a8965cd49cce2486d002596ad30338921b419965ab49d14338922086d96641789ab49cce2486d00000965b549cce2486da767a965ab49cce2486d002596ad27338921b86d002596ad273fcce2486d002596ad5e338921b445966596ad27338922486d96659789ab49cce2486d965ab57927450ce2486d965ab49cce2486d04000965ab52d27338b62486d966596ad27338921b434002596ad27338921b4109be596ad27338921b40b002596ad27338921b4670025989527450ce2486daa2596ad27338921b410965ab49d27338b62486daa2596ad27338921b46700000965ab49cce24877965cd6ad4b49cce2486d965ab49cce2486d1b40b002596ad27378921b445965ab49cce248921b404965e26ad27338921b4049be596ad27338bd2486d965e26ad27338921b43d965ab66127338921b400965ab49d04338922486d965e26ad27410ce2486d965cd6ad2749cce2486d965ab49cce2486d0d004965ab49cce2486d094199be596ad27338ce2486da1e597fdab49cce2486d965ab49d04338921b434965ab49cce2f4921b46d002596ad273c8ce2486d965ab5f127338921b40b002596ad9849cce2486d002596ad7649cce2486daa2596ad273c8ce2486d9662c6ad27338921b45b965ab5b127338b62486daa2596ad9849cce2486d965ab49cce338921b46d965ab52d27338922086d00000965ab49cce2c492965ab49cce2c4922086d965ab49cce2486d00400965ab5f127338bd2486d00287965ab49cce2d892965ab5794b49cce2486d002596ad27338921b430002596ad27338942486d965ab49d27338922086d002596ad27338ac2486d002596c5ab49cce2486d965ab5f127338ce2486d002596ad27338921b401a76596ad27338921b425965ab49cce24c921b401965ff6ad27450ce2486daa2596ad27338921b401002596ad27338991b4259662c6ad27338921b445002596ad27338c22486d00287965cd6ad27338929662c6ad27338921b402965ab5792749cce2486daa2596ad27338c22486d002596ad27338921b44796a596ad27338921b401002596ad27338921b452ade7a965ab49cce2486da96596ad5e49cce2486d9662c6adab49cce2486d002a8965ff49cce2486d002596ad27364921b4340027a965ff6ad272486d965ab49cf2338921b43b9be596ad27338921b419965ab49cce248922486d986596ad27338921b40b965e26ad27338922486d965ab5b15e49cce2486d965ac6ad27338921b401965e2789ab49cce2486d965ab49cce2486d1b419965ab49cce248921b434965e26ad27338921b434965ab49cce2d8921b410965ab49cce2486d16c07965ab49cce2486d0d03400000965ab49cce2786da1e59965ab49cce2486d965ab49cfb338bd2486d965ab5f127338921b403965ab5f127338921b419a766f965ab49cce2486d965ff6ad4b49cce2486d965cd6ad27338921b410ad69d965ab49cce2486d002596ad27338921b4279ea596ad9d49cce2486da76596ad27338921b46d965ab49cce2486d11407965ab49cff338922086d965ab49cf2338b62486d965ff6ad2749cce2486d965ab66127338b62486d965ab49cce2486d01c02965ab49cce2487c1b445a1e596ad27338921b404966596ad27450ce2486d00000a05ab49cce2486d965ab6ad27338921b407a1e596ad27410ce2486d965ab49cce2486d02c00a76596ad7c49cce2486d965cd6ad273c8ce2486d965ab49cce248731b419965cd6ad9849cce2486d965ab49cce248821b4109ea596ad27338921b45b00259735ab52d2733892002596ad27338921b42b965ab49cce2d8921b401002596ad27338921b40b965ab49cce2f4921b400965ab57927338921b410aa2596ad27338921b40b965ab49d14338921b404965cd6ad27338921b401002596ad27338bd2486d965ab49d14410ce2486d9ea596ad27338921b445965ab49cf2338922086daa2596ad27338bd2486d9ea596ad27338921b402965ab66127338922086d00000965ab508ce2486d965cd6ad27338921b447002596ad27338ce2486d002596ad27348ce2486daa2596ad27338ce2486d002596ad27338b1248829ea596adab49cce2486d965ab579273c8ce2486d96e596ad27338921b402965ab6615e49cce2486dac259789ab49cce2486d0027a965ab49d042486d0029d965ab450ce2486d965ab4a927338921b40b965ab50927338921b45b966596ad4b49cce2486d965c86ad27338921b45b965ab49cce248821b40100259871ab49cce2486d965ab57927338921b430a02596ad27410ce2486da1e596ad27338922486d965ab4d527338921b434965ab57927338921b401966596ad2749cce2486da1e59789ab49cce2486d002596ad2949cce2486da1e596ad27338921b434ad2598b1ab49cce2486d965ab49cce2486d16c25965ab52d27338921b404965ab49cce2486d06400965ff6ad27338921b410965ab52d27410ce2486d965ab5f127338921b44b002596ad27338921b40300292965ab49cce2486d002596ad27338921b419965ab49d27338921b40400259789ab49cce1b419965ab49d14338922486d965e26ad27450ce2486daa2596ad27338921b419002597fdab5f1272486d965ab49d27410ce2486d9662c8b1ab49cce2486d965ab49d14338921b434965ab49cce2486d11425965ab49cce290921b445965ab49cce2486d09402965ff6ad273c8ce2486d965ff6ad9849cce2486d965ab49cce2d8921b40b0029d965ab52cce2486d002597e127338bd2486d965ab6ad27338921b425002946ad27338921b445002a8965e249cce2486d00000965ab49ce72486d965ab49ccf338921b40200259859ab49cce2486d0029d965ab49cce2486d965ab49cce2f4b62486d965cd6ad27338921b40b002596ad273c8ce2d89200000965ab49cce2646daa29d965ab49cce2486d00264965ab49cce2486d002596ad27338921f045965ab4a127338921b401965ff6ad27338921b401965ab49cce338b62486d002596ad27338921c46d9be596ad27338921b45b965cd6ad27338bd2486d002596ad27338921cc19965ab49d04338921b411965ff6ad27338921b452965ab49cce2486d1b45b965cd6ad27338ce2486d002596ad76338bd2486d965ab49cce248821b40b965ab52d27338922486d965e26ad4b49cce2486d0027a9bdab49cce2486d966596ad27338921b410965ab52d27338921b4349be596ad27338921b4459be596ad27338921b402965ab57927338921b40b965ab5f127338921b45b965ab49cce2486e1b404965ab49d27338922486d9662c6ad27338921b407965ab49cce2f4922086d965e26ad2749cce2486d965ab49cce2486d1b445002596ad7049d142486d9be596adab49cce2486d965ab49cce2486d1b402965ab49d27338921b434965ab49cce338922086d966376ad4b49cce2486d965ab57927338bd2486d965ab6ad27338921b46da1e87965ab49cce2486d966596ad273c8ce2486d965ab49cce2486d04004965ab57927338ce2486d966596ad9849cce2486d965ab5f127338921b445965ab52d27338921b426965ab49cce2d8921b419965ab5f127338921b402965ab49d04338921b410002596ad27338921b406965ab6ad7c49cce2486d965cd6ad27338921b419002b7965ab49cce2486d965f16ad9849cce2486d9ea598b1ab49cce2486d966596ad27338921b401adea8965ab49cce2486d965ab49cf2338921b404a1e596ad27450ce2486d002596ad27338921b44b965ab66127338921b404965ab49d043c8ce2486d965b56ad27338921b419a76596ad27338b62486d965ab66127410ce2486d965ab5f127338921b41c00259789cd49cce2486d965ab49cce258921b40b965ff6ad27338921b40b965ab49cce248821b419965ab49cce2486d01c07a7659735ab49cce2486d965ab49cce2486d01001965ad6ad27338921b402965ab49d14450ce2486d965ab49d04338921b401965ff6ad27338bd2486d965ab57927338921b419002596ad27338922186daa2596ad27338922186d965ff6ad27338ce2486d965ab49cce248921b410002596ad9d49cce2486d965e26ad27338921b410a76596ad27338922086d9ea596ad27338922306d965ab49cce2486d0d010a1e596ad4b49cce2486d965ab49cce2486d16c00002596ad27338921b41aa76596ad5e49cce2486d9ea596ad27338921b40700000965ab49cce2906d9662c6ad27338921b425a1e596ad2749cce2486d002596ad27338921b45b965ab49cf2338922486d965e26ad273c8ce2486d965ab66127338922486d965e26ad9849cce2486daa2596ad27338921b45b965ab49cce2d8921b40600281965ab49cce2486d965ab49cf2338921b434965ab66127338921b434965ab49cce2486d11400002596ad7c578ce2486d965ab49cce2486d00800965ab52d27450ce2486d002596ad3b49cce2486d00259771ab49cce2486da76596ad27338921b45d966596ad27338921b40b002596ad27338921b445965ff6ad27338921b419965ab49cce248921b401002596ad27338921b402965e26ad27338921b401965ab49d27450ce2486daa2596ad27338921b445965ab49cce264921b425000009a5ab49cce2486daa2596ad27338921b402965ab49cce2486d0d0019ea7a965ab49cce2486d00000965f16ad272486da3a6f965ab49cce2486d002596adab49cce2486d002596ad27338921b420966596ad27338bd2486daa2596adab49cce2486d002597fde249cce2486d966596ad27338ce2486d966206ad9849cce2486d002596ad27338921b422965ab49cce2486d02c04002597fd27338921b434966167fdab49cce2486da76597fdab49cce2486d965ab49d04338921b40b002596ad27338921b41c9be598b1ab49cce2486d002596ad2744cce2486d965ab49cce2f4921b404965ab49cce2486d094079662c6ad27338921b46d965ab49d04338bd2486d00259709ab49cce2486d965ab52d4b49cce2486d965ab49cce338921b40400000965ab545273386d00259831ab49cce2486d002596ad273389e2486d965ab49d04338ce2486d9662c6ad7c49cce2486d002596ad273389e1b434965ab49cce2d8921b41a965ab52d2749cce2486d002736ad27338921b425a1e596ad27338921b410965ab49cce2d8921b45b965ab49d2749cce2486d00000965d56ad273386da76596ad27338c82486d966596ad27338921b4199ea596ad27338921b4250025974dab49cce2486d965cd6ad27338921b45b002596ad2d49cce2486d965ab5b14b49cce2486d002816ad27338921b434965ab49ce7338921b45ba1e596ad273c8ce2486d00000965ab560ce2486da1e596ad9849cce2486d965ab49d14338921b410965ab49cce2d8921b445965ab49cce248921b40b002597e1ab49cce2486d965ab49cce2d8921b4029be596ad27338921b407965e26ad27338921b40b00287965ab52d2733892002596ad27390ce2486d002596ad27338921b448a52596ad27338921b445002596ad27364ce2486d965ab49cce2486d0d00b965ab49cce2486d06404965ab6ad27338b62486da7659965ab49cce2486d965ab49cce2486d1b407965ab49d04338921b419965cd6ad27338921b445965ab49cce2f4922486d965cd6ad27338921b402965e26ad27338bd2486dade597fdab49cce2486d965ab49cce248821b45b002596ad27338922146d00000965ab49cfb3386da1e596ad27338921b401965ab49cce2f4921b434965ab49cce338922486d002596ad273c8ce24834965ab49d143c8ce2486d965e26ad27338ce2486d965cd6adab49cce2486d0026f965ab49cce2d86d965ab66127450ce2486d965ab5f127338921b407965ab57927338921b45b965ab49cce338921b434965ab49d13338b62486d002596ad27458ce2486da76596ad27338921b404965ab49ceb338bd2486d965dc6ad27338922086d00000965ab49cde2486d965ab49cce248821b445966166ad27410ce2486da76596ad27410ce2486d9ea6f965ab49cce2486d965ab49cce248821b402965ab4c127338921b4190027a965ab49cf22486d002a89659849cce2486d002596ad27350921b410965ab49d14338921b401965ab57927338921b4459ea596ad27338921b46d965ab6ad27338922086d965ab57927338921b402965ab52d27338921b410002b4965ab49cce2486d965ab49cce2486d094250028e965ab49cce2486dad2a8965ab49cce2486d00000965b149cce2486d9660c735ab49cce2486d965ab6ad5e49cce2486d002596ad27338922246d002598b1ab52cce2486d0026f965ab49cce2086d965ab49d27338921b4109ea596ad7c49cce2486d00259895ab49cce2486d0026f965ab579273386d965ab49cce248921b419002598b1ab49cce2486d965e26ad27338921b419965ab52d273c8ce2486d002596ad2d338921b410965ab6614b49cce2486d00000965c26ad2733892aa2598b1ab49cce2486d002596ad27338be2486d965ab49cce2486d0d019002ae965ab49cce2486dabaa8965ab49cce2486d965ff6ad27338921b45b965ab49d273c8ce2486d965ab6612749cce2486d002596ad3e49cce2486d002596ad7049cce2486d965ab52d27338921b4019ea596ad27474ce2486da76596ad27338922486d96616789ab49cce2486da7659789ab49cce2486d002596ad27338992486da76596ad27338921b4349be596ad27338921b425a1e596ad27338921b40b965ff6ad27338921b445965ab5f16d49cce2486d002596ad273c8921b425965ff6ad27338921b402965ab49d27338921b401002596ad27338a92486d965ab49cce2486d1b425002646ad27338921b410965ff6adab49cce2486da1e596ad27338bd2486d00287965ab49cf233892002596ad27338922306d965ab49cce2486d01c00002596ad58338922086da1e596ad27338ce2486d002596ad27338921b428965ab5f127338921b4259be596ad27338921b462965ab49d14338921b40b002596ad27338921b407aa2596ad27338921b407002596ad27338921f06da3a596ad27338b62486d965ab49d14338bd2486d965ab49cce2486f1b407965ab49cce2486d04010002596ad27338921b412965ab49d14338ce2486d9660c7fdab49cce2486d000009cdab49cce2486d966596ad27338921b45b9be6f965ab49cce2486d002596ad273acce2f4929662c6ad27338b62486d0027a965ab49cbd2486d9be596ad27338921b46d965ab49cf2338921b410965ab66127338921b4100027a965ab49cce2486d9662c735ab49cce2486d002596ad4b49cce24810965ab49cce2486d1b46daa27a965ab49cce2486d966596ad27338921b445a4a87965ab49cce2486da1e596ad27338921b419966596ad27338921b402965ab49cce2486d16c04aba59735ab49cce2486d00269965ab49cce2486d002596ad27338921b4569be596ad7c49cce2486d0025b965ab49cce2486d965ab52d27338921b40b0025972127338921b45b965ab49d04338921b45ba76596ada549cce2486d966596adab49cce2486d965b16ad27338921b410965ab5f127338921b46d965ab49cce2486d04001965ab49cf23c8ce2486da929d965ab49cce2486d965ab661273c8ce2486d00000965ab4c0ce2486d965ab49d27338921b40b965ab6619849cce2486d002596ad27350ce2486d965ab52d27338bd2486d965ab49cce2d8a92486d002596ad4b49cf2338929662c6ad27338922086d002596ad4f49cce2486d965ab49cce2486d11404965ab49cce2486d01002965ab49d14338921b419965ab52d27338ce2486da7687965ab49cce2486d965ab49d04338921b445965ab5f17c49cce2486d965ab49d04338921b402965ab49d27338bd2486d9662c6ad5e49cce2486d002596ad27338ac1b45b965ab6ad27338921b40400000965ab4f92733892965ab49cf2338921b401002596ad4249cce2486d002596ad6d49cce2486d00259721ab49cce2486d965ab49d27338ce2486d965ab6ad27410ce2486d965ab66127338921b401965ab49cce2d8921b40797e596ad27338921b407002596ad4b338921b425965ab49cce2486d094000026f965ab49d043386da76596ad27450ce2486d9ce596ad27338921b425965cd6ad27338921b407965ab6297c49cce2486d965ab49d13410ce2486d965ab49cce2486d00401002596ad27338921b425002596ad27338a42486daa2596ad27338921b425965ab49cce248921b45b965e26ad27338921b45b00000a51ab49cce2486d965ab49cce2486d16c34002596ad2733cce2486d00000965ab49cff2486d965ab52d27338921b419a06596ad27338921b4349ea596ad27338b62486d965ab49cce248821b40700000965ab49cce2487c9664e8b1ab49cce2486d002596ad27338921b462965ab49cce248921b445965e26ad27338921b4459662c7fdab49cce2486d965ab49d27338921b419965ab49cce248921b40200000966206acce2486d965ab49cf2338921b427965ab57927338921b407965e26ad27338921b4029ea59735ab49cce2486d9be596ad27338c52486d965ab49cce2486d114349be596ad9c49cce2486d965ab49cce2486d0d002965ab6ad27338922486d965e26adab49cce2486d965e26ad27338921b420965ab49cce2486d0400b002596fdab49cce2486da76596ad4b49cce2486d965ab6ad27338921b434965ab57927338921b4120026f965ab49cce2486d965ab49cce2f4921b410002b5965ab49cce2486d0026f965e26ad273386daa26f965ab49cce2486da76596ad2749cce2486d9ea596ad27338922086da969d965ab49cce2486d002596ad27338921b46d965ab49cce338921b410965ab49cf2338921b40baa2596ad27338921b46d965ab66127338921b40b002596ad27338921b4149ea596ad5e49cce2486d965ab49cde338921b445002596ad5149cce2486d002597b9ab49cce2486d002596ad27484ce2486d002596ad7c49cce2486d965ab49cf2338bd2486daa2596ad27484ce2486d965ab66127338bd2486d965ab5d927338bd2486d965b96ad27338921b425aa2596ad7c49cce2486d965ab49cce278921b434965ab49cf2338ce2486d002596ad27338921b439965ab66127338ce2486d965ab49cce2486d02c01965ab49cce2d8921b42500000965ab4d4ce2486d965ff6ad27338921b407966418b1ab49cce2486d002596d527338921b41900259755ab49cce2486d965ab5794f49cce2486d965ab49cce2f4921b401965cd6ad27338921b425966598b1ab49cce2486d002596ad27338921cc6d002596ad8a49cce2486d965e274dab49cce2486d965ab49cce338921b401002596ad27474ce2486da1e596ad27338921b45b965ab49cce2486d06410965e26ad27338921b4489662c6ad27338921b40a002596b5ab49cce2486d9662c6ad27338921b404965ab49cce248821b425965ab49cd9338921b43400261965ab49cce2486d9ea597fdab49cce2486d9662c6ad27410ce2486d002596ad273ecce2486da1e596ad27338921b445002596ad27338921b435965ab57927338921b425a1e596ad27338921b402a4a596ad273c8ce2486d965ab49cf2338921b419965ab49d14338921b45b965ab66127338921b4199be596ad27338b62486da76596ad27338921b410965cd6fdab49cce2486d002596ad273fc922086d992596ad27338921b410a1e596adab49cce2486d002596ad27338921b40f965ab49cce2d8921b46d0029d9662c6acce2486d9be59735ab49cce2486d965ab49cce2486d06401965ab49d14338921b445965ee6ad27338b62486d002596ad27340ce2486d966596ad27338921b407965cd6ad27338921b46d965ab49d14338921b402a76596ad273c8ce2486d965ab5f127338b62486da76596ad9849cce2486d002596bdab49cce2486d002596ad27338c52486d002596ad9c49cce2486d965ab6497c49cce2486d965ab6ad27450ce2486d00000965dc49cce2486d965ab49cce2d8921b439965ee735ab49cce2486d965ab49cce2486d02c0b002596ad27338921b400965cd6ad7c49cce2486d9be596ad27338922086d002596ada249cce2486d00273965ab49cce2486d965ab49d04338921b428002596ad27338921b41e965ab49cce2486d01c04a76596ad27338921b40100000965ab49cce2486d002596ad27338932486d965ab49cce248821b46d965ab49cce2f4921b40b9be596ad5e49cce2486d002a8965ab49cce2486d965ab49d04338921b4079662c6ad27338922486d965ab52d27338921b45b9662c789ab49cce2486daa2a8965ab49cce2486d0025a965ab49cce2486d965ab49cce338921b40b965ff6ad27338921b425002596ad27338921bc6d9662c6ad27338921b434965ab57927338921b46d9ea59965ab49cce2486d965ab49cce2f4bd2486d965ab49d27338921b45b965ab5f127338922086d002596ad5149d143386d965ab52d3b49cce2486d965ab49cce338bd2486d966378b1ab49cce2486d965ab52d27338921b445965ab5f15e49cce2486d965ab52d27338921b402965ab49cce338ce2486d002596b1ab49cce2486d002596ad2a49cce2486d965ab6ad4b49cce2486d9ea596ad27338921b404965ab49d27338921b445965ab49d27338921b402002597bdab49cce2486d9ea596ad27410ce2486d00000965ab49cce24873002596ad27338921b43b965ab6ad2749cce2486d00287965ab49cce2485b965ab49cce2486d0640b9be597fdab49cce2486d002879bdab49cce2486d002597fdab49cf22486d965ab49cce248921b407965e26ad27338921b407a1e596ad27458ce2486d965ff6ad27338921b46d965ab49cce2486d0d007965ab49cce2f4921b419002596ad5e49d043386d00000965f849cce2486d002596e5ab49cce2486d9664e6ad7c49cce2486d966596ad27338921b425965ab49cce338921b419965ff6ad7c49cce2486d002596ad27338b62486da76596ad27338921b40b00259789ab49cce2d86d0025f965ab49cce2486daa2596ad27338b62486da3a87965ab49cce2486d00294965ab49cce2486d002596ad9249cce2486da1e596ad27338922246d965ab49cce248711b40b965ab49cce2486d16c1000259735ab49cce2486da76596ad27338bd2486d9ea596ad27338922486daa259735ab49cce2486d965ab49cce2486d094049ea59789ab49cce2486d002596ad2739cce2486da76596ad27338ce2486d00000965ab5d8ce2486d965ab49d04338921b4259ea596ad27338921b434a1e598b1ab49cce2486d0025977127338922086d002596d5ab49cce2486d965ab49cce248821b400a1e596ad27338be2486daba87965ab49cce2486d965ab49cce2486d11410965ab49cf2338921b45b002596ad5849cce2486d965ab49cce2486d04002002596ad5e52cce2486d9662c6ad27338921b436965ab66127338921b45b002596ad27338922086daa2596ad27338922086d9be59965ab49cce2486d965ab6ad27338921b410965ab49cce2486d06419966256ad27450ce2486d0025d965ab49cce2486d002596ad5e49cce2486d9662c6ad27450ce2486d00259789ab579273386daa2596ad5e49cce2486d966596ad27338921b46d965ab49cce2b0921b45b965ff6ad27338921b435965ab49cf2338921b445965ab49cce2486d16c01965ab66127338921b445965ab49cf2338921b402965ab66127338921b402000009662549cce2486d965ab4f927450ce2486d965ab5c127450ce2486d002a89662c49cce2486d965ab6ad273c8ce2486d002597c5ab661272486d9be596ad27338921b404966596ad7c49cce2486d965ab6ad9849cce2486da76596ad27338921b4199be596ad27410ce2486d002596ad27410f22486d965ab49cce2486d1b404002596ad27338921b45d965ab49cce250921b402965ab49cf2338921b422965ab49cce2486d11401965ab49cce248921b425965ab49d04338921b46d965ab49cce2486d00801965e26ad27338921b425a1e596ad27338921b407965ab49cce2d8b62486d965ab49cce2486d0d025965ab49d133c8ce2486d965ab6ad27338921b401965ab5f127338921b404965ab5f127410ce2486da769d965ab49cce2486d965cd6ad27338b62486d965c26ad9849cce2486d9662c6ad4b49cce2486d00259939ab49cce2486d002596ad27338962486d9660c6ad273c8ce2486d002596ad2849cce2486d965ff6ad27338921b41e002597fdab49cce2486d965ab49d14338921b407aa2597fdab49cce2486da927a965ab49cce2486d002a8a1dab49cce2486d965cd735ab49cce2486d9662c6ad2749cce2486d965ab4b527338921b4100029d965ab5f0ce2486da1e7a965ab49cce2486d965ab49cce2d8922086d
  | 8 => 0x259965ab49cce2486d002596ad27338921b404002596ad27410ce2486d002596ad27338922486d00259789ab49cce2486d002596ad27338921b43400287965ab49cce2486d002596ad27450ce2486d002596ad4b49cce2486d002596ad2749cce2486d002596ad27338921b410002596ad273c8ce2486d002596ad9849cce2486d002596ad27338921b401002596ad27338921b40b002596ad27338bd2486d002596ad27338ce2486d002596ad27338921b4190029d965ab49cce2486d002596ad27338921b45b002596ad27338921b445002596ad27338921b402002596adab49cce2486d002598b1ab49cce2486d002596ad27338921b4070027a965ab49cce2486d002596ad27338921b4250026f965ab49cce2486d002596ad27338921b46d002596ad7c49cce2486d00000965ab49cce2486d002a8965ab49cce2486d002596ad27338b62486d00259735ab49cce2486d002596ad27338922086d002596ad5e49cce2486d002597fdab49cce2486d
  | 9 => 0x965ab49cce2486d
  | _ => 0

def VT : Nat := 0xfffffffffffffffffffffffffffc00fffffffffffffffffffffffff003ffffffffffffffffffffffffc00fffffffffffffffffffffffff003ffffffffffffffffffffffffc00ffffffffffffbfeffbfeffbfefffffffffffffffffbfeffbfeffbfefffffffc00003ffff7fdff7fdff7fdfffffffffffffffff7fdff7fdff7fdffc00003fffffffff3fcff3fcff3fcffffffffffffc00ff3fcff3fcff3fcfffffffc0000000ff3fcff3fcff3fcffc00003ffffc00feffbfeffbfeffbffffffffffffffffeffbfeffbfeffbffffffffff00000febfafebfafebfafffffffc0000000fe7f9fe7f9fe7f9fffffffc00ffffffe7f9fe7f9fe7f9fffffffc0000000fe7f9fe7f9fe7f9ffc0000000ffffffe3f8fe3f8fe3f8ffffffffff00000fe3f8fe3f8fe3f8fffffffc00ffc00fe3f8fe3f8fe3f8fffffffc00003fffe3f8fe3f8fe3f8fffffffc0000000fe3f8fe3f8fe3f8ffc000000000000fdff7fdff7fdff7ffffffffffffffffdff7fdff7fdff7ffc00fffffffc00fdbf6fdbf6fdbf6fffff003ffffffffdbf6fdbf6fdbf6fffff00000003fffdbf6fdbf6fdbf6ffc00003ffffc00fd7f5fd7f5fd7f5ffc00003ffffc00fd3f4fd3f4fd3f4fffff003ffffc00fd3f4fd3f4fd3f4ffc00fffffffc00fd3f4fd3f4fd3f4ffc00003ffffffffd3f4fd3f4fd3f4ffc00003ffffc00fd3f4fd3f4fd3f4ffc000000000000fcff3fcff3fcff3ffc00fffff00000fcbf2fcbf2fcbf2ffc000000000000fc7f1fc7f1fc7f1ffc000000000000fc3f0fc3f0fc3f0fffff0000000000fc3f0fc3f0fc3f0ffc00ffc0000000fc3f0fc3f0fc3f0ffc00003ff00000fc3f0fc3f0fc3f0ffc0000000ffc00fc3f0fc3f0fc3f0ffc000000000000fbfeffbfeffbfefffffffffffffffffbfeffbfeffbfeffffff00000ffffffbbeefbbeefbbeefffff00000003fffb7edfb7edfb7edffc0000000ffffffb3ecfb3ecfb3ecffc000000000000fafebfafebfafebffc00fffffffffffafebfafebfafebffc00fffff00000fafebfafebfafebffc0000000ffffffabeafabeafabeaffc000000000000fa7e9fa7e9fa7e9fffff00000ffffffa7e9fa7e9fa7e9ffc00ffc00ffffffa7e9fa7e9fa7e9ffc00003ffffffffa7e9fa7e9fa7e9ffc0000000ffffffa7e9fa7e9fa7e9ffc000000000000fa3e8fa3e8fa3e8fffff0000000000fa3e8fa3e8fa3e8ffc00ffc0000000fa3e8fa3e8fa3e8ffc0000000ffc00fa3e8fa3e8fa3e8ffc0000000003fffa3e8fa3e8fa3e8ffc000000000000f9fe7f9fe7f9fe7ffffffffff003fff9fe7f9fe7f9fe7fffff00000003fff9fe7f9fe7f9fe7ffc00fffff00000f9be6f9be6f9be6fffffffc00003fff9be6f9be6f9be6fffff003ff003fff9be6f9be6f9be6fffff00000ffffff9be6f9be6f9be6fffff00000003fff9be6f9be6f9be6ffc000000000000f97e5f97e5f97e5ffc000000000000f93e4f93e4f93e4fffff0000000000f93e4f93e4f93e4ffc00003ff00000f93e4f93e4f93e4ffc0000000ffc00f93e4f93e4f93e4ffc0000000003fff93e4f93e4f93e4ffc000000000000f8fe3f8fe3f8fe3ffffffffff00000f8fe3f8fe3f8fe3ffc00fffffffc00f8fe3f8fe3f8fe3ffc00fffff003fff8fe3f8fe3f8fe3ffc00fffff00000f8fe3f8fe3f8fe3ffc000000000000f8be2f8be2f8be2fffff0000000000f8be2f8be2f8be2ffc00ffc0000000f8be2f8be2f8be2ffc00003ff00000f8be2f8be2f8be2ffc0000000003fff8be2f8be2f8be2ffc000000000000f87e1f87e1f87e1ffc00ffc0000000f87e1f87e1f87e1ffc00003ff00000f87e1f87e1f87e1ffc0000000ffc00f87e1f87e1f87e1ffc0000000003fff87e1f87e1f87e1ffc000000000000f83e0f83e0f83e0fffffffc0000000f83e0f83e0f83e0fffff00000003fff83e0f83e0f83e0fffff0000000000f83e0f83e0f83e0ffc00fffff00000f83e0f83e0f83e0ffc00ffc0000000f83e0f83e0f83e0ffc00003ffffc00f83e0f83e0f83e0ffc00003ff00000f83e0f83e0f83e0ffc0000000ffffff83e0f83e0f83e0ffc0000000ffc00f83e0f83e0f83e0ffc0000000003fff83e0f83e0f83e0ffc000000000000f7fdff7fdff7fdf003fffffffffffff63d8f63d8f63d8003ffffc0000000f53d4f53d4f53d400000003ffffc00f1bc6f1bc6f1bc6003ff00000003fff0fc3f0fc3f0fc300000fffff00000effbfeffbfeffbf003ffffffffffffee3b8ee3b8ee3b8003ffffc0000000ed3b4ed3b4ed3b400000003ffffc00ea7a9ea7a9ea7a90000000000fffffe9ba6e9ba6e9ba6003ff00000003ffe7b9ee7b9ee7b9e003ffffffffffffe7b9ee7b9ee7b9e003ffffc00003ffe739ce739ce739c003fffffffffc00e6398e6398e6398003ffffc0000000e5b96e5b96e5b96003ff003fffffffe5394e5394e539400000003ffffc00e1b86e1b86e1b86003ff00000003ffe0380e0380e0380000000000000000dff7fdff7fdff7f003ffffffffffffde378de378de378003ffffc0000000dd374dd374dd37400000003ffffc00da769da769da7690000000000fffffd8f63d8f63d8f6300000fffff00000d7f5fd7f5fd7f5f003fffffffffc00d7b5ed7b5ed7b5e003ffffc0000000d775dd775dd775d00000003ffffc00d735cd735cd735c003fffffffffc00d6f5bd6f5bd6f5b003fffffff00000d6358d6358d6358003ffffc0000000d5f57d5f57d5f5700000fffffffc00d5354d5354d535400000003ffffc00d0f43d0f43d0f4300000fffff00000d0340d0340d0340000000000000000cf73dcf73dcf73d003ffffffffffffcf73dcf73dcf73d00000003fffffffcf33ccf33ccf33c003fffffffffc00ce739ce739ce739003ffffc00fffffce338ce338ce338003ffffc0000000cd334cd334cd33400000003ffffc00ca729ca729ca7290000000000fffffc8320c8320c8320000000000000000c7b1ec7b1ec7b1e003fffffffffc00c771dc771dc771d003fffffffffc00c731cc731cc731c003ffffffffffffc731cc731cc731c003fffffffffc00c731cc731cc731c003ffffc0000000c731cc731cc731c00000003ffffc00c6b1ac6b1ac6b1a003ffffc0000000c6719c6719c6719003ffffc0000000c6318c6318c6318003fffffff00000c6318c6318c6318003ffffc00ffc00c6318c6318c6318003ffffc0000000c5b16c5b16c5b1600000003ffffc00c5715c5715c571500000003ffffc00c5314c5314c5314003ff003ffffc00c5314c5314c531400000fffffffc00c5314c5314c531400000003ffffc00c2308c2308c23080000000000ffc00c1304c1304c1304003ff0000000000c0300c0300c030000000fffff00000c0300c0300c0300000000000000000bfeffbfeffbfeff003ffffffffffffbe2f8be2f8be2f8003ffffc0000000ba6e9ba6e9ba6e90000000000fffffb9ae6b9ae6b9ae6003ff00000003ffb8ee3b8ee3b8ee300000fffff00000b7edfb7edfb7edf003fffffff003ffb7adeb7adeb7ade003ffffc00003ffb6edbb6edbb6edb003fffffff00000b62d8b62d8b62d8003ffffc0000000b5ed7b5ed7b5ed700000fffff00000b3ecfb3ecfb3ecf003ff00000003ffb1ec7b1ec7b1ec7003fffffff003ffb1ac6b1ac6b1ac6003ff00000003ffb0ec3b0ec3b0ec300000fffff00000b02c0b02c0b02c0000000000000000afebfafebfafebf003ffffc00fffffafabeafabeafabe003ffffc00003ffaf6bdaf6bdaf6bd0000000000fffffaeebbaeebbaeebb003ffffc0000000ae6b9ae6b9ae6b9003ffffc00fffffae2b8ae2b8ae2b8003ffffc0000000abeafabeafabeaf003ff00000fffffaa6a9aa6a9aa6a90000000000fffffa9aa6a9aa6a9aa6003ff00000003ffa82a0a82a0a82a0000000000000000a7e9fa7e9fa7e9f003ffffc00003ffa7a9ea7a9ea7a9e003fffffff003ffa7a9ea7a9ea7a9e003ffffc00fffffa7a9ea7a9ea7a9e003ffffc00003ffa7a9ea7a9ea7a9e003ffffc0000000a7a9ea7a9ea7a9e003ff00000003ffa729ca729ca729c003ffffc0000000a6a9aa6a9aa6a9a003ffffc0000000a6699a6699a6699003ffffc0000000a6298a6298a6298003ffffc00003ffa6298a6298a6298003ffffc0000000a5a96a5a96a5a96003ff00000003ffa5294a5294a5294000000000000000a3a8ea3a8ea3a8e003ff00000003ffa2288a2288a22880000000000003ffa1e87a1e87a1e87003ff00000003ffa1a86a1a86a1a86003ffffc00003ffa1a86a1a86a1a86003ff00000003ffa0a82a0a82a0a8200000ffc0000000a0280a0280a02800000000000000009ee7b9ee7b9ee7b003ffffffffffff9ee7b9ee7b9ee7b003fffffff000009e6799e6799e679003ffffc00fffff9e2789e2789e278003ffffc00000009ae6b9ae6b9ae6b00000ffffffffff9a6699a6699a6690000000000fffff98e6398e6398e6300000fffff0000098260982609826000000000000000097e5f97e5f97e5f003fffffff000009725c9725c9725c003ffffc000000096e5b96e5b96e5b003fffffffffc0096e5b96e5b96e5b003fffffff003ff96e5b96e5b96e5b003fffffff0000096e5b96e5b96e5b003ffffc000000096e5b96e5b96e5b00000fffff0000096a5a96a5a96a5a003ffffc0000000966599665996659003ffffc0000000962589625896258003fffffff00000962589625896258003ffffc000000094e5394e5394e5300000fffff0000094250942509425000000003ff0000092e4b92e4b92e4b00000fffff0000092649926499264900000000000000091e4791e4791e4700000fffff0000090e4390e4390e43003fffffff0000090e4390e4390e4300000fffff0000090a4290a4290a42003ff00000000009024090240902400000000000000008f63d8f63d8f63d003ffffc00fffff8f23c8f23c8f23c003ffffc00000008ee3b8ee3b8ee3b003ffffc00fffff8ea3a8ea3a8ea3a003ffffc00000008e6398e6398e639003ffffffffffff8e6398e6398e639003ffffc00fffff8e6398e6398e639003ffffc00000008e6398e6398e6390000000000fffff8e2388e2388e238003ffffc00ffc008e2388e2388e238003ffffc00003ff8e2388e2388e238003ffffc00000008c2308c2308c2300000000000ffc008b62d8b62d8b62d0000000000fffff8ae2b8ae2b8ae2b0000000000fffff8a6298a6298a629003ff00000fffff8a6298a6298a62900000ffc00fffff8a6298a6298a6290000000000fffff88621886218862100000ffc0000000882208822088220003ff00000003ff88220882208822000000000000000087a1e87a1e87a1e003ffffc00000008761d8761d8761d003ffffc00000008721c8721c8721c003fffffff000008721c8721c8721c003ffffc00ffc008721c8721c8721c003ffffc00003ff8721c8721c8721c003ffffc000000086e1b86e1b86e1b003ffffc000000086a1a86a1a86a1a003fffffff0000086a1a86a1a86a1a003ffffc00003ff86a1a86a1a86a1a003ffffc0000000866198661986619003fffffff00000866198661986619003ffffc00ffc00866198661986619003ffffc00003ff866198661986619003ffffc0000000862188621886218003fffffffffc00862188621886218003fffffff00000862188621886218003ffffc00fffff862188621886218003ffffc00ffc00862188621886218003ffffc00003ff862188621886218003ffffc0000000862188621886218003ff000000000086218862188621800000ffc0000000862188621886218000000000000000842108421084210003ff000000000084210842108421000000ffc0000000842108421084210000000000000000822088220882208003ff000000000082208822088220800000ffc000000082208822088220800000000000000081204812048120400000000000000080a0280a0280a02000000000000000806018060180601000000000000000802008020080200003ffffc0000000802008020080200003ff000000000080200802008020000000ffc000000080200802008020000000003ff000008020080200802000000000000ffc008020080200802000000000000003ff8020080200802000000000000000007fdff7fdff7fdff003ffffffffffff7d1f47d1f47d1f400000003ffffc007a5e97a5e97a5e90000000000fffff799e6799e6799e6003ff00000003ff78de378de378de300000fffff0000075dd775dd775dd7003ffffffffffff75dd775dd775dd700000fffffffc00759d6759d6759d6003ff003fffffff751d4751d4751d400000003ffffc0071dc771dc771dc7003fffffff003ff719c6719c6719c6003ff00000003ff70dc370dc370dc300000fffff00000701c0701c0701c00000000000000006fdbf6fdbf6fdbf003ff003fffffff6f9be6f9be6f9be003ff00000003ff6f5bd6f5bd6f5bd00000003fffffff6ddb76ddb76ddb700000003ffffc006d9b66d9b66d9b6003ff003fffffff6d1b46d1b46d1b400000003ffffc006bdaf6bdaf6bdaf003ff00000fffff6a5a96a5a96a5a90000000000fffff699a6699a6699a6003ff00000003ff681a0681a0681a00000000000000006799e6799e6799e003ff003fffffff6719c6719c6719c00000003ffffc0065d9765d9765d97003ff003fffffff659966599665996003ffffffffffff659966599665996003ff003fffffff659966599665996003ff00000003ff65996659966599600000003ffffc0065595655956559500000003ffffc00651946519465194003ff003ffffc0065194651946519400000003fffffff65194651946519400000003ffffc00641906419064190003ff00000000006398e6398e6398e003ff00000003ff61d8761d8761d87003ff00000003ff619866198661986003ff003ff003ff619866198661986003ff00000fffff619866198661986003ff00000003ff60982609826098200000003ff000006018060180601800000000000fffff6018060180601800000000000000005fd7f5fd7f5fd7f00000ffffffffff5f57d5f57d5f57d00000003fffffff5ed7b5ed7b5ed7b00000fffff000005dd775dd775dd7700000fffffffc005d1745d1745d17400000003ffffc005bd6f5bd6f5bd6f0000000000fffff5ad6b5ad6b5ad6b00000ffffffffff5a5695a5695a5690000000000fffff58d6358d6358d6300000fffff0000058160581605816000000000000000057d5f57d5f57d5f00000fffffffc005715c5715c5715c00000003ffffc0055d5755d5755d57003fffffffffc0055d5755d5755d5700000ffffffffff55d5755d5755d5700000fffffffc0055d5755d5755d5700000fffff0000055d5755d5755d5700000003ffffc0055956559565595600000003ffffc0055555555555555500000003ffffc0055154551545515400000fffffffc0055154551545515400000003ffffc0054d5354d5354d5300000fffff0000054150541505415000000ffc000000052d4b52d4b52d4b00000fffff0000051d4751d4751d4700000fffff0000051946519465194600000000000000050d4350d4350d4300000fffffffc0050d4350d4350d4300000fffff000005054150541505410000000000ffc005014050140501400000000000000004fd3f4fd3f4fd3f00000003fffffff4f53d4f53d4f53d003ff003fffffff4f53d4f53d4f53d00000ffffffffff4f53d4f53d4f53d00000003fffffff4f53d4f53d4f53d00000003ffffc004f53d4f53d4f53d0000000000fffff4f13c4f13c4f13c00000003ffffc004e5394e5394e5390000000000fffff4e1384e1384e1380000000000000004d9364d9364d93600000003ffffc004d5354d5354d53500000003ffffc004d1344d1344d13400000003fffffff4d1344d1344d13400000003ffffc004b52d4b52d4b52d0000000000fffff4ad2b4ad2b4ad2b0000000000fffff4a5294a5294a52900000003fffffff4a5294a5294a5290000000000fffff4912449124491240000000000003ff48521485214852100000003ff000004812048120481200000000000000004791e4791e4791e00000003ffffc004751d4751d4751d00000003ffffc004711c4711c4711c003ff003ffffc004711c4711c4711c00000fffffffc004711c4711c4711c00000003fffffff4711c4711c4711c00000003ffffc0045d1745d1745d1700000003ffffc00459164591645916003ff003ffffc0045916459164591600000fffffffc0045916459164591600000003fffffff45916459164591600000003ffffc0045515455154551500000fffffffc0045515455154551500000003fffffff45515455154551500000003ffffc00451144511445114003fffffffffc00451144511445114003ff003fffffff451144511445114003ff003ffffc0045114451144511400000fffffffc0045114451144511400000003fffffff45114451144511400000003ffffc0045114451144511400000003ff000004511445114451140000000000ffc0045114451144511400000000000000044110441104411000000003ff000004411044110441100000000000ffc0044110441104411000000000000000042108421084210800000000000000041104411044110400000003ff000004110441104411040000000000ffc00411044110441104000000000000000409024090240902000000000000000405014050140501000000000000000401004010040100003ff000000000040100401004010000000ffc000000040100401004010000000003ffffc0040100401004010000000003ff000004010040100401000000000000ffc004010040100401000000000000003ff4010040100401000000000000000003bcef3bcef3bcef003ffffffffffff3bcef3bcef3bcef003ff00000fffff3aceb3aceb3aceb00000ffffffffff3a4e93a4e93a4e90000000000fffff39ce739ce739ce7003fffffff003ff398e6398e6398e6003ff00000003ff38ce338ce338ce300000fffff00000380e0380e0380e000000000000000035cd735cd735cd7003fffffff003ff358d6358d6358d6003ff00000003ff34cd334cd334cd300000fffff0000033ccf33ccf33ccf003fffffff003ff338ce338ce338ce003ff00000003ff32ccb32ccb32ccb00000fffff0000031cc731cc731cc7003ffffffffffff31cc731cc731cc7003fffffff003ff31cc731cc731cc7003ff00000003ff31cc731cc731cc700000fffff00000318c6318c6318c6003ffffc00003ff318c6318c6318c6003ff003ff003ff318c6318c6318c6003ff00000003ff310c4310c4310c400000003ff0000030cc330cc330cc3003fffffff0000030cc330cc330cc300000fffff003ff30cc330cc330cc300000fffff00000304c1304c1304c10000000000003ff300c0300c0300c0003ffffc0000000300c0300c0300c00000000000000002fcbf2fcbf2fcbf003ff00000fffff2e4b92e4b92e4b90000000000fffff2d8b62d8b62d8b6003ff00000003ff2bcaf2bcaf2bcaf003ffffc00fffff2bcaf2bcaf2bcaf003ff003fffffff2bcaf2bcaf2bcaf003ff00000fffff2bcaf2bcaf2bcaf003ff00000003ff2bcaf2bcaf2bcaf0000000000fffff2b8ae2b8ae2b8ae003ff00000003ff2b4ad2b4ad2b4ad0000000000fffff2acab2acab2acab0000000000fffff2a4a92a4a92a4a9003ff00000fffff2a4a92a4a92a4a90000000000fffff2a0a82a0a82a0a8003ff000000000029ca729ca729ca7003ff00000003ff298a6298a6298a6003ff00000fffff298a6298a6298a6003ff00000003ff290a4290a4290a40000000000ffc0028ca328ca328ca3000000000000000280a0280a0280a00000000000000002789e2789e2789e003ff00000003ff25c9725c9725c97003ff00000003ff258962589625896003ffffc00003ff258962589625896003ff003ff003ff258962589625896003ff00000fffff258962589625896003ff00000003ff24090240902409000000000000000023c8f23c8f23c8f003ff00000003ff2388e2388e2388e003ffffc00003ff2388e2388e2388e003ff00000fffff2388e2388e2388e003ff00000003ff22088220882208800000000000000021c8721c8721c87003ffffc00003ff21c8721c8721c87003ff003ff003ff21c8721c8721c87003ff00000fffff21c8721c8721c87003ff00000003ff218862188621886003fffffff003ff218862188621886003ffffc00003ff218862188621886003ff003fffffff218862188621886003ff003ff003ff218862188621886003ff00000fffff218862188621886003ff00000003ff218862188621886003ff00000000002188621886218860000000000003ff218862188621886000000000000000210842108421084003ff00000000002108421084210840000000000003ff210842108421084000000000000000208822088220882003ff00000000002088220882208820000000000003ff208822088220882000000000000000204812048120481000000000000000200802008020080003ff00000003ff200802008020080003ff000000000020080200802008000000ffc000000020080200802008000000003ff000002008020080200800000000000ffc002008020080200800000000000003ff2008020080200800000000000000001ec7b1ec7b1ec7b00000ffffffffff1e4791e4791e4790000000000fffff1cc731cc731cc7300000fffff000001bc6f1bc6f1bc6f00000ffffffffff1b46d1b46d1b46d0000000000fffff1ac6b1ac6b1ac6b003ffffffffffff1ac6b1ac6b1ac6b00000ffffffffff1ac6b1ac6b1ac6b00000fffff000001ac6b1ac6b1ac6b0000000000fffff1a4691a4691a46900000ffc00fffff1a4691a4691a46900000003fffffff1a4691a4691a4690000000000fffff1a0681a0681a06800000ffc000000019c6719c6719c6700000fffff0000018c6318c6318c6300000fffffffc0018c6318c6318c6300000fffff003ff18c6318c6318c6300000fffff000001886218862188620000000000003ff18060180601806000000003ffffc0018060180601806000000000000000016c5b16c5b16c5b00000fffff0000015c5715c5715c5700000fffff0000014c5314c5314c53003fffffff0000014c5314c5314c5300000fffffffc0014c5314c5314c5300000fffff0000014050140501405000000000000000013c4f13c4f13c4f00000fffff0000012c4b12c4b12c4b003fffffff0000012c4b12c4b12c4b00000fffffffc0012c4b12c4b12c4b00000fffff003ff12c4b12c4b12c4b00000fffff0000012048120481204800000000000000011c4711c4711c47003fffffff0000011c4711c4711c4700000fffffffc0011c4711c4711c4700000fffff003ff11c4711c4711c4700000fffff0000011044110441104400000000000000010c4310c4310c43003fffffff003ff10c4310c4310c43003fffffff0000010c4310c4310c4300000ffffffffff10c4310c4310c4300000fffffffc0010c4310c4310c4300000fffff003ff10c4310c4310c4300000fffff0000010c4310c4310c4300000ffc000000010c4310c4310c4300000003ff0000010c4310c4310c4300000000000000010842108421084200000ffc000000010842108421084200000003ff0000010842108421084200000000000000010441104411044100000ffc000000010441104411044100000003ff00000104411044110441000000000000000100401004010040003ff000000000010040100401004000000fffff0000010040100401004000000ffc000000010040100401004000000003ff000001004010040100400000000000ffc001004010040100400000000000003ff1004010040100400000000000000000f43d0f43d0f43d0000000000fffff0ec3b0ec3b0ec3b0000000000fffff0e4390e4390e439003ff00000fffff0e4390e4390e43900000ffc00fffff0e4390e4390e43900000003fffffff0e4390e4390e4390000000000fffff0c0300c0300c0300000000000000000bc2f0bc2f0bc2f0000000000fffff0b42d0b42d0b42d003ff00000fffff0b42d0b42d0b42d00000003fffffff0b42d0b42d0b42d0000000000fffff0ac2b0ac2b0ac2b003ff00000fffff0ac2b0ac2b0ac2b00000ffc00fffff0ac2b0ac2b0ac2b00000003fffffff0ac2b0ac2b0ac2b0000000000fffff0a4290a4290a429003ffffc00fffff0a4290a4290a429003ff00000fffff0a4290a4290a42900000ffffffffff0a4290a4290a42900000ffc00fffff0a4290a4290a42900000003fffffff0a4290a4290a4290000000000fffff0a4290a4290a4290000000000ffc000a4290a4290a4290000000000003ff0a4290a4290a4290000000000000000a0280a0280a0280000000000ffc000a0280a0280a0280000000000003ff0a0280a0280a0280000000000000000902409024090240000000000000000882208822088220000000000000000842108421084210000000000ffc000842108421084210000000000003ff084210842108421000000000000000080200802008020003ff000000000008020080200802000000ffc000000008020080200802000000003ff000000802008020080200000000000fffff0802008020080200000000000ffc000802008020080200000000000003ff0802008020080200000000000000000701c0701c0701c0000000000003ff06419064190641900000003ff00000060180601806018003ff000000000006018060180601800000ffc000000006018060180601800000000000000005816058160581600000ffc000000005014050140501400000003ff000000501405014050140000000000ffc00050140501405014000000000000000048120481204812003ff003ff0000004812048120481200000000000000004411044110441100000ffc00ffc00044110441104411000000000000000040100401004010003ffffc0000000040100401004010003ff00000fffff040100401004010003ff000000000004010040100401000000ffc000000004010040100401000000003ffffc0004010040100401000000003ff000000401004010040100000000000ffc000401004010040100000000000003ff0401004010040100000000000000000300c0300c0300c003ff00000ffc000300c0300c0300c00000000000000002c0b02c0b02c0b003ff00000000000280a0280a0280a00000ffc00003ff0280a0280a0280a0000000000000000240902409024090000000000ffc000240902409024090000000000003ff024090240902409000000000000000020080200802008003ffffc0000000020080200802008003ff000000000002008020080200800000fffffffc0002008020080200800000ffc000000002008020080200800000003ff000000200802008020080000000000fffff0200802008020080000000000ffc000200802008020080000000000003ff02008020080200800000000000000001c0701c0701c070000000000ffc00018060180601806003ff00000000000180601806018060000000000003ff01806018060180600000000000000001405014050140500000003ff003ff014050140501405000000000000000010040100401004003fffffff00000010040100401004003ff00000003ff010040100401004003ff000000000001004010040100400000ffc000000001004010040100400000003ffffc0001004010040100400000003ff000000100401004010040000000000ffc000100401004010040000000000003ff01004010040100400000000000000000c0300c0300c0300000ffc000000000c0300c0300c0300000003ff0000000c0300c0300c03000000000000000008020080200802003ff00000003ff008020080200802003ff000000000000802008020080200000fffff0000000802008020080200000ffc000000000802008020080200000003fffffff00802008020080200000003ff000000080200802008020000000000ffc000080200802008020000000000003ff008020080200802000000000000000004010040100401003ffffc00003ff004010040100401003ff000000000000401004010040100000fffff0000000401004010040100000ffc000000000401004010040100000003ff000000040100401004010000000000fffff0040100401004010000000000ffc000040100401004010000000000003ff004010040100401000000000000000000000000000000003ffffc0000000000000000000000003ff003ff00000000000000000000003ff00000ffc00000000000000000003ff00000003ff000000000000000003ff000000000000000000000000000000fffff0000000000000000000000000ffc00ffc0000000000000000000000ffc00003ff00000000000000000000ffc000000000000000000000000000003ffffc0000000000000000000000003ff003ff00000000000000000000003ff000000000000000000000000000000fffff0000000000000000000000000ffc000000000000000000000000000003ff000000000000000000000000000000

def S (s j : Nat) : List Nat :=
  (List.range (fld (LT s) 4 j)).map (fun t => fld VT 120 (fld (DT s) 10 (8*j+t)))

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)

def Z (s : Nat) := bar 60 S NN idx s

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL wheel rowsG = goal 60 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (covUp 60 zs &&& lo 60) ≠ lo 60 := by decide +kernel

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
theorem h4x224 : span (Z 4) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x232 : span (Z 4) 8 232 = true := by decide +kernel
theorem z4 : span (Z 4) 240 0 = true := (@span_join (Z 4) 120 0 120 (@span_join (Z 4) 56 0 64 (@span_join (Z 4) 24 0 32 (@span_join (Z 4) 8 0 16 h4x0 (@span_join (Z 4) 8 8 8 h4x8 h4x16)) (@span_join (Z 4) 16 24 16 (@span_join (Z 4) 8 24 8 h4x24 h4x32) (@span_join (Z 4) 8 40 8 h4x40 h4x48))) (@span_join (Z 4) 32 56 32 (@span_join (Z 4) 16 56 16 (@span_join (Z 4) 8 56 8 h4x56 h4x64) (@span_join (Z 4) 8 72 8 h4x72 h4x80)) (@span_join (Z 4) 16 88 16 (@span_join (Z 4) 8 88 8 h4x88 h4x96) (@span_join (Z 4) 8 104 8 h4x104 h4x112)))) (@span_join (Z 4) 56 120 64 (@span_join (Z 4) 24 120 32 (@span_join (Z 4) 8 120 16 h4x120 (@span_join (Z 4) 8 128 8 h4x128 h4x136)) (@span_join (Z 4) 16 144 16 (@span_join (Z 4) 8 144 8 h4x144 h4x152) (@span_join (Z 4) 8 160 8 h4x160 h4x168))) (@span_join (Z 4) 32 176 32 (@span_join (Z 4) 16 176 16 (@span_join (Z 4) 8 176 8 h4x176 h4x184) (@span_join (Z 4) 8 192 8 h4x192 h4x200)) (@span_join (Z 4) 16 208 16 (@span_join (Z 4) 8 208 8 h4x208 h4x216) (@span_join (Z 4) 8 224 8 h4x224 h4x232)))))

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
theorem h5x1640 : span (Z 5) 8 1640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1648 : span (Z 5) 8 1648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1656 : span (Z 5) 8 1656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1664 : span (Z 5) 8 1664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1672 : span (Z 5) 8 1672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1680 : span (Z 5) 8 1680 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1688 : span (Z 5) 8 1688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1696 : span (Z 5) 8 1696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1704 : span (Z 5) 8 1704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1712 : span (Z 5) 8 1712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1720 : span (Z 5) 8 1720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1728 : span (Z 5) 8 1728 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1736 : span (Z 5) 8 1736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1744 : span (Z 5) 8 1744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1752 : span (Z 5) 8 1752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1760 : span (Z 5) 8 1760 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1768 : span (Z 5) 8 1768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1776 : span (Z 5) 8 1776 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1784 : span (Z 5) 8 1784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1792 : span (Z 5) 8 1792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1800 : span (Z 5) 8 1800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1808 : span (Z 5) 8 1808 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1816 : span (Z 5) 8 1816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1824 : span (Z 5) 8 1824 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1832 : span (Z 5) 8 1832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1840 : span (Z 5) 8 1840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1848 : span (Z 5) 8 1848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1856 : span (Z 5) 8 1856 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1864 : span (Z 5) 8 1864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1872 : span (Z 5) 8 1872 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1880 : span (Z 5) 8 1880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1888 : span (Z 5) 8 1888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1896 : span (Z 5) 8 1896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1904 : span (Z 5) 8 1904 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1912 : span (Z 5) 8 1912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1920 : span (Z 5) 8 1920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1928 : span (Z 5) 8 1928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1936 : span (Z 5) 8 1936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1944 : span (Z 5) 8 1944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1952 : span (Z 5) 8 1952 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1960 : span (Z 5) 8 1960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1968 : span (Z 5) 8 1968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1976 : span (Z 5) 8 1976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1984 : span (Z 5) 8 1984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x1992 : span (Z 5) 8 1992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x2000 : span (Z 5) 8 2000 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x2008 : span (Z 5) 8 2008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x2016 : span (Z 5) 8 2016 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x2024 : span (Z 5) 2 2024 = true := by decide +kernel
theorem z5 : span (Z 5) 2026 0 = true := (@span_join (Z 5) 1016 0 1010 (@span_join (Z 5) 504 0 512 (@span_join (Z 5) 248 0 256 (@span_join (Z 5) 120 0 128 (@span_join (Z 5) 56 0 64 (@span_join (Z 5) 24 0 32 (@span_join (Z 5) 8 0 16 h5x0 (@span_join (Z 5) 8 8 8 h5x8 h5x16)) (@span_join (Z 5) 16 24 16 (@span_join (Z 5) 8 24 8 h5x24 h5x32) (@span_join (Z 5) 8 40 8 h5x40 h5x48))) (@span_join (Z 5) 32 56 32 (@span_join (Z 5) 16 56 16 (@span_join (Z 5) 8 56 8 h5x56 h5x64) (@span_join (Z 5) 8 72 8 h5x72 h5x80)) (@span_join (Z 5) 16 88 16 (@span_join (Z 5) 8 88 8 h5x88 h5x96) (@span_join (Z 5) 8 104 8 h5x104 h5x112)))) (@span_join (Z 5) 64 120 64 (@span_join (Z 5) 32 120 32 (@span_join (Z 5) 16 120 16 (@span_join (Z 5) 8 120 8 h5x120 h5x128) (@span_join (Z 5) 8 136 8 h5x136 h5x144)) (@span_join (Z 5) 16 152 16 (@span_join (Z 5) 8 152 8 h5x152 h5x160) (@span_join (Z 5) 8 168 8 h5x168 h5x176))) (@span_join (Z 5) 32 184 32 (@span_join (Z 5) 16 184 16 (@span_join (Z 5) 8 184 8 h5x184 h5x192) (@span_join (Z 5) 8 200 8 h5x200 h5x208)) (@span_join (Z 5) 16 216 16 (@span_join (Z 5) 8 216 8 h5x216 h5x224) (@span_join (Z 5) 8 232 8 h5x232 h5x240))))) (@span_join (Z 5) 128 248 128 (@span_join (Z 5) 64 248 64 (@span_join (Z 5) 32 248 32 (@span_join (Z 5) 16 248 16 (@span_join (Z 5) 8 248 8 h5x248 h5x256) (@span_join (Z 5) 8 264 8 h5x264 h5x272)) (@span_join (Z 5) 16 280 16 (@span_join (Z 5) 8 280 8 h5x280 h5x288) (@span_join (Z 5) 8 296 8 h5x296 h5x304))) (@span_join (Z 5) 32 312 32 (@span_join (Z 5) 16 312 16 (@span_join (Z 5) 8 312 8 h5x312 h5x320) (@span_join (Z 5) 8 328 8 h5x328 h5x336)) (@span_join (Z 5) 16 344 16 (@span_join (Z 5) 8 344 8 h5x344 h5x352) (@span_join (Z 5) 8 360 8 h5x360 h5x368)))) (@span_join (Z 5) 64 376 64 (@span_join (Z 5) 32 376 32 (@span_join (Z 5) 16 376 16 (@span_join (Z 5) 8 376 8 h5x376 h5x384) (@span_join (Z 5) 8 392 8 h5x392 h5x400)) (@span_join (Z 5) 16 408 16 (@span_join (Z 5) 8 408 8 h5x408 h5x416) (@span_join (Z 5) 8 424 8 h5x424 h5x432))) (@span_join (Z 5) 32 440 32 (@span_join (Z 5) 16 440 16 (@span_join (Z 5) 8 440 8 h5x440 h5x448) (@span_join (Z 5) 8 456 8 h5x456 h5x464)) (@span_join (Z 5) 16 472 16 (@span_join (Z 5) 8 472 8 h5x472 h5x480) (@span_join (Z 5) 8 488 8 h5x488 h5x496)))))) (@span_join (Z 5) 256 504 256 (@span_join (Z 5) 128 504 128 (@span_join (Z 5) 64 504 64 (@span_join (Z 5) 32 504 32 (@span_join (Z 5) 16 504 16 (@span_join (Z 5) 8 504 8 h5x504 h5x512) (@span_join (Z 5) 8 520 8 h5x520 h5x528)) (@span_join (Z 5) 16 536 16 (@span_join (Z 5) 8 536 8 h5x536 h5x544) (@span_join (Z 5) 8 552 8 h5x552 h5x560))) (@span_join (Z 5) 32 568 32 (@span_join (Z 5) 16 568 16 (@span_join (Z 5) 8 568 8 h5x568 h5x576) (@span_join (Z 5) 8 584 8 h5x584 h5x592)) (@span_join (Z 5) 16 600 16 (@span_join (Z 5) 8 600 8 h5x600 h5x608) (@span_join (Z 5) 8 616 8 h5x616 h5x624)))) (@span_join (Z 5) 64 632 64 (@span_join (Z 5) 32 632 32 (@span_join (Z 5) 16 632 16 (@span_join (Z 5) 8 632 8 h5x632 h5x640) (@span_join (Z 5) 8 648 8 h5x648 h5x656)) (@span_join (Z 5) 16 664 16 (@span_join (Z 5) 8 664 8 h5x664 h5x672) (@span_join (Z 5) 8 680 8 h5x680 h5x688))) (@span_join (Z 5) 32 696 32 (@span_join (Z 5) 16 696 16 (@span_join (Z 5) 8 696 8 h5x696 h5x704) (@span_join (Z 5) 8 712 8 h5x712 h5x720)) (@span_join (Z 5) 16 728 16 (@span_join (Z 5) 8 728 8 h5x728 h5x736) (@span_join (Z 5) 8 744 8 h5x744 h5x752))))) (@span_join (Z 5) 128 760 128 (@span_join (Z 5) 64 760 64 (@span_join (Z 5) 32 760 32 (@span_join (Z 5) 16 760 16 (@span_join (Z 5) 8 760 8 h5x760 h5x768) (@span_join (Z 5) 8 776 8 h5x776 h5x784)) (@span_join (Z 5) 16 792 16 (@span_join (Z 5) 8 792 8 h5x792 h5x800) (@span_join (Z 5) 8 808 8 h5x808 h5x816))) (@span_join (Z 5) 32 824 32 (@span_join (Z 5) 16 824 16 (@span_join (Z 5) 8 824 8 h5x824 h5x832) (@span_join (Z 5) 8 840 8 h5x840 h5x848)) (@span_join (Z 5) 16 856 16 (@span_join (Z 5) 8 856 8 h5x856 h5x864) (@span_join (Z 5) 8 872 8 h5x872 h5x880)))) (@span_join (Z 5) 64 888 64 (@span_join (Z 5) 32 888 32 (@span_join (Z 5) 16 888 16 (@span_join (Z 5) 8 888 8 h5x888 h5x896) (@span_join (Z 5) 8 904 8 h5x904 h5x912)) (@span_join (Z 5) 16 920 16 (@span_join (Z 5) 8 920 8 h5x920 h5x928) (@span_join (Z 5) 8 936 8 h5x936 h5x944))) (@span_join (Z 5) 32 952 32 (@span_join (Z 5) 16 952 16 (@span_join (Z 5) 8 952 8 h5x952 h5x960) (@span_join (Z 5) 8 968 8 h5x968 h5x976)) (@span_join (Z 5) 16 984 16 (@span_join (Z 5) 8 984 8 h5x984 h5x992) (@span_join (Z 5) 8 1000 8 h5x1000 h5x1008))))))) (@span_join (Z 5) 504 1016 506 (@span_join (Z 5) 248 1016 256 (@span_join (Z 5) 120 1016 128 (@span_join (Z 5) 56 1016 64 (@span_join (Z 5) 24 1016 32 (@span_join (Z 5) 8 1016 16 h5x1016 (@span_join (Z 5) 8 1024 8 h5x1024 h5x1032)) (@span_join (Z 5) 16 1040 16 (@span_join (Z 5) 8 1040 8 h5x1040 h5x1048) (@span_join (Z 5) 8 1056 8 h5x1056 h5x1064))) (@span_join (Z 5) 32 1072 32 (@span_join (Z 5) 16 1072 16 (@span_join (Z 5) 8 1072 8 h5x1072 h5x1080) (@span_join (Z 5) 8 1088 8 h5x1088 h5x1096)) (@span_join (Z 5) 16 1104 16 (@span_join (Z 5) 8 1104 8 h5x1104 h5x1112) (@span_join (Z 5) 8 1120 8 h5x1120 h5x1128)))) (@span_join (Z 5) 64 1136 64 (@span_join (Z 5) 32 1136 32 (@span_join (Z 5) 16 1136 16 (@span_join (Z 5) 8 1136 8 h5x1136 h5x1144) (@span_join (Z 5) 8 1152 8 h5x1152 h5x1160)) (@span_join (Z 5) 16 1168 16 (@span_join (Z 5) 8 1168 8 h5x1168 h5x1176) (@span_join (Z 5) 8 1184 8 h5x1184 h5x1192))) (@span_join (Z 5) 32 1200 32 (@span_join (Z 5) 16 1200 16 (@span_join (Z 5) 8 1200 8 h5x1200 h5x1208) (@span_join (Z 5) 8 1216 8 h5x1216 h5x1224)) (@span_join (Z 5) 16 1232 16 (@span_join (Z 5) 8 1232 8 h5x1232 h5x1240) (@span_join (Z 5) 8 1248 8 h5x1248 h5x1256))))) (@span_join (Z 5) 128 1264 128 (@span_join (Z 5) 64 1264 64 (@span_join (Z 5) 32 1264 32 (@span_join (Z 5) 16 1264 16 (@span_join (Z 5) 8 1264 8 h5x1264 h5x1272) (@span_join (Z 5) 8 1280 8 h5x1280 h5x1288)) (@span_join (Z 5) 16 1296 16 (@span_join (Z 5) 8 1296 8 h5x1296 h5x1304) (@span_join (Z 5) 8 1312 8 h5x1312 h5x1320))) (@span_join (Z 5) 32 1328 32 (@span_join (Z 5) 16 1328 16 (@span_join (Z 5) 8 1328 8 h5x1328 h5x1336) (@span_join (Z 5) 8 1344 8 h5x1344 h5x1352)) (@span_join (Z 5) 16 1360 16 (@span_join (Z 5) 8 1360 8 h5x1360 h5x1368) (@span_join (Z 5) 8 1376 8 h5x1376 h5x1384)))) (@span_join (Z 5) 64 1392 64 (@span_join (Z 5) 32 1392 32 (@span_join (Z 5) 16 1392 16 (@span_join (Z 5) 8 1392 8 h5x1392 h5x1400) (@span_join (Z 5) 8 1408 8 h5x1408 h5x1416)) (@span_join (Z 5) 16 1424 16 (@span_join (Z 5) 8 1424 8 h5x1424 h5x1432) (@span_join (Z 5) 8 1440 8 h5x1440 h5x1448))) (@span_join (Z 5) 32 1456 32 (@span_join (Z 5) 16 1456 16 (@span_join (Z 5) 8 1456 8 h5x1456 h5x1464) (@span_join (Z 5) 8 1472 8 h5x1472 h5x1480)) (@span_join (Z 5) 16 1488 16 (@span_join (Z 5) 8 1488 8 h5x1488 h5x1496) (@span_join (Z 5) 8 1504 8 h5x1504 h5x1512)))))) (@span_join (Z 5) 256 1520 250 (@span_join (Z 5) 128 1520 128 (@span_join (Z 5) 64 1520 64 (@span_join (Z 5) 32 1520 32 (@span_join (Z 5) 16 1520 16 (@span_join (Z 5) 8 1520 8 h5x1520 h5x1528) (@span_join (Z 5) 8 1536 8 h5x1536 h5x1544)) (@span_join (Z 5) 16 1552 16 (@span_join (Z 5) 8 1552 8 h5x1552 h5x1560) (@span_join (Z 5) 8 1568 8 h5x1568 h5x1576))) (@span_join (Z 5) 32 1584 32 (@span_join (Z 5) 16 1584 16 (@span_join (Z 5) 8 1584 8 h5x1584 h5x1592) (@span_join (Z 5) 8 1600 8 h5x1600 h5x1608)) (@span_join (Z 5) 16 1616 16 (@span_join (Z 5) 8 1616 8 h5x1616 h5x1624) (@span_join (Z 5) 8 1632 8 h5x1632 h5x1640)))) (@span_join (Z 5) 64 1648 64 (@span_join (Z 5) 32 1648 32 (@span_join (Z 5) 16 1648 16 (@span_join (Z 5) 8 1648 8 h5x1648 h5x1656) (@span_join (Z 5) 8 1664 8 h5x1664 h5x1672)) (@span_join (Z 5) 16 1680 16 (@span_join (Z 5) 8 1680 8 h5x1680 h5x1688) (@span_join (Z 5) 8 1696 8 h5x1696 h5x1704))) (@span_join (Z 5) 32 1712 32 (@span_join (Z 5) 16 1712 16 (@span_join (Z 5) 8 1712 8 h5x1712 h5x1720) (@span_join (Z 5) 8 1728 8 h5x1728 h5x1736)) (@span_join (Z 5) 16 1744 16 (@span_join (Z 5) 8 1744 8 h5x1744 h5x1752) (@span_join (Z 5) 8 1760 8 h5x1760 h5x1768))))) (@span_join (Z 5) 128 1776 122 (@span_join (Z 5) 64 1776 64 (@span_join (Z 5) 32 1776 32 (@span_join (Z 5) 16 1776 16 (@span_join (Z 5) 8 1776 8 h5x1776 h5x1784) (@span_join (Z 5) 8 1792 8 h5x1792 h5x1800)) (@span_join (Z 5) 16 1808 16 (@span_join (Z 5) 8 1808 8 h5x1808 h5x1816) (@span_join (Z 5) 8 1824 8 h5x1824 h5x1832))) (@span_join (Z 5) 32 1840 32 (@span_join (Z 5) 16 1840 16 (@span_join (Z 5) 8 1840 8 h5x1840 h5x1848) (@span_join (Z 5) 8 1856 8 h5x1856 h5x1864)) (@span_join (Z 5) 16 1872 16 (@span_join (Z 5) 8 1872 8 h5x1872 h5x1880) (@span_join (Z 5) 8 1888 8 h5x1888 h5x1896)))) (@span_join (Z 5) 64 1904 58 (@span_join (Z 5) 32 1904 32 (@span_join (Z 5) 16 1904 16 (@span_join (Z 5) 8 1904 8 h5x1904 h5x1912) (@span_join (Z 5) 8 1920 8 h5x1920 h5x1928)) (@span_join (Z 5) 16 1936 16 (@span_join (Z 5) 8 1936 8 h5x1936 h5x1944) (@span_join (Z 5) 8 1952 8 h5x1952 h5x1960))) (@span_join (Z 5) 32 1968 26 (@span_join (Z 5) 16 1968 16 (@span_join (Z 5) 8 1968 8 h5x1968 h5x1976) (@span_join (Z 5) 8 1984 8 h5x1984 h5x1992)) (@span_join (Z 5) 16 2000 10 (@span_join (Z 5) 8 2000 8 h5x2000 h5x2008) (@span_join (Z 5) 8 2016 2 h5x2016 h5x2024))))))))

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
theorem h6x3152 : span (Z 6) 8 3152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3160 : span (Z 6) 8 3160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3168 : span (Z 6) 8 3168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3176 : span (Z 6) 8 3176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3184 : span (Z 6) 8 3184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3192 : span (Z 6) 8 3192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3200 : span (Z 6) 8 3200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3208 : span (Z 6) 8 3208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3216 : span (Z 6) 8 3216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3224 : span (Z 6) 8 3224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3232 : span (Z 6) 8 3232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3240 : span (Z 6) 8 3240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3248 : span (Z 6) 8 3248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3256 : span (Z 6) 8 3256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3264 : span (Z 6) 8 3264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3272 : span (Z 6) 8 3272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3280 : span (Z 6) 8 3280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3288 : span (Z 6) 8 3288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3296 : span (Z 6) 8 3296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3304 : span (Z 6) 8 3304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3312 : span (Z 6) 8 3312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3320 : span (Z 6) 8 3320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3328 : span (Z 6) 8 3328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3336 : span (Z 6) 8 3336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3344 : span (Z 6) 8 3344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3352 : span (Z 6) 8 3352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3360 : span (Z 6) 8 3360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3368 : span (Z 6) 8 3368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3376 : span (Z 6) 8 3376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3384 : span (Z 6) 8 3384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3392 : span (Z 6) 8 3392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3400 : span (Z 6) 8 3400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3408 : span (Z 6) 8 3408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3416 : span (Z 6) 8 3416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3424 : span (Z 6) 8 3424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3432 : span (Z 6) 8 3432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3440 : span (Z 6) 8 3440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3448 : span (Z 6) 8 3448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3456 : span (Z 6) 8 3456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3464 : span (Z 6) 8 3464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3472 : span (Z 6) 8 3472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3480 : span (Z 6) 8 3480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3488 : span (Z 6) 8 3488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3496 : span (Z 6) 8 3496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3504 : span (Z 6) 8 3504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x3512 : span (Z 6) 6 3512 = true := by decide +kernel
theorem z6 : span (Z 6) 3518 0 = true := (@span_join (Z 6) 1760 0 1758 (@span_join (Z 6) 880 0 880 (@span_join (Z 6) 440 0 440 (@span_join (Z 6) 216 0 224 (@span_join (Z 6) 104 0 112 (@span_join (Z 6) 48 0 56 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 8 0 16 h6x0 (@span_join (Z 6) 8 8 8 h6x8 h6x16)) (@span_join (Z 6) 8 24 16 h6x24 (@span_join (Z 6) 8 32 8 h6x32 h6x40))) (@span_join (Z 6) 24 48 32 (@span_join (Z 6) 8 48 16 h6x48 (@span_join (Z 6) 8 56 8 h6x56 h6x64)) (@span_join (Z 6) 16 72 16 (@span_join (Z 6) 8 72 8 h6x72 h6x80) (@span_join (Z 6) 8 88 8 h6x88 h6x96)))) (@span_join (Z 6) 56 104 56 (@span_join (Z 6) 24 104 32 (@span_join (Z 6) 8 104 16 h6x104 (@span_join (Z 6) 8 112 8 h6x112 h6x120)) (@span_join (Z 6) 16 128 16 (@span_join (Z 6) 8 128 8 h6x128 h6x136) (@span_join (Z 6) 8 144 8 h6x144 h6x152))) (@span_join (Z 6) 24 160 32 (@span_join (Z 6) 8 160 16 h6x160 (@span_join (Z 6) 8 168 8 h6x168 h6x176)) (@span_join (Z 6) 16 184 16 (@span_join (Z 6) 8 184 8 h6x184 h6x192) (@span_join (Z 6) 8 200 8 h6x200 h6x208))))) (@span_join (Z 6) 112 216 112 (@span_join (Z 6) 56 216 56 (@span_join (Z 6) 24 216 32 (@span_join (Z 6) 8 216 16 h6x216 (@span_join (Z 6) 8 224 8 h6x224 h6x232)) (@span_join (Z 6) 16 240 16 (@span_join (Z 6) 8 240 8 h6x240 h6x248) (@span_join (Z 6) 8 256 8 h6x256 h6x264))) (@span_join (Z 6) 24 272 32 (@span_join (Z 6) 8 272 16 h6x272 (@span_join (Z 6) 8 280 8 h6x280 h6x288)) (@span_join (Z 6) 16 296 16 (@span_join (Z 6) 8 296 8 h6x296 h6x304) (@span_join (Z 6) 8 312 8 h6x312 h6x320)))) (@span_join (Z 6) 56 328 56 (@span_join (Z 6) 24 328 32 (@span_join (Z 6) 8 328 16 h6x328 (@span_join (Z 6) 8 336 8 h6x336 h6x344)) (@span_join (Z 6) 16 352 16 (@span_join (Z 6) 8 352 8 h6x352 h6x360) (@span_join (Z 6) 8 368 8 h6x368 h6x376))) (@span_join (Z 6) 24 384 32 (@span_join (Z 6) 8 384 16 h6x384 (@span_join (Z 6) 8 392 8 h6x392 h6x400)) (@span_join (Z 6) 16 408 16 (@span_join (Z 6) 8 408 8 h6x408 h6x416) (@span_join (Z 6) 8 424 8 h6x424 h6x432)))))) (@span_join (Z 6) 216 440 224 (@span_join (Z 6) 104 440 112 (@span_join (Z 6) 48 440 56 (@span_join (Z 6) 24 440 24 (@span_join (Z 6) 8 440 16 h6x440 (@span_join (Z 6) 8 448 8 h6x448 h6x456)) (@span_join (Z 6) 8 464 16 h6x464 (@span_join (Z 6) 8 472 8 h6x472 h6x480))) (@span_join (Z 6) 24 488 32 (@span_join (Z 6) 8 488 16 h6x488 (@span_join (Z 6) 8 496 8 h6x496 h6x504)) (@span_join (Z 6) 16 512 16 (@span_join (Z 6) 8 512 8 h6x512 h6x520) (@span_join (Z 6) 8 528 8 h6x528 h6x536)))) (@span_join (Z 6) 56 544 56 (@span_join (Z 6) 24 544 32 (@span_join (Z 6) 8 544 16 h6x544 (@span_join (Z 6) 8 552 8 h6x552 h6x560)) (@span_join (Z 6) 16 568 16 (@span_join (Z 6) 8 568 8 h6x568 h6x576) (@span_join (Z 6) 8 584 8 h6x584 h6x592))) (@span_join (Z 6) 24 600 32 (@span_join (Z 6) 8 600 16 h6x600 (@span_join (Z 6) 8 608 8 h6x608 h6x616)) (@span_join (Z 6) 16 624 16 (@span_join (Z 6) 8 624 8 h6x624 h6x632) (@span_join (Z 6) 8 640 8 h6x640 h6x648))))) (@span_join (Z 6) 112 656 112 (@span_join (Z 6) 56 656 56 (@span_join (Z 6) 24 656 32 (@span_join (Z 6) 8 656 16 h6x656 (@span_join (Z 6) 8 664 8 h6x664 h6x672)) (@span_join (Z 6) 16 680 16 (@span_join (Z 6) 8 680 8 h6x680 h6x688) (@span_join (Z 6) 8 696 8 h6x696 h6x704))) (@span_join (Z 6) 24 712 32 (@span_join (Z 6) 8 712 16 h6x712 (@span_join (Z 6) 8 720 8 h6x720 h6x728)) (@span_join (Z 6) 16 736 16 (@span_join (Z 6) 8 736 8 h6x736 h6x744) (@span_join (Z 6) 8 752 8 h6x752 h6x760)))) (@span_join (Z 6) 56 768 56 (@span_join (Z 6) 24 768 32 (@span_join (Z 6) 8 768 16 h6x768 (@span_join (Z 6) 8 776 8 h6x776 h6x784)) (@span_join (Z 6) 16 792 16 (@span_join (Z 6) 8 792 8 h6x792 h6x800) (@span_join (Z 6) 8 808 8 h6x808 h6x816))) (@span_join (Z 6) 24 824 32 (@span_join (Z 6) 8 824 16 h6x824 (@span_join (Z 6) 8 832 8 h6x832 h6x840)) (@span_join (Z 6) 16 848 16 (@span_join (Z 6) 8 848 8 h6x848 h6x856) (@span_join (Z 6) 8 864 8 h6x864 h6x872))))))) (@span_join (Z 6) 440 880 440 (@span_join (Z 6) 216 880 224 (@span_join (Z 6) 104 880 112 (@span_join (Z 6) 48 880 56 (@span_join (Z 6) 24 880 24 (@span_join (Z 6) 8 880 16 h6x880 (@span_join (Z 6) 8 888 8 h6x888 h6x896)) (@span_join (Z 6) 8 904 16 h6x904 (@span_join (Z 6) 8 912 8 h6x912 h6x920))) (@span_join (Z 6) 24 928 32 (@span_join (Z 6) 8 928 16 h6x928 (@span_join (Z 6) 8 936 8 h6x936 h6x944)) (@span_join (Z 6) 16 952 16 (@span_join (Z 6) 8 952 8 h6x952 h6x960) (@span_join (Z 6) 8 968 8 h6x968 h6x976)))) (@span_join (Z 6) 56 984 56 (@span_join (Z 6) 24 984 32 (@span_join (Z 6) 8 984 16 h6x984 (@span_join (Z 6) 8 992 8 h6x992 h6x1000)) (@span_join (Z 6) 16 1008 16 (@span_join (Z 6) 8 1008 8 h6x1008 h6x1016) (@span_join (Z 6) 8 1024 8 h6x1024 h6x1032))) (@span_join (Z 6) 24 1040 32 (@span_join (Z 6) 8 1040 16 h6x1040 (@span_join (Z 6) 8 1048 8 h6x1048 h6x1056)) (@span_join (Z 6) 16 1064 16 (@span_join (Z 6) 8 1064 8 h6x1064 h6x1072) (@span_join (Z 6) 8 1080 8 h6x1080 h6x1088))))) (@span_join (Z 6) 112 1096 112 (@span_join (Z 6) 56 1096 56 (@span_join (Z 6) 24 1096 32 (@span_join (Z 6) 8 1096 16 h6x1096 (@span_join (Z 6) 8 1104 8 h6x1104 h6x1112)) (@span_join (Z 6) 16 1120 16 (@span_join (Z 6) 8 1120 8 h6x1120 h6x1128) (@span_join (Z 6) 8 1136 8 h6x1136 h6x1144))) (@span_join (Z 6) 24 1152 32 (@span_join (Z 6) 8 1152 16 h6x1152 (@span_join (Z 6) 8 1160 8 h6x1160 h6x1168)) (@span_join (Z 6) 16 1176 16 (@span_join (Z 6) 8 1176 8 h6x1176 h6x1184) (@span_join (Z 6) 8 1192 8 h6x1192 h6x1200)))) (@span_join (Z 6) 56 1208 56 (@span_join (Z 6) 24 1208 32 (@span_join (Z 6) 8 1208 16 h6x1208 (@span_join (Z 6) 8 1216 8 h6x1216 h6x1224)) (@span_join (Z 6) 16 1232 16 (@span_join (Z 6) 8 1232 8 h6x1232 h6x1240) (@span_join (Z 6) 8 1248 8 h6x1248 h6x1256))) (@span_join (Z 6) 24 1264 32 (@span_join (Z 6) 8 1264 16 h6x1264 (@span_join (Z 6) 8 1272 8 h6x1272 h6x1280)) (@span_join (Z 6) 16 1288 16 (@span_join (Z 6) 8 1288 8 h6x1288 h6x1296) (@span_join (Z 6) 8 1304 8 h6x1304 h6x1312)))))) (@span_join (Z 6) 216 1320 224 (@span_join (Z 6) 104 1320 112 (@span_join (Z 6) 48 1320 56 (@span_join (Z 6) 24 1320 24 (@span_join (Z 6) 8 1320 16 h6x1320 (@span_join (Z 6) 8 1328 8 h6x1328 h6x1336)) (@span_join (Z 6) 8 1344 16 h6x1344 (@span_join (Z 6) 8 1352 8 h6x1352 h6x1360))) (@span_join (Z 6) 24 1368 32 (@span_join (Z 6) 8 1368 16 h6x1368 (@span_join (Z 6) 8 1376 8 h6x1376 h6x1384)) (@span_join (Z 6) 16 1392 16 (@span_join (Z 6) 8 1392 8 h6x1392 h6x1400) (@span_join (Z 6) 8 1408 8 h6x1408 h6x1416)))) (@span_join (Z 6) 56 1424 56 (@span_join (Z 6) 24 1424 32 (@span_join (Z 6) 8 1424 16 h6x1424 (@span_join (Z 6) 8 1432 8 h6x1432 h6x1440)) (@span_join (Z 6) 16 1448 16 (@span_join (Z 6) 8 1448 8 h6x1448 h6x1456) (@span_join (Z 6) 8 1464 8 h6x1464 h6x1472))) (@span_join (Z 6) 24 1480 32 (@span_join (Z 6) 8 1480 16 h6x1480 (@span_join (Z 6) 8 1488 8 h6x1488 h6x1496)) (@span_join (Z 6) 16 1504 16 (@span_join (Z 6) 8 1504 8 h6x1504 h6x1512) (@span_join (Z 6) 8 1520 8 h6x1520 h6x1528))))) (@span_join (Z 6) 112 1536 112 (@span_join (Z 6) 56 1536 56 (@span_join (Z 6) 24 1536 32 (@span_join (Z 6) 8 1536 16 h6x1536 (@span_join (Z 6) 8 1544 8 h6x1544 h6x1552)) (@span_join (Z 6) 16 1560 16 (@span_join (Z 6) 8 1560 8 h6x1560 h6x1568) (@span_join (Z 6) 8 1576 8 h6x1576 h6x1584))) (@span_join (Z 6) 24 1592 32 (@span_join (Z 6) 8 1592 16 h6x1592 (@span_join (Z 6) 8 1600 8 h6x1600 h6x1608)) (@span_join (Z 6) 16 1616 16 (@span_join (Z 6) 8 1616 8 h6x1616 h6x1624) (@span_join (Z 6) 8 1632 8 h6x1632 h6x1640)))) (@span_join (Z 6) 56 1648 56 (@span_join (Z 6) 24 1648 32 (@span_join (Z 6) 8 1648 16 h6x1648 (@span_join (Z 6) 8 1656 8 h6x1656 h6x1664)) (@span_join (Z 6) 16 1672 16 (@span_join (Z 6) 8 1672 8 h6x1672 h6x1680) (@span_join (Z 6) 8 1688 8 h6x1688 h6x1696))) (@span_join (Z 6) 24 1704 32 (@span_join (Z 6) 8 1704 16 h6x1704 (@span_join (Z 6) 8 1712 8 h6x1712 h6x1720)) (@span_join (Z 6) 16 1728 16 (@span_join (Z 6) 8 1728 8 h6x1728 h6x1736) (@span_join (Z 6) 8 1744 8 h6x1744 h6x1752)))))))) (@span_join (Z 6) 880 1760 878 (@span_join (Z 6) 440 1760 440 (@span_join (Z 6) 216 1760 224 (@span_join (Z 6) 104 1760 112 (@span_join (Z 6) 48 1760 56 (@span_join (Z 6) 24 1760 24 (@span_join (Z 6) 8 1760 16 h6x1760 (@span_join (Z 6) 8 1768 8 h6x1768 h6x1776)) (@span_join (Z 6) 8 1784 16 h6x1784 (@span_join (Z 6) 8 1792 8 h6x1792 h6x1800))) (@span_join (Z 6) 24 1808 32 (@span_join (Z 6) 8 1808 16 h6x1808 (@span_join (Z 6) 8 1816 8 h6x1816 h6x1824)) (@span_join (Z 6) 16 1832 16 (@span_join (Z 6) 8 1832 8 h6x1832 h6x1840) (@span_join (Z 6) 8 1848 8 h6x1848 h6x1856)))) (@span_join (Z 6) 56 1864 56 (@span_join (Z 6) 24 1864 32 (@span_join (Z 6) 8 1864 16 h6x1864 (@span_join (Z 6) 8 1872 8 h6x1872 h6x1880)) (@span_join (Z 6) 16 1888 16 (@span_join (Z 6) 8 1888 8 h6x1888 h6x1896) (@span_join (Z 6) 8 1904 8 h6x1904 h6x1912))) (@span_join (Z 6) 24 1920 32 (@span_join (Z 6) 8 1920 16 h6x1920 (@span_join (Z 6) 8 1928 8 h6x1928 h6x1936)) (@span_join (Z 6) 16 1944 16 (@span_join (Z 6) 8 1944 8 h6x1944 h6x1952) (@span_join (Z 6) 8 1960 8 h6x1960 h6x1968))))) (@span_join (Z 6) 112 1976 112 (@span_join (Z 6) 56 1976 56 (@span_join (Z 6) 24 1976 32 (@span_join (Z 6) 8 1976 16 h6x1976 (@span_join (Z 6) 8 1984 8 h6x1984 h6x1992)) (@span_join (Z 6) 16 2000 16 (@span_join (Z 6) 8 2000 8 h6x2000 h6x2008) (@span_join (Z 6) 8 2016 8 h6x2016 h6x2024))) (@span_join (Z 6) 24 2032 32 (@span_join (Z 6) 8 2032 16 h6x2032 (@span_join (Z 6) 8 2040 8 h6x2040 h6x2048)) (@span_join (Z 6) 16 2056 16 (@span_join (Z 6) 8 2056 8 h6x2056 h6x2064) (@span_join (Z 6) 8 2072 8 h6x2072 h6x2080)))) (@span_join (Z 6) 56 2088 56 (@span_join (Z 6) 24 2088 32 (@span_join (Z 6) 8 2088 16 h6x2088 (@span_join (Z 6) 8 2096 8 h6x2096 h6x2104)) (@span_join (Z 6) 16 2112 16 (@span_join (Z 6) 8 2112 8 h6x2112 h6x2120) (@span_join (Z 6) 8 2128 8 h6x2128 h6x2136))) (@span_join (Z 6) 24 2144 32 (@span_join (Z 6) 8 2144 16 h6x2144 (@span_join (Z 6) 8 2152 8 h6x2152 h6x2160)) (@span_join (Z 6) 16 2168 16 (@span_join (Z 6) 8 2168 8 h6x2168 h6x2176) (@span_join (Z 6) 8 2184 8 h6x2184 h6x2192)))))) (@span_join (Z 6) 216 2200 224 (@span_join (Z 6) 104 2200 112 (@span_join (Z 6) 48 2200 56 (@span_join (Z 6) 24 2200 24 (@span_join (Z 6) 8 2200 16 h6x2200 (@span_join (Z 6) 8 2208 8 h6x2208 h6x2216)) (@span_join (Z 6) 8 2224 16 h6x2224 (@span_join (Z 6) 8 2232 8 h6x2232 h6x2240))) (@span_join (Z 6) 24 2248 32 (@span_join (Z 6) 8 2248 16 h6x2248 (@span_join (Z 6) 8 2256 8 h6x2256 h6x2264)) (@span_join (Z 6) 16 2272 16 (@span_join (Z 6) 8 2272 8 h6x2272 h6x2280) (@span_join (Z 6) 8 2288 8 h6x2288 h6x2296)))) (@span_join (Z 6) 56 2304 56 (@span_join (Z 6) 24 2304 32 (@span_join (Z 6) 8 2304 16 h6x2304 (@span_join (Z 6) 8 2312 8 h6x2312 h6x2320)) (@span_join (Z 6) 16 2328 16 (@span_join (Z 6) 8 2328 8 h6x2328 h6x2336) (@span_join (Z 6) 8 2344 8 h6x2344 h6x2352))) (@span_join (Z 6) 24 2360 32 (@span_join (Z 6) 8 2360 16 h6x2360 (@span_join (Z 6) 8 2368 8 h6x2368 h6x2376)) (@span_join (Z 6) 16 2384 16 (@span_join (Z 6) 8 2384 8 h6x2384 h6x2392) (@span_join (Z 6) 8 2400 8 h6x2400 h6x2408))))) (@span_join (Z 6) 112 2416 112 (@span_join (Z 6) 56 2416 56 (@span_join (Z 6) 24 2416 32 (@span_join (Z 6) 8 2416 16 h6x2416 (@span_join (Z 6) 8 2424 8 h6x2424 h6x2432)) (@span_join (Z 6) 16 2440 16 (@span_join (Z 6) 8 2440 8 h6x2440 h6x2448) (@span_join (Z 6) 8 2456 8 h6x2456 h6x2464))) (@span_join (Z 6) 24 2472 32 (@span_join (Z 6) 8 2472 16 h6x2472 (@span_join (Z 6) 8 2480 8 h6x2480 h6x2488)) (@span_join (Z 6) 16 2496 16 (@span_join (Z 6) 8 2496 8 h6x2496 h6x2504) (@span_join (Z 6) 8 2512 8 h6x2512 h6x2520)))) (@span_join (Z 6) 56 2528 56 (@span_join (Z 6) 24 2528 32 (@span_join (Z 6) 8 2528 16 h6x2528 (@span_join (Z 6) 8 2536 8 h6x2536 h6x2544)) (@span_join (Z 6) 16 2552 16 (@span_join (Z 6) 8 2552 8 h6x2552 h6x2560) (@span_join (Z 6) 8 2568 8 h6x2568 h6x2576))) (@span_join (Z 6) 24 2584 32 (@span_join (Z 6) 8 2584 16 h6x2584 (@span_join (Z 6) 8 2592 8 h6x2592 h6x2600)) (@span_join (Z 6) 16 2608 16 (@span_join (Z 6) 8 2608 8 h6x2608 h6x2616) (@span_join (Z 6) 8 2624 8 h6x2624 h6x2632))))))) (@span_join (Z 6) 440 2640 438 (@span_join (Z 6) 216 2640 224 (@span_join (Z 6) 104 2640 112 (@span_join (Z 6) 48 2640 56 (@span_join (Z 6) 24 2640 24 (@span_join (Z 6) 8 2640 16 h6x2640 (@span_join (Z 6) 8 2648 8 h6x2648 h6x2656)) (@span_join (Z 6) 8 2664 16 h6x2664 (@span_join (Z 6) 8 2672 8 h6x2672 h6x2680))) (@span_join (Z 6) 24 2688 32 (@span_join (Z 6) 8 2688 16 h6x2688 (@span_join (Z 6) 8 2696 8 h6x2696 h6x2704)) (@span_join (Z 6) 16 2712 16 (@span_join (Z 6) 8 2712 8 h6x2712 h6x2720) (@span_join (Z 6) 8 2728 8 h6x2728 h6x2736)))) (@span_join (Z 6) 56 2744 56 (@span_join (Z 6) 24 2744 32 (@span_join (Z 6) 8 2744 16 h6x2744 (@span_join (Z 6) 8 2752 8 h6x2752 h6x2760)) (@span_join (Z 6) 16 2768 16 (@span_join (Z 6) 8 2768 8 h6x2768 h6x2776) (@span_join (Z 6) 8 2784 8 h6x2784 h6x2792))) (@span_join (Z 6) 24 2800 32 (@span_join (Z 6) 8 2800 16 h6x2800 (@span_join (Z 6) 8 2808 8 h6x2808 h6x2816)) (@span_join (Z 6) 16 2824 16 (@span_join (Z 6) 8 2824 8 h6x2824 h6x2832) (@span_join (Z 6) 8 2840 8 h6x2840 h6x2848))))) (@span_join (Z 6) 112 2856 112 (@span_join (Z 6) 56 2856 56 (@span_join (Z 6) 24 2856 32 (@span_join (Z 6) 8 2856 16 h6x2856 (@span_join (Z 6) 8 2864 8 h6x2864 h6x2872)) (@span_join (Z 6) 16 2880 16 (@span_join (Z 6) 8 2880 8 h6x2880 h6x2888) (@span_join (Z 6) 8 2896 8 h6x2896 h6x2904))) (@span_join (Z 6) 24 2912 32 (@span_join (Z 6) 8 2912 16 h6x2912 (@span_join (Z 6) 8 2920 8 h6x2920 h6x2928)) (@span_join (Z 6) 16 2936 16 (@span_join (Z 6) 8 2936 8 h6x2936 h6x2944) (@span_join (Z 6) 8 2952 8 h6x2952 h6x2960)))) (@span_join (Z 6) 56 2968 56 (@span_join (Z 6) 24 2968 32 (@span_join (Z 6) 8 2968 16 h6x2968 (@span_join (Z 6) 8 2976 8 h6x2976 h6x2984)) (@span_join (Z 6) 16 2992 16 (@span_join (Z 6) 8 2992 8 h6x2992 h6x3000) (@span_join (Z 6) 8 3008 8 h6x3008 h6x3016))) (@span_join (Z 6) 24 3024 32 (@span_join (Z 6) 8 3024 16 h6x3024 (@span_join (Z 6) 8 3032 8 h6x3032 h6x3040)) (@span_join (Z 6) 16 3048 16 (@span_join (Z 6) 8 3048 8 h6x3048 h6x3056) (@span_join (Z 6) 8 3064 8 h6x3064 h6x3072)))))) (@span_join (Z 6) 216 3080 222 (@span_join (Z 6) 104 3080 112 (@span_join (Z 6) 48 3080 56 (@span_join (Z 6) 24 3080 24 (@span_join (Z 6) 8 3080 16 h6x3080 (@span_join (Z 6) 8 3088 8 h6x3088 h6x3096)) (@span_join (Z 6) 8 3104 16 h6x3104 (@span_join (Z 6) 8 3112 8 h6x3112 h6x3120))) (@span_join (Z 6) 24 3128 32 (@span_join (Z 6) 8 3128 16 h6x3128 (@span_join (Z 6) 8 3136 8 h6x3136 h6x3144)) (@span_join (Z 6) 16 3152 16 (@span_join (Z 6) 8 3152 8 h6x3152 h6x3160) (@span_join (Z 6) 8 3168 8 h6x3168 h6x3176)))) (@span_join (Z 6) 56 3184 56 (@span_join (Z 6) 24 3184 32 (@span_join (Z 6) 8 3184 16 h6x3184 (@span_join (Z 6) 8 3192 8 h6x3192 h6x3200)) (@span_join (Z 6) 16 3208 16 (@span_join (Z 6) 8 3208 8 h6x3208 h6x3216) (@span_join (Z 6) 8 3224 8 h6x3224 h6x3232))) (@span_join (Z 6) 24 3240 32 (@span_join (Z 6) 8 3240 16 h6x3240 (@span_join (Z 6) 8 3248 8 h6x3248 h6x3256)) (@span_join (Z 6) 16 3264 16 (@span_join (Z 6) 8 3264 8 h6x3264 h6x3272) (@span_join (Z 6) 8 3280 8 h6x3280 h6x3288))))) (@span_join (Z 6) 112 3296 110 (@span_join (Z 6) 56 3296 56 (@span_join (Z 6) 24 3296 32 (@span_join (Z 6) 8 3296 16 h6x3296 (@span_join (Z 6) 8 3304 8 h6x3304 h6x3312)) (@span_join (Z 6) 16 3320 16 (@span_join (Z 6) 8 3320 8 h6x3320 h6x3328) (@span_join (Z 6) 8 3336 8 h6x3336 h6x3344))) (@span_join (Z 6) 24 3352 32 (@span_join (Z 6) 8 3352 16 h6x3352 (@span_join (Z 6) 8 3360 8 h6x3360 h6x3368)) (@span_join (Z 6) 16 3376 16 (@span_join (Z 6) 8 3376 8 h6x3376 h6x3384) (@span_join (Z 6) 8 3392 8 h6x3392 h6x3400)))) (@span_join (Z 6) 56 3408 54 (@span_join (Z 6) 24 3408 32 (@span_join (Z 6) 8 3408 16 h6x3408 (@span_join (Z 6) 8 3416 8 h6x3416 h6x3424)) (@span_join (Z 6) 16 3432 16 (@span_join (Z 6) 8 3432 8 h6x3432 h6x3440) (@span_join (Z 6) 8 3448 8 h6x3448 h6x3456))) (@span_join (Z 6) 24 3464 30 (@span_join (Z 6) 8 3464 16 h6x3464 (@span_join (Z 6) 8 3472 8 h6x3472 h6x3480)) (@span_join (Z 6) 16 3488 14 (@span_join (Z 6) 8 3488 8 h6x3488 h6x3496) (@span_join (Z 6) 8 3504 6 h6x3504 h6x3512)))))))))

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
theorem h7x1152 : span (Z 7) 8 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1160 : span (Z 7) 8 1160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x1168 : span (Z 7) 6 1168 = true := by decide +kernel
theorem z7 : span (Z 7) 1174 0 = true := (@span_join (Z 7) 584 0 590 (@span_join (Z 7) 288 0 296 (@span_join (Z 7) 144 0 144 (@span_join (Z 7) 72 0 72 (@span_join (Z 7) 32 0 40 (@span_join (Z 7) 16 0 16 (@span_join (Z 7) 8 0 8 h7x0 h7x8) (@span_join (Z 7) 8 16 8 h7x16 h7x24)) (@span_join (Z 7) 16 32 24 (@span_join (Z 7) 8 32 8 h7x32 h7x40) (@span_join (Z 7) 8 48 16 h7x48 (@span_join (Z 7) 8 56 8 h7x56 h7x64)))) (@span_join (Z 7) 32 72 40 (@span_join (Z 7) 16 72 16 (@span_join (Z 7) 8 72 8 h7x72 h7x80) (@span_join (Z 7) 8 88 8 h7x88 h7x96)) (@span_join (Z 7) 16 104 24 (@span_join (Z 7) 8 104 8 h7x104 h7x112) (@span_join (Z 7) 8 120 16 h7x120 (@span_join (Z 7) 8 128 8 h7x128 h7x136))))) (@span_join (Z 7) 72 144 72 (@span_join (Z 7) 32 144 40 (@span_join (Z 7) 16 144 16 (@span_join (Z 7) 8 144 8 h7x144 h7x152) (@span_join (Z 7) 8 160 8 h7x160 h7x168)) (@span_join (Z 7) 16 176 24 (@span_join (Z 7) 8 176 8 h7x176 h7x184) (@span_join (Z 7) 8 192 16 h7x192 (@span_join (Z 7) 8 200 8 h7x200 h7x208)))) (@span_join (Z 7) 32 216 40 (@span_join (Z 7) 16 216 16 (@span_join (Z 7) 8 216 8 h7x216 h7x224) (@span_join (Z 7) 8 232 8 h7x232 h7x240)) (@span_join (Z 7) 16 248 24 (@span_join (Z 7) 8 248 8 h7x248 h7x256) (@span_join (Z 7) 8 264 16 h7x264 (@span_join (Z 7) 8 272 8 h7x272 h7x280)))))) (@span_join (Z 7) 144 288 152 (@span_join (Z 7) 72 288 72 (@span_join (Z 7) 32 288 40 (@span_join (Z 7) 16 288 16 (@span_join (Z 7) 8 288 8 h7x288 h7x296) (@span_join (Z 7) 8 304 8 h7x304 h7x312)) (@span_join (Z 7) 16 320 24 (@span_join (Z 7) 8 320 8 h7x320 h7x328) (@span_join (Z 7) 8 336 16 h7x336 (@span_join (Z 7) 8 344 8 h7x344 h7x352)))) (@span_join (Z 7) 32 360 40 (@span_join (Z 7) 16 360 16 (@span_join (Z 7) 8 360 8 h7x360 h7x368) (@span_join (Z 7) 8 376 8 h7x376 h7x384)) (@span_join (Z 7) 16 392 24 (@span_join (Z 7) 8 392 8 h7x392 h7x400) (@span_join (Z 7) 8 408 16 h7x408 (@span_join (Z 7) 8 416 8 h7x416 h7x424))))) (@span_join (Z 7) 72 432 80 (@span_join (Z 7) 32 432 40 (@span_join (Z 7) 16 432 16 (@span_join (Z 7) 8 432 8 h7x432 h7x440) (@span_join (Z 7) 8 448 8 h7x448 h7x456)) (@span_join (Z 7) 16 464 24 (@span_join (Z 7) 8 464 8 h7x464 h7x472) (@span_join (Z 7) 8 480 16 h7x480 (@span_join (Z 7) 8 488 8 h7x488 h7x496)))) (@span_join (Z 7) 40 504 40 (@span_join (Z 7) 16 504 24 (@span_join (Z 7) 8 504 8 h7x504 h7x512) (@span_join (Z 7) 8 520 16 h7x520 (@span_join (Z 7) 8 528 8 h7x528 h7x536))) (@span_join (Z 7) 16 544 24 (@span_join (Z 7) 8 544 8 h7x544 h7x552) (@span_join (Z 7) 8 560 16 h7x560 (@span_join (Z 7) 8 568 8 h7x568 h7x576))))))) (@span_join (Z 7) 296 584 294 (@span_join (Z 7) 144 584 152 (@span_join (Z 7) 72 584 72 (@span_join (Z 7) 32 584 40 (@span_join (Z 7) 16 584 16 (@span_join (Z 7) 8 584 8 h7x584 h7x592) (@span_join (Z 7) 8 600 8 h7x600 h7x608)) (@span_join (Z 7) 16 616 24 (@span_join (Z 7) 8 616 8 h7x616 h7x624) (@span_join (Z 7) 8 632 16 h7x632 (@span_join (Z 7) 8 640 8 h7x640 h7x648)))) (@span_join (Z 7) 32 656 40 (@span_join (Z 7) 16 656 16 (@span_join (Z 7) 8 656 8 h7x656 h7x664) (@span_join (Z 7) 8 672 8 h7x672 h7x680)) (@span_join (Z 7) 16 688 24 (@span_join (Z 7) 8 688 8 h7x688 h7x696) (@span_join (Z 7) 8 704 16 h7x704 (@span_join (Z 7) 8 712 8 h7x712 h7x720))))) (@span_join (Z 7) 72 728 80 (@span_join (Z 7) 32 728 40 (@span_join (Z 7) 16 728 16 (@span_join (Z 7) 8 728 8 h7x728 h7x736) (@span_join (Z 7) 8 744 8 h7x744 h7x752)) (@span_join (Z 7) 16 760 24 (@span_join (Z 7) 8 760 8 h7x760 h7x768) (@span_join (Z 7) 8 776 16 h7x776 (@span_join (Z 7) 8 784 8 h7x784 h7x792)))) (@span_join (Z 7) 40 800 40 (@span_join (Z 7) 16 800 24 (@span_join (Z 7) 8 800 8 h7x800 h7x808) (@span_join (Z 7) 8 816 16 h7x816 (@span_join (Z 7) 8 824 8 h7x824 h7x832))) (@span_join (Z 7) 16 840 24 (@span_join (Z 7) 8 840 8 h7x840 h7x848) (@span_join (Z 7) 8 856 16 h7x856 (@span_join (Z 7) 8 864 8 h7x864 h7x872)))))) (@span_join (Z 7) 144 880 150 (@span_join (Z 7) 72 880 72 (@span_join (Z 7) 32 880 40 (@span_join (Z 7) 16 880 16 (@span_join (Z 7) 8 880 8 h7x880 h7x888) (@span_join (Z 7) 8 896 8 h7x896 h7x904)) (@span_join (Z 7) 16 912 24 (@span_join (Z 7) 8 912 8 h7x912 h7x920) (@span_join (Z 7) 8 928 16 h7x928 (@span_join (Z 7) 8 936 8 h7x936 h7x944)))) (@span_join (Z 7) 32 952 40 (@span_join (Z 7) 16 952 16 (@span_join (Z 7) 8 952 8 h7x952 h7x960) (@span_join (Z 7) 8 968 8 h7x968 h7x976)) (@span_join (Z 7) 16 984 24 (@span_join (Z 7) 8 984 8 h7x984 h7x992) (@span_join (Z 7) 8 1000 16 h7x1000 (@span_join (Z 7) 8 1008 8 h7x1008 h7x1016))))) (@span_join (Z 7) 72 1024 78 (@span_join (Z 7) 32 1024 40 (@span_join (Z 7) 16 1024 16 (@span_join (Z 7) 8 1024 8 h7x1024 h7x1032) (@span_join (Z 7) 8 1040 8 h7x1040 h7x1048)) (@span_join (Z 7) 16 1056 24 (@span_join (Z 7) 8 1056 8 h7x1056 h7x1064) (@span_join (Z 7) 8 1072 16 h7x1072 (@span_join (Z 7) 8 1080 8 h7x1080 h7x1088)))) (@span_join (Z 7) 40 1096 38 (@span_join (Z 7) 16 1096 24 (@span_join (Z 7) 8 1096 8 h7x1096 h7x1104) (@span_join (Z 7) 8 1112 16 h7x1112 (@span_join (Z 7) 8 1120 8 h7x1120 h7x1128))) (@span_join (Z 7) 16 1136 22 (@span_join (Z 7) 8 1136 8 h7x1136 h7x1144) (@span_join (Z 7) 8 1152 14 h7x1152 (@span_join (Z 7) 8 1160 6 h7x1160 h7x1168))))))))

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

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : MonRun (goal 60) s xsG) : False := by
  have hl := run_len h
  have hlen : xsG.length = 6 := by decide +kernel
  rw [hlen] at hl
  have hlo : 5 ≤ s := by omega
  interval_cases s
  · exact bar_all checked 5 (by decide) 275 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 5 275)) h)
  · exact bar_all checked 6 (by decide) 479 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 6 479)) h)
  · exact bar_all checked 7 (by decide) 159 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 7 159)) h)
  · exact bar_all checked 8 (by decide) 6 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 8 6)) h)
  · exact bar_all checked 9 (by decide) 0 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 9 0)) h)

theorem no_small : ¬ HasMonoSize 6 wheel 9 :=
  encoded_wheel_mono_exclusion rowsG xsG 60 enc_inputsG enc_goalG proper_failG noRunFull

end PEqualNP.Outside.L_meta_744_aux

theorem PEqualNP.Outside.L_meta_744 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 10 ≤ C.size := by
  intro C hm hev
  exact PEqualNP.Outside.L_meta_744_aux.wheel_lower_from_mono_exclusion PEqualNP.Outside.L_meta_744_aux.no_small C hm hev
